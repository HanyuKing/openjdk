/*
 * Copyright (c) 2012, 2013, Oracle and/or its affiliates. All rights reserved.
 * DO NOT ALTER OR REMOVE COPYRIGHT NOTICES OR THIS FILE HEADER.
 *
 * This code is free software; you can redistribute it and/or modify it
 * under the terms of the GNU General Public License version 2 only, as
 * published by the Free Software Foundation.
 *
 * This code is distributed in the hope that it will be useful, but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
 * FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License
 * version 2 for more details (a copy is included in the LICENSE file that
 * accompanied this code).
 *
 * You should have received a copy of the GNU General Public License version
 * 2 along with this work; if not, write to the Free Software Foundation,
 * Inc., 51 Franklin St, Fifth Floor, Boston, MA 02110-1301 USA.
 *
 * Please contact Oracle, 500 Oracle Parkway, Redwood Shores, CA 94065 USA
 * or visit www.oracle.com if you need additional information or have any
 * questions.
 *
 */

#include "precompiled.hpp"
#include "gc_implementation/shared/gcTimer.hpp"
#include "gc_implementation/shared/gcTraceTime.hpp"
#include "runtime/globals.hpp"
#include "runtime/os.hpp"
#include "runtime/safepoint.hpp"
#include "runtime/timer.hpp"
#include "utilities/ostream.hpp"
#ifdef TARGET_OS_FAMILY_linux
# include "thread_linux.inline.hpp"
#endif
#ifdef TARGET_OS_FAMILY_solaris
# include "thread_solaris.inline.hpp"
#endif
#ifdef TARGET_OS_FAMILY_windows
# include "thread_windows.inline.hpp"
#endif
#ifdef TARGET_OS_FAMILY_bsd
# include "thread_bsd.inline.hpp"
#endif

#include "utilities/ticks.inline.hpp"


GCTraceTime::GCTraceTime(const char* title, bool doit, bool print_cr, GCTimer* timer) :
    _title(title), _doit(doit), _print_cr(print_cr), _timer(timer), _start_counter() {
  if (_doit || _timer != NULL) {
    _start_counter.stamp();
  }

  if (_timer != NULL) {
    assert(SafepointSynchronize::is_at_safepoint(), "Tracing currently only supported at safepoints");
    assert(Thread::current()->is_VM_thread(), "Tracing currently only supported from the VM thread");

    _timer->register_gc_phase_start(title, _start_counter);
  }

  if (_doit) {
    gclog_or_tty->date_stamp(PrintGCDateStamps);
    gclog_or_tty->stamp(PrintGCTimeStamps);
    gclog_or_tty->print("[%s", title);
    gclog_or_tty->flush();
  }
}

GCTraceTime::~GCTraceTime() {
  Ticks stop_counter;

  if (_doit || _timer != NULL) {
    stop_counter.stamp();
  }

  if (_timer != NULL) {
    _timer->register_gc_phase_end(stop_counter);
  }

  if (_doit) {
    const Tickspan duration = stop_counter - _start_counter;
    double duration_in_seconds = TicksToTimeHelper::seconds(duration);
    if (_print_cr) {
      gclog_or_tty->print_cr(", %3.7f secs]", duration_in_seconds);
    } else {
      gclog_or_tty->print(", %3.7f secs]", duration_in_seconds);
    }
    gclog_or_tty->flush();
  }
}

long GCTraceTime::getCurrentTime() {
    struct timeval tv;
    gettimeofday(&tv,NULL);
    return tv.tv_sec * 1000 + tv.tv_usec / 1000;
}

void GCTraceTime::printf_format_time(const char* title, long start_time, long cost_time) {
    char time_format_str[64];
    time_t start_time_secs = start_time / 1000; // millisecond to second
    strftime(time_format_str, sizeof(time_format_str), "%Y-%m-%d %X", localtime(&start_time_secs));

    // print as a json string
    printf("{\"happened_time\":\"%s\", \"method\":\"%s\", \"time\":\"%ld\", \"time_unit\":\"milliseconds\"},\n", time_format_str, title, cost_time);
}