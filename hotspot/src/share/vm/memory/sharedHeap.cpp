/*
 * Copyright (c) 2000, 2013, Oracle and/or its affiliates. All rights reserved.
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

#include <stdio.h>
#include "precompiled.hpp"
#include "classfile/symbolTable.hpp"
#include "classfile/systemDictionary.hpp"
#include "code/codeCache.hpp"
#include "gc_interface/collectedHeap.inline.hpp"
#include "memory/sharedHeap.hpp"
#include "oops/oop.inline.hpp"
#include "runtime/fprofiler.hpp"
#include "runtime/java.hpp"
#include "services/management.hpp"
#include "utilities/copy.hpp"
#include "utilities/workgroup.hpp"
#include "gc_implementation/shared/gcTraceTime.hpp"

SharedHeap* SharedHeap::_sh;

// The set of potentially parallel tasks in strong root scanning.
enum SH_process_strong_roots_tasks {
  SH_PS_Universe_oops_do,
  SH_PS_JNIHandles_oops_do,
  SH_PS_ObjectSynchronizer_oops_do,
  SH_PS_FlatProfiler_oops_do,
  SH_PS_Management_oops_do,
  SH_PS_SystemDictionary_oops_do,
  SH_PS_jvmti_oops_do,
  SH_PS_CodeCache_oops_do,
  // Leave this one last.
  SH_PS_NumElements
};

SharedHeap::SharedHeap(CollectorPolicy* policy_) :
  CollectedHeap(),
  _collector_policy(policy_),
  _perm_gen(NULL), _rem_set(NULL),
  _strong_roots_parity(0),
  _process_strong_tasks(new SubTasksDone(SH_PS_NumElements)),
  _workers(NULL)
{
  if (_process_strong_tasks == NULL || !_process_strong_tasks->valid()) {
    vm_exit_during_initialization("Failed necessary allocation.");
  }
  _sh = this;  // ch is static, should be set only once.
  if ((UseParNewGC ||
      (UseConcMarkSweepGC && (CMSParallelInitialMarkEnabled ||
                              CMSParallelRemarkEnabled)) ||
       UseG1GC) &&
      ParallelGCThreads > 0) {
    _workers = new FlexibleWorkGang("Parallel GC Threads", ParallelGCThreads,
                            /* are_GC_task_threads */true,
                            /* are_ConcurrentGC_threads */false);
    if (_workers == NULL) {
      vm_exit_during_initialization("Failed necessary allocation.");
    } else {
      _workers->initialize_workers();
    }
  }
}

int SharedHeap::n_termination() {
  return _process_strong_tasks->n_threads();
}

void SharedHeap::set_n_termination(int t) {
  _process_strong_tasks->set_n_threads(t);
}

bool SharedHeap::heap_lock_held_for_gc() {
  Thread* t = Thread::current();
  return    Heap_lock->owned_by_self()
         || (   (t->is_GC_task_thread() ||  t->is_VM_thread())
             && _thread_holds_heap_lock_for_gc);
}

void SharedHeap::set_par_threads(uint t) {
  assert(t == 0 || !UseSerialGC, "Cannot have parallel threads");
  _n_par_threads = t;
  _process_strong_tasks->set_n_threads(t);
}

class AssertIsPermClosure: public OopClosure {
public:
  virtual void do_oop(oop* p) {
    assert((*p) == NULL || (*p)->is_perm(), "Referent should be perm.");
  }
  virtual void do_oop(narrowOop* p) { ShouldNotReachHere(); }
};
static AssertIsPermClosure assert_is_perm_closure;

#ifdef ASSERT
class AssertNonScavengableClosure: public OopClosure {
public:
  virtual void do_oop(oop* p) {
    assert(!Universe::heap()->is_in_partial_collection(*p),
      "Referent should not be scavengable.");  }
  virtual void do_oop(narrowOop* p) { ShouldNotReachHere(); }
};
static AssertNonScavengableClosure assert_is_non_scavengable_closure;
#endif

void SharedHeap::change_strong_roots_parity() {
  // Also set the new collection parity.
  assert(_strong_roots_parity >= 0 && _strong_roots_parity <= 2,
         "Not in range.");
  _strong_roots_parity++;
  if (_strong_roots_parity == 3) _strong_roots_parity = 1;
  assert(_strong_roots_parity >= 1 && _strong_roots_parity <= 2,
         "Not in range.");
}

SharedHeap::StrongRootsScope::StrongRootsScope(SharedHeap* outer, bool activate)
  : MarkScope(activate)
{
  if (_active) {
    outer->change_strong_roots_parity();
    // Zero the claimed high water mark in the StringTable
    StringTable::clear_parallel_claimed_index();
  }
}

SharedHeap::StrongRootsScope::~StrongRootsScope() {
  // nothing particular
}

void SharedHeap::process_strong_roots(bool activate_scope,
                                      bool collecting_perm_gen,
                                      ScanningOption so,
                                      OopClosure* roots,
                                      CodeBlobClosure* code_roots,
                                      OopsInGenClosure* perm_blk,
                                      bool manages_code_roots) {
  StrongRootsScope srs(this, activate_scope);
  // General strong roots.
  assert(_strong_roots_parity != 0, "must have called prologue code");
  // _n_termination for _process_strong_tasks should be set up stream
  // in a method not running in a GC worker.  Otherwise the GC worker
  // could be trying to change the termination condition while the task
  // is executing in another GC worker.
  if (!_process_strong_tasks->is_task_claimed(SH_PS_Universe_oops_do)) {
    long start = GCTraceTime::getCurrentTime();
    Universe::oops_do(roots);
    GCTraceTime::printf_format_time("Universe::oops_do", start, GCTraceTime::getCurrentTime() - start);

    // Consider perm-gen discovered lists to be strong.
    start = GCTraceTime::getCurrentTime();
    perm_gen()->ref_processor()->weak_oops_do(roots);
    GCTraceTime::printf_format_time("perm_gen()->ref_processor()->weak_oops_do", start, GCTraceTime::getCurrentTime() - start);
  }
  // Global (strong) JNI handles
  if (!_process_strong_tasks->is_task_claimed(SH_PS_JNIHandles_oops_do)) {
    long start = GCTraceTime::getCurrentTime();
    JNIHandles::oops_do(roots);
    GCTraceTime::printf_format_time("JNIHandles::oops_do", start, GCTraceTime::getCurrentTime() - start);
  }

  // All threads execute this; the individual threads are task groups.
  if (CollectedHeap::use_parallel_gc_threads()) {
    long start = GCTraceTime::getCurrentTime();
    Threads::possibly_parallel_oops_do(roots, code_roots);
    GCTraceTime::printf_format_time("Threads::possibly_parallel_oops_do", start, GCTraceTime::getCurrentTime() - start);
  } else {
    long start = GCTraceTime::getCurrentTime();
    Threads::oops_do(roots, code_roots);
    GCTraceTime::printf_format_time("Threads::oops_do", start, GCTraceTime::getCurrentTime() - start);
  }

  if (!_process_strong_tasks-> is_task_claimed(SH_PS_ObjectSynchronizer_oops_do)) {
    long start = GCTraceTime::getCurrentTime();
    ObjectSynchronizer::oops_do(roots);
    GCTraceTime::printf_format_time("ObjectSynchronizer::oops_do", start, GCTraceTime::getCurrentTime() - start);
  }
  if (!_process_strong_tasks->is_task_claimed(SH_PS_FlatProfiler_oops_do)) {
    long start = GCTraceTime::getCurrentTime();
    FlatProfiler::oops_do(roots);
    GCTraceTime::printf_format_time("FlatProfiler::oops_do", start, GCTraceTime::getCurrentTime() - start);
  }
  if (!_process_strong_tasks->is_task_claimed(SH_PS_Management_oops_do)) {
    long start = GCTraceTime::getCurrentTime();
    Management::oops_do(roots);
    GCTraceTime::printf_format_time("Management::oops_do", start, GCTraceTime::getCurrentTime() - start);
  }
  if (!_process_strong_tasks->is_task_claimed(SH_PS_jvmti_oops_do)) {
    long start = GCTraceTime::getCurrentTime();
    JvmtiExport::oops_do(roots);
    GCTraceTime::printf_format_time("JvmtiExport::oops_do", start, GCTraceTime::getCurrentTime() - start);
  }

  if (!_process_strong_tasks->is_task_claimed(SH_PS_SystemDictionary_oops_do)) {
    if (so & SO_AllClasses) {
      long start = GCTraceTime::getCurrentTime();

      SystemDictionary::oops_do(roots);

      long end = GCTraceTime::getCurrentTime();
      GCTraceTime::printf_format_time("SystemDictionary::oops_do", start, end - start);
    } else if (so & SO_SystemClasses) {
      long start = GCTraceTime::getCurrentTime();

      SystemDictionary::always_strong_oops_do(roots);

      long end = GCTraceTime::getCurrentTime();
      GCTraceTime::printf_format_time("SystemDictionary::always_strong_oops_do", start, end - start);
    }
  }

  // All threads execute the following. A specific chunk of buckets
  // from the StringTable are the individual tasks.
  if (so & SO_Strings || (!collecting_perm_gen && !JavaObjectsInPerm)) {
    if (CollectedHeap::use_parallel_gc_threads()) {
      long start = GCTraceTime::getCurrentTime();

      StringTable::possibly_parallel_oops_do(roots);

      long end = GCTraceTime::getCurrentTime();
      GCTraceTime::printf_format_time("StringTable::possibly_parallel_oops_do", start, end - start);
    } else {
      long start = GCTraceTime::getCurrentTime();
      StringTable::oops_do(roots);
      long end = GCTraceTime::getCurrentTime();
      GCTraceTime::printf_format_time("StringTable::oops_do", start, end - start);
    }
  }
  if (JavaObjectsInPerm) {
    // Verify the string table contents are in the perm gen
    if (CollectedHeap::use_parallel_gc_threads()) {
      long start = GCTraceTime::getCurrentTime();
      NOT_PRODUCT(StringTable::possibly_parallel_oops_do(&assert_is_perm_closure));
      GCTraceTime::printf_format_time("NOT_PRODUCT(StringTable::possibly_parallel_oops_do", start, GCTraceTime::getCurrentTime() - start);
    } else {
      long start = GCTraceTime::getCurrentTime();
      NOT_PRODUCT(StringTable::oops_do(&assert_is_perm_closure));
      GCTraceTime::printf_format_time("NOT_PRODUCT(StringTable::oops_do", start, GCTraceTime::getCurrentTime() - start);
    }
  }

  if (!_process_strong_tasks->is_task_claimed(SH_PS_CodeCache_oops_do)) {
    if (so & SO_CodeCache) {
      // (Currently, CMSCollector uses this to do intermediate-strength collections.)
      assert(collecting_perm_gen, "scanning all of code cache");
      assert(code_roots != NULL, "must supply closure for code cache");
      if (code_roots != NULL) {
        long start = GCTraceTime::getCurrentTime();
        CodeCache::blobs_do(code_roots);
        GCTraceTime::printf_format_time("CodeCache::blobs_do", start, GCTraceTime::getCurrentTime() - start);
      }
    } else if (so & (SO_SystemClasses|SO_AllClasses)) {
      if (!manages_code_roots && !collecting_perm_gen) {
        // If we are collecting from class statics, but we are not going to
        // visit all of the CodeCache, collect from the non-perm roots if any.
        // This makes the code cache function temporarily as a source of strong
        // roots for oops, until the next major collection.
        //
        // If collecting_perm_gen is true, we require that this phase will call
        // CodeCache::do_unloading.  This will kill off nmethods with expired
        // weak references, such as stale invokedynamic targets.
        long start = GCTraceTime::getCurrentTime();
        CodeCache::scavenge_root_nmethods_do(code_roots);
        GCTraceTime::printf_format_time("CodeCache::scavenge_root_nmethods_do", start, GCTraceTime::getCurrentTime() - start);
      }
    }
    // Verify that the code cache contents are not subject to
    // movement by a scavenging collection.
    DEBUG_ONLY(CodeBlobToOopClosure assert_code_is_non_scavengable(&assert_is_non_scavengable_closure, /*do_marking=*/ false));
    DEBUG_ONLY(CodeCache::asserted_non_scavengable_nmethods_do(&assert_code_is_non_scavengable));
  }

  if (!collecting_perm_gen) {
    // All threads perform this; coordination is handled internally.
    long start = GCTraceTime::getCurrentTime();

    rem_set()->younger_refs_iterate(perm_gen(), perm_blk);
    GCTraceTime::printf_format_time("rem_set()->younger_refs_iterate", start, GCTraceTime::getCurrentTime() - start);
  }

  long start = GCTraceTime::getCurrentTime();
  _process_strong_tasks->all_tasks_completed();
  GCTraceTime::printf_format_time("_process_strong_tasks->all_tasks_completed", start, GCTraceTime::getCurrentTime() - start);
}

class AlwaysTrueClosure: public BoolObjectClosure {
public:
  void do_object(oop p) { ShouldNotReachHere(); }
  bool do_object_b(oop p) { return true; }
};
static AlwaysTrueClosure always_true;

class SkipAdjustingSharedStrings: public OopClosure {
  OopClosure* _clo;
public:
  SkipAdjustingSharedStrings(OopClosure* clo) : _clo(clo) {}

  virtual void do_oop(oop* p) {
    oop o = (*p);
    if (!o->is_shared_readwrite()) {
      _clo->do_oop(p);
    }
  }
  virtual void do_oop(narrowOop* p) { ShouldNotReachHere(); }
};

// Unmarked shared Strings in the StringTable (which got there due to
// being in the constant pools of as-yet unloaded shared classes) were
// not marked and therefore did not have their mark words preserved.
// These entries are also deliberately not purged from the string
// table during unloading of unmarked strings. If an identity hash
// code was computed for any of these objects, it will not have been
// cleared to zero during the forwarding process or by the
// RecursiveAdjustSharedObjectClosure, and will be confused by the
// adjusting process as a forwarding pointer. We need to skip
// forwarding StringTable entries which contain unmarked shared
// Strings. Actually, since shared strings won't be moving, we can
// just skip adjusting any shared entries in the string table.

void SharedHeap::process_weak_roots(OopClosure* root_closure,
                                    CodeBlobClosure* code_roots,
                                    OopClosure* non_root_closure) {
  // Global (weak) JNI handles
  JNIHandles::weak_oops_do(&always_true, root_closure);

  CodeCache::blobs_do(code_roots);
  if (UseSharedSpaces && !DumpSharedSpaces) {
    SkipAdjustingSharedStrings skip_closure(root_closure);
    StringTable::oops_do(&skip_closure);
  } else {
    StringTable::oops_do(root_closure);
  }
}

void SharedHeap::set_barrier_set(BarrierSet* bs) {
  _barrier_set = bs;
  // Cached barrier set for fast access in oops
  oopDesc::set_bs(bs);
}

void SharedHeap::post_initialize() {
  ref_processing_init();
}

void SharedHeap::ref_processing_init() {
  perm_gen()->ref_processor_init();
}

// Some utilities.
void SharedHeap::print_size_transition(outputStream* out,
                                       size_t bytes_before,
                                       size_t bytes_after,
                                       size_t capacity) {
  out->print(" %d%s->%d%s(%d%s)",
             byte_size_in_proper_unit(bytes_before),
             proper_unit_for_byte_size(bytes_before),
             byte_size_in_proper_unit(bytes_after),
             proper_unit_for_byte_size(bytes_after),
             byte_size_in_proper_unit(capacity),
             proper_unit_for_byte_size(capacity));
}
