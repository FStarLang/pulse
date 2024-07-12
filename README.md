# Supplementary material for the paper "PulseCore: A Dependently Typed Stratified Separation Logic"

This directory contains the F* code described in the paper.
The code is anonymized, names have been redacted and some comments removed entirely.

  - `lib/pulse/core` contains the PulseCore formalization described in Sec. 3
     A more detailed description of the formalization is below.

The PulseCore formalization is written in pure F* and can be checked using `make -C lib/pulse/core`.
This requires an F* version built from a git version from July 10th 2024.

Compiling the other parts of the supplementary material would require the Pulse plugin,
which is neither part of the paper nor part of this submission.

  - `share/pulse/examples/PulseCorePaper.S2.Lock.fst` contains the spinlock example from Sec 2
  - `share/pulse/examples/by-example/PulseTutorial.PCMParallelIncrement.fst` contains the parallel increment from Sec. 4.1
  - `lib/pulse/lib/Pulse.Lib.ConditionVarWithCodes.fst` contains the barrier from Sec. 4.2
  - `share/pulse/examples/dice/dpe` contains the DPE implementation from Sec. 4.3
    - `pulse2rust/dpe/src` containes the Rust code extracted from this DPE implementation

# A Tour of the Formalization of PulseCore

`lib/pulse/core` contains the formalization of PulseCore presented in Section 3 of
the paper.

As mentioned in the paper, the presentation in the paper is more abstract and
uses a more mathematical notation than the code. It also omits a few
technicalities that the code deals with. This README aims to relate concepts in
the paper to the code.

* `PulseCore.HeapSig.fsti`:
   - Defines the signature `heap_sig`, called `slsig` in the paper

   - heap_sig is a flattening of `slsig`: where `slsig` uses several sub-classes,
     for `invariants`, `erasability` etc.; in heap_sig, the fields of all classes
     are flattened into a single record.

   - heap_sig also defines a signature of separable heaps, which is just another
     formulation of a PCM, with a separate "full_mem_pred". In CompactHeapSig,
     we show that `separable` and `pcm` are equivalent.

   - The type of actions does not take the `except:set iname { except \cap opens
     == \emptyset}` argument. We add this parameter in PulseCore.Action. The
     paper presents fuses these two parts of the development together.

* `PulseCore.Heap`: Defines the core heap

* `PulseCore.Heap2`: Defines a product of core heap and erased core heap

* `PulseCore.BaseHeapSig`: Packaged Heap2 with allocation counters and
  instantiates `heap_sig`, i.e., the base case.

* `PulseCore.HeapExtension`: The main construction of heap extension

* PulseCore.MemoryAlt: The instantiation of HeapExtension to
  `extend (extend (extend (base_heap u#a)))`, and defining many of the types
  used in the rest of the development, slprop_4, slprop_3, slprop_2, etc.
  Some of the complexity here is related to proving that the types derived from 
  the extended heap are correctly marked as erasable for F*.

* PulseCore.Semantics: A generic Act-Ret-Par definition for action-tree forests
  and its interpreter. It's defined for an even more abstract separation logic
  than slsig.

* PulseCore.InstantiatedSemantics: Instantiates PulseCore.Semantics with the
  extended heap derived in MemoryAlt, setting the `base_heap u#a` to
  `base_heap u#0`.

* PulseCore.Action: The `except:set iname { except \cap opens == \emptyset}`
  parameter is introduced here, allowing an atomic computation's type to speak
  about the invariants it opens, rather than the invariants that the context
  must not open.

* PulseCore.Atomic: A final level of abstraction, packaging actions and action
  trees into the stt_atomic, stt_ghost, and stt types.
