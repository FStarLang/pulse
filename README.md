# Supplementary material for the paper "PulseCore: An Impredicative Concurrent Separation Logic for Dependently Typed Programs"

This directory contains the F* code described in the paper.
The code is anonymized, names have been redacted and some comments have been changed or removed entirely.

  - `lib/pulse/core` contains the PulseCore formalization described in Sec. 3-4.
     A more detailed description of the formalization is below.

The PulseCore formalization is written in pure F* and can be checked using `make -C lib/pulse/core`.
This requires an F* version built from a git version from November 13th 2024.

Compiling the other parts of the supplementary material would require the Pulse plugin,
which is neither part of the paper nor part of this submission.

  - `share/pulse/examples/PulseCorePaper.S2.Lock.fst` contains the spinlock example from Sec 2
  - `lib/pulse/lib/Pulse.Lib.Task.fst` contains the task pool from Sec. 5.1
  - `share/pulse/examples/Quicksort.Task.fst` contains the parallel quicksort from Sec. 5.2
  - `lib/pulse/lib/Pulse.Lib.ConditionVar.fst` contains the barrier from Sec. 5.3
  - `share/pulse/examples/dice/dpe` contains the DPE implementation from Sec. 5.4
    - `pulse2rust/dpe/src` contains the Rust code extracted from this DPE implementation

## A Tour of the Formalization of PulseCore

`lib/pulse/core` contains the formalization of PulseCore presented in Sections 3-4 of
the paper.

As mentioned in the paper, the presentation in the paper is more abstract and
uses a more mathematical notation than the code. It also omits a few
technicalities that the code deals with. This README aims to relate concepts in
the paper to the code.

* `PulseCore.BaseHeapSig`: Defines the product of the core heap and erased core heap

* `PulseCore.IndirectionTheory`: Defines the Knot construction from Indirection Theory

* `PulseCore.KnotInstantiation`: Defines the instantion of the Knot construction for the Pulse-specific functor

* `PulseCore.IndirectionTheorySep`: Defines mem, slprop, and the concrete predicates from Sec. 3.3

* `PulseCore.Semantics`: A generic Act-Ret-Par definition for action-tree forests
  and its interpreter. It's defined generally for an abstract separation logic.

* `PulseCore.InstantiatedSemantics`: Instantiates PulseCore.Semantics with the
  extended heap derived in IndirectionTheorySep.

* `PulseCore.Action`: The `except:set iname { except \cap opens == \emptyset}`
  parameter is introduced here, allowing an atomic computation's type to speak
  about the invariants it opens, rather than the invariants that the context
  must not open.

* `PulseCore.Atomic`: A final level of abstraction, packaging actions and action
  trees into the stt_atomic, stt_ghost, and stt types.

* `Pulse.Lib.Core`: Contains the definition `later_credit_buy`.
