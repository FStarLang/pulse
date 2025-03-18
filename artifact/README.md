# PulseCore artifact (PLDI 2025)

The artifact includes:

  1. The implementation of the PulseCore logic.
  2. The examples from the paper, in Pulse.
  3. The implementation of the Pulse checker (not a contribution of the paper).

The main contribution of the paper is the PulseCore logic (1) and
showing that it is expressive enough to handle many interesting programs
(2). The Pulse checker is a partially-verified certified type checker
for Pulse and, as such, has some admitted proofs. The admitted proofs
are mostly related to the difficulties of writing a certified type
checker and some scalability limitations of the F* metaprogramming
engine, and not at all to the separation logic itself. We include it in
the interest of transparency, but remark that its partial verification
status should not be of interest to the reviewers.

There are no admits in the PulseCore logic, nor in the examples
explained in the paper. There are other admits in tests (intentional)
and in some other examples.

# Getting Started Guide

The artifact is a docker container that starts a vscode server on port 8080.

  1. To run this container you first need to load it:

    docker load < pulsecore-pldi2025-docker.tar.gz

  2. Then you can start it:

    docker run -p 127.0.0.1:8080:8080 -it pulsecore-pldi2025

  3. You can now access the vscode server by opening http://localhost:8080 in
     your browser.

  4. Open a terminal inside vscode using the keyboard shortcut `` ctrl+` ``

  5. Run `make -j$(nproc)`.  This will build and verify PulseCore (and Pulse) using F\*.
     That this command successfully terminates shows that F\* fully verifies the
     PulseCore logic and the Pulse standard library (including spinlocks, linked
     list, task pool, etc).

     You may see some warnings (e.g. Warning 241 about not being able to load
     checked dependencies).  This is expected, and has no impact on the
     verification status.

  6. To check that everything works as expected, open the
     `share/pulse/examples/PulseCorePaper.S2.Lock.fst` file which is the
     spinlock example from the paper.  Put the cursor at the end of the file and
     press `ctrl+.`, this instructs F\* to verify the file until the cursor
     position (i.e., the whole file).  After a few seconds, you should see a
     green bar on the left of the file.  The green bar indicates that the file
     has been successfully checked.

     The [F* VS Code extension homepage](https://github.com/FStarLang/fstar-vscode-assistant/?tab=readme-ov-file#features-and-basic-usage-guide)
     contains a detailed explanation on how to use the F* mode in VS Code.

Optional:
We have included a `pulse.sh` script that sets all the right options for F\*
to verify a particular Pulse file.  You can run
`./pulse.sh -f share/pulse/examples/PulseCorePaper.S2.Lock.fst` (`-f` makes sure
F\* verifies it even if the result is cached).  If you see an error like
`Unknown language extension pulse` it indicates that the Pulse checker has not
been built, make sure that `make` succeeded.

# Step-By-Step Instructions

  7. To check all the examples in the artifact, covering those mentioned in the
     paper, run `make test-share -j$(nproc)`.

  8. To build and run the task-parallel Quicksort, run `make test-qs`.

  9. Open the files listed in the "Connection to Paper Text" section in this
     README and check that they contain the corresponding concepts from the
     paper.  You can use go-to-definition to navigate around the code
     (ctrl+click).

## Structure of the Artifact

- `lib/common` and `lib/core`: contain the F\* definitions for the
PulseCore logic. This directories can be checked fully by running 'make
lib-core'. There is no imperative Pulse code here, only pure F\*.

- `lib/pulse`: contains the Pulse library, e.g. with implementations for
references, arrays, linked lists, task pools, etc.

- `share/pulse/examples`: contains examples of verified Pulse code using
the library.

- `qs/`: contains the build logic to compile our QuickSort example into
OCaml5.

For any of these above directories, you can run `make -C <DIR>` to
verify all files under them.

There is also:

- `src/` `build/` `mk/`: contain source code for the Pulse checker (not
a contribution of this paper) and build infrastructure.

- `pulse2rust/`: contains the tool that translates Pulse to Rust.

- `test/`: contains Pulse unit tests.

- `artifact/`: contains Dockerfile and scripts to generate this
artifact.

- `out/`: contains the build result of PulseCore and Pulse.

## Connection to Paper Text

For every `.fst` file mentioned here, there is usually also a matching
`.fsti` with the interface for the module.

### 1.0

- Task pool: see 5.1.

### 1.1:

- The full PulseCore logic is under `lib/core`, with some interfaces in
  `lib/common`. We provide more detailed pointers below.

- The definitional interpreter is defined in
  `lib/core/PulseCore.Semantics.fst`. See 4.2 for its instantiation.

### 2.1, 2.2:

Spinlock: `lib/pulse/Pulse.Lib.SpinLock.fst`

### 3.0

- PCMs: The theory of PCMs is implemented in F\*, outside of PulseCore.
  You can find it in `ulib/FStar.PCM.fst` wherever F\* is installed (if
  using the container, `/home/ubuntu/FStar`)

- Cell, core: `lib/core/PulseCore.Heap.fsti`. Note that the F\* type for
  `cell` has an extra `erased bool` field in the code, which is not in
  the paper. This legacy feature was used to encode invariants in an
  earlier version of Pulse. It is no longer needed.

### 3.2

Our implementation of indirection theory is in
`lib/core/PulseCore.IndirectionTheory.fst`.

### 3.3

The functor for the indirection theory construction is defined in
`lib/core/PulseCore.KnotInstantiation.fst`.

These two modules are used to construct a separation logic
in `lib/core/PulseCore.IndirectionTheorySep.fst`.

### 4.1

- Actions are defined in `lib/core/PulseCore.Semantics.fst`. The type
here is a record, with pre- and postconditions fields, instead of being
indexed by them as in the paper. This is inconsequential.

- Invariant operations: defined in `lib/core/PulseCore.Atomic.fst`.
The `gather_invariant` function is named
`invariant_name_identifies_invariant`.

- `extend` is in `lib/core/PulseCore.Heap.fst`. Here, it takes an
argument for an address, which must be fresh. This is later composed
with `with_fresh_counter` in `lib/core/PulseCore.BaseHeapSig.fst` to
obtain type like the one in the paper.

- Shifts:  `lib/pulse/lib/pledge/Pulse.Lib.Shift.fst`
- Trades:  `lib/pulse/lib/pledge/Pulse.Lib.Trade.fst`
- Pledges: `lib/pulse/lib/pledge/Pulse.Lib.Pledge.fst`

### 4.2

The module `lib/core/PulseCore.Semantics.fst` contains the definition
of the `m` type, which is the `stt` type of concurrent computation
presented in the paper. The actual `stt` of PulseCore is is in
`lib/core/Pulse.Lib.Core.fst`, and defined to a universe lowering of
`m`. The the function `run` in `lib/core/PulseCore.Semantics.fst`
implements the interpreter. This development in this module is generic
over an abstract type of heaps, it is instantiated to the actual type of
memories in `lib/core/PulseCore.InstantiatedSemantics.fst`.

### 5.1

- Task pool: `lib/pulse/lib/Pulse.Lib.Task.fst`.
  The anchored references are implemented in
  `lib/pulse/lib/Pulse.Lib.AnchoredReference.fst`, the related PCM being
  in `lib/pulse/lib/Pulse.Lib.FractionalAnchoredPreorder.fst`

### 5.2

- Task-parallel Quicksort: `share/pulse/examples/Quicksort.Task.fst`,
  using lemmas from `share/pulse/examples/Quicksort.Base.fst`.
  There is also a sequential implementation in
  `share/pulse/examples/Quicksort.Sequential.fst`.

### 5.3

- Barrier: `lib/pulse/lib/Pulse.Lib.ConditionVar.fst`

### 5.4

- The DICE and DPE implementation is under `share/pulse/examples/dice`.
