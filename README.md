# Supplementary material for the paper "PulseCore: A Dependently Typed Stratified Separation Logic"

This directory contains the F* code described in the paper.
The code is anonymized, names have been redacted and some comments removed entirely.

  - `lib/pulse/core` contains the PulseCore formalization described in Sec. 3

The PulseCore formalization is written in pure F* and can be checked using `make -C lib/pulse/core`.
This requires an F* version built from a git version from July 10th 2024.

Compiling the other parts of the supplementary material requires the Pulse plugin,
which is neither part of the paper nor part of this submission.

  - `share/pulse/examples/by-example/PulseTutorial.PCMParallelIncrement.fst` contains the parallel increment from Sec. 4.1
  - `lib/pulse/lib/Pulse.Lib.ConditionVarWithCodes.fst` contains the barrier from Sec. 4.2
  - `share/pulse/examples/dice/dpe` contains the DPE implementation from Sec. 4.3
    - `pulse2rust/dpe/src` containes the Rust code extracted from this DPE implementation
