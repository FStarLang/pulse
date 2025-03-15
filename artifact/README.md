FIXME: There are many warnings about Reference.free/alloc being unsound,
can we fix them?

# PulseCore artifact (PLDI 2025)

The artifact includes:

- The implementation of the PulseCore logic.
- The implementation of the Pulse checker (not a contribution of the
  paper).
- The examples from the paper, in Pulse.

# Getting Started (with code-server)

The artifact is a docker container that starts a vscode server on port 8080.

 1. To run this container you first need to load it:

  docker load < pulsecore-pldi2025-docker.tar.gz

 2. Then you can start it:

  docker run -p 127.0.0.1:8080:8080 -it pulsecore-pldi2025

 3. You can now access the vscode server at http://localhost:8080

# Getting Started

We provide three options to use our artifact

- Devcontainer in VS code. We recommend this to get an interactive
  experience.
- Using the shell in Docker.
- Building from source.

After any of these options, you should be able to run

    $ ./pulse.sh share/pulse/examples/Quicksort.Task.fst
    Verified module: Quicksort.Task
    All verification conditions discharged successfully

And get a successful verification (you may see Warning 241 about not
being able to load checked dependencies--- this is fine). The `pulse.sh`
script is just a wrapper to pass the required options to F*.

If you see an error like

    * Error 168 at Quicksort.Task.fst:18.11-18.11:
      - Unknown language extension pulse

it indicates that the Pulse checker has not been built, this should not
happen in the containers. If building from source, make sure that `make`
succeeded.

## Using a Devcontainer and VS Code

The artifact contains a devcontainer specification, that can be used to
easily drop into a development environment with all needed dependencies.
The devcontainer is configured to use the same Docker image provided in
this artifact. Since it is not published to a container storage, you
need to first load the provided Docker image into your system

    $ docker load < pulsecore-pldi2025-docker.tar.gz

and then extract the source package (`pulsecore-pldi2025-src.tar.gz`)

    $ tar xzf pulsecore-pldi2025.tar.gz

This will create the pulsecore/ directory with the artifact
contents. You can now open this directory in VS Code (or another
devcontainer-capable editor) and tell it to use the devcontainer (see
`.devcontainer/devcontainer.json` for its definition). VS Code will
usually prompt you about it, but otherwise can be done via Ctrl-Shift-P
and "Dev Containers: Rebuild and Reopen in Container".

Once done, you should be able to open F* files in the artifact
and immediately be able to verify them interactively. This link
https://github.com/FStarLang/fstar-vscode-assistant/?tab=readme-ov-file#features-and-basic-usage-guide
contains an explanation on how to use the F* mode in VS Code.

**NOTE:** the devcontainer user has a UID of 1000. VS code will bind
mount your workspace (i.e. a directory in your own host system) into the
container, usually somewhere under `/workspaces`, without remapping any
UIDs. If the UID of your host user is different, it is possible that
you will not be able to read/write any of the workspace files while
inside the container. You can, externally, run `chmod -R ugo+rw` over
the artifact to prevent this.

There will also be an artifact checkout in `/home/ubuntu`, as this uses
the same Docker container as the option below. You can ignore the one in
`/home/ubuntu` if you choose this option.

## Running in Docker

To run the provided image purely in Docker, you need to first load the
image into Docker

    $ docker load < pulsecore-pldi2025-docker.tar.gz

and run it, which should drop to a shell. The contents of the artifact
proper are under the `pulsecore/` directory. Dependencies (FStar and
karamel) are installed too.

    $ docker run -it pulsecore-pldi2025
    user@10693fcfc3bd:~$ ls
    FStar  karamel  pulsecore
    user@10693fcfc3bd:~$ ls pulsecore/
    CONTRIBUTING.md   Pulse.fst.config.json  lib         pulse.sh    src
    CONTRIBUTORS.txt  README.md              mk          pulse2rust  test
    LICENSE           artifact               out         qs
    Makefile          build                  pulse.opam  share

The pulsecore/ has a fully-built checkout of the PulseCore logic, the
Pulse checker, and the examples in the paper (and more).

To verify a particular file, you can run `./pulse.sh -f
path/to/file.fst` (`-f` makes sure F* does it, even if the respective
`.checked` exists). You can also run `make clean` and remove the `out`
directory (this removes every built object) and run `make` to start the
build and verification process, which will verify every file.

## Building from source

If desired, Pulse can be built from source. But we do not recommend this
as it is very much sensitive to versions of F* and KaRaMeL involved. To
do so, you can follow the instructions in `pulsecore/README.md`.

FIXME: instructions, or just remove. We should write down commit hashes
if we want this.

# Step-by-Step Guide

We provide some broad comments here and then more details.

By having build Pulse by any of the methods above, the PulseCore logic
has already been fully verified. The Pulse standard library (including
spinlocks, linked list, task pool, etc) has also been verified.
To check all the examples in the artifact, covering those mentioned
in the paper, you can run `make test-share`. To build and run
the task-parallel Quicksort, run `make test-qs`.

## Structure of the Artifact

- `lib/common` and `lib/core`: contain the F* definitions for the
PulseCore logic. This directories can be checked fully by running 'make
lib-core'. There is no imperative Pulse code here, only pure F*

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
  `lib/core/PulseCore.Semantics.fst`, and instantiated

### 2.1, 2.2:

Spinlock: lib/pulse/Pulse.Lib.SpinLock.fst

### 3.0

- PCMs: The theory of PCMs is implemented in F*, outside of PulseCore.
  You can find it in `ulib/FStar.PCM.fst` wherever F* is installed (if
  using the container, `/home/ubuntu/FStar`)

- Cell, core: `lib/core/PulseCore.Heap.fsti`

FIXME: cell has a meta: erased bool in code but not in paper.

### 3.2

Our implementation of indirection theory is in
`lib/core/PulseCore.IndirectionTheory.fst`.

### 3.3

The functor for the indirection theory construction is defined in
`lib/core/PulseCore.KnotInstantiation.fst`.

### 4.0


These two modules are used to construct a separation logic
in `lib/core/PulseCore.IndirectionTheorySep.fst`.

lib/core/PulseCore.IndirectionTheoryActions.fst

### 4.1

- Shifts:  `lib/pulse/lib/pledge/Pulse.Lib.Shift.fst`
- Trades:  `lib/pulse/lib/pledge/Pulse.Lib.Trade.fst`
- Pledges: `lib/pulse/lib/pledge/Pulse.Lib.Pledge.fst`

### 4.2

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
- You can build and run this implementation by following the
  instructions in the `qs/` directory (in the container, `make run`
  should do it).

### 5.3

- Barrier: `lib/pulse/lib/Pulse.Lib.ConditionVar.fst` FIXME: naming

### 5.4

- The DICE and DPE implementation is under `share/pulse/examples/dice`.
