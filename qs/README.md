# Parallel quicksort extracted to OCaml 5

This directory contains Quicksort.Task and its extracted OCaml code. The latter (in dune/_output) can be built with OCaml 5.1.1 and domainslib.

```shell
opam switch create 5.1.1
opam install --switch=5.1.1 domainslib
make
```
