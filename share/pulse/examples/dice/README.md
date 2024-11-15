# Verified DPE in Pulse

This directory contains a verified DPE (DICE Protection 
Environment) in Pulse. The implementation of the DICE Engine and Layer 0 is based 
on a verified DICE implementationin in Low* called [DICE*](https://github.com/verified-HRoT/dice-star) 
(dice-star). The implementation of DPE is based on the 
[DPE specification](https://trustedcomputinggroup.org/wp-content/uploads/TCG-DICE-Protection-Environment-Specification_14february2023-1.pdf)
provided by the Trusted Computing Group. 

```
dpe/
  DPETypes.fsti               (* types for DPE state *)
  DPE.fst(i)                  (* DPE commands *)
engine/
  EngineTypes.fst(i)          (* types for engine state *)
  EngineCore.fst              (* engine logic *)
l0/
  L0Types.fst(i)              (* types for layer 0 state *)
external/
  c/hacl/                     (* C API for HACL* *)
  hacl/                       (* Pulse API for HACL* *)
  l0/                         (* Pulse API for DICE* (layer 0 logic) *)
  HACL.fst                    (* abstraction of HACL* API *)
_output/c/
  DPE.c                       (* Extracted C code from DPE *)
  EverCrypt_Base.h            (* Extracted C code for the EverCrypt API *)
  HACL.*                      (* Extracted C code for the HACL* API *)
  krmlinit.c                  (* Extracted C code for global state initialization *)
```
