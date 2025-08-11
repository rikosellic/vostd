# Simplified

## Description

*Simplified* is the refactoring of the original *mainline* codebase, towards the 
easier of formal verification. It reduces the complexity of the original code and
enable the use of formal methods to verify the correctness of the code. In particular,
Verus-incompatible idioms are replaced with Verus compatible equivalents.

## Rules of Mainline

1. **Compilable**.
2. **Simple**: remove idioms that are imcompatible with Verus, and avoid those that are challenging to verify.

## Example

The impls of `CursorMut`, found in `src/mm/frame/linked_list.rs`, have been transformed along the lines described,
mostly using the macros found in `src/mm/frame/ptr_extra.rs`. Compare these to their equivalents in *Verifiable*.
