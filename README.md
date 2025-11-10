# Simplified

English | [中文版](README_CN.md) | [日本語](README_JP.md)

*Simplified* is the refactoring of the original *mainline* codebase, towards the 
easier of formal verification. It reduces the complexity of the original code and
enable the use of formal methods to verify the correctness of the code. In particular,
Verus-incompatible idioms are replaced with Verus compatible equivalents.

**NEWS: [USENIX ATC'25](https://www.usenix.org/conference/atc25) accepted two research papers on Asterinas: (1) _Asterinas: A Linux ABI-Compatible, Rust-Based Framekernel OS with a Small and Sound TCB_ and (2) _Converos: Practical Model Checking for Verifying Rust OS Kernel Concurrency_. Congratulations to the Asterinas community🎉🎉🎉**

1. **Compilable**.
2. **Simple**: remove idioms that are imcompatible with Verus, and avoid those that are challenging to verify.

## Example

The impls of `CursorMut`, found in `src/mm/frame/linked_list.rs`, have been transformed along the lines described,
mostly using the macros found in `src/mm/frame/ptr_extra.rs`. Compare these to their equivalents in *Verifiable*.
