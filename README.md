<<<<<<< HEAD
# Verifiable

## Description

Verifiable contains all the specifications and verifiable code for the formal
verification. It converts all the syntax that is not suitable for formal verification
into the structures that can be parsed and evaluated by the formal verification tools.

## Usage

To build the Verifiable module, you need to run the following command:

```shell
cargo dv compile --targets <target1> <target2> ...
```
=======
# Next-gen

## Description

Next-gen is the refactoring of the original *mainline* codebase, towards the 
easier of formal verification. It removes the complexity of the original code and
enable the use of formal methods to verify the correctness of the code.

## Rules of Mainline

1. **Compilable**.
2. **Simple**: no complex data structures and algorithms.
>>>>>>> demo/nextgen
