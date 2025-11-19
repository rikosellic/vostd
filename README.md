# Verified

## Description

*Verified* holds all the code verification for the *verifiable* base. Specifications for the verification targets live in `specs`.

## Usage

To build the Verified module, you need to run the following command:

```shell
cargo dv verify --targets <target1> <target2> ...
```

## Example

Continuing our examples of `CursorMut` members from the *verifiable* branch, consider the proof of `CursorMut::move_next`.
