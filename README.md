# Formal Verification of Asterinas with Verus

## Building the Proof Development

The ``tools/verus`` directory contains the Verus repository at tag
``release/rolling/0.2024.10.25.601e1e7``, which is guaranteed to be compatible with
the rest of the development. You can build verus with:
```bash
cargo xtask bootstrap
```

Then, run ``make`` to build the common libraries and both verification targets.
Make simply runs:

```bash
cargo xtask compile --targets vstd_extra
cargo xtask compile --targets aster_common
cargo xtask verify --targets fvt10-pt-cursor-navigation
cargo xtask verify --targets fvt11-pt-cursor-guards
```

After the first build, you may directly build one of the specific targets
with ``make fvt10`` or ``make fvt11``

## The verification targets

This repository contains two verification targets. ``fvt10-pt-cursor-navigation``
verifies the behavior of the cursor methods ``push_level``, ``pop_level``, and ``move_forward``.
The specification for these functions are defined in ``src/page_table/cursor/model.rs``, along with
the ``ConcreteCursor`` type that contains an abstract instance of a page table, represented as a tree,
as well as the path into that tree that the cursor currently points to, and the subtree found at the
end of the path. The functions themselves, and their verification, are found in ``src/page_table/cursor/mod.rs``.

Target ``fvt11-pt-guards`` extends the previous target's specification with a system of locks. Take a look at
``src/page_table/cursor/mod.rs`` and note that the proofs are much more complex, requiring multiple assertions and
lemmas. Several proof steps have been replaced by ``admit()``. Can you fill in the holes? Useful
lemmas can be found in ``src/page_table/cursor/moded.rs``
