# Switch13 Lean Artifact

This directory contains a Lean 4.29.1 artifact for a finite-state
entry/classification theorem.

The public entry point is `Switch13Package.lean`.

The main theorem is:

```lean
theorem forum_c17_global_input_to_switch13
    (source : Nat) (hodd : Odd source) :
    ForumC17GlobalInputToSwitch13 source
```

Informally, this says that for every odd `source : Nat`, the finite transition
system initialized from `source` reaches an exit state in finitely many steps,
and the exit state is classified into one of thirteen switch rows.

The proof compiles with no `sorry` or admitted steps.

## Files

- `Switch13Package.lean` - small public entry point.
- `Switch13Reachability.lean` - finite-state reachability and exit theorem.
- `Switch13Core.lean` - arithmetic lemmas, generated finite tables, and
  switch-row ledger.

## Build

From the repository root:

```bash
lake exe cache get
lake build Switch13Package
```

Toolchain: `leanprover/lean4:v4.29.1`.

## Scope

This artifact proves the finite-state entry/classification theorem above. The
thirteen switch rows are the named outputs of this entry classifier.
