# local-mech

`local-mech` is a Rocq mechanization project for the **Location Calculus (LoCal)** from Michael Vollmer's thesis, *A Language-based Approach to Programming with Serialized Data*.

The current goal is to formalize LoCal in small, focused modules, following the style used in the reference STLC developments in `materials/`.

## Current status

The repository currently contains one mechanization module:

- `LoCalSyntax.v` — a first syntax-focused draft of LoCal, including:
  - core abstract syntax (`loc_exp`, `hty`, `val`, `expr`, etc.),
  - custom entries / notation for readable terms,
  - small example expressions inspired by thesis snippets (`start`, `+1`, `after`, `letloc`, `case`).

Typing, operational semantics, and metatheory proofs are planned next.

## Build instructions

This project is driven by `_CoqProject`.

Regenerate the Coq Makefile:

```sh
coq_makefile -f _CoqProject -o Makefile
```

Build all tracked modules:

```sh
make
```

Fast check for the current module:

```sh
coqc -Q . LocalMech LoCalSyntax.v
```

### Notes on structure

- `LoCalSyntax.v` is the active mechanization entry point today.
- `materials/` contains reference/specification material and is not part of the core build target for LoCal mechanization work.
- As the project grows, this section can be expanded with separate files for:
  - typing rules,
  - dynamic semantics,
  - auxiliary lemmas/infrastructure,
  - type safety proofs.

