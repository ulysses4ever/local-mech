# local-mech

[![Rocq build](https://github.com/ulysses4ever/local-mech/actions/workflows/rocq-build.yml/badge.svg)](https://github.com/ulysses4ever/local-mech/actions/workflows/rocq-build.yml)

`local-mech` is a Rocq mechanization project for the **Location Calculus (LoCal)** from Michael Vollmer's thesis, *A Language-based Approach to Programming with Serialized Data*.

The current goal is to formalize LoCal in small, focused modules, following the style used in the reference STLC developments in `materials/`.

## Current status

The repository currently contains one mechanization module:

- `LoCalSyntax.v` — a first syntax-focused draft of LoCal, including:
  - core abstract syntax (`loc_exp`, `ty`, `val`, `expr`, etc.),
  - custom entries / notation for readable terms,
  - small example expressions inspired by thesis snippets (`start`, `+1`, `after`, `letloc`, `case`).

Typing, operational semantics, and metatheory proofs are planned next.

## Build instructions

This project targets **Rocq 9+** and is driven by `_CoqProject`.

Generate `Makefile` and build:

```sh
rocq makefile -f _CoqProject -o Makefile && make
```

### Notes on structure

- `LoCalSyntax.v` is the active mechanization entry point today.
- `materials/` contains reference/specification material and is not part of the core build target for LoCal mechanization work.
- As the project grows, this section can be expanded with separate files for:
  - typing rules,
  - dynamic semantics,
  - auxiliary lemmas/infrastructure,
  - type safety proofs.
