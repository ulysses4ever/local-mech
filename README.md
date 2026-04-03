# local-mech

[![Rocq build](https://github.com/ulysses4ever/local-mech/actions/workflows/rocq-build.yml/badge.svg)](https://github.com/ulysses4ever/local-mech/actions/workflows/rocq-build.yml)

`local-mech` is a Rocq mechanization project for the **Location Calculus (LoCal)** from Michael Vollmer's thesis, *A Language-based Approach to Programming with Serialized Data*.

The current goal is to formalize LoCal in small, focused modules, following the style used in the reference STLC developments in `materials/`.

## Current status

The repository contains four mechanization modules (in dependency order):

- `LoCalSyntax.v` — core abstract syntax for LoCal, including:
  - identifier wrapper types (`loc_var`, `region_var`, `term_var`, etc.),
  - abstract syntax types (`loc_exp`, `ty`, `val`, `expr`, `pat`, `fdecl`, etc.),
  - custom notation entries for readable terms,
  - small example expressions inspired by thesis snippets.

- `LoCalStatic.v` — the LoCal type system (thesis §2.2.1), including:
  - typing environment definitions (Γ, Σ, C, A, N),
  - the `has_type` inductive judgment threading input/output alloc and nursery environments,
  - typing rules for all expression forms: variables, `let`, `letregion`, `letloc`, data constructors, `case`, and function application.

- `LoCalDynamic.v` — the small-step operational semantics (thesis §2.2.2), including:
  - runtime structures: store, location map, concrete addresses,
  - the `step` relation (`S ; M ; e ⇒ S' ; M' ; e'`),
  - multi-step closure (`multi_step`),
  - auxiliary definitions: substitution, `end_witness`, `field_starts`.

- `LoCalSafety.v` — type safety (thesis §2.2.3 and Appendix A), including:
  - store well-formedness (`store_wf`), covering map-store consistency, constructor-application well-formedness, and allocation well-formedness,
  - **Progress** — proved: a well-typed expression in an empty variable environment is a value or can step,
  - **Preservation** — stated with a detailed proof sketch, admitted pending the substitution lemma,
  - **Type Safety** — stated, follows from Progress and Preservation (admitted).

## Build instructions

This project targets **Rocq 9+** and is driven by `_CoqProject`.

Generate `Makefile` and build:

```sh
rocq makefile -f _CoqProject -o Makefile && make
```

### Building with Nix

A `shell.nix` is provided that pulls `rocq-core` and `rocqPackages.stdlib` from `nixpkgs-unstable`. To enter a shell with all dependencies available:

```sh
nix-shell
```

Then run the build as usual:

```sh
rocq makefile -f _CoqProject -o Makefile && make
```

### Notes on structure

- `materials/` contains reference/specification material (STLC developments, the thesis) and is not part of the core build target for LoCal mechanization work.
- The four `.v` files follow the style of `materials/References.v`: small inductive definitions, custom notation scopes, and explicit constructors for runtime artifacts.
