# Copilot Instructions

## Overview

This project is a Rocq (formerly Coq) mechanization effort for the Location Calculus (LoCal) from Michael Vollmer's thesis *"A Language-based Approach to Programming with Serialized Data"*.

The thesis (`thesis.tex`) and the provided STLC developments (`Stlc.v`, `StlcProp.v`, `References.v`) are **reference material only** and are not built as part of project workflow, they live inside `materials` subdirectory. `References.v` (STLC with references/store typing) is the primary style reference for the LoCal mechanization.

Current mechanization entry point: `LoCalSyntax.v` (initial LoCal syntax draft).

## Rocq Project Setup

- `_CoqProject` defines a single logical root:
  - `-Q . LocalMech`
- Tracked files currently include:
  - `LoCalSyntax.v`

Use `LocalMech` as the root namespace for new files/modules.

## Build and Typecheck (Rocq)

Typechecking must pass after every meaningful change.

- Generate the project `Makefile` from `_CoqProject`:
  - `coq_makefile -f _CoqProject -o Makefile`
- Build all tracked modules:
  - `make`
- Build one module:
  - `make LoCalSyntax.vo`
- Fast direct check for a single file:
  - `coqc -Q . LocalMech LoCalSyntax.v`

When adding new `.v` files, add them to `_CoqProject` (in dependency order), regenerate `Makefile`, and rerun `make`.

## Thesis Structure (reference material)

All content lives in `thesis.tex`. The relevant chapters:

- **Introduction** (`\label{chapter:intro}`, line ~819)
- **The Location Calculus** (`\label{chapter:local}`, line ~1337) — formal grammar, type system, operational semantics, extensions
- **The Gibbon Compiler** (`\label{chapter:gibbon}`, line ~2580) — inference, compilation, evaluation
- **Type Safety Proof** (`\label{appendix:proof}`, line ~4003) — this is the primary target for mechanization

Document class: `iuphd` (Indiana University PhD thesis class).

## Key Thesis Macros (for reading `thesis.tex`)

### System names
| Macro | Meaning |
|---|---|
| `\sysname`, `\ourcalc` | LoCal — the main calculus |
| `\lamadt` | HiCal — the high-level source calculus |
| `\lamcur` | NoCal |

### Grammar / math notation
- `\keywd{x}` — math-italic metavariable or syntactic category
- `\gramwd{x}` — `\texttt{x}` concrete grammar terminal
- `\gramdef` / `\gramor` — `::=` / `|`
- Type environment shorthands: `\LENV` (location env), `\RENV` (region env), `\CENV` (constructor env), `\TENV` (`Γ` value env), `\SENV` (store), `\FENV` (function env), etc.
- Substitution: `\subst{e}{x}{v}` means `e[v/x]`

### Judgement forms
- `\ewitness{L}{R}{C}{e}` — end-witness judgement
- `\storewf{...}` — store well-formedness
- `\tcfun`, `\tcpat`, `\tcts` — typing judgements for functions, patterns, task sets

### Proof rule names (macros for rule labels)
e.g. `\tdatacon`, `\dletloctag`, `\dcase`, `\tprogram`, `\tllafter`, `\tlregion`, etc. These correspond directly to the inference rules in the type safety proof.

### Theorem environments
- `theorem`, `lemma` — numbered by section
- `ncase` (Case), `subcase` (SubCase), `bcase` (unnumbered Case)
- `nproof` (Proof), `proofsketch` (Proof Sketch)
- `goal` (Obl.) — proof obligation, unnumbered

## Code Listings in the Thesis

The `code` environment is Haskell-like with math escape (`@...@`). Literate replacements: `->` → `→`, `=>` → `⇒`, `forall` → `∀`, `exists` → `∃`. The `\il{...}` command is used for inline code snippets.

## Working Conventions for This Repository

- Treat `thesis.tex` as the source specification; do not add LaTeX build steps to instructions or automation.
- Reuse modeling style from `References.v` when defining syntax and later semantics:
  - small inductive definitions,
  - custom entries/scopes for readable concrete syntax,
  - explicit constructors for runtime artifacts (e.g., locations).
- Keep LoCal mechanization in separate files (e.g., `LoCalSyntax.v`, then typing/semantics/proofs in follow-up files) rather than modifying STLC reference developments.
