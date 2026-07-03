# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project Overview

This is the Agda formalisation accompanying the paper *"A Complete and Natural Rule Set for Multi-Qudit Clifford Circuits in All Odd Prime Dimensions"*. It is being prepared for submission to the Agda standard library. Tested with **Agda 2.8 + stdlib 2.3** (also works with Agda 2.7 + stdlib 2.2).

## Typechecking

```bash
# Typecheck a single file via WSL (Agda 2.8, resolves dependencies automatically)
wsl --exec /home/onest/.cabal/bin/agda Examples/CliffordT1.agda
wsl --exec /home/onest/.cabal/bin/agda Examples/QutritCliffordT1.agda
wsl --exec /home/onest/.cabal/bin/agda Zp/Mod-Lemmas.agda
```

Use WSL Agda 2.8 (`wsl --exec /home/onest/.cabal/bin/agda`) for all files. The Windows install (Agda 2.6.5 nightly at `C:\Users\onest\Downloads\Agda-nightly-win64\Agda-nightly\bin\agda.exe`) is outdated and cannot typecheck `Zp/` files because `Tactic.RingSolver` requires Agda 2.8.

The WSL install uses its own stdlib at `/home/onest/.agda/lib/agda-stdlib/`. The `.agda-lib` file (`qupit.agda-lib`) includes `.` and depends on `standard-library`.

## Architecture

The library is layered bottom-up:

### Layer 1 — Free Monoid (`Word/`)
- **`Word/Base.agda`**: The `Word X` type (free monoid over generators `X`): constructors `[_]ʷ`, `ε`, `_•_`. Also defines `wmap`, `wconcat`, `wfoldr`, `wfoldl`, `_*` (extend a function on generators to words), `_**`/`_⋆⋆` (stateful fold variants for coset enumeration), `WRel X = Rel (Word X) 0ℓ`.
- **`Word/Properties.agda`**: `wmap`-fusion lemmas, `≡-dec` (decidable equality), `lemma-f*-w^n`, and deprecated aliases.

### Layer 2 — Group Presentations (`Presentation/`)
- **`Presentation/Base.agda`**: Parameterised by a relation `Γ : WRel X`. Defines `_≈_` as the congruence closure of `Γ` extended with monoid axioms (refl/sym/trans/cong/assoc/left-unit/right-unit/axiom). `Alphabet = X`. Also helper combinators `cleft_`, `cright_`, `_reversed`.
- **`Presentation/Properties.agda`**: Proves `_≈_` is an `IsEquivalence`; builds `Setoid`, `Magma`, `Semigroup`, `Monoid` bundles. Contains the `mod-assoc`/`by-assoc` tactic (normalise associativity via list roundtrip), `NFProperty`/`NFProperty'`/`SNFProperty`/`AlmostNFProperty` records, and extensive word-power lemmas (`^`, `^'`, `lemma-^^`, `lemma-^-+`, etc.).
- **`Presentation/Morphism.agda`**: Parameterised by two presentations `Γ`, `Δ`. Contains `Star-Congruence`, `Congruence`, `StarHomomorphism`, `GenHomomorphism`, `StarMonomorphism`, `StarIsomorphism`, `StarGroupHomomorphism` — all building `IsMonoidHomomorphism`/`IsMonoidMonomorphism`/`IsMonoidIsomorphism` witnesses from generator-level data.
- **`Presentation/Reidemeister-Schreier.agda`**: The core injectivity/surjectivity engine. `Star-Injective-Simplified` proves `f*` is injective given a left inverse `g` on generators. `Star-Surjective` proves surjectivity.
- **`Presentation/CosetNF.agda`**: Coset normal form construction. Given a right action `h : C → Y → Word X × C` (coset table) and a section `[_] : C → Word Y`, constructs an `NFProperty` for the larger presentation using Reidemeister–Schreier.
- **`Presentation/GroupLike.agda`**: `Grouplike` record capturing group-like axioms (inverses), and `Group-Lemmas` proving uniqueness of inverses and congruence.

### Layer 3 — Constructions (`Presentation/Construct/`)
- **`Base.agda`**: Amalgamated product construction `_⊕_` on `WRel`.
- **`Properties/DirectProduct.agda`**, **`SemiDirectProduct.agda`**, **`NDirectProduct.agda`**: Lifts `NFProperty` through products.
- **`Properties/Amalgamation.agda`**: Amalgamated free product with coset NF.

### Layer 4 — Specific Groups (`Presentation/Groups/`)
- **`Cyclic.agda`**: Cyclic group ℤ/nℤ presentation and `NFProperty`.
- **`Sn.agda`**: Symmetric group Sₙ via the Reidemeister–Schreier method inductively. Exports `pres n`, `nfp n`.
- **`SnD.agda`**: Wreath-product / direct-product extensions of Sₙ.
- **`Trivial.agda`**: Trivial group presentation.
- **`Clifford1.agda`**, **`Clifford2.agda`**: Clifford group presentations (qubit case).
- **`S16*.agda`**, **`Symplectic2-Lemmas.agda`**: Specialised presentations for the paper.

### Layer 5 — Examples (`Examples/`)
- **`CliffordT1.agda`**: Proves completeness for the qubit Clifford+T gate set.
- **`QutritCliffordT1.agda`**: Proves completeness for the qutrit Clifford+T gate set.
- **`U33Di.agda`**: Proves the group U₃(ℤ[½,i]) is isomorphic to a given presentation. Requires the external `CliffordCCS` library (not in this repo).

### Research files (`N/`)
Large collection of in-progress files for the multi-qudit case. Not yet part of the clean library layer.

## Key Conventions (existing codebase)

- `_===_` always means the raw relation (the axioms); `_≈_` always means the congruence closure.
- `[_]ʷ` injects a generator into `Word`. `[_]ₗ`/`[_]ᵣ` are used for left/right embeddings in products.
- `(f *)` extends `f : X → Word Y` to `Word X → Word Y` via `wconcat ∘ wmap f`.
- `nfp` is the standard name for an `NFProperty` witness.
- `by-equal-nf` proves `w ≈ v` from `nf w ≡ nf v`; `by-assoc` proves `w ≈ v` from `to-list w ≡ to-list v`.

## Stdlib compatibility notes

- `Homomorphic₂` is imported from `Relation.Binary.Morphism.Definitions` (re-exported `Congruent`). That module is parameterised by `A B : Set`, so `A`/`B` are implicit at the call site — do **not** pass them explicitly.
- `IsMagmaHomomorphism` uses field `∙-homo` (renamed from `homo` in stdlib v3.0).
- `Data.Product.Relation.Binary.Pointwise.Dependent` is from stdlib master; it may not exist in older releases.
