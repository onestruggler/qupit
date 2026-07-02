# `Circuit.Structure` — generic structural rules for wire-indexed circuits

A wire-indexed circuit family is a generator family `Gen : ℕ → Set` plus a
shift `_↥ : Gen n → Gen (suc n)` that moves a gate onto a later wire.
Clifford circuits (`N/Symplectic.agda`) and the symmetric group
(`Circuit/Example/Sn.agda`) are two instances.

Every such family shares the **same structural rules**, independent of the
group-specific relations. `Circuit.Structure` provides them once:

| Concept | Old (per-group, in `N/Symplectic.agda`) | New (generic, proved once) |
|---|---|---|
| lift a word | `_↑` | `_↑` |
| lift a relation | `cong↑` constructor inside `_QRel,_===_` | `lift↑` constructor of `Lifted R` |
| lift the closure | `lemma-cong↑` | `lemma-lift R` |
| gate ∥ far word | `lemma-comm-S-w↑`, `lemma-comm-H-w↑`, `lemma-comm-CZ-w↑` | `comm-along e Γ` |
| gate^k ∥ far word | `lemma-comm-Sᵏ-w↑`, `lemma-comm-Hᵏ-w↑`, … | `comm-along-^ e Γ` |

## How to define a new group

```agda
open import Circuit.Structure {MyGen} _↥        -- ← the whole reuse

data MyRel : (n : ℕ) → WRel (MyGen n) where
  ...only group-specific relations...           -- no cong↑, no whole-word comm
  comm-c : ... [ g ↥ ]ʷ • c === c • [ g ↥ ]ʷ    -- only the one-GENERATOR base fact

MyPresentation = Lifted MyRel
```

Then `lemma-lift`, `comm-along`, `comm-along-^` are available already proved.
See `Circuit/Example/Sn.agda` for a complete, type-checked instance.

## Migration status for `N/Symplectic.agda`

**Done (safe delegation).** The primary `module Lemmas-Sym` now imports
`Circuit.Structure {Gen} _↥` and its derived lemmas are one-liners over the
framework — the datatype and every public name/type are unchanged, so all
downstream importers still typecheck:

```agda
lemma-cong↑    {n} w v = lift-closure (λ m → (m QRel,_===_)) cong↑ w v
lemma-comm-S-w↑  {n} w = comm-along   (λ g → g ↥)   ((₂₊ n) QRel,_===_) S  (λ g → sym (axiom comm-S))  w
lemma-comm-Sᵏ-w↑ {n} k w = comm-along-^ (λ g → g ↥) ((₂₊ n) QRel,_===_) S  (λ g → sym (axiom comm-S))  k w
lemma-comm-H-w↑  {n} w = comm-along   (λ g → g ↥)   ((₂₊ n) QRel,_===_) H  (λ g → sym (axiom comm-H))  w
lemma-comm-CZ-w↑ {n} w = Eq.subst … (WP.wmap-∘ {g = _↥} {f = _↥} w)
                           (comm-along (λ g → g ↥ ↥) ((₃₊ n) QRel,_===_) CZ (λ g → sym (axiom comm-CZ)) w)
```

The `sym` is because the `comm-*` axioms are oriented `[ g ↥ ]ʷ • c === c • [ g ↥ ]ʷ`
while `comm-along` wants `c • [ e g ]ʷ ≈ [ e g ]ʷ • c`. CZ (arity 2) needs the
`wmap-∘` fusion to bridge `w ↑ ↑` with the double embedding `λ g → g ↥ ↥`.

**All three copies delegated.** The same delegation is applied to the two
further near-duplicate copies of these lemmas — in `module Symplectic-Derived-Gen`
(its own parameterised gens) and in `module Lemmas` (`Powers-Symplectic`, which
`open`s the primary `Symplectic`). Each gets its own
`open import Circuit.Structure {Gen} _↥`.

## Why comm-H/S/CZ can NOT be turned into lemmas here

We attempted to pull `comm-H/S/CZ` *out* of `_QRel,_===_` — replacing them with a
single generic `disj` axiom (`arity-b`/`embed-b` à la `Circuit.Arity`) and
re-deriving `comm-H/S/CZ` as instances. This is **infeasible** in this codebase:

- `disj` must index the wire count by `arity-b b Nat.+ n`. A function application
  in an index is *green slime*: when a downstream proof matches a concrete
  instance (`disj bgH {g = S-gen}` in `lemma-dual`), Agda cannot invert the index
  and fails with **`SplitError.UnificationStuck`**.
- The `--safe` total proofs `lemma-dual`, `lemma-act-cong-ax`, and the
  `*-well-defined` families rely on `comm-H`, `comm-S`, `comm-CZ` being *distinct,
  fixed-arity constructors*. No single arity-indexed axiom (whether exposed as a
  lemma or a pattern synonym — both reduce to `disj`) can replace them without
  rewriting those proofs.

So `comm-H/S/CZ` stay as primitive constructors. The generic disjoint scheme
lives instead in `Circuit.Arity` (`disj` + `gate-comm-word`), where it is used by
*new* groups that never pattern-match their axioms — see `Example/SnArity.agda`.

## Optional deeper layer

`comm-H/comm-S/comm-CZ` still name specific gates, so they stay group-specific.
To make even those generic, extend the signature with a per-generator *arity*
and a single scheme "a bottom gate of arity `a` commutes with any generator
lifted `≥ a` times" (disjoint support). That removes the last per-gate
boilerplate at the cost of arity bookkeeping in the generator type.
