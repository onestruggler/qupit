{-# OPTIONS --safe #-}

------------------------------------------------------------------------
-- Worked example: the symmetric group Sₙ as a wire-indexed circuit
-- family, built on the GENERIC structural rules of Circuit.Structure.
--
-- The point of this file is to show that a brand new group only has to
-- declare its own generators and its own *group-specific* relations.
-- The structural rules (lifting `cong↑`, and disjoint commutation with
-- their word/power lemmas) are NOT restated here: they are obtained by
-- applying `Circuit.Structure` and are proved once and for all there.
--
-- Generators: `σ` is the adjacent transposition acting on wires 0,1.
-- Group-specific (Coxeter) relations:
--     σ² = ε                             (involution)
--     σ σ' σ = σ' σ σ'                   (braid, σ' = σ on wires 1,2)
--     σ commutes with far generators     (disjoint support)
------------------------------------------------------------------------

module Circuit.Example.Sn where

open import Data.Nat using (ℕ ; suc ; zero)
open import Word.Base
import Presentation.Base as PB

------------------------------------------------------------------------
-- Generators of the family.  Exactly the same shape as Clifford's
-- `Gen`: named bottom gates plus the generic shift `_↥`.

infixl 10 _↥

data Gen : ℕ → Set where
  σ-gen : ∀ {n} → Gen (suc (suc n))          -- transposition on wires 0,1
  _↥    : ∀ {n} → Gen n → Gen (suc n)          -- shift onto a later wire

------------------------------------------------------------------------
-- Apply the generic framework.  This single line is the whole reuse:
-- it brings `_↑`, `Lifted`, `lemma-lift`, `comm-along`, `comm-along-^`
-- into scope for THIS group, already proved.

open import Circuit.Structure {Gen} _↥

-- The transposition as a one-letter word (polymorphic in extra wires).
σ : ∀ {n} → Word (Gen (suc (suc n)))
σ = [ σ-gen ]ʷ

-- Embedding of "far" generators, i.e. gates on wires ≥ 2, disjoint from
-- σ's support {0,1}.
↥↥ : ∀ {n} → Gen n → Gen (suc (suc n))
↥↥ g = g ↥ ↥

------------------------------------------------------------------------
-- GROUP-SPECIFIC relations only.  No `cong↑`, no per-gate `comm`
-- boilerplate for whole words — just the mathematical content of Sₙ.

data Rel : (n : ℕ) → WRel (Gen n) where
  invol : ∀ {n}         → Rel (suc (suc n))       (σ • σ)           ε
  braid : ∀ {n}         → Rel (suc (suc (suc n))) (σ • σ ↑ • σ)     (σ ↑ • σ • σ ↑)
  far-σ : ∀ {n} {g : Gen n}
                        → Rel (suc (suc n))       (σ • [ ↥↥ g ]ʷ)   ([ ↥↥ g ]ʷ • σ)

-- The presentation actually reasoned in is R closed under lifting.
Sₙ : (n : ℕ) → WRel (Gen n)
Sₙ = Lifted Rel

------------------------------------------------------------------------
-- Consequences obtained FOR FREE from the framework.

module _ {n} where
  open PB (Sₙ (suc (suc n)))

  -- (a) σ commutes with an ARBITRARY subcircuit `w` on the far wires.
  --     Group-specific input: only the one-generator fact `far-σ`.
  --     The induction on `w` comes from the generic `comm-along`.
  σ-comm-w : ∀ (w : Word (Gen n)) →
             σ • wmap ↥↥ w ≈ wmap ↥↥ w • σ
  σ-comm-w = comm-along ↥↥ (Sₙ (suc (suc n))) σ (λ g → axiom (base far-σ))

  -- (b) …and so does every power σ ^ k (here only 0 and 1 are non-trivial
  --     since σ² = ε, but the generic lemma does not know that).
  σ^-comm-w : ∀ k (w : Word (Gen n)) →
              (σ ^ k) • wmap ↥↥ w ≈ wmap ↥↥ w • (σ ^ k)
  σ^-comm-w = comm-along-^ ↥↥ (Sₙ (suc (suc n))) σ (λ g → axiom (base far-σ))

-- (c) The lifting rule, also for free: the involution relation, valid on
--     (2+n) wires, is automatically valid one wire up.
σ²-lifted : ∀ {n} →
  let open PB (Sₙ (suc (suc n)))       using ()  renaming (_≈_ to _≈₀_) in
  let open PB (Sₙ (suc (suc (suc n)))) using ()  renaming (_≈_ to _≈₁_) in
  (σ • σ) ↑ ≈₁ ε ↑
σ²-lifted {n} = lemma-lift Rel (σ • σ) ε (PB.axiom (base invol))
