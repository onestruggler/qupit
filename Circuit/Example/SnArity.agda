{-# OPTIONS --safe #-}

------------------------------------------------------------------------
-- Sₙ again, now on the DEEPER layer (Circuit.Arity).
--
-- Compare with Circuit/Example/Sn.agda: there, the group still had to
-- declare `far-σ` (σ commutes with far generators).  Here the group's
-- relation type `Rel` contains ONLY the genuine Coxeter content
-- (involution + braid) — disjoint commutation is generated for free
-- from the arity annotation of σ.
------------------------------------------------------------------------

module Circuit.Example.SnArity where

open import Data.Nat using (ℕ ; suc ; zero ; _+_)
open import Data.Sum using (inj₁ ; inj₂)
open import Word.Base
import Presentation.Base as PB

-- Generators: transposition σ on wires 0,1, plus the generic shift.
infixl 10 _↥
data Gen : ℕ → Set where
  σ-gen : ∀ {n} → Gen (suc (suc n))
  _↥    : ∀ {n} → Gen n → Gen (suc n)

-- The bottom-gate signature: one named gate σ, of arity 2.
data BottomS : Set where σ* : BottomS

arityS : BottomS → ℕ
arityS σ* = 2

embedS : (b : BottomS) → ∀ {n} → Gen (arityS b + n)
embedS σ* = σ-gen

-- Apply the deeper framework.  One line brings in _↑, Lifted,
-- lemma-lift, comm-along, liftⁿ, Disj, _+Disj, Pres, gate-comm-word, …
open import Circuit.Arity {Gen} _↥ BottomS arityS embedS public

σ : ∀ {n} → Word (Gen (suc (suc n)))
σ = [ σ-gen ]ʷ

------------------------------------------------------------------------
-- GROUP-SPECIFIC relations: ONLY the Coxeter relations.
-- No commutation axiom, no lifting axiom.

data Rel : (n : ℕ) → WRel (Gen n) where
  invol : ∀ {n} → Rel (suc (suc n))       (σ • σ)       ε
  braid : ∀ {n} → Rel (suc (suc (suc n))) (σ • σ ↑ • σ) (σ ↑ • σ • σ ↑)

------------------------------------------------------------------------
-- Everything structural is now free.

-- (a) σ commutes with an arbitrary subcircuit on the far wires — with
--     ZERO commutation input from the group.
σ-comm-w : ∀ {n} (w : Word (Gen n)) →
  let open PB (Pres Rel (2 + n)) using (_≈_) in
  σ • wmap (liftⁿ 2) w ≈ wmap (liftⁿ 2) w • σ
σ-comm-w {n} = gate-comm-word Rel σ* {n}

-- (b) and every power σ ^ k likewise.
σ^-comm-w : ∀ {n} k (w : Word (Gen n)) →
  let open PB (Pres Rel (2 + n)) using (_≈_) in
  (σ ^ k) • wmap (liftⁿ 2) w ≈ wmap (liftⁿ 2) w • (σ ^ k)
σ^-comm-w {n} k = gate-comm-word-^ Rel σ* {n} k

-- (c) lifting is free as before.
σ²-lifted : ∀ {n} →
  let open PB (Pres Rel (suc (suc n)))       using ()  renaming (_≈_ to _≈₀_) in
  let open PB (Pres Rel (suc (suc (suc n)))) using ()  renaming (_≈_ to _≈₁_) in
  (σ • σ) ↑ ≈₁ ε ↑
σ²-lifted {n} = lemma-lift (Rel +Disj) (σ • σ) ε (PB.axiom (base (inj₁ invol)))
