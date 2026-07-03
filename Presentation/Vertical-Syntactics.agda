------------------------------------------------------------------------
-- The Agda standard library
--
-- Inductively defined circuits with structural congruence rules
------------------------------------------------------------------------

{-# OPTIONS --safe #-}

open import Data.Nat
open import Level using (0ℓ ; _⊔_)
open import Relation.Binary using (Rel)

open import Word.Base
open import Notations
import Presentation.Horizontal-Syntactics as PB

module Presentation.Vertical-Syntactics (Gate : ℕ → Set) where

private
  variable
    n m k : ℕ

------------------------------------------------------------------------
-- Generators and circuits

-- Gen n: a single-step generator on exactly n wires.
-- gate₁ h acts on the bottom 1 wire of a (₁₊ k)-wire circuit;
-- gate₂ h acts on the bottom 2 wires of a (₂₊ k)-wire circuit.
-- _↥ shifts any generator up by one wire.
--
-- Indices begin with suc (no top-level addition) so Agda's coverage
-- checker can solve unification goals by injectivity of ₁₊ alone,
-- avoiding stuck Diophantine equations of the form arity + k ≟ target.
data Gen : ℕ → Set where
  gate₁ : Gate 1 → Gen (₁₊ n)
  gate₂ : Gate 2 → Gen (₂₊ n)
  _↥   : Gen n → Gen (₁₊ n)

Circuit : ℕ → Set
Circuit n = Word (Gen n)

-- A relation on n-wire circuit.
CRel : ℕ → Set₁
CRel n = Rel (Circuit n) 0ℓ

private
  variable
    w v : Circuit n

------------------------------------------------------------------------
-- Structural lift operations

-- Shift all generators up by one wire.
_↑ : Circuit n → Circuit (₁₊ n)
_↑ = wmap _↥

-- Identity: marks a circuit acting on the bottom wires (notation only).
_↓ : Circuit n → Circuit n
_↓ x = x

-- Shift a generator up by k wires.
-- Type Gen (k + n) (k on the left) avoids the n + 0 ≢ n issue.
infixl 8 _↥ᵏ_
_↥ᵏ_ : Gen n → (k : ℕ) → Gen (k + n)
g ↥ᵏ zero    = g
g ↥ᵏ ₁₊ k   = (g ↥ᵏ k) ↥

-- Lift a circuit up by k wires.
infixl 7 _↑ᵏ_
_↑ᵏ_ : Circuit n → (k : ℕ) → Circuit (k + n)
w ↑ᵏ zero    = w
w ↑ᵏ ₁₊ k   = (w ↑ᵏ k) ↑

------------------------------------------------------------------------
-- Lift-Relation
--
-- Extends any family of circuit relations (indexed by wire count) with
-- the two structural rules shared by ALL circuit presentations:
--
--   cong↑  — equalities are preserved under _↑
--   comm   — an m-ary gate at the bottom commutes with any generator
--            that has been shifted up m wires
--
-- Usage: define a group-specific CRel (order relations, braid
-- relations, etc.), then open Lift-Relation CRel to obtain the full
-- relation that includes the structural rules automatically.
module Lift-Relation (_SRel,_===_ : (n : ℕ) → CRel n) where

  infix 4 _CRel,_===_
  data _CRel,_===_ : (n : ℕ) → CRel n where

    -- Embed the group-specific relation.
    srel  : n SRel, w === v → n CRel, w === v

    -- Structural: congruence under wire-shifting.
    cong↑ : n CRel, w === v → (₁₊ n) CRel, w ↑ === v ↑

    -- Structural: a gate at the bottom commutes with any generator
    -- that has been shifted up past it.
    --
    -- comm₁: a 1-ary gate at wire 0 commutes with g shifted up 1 wire.
    -- comm₂: a 2-ary gate at wires 0-1 commutes with g shifted up 2 wires.
    comm₁ : (h : Gate 1) (g : Gen n) → (₁₊ n) CRel,
      [ g ↥ ]ʷ • [ gate₁ h ]ʷ === [ gate₁ h ]ʷ • [ g ↥ ]ʷ
    comm₂ : (h : Gate 2) (g : Gen n) → (₂₊ n) CRel,
      [ g ↥ ↥ ]ʷ • [ gate₂ h ]ʷ === [ gate₂ h ]ʷ • [ g ↥ ↥ ]ʷ

  -- The congruence closure at wire count n lifts to wire count ₁₊ n.
  lemma-cong↑ : ∀ {n} (w v : Circuit n)
    → let open PB (_CRel,_===_ n)       using (_≈_)
          open PB (_CRel,_===_ (₁₊ n)) renaming (_≈_ to _≈↑_) using ()
      in w ≈ v → w ↑ ≈↑ v ↑
  lemma-cong↑ w v PB.refl              = PB.refl
  lemma-cong↑ w v (PB.sym eq)          = PB.sym (lemma-cong↑ v w eq)
  lemma-cong↑ w v (PB.trans eq eq₁)   = PB.trans (lemma-cong↑ _ _ eq) (lemma-cong↑ _ _ eq₁)
  lemma-cong↑ w v (PB.cong eq eq₁)    = PB.cong  (lemma-cong↑ _ _ eq) (lemma-cong↑ _ _ eq₁)
  lemma-cong↑ w v PB.assoc            = PB.assoc
  lemma-cong↑ w v PB.left-unit        = PB.left-unit
  lemma-cong↑ w v PB.right-unit       = PB.right-unit
  lemma-cong↑ w v (PB.axiom x)        = PB.axiom (cong↑ x)
