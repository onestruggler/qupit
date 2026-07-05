------------------------------------------------------------------------
-- Presentations of groups
--
-- Semantics of the symmetric group: permutations of Fin n.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}

open import Data.Nat using (ℕ ; zero ; suc)
open import Data.Fin using (Fin ; zero ; suc)
open import Data.Vec.Functional.Relation.Binary.Permutation
open import Data.Vec.Functional.Relation.Binary.Permutation.Properties

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_ ; refl ; _≗_)
open import Relation.Binary.Bundles using (Setoid)
open import Function using (_∘_ ; id)

open import Word.Base
open import Notations

module Examples.Groups.Symmetric.Loose.Semantics where

open import Examples.Groups.Symmetric.Syntactics

------------------------------------------------------------------------
-- Permutation type

Endo : ℕ → Set
Endo n = Fin n → Fin n

Endo-setoid : ℕ → Setoid _ _
Endo-setoid n = record
  { Carrier       = Endo n
  ; _≈_           = _≗_
  ; isEquivalence = record
    { refl  = λ _   → refl
    ; sym   = λ p k → Eq.sym (p k)
    ; trans = λ p q k → Eq.trans (p k) (q k)
    }
  }

------------------------------------------------------------------------
-- Semantic building blocks

-- Swap positions 0 and 1: the denotation of σ-gate.
swap01 : ∀ {n} → Endo (₂₊ n)
swap01 zero          = ₁₊ zero
swap01 (₁₊ zero)    = zero
swap01 (₂₊ k) = ₂₊ k

-- Shift a permutation up by one wire: the action of _↥.
shift : ∀ {n} → Endo n → Endo (₁₊ n)
shift f zero    = zero
shift f (₁₊ k) = suc (f k)

------------------------------------------------------------------------
-- Denotation of generators and words

⟦_⟧ᵍ : ∀ {n} → Gen n → Endo n
⟦ gate₁ () ⟧ᵍ
⟦ gate₂ σ-gate ⟧ᵍ = swap01
⟦ g ↥ ⟧ᵍ          = shift ⟦ g ⟧ᵍ

-- Words are read left-to-right: w • v applies w first, then v.
⟦_⟧ : ∀ {n} → Word (Gen n) → Endo n
⟦ ε ⟧      = id
⟦ [ g ]ʷ ⟧ = ⟦ g ⟧ᵍ
⟦ w • v ⟧  = ⟦ v ⟧ ∘ ⟦ w ⟧

------------------------------------------------------------------------
-- Lemmas about shift

shift-id : ∀ {n} (k : Fin (₁₊ n)) → shift id k ≡ k
shift-id zero    = refl
shift-id (₁₊ k) = refl

shift-hom : ∀ {n} (f g : Endo n) (k : Fin (₁₊ n))
          → shift (f ∘ g) k ≡ (shift f ∘ shift g) k
shift-hom f g zero    = refl
shift-hom f g (₁₊ k) = refl

shift-cong : ∀ {n} {f g : Endo n} → f ≗ g → shift f ≗ shift g
shift-cong eq zero    = refl
shift-cong eq (₁₊ k) = Eq.cong suc (eq k)

-- ⟦ w ↑ ⟧ agrees with shift ⟦ w ⟧ pointwise.
⟦↑⟧ : ∀ {n} (w : Word (Gen n)) → ⟦ w ↑ ⟧ ≗ shift ⟦ w ⟧
⟦↑⟧ ε       k = Eq.sym (shift-id k)
⟦↑⟧ [ g ]ʷ  k = refl
⟦↑⟧ (w • v) k = Eq.trans (Eq.cong (⟦ v ↑ ⟧) (⟦↑⟧ w k))
                           (Eq.trans (⟦↑⟧ v _) (Eq.sym (shift-hom _ _ k)))

