------------------------------------------------------------------------
-- Presentations of groups
--
-- Semantics of the symmetric group: permutations of Fin n.
-- Proves soundness of _CRel,_===_ (and its congruence closure) for any n.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}

open import Data.Nat using (ℕ ; zero ; suc)
open import Data.Fin using (Fin ; zero ; suc)
open import Data.Vec.Functional.Relation.Binary.Permutation
open import Data.Vec.Functional.Relation.Binary.Permutation.Properties

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_ ; refl)
open import Function using (_∘_ ; id)

open import Word.Base
import Presentation.Horizontal-Syntactics as PB
open import Notations

module Examples.Groups.Symmetric.Semantics where

open import Examples.Groups.Symmetric.Syntactics

------------------------------------------------------------------------
-- Permutation type

Perm : ℕ → Set
Perm n = Fin n → Fin n

------------------------------------------------------------------------
-- Semantic building blocks

-- Swap positions 0 and 1: the denotation of σ-gate.
swap01 : ∀ {n} → Perm (₂₊ n)
swap01 zero          = ₁₊ zero
swap01 (₁₊ zero)    = zero
swap01 (₂₊ k) = ₂₊ k

-- Shift a permutation up by one wire: the action of _↥.
shift : ∀ {n} → Perm n → Perm (₁₊ n)
shift f zero    = zero
shift f (₁₊ k) = suc (f k)

------------------------------------------------------------------------
-- Denotation of generators and words

⟦_⟧ᵍ : ∀ {n} → Gen n → Perm n
⟦ gate₁ () ⟧ᵍ
⟦ gate₂ σ-gate ⟧ᵍ = swap01
⟦ g ↥ ⟧ᵍ          = shift ⟦ g ⟧ᵍ

-- Words are read left-to-right: w • v applies w first, then v.
⟦_⟧ : ∀ {n} → Word (Gen n) → Perm n
⟦ ε ⟧      = id
⟦ [ g ]ʷ ⟧ = ⟦ g ⟧ᵍ
⟦ w • v ⟧  = ⟦ v ⟧ ∘ ⟦ w ⟧

------------------------------------------------------------------------
-- Lemmas about shift

shift-id : ∀ {n} (k : Fin (₁₊ n)) → shift id k ≡ k
shift-id zero    = refl
shift-id (₁₊ k) = refl

shift-hom : ∀ {n} (f g : Perm n) (k : Fin (₁₊ n))
          → shift (f ∘ g) k ≡ (shift f ∘ shift g) k
shift-hom f g zero    = refl
shift-hom f g (₁₊ k) = refl

shift-cong : ∀ {n} {f g : Perm n} → (∀ k → f k ≡ g k)
           → ∀ k → shift f k ≡ shift g k
shift-cong eq zero    = refl
shift-cong eq (₁₊ k) = Eq.cong suc (eq k)

-- ⟦ w ↑ ⟧ agrees with shift ⟦ w ⟧ pointwise.
⟦↑⟧ : ∀ {n} (w : Word (Gen n)) (k : Fin (₁₊ n)) → ⟦ w ↑ ⟧ k ≡ shift ⟦ w ⟧ k
⟦↑⟧ ε       k = Eq.sym (shift-id k)
⟦↑⟧ [ g ]ʷ  k = refl
⟦↑⟧ (w • v) k = Eq.trans (Eq.cong (⟦ v ↑ ⟧) (⟦↑⟧ w k))
                           (Eq.trans (⟦↑⟧ v _) (Eq.sym (shift-hom _ _ k)))

------------------------------------------------------------------------
-- Soundness of the base axioms (by case analysis on Fin)

sound-order : ∀ {n} (k : Fin (₂₊ n)) → swap01 (swap01 k) ≡ k
sound-order zero          = refl
sound-order (₁₊ zero)    = refl
sound-order (₂₊ k) = refl

-- yang-baxter: σ · σ₁ · σ = σ₁ · σ · σ₁   (all refl by computation)
sound-yb : ∀ {n} (k : Fin (₃₊ n))
         → (swap01 ∘ shift swap01 ∘ swap01) k
         ≡ (shift swap01 ∘ swap01 ∘ shift swap01) k
sound-yb zero             = refl
sound-yb (₁₊ zero)       = refl
sound-yb (₂₊ zero) = refl
sound-yb (₃₊ k) = refl

-- shift(shift f) and swap01 act on disjoint wire ranges and commute.
sound-comm2 : ∀ {n} (f : Perm n) (k : Fin (₂₊ n))
            → swap01 (shift (shift f) k) ≡ shift (shift f) (swap01 k)
sound-comm2 f zero          = refl
sound-comm2 f (₁₊ zero)    = refl
sound-comm2 f (₂₊ k) = refl

------------------------------------------------------------------------
-- Soundness of the raw relation _CRel,_===_

sound-ax : ∀ {n} {w v : Circuit n} → n CRel, w === v
         → ∀ k → ⟦ w ⟧ k ≡ ⟦ v ⟧ k
sound-ax (srel order)             k = sound-order k
sound-ax (srel yang-baxter)       k = sound-yb k
sound-ax (cong↑ {_} {w₀} {v₀} p)     k = Eq.trans (⟦↑⟧ w₀ k)
                                           (Eq.trans (shift-cong (sound-ax p) k)
                                                     (Eq.sym (⟦↑⟧ v₀ k)))
sound-ax (comm₁ () _)                 _
sound-ax (comm₂ σ-gate g)             k = sound-comm2 ⟦ g ⟧ᵍ k

------------------------------------------------------------------------
-- Full soundness: the congruence closure _≈_ preserves denotation

sound : ∀ {n} {w v : Circuit n} → PB._≈_ (_CRel,_===_ n) w v
      → ∀ k → ⟦ w ⟧ k ≡ ⟦ v ⟧ k
sound {n} p = go p
  where
  open PB (_CRel,_===_ n)
  go : ∀ {w v : Word (Gen n)} → w ≈ v → ∀ k → ⟦ w ⟧ k ≡ ⟦ v ⟧ k
  go refl                          k = refl
  go (sym p)                       k = Eq.sym (go p k)
  go (trans p q)                   k = Eq.trans (go p k) (go q k)
  go (cong {w₀} {_} {_} {v₁} p q) k = Eq.trans (go q (⟦ w₀ ⟧ k)) (Eq.cong ⟦ v₁ ⟧ (go p k))
  go assoc                         k = refl
  go left-unit                     k = refl
  go right-unit                    k = refl
  go (axiom x)                     k = sound-ax x k
