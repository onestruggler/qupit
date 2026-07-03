------------------------------------------------------------------------
-- Presentations of groups
--
-- Semantics of the symmetric group: bijections on Fin n via
-- Data.Fin.Permutation.Permutation′.
-- Proves soundness of _CRel,_===_ (and its congruence closure) for any n.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}

open import Data.Nat using (ℕ ; zero ; suc)
open import Data.Fin using (Fin ; zero ; suc)
open import Data.Fin.Permutation
  using ( Permutation′ ; permutation ; _⟨$⟩ʳ_ ; _∘ₚ_
        ; lift₀ ; lift₀-id ; lift₀-comp ; lift₀-cong )
  renaming (id to idP)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_ ; refl)

open import Word.Base
import Presentation.Horizontal-Syntactics as PB
open import Notations

module Examples.Groups.Symmetric.Semantics2 where

open import Examples.Groups.Symmetric.Syntactics

------------------------------------------------------------------------
-- Permutation type

Perm : ℕ → Set
Perm n = Permutation′ n

------------------------------------------------------------------------
-- Semantic building blocks

-- The underlying function for swap01 (used to build the Permutation′).
private
  swap01-fun : ∀ {n} → Fin (₂₊ n) → Fin (₂₊ n)
  swap01-fun zero      = ₁₊ zero
  swap01-fun (₁₊ zero) = zero
  swap01-fun (₂₊ k)    = ₂₊ k

-- Swap positions 0 and 1: the denotation of σ-gate.
swap01 : ∀ {n} → Perm (₂₊ n)
swap01 = permutation swap01-fun swap01-fun
  (λ { zero → refl ; (₁₊ zero) → refl ; (₂₊ _) → refl })
  (λ { zero → refl ; (₁₊ zero) → refl ; (₂₊ _) → refl })

-- Shift a permutation up by one wire: the action of _↥.
shift : ∀ {n} → Perm n → Perm (₁₊ n)
shift = lift₀

------------------------------------------------------------------------
-- Denotation of generators and words

⟦_⟧ᵍ : ∀ {n} → Gen n → Perm n
⟦ gate₁ () ⟧ᵍ
⟦ gate₂ σ-gate ⟧ᵍ = swap01
⟦ g ↥ ⟧ᵍ          = shift ⟦ g ⟧ᵍ

-- Words are read left-to-right: w • v applies w first, then v.
⟦_⟧ : ∀ {n} → Word (Gen n) → Perm n
⟦ ε ⟧      = idP
⟦ [ g ]ʷ ⟧ = ⟦ g ⟧ᵍ
⟦ w • v ⟧  = ⟦ w ⟧ ∘ₚ ⟦ v ⟧

------------------------------------------------------------------------
-- Lemmas about shift (= lift₀)

-- ⟦ w ↑ ⟧ agrees with shift ⟦ w ⟧ pointwise.
⟦↑⟧ : ∀ {n} (w : Word (Gen n)) (k : Fin (₁₊ n))
     → ⟦ w ↑ ⟧ ⟨$⟩ʳ k ≡ shift ⟦ w ⟧ ⟨$⟩ʳ k
⟦↑⟧ ε       k = Eq.sym (lift₀-id k)
⟦↑⟧ [ g ]ʷ  k = refl
⟦↑⟧ (w • v) k =
  Eq.trans (Eq.cong (⟦ v ↑ ⟧ ⟨$⟩ʳ_) (⟦↑⟧ w k))
  (Eq.trans (⟦↑⟧ v _) (lift₀-comp ⟦ w ⟧ ⟦ v ⟧ k))

------------------------------------------------------------------------
-- Soundness of the base axioms (by case analysis on Fin)

sound-order : ∀ {n} (k : Fin (₂₊ n))
            → (swap01 ∘ₚ swap01) ⟨$⟩ʳ k ≡ idP ⟨$⟩ʳ k
sound-order zero      = refl
sound-order (₁₊ zero) = refl
sound-order (₂₊ k)    = refl

-- yang-baxter: σ · σ₁ · σ = σ₁ · σ · σ₁   (all refl by computation)
sound-yb : ∀ {n} (k : Fin (₃₊ n))
         → (swap01 ∘ₚ shift swap01 ∘ₚ swap01) ⟨$⟩ʳ k
         ≡ (shift swap01 ∘ₚ swap01 ∘ₚ shift swap01) ⟨$⟩ʳ k
sound-yb zero       = refl
sound-yb (₁₊ zero)  = refl
sound-yb (₂₊ zero)  = refl
sound-yb (₃₊ k)     = refl

-- shift(shift π) and swap01 act on disjoint wire ranges and commute.
sound-comm2 : ∀ {n} (π : Perm n) (k : Fin (₂₊ n))
            → (shift (shift π) ∘ₚ swap01) ⟨$⟩ʳ k
            ≡ (swap01 ∘ₚ shift (shift π)) ⟨$⟩ʳ k
sound-comm2 π zero      = refl
sound-comm2 π (₁₊ zero) = refl
sound-comm2 π (₂₊ k)    = refl

------------------------------------------------------------------------
-- Soundness of the raw relation _CRel,_===_

sound-ax : ∀ {n} {w v : Circuit n} → n CRel, w === v
         → ∀ k → ⟦ w ⟧ ⟨$⟩ʳ k ≡ ⟦ v ⟧ ⟨$⟩ʳ k
sound-ax (srel order)               k = sound-order k
sound-ax (srel yang-baxter)         k = sound-yb k
sound-ax (cong↑ {_} {w₀} {v₀} p)   k =
  Eq.trans (⟦↑⟧ w₀ k)
  (Eq.trans (lift₀-cong ⟦ w₀ ⟧ ⟦ v₀ ⟧ (sound-ax p) k)
            (Eq.sym (⟦↑⟧ v₀ k)))
sound-ax (comm₁ () _)               _
sound-ax (comm₂ σ-gate g)           k = sound-comm2 ⟦ g ⟧ᵍ k

------------------------------------------------------------------------
-- Full soundness: the congruence closure _≈_ preserves denotation

sound : ∀ {n} {w v : Circuit n} → PB._≈_ (_CRel,_===_ n) w v
      → ∀ k → ⟦ w ⟧ ⟨$⟩ʳ k ≡ ⟦ v ⟧ ⟨$⟩ʳ k
sound {n} p = go p
  where
  open PB (_CRel,_===_ n)
  go : ∀ {w v : Word (Gen n)} → w ≈ v → ∀ k → ⟦ w ⟧ ⟨$⟩ʳ k ≡ ⟦ v ⟧ ⟨$⟩ʳ k
  go refl                          k = refl
  go (sym p)                       k = Eq.sym (go p k)
  go (trans p q)                   k = Eq.trans (go p k) (go q k)
  go (cong {w₀} {_} {_} {v₁} p q) k =
    Eq.trans (go q (⟦ w₀ ⟧ ⟨$⟩ʳ k)) (Eq.cong (⟦ v₁ ⟧ ⟨$⟩ʳ_) (go p k))
  go assoc                         k = refl
  go left-unit                     k = refl
  go right-unit                    k = refl
  go (axiom x)                     k = sound-ax x k
