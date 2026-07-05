------------------------------------------------------------------------
-- Presentations of groups
--
-- Soundness of the symmetric group presentation in the tight semantics:
-- the congruence closure _≈_ of _VRel,_===_ preserves the denotation
-- ⟦_⟧ : Word (Gen n) → Perm n.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}

open import Data.Nat using (ℕ ; zero ; suc)
open import Data.Fin using (Fin ; zero ; suc)
open import Data.Fin.Permutation
  using ( _⟨$⟩ʳ_ ; _∘ₚ_ ; lift₀-cong )
  renaming (id to idP)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_ ; refl)

open import Word.Base
import Presentation.Base as PB
open import Notations

module Examples.Groups.Symmetric.Tight.Soundness where

open import Examples.Groups.Symmetric.Syntactics
open import Examples.Groups.Symmetric.Tight.Semantics

------------------------------------------------------------------------
-- Soundness of the base axioms (by case analysis on Fin)

sound-order : ∀ {n} (k : Fin (₂₊ n))
            → (swap01 ∘ₚ swap01) ⟨$⟩ʳ k ≡ idP ⟨$⟩ʳ k
sound-order zero      = refl
sound-order (₁₊ zero) = refl
sound-order (₂₊ k)    = refl

sound-yb : ∀ {n} (k : Fin (₃₊ n))
         → (swap01 ∘ₚ shift swap01 ∘ₚ swap01) ⟨$⟩ʳ k
         ≡ (shift swap01 ∘ₚ swap01 ∘ₚ shift swap01) ⟨$⟩ʳ k
sound-yb zero       = refl
sound-yb (₁₊ zero)  = refl
sound-yb (₂₊ zero)  = refl
sound-yb (₃₊ k)     = refl

sound-comm2 : ∀ {n} (π : Perm n) (k : Fin (₂₊ n))
            → (shift (shift π) ∘ₚ swap01) ⟨$⟩ʳ k
            ≡ (swap01 ∘ₚ shift (shift π)) ⟨$⟩ʳ k
sound-comm2 π zero      = refl
sound-comm2 π (₁₊ zero) = refl
sound-comm2 π (₂₊ k)    = refl

------------------------------------------------------------------------
-- Soundness of the raw relation _VRel,_===_

sound-ax : ∀ {n} {w v : Circuit n} → n VRel, w === v
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

sound : ∀ {n} {w v : Circuit n} → PB._≈_ (_VRel,_===_ n) w v
      → ∀ k → ⟦ w ⟧ ⟨$⟩ʳ k ≡ ⟦ v ⟧ ⟨$⟩ʳ k
sound {n} p = go p
  where
  open PB (_VRel,_===_ n)
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
