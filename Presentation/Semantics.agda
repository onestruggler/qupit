------------------------------------------------------------------------
-- The Agda standard library
--
-- Completeness and Soundness.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Level using (_⊔_)
open import Relation.Binary using (Setoid)

module Presentation.Semantics {a b ℓ₁ ℓ₂}
  (Syn : Setoid a ℓ₁)
  (Sem : Setoid b ℓ₂)
  where

open Setoid Syn using () renaming (Carrier to A; _≈_ to _≈₁_)
open Setoid Sem using () renaming (Carrier to B; _≈_ to _≈₂_)

Soundness : (⟦_⟧ : A → B) → Set (a ⊔ ℓ₁ ⊔ ℓ₂)
Soundness ⟦_⟧ = ∀ {x y : A} → x ≈₁ y → ⟦ x ⟧ ≈₂ ⟦ y ⟧

Completeness : (⟦_⟧ : A → B) → Set (a ⊔ ℓ₁ ⊔ ℓ₂)
Completeness ⟦_⟧ = ∀ {x y : A} → ⟦ x ⟧ ≈₂ ⟦ y ⟧ → x ≈₁ y
