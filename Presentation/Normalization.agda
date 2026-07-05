------------------------------------------------------------------------
-- The Agda standard library
--
-- Normalization as the composition of the retraction and the section.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Level using (_⊔_)
open import Function using (_∘_)
open import Relation.Binary using (Setoid)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)
import Relation.Binary.Reasoning.Setoid as SR

module Presentation.Normalization {a b ℓ}
  (S : Setoid a ℓ)
  (B : Set b)
  (let open Setoid S using (trans) renaming (Carrier to A ; _≈_ to _≈₁_ ; sym to sym₁))
  (f : A → B)
  (g : B → A)
  where

private
  variable
    x y : A
    u v : B

normalize : A → A
normalize = g ∘ f

record NormalForm : Set (a ⊔ b ⊔ ℓ) where
  field
    f-cong : x ≈₁ y → f x ≡ f y
    g∘f=id : g (f x) ≈₁ x

  f-inj : f x ≡ f y → x ≈₁ y
  f-inj {a} {a'} eq = begin
    a ≈⟨ sym₁ g∘f=id ⟩
    g (f a) ≡⟨ ≡.cong g eq ⟩
    g (f a') ≈⟨ g∘f=id ⟩
    a' ∎
    where
    open SR S

  idempotent : normalize (normalize x) ≈₁ x
  idempotent = trans g∘f=id g∘f=id

module _ {c d} (Sem : Setoid c d)
  (let open Setoid Sem using () renaming (Carrier to C; _≈_ to _≈₂_ ; sym to sym₂))
  (⟦_⟧ : A → C)
  where
  record UniqueNormalForm : Set (a ⊔ b ⊔ ℓ ⊔ c ⊔ d) where
    field
      nf : NormalForm
      unique : ⟦ g u ⟧ ≈₂ ⟦ g v ⟧ → u ≡ v

    open NormalForm nf public

module Completeness {c d} (Sem : Setoid c d)
  (let open Setoid Sem using () renaming (Carrier to C; _≈_ to _≈₂_ ; sym to sym₂))
  (⟦_⟧ : A → C)
  where

  open import Presentation.Semantics S Sem

  by-normalization : UniqueNormalForm Sem ⟦_⟧ →  Soundness ⟦_⟧ → Completeness ⟦_⟧
  by-normalization uni sound {x} {y} eq = f-inj (unique claim)
    where
    open UniqueNormalForm uni
    claim : ⟦ g (f x) ⟧ ≈₂ ⟦ g (f y) ⟧
    claim = begin
      ⟦ g (f x) ⟧ ≈⟨ sound g∘f=id ⟩
      ⟦ x ⟧ ≈⟨ eq ⟩
      ⟦ y ⟧ ≈⟨ sym₂ (sound g∘f=id) ⟩
      ⟦ g (f y) ⟧ ∎
      where
      open SR Sem
