{-# OPTIONS --safe #-}
open import Level using (0ℓ)
open import Relation.Binary using (IsEquivalence ; Setoid ; Rel)
open import Data.Product using (_,_)
open import Relation.Binary.Morphism.Definitions using (Homomorphic₂)
open import Relation.Binary.PropositionalEquality using (_≡_)
import Relation.Binary.PropositionalEquality as Eq
import Relation.Binary.Reasoning.Setoid as SR

open import Algebra.Morphism.Structures using (module MonoidMorphisms ; module GroupMorphisms)
open import Function.Definitions using (Injective ; Surjective)
open import Algebra.Bundles using (Monoid ; Group)
open import Algebra.Bundles.Raw using (RawGroup)

open import Word.Base
open import Word.Properties
import Presentation.Base as PB
import Presentation.Properties as PP
open import Presentation.Reidemeister-Schreier hiding (module Star-Congruence)

module Presentation.Morphism.Properties {A B : Set} (Γ : WRel A) (Δ : WRel B) where

open PB Γ renaming (_===_ to _===₁_ ; _≈_ to _≈₁_ ; refl to refl₁ ; cong to cong₁ ; sym to sym₁)
open PP Γ renaming (•-ε-monoid to m₁ ; word-setoid to ws₁)
open PB Δ renaming (_===_ to _===₂_ ; _≈_ to _≈₂_ ; refl to refl₂ ; cong to cong₂ ; sym to sym₂)
open PP Δ renaming (•-ε-monoid to m₂ ; word-setoid to ws₂)

open PB


open import Algebra.Morphism.Bundles
open import Function using (_∘_)
open import Function.Bundles
import Relation.Binary.Reasoning.Setoid as SR
open import Data.Product
import Function.Properties.Bijection as PBi

iso-nf : Inverse ws₁ ws₂ -> PP.NFProperty' Γ -> PP.NFProperty' Δ
iso-nf
  record { to = to ; from = from ; to-cong = to-cong ; from-cong = from-cong ; inverse = inverse }
  gp@record { NF = NF₁ ; nf = nf₁ ; nf-cong = nf-cong₁ ; inv-nf = inv-nf₁ ; inv-nf∘nf=id = inv-nf∘nf=id₁ } =
  record
   { NF = NF ; nf = nf ∘ from ; nf-cong = lemma-nf-cong ; inv-nf = to ∘ inv-nf ; inv-nf∘nf=id = lemma-∘ }
  where

  open PP.NFProperty' gp

  lemma-nf-cong : {w v : Word B} → w ≈₂ v → nf₁ (from w) ≡ nf₁ (from v)
  lemma-nf-cong {w} {v} eq = begin
    nf₁ (from w) ≡⟨ nf-cong₁ (from-cong eq) ⟩
    nf₁ (from v) ∎
    where open Eq.≡-Reasoning

  lemma-∘ : {w : Word B} → to (inv-nf₁ (nf₁ (from w))) ≈₂ w
  lemma-∘ {w} = begin
    to (inv-nf₁ (nf₁ (from w))) ≈⟨ to-cong inv-nf∘nf=id₁ ⟩
    to ( (from w)) ≈⟨ inverse .proj₁ refl ⟩
    w ∎
    where open SR ws₂

iso-nf' : Bijection ws₁ ws₂ -> PP.NFProperty' Γ -> PP.NFProperty' Δ
iso-nf' bi gp = iso-nf (PBi.Bijection⇒Inverse bi) gp
