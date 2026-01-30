open import Relation.Binary using (Rel ; REL)

open import Level using (0ℓ)
open import Data.Product using (_,_ ; _×_ ; map ; proj₁ ; proj₂ ; Σ ; ∃ ; ∃-syntax)
import Data.Product.Relation.Binary.Pointwise.NonDependent as PW
open import Data.Sum using (_⊎_ ; inj₁ ; inj₂)
open import Function using (_∘_ ; _∘₂_)
open import Relation.Binary.PropositionalEquality using (_≡_ ; inspect ; setoid ; module ≡-Reasoning) renaming ([_] to [_]')
import Relation.Binary.PropositionalEquality as Eq

import Relation.Binary.Reasoning.Setoid as SR

open import Word.Base
open import Word.Properties
import Presentation.Base as PB
import Presentation.Properties as PP
open import Presentation.Properties 

open import Presentation.Reidemeister-Schreier
open import Presentation.Construct.Base
module Presentation.Construct.Properties.SugarProduct
  {M A : Set}
  (Γ : WRel M)
  (Δ : WRel A)
  (f : M -> Word A)
  where
  
open PB Γ renaming (_===_ to _===₁_ ; _≈_ to _≈₁_) using ()
open PP Γ renaming (•-ε-monoid to m₁ ; word-setoid to word-setoid₁) using ()
open PB Δ renaming (_===_ to _===₂_ ; _≈_ to _≈₂_) using ()
open PP Δ renaming (•-ε-monoid to m₂ ; word-setoid to word-setoid₂) using ()

open PB (Γ ⸲ Δ ⸲ Γₛ f) renaming (_===_ to _===_ ; _≈_ to _≈_) using ()
open PP (Γ ⸲ Δ ⸲ Γₛ f) renaming (•-ε-monoid to mm ; word-setoid to ws) using ()

open _≈_

module _
  (f-wd-ax : ∀ {w v} -> w ===₁ v -> ((f *) w) ≈₂ ((f *) v))
  where

  X = M ⊎ A

  to-right : X -> Word A
  to-right (inj₁ x) = f x
  to-right (inj₂ y) = [ y ]ʷ

  to-right-right : ∀ x -> [ x ]ʷ ≈ [ to-right x ]ᵣ
  to-right-right (inj₁ x) = axiom (mid desugar)
  to-right-right (inj₂ y) = refl
  
  to-right*-right : ∀ w -> w ≈ [ (to-right *) w ]ᵣ
  to-right*-right [ x ]ʷ = to-right-right x
  to-right*-right ε = _≈_.refl
  to-right*-right (w • w₁) with to-right*-right w | to-right*-right w₁
  to-right*-right (w • w₁) | ih1 | ih2 = _≈_.cong ih1 ih2


  lemma-to-right-r : ∀ w -> (to-right *) [ w ]ᵣ ≡ w
  lemma-to-right-r [ x ]ʷ = Eq.refl
  lemma-to-right-r ε = Eq.refl
  lemma-to-right-r (w • w₁) rewrite lemma-to-right-r w | lemma-to-right-r w₁  = Eq.refl

  lemma-to-right-l : ∀ w -> (to-right *) [ w ]ₗ ≡ (f *) w
  lemma-to-right-l [ x ]ʷ = Eq.refl
  lemma-to-right-l ε = Eq.refl
  lemma-to-right-l (w • w₁) rewrite lemma-to-right-l w | lemma-to-right-l w₁ = Eq.refl

  to-right-wd :  ∀ {w v} -> w === v -> (to-right *) w ≈₂ (to-right *) v
  to-right-wd {w} {v} (left {u} {v₁} x) = begin
    (to-right *) [ u ]ₗ ≡⟨ lemma-to-right-l u ⟩
    (f *) u ≈⟨ f-wd-ax x ⟩
    (f *) v₁ ≡⟨ Eq.sym (lemma-to-right-l v₁) ⟩
    (to-right *) [ v₁ ]ₗ ∎
    where
    open SR word-setoid₂
  to-right-wd {w} {v} (right {u} {v₁} x) rewrite lemma-to-right-r u | lemma-to-right-r v₁ = _≈₂_.axiom x
  to-right-wd {w} {v} (mid (desugar {m})) rewrite lemma-to-right-r (f m) = _≈₂_.refl


  Cₛ = word-setoid₂


  I : Word A
  I = ε

  nfp : NFProperty Δ -> NFProperty (Γ ⸲ Δ ⸲ Γₛ f)
  nfp p = record { NF = NF ; nf = nf ∘ (to-right *) ; nf-cong = nf'-cong ; nf-injective = nf'-inj }
    where
    open NFProperty p

    open Star-Injective-Full-Setoid Γ (Γ ⸲ Δ ⸲ Γₛ f) Cₛ I renaming (nf to anf)
    import Function.Construct.Composition as FCC
    open import Function.Definitions
    
    to-right*-cong = Star-Congruence.lemma-f*-cong (Γ ⸲ Δ ⸲ Γₛ f) Δ to-right to-right-wd
    
    module MA = LeftRightCongruence Γ Δ (Γₛ f)
    to-right*-inj : Injective _≈_ _≈₂_ (to-right *)
    to-right*-inj {x} {y} eq = begin
      x ≈⟨ to-right*-right x ⟩
      [ (to-right *) x ]ᵣ ≈⟨ MA.rights eq ⟩
      [ (to-right *) y ]ᵣ ≈⟨ sym (to-right*-right y) ⟩
      y ∎
      where
      open SR ws

    nf' = nf ∘ (to-right *)
    
    nf'-cong : Congruent _≈_ _≡_ nf'
    nf'-cong = FCC.congruent _≈_ _≈₂_ _≡_ to-right*-cong nf-cong

    nf'-inj : Injective _≈_ _≡_ nf'
    nf'-inj = FCC.injective _≈_ _≈₂_ _≡_ to-right*-inj nf-injective

  nfp' : NFProperty' Δ -> NFProperty' (Γ ⸲ Δ ⸲ Γₛ f)
  nfp' p = record
             { NF = NF ; nf = nf' ; nf-cong = nf'-cong ; inv-nf = inv-nf' ; inv-nf∘nf=id = gf=id }
    where
    open NFProperty' p

    nf' = nf ∘ (to-right *)
    
    inv-nf' : NF -> Word X
    inv-nf' = [_]ᵣ ∘ inv-nf

    open Star-Injective-Full-Setoid Γ (Γ ⸲ Δ ⸲ Γₛ f) Cₛ I renaming (nf to anf)
    import Function.Construct.Composition as FCC
    open import Function.Definitions
    
    to-right*-cong = Star-Congruence.lemma-f*-cong (Γ ⸲ Δ ⸲ Γₛ f) Δ to-right to-right-wd
    
    module MA = LeftRightCongruence Γ Δ (Γₛ f)
    to-right*-inj : Injective _≈_ _≈₂_ (to-right *)
    to-right*-inj {x} {y} eq = begin
      x ≈⟨ to-right*-right x ⟩
      [ (to-right *) x ]ᵣ ≈⟨ MA.rights eq ⟩
      [ (to-right *) y ]ᵣ ≈⟨ sym (to-right*-right y) ⟩
      y ∎
      where
      open SR ws

    
    nf'-cong : Congruent _≈_ _≡_ nf'
    nf'-cong = FCC.congruent _≈_ _≈₂_ _≡_ to-right*-cong nf-cong

    nf'-inj : Injective _≈_ _≡_ nf'
    nf'-inj = FCC.injective _≈_ _≈₂_ _≡_ to-right*-inj nf-injective

    gf=id : {w : Word (M ⊎ A)} → inv-nf' (nf' w) ≈ w
    gf=id {w} = begin
      inv-nf' (nf' w) ≈⟨ refl ⟩
      ([_]ᵣ ∘ inv-nf ∘ nf ∘ (to-right *)) (w) ≈⟨ MA.rights inv-nf∘nf=id ⟩
      ([_]ᵣ ∘ (to-right *)) (w) ≈⟨ sym (to-right*-right w) ⟩
      w ∎
      where
      open SR ws
