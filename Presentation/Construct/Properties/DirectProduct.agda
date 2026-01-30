{-# OPTIONS  --safe #-}
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
module Presentation.Construct.Properties.DirectProduct
  {A B : Set}
  (Γ : WRel A)
  (Δ : WRel B)
  where

open PB Γ renaming (_===_ to _===₁_ ; _≈_ to _≈₁_) using ()
open PP Γ renaming (•-ε-monoid to m₁ ; word-setoid to word-setoid₁) using ()
open PB Δ renaming (_===_ to _===₂_ ; _≈_ to _≈₂_) using ()
open PP Δ renaming (•-ε-monoid to m₂ ; word-setoid to word-setoid₂) using ()
open PB (Γ ⸲ Δ ⸲ Γₓ) renaming (_===_ to _===₃_ ; _≈_ to _≈₃_) using ()
open PP (Γ ⸲ Δ ⸲ Γₓ) renaming (•-ε-monoid to m₃ ; word-setoid to word-setoid₃) using ()

open _≈₃_

Cₛ = word-setoid₂

Y = A ⊎ B

I : Word B
I = ε

open Star-Injective-Full-Setoid Γ (Γ ⸲ Δ ⸲ Γₓ) Cₛ I renaming (nf to anf)


[_] : C -> Word Y
[_] = [_]ᵣ

f : A -> Word Y
f x = [ [ x ]ʷ ]ₗ

h : C -> Y -> Word A × C
h c (inj₁ x) = [ x ]ʷ , c
h c (inj₂ y) = ε , (c • [ y ]ʷ)


⁻¹f-gen : ∀ (x : A) -> ([ x ]ʷ , I) ~ ((h **) I (f x))
⁻¹f-gen x = _≈₁_.refl , _≈₂_.refl

lemma-h**-left' : ∀ c {w} -> (h **) c [ w ]ₗ ≡ (w , c)
lemma-h**-left' c {[ x ]ʷ} = Eq.refl
lemma-h**-left' c {ε} = Eq.refl
lemma-h**-left' c {w • w₁} rewrite lemma-h**-left' c {w} | lemma-h**-left' c {w₁} = Eq.refl

lemma-h**-left : ∀ c {w} -> (h **) c [ w ]ₗ ~ (w , c)
lemma-h**-left c {[ x ]ʷ} = _≈₁_.refl , _≈₂_.refl
lemma-h**-left c {ε} = _≈₁_.refl , _≈₂_.refl
lemma-h**-left c {w • w₁} with (h **) c [ w ]ₗ | inspect ((h **) c) [ w ]ₗ
... | (w' , c') | [ eq1 ]' with (h **) c' [ w₁ ]ₗ | inspect ((h **) c') [ w₁ ]ₗ
... | (w₁' , c'') | [ eq2 ]' with lemma-h**-left c {w} | lemma-h**-left c' {w₁}
... | ih1 | ih2 rewrite eq1 | eq2 = (_≈₁_.cong (ih1 .proj₁) (ih2 .proj₁)) , _≈₂_.trans (ih2 .proj₂) (ih1 .proj₂)

lemma-h**-right : ∀ c {w} -> (h **) c [ w ]ᵣ ~ (ε , c • w)
lemma-h**-right c {[ x ]ʷ} = _≈₁_.refl , _≈₂_.refl
lemma-h**-right c {ε} = _≈₁_.refl , _≈₂_.sym _≈₂_.right-unit
lemma-h**-right c {w • w₁} with (h **) c [ w ]ᵣ | inspect ((h **) c) [ w ]ᵣ
... | (w' , c') | [ eq1 ]' with (h **) c' [ w₁ ]ᵣ | inspect ((h **) c') [ w₁ ]ᵣ
... | (w₁' , c'') | [ eq2 ]' with lemma-h**-right c {w} | lemma-h**-right c' {w₁}
... | ih1 | ih2 rewrite eq1 | eq2 = (_≈₁_.trans (_≈₁_.cong (ih1 .proj₁) (ih2 .proj₁)) _≈₁_.right-unit) , _≈₂_.trans (ih2 .proj₂) (_≈₂_.trans (_≈₂_.cong (ih1 .proj₂) _≈₂_.refl) _≈₂_.assoc )

h-congₛ-gen : ∀ {c d} y -> c ≈ₛ d -> h c y ~ h d y
h-congₛ-gen {c} {d} (inj₁ x) eq rewrite lemma-h**-left' c {[ x ]ʷ} | lemma-h**-left' d {[ x ]ʷ} = _≈₁_.refl , eq
h-congₛ-gen {c} {d} (inj₂ y) eq = trans~ (lemma-h**-right c {[ y ]ʷ}) (trans~ (_≈₁_.refl , _≈₂_.cong eq (_≈₂_.refl)) (sym~ (lemma-h**-right d {[ y ]ʷ})))

h=⁻¹f-gen : ∀ (x : A) -> ([ x ]ʷ , I) ~ ((h **) I (f x))
h=⁻¹f-gen x = refl~

h-wd : ∀ (c : C){u t : Word Y} -> u ===₃ t -> ((h **) c u) ~ ((h **) c t)
h-wd c {u} {t} (left x) = trans~ (lemma-h**-left c) (trans~ ((_≈₁_.axiom x) , reflₛ) (sym~ (lemma-h**-left c)))
h-wd c {u} {t} (right x) = trans~ (lemma-h**-right c) (trans~ (_≈₁_.refl , _≈₂_.cong _≈₂_.refl (_≈₂_.axiom x)) (sym~ (lemma-h**-right c)))
h-wd c {u} {t} (mid (comm a b)) = _≈₁_.trans _≈₁_.right-unit (_≈₁_.sym _≈₁_.left-unit) , reflₛ

open Reidemeister-Schreier-Full f h h-congₛ-gen h=⁻¹f-gen h-wd


aux-f* : ∀ {w} -> (f *) w ≡ [ ([_]ʷ *) w ]ₗ
aux-f* {[ x ]ʷ} = Eq.refl
aux-f* {ε} = Eq.refl
aux-f* {w • w₁} rewrite aux-f* {w} | aux-f* {w₁} = Eq.refl

f-well-defined : ∀ {w v} -> w ===₁ v -> (f *) w ≈₃ (f *) v
f-well-defined {w} {v} ax rewrite aux-f* {w} | aux-f* {v} | wconcatmap-[-]ʷ w | wconcatmap-[-]ʷ v = axiom (left ax)

[I]≈ε : [ I ] ≈₃ ε
[I]≈ε = _≈₃_.refl

ract = h

[_]ₓ = f *

lemma-comm1 : ∀ x w -> [ [ x ]ʷ ]ᵣ • [ w ]ₗ ≈₃ [ w ]ₗ • [ [ x ]ʷ ]ᵣ 
lemma-comm1 x [ x₁ ]ʷ = _≈₃_.sym (_≈₃_.axiom (mid (comm x₁ x)))
lemma-comm1 x ε = _≈₃_.trans _≈₃_.right-unit (_≈₃_.sym _≈₃_.left-unit)
lemma-comm1 x (w • w₁) with lemma-comm1 x w | lemma-comm1 x w₁
... | ih1 | ih2 = _≈₃_.trans (_≈₃_.sym _≈₃_.assoc ) (_≈₃_.trans (_≈₃_.cong ih1 _≈₃_.refl) (_≈₃_.trans _≈₃_.assoc (_≈₃_.trans (_≈₃_.cong refl ih2) (_≈₃_.sym _≈₃_.assoc)) ) )

lemma-comm : ∀ w v -> [ v ]ᵣ • [ w ]ₗ ≈₃ [ w ]ₗ • [ v ]ᵣ 
lemma-comm w [ x ]ʷ = lemma-comm1 x w
lemma-comm w ε = _≈₃_.trans _≈₃_.left-unit (_≈₃_.sym _≈₃_.right-unit)
lemma-comm w (v • v₁) with lemma-comm w v | lemma-comm w v₁
... | ih1 | ih2 = _≈₃_.sym (_≈₃_.trans (_≈₃_.sym _≈₃_.assoc ) (_≈₃_.trans (_≈₃_.cong (_≈₃_.sym ih1) _≈₃_.refl) (_≈₃_.trans _≈₃_.assoc (_≈₃_.trans (_≈₃_.cong refl (_≈₃_.sym ih2)) (_≈₃_.sym _≈₃_.assoc)) ) ))

lemma-ract : ∀ c y -> let (y' , c') = ract c y in [ c ] • [ y ]ʷ ≈₃ [ y' ]ₓ • [ c' ]
lemma-ract c (inj₁ x₁) rewrite lemma-h**-left' c {[ x₁ ]ʷ} = lemma-comm [ x₁ ]ʷ c
lemma-ract c (inj₂ y) = _≈₃_.sym _≈₃_.left-unit

open LeftRightCongruence Γ Δ Γₓ

[]-cong : ∀ {c d} -> c ≈ₛ d -> [ c ] ≈₃ [ d ]
[]-cong = rights

open RightAction f h h-congₛ-gen f-well-defined [_] []-cong [I]≈ε lemma-ract hiding ([_]ₓ)

nf0 = (anf f h h-congₛ-gen)

nf0-cong : ∀ {w v} -> w ≈₃ v -> nf0 w ~ nf0 v
nf0-cong {w} {v} = lemma-hypB I w v

-- lemma-nf0 : ∀ w v -> nf0 ([ w ]ₓ • [ v ]) ~ (w , v)
-- lemma-nf0 w v = {!!}

module NFP
  (nfp-Γ : NFProperty Γ)
  (nfp-Δ : NFProperty Δ)
  where

  open NFProperty nfp-Γ renaming (NF to NF₁ ; nf to nf₁ ; nf-injective to nf₁-inj ; nf-cong to nf₁-cong) using ()
  open NFProperty nfp-Δ renaming (NF to NF₂ ; nf to nf₂ ; nf-injective to nf₂-inj ; nf-cong to nf₂-cong) using ()

  nf : Word Y -> NF₁ × NF₂
  nf = map nf₁ nf₂ ∘ nf0

  import Function.Construct.Composition as FCC
  import Data.Product.Function.NonDependent.Setoid as FS
  open import Function.Bundles using (Injection)
  open import Function.Definitions using (Injective)

  nf-inj× : Injective _≈₃_ (PW.Pointwise _≡_ _≡_) nf
  nf-inj× {w} {v} = FCC.injective _≈₃_ _~_ (PW.Pointwise _≡_ _≡_) nf-isInjective' (map nf₁-inj nf₂-inj)

  nf-inj : Injective _≈₃_ _≡_ nf
  nf-inj {w} {v} = FCC.injective _≈₃_ (PW.Pointwise _≡_ _≡_) _≡_ nf-inj× PW.≡⇒≡×≡

  nf-cong : ∀ {w v} -> w ≈₃ v -> nf w ≡ nf v
  nf-cong {w} {v} eq = PW.≡×≡⇒≡ (FCC.congruent _≈₃_ _~_ (PW.Pointwise _≡_ _≡_) nf0-cong (map nf₁-cong nf₂-cong) eq)

  nfp : NFProperty (Γ ⸲ Δ ⸲ Γₓ)
  nfp = record { NF = NF₁ × NF₂ ; nf = nf ; nf-cong = nf-cong ; nf-injective = nf-inj }

module NFP'
  (nfp-Γ : NFProperty' Γ)
  (nfp-Δ : NFProperty' Δ)
  where

  open NFProperty' nfp-Γ renaming (hasNFProperty to nfp-Γ' ; NF to NF₁ ; nf to nf₁ ; nf-injective to nf₁-inj ; nf-cong to nf₁-cong ; inv-nf to inv-nf₁ ; inv-nf∘nf=id to inv-nf₁∘nf₁=id) using ()
  open NFProperty' nfp-Δ renaming (hasNFProperty to nfp-Δ' ; NF to NF₂ ; nf to nf₂ ; nf-injective to nf₂-inj ; nf-cong to nf₂-cong ; inv-nf to inv-nf₂ ; inv-nf∘nf=id to inv-nf₂∘nf₂=id) using ()

  open NFP nfp-Γ' nfp-Δ' using (nfp)
  open NFProperty nfp

  gg : NF₁ × NF₂ → Word Y
  gg (a , b) = ([_]ₓ ∘ inv-nf₁) a • ([_] ∘ inv-nf₂) b

  h**-hyp : ∀ c b -> let (b' , c') = (ract **) c b in
      [ c ] • b ≈₃ [ b' ]ₓ • [ c' ]
  h**-hyp c b = Star-Injective-Full.RightAction.lemma-⊛ Γ (Γ ⸲ Δ ⸲ Γₓ) C I f h f-well-defined [_] [I]≈ε lemma-ract c b

  f*-cong : ∀ {w v} -> w ≈₁ v -> (f *) w ≈₃ (f *) v
  f*-cong {w} {v} eq = Star-Congruence.lemma-f*-cong Γ (Γ ⸲ Δ ⸲ Γₓ) f f-well-defined eq


  ggnf=id : {w : Word Y} → gg (nf w) ≈₃ w
  ggnf=id {w} =
    let (a , b) = nf0 w in
    begin
    gg (nf w) ≈⟨ refl ⟩
    gg ((map nf₁ nf₂) (a , b)) ≈⟨ refl ⟩
    gg (nf₁ a , nf₂ b) ≈⟨ refl ⟩
    ([_]ₓ ∘ inv-nf₁ ∘ nf₁) a • ([_] ∘ inv-nf₂ ∘ nf₂) b ≈⟨ refl ⟩
    [ inv-nf₁ (nf₁ a)]ₓ • [ inv-nf₂ (nf₂ b) ] ≈⟨ cong (f*-cong inv-nf₁∘nf₁=id) refl ⟩
    [ a ]ₓ • [ inv-nf₂ (nf₂ b) ] ≈⟨ cong refl ([]-cong inv-nf₂∘nf₂=id) ⟩
    [ a ]ₓ • [ b ] ≈⟨ sym (h**-hyp ε w) ⟩
    [ I ] • w ≈⟨ refl ⟩
    ε • w ≈⟨ left-unit ⟩
    w ∎
    where
      open SR word-setoid₃
      
  nfp' : NFProperty' (Γ ⸲ Δ ⸲ Γₓ)
  nfp' = record
           { NF = NF ; nf = nf ; nf-cong = nf-cong ; inv-nf = gg ; inv-nf∘nf=id = ggnf=id }

module SNFP
  (nfp-Γ : SNFProperty Γ)
  (nfp-Δ : SNFProperty Δ)
  where

  open SNFProperty nfp-Γ renaming
    (hasNFProperty' to nfp-Γ' ; NF to NF₁ ; nf to nf₁ ; nf-injective to nf₁-inj ; nf-cong to nf₁-cong ; inv-nf to inv-nf₁ ; inv-nf∘nf=id to inv-nf₁∘nf₁=id) using ()
  open SNFProperty nfp-Δ renaming
    (hasNFProperty' to nfp-Δ' ; NF to NF₂ ; nf to nf₂ ; nf-injective to nf₂-inj ; nf-cong to nf₂-cong ; inv-nf to inv-nf₂ ; inv-nf∘nf=id to inv-nf₂∘nf₂=id) using ()

  open NFP' nfp-Γ' nfp-Δ' using (nfp' ; gg)
  open NFProperty' nfp'

{-
  nf-sur : (y : NF) → ∃ (λ w → {v : Word (A ⊎ B)} → v ≈₃ w → nf v ≡ y)
  nf-sur y@(a , b) = (inv-nf y) , (λ x → Eq.trans (nf-cong x) claim)
    where
    open ≡-Reasoning
    claim : nf (inv-nf (a , b)) ≡ (a , b)
    claim = begin
      nf (inv-nf (a , b)) ≡⟨ Eq.refl ⟩
      nf ([ inv-nf₁ a ]ₓ • [ inv-nf₂ b ]) ≡⟨ Eq.refl ⟩
      (map nf₁ nf₂ ∘ nf0) ([ inv-nf₁ a ]ₓ • [ inv-nf₂ b ]) ≡⟨ {!!} ⟩
      (a , b) ∎
  
  snfp : SNFProperty (Γ ⸲ Δ ⸲ Γₓ)
  snfp = record
           { NF = NF
           ; nf = nf
           ; nf-cong = nf-cong
           ; nf-injective = nf-injective
           ; nf-surjective = nf-sur
           }
-}
