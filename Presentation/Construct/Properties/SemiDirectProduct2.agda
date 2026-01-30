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

module Presentation.Construct.Properties.SemiDirectProduct2
  {N H : Set}
  (Γ : WRel N)
  (Δ : WRel H)
  (conj : H -> N -> Word N)
  where

open PB Γ renaming (_===_ to _===₁_ ; _≈_ to _≈₁_ ; refl' to refl'₁ ; refl to refl₁ ; sym to sym₁ ; trans to trans₁ ; cong to cong₁ ; left-unit to left-unit₁ ; right-unit to right-unit₁) using ()
open PP Γ renaming (•-ε-monoid to m₁ ; word-setoid to word-setoid₁) using ()
open PB Δ renaming (_===_ to _===₂_ ; _≈_ to _≈₂_ ; axiom to axiom₂ ; refl to refl₂ ; sym to sym₂ ; trans to trans₂ ; cong to cong₂ ; right-unit to right-unit₂ ; left-unit to left-unit₂ ; assoc to assoc₂) using ()
open PP Δ renaming (•-ε-monoid to m₂ ; word-setoid to word-setoid₂) using ()


open PB (Γ ⸲ Δ ⸲ Γⱼ' conj) renaming (_===_ to _===₃_ ; _≈_ to _≈₃_ ; refl' to refl'₃) using ()
open PP (Γ ⸲ Δ ⸲ Γⱼ' conj) renaming (•-ε-monoid to m₃ ; word-setoid to word-setoid₃) using ()

open _≈₃_

Cₛ = word-setoid₂

I : Word H
I = ε

Y = N ⊎ H

open Star-Injective-Full-Setoid Γ (Γ ⸲ Δ ⸲ Γⱼ' conj) Cₛ I renaming (nf to anf)

[_] : C -> Word Y
[_] = [_]ᵣ

f : N -> Word Y
f x = [ [ x ]ʷ ]ₗ

conjs : H -> Word N -> Word N
conjs = conj ⁿ'

conjss : Word H -> Word N -> Word N
conjss = conj ʰ'

module _
  (conj-hyph : ∀ {c d} n -> c ===₂ d -> (conj ʰ') c n ≈₁ (conj ʰ') d n)
  (conj-hypn : ∀ c {w v} -> w ===₁ v -> (conj ⁿ') c w ≈₁ (conj ⁿ') c v)
  where

  conj-congN : ∀ h {ns ns'} -> ns ≈₁ ns' -> conjs h ns ≈₁ conjs h ns'
  conj-congN h {ns} {ns'} refl = _≈₁_.refl
  conj-congN h {ns} {ns'} (sym eq) = _≈₁_.sym (conj-congN h eq)
  conj-congN h {ns} {ns'} (trans eq eqₕ) = _≈₁_.trans (conj-congN h eq) (conj-congN h eqₕ)
  conj-congN h {ns} {ns'} (cong eq eqₕ) = (_≈₁_.cong (conj-congN h eq) (conj-congN h eqₕ))
  conj-congN h {ns} {ns'} assoc = _≈₁_.assoc
  conj-congN h {ns} {ns'} left-unit =  _≈₁_.left-unit
  conj-congN h {ns} {ns'} right-unit =  _≈₁_.right-unit
  conj-congN h {ns} {ns'} (axiom x) = conj-hypn h x

  conj-congNH : ∀ h {ns ns'} -> ns ≈₁ ns' -> conjss h ns ≈₁ conjss h ns'
  conj-congNH [ x ]ʷ {ns} {ns'} eq = conj-congN x eq
  conj-congNH ε {ns} {ns'} eq = eq
  conj-congNH (h • h₁) {ns} {ns'} eq = conj-congNH h ih1
    where
    ih1 : conjss h₁ ns ≈₁ conjss h₁ ns'
    ih1 = conj-congNH h₁ {ns} {ns'} eq
    
  lemma-conjss-ε : ∀ n -> conjss ε n ≡ n
  lemma-conjss-ε [ x ]ʷ = Eq.refl
  lemma-conjss-ε ε = Eq.refl
  lemma-conjss-ε (n • n₁) = Eq.refl

  conjss-homo : ∀ c w v -> conjss c (w • v) ≡ conjss c w • conjss c v
  conjss-homo [ x ]ʷ w v = Eq.refl
  conjss-homo ε w v = Eq.refl
  conjss-homo (c • c₁) w v with conjss-homo c₁ w v
  ... | ih with conjss-homo c (conjss c₁ w) (conjss c₁ v)
  ... | ih2 rewrite ih = ih2

  conjss-c-ε=ε : ∀ c -> conjss c ε ≡ ε
  conjss-c-ε=ε [ x ]ʷ = Eq.refl
  conjss-c-ε=ε ε = Eq.refl
  conjss-c-ε=ε (c • c₁) with conjss-c-ε=ε c₁
  ... | ih1 rewrite ih1 with conjss-c-ε=ε c
  ... | ih2 = ih2

  mutual
    conj-congH : ∀ {h1 h2} ns -> h1 ≈₂ h2 -> conjss h1 ns ≈₁ conjss h2 ns
    conj-congH {h1} {h2} ns PB.refl = refl₁
    conj-congH {h1} {h2} ns (PB.sym eq) = sym₁ (conj-congH ns eq)
    conj-congH {h1} {h2} ns (PB.trans eq eq₁) = trans₁ (conj-congH ns eq) (conj-congH ns eq₁)
    conj-congH {h1} {h2} ns (PB.cong eq eq₁) = conjss-cong eq (conj-congH ns eq₁)
    conj-congH {h1} {h2} ns PB.assoc = refl₁
    conj-congH {h1} {h2} ns PB.left-unit = refl₁
    conj-congH {h1} {h2} ns PB.right-unit = refl₁
    conj-congH {h1} {h2} ns (PB.axiom x) = conj-hyph ns x

    conjss-cong : ∀ {hs hs' ns ns'} -> hs ≈₂ hs' -> ns ≈₁ ns' -> conjss hs ns ≈₁ conjss hs' ns'
    conjss-cong {hs} {hs'} {ns} {ns'} eqh eqn = begin
      conjss hs ns ≈⟨ conj-congH ns eqh ⟩
      conjss hs' ns ≈⟨ conj-congNH hs' eqn ⟩
      conjss hs' ns' ∎
      where
        open SR word-setoid₁

  h : C -> Y -> Word N × C
  h c (inj₁ x) = conjss c [ x ]ʷ , c
  h c (inj₂ y) = ε , (c • [ y ]ʷ)

  ⁻¹f-gen : ∀ (x : N) -> ([ x ]ʷ , I) ~ ((h **) I (f x))
  ⁻¹f-gen x = _≈₁_.refl , _≈₂_.refl

  h-congₛ-gen-gen : ∀ {c d} y -> c ===₂ d -> h c y ~ h d y
  h-congₛ-gen-gen {c} {d} (inj₁ x) eq = conjss-cong (axiom₂ eq) refl₁ , (axiom₂ eq)
  h-congₛ-gen-gen {c} {d} (inj₂ y) eq = refl₁ , (cong₂ (axiom₂ eq) refl₂)

  h-congₛ-gen : ∀ {c d} y -> c ≈ₛ d -> h c y ~ h d y
  h-congₛ-gen {c} {d} y refl = refl~
  h-congₛ-gen {c} {d} y (sym eq) = sym~ (h-congₛ-gen y eq)
  h-congₛ-gen {c} {d} y (trans eq eq₁) = trans~ (h-congₛ-gen y eq) (h-congₛ-gen y eq₁)
  h-congₛ-gen {c} {d} y (axiom x) = h-congₛ-gen-gen y x
  h-congₛ-gen (inj₁ x₂) (PB.cong x x₁) = conjss-cong x (conjss-cong x₁ refl₁) , (cong₂ x x₁)
  h-congₛ-gen (inj₂ y) (PB.cong x x₁) = refl₁ , cong₂ (cong₂ x x₁) refl₂
  h-congₛ-gen (inj₁ x) PB.assoc = refl₁ , assoc₂
  h-congₛ-gen (inj₂ y) PB.assoc = refl₁ , cong₂ assoc₂ refl₂
  h-congₛ-gen (inj₁ x) PB.left-unit = refl₁ , left-unit₂
  h-congₛ-gen (inj₂ y) PB.left-unit = refl₁ , cong₂ left-unit₂ refl₂
  h-congₛ-gen (inj₁ x) PB.right-unit = refl₁ , right-unit₂
  h-congₛ-gen (inj₂ y) PB.right-unit = refl₁ , cong₂ right-unit₂ refl₂

  lemma-h**-left' : ∀ c {w} -> (h **) c [ w ]ₗ ≡ (conjss c w , c)
  lemma-h**-left' c {[ x ]ʷ} = Eq.refl
  lemma-h**-left' c {ε} = PW.≡×≡⇒≡ ((Eq.sym (conjss-c-ε=ε c)) , Eq.refl)
  lemma-h**-left' c {w • w₁} rewrite lemma-h**-left' c {w} | lemma-h**-left' c {w₁} = PW.≡×≡⇒≡ ((Eq.sym (conjss-homo c w w₁)) , Eq.refl)

  lemma-h**-left : ∀ c {w} -> (h **) c [ w ]ₗ ~ (conjss c w , c)
  lemma-h**-left c {w} with lemma-h**-left' c {w}
  ... | ih rewrite ih = _≈₁_.refl , _≈₂_.refl 

  lemma-h**-right : ∀ c {w} -> (h **) c [ w ]ᵣ ~ (ε , c • w)
  lemma-h**-right c {[ x ]ʷ} = _≈₁_.refl , _≈₂_.refl
  lemma-h**-right c {ε} = _≈₁_.refl , _≈₂_.sym _≈₂_.right-unit
  lemma-h**-right c {w • w₁} with (h **) c [ w ]ᵣ | inspect ((h **) c) [ w ]ᵣ
  ... | (w' , c') | [ eq1 ]' with (h **) c' [ w₁ ]ᵣ | inspect ((h **) c') [ w₁ ]ᵣ
  ... | (w₁' , c'') | [ eq2 ]' with lemma-h**-right c {w} | lemma-h**-right c' {w₁}
  ... | ih1 | ih2 rewrite eq1 | eq2 = (_≈₁_.trans (_≈₁_.cong (ih1 .proj₁) (ih2 .proj₁)) _≈₁_.right-unit) , _≈₂_.trans (ih2 .proj₂) (_≈₂_.trans (_≈₂_.cong (ih1 .proj₂) _≈₂_.refl) _≈₂_.assoc )

  h=⁻¹f-gen : ∀ (x : N) -> ([ x ]ʷ , I) ~ ((h **) I (f x))
  h=⁻¹f-gen x = refl~
  
  h-wd : ∀ (c : C){u t : Word Y} -> u ===₃ t -> ((h **) c u) ~ ((h **) c t)
  h-wd c {u} {t} (left {u₁} {v} x) rewrite lemma-h**-left' c {u₁} | lemma-h**-left' c {v} = conj-congNH c (_≈₁_.axiom x) , _≈₂_.refl
  h-wd c {u} {t} (right {w} {v} x) = trans~ (lemma-h**-right c {w}) (trans~ (_≈₁_.refl , _≈₂_.cong _≈₂_.refl (_≈₂_.axiom x)) (sym~ (lemma-h**-right c {v})))
  h-wd c {u} {t} (mid (comm a b)) =
    let (w1 , c1) = (h **) c ([ conj b a ]ₗ) in
    let (w2 , c2) = (h **) c1 [ inj₂ b ]ʷ in
    let (w3 , c3) = (h **) c [ inj₂ b ]ʷ in
    let (eq1 , eq2) = lemma-h**-left c {(conj b a)} in
    begin
    (h **) c ([ inj₂ b ]ʷ • [ inj₁ a ]ʷ) ≈⟨ left-unit₁ , refl₂ ⟩
    (h **) (c • [ b ]ʷ) ([ inj₁ a ]ʷ) ≈⟨ lemma-h**-left (c • [ b ]ʷ) ⟩
    (conjss (c • [ b ]ʷ) [ a ]ʷ , c • [ b ]ʷ) ≈⟨ sym₁ right-unit₁ , refl₂ ⟩
    (conjss c (conj b a) • (ε) , c • [ b ]ʷ) ≈⟨ cong₁ (sym₁ eq1) refl₁ , cong₂ (sym₂ eq2) refl₂ ⟩
    (h **) c ([ conj b a ]ₗ • [ inj₂ b ]ʷ) ∎
      where
        open SR setoid-WX-Cₛ

  open Reidemeister-Schreier-Full f h h-congₛ-gen h=⁻¹f-gen h-wd


  aux-f* : ∀ {w} -> (f *) w ≡ [ ([_]ʷ *) w ]ₗ
  aux-f* {[ x ]ʷ} = Eq.refl
  aux-f* {ε} = Eq.refl
  aux-f* {w • w₁} rewrite aux-f* {w} | aux-f* {w₁} = Eq.refl

  f-well-defined : ∀ {w v} -> w ===₁ v -> (f *) w ≈₃ (f *) v
  f-well-defined {w} {v} ax rewrite aux-f* {w} | aux-f* {v} | wconcatmap-[-]ʷ w | wconcatmap-[-]ʷ v = _≈₃_.axiom (left ax)

  [I]≈ε : [ I ] ≈₃ ε
  [I]≈ε = _≈₃_.refl

  ract = h

  [_]ₓ = f *

  aux-f*' : ∀ {w} -> [ w ]ₓ ≡ [ w ]ₗ
  aux-f*' {[ x ]ʷ} = Eq.refl
  aux-f*' {ε} = Eq.refl
  aux-f*' {w • w₁} rewrite aux-f*' {w} | aux-f*' {w₁} = Eq.refl


  lemma-comm1 : ∀ x w -> [ [ x ]ʷ ]ᵣ • [ w ]ₗ ≈₃ [ conjs x w ]ₗ • [ [ x ]ʷ ]ᵣ 
  lemma-comm1 x [ x₁ ]ʷ = (_≈₃_.axiom (mid (comm x₁ x)))
  lemma-comm1 x ε = _≈₃_.trans _≈₃_.right-unit (_≈₃_.sym _≈₃_.left-unit)
  lemma-comm1 x (w • w₁) with lemma-comm1 x w | lemma-comm1 x w₁
  ... | ih1 | ih2 = _≈₃_.trans (_≈₃_.sym _≈₃_.assoc ) (_≈₃_.trans (_≈₃_.cong ih1 _≈₃_.refl) (_≈₃_.trans _≈₃_.assoc (_≈₃_.trans (_≈₃_.cong _≈₃_.refl ih2) (_≈₃_.sym _≈₃_.assoc)) ) )

  lemma-comm : ∀ w v -> [ v ]ᵣ • [ w ]ₗ ≈₃ [ conjss v w ]ₗ • [ v ]ᵣ 
  lemma-comm w [ x ]ʷ = lemma-comm1 x w
  lemma-comm w ε = _≈₃_.trans _≈₃_.left-unit (_≈₃_.sym _≈₃_.right-unit)
  lemma-comm w (v • v₁) with lemma-comm w v₁
  ... | ih2 with lemma-comm (conjss v₁ w) v
  ... | ih1 = _≈₃_.sym (_≈₃_.trans (_≈₃_.sym _≈₃_.assoc ) (_≈₃_.trans (_≈₃_.cong (_≈₃_.sym ih1) _≈₃_.refl) (_≈₃_.trans _≈₃_.assoc (_≈₃_.trans (_≈₃_.cong _≈₃_.refl (_≈₃_.sym ih2)) (_≈₃_.sym _≈₃_.assoc)) ) ))

  lemma-comm' : ∀ w v -> [ v ]ᵣ • [ w ]ₗ ≈₃ [ conjss v w ]ₗ • [ v ]ᵣ 
  lemma-comm' w v with lemma-comm w v
  ... | fact = fact
  
  lemma-ract : ∀ c y -> let (y' , c') = ract c y in [ c ] • [ y ]ʷ ≈₃ [ y' ]ₓ • [ c' ]
  lemma-ract c y@(inj₁ x₁) rewrite lemma-h**-left' c {[ x₁ ]ʷ} = begin
    [ c ]ᵣ • [ y ]ʷ ≈⟨ lemma-comm [ x₁ ]ʷ c ⟩
    [ conjss c [ x₁ ]ʷ ]ₗ • [ c ]ᵣ ≈⟨ cong (refl'₃ (Eq.sym (aux-f*' {conjss c [ x₁ ]ʷ}))) refl ⟩
    [ conjss c [ x₁ ]ʷ ]ₓ • [ c ] ∎
    where open SR word-setoid₃
  lemma-ract c (inj₂ y) = _≈₃_.sym _≈₃_.left-unit

  open LeftRightCongruence Γ Δ Γₓ

  []-cong : ∀ {c d} -> c ≈ₛ d -> [ c ] ≈₃ [ d ]
  []-cong {c} {d} refl = _≈₃_.refl
  []-cong {c} {d} (sym eqv) = _≈₃_.sym ([]-cong eqv)
  []-cong {c} {d} (trans eqv eqv₁) = _≈₃_.trans ([]-cong eqv) ([]-cong eqv₁)
  []-cong {c} {d} (cong eqv eqv₁) = _≈₃_.cong ([]-cong eqv) ([]-cong eqv₁)
  []-cong {c} {d} assoc = _≈₃_.assoc
  []-cong {c} {d} left-unit = _≈₃_.left-unit
  []-cong {c} {d} right-unit = _≈₃_.right-unit
  []-cong {c} {d} (axiom x) = _≈₃_.axiom (right x)

  open RightAction f h h-congₛ-gen f-well-defined [_] []-cong [I]≈ε lemma-ract renaming (nf-isInjective' to nf0-inj) hiding ([_]ₓ)

  nf0 = (anf f h h-congₛ-gen)

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
    nf-inj× {w} {v} = FCC.injective _≈₃_ _~_ (PW.Pointwise _≡_ _≡_) nf0-inj (map nf₁-inj nf₂-inj)

    nf-inj : Injective _≈₃_ _≡_ nf
    nf-inj {w} {v} = FCC.injective _≈₃_ (PW.Pointwise _≡_ _≡_) _≡_ nf-inj× PW.≡⇒≡×≡

    nf0-cong : ∀ {w v} -> w ≈₃ v -> nf0 w ~ nf0 v
    nf0-cong {w} {v} = lemma-hypB I w v

    nf-cong : ∀ {w v} -> w ≈₃ v -> nf w ≡ nf v
    nf-cong {w} {v} eq = PW.≡×≡⇒≡ (FCC.congruent _≈₃_ _~_ (PW.Pointwise _≡_ _≡_) nf0-cong (map nf₁-cong nf₂-cong) eq)

    nfp : NFProperty (Γ ⸲ Δ ⸲ Γⱼ' conj)
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
    h**-hyp c b = Star-Injective-Full.RightAction.lemma-⊛ Γ (Γ ⸲ Δ ⸲ Γⱼ' conj) C I f h f-well-defined [_] [I]≈ε lemma-ract c b

    f*-cong : ∀ {w v} -> w ≈₁ v -> (f *) w ≈₃ (f *) v
    f*-cong {w} {v} eq = Star-Congruence.lemma-f*-cong Γ (Γ ⸲ Δ ⸲ Γⱼ' conj) f f-well-defined eq


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

    nfp' : NFProperty' (Γ ⸲ Δ ⸲ Γⱼ' conj)
    nfp' = record
             { NF = NF ; nf = nf ; nf-cong = nf-cong ; inv-nf = gg ; inv-nf∘nf=id = ggnf=id }

