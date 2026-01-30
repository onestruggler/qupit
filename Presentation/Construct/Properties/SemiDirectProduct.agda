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

module Presentation.Construct.Properties.SemiDirectProduct
  {N H : Set}
  (Γ : WRel N)
  (Δ : WRel H)
  (conj : H -> N -> N)
  where

open PB Γ renaming (_===_ to _===₁_ ; _≈_ to _≈₁_ ; refl' to refl'₁) using ()
open PP Γ renaming (•-ε-monoid to m₁ ; word-setoid to word-setoid₁) using ()
open PB Δ renaming (_===_ to _===₂_ ; _≈_ to _≈₂_) using ()
open PP Δ renaming (•-ε-monoid to m₂ ; word-setoid to word-setoid₂) using ()


open PB (Γ ⸲ Δ ⸲ Γⱼ conj) renaming (_===_ to _===₃_ ; _≈_ to _≈₃_) using ()
open PP (Γ ⸲ Δ ⸲ Γⱼ conj) renaming (•-ε-monoid to m₃ ; word-setoid to word-setoid₃) using ()

open _≈₃_

Cₛ = word-setoid₂

I : Word H
I = ε

Y = N ⊎ H

open Star-Injective-Full-Setoid Γ (Γ ⸲ Δ ⸲ Γⱼ conj) Cₛ I renaming (nf to anf)

[_] : C -> Word Y
[_] = [_]ᵣ

f : N -> Word Y
f x = [ [ x ]ʷ ]ₗ

conjs : H -> Word N -> Word N
conjs = conj ⁿ

conjs' : Word H -> N -> N
conjs' = conj ʰ

conjss : Word H -> Word N -> Word N
conjss = conjs ʰ

conjss' : Word H -> Word N -> Word N
conjss' = conjs' ⁿ

module _
  (conj-hyph : ∀ {c d} n -> c ===₂ d -> (conj ʰ) c n ≡ (conj ʰ) d n)
  (conj-hypn : ∀ c {w v} -> w ===₁ v -> (conj ⁿ) c w ≈₁ (conj ⁿ) c v)
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
  conj-congNH = lemma-wfoldr _≈₁_ _≈₁_ conj-congN

  lemma-conjss-on-ε : ∀ h -> conjss h ε ≈₁ ε
  lemma-conjss-on-ε [ x ]ʷ = _≈₁_.refl
  lemma-conjss-on-ε ε = _≈₁_.refl
  lemma-conjss-on-ε (h • h₁) with lemma-conjss-on-ε h₁ | lemma-conjss-on-ε h 
  ... | ih1 | ih = begin
    conjss h ( (conjss h₁ ε)) ≈⟨ conj-congNH h _≈₁_.refl ⟩
    conjss h (conjss h₁ ε) ≈⟨ conj-congNH h ih1 ⟩
    conjss h ε ≈⟨ ih ⟩
    ε ∎
    where
    open import Relation.Binary.Reasoning.Setoid word-setoid₁

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

  conjss=conjs' : ∀ c x -> conjss c [ x ]ʷ ≡ [ conjs' c x ]ʷ
  conjss=conjs' [ x₁ ]ʷ x = Eq.refl
  conjss=conjs' ε x = Eq.refl
  conjss=conjs' (c • c₁) x with conjss=conjs' c₁ x
  ... | ih with conjss=conjs' c (conjs' c₁  x )
  ... | ih2 rewrite ih = ih2

  conjs'=conjs : ∀ h x -> [ conjs' [ h ]ʷ x ]ʷ  ≡ conjs h [ x ]ʷ
  conjs'=conjs h x = Eq.refl


  lemma-conjss-conjs' : ∀ h n -> conjss h [ n ]ʷ ≈₁ [ conjs' h n ]ʷ
  lemma-conjss-conjs' h n rewrite conjss=conjs' h n = _≈₁_.refl

  conjhs = conjs'

  mutual
    conj-congH : ∀ {h1 h2} n -> h1 ≈₂ h2 -> conjhs h1 n ≡ conjhs h2 n
    conj-congH {h1} {h2} n refl = Eq.refl
    conj-congH {h1} {h2} n (sym eq) rewrite conj-congH {h2} {h1} n eq = Eq.refl
    conj-congH {h1} {h2} n (trans {v = v} eq eq₁) rewrite conj-congH n eq | conj-congH n eq₁ = Eq.refl
    conj-congH {h1} {h2} n (cong {w} {w'} {v} {v'} eq eq₁) with conj-congH n eq₁
    ... | ih rewrite ih with conj-congH ((conj ʰ) v' n) eq
    ... | ih2 = ih2
    conj-congH {h1} {h2} n assoc = Eq.refl
    conj-congH {h1} {h2} n left-unit = Eq.refl
    conj-congH {h1} {h2} n right-unit = Eq.refl
    conj-congH {h1} {h2} n (axiom x) = conj-hyph n x

    conj-congHN : ∀ {hs hs'} ns -> hs ≈₂ hs' -> conjss hs ns ≈₁ conjss hs' ns
    conj-congHN {hs} {hs'} ns refl = _≈₁_.refl
    conj-congHN {hs} {hs'} ns (sym eq) = _≈₁_.sym (conj-congHN ns eq)
    conj-congHN {hs} {hs'} ns (trans eq eq₁) = _≈₁_.trans (conj-congHN ns eq) (conj-congHN ns eq₁)
    conj-congHN {hs} {hs'} n (cong {w} {w'} {v} {v'} eq eq₁) =  begin
      conjss (w • v) n ≈⟨ _≈₁_.refl ⟩
      conjss w ( (conjss v n)) ≈⟨ conj-congNH w _≈₁_.refl ⟩
      conjss w ((conjss v n)) ≈⟨ conj-congNH w (conj-congHN n eq₁) ⟩
      conjss w ((conjss v' n)) ≈⟨ conj-congHN (conjss v' n) eq ⟩
      conjss w' ((conjss v' n)) ≈⟨ conj-congNH w' (_≈₁_.sym _≈₁_.refl) ⟩
      conjss w' ( (conjss v' n)) ≈⟨ _≈₁_.refl ⟩
      conjss (w' • v') n ∎
      where open SR word-setoid₁
    conj-congHN {hs} {hs'} ns assoc = _≈₁_.refl
    conj-congHN {hs} {hs'} ns left-unit = _≈₁_.refl
    conj-congHN {hs} {h2} ns right-unit = begin
      conjss (h2 • ε) ns ≈⟨ _≈₁_.refl ⟩
      conjss h2 ( (conjss ε ns)) ≈⟨ conj-congNH h2 _≈₁_.refl ⟩
      conjss h2 (conjss ε ns) ≈⟨ _≈₁_.refl ⟩
      conjss h2 ( ns) ≈⟨  conj-congNH h2 _≈₁_.refl ⟩
      conjss h2 ns ∎
      where open SR word-setoid₁
    conj-congHN {hs} {hs'} [ x₁ ]ʷ (axiom x) = begin
      conjss hs [ x₁ ]ʷ ≈⟨ claim hs x₁ ⟩
      [ conjhs hs x₁ ]ʷ ≡⟨  Eq.cong [_]ʷ (conj-congH x₁ (_≈₂_.axiom x)) ⟩
      [ conjhs hs' x₁ ]ʷ ≈⟨ _≈₁_.sym (claim hs' x₁) ⟩
      conjss hs' [ x₁ ]ʷ ∎
      where
        open SR word-setoid₁
        claim : ∀ hs x -> conjss hs [ x ]ʷ ≈₁ [ conjhs hs x ]ʷ
        claim [ x₁ ]ʷ x = _≈₁_.refl
        claim ε x = _≈₁_.refl
        claim (hs • hs₁) x = begin
          conjss (hs • hs₁) [ x ]ʷ ≈⟨ _≈₁_.refl ⟩
          conjss hs ( (conjss hs₁ [ x ]ʷ)) ≈⟨  conj-congNH hs _≈₁_.refl ⟩
          conjss hs ((conjss hs₁ [ x ]ʷ)) ≈⟨ conj-congNH hs (claim hs₁ x) ⟩
          conjss hs (([ conjhs hs₁ x ]ʷ)) ≈⟨ conj-congNH hs (_≈₁_.sym _≈₁_.refl) ⟩
          conjss hs ( ([ conjhs hs₁ x ]ʷ)) ≈⟨ claim hs (conjhs hs₁ x) ⟩
          [ conjhs (hs • hs₁) x ]ʷ ∎
    conj-congHN {hs} {hs'} ε (axiom x) = begin
      conjss hs ε ≈⟨ _≈₁_.trans _≈₁_.refl (lemma-conjss-on-ε hs) ⟩
      ε ≈⟨ _≈₁_.sym (_≈₁_.trans _≈₁_.refl (lemma-conjss-on-ε hs')) ⟩
      conjss hs' ε ∎
      where
        open SR word-setoid₁

    conj-congHN {hs} {hs'} (ns • ms) (axiom x) = begin
      conjss hs (ns • ms) ≡⟨ conjss-homo hs ns ms ⟩
      conjss hs ns • conjss hs ms ≈⟨ _≈₁_.cong (conj-congHN ns (_≈₂_.axiom x)) (conj-congHN ms (_≈₂_.axiom x)) ⟩
      conjss hs' ns • conjss hs' ms ≡⟨ Eq.sym (conjss-homo hs' ns ms) ⟩
      conjss hs' (ns • ms) ∎
      where
        open SR word-setoid₁


    conjss-cong : ∀ {hs hs' ns ns'} -> hs ≈₂ hs' -> ns ≈₁ ns' -> conjss hs ns ≈₁ conjss hs' ns'
    conjss-cong {hs} {hs'} {ns} {ns'} eqh eqn = begin
      conjss hs ns ≈⟨ conj-congHN ns eqh ⟩
      conjss hs' ns ≈⟨ conj-congNH hs' eqn ⟩
      conjss hs' ns' ∎
      where
        open SR word-setoid₁

  aux-h0 : ∀ h n -> [ conjs' h n ]ʷ ≡ conjss h [ n ]ʷ
  aux-h0 [ x ]ʷ n = Eq.refl
  aux-h0 ε n = Eq.refl
  aux-h0 (h • h₁) n with aux-h0 h₁ n
  ... | ih with aux-h0 h (wfoldr conj h₁ n)
  ... | ih2 rewrite ih2 = Eq.cong (λ ff → wfoldr (λ x → wmap (conj x)) h ff) ih

  aux-h : ∀ h n -> conjss' h [ n ]ʷ ≡ conjss h [ n ]ʷ
  aux-h [ x ]ʷ n = Eq.refl
  aux-h ε n = Eq.refl
  aux-h (h • h₁) n with aux-h h₁ n
  ... | ih  with aux-h h (conjs' h₁ n)
  ... | ih2 rewrite aux-h0 h₁ n  = ih2

  lemma-ⁿʰ : ∀ h n -> conjss' h n ≡ conjss h n
  lemma-ⁿʰ h [ x ]ʷ = aux-h h x
  lemma-ⁿʰ h ε rewrite conjss-c-ε=ε h = Eq.refl
  lemma-ⁿʰ h (n • n₁) with lemma-ⁿʰ h n
  ... | ih rewrite ih with lemma-ⁿʰ h n₁
  ... | ih2 rewrite ih2 | conjss-homo h n n₁ = Eq.refl


  h : C -> Y -> Word N × C
  h c (inj₁ x) = [ conjs' c x ]ʷ  , c
  h c (inj₂ y) = ε , (c • [ y ]ʷ)

  ⁻¹f-gen : ∀ (x : N) -> ([ x ]ʷ , I) ~ ((h **) I (f x))
  ⁻¹f-gen x = _≈₁_.refl , _≈₂_.refl

  lemma-h**-left' : ∀ c {w} -> (h **) c [ w ]ₗ ≡ (conjss c w , c)
  lemma-h**-left' c {[ x ]ʷ} = PW.≡×≡⇒≡ ((Eq.sym (conjss=conjs' c x)) , Eq.refl)
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


  h-congₛ-gen-gen : ∀ {c d} y -> c ===₂ d -> h c y ~ h d y
  h-congₛ-gen-gen {c} {d} (inj₁ x) eq = refl'₁ (Eq.cong [_]ʷ (conj-hyph x eq)) , _≈₂_.axiom eq
  h-congₛ-gen-gen {c} {d} (inj₂ y) eq = trans~ (lemma-h**-right c {[ y ]ʷ}) (trans~ (_≈₁_.refl , _≈₂_.cong (_≈₂_.axiom eq) (_≈₂_.refl)) (sym~ (lemma-h**-right d {[ y ]ʷ})))


  h-congₛ-gen : ∀ {c d} y -> c ≈ₛ d -> h c y ~ h d y
  h-congₛ-gen {c} {d} y refl = refl~
  h-congₛ-gen {c} {d} y (sym eq) = sym~ (h-congₛ-gen y eq)
  h-congₛ-gen {c} {d} y (trans eq eq₁) = trans~ (h-congₛ-gen y eq) (h-congₛ-gen y eq₁)
  h-congₛ-gen {c} {d} (inj₁ x) eqv@(cong eq eq₁) rewrite conj-congH x eqv = _≈₁_.refl , _≈₂_.cong eq eq₁
  h-congₛ-gen {c} {d} (inj₂ y) (cong eq eq₁) = _≈₁_.refl , _≈₂_.cong (_≈₂_.cong eq eq₁) _≈₂_.refl
  h-congₛ-gen {c} {d} (inj₁ x) assoc = _≈₁_.refl ,  _≈₂_.assoc
  h-congₛ-gen {c} {d} (inj₂ y) assoc = _≈₁_.refl ,  _≈₂_.cong  _≈₂_.assoc  _≈₂_.refl
  h-congₛ-gen {c} {d} (inj₁ x) left-unit = _≈₁_.refl ,  _≈₂_.left-unit
  h-congₛ-gen {c} {d} (inj₂ y) left-unit = _≈₁_.refl ,  _≈₂_.cong  _≈₂_.left-unit  _≈₂_.refl
  h-congₛ-gen {c} {d} (inj₁ x) right-unit = _≈₁_.refl ,  _≈₂_.right-unit
  h-congₛ-gen {c} {d} (inj₂ y) right-unit = _≈₁_.refl ,  _≈₂_.cong  _≈₂_.right-unit  _≈₂_.refl
  h-congₛ-gen {c} {d} y (axiom x) = h-congₛ-gen-gen y x

  h=⁻¹f-gen : ∀ (x : N) -> ([ x ]ʷ , I) ~ ((h **) I (f x))
  h=⁻¹f-gen x = refl~

  h-wd : ∀ (c : C){u t : Word Y} -> u ===₃ t -> ((h **) c u) ~ ((h **) c t)
  h-wd c {u} {t} (left {u₁} {v} x) rewrite lemma-h**-left' c {u₁} | lemma-h**-left' c {v} = conj-congNH c (_≈₁_.axiom x) , _≈₂_.refl
  h-wd c {u} {t} (right {w} {v} x) = trans~ (lemma-h**-right c {w}) (trans~ (_≈₁_.refl , _≈₂_.cong _≈₂_.refl (_≈₂_.axiom x)) (sym~ (lemma-h**-right c {v})))
  h-wd c {u} {t} (mid (comm a b)) = _≈₁_.trans _≈₁_.left-unit (_≈₁_.sym _≈₁_.right-unit) , _≈₂_.refl

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

  lemma-comm' : ∀ w v -> [ v ]ᵣ • [ w ]ₗ ≈₃ [ conjss' v w ]ₗ • [ v ]ᵣ 
  lemma-comm' w v with lemma-comm w v
  ... | fact rewrite lemma-ⁿʰ v w = fact
  
  lemma-ract : ∀ c y -> let (y' , c') = ract c y in [ c ] • [ y ]ʷ ≈₃ [ y' ]ₓ • [ c' ]
  lemma-ract c (inj₁ x₁) = lemma-comm' [ x₁ ]ʷ c
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

    nfp : NFProperty (Γ ⸲ Δ ⸲ Γⱼ conj)
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
    h**-hyp c b = Star-Injective-Full.RightAction.lemma-⊛ Γ (Γ ⸲ Δ ⸲ Γⱼ conj) C I f h f-well-defined [_] [I]≈ε lemma-ract c b

    f*-cong : ∀ {w v} -> w ≈₁ v -> (f *) w ≈₃ (f *) v
    f*-cong {w} {v} eq = Star-Congruence.lemma-f*-cong Γ (Γ ⸲ Δ ⸲ Γⱼ conj) f f-well-defined eq


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

    nfp' : NFProperty' (Γ ⸲ Δ ⸲ Γⱼ conj)
    nfp' = record
             { NF = NF ; nf = nf ; nf-cong = nf-cong ; inv-nf = gg ; inv-nf∘nf=id = ggnf=id }
