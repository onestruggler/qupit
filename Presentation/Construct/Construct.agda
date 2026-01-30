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
open import Presentation.Base
open import Reidemeister-Schreier

module Presentation.Construct.Construct where

WREL : Set -> Set -> Set₁
WREL X Y = REL (Word X) (Word Y) 0ℓ

[_]ₗ : ∀ {A B} -> Word A -> Word (A ⊎ B)
[_]ₗ {A} {B} = wmap inj₁

[_]ᵣ : ∀ {A B} -> Word B -> Word (A ⊎ B)
[_]ᵣ {A} {B} = wmap inj₂


infix 5 _⸲_⸲_

data _⸲_⸲_ {A B} (Γ₁ : WRel A) (Γ₂ : WRel B) (Γ₃ : WRel (A ⊎ B)) : WRel (A ⊎ B) where
 left : ∀ {u v} -> Γ₁ u v -> ( Γ₁ ⸲ Γ₂ ⸲ Γ₃) [ u ]ₗ [ v ]ₗ
 right : ∀ {u v} -> Γ₂ u v -> ( Γ₁ ⸲  Γ₂ ⸲ Γ₃) [ u ]ᵣ [ v ]ᵣ
 mid : ∀ {u v} -> Γ₃ u v -> (Γ₁ ⸲ Γ₂ ⸲ Γ₃) u v


-- General product.
infix 4 _⍟_⋆_
_⍟_⋆_ : (p1 p2 : Pres) -> let A = Pres.X p1 in let B = Pres.X p2 in
  WRel (A ⊎ B) -> Pres
_⍟_⋆_ p1 p2 rel = ⟨ A ⊎ B ∣ Γ₁ ⸲ Γ₂ ⸲ rel ⟩
  where
    open Pres p1 renaming (X to A ; _===_ to Γ₁)
    open Pres p2 renaming (X to B ; _===_ to Γ₂)

-- Empty rel.
data Γₑ {A} : WRel A where 

-- Comm rel
data Γₓ {A B} : WRel (A ⊎ B) where
  comm : (a : A) (b : B) -> Γₓ ([ [ a ]ʷ ]ₗ • [ [ b ]ʷ ]ᵣ) ([ [ b ]ʷ ]ᵣ • [ [ a ]ʷ ]ₗ)

-- Semi comm rel.
data Γⱼ {N H} (conj : H -> N -> N) : WRel (N ⊎ H) where
  comm : (n : N) (h : H) -> Γⱼ conj ([ [ h ]ʷ ]ᵣ • [ [ n ]ʷ ]ₗ) ([ [ conj h n ]ʷ ]ₗ • [ [ h ]ʷ ]ᵣ)


record AmalData {M A B : Set}(p1 : Pres' (M ⊎ A)) (p2 : Pres' (M ⊎ B)) : Set₁ where
  P₁ = Pres'.pres p1
  P₂ = Pres'.pres p2
  field
    PM : Pres' M
    J₁ : Morphism.IsPresMonomorphism (Pres'.pres PM) P₁ ([_]ʷ ∘ inj₁)
    J₂ : Morphism.IsPresMonomorphism (Pres'.pres PM) P₂ ([_]ʷ ∘ inj₁)




-- Amalgamation rel.
data Γₐ {M A B : Set}(p1 : Pres' (M ⊎ A)) (p2 : Pres' (M ⊎ B)) : WRel ((M ⊎ A) ⊎ (M ⊎ B)) where
  amal : ∀ (x : M) -> Γₐ p1 p2 [ [ inj₁ x ]ʷ ]ₗ [ [ inj₁ x ]ʷ ]ᵣ

-- Free product.
infix 4 _⍟_
_⍟_ : (p1 p2 : Pres) -> Pres
_⍟_ p1 p2 = ⟨ A ⊎ B ∣ Γ₁ ⸲ Γ₂ ⸲ Γₑ ⟩
  where
    open Pres p1 renaming (X to A ; _===_ to Γ₁)
    open Pres p2 renaming (X to B ; _===_ to Γ₂)

-- Direct product.
infix 4 _⨂_
_⨂_ : (p1 p2 : Pres) -> Pres
_⨂_ p1 p2 = ⟨ A ⊎ B ∣ Γ₁ ⸲ Γ₂ ⸲ Γₓ ⟩
  where
    open Pres p1 renaming (X to A ; _===_ to Γ₁)
    open Pres p2 renaming (X to B ; _===_ to Γ₂)


-- Semi-direct product.
infix 4 _⋊_⋆_
_⋊_⋆_ : (p1 p2 : Pres) -> let N = Pres.X p1 in let H = Pres.X p2 in let _===₁_ = Pres._===_ p1 in let _===₂_ = Pres._===_ p2 in let _≈₁_ = Pres._≈_ p1 in
  (conj,hyp : ∃[ conj ] ((∀ {c d} n -> c ===₂ d -> (conj ʰ) c n ≡ (conj ʰ) d n) × (∀ c {w v} -> w ===₁ v -> (conj ⁿ) c w ≈₁ (conj ⁿ) c v))) -> Pres
_⋊_⋆_ p1 p2 conj,hyp = ⟨ N ⊎ H ∣ Γ₁ ⸲ Γ₂ ⸲ Γⱼ (proj₁ conj,hyp) ⟩
  where
    open Pres p1 renaming (X to N ; _===_ to Γ₁)
    open Pres p2 renaming (X to H ; _===_ to Γ₂)

-- Amalgamation product.
infix 4 _⨀_
_⨀_ : {M A B : Set}(p1 : Pres' (M ⊎ A)) (p2 : Pres' (M ⊎ B)) -> Pres
_⨀_ {M} {A} {B} p1 p2 = ⟨ (M ⊎ A) ⊎ (M ⊎ B) ∣ Γ₁ ⸲ Γ₂ ⸲ Γₐ p1 p2 ⟩
  where
    open Pres (Pres'.pres p1) renaming ( _===_ to Γ₁)
    open Pres (Pres'.pres p2) renaming ( _===_ to Γ₂)

{-
-- Amalgamation product.
infix 4 _⨀'_⋆_
_⨀'_⋆_ : (p1 p2 : Pres) -> let A = Pres.X p1 in let B = Pres.X p2 in
  AmalData p1 p2 -> Pres
_⨀'_⋆_ p1 p2 ad = ⟨ A ⊎ B ∣ Γ₁ ⸲ Γ₂ ⸲ Γₐ ad ⟩
  where
    open Pres p1 renaming (X to A ; _===_ to Γ₁)
    open Pres p2 renaming (X to B ; _===_ to Γ₂)
-}
module LeftRightCongruence
  (P₁ P₂ : Pres)
  (rel : let A = Pres.X P₁ in let B = Pres.X P₂ in WRel (A ⊎ B))
  where
  open Pres P₁ renaming (X to A ; _===_ to _===₁_ ; _≈_ to _≈₁_)
  open Pres P₂ renaming (X to B ; _===_ to _===₂_ ; _≈_ to _≈₂_)
  open Pres (P₁ ⍟ P₂ ⋆ rel) renaming (X to C ; _===_ to _===₃_ ; _≈_ to _≈₃_)

  lefts :  ∀ {u v} -> u ≈₁ v -> [ u ]ₗ ≈₃ [ v ]ₗ
  lefts {u} {v} refl = _≈₃_.refl
  lefts {u} {v} (sym h) = _≈₃_.sym (lefts h)
  lefts {u} {v} (trans h h₁) = _≈₃_.trans (lefts h) (lefts h₁)
  lefts {u} {v} (cong h h₁) = _≈₃_.cong (lefts h) (lefts h₁)
  lefts {u} {v} assoc = _≈₃_.assoc
  lefts {u} {v} left-unit = _≈₃_.left-unit
  lefts {u} {v} right-unit = _≈₃_.right-unit
  lefts {u} {v} (axiom x) = _≈₃_.axiom (left x)

  rights :  ∀ {u v} -> u ≈₂ v -> [ u ]ᵣ ≈₃ [ v ]ᵣ
  rights {u} {v} refl = _≈₃_.refl
  rights {u} {v} (sym h) = _≈₃_.sym (rights h)
  rights {u} {v} (trans h h₁) = _≈₃_.trans (rights h) (rights h₁)
  rights {u} {v} (cong h h₁) = _≈₃_.cong (rights h) (rights h₁)
  rights {u} {v} assoc = _≈₃_.assoc
  rights {u} {v} left-unit = _≈₃_.left-unit
  rights {u} {v} right-unit = _≈₃_.right-unit
  rights {u} {v} (axiom x) = _≈₃_.axiom (right x)



module DirectProductNF
  (P₁ P₂ : NFPres)
  where
  open NFPres P₁ renaming (X to A ; _===_ to _===₁_ ; _≈_ to _≈₁_ ; pres to p₁ ; NF to NF₁ ; f to f₁ ; f-cong to f₁-cong ; f-injective to f₁-inj) using ()
  open NFPres P₂ renaming (X to B ; _===_ to _===₂_ ; _≈_ to _≈₂_ ; pres to p₂ ; NF to NF₂ ; f to f₂ ; f-cong to f₂-cong ; f-injective to f₂-inj) using ()
  open Pres-Properties {B} {_===₂_} renaming (word-setoid to word-setoid₂) using ()

  open Pres (p₁ ⨂ p₂) renaming ( X to Y ; _===_ to _===₃_ ; _≈_ to _≈₃_)


  Cₛ = word-setoid₂

  I : Word B
  I = ε

  open Star-Injective-Full-Setoid p₁ (p₁ ⨂ p₂) Cₛ I renaming (nf to anf)


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
  f-well-defined {w} {v} ax rewrite aux-f* {w} | aux-f* {v} | lemma-wconcat-wmap0 w | lemma-wconcat-wmap0 v = _≈₃_.axiom (left ax)

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

  open LeftRightCongruence p₁ p₂ Γₓ

  []-cong : ∀ {c d} -> c ≈ₛ d -> [ c ] ≈₃ [ d ]
  []-cong = rights

  open RightAction f h h-congₛ-gen f-well-defined [_] []-cong [I]≈ε lemma-ract

  nf0 = (anf f h h-congₛ-gen)
  
  nf : Word Y -> NF₁ × NF₂
  nf = map f₁ f₂ ∘ nf0


  import Function.Construct.Composition as FCC
  import Data.Product.Function.NonDependent.Setoid as FS
  open import Function.Bundles using (Injection)
  open import Function.Definitions using (Injective)


  nf-inj× : Injective _≈₃_ (PW.Pointwise _≡_ _≡_) nf
  nf-inj× {w} {v} = FCC.injective _≈₃_ _~_ (PW.Pointwise _≡_ _≡_) nf-isInjective' (map f₁-inj f₂-inj)

  nf-inj : Injective _≈₃_ _≡_ nf
  nf-inj {w} {v} = FCC.injective _≈₃_ (PW.Pointwise _≡_ _≡_) _≡_ nf-inj× PW.≡⇒≡×≡

  nf0-cong : ∀ {w v} -> w ≈₃ v -> nf0 w ~ nf0 v
  nf0-cong {w} {v} = lemma-hypB I w v
  
  nf-cong : ∀ {w v} -> w ≈₃ v -> nf w ≡ nf v
  nf-cong {w} {v} eq = PW.≡×≡⇒≡ (FCC.congruent _≈₃_ _~_ (PW.Pointwise _≡_ _≡_) nf0-cong (map f₁-cong f₂-cong) eq)

  nfpres : NFPres
  nfpres = record { pres = p₁ ⨂ p₂ ; NF = NF₁ × NF₂ ; f = nf ;
    isRelMonomorphism = record {
      isHomomorphism = record { cong = nf-cong } ;
      injective = nf-inj } }


module DirectProductNF'
  (P₁ P₂ : NFPres')
  where
  open NFPres' P₁ renaming (X to A ; _===_ to _===₁_ ; _≈_ to _≈₁_ ; pres to p₁ ; NF to NF₁ ; f to f₁ ; f-cong to f₁-cong ; f-injective to f₁-inj ; g to g₁ ; gf=id to gf=id₁) using ()
  open NFPres' P₂ renaming (X to B ; _===_ to _===₂_ ; _≈_ to _≈₂_ ; pres to p₂ ; NF to NF₂ ; f to f₂ ; f-cong to f₂-cong ; f-injective to f₂-inj ; g to g₂ ; gf=id to gf=id₂) using ()
  open Pres-Properties {B} {_===₂_} renaming (word-setoid to word-setoid₂) using ()

  open Pres (p₁ ⨂ p₂) renaming ( X to Y ; _===_ to _===₃_ ; _≈_ to _≈₃_)


  Cₛ = word-setoid₂

  I : Word B
  I = ε

  open Star-Injective-Full-Setoid p₁ (p₁ ⨂ p₂) Cₛ I renaming (nf to anf)


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
  f-well-defined {w} {v} ax rewrite aux-f* {w} | aux-f* {v} | lemma-wconcat-wmap0 w | lemma-wconcat-wmap0 v = _≈₃_.axiom (left ax)

  [I]≈ε : [ I ] ≈₃ ε
  [I]≈ε = _≈₃_.refl

  ract = h

  [_]ₓ = f *

  f*-cong : ∀ {w v} -> w ≈₁ v -> (f *) w ≈₃ (f *) v
  f*-cong {w} {v} eq = Star-Congruence.lemma-f*-cong (NFPres'.pres P₁) (p₁ ⨂ p₂) f f-well-defined eq

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

  open LeftRightCongruence p₁ p₂ Γₓ

  []-cong : ∀ {c d} -> c ≈ₛ d -> [ c ] ≈₃ [ d ]
  []-cong = rights

  open RightAction f h h-congₛ-gen f-well-defined [_] []-cong [I]≈ε lemma-ract hiding ([_]ₓ)

  nf0 = (anf f h h-congₛ-gen)
  
  nf : Word Y -> NF₁ × NF₂
  nf = map f₁ f₂ ∘ nf0


  import Function.Construct.Composition as FCC
  import Data.Product.Function.NonDependent.Setoid as FS
  open import Function.Bundles using (Injection)
  open import Function.Definitions using (Injective)


  nf-inj× : Injective _≈₃_ (PW.Pointwise _≡_ _≡_) nf
  nf-inj× {w} {v} = FCC.injective _≈₃_ _~_ (PW.Pointwise _≡_ _≡_) nf-isInjective' (map f₁-inj f₂-inj)

  nf-inj : Injective _≈₃_ _≡_ nf
  nf-inj {w} {v} = FCC.injective _≈₃_ (PW.Pointwise _≡_ _≡_) _≡_ nf-inj× PW.≡⇒≡×≡

  nf0-cong : ∀ {w v} -> w ≈₃ v -> nf0 w ~ nf0 v
  nf0-cong {w} {v} = lemma-hypB I w v
  
  nf-cong : ∀ {w v} -> w ≈₃ v -> nf w ≡ nf v
  nf-cong {w} {v} eq = PW.≡×≡⇒≡ (FCC.congruent _≈₃_ _~_ (PW.Pointwise _≡_ _≡_) nf0-cong (map f₁-cong f₂-cong) eq)

  nfpres : NFPres
  nfpres = record { pres = p₁ ⨂ p₂ ; NF = NF₁ × NF₂ ; f = nf ;
    isRelMonomorphism = record {
      isHomomorphism = record { cong = nf-cong } ;
      injective = nf-inj } }

  open Pres-Properties {axioms = NFPres._===_ nfpres} renaming (word-setoid to word-setoid₃) using ()

  gg : NF₁ × NF₂ → Word Y
  gg (a , b) = ([_]ₓ ∘ g₁) a • ([_] ∘ g₂) b

  h**-hyp : ∀ c b -> let (b' , c') = (ract **) c b in
      [ c ] • b ≈₃ [ b' ]ₓ • [ c' ]
  h**-hyp c b = Star-Injective-Full.RightAction.lemma-⊛ (NFPres'.pres P₁) (p₁ ⨂ p₂) C I f h f-well-defined [_] [I]≈ε lemma-ract c b

  ggnf=id : {w : Word Y} → gg (nf w) ≈₃ w
  ggnf=id {w} =
    let (a , b) = nf0 w in
    begin
    gg (nf w) ≈⟨ refl ⟩
    gg ((map f₁ f₂) (a , b)) ≈⟨ refl ⟩
    gg (f₁ a , f₂ b) ≈⟨ refl ⟩
    ([_]ₓ ∘ g₁ ∘ f₁) a • ([_] ∘ g₂ ∘ f₂) b ≈⟨ refl ⟩
    [ g₁ (f₁ a)]ₓ • [ g₂ (f₂ b) ] ≈⟨ cong (f*-cong gf=id₁) refl ⟩
    [ a ]ₓ • [ g₂ (f₂ b) ] ≈⟨ cong refl ([]-cong gf=id₂) ⟩
    [ a ]ₓ • [ b ] ≈⟨ sym (h**-hyp ε w) ⟩
    [ I ] • w ≈⟨ refl ⟩
    ε • w ≈⟨ left-unit ⟩
    w ∎
    where
      open SR word-setoid₃
      
  nfpres' : NFPres'
  nfpres' = record { pres = p₁ ⨂ p₂ ; NF = NF₁ × NF₂ ; f = nf ; f-cong = nf-cong ; g = gg ;  gf=id = ggnf=id }


module SemiDirectProductNF
  (P₁ P₂ : NFPres)
  (conj : let H = (NFPres.X P₂) in let N = (NFPres.X P₁) in H -> N -> N)
  (conj-hyph : let _===₂_ = NFPres._===_ P₂ in ∀ {c d} n -> c ===₂ d -> (conj ʰ) c n ≡ (conj ʰ) d n)
  (conj-hypn : let _===₁_ = NFPres._===_ P₁ in let _≈₁_ = NFPres._≈_ P₁ in ∀ c {w v} -> w ===₁ v -> (conj ⁿ) c w ≈₁ (conj ⁿ) c v)
  where
  open NFPres P₁ renaming (X to N ; _===_ to _===₁_ ; _≈_ to _≈₁_ ; pres to p₁ ; NF to NF₁ ; f to f₁ ; f-cong to f₁-cong ; f-injective to f₁-inj ; refl' to refl'₁) using ()
  open Pres-Properties {N} {_===₁_} renaming (word-setoid to word-setoid₁) using ()

  open NFPres P₂ renaming (X to H ; _===_ to _===₂_ ; _≈_ to _≈₂_ ; pres to p₂ ; NF to NF₂ ; f to f₂ ; f-cong to f₂-cong ; f-injective to f₂-inj ; refl' to refl'₂) using ()
  open Pres-Properties {H} {_===₂_} renaming (word-setoid to word-setoid₂) using ()

  open Pres (p₁ ⋊ p₂ ⋆ (conj , conj-hyph , conj-hypn )) renaming ( X to Y ; _===_ to _===₃_ ; _≈_ to _≈₃_) using ()
  open Pres-Properties {Y} {_===₃_} renaming (word-setoid to word-setoid₃) using ()

  Cₛ = word-setoid₂

  I : Word H
  I = ε

  open Star-Injective-Full-Setoid p₁ (p₁ ⋊ p₂ ⋆ (conj , (conj-hyph , conj-hypn))) Cₛ I renaming (nf to anf)

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

  open Pres p₁
  
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
  conj-congNH = lemma-wfoldr _≈₁_ conj-congN

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
  ... | ih rewrite ih with aux-h0 h (wfoldr conj h₁ n)
  ... | ih2 rewrite ih2 = Eq.cong (λ ff → wfoldr (λ x → wmap (conj x)) h ff) ih

  aux-h : ∀ h n -> conjss' h [ n ]ʷ ≡ conjss h [ n ]ʷ
  aux-h [ x ]ʷ n = Eq.refl
  aux-h ε n = Eq.refl
  aux-h (h • h₁) n with aux-h h₁ n
  ... | ih rewrite ih with aux-h h (conjs' h₁ n)
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
  h-congₛ-gen-gen {c} {d} (inj₁ x) eq rewrite lemma-h**-left' c {[ x ]ʷ} | lemma-h**-left' d {[ x ]ʷ} = refl'₁ (Eq.cong [_]ʷ (conj-hyph x eq)) , _≈₂_.axiom eq
  h-congₛ-gen-gen {c} {d} (inj₂ y) eq = trans~ (lemma-h**-right c {[ y ]ʷ}) (trans~ (_≈₁_.refl , _≈₂_.cong (_≈₂_.axiom eq) (_≈₂_.refl)) (sym~ (lemma-h**-right d {[ y ]ʷ})))


  h-congₛ-gen : ∀ {c d} y -> c ≈ₛ d -> h c y ~ h d y
  h-congₛ-gen {c} {d} y refl = refl~
  h-congₛ-gen {c} {d} y (sym eq) = sym~ (h-congₛ-gen y eq)
  h-congₛ-gen {c} {d} y (trans eq eq₁) = trans~ (h-congₛ-gen y eq) (h-congₛ-gen y eq₁)
  h-congₛ-gen {c} {d} (inj₁ x) eqv@(Pres.cong eq eq₁) rewrite conj-congH x eqv = refl , _≈₂_.cong eq eq₁
  h-congₛ-gen {c} {d} (inj₂ y) (Pres.cong eq eq₁) = refl , _≈₂_.cong (_≈₂_.cong eq eq₁) _≈₂_.refl
  h-congₛ-gen {c} {d} (inj₁ x) Pres.assoc =  _≈₁_.refl ,  _≈₂_.assoc
  h-congₛ-gen {c} {d} (inj₂ y) Pres.assoc =  _≈₁_.refl ,  _≈₂_.cong  _≈₂_.assoc  _≈₂_.refl
  h-congₛ-gen {c} {d} (inj₁ x) Pres.left-unit =  _≈₁_.refl ,  _≈₂_.left-unit
  h-congₛ-gen {c} {d} (inj₂ y) Pres.left-unit =  _≈₁_.refl ,  _≈₂_.cong  _≈₂_.left-unit  _≈₂_.refl
  h-congₛ-gen {c} {d} (inj₁ x) Pres.right-unit =  _≈₁_.refl ,  _≈₂_.right-unit
  h-congₛ-gen {c} {d} (inj₂ y) Pres.right-unit =  _≈₁_.refl ,  _≈₂_.cong  _≈₂_.right-unit  _≈₂_.refl
  h-congₛ-gen {c} {d} y (axiom x) = h-congₛ-gen-gen y x

  h=⁻¹f-gen : ∀ (x : N) -> ([ x ]ʷ , I) ~ ((h **) I (f x))
  h=⁻¹f-gen x = refl~

  h-wd : ∀ (c : C){u t : Word Y} -> u ===₃ t -> ((h **) c u) ~ ((h **) c t)
  h-wd c {u} {t} (left {u₁} {v} x) rewrite lemma-h**-left' c {u₁} | lemma-h**-left' c {v} = conj-congNH c (axiom x) , _≈₂_.refl
  h-wd c {u} {t} (right {w} {v} x) = trans~ (lemma-h**-right c {w}) (trans~ (_≈₁_.refl , _≈₂_.cong _≈₂_.refl (_≈₂_.axiom x)) (sym~ (lemma-h**-right c {v})))
  h-wd c {u} {t} (mid (comm a b)) = trans left-unit (sym right-unit) , _≈₂_.refl

  open Reidemeister-Schreier-Full f h h-congₛ-gen h=⁻¹f-gen h-wd


  aux-f* : ∀ {w} -> (f *) w ≡ [ ([_]ʷ *) w ]ₗ
  aux-f* {[ x ]ʷ} = Eq.refl
  aux-f* {ε} = Eq.refl
  aux-f* {w • w₁} rewrite aux-f* {w} | aux-f* {w₁} = Eq.refl

  f-well-defined : ∀ {w v} -> w ===₁ v -> (f *) w ≈₃ (f *) v
  f-well-defined {w} {v} ax rewrite aux-f* {w} | aux-f* {v} | lemma-wconcat-wmap0 w | lemma-wconcat-wmap0 v = _≈₃_.axiom (left ax)

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
  lemma-ract c (inj₁ x₁) rewrite lemma-h**-left' c {[ x₁ ]ʷ} | lemma-ⁿʰ c [ x₁ ]ʷ | Eq.sym (conjss=conjs' c x₁) = lemma-comm' [ x₁ ]ʷ c
  lemma-ract c (inj₂ y) = _≈₃_.sym _≈₃_.left-unit

  open LeftRightCongruence p₁ p₂ Γₓ

  []-cong : ∀ {c d} -> c ≈ₛ d -> [ c ] ≈₃ [ d ]
  []-cong {c} {d} Pres.refl = _≈₃_.refl
  []-cong {c} {d} (Pres.sym eqv) = _≈₃_.sym ([]-cong eqv)
  []-cong {c} {d} (Pres.trans eqv eqv₁) = _≈₃_.trans ([]-cong eqv) ([]-cong eqv₁)
  []-cong {c} {d} (Pres.cong eqv eqv₁) = _≈₃_.cong ([]-cong eqv) ([]-cong eqv₁)
  []-cong {c} {d} Pres.assoc = _≈₃_.assoc
  []-cong {c} {d} Pres.left-unit = _≈₃_.left-unit
  []-cong {c} {d} Pres.right-unit = _≈₃_.right-unit
  []-cong {c} {d} (Pres.axiom x) = _≈₃_.axiom (right x)

  open RightAction f h h-congₛ-gen f-well-defined [_] []-cong [I]≈ε lemma-ract renaming (nf-isInjective' to nf0-inj)

  nf0 = (anf f h h-congₛ-gen)
  
  nf : Word Y -> NF₁ × NF₂
  nf = map f₁ f₂ ∘ nf0

  import Function.Construct.Composition as FCC
  import Data.Product.Function.NonDependent.Setoid as FS
  open import Function.Bundles using (Injection)
  open import Function.Definitions using (Injective)


  nf-inj× : Injective _≈₃_ (PW.Pointwise _≡_ _≡_) nf
  nf-inj× {w} {v} = FCC.injective _≈₃_ _~_ (PW.Pointwise _≡_ _≡_) nf0-inj (map f₁-inj f₂-inj)

  nf-inj : Injective _≈₃_ _≡_ nf
  nf-inj {w} {v} = FCC.injective _≈₃_ (PW.Pointwise _≡_ _≡_) _≡_ nf-inj× PW.≡⇒≡×≡

  nf0-cong : ∀ {w v} -> w ≈₃ v -> nf0 w ~ nf0 v
  nf0-cong {w} {v} = lemma-hypB I w v
  
  nf-cong : ∀ {w v} -> w ≈₃ v -> nf w ≡ nf v
  nf-cong {w} {v} eq = PW.≡×≡⇒≡ (FCC.congruent _≈₃_ _~_ (PW.Pointwise _≡_ _≡_) nf0-cong (map f₁-cong f₂-cong) eq)

  nfpres : NFPres
  nfpres = record { pres = p₁ ⋊ p₂ ⋆ (conj , (conj-hyph , conj-hypn)) ; NF = NF₁ × NF₂ ; f = nf ;
    isRelMonomorphism = record {
      isHomomorphism = record { cong = nf-cong } ;
      injective = nf-inj } }


module AmalProduct
  (P₁ P₂ : NFPres)
  (conj : let H = (NFPres.X P₂) in let N = (NFPres.X P₁) in H -> N -> N)
  (conj-hyph : let _===₂_ = NFPres._===_ P₂ in ∀ {c d} n -> c ===₂ d -> (conj ʰ) c n ≡ (conj ʰ) d n)
  (conj-hypn : let _===₁_ = NFPres._===_ P₁ in let _≈₁_ = NFPres._≈_ P₁ in ∀ c {w v} -> w ===₁ v -> (conj ⁿ) c w ≈₁ (conj ⁿ) c v)
  where
  open NFPres P₁ renaming (X to N ; _===_ to _===₁_ ; _≈_ to _≈₁_ ; pres to p₁ ; NF to NF₁ ; f to f₁ ; f-cong to f₁-cong ; f-injective to f₁-inj ; refl' to refl'₁) using ()
  open Pres-Properties {N} {_===₁_} renaming (word-setoid to word-setoid₁) using ()

  open NFPres P₂ renaming (X to H ; _===_ to _===₂_ ; _≈_ to _≈₂_ ; pres to p₂ ; NF to NF₂ ; f to f₂ ; f-cong to f₂-cong ; f-injective to f₂-inj ; refl' to refl'₂) using ()
  open Pres-Properties {H} {_===₂_} renaming (word-setoid to word-setoid₂) using ()

  open Pres (p₁ ⋊ p₂ ⋆ (conj , conj-hyph , conj-hypn )) renaming ( X to Y ; _===_ to _===₃_ ; _≈_ to _≈₃_) using ()
  open Pres-Properties {Y} {_===₃_} renaming (word-setoid to word-setoid₃) using ()

  Cₛ = word-setoid₂

  I : Word H
  I = ε

  open Star-Injective-Full-Setoid p₁ (p₁ ⋊ p₂ ⋆ (conj , (conj-hyph , conj-hypn))) Cₛ I renaming (nf to anf)

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

  open Pres p₁
  
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
  conj-congNH = lemma-wfoldr _≈₁_ conj-congN

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
  ... | ih rewrite ih with aux-h0 h (wfoldr conj h₁ n)
  ... | ih2 rewrite ih2 = Eq.cong (λ ff → wfoldr (λ x → wmap (conj x)) h ff) ih

  aux-h : ∀ h n -> conjss' h [ n ]ʷ ≡ conjss h [ n ]ʷ
  aux-h [ x ]ʷ n = Eq.refl
  aux-h ε n = Eq.refl
  aux-h (h • h₁) n with aux-h h₁ n
  ... | ih rewrite ih with aux-h h (conjs' h₁ n)
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
  h-congₛ-gen-gen {c} {d} (inj₁ x) eq rewrite lemma-h**-left' c {[ x ]ʷ} | lemma-h**-left' d {[ x ]ʷ} = refl'₁ (Eq.cong [_]ʷ (conj-hyph x eq)) , _≈₂_.axiom eq
  h-congₛ-gen-gen {c} {d} (inj₂ y) eq = trans~ (lemma-h**-right c {[ y ]ʷ}) (trans~ (_≈₁_.refl , _≈₂_.cong (_≈₂_.axiom eq) (_≈₂_.refl)) (sym~ (lemma-h**-right d {[ y ]ʷ})))


  h-congₛ-gen : ∀ {c d} y -> c ≈ₛ d -> h c y ~ h d y
  h-congₛ-gen {c} {d} y refl = refl~
  h-congₛ-gen {c} {d} y (sym eq) = sym~ (h-congₛ-gen y eq)
  h-congₛ-gen {c} {d} y (trans eq eq₁) = trans~ (h-congₛ-gen y eq) (h-congₛ-gen y eq₁)
  h-congₛ-gen {c} {d} (inj₁ x) eqv@(Pres.cong eq eq₁) rewrite conj-congH x eqv = refl , _≈₂_.cong eq eq₁
  h-congₛ-gen {c} {d} (inj₂ y) (Pres.cong eq eq₁) = refl , _≈₂_.cong (_≈₂_.cong eq eq₁) _≈₂_.refl
  h-congₛ-gen {c} {d} (inj₁ x) Pres.assoc =  _≈₁_.refl ,  _≈₂_.assoc
  h-congₛ-gen {c} {d} (inj₂ y) Pres.assoc =  _≈₁_.refl ,  _≈₂_.cong  _≈₂_.assoc  _≈₂_.refl
  h-congₛ-gen {c} {d} (inj₁ x) Pres.left-unit =  _≈₁_.refl ,  _≈₂_.left-unit
  h-congₛ-gen {c} {d} (inj₂ y) Pres.left-unit =  _≈₁_.refl ,  _≈₂_.cong  _≈₂_.left-unit  _≈₂_.refl
  h-congₛ-gen {c} {d} (inj₁ x) Pres.right-unit =  _≈₁_.refl ,  _≈₂_.right-unit
  h-congₛ-gen {c} {d} (inj₂ y) Pres.right-unit =  _≈₁_.refl ,  _≈₂_.cong  _≈₂_.right-unit  _≈₂_.refl
  h-congₛ-gen {c} {d} y (axiom x) = h-congₛ-gen-gen y x

  h=⁻¹f-gen : ∀ (x : N) -> ([ x ]ʷ , I) ~ ((h **) I (f x))
  h=⁻¹f-gen x = refl~

  h-wd : ∀ (c : C){u t : Word Y} -> u ===₃ t -> ((h **) c u) ~ ((h **) c t)
  h-wd c {u} {t} (left {u₁} {v} x) rewrite lemma-h**-left' c {u₁} | lemma-h**-left' c {v} = conj-congNH c (axiom x) , _≈₂_.refl
  h-wd c {u} {t} (right {w} {v} x) = trans~ (lemma-h**-right c {w}) (trans~ (_≈₁_.refl , _≈₂_.cong _≈₂_.refl (_≈₂_.axiom x)) (sym~ (lemma-h**-right c {v})))
  h-wd c {u} {t} (mid (comm a b)) = trans left-unit (sym right-unit) , _≈₂_.refl

  open Reidemeister-Schreier-Full f h h-congₛ-gen h=⁻¹f-gen h-wd


  aux-f* : ∀ {w} -> (f *) w ≡ [ ([_]ʷ *) w ]ₗ
  aux-f* {[ x ]ʷ} = Eq.refl
  aux-f* {ε} = Eq.refl
  aux-f* {w • w₁} rewrite aux-f* {w} | aux-f* {w₁} = Eq.refl

  f-well-defined : ∀ {w v} -> w ===₁ v -> (f *) w ≈₃ (f *) v
  f-well-defined {w} {v} ax rewrite aux-f* {w} | aux-f* {v} | lemma-wconcat-wmap0 w | lemma-wconcat-wmap0 v = _≈₃_.axiom (left ax)

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
  lemma-ract c (inj₁ x₁) rewrite lemma-h**-left' c {[ x₁ ]ʷ} | lemma-ⁿʰ c [ x₁ ]ʷ | Eq.sym (conjss=conjs' c x₁) = lemma-comm' [ x₁ ]ʷ c
  lemma-ract c (inj₂ y) = _≈₃_.sym _≈₃_.left-unit

  open LeftRightCongruence p₁ p₂ Γₓ

  []-cong : ∀ {c d} -> c ≈ₛ d -> [ c ] ≈₃ [ d ]
  []-cong {c} {d} Pres.refl = _≈₃_.refl
  []-cong {c} {d} (Pres.sym eqv) = _≈₃_.sym ([]-cong eqv)
  []-cong {c} {d} (Pres.trans eqv eqv₁) = _≈₃_.trans ([]-cong eqv) ([]-cong eqv₁)
  []-cong {c} {d} (Pres.cong eqv eqv₁) = _≈₃_.cong ([]-cong eqv) ([]-cong eqv₁)
  []-cong {c} {d} Pres.assoc = _≈₃_.assoc
  []-cong {c} {d} Pres.left-unit = _≈₃_.left-unit
  []-cong {c} {d} Pres.right-unit = _≈₃_.right-unit
  []-cong {c} {d} (Pres.axiom x) = _≈₃_.axiom (right x)

  open RightAction f h h-congₛ-gen f-well-defined [_] []-cong [I]≈ε lemma-ract renaming (nf-isInjective' to nf0-inj)

  nf0 = (anf f h h-congₛ-gen)
  
  nf : Word Y -> NF₁ × NF₂
  nf = map f₁ f₂ ∘ nf0

  import Function.Construct.Composition as FCC
  import Data.Product.Function.NonDependent.Setoid as FS
  open import Function.Bundles using (Injection)
  open import Function.Definitions using (Injective)


  nf-inj× : Injective _≈₃_ (PW.Pointwise _≡_ _≡_) nf
  nf-inj× {w} {v} = FCC.injective _≈₃_ _~_ (PW.Pointwise _≡_ _≡_) nf0-inj (map f₁-inj f₂-inj)

  nf-inj : Injective _≈₃_ _≡_ nf
  nf-inj {w} {v} = FCC.injective _≈₃_ (PW.Pointwise _≡_ _≡_) _≡_ nf-inj× PW.≡⇒≡×≡

  nf0-cong : ∀ {w v} -> w ≈₃ v -> nf0 w ~ nf0 v
  nf0-cong {w} {v} = lemma-hypB I w v
  
  nf-cong : ∀ {w v} -> w ≈₃ v -> nf w ≡ nf v
  nf-cong {w} {v} eq = PW.≡×≡⇒≡ (FCC.congruent _≈₃_ _~_ (PW.Pointwise _≡_ _≡_) nf0-cong (map f₁-cong f₂-cong) eq)

  nfpres : NFPres
  nfpres = record { pres = p₁ ⋊ p₂ ⋆ (conj , (conj-hyph , conj-hypn)) ; NF = NF₁ × NF₂ ; f = nf ;
    isRelMonomorphism = record {
      isHomomorphism = record { cong = nf-cong } ;
      injective = nf-inj } }



module Sugar-Product
  (npm : NFPres)
  (npa : NFPres)
  (f : NFPres.X npm -> Word (NFPres.X npa))
  (f-wd-ax : let _===₀_ = NFPres._===_ npm in let _≈₁_ = NFPres._≈_ npa in 
    ∀ {w v} -> w ===₀ v -> (f *) w ≈₁ (f *) v)
  where
  
  pm : Pres
  pm = NFPres.pres npm

  pa : Pres
  pa = NFPres.pres npa

  M = NFPres.X npm
  A = NFPres.X npa
  X = M ⊎ A

  data Γₛ : WRel X where
    emb : ∀ {m} -> Γₛ [ inj₁ m ]ʷ [ f m ]ᵣ 

  pma : Pres
  pma = pm ⍟ pa ⋆ Γₛ 

  to-right : X -> Word A
  to-right (inj₁ x) = f x
  to-right (inj₂ y) = [ y ]ʷ

  open Pres pma hiding (X)
  open Pres pm  renaming (_≈_ to _≈₀_ ; _===_ to _===₀_) using ()
  open NFPres npa renaming (_≈_ to _≈₁_ ; _===_ to _===₁_) using ()

  to-right-right : ∀ x -> [ x ]ʷ ≈ [ to-right x ]ᵣ
  to-right-right (inj₁ x) = axiom (mid emb)
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

  to-right-wd :  ∀ {w v} -> w === v -> (to-right *) w ≈₁ (to-right *) v
  to-right-wd {w} {v} (left {u} {v₁} x) = begin
    (to-right *) [ u ]ₗ ≡⟨ lemma-to-right-l u ⟩
    (f *) u ≈⟨ f-wd-ax x ⟩
    (f *) v₁ ≡⟨ Eq.sym (lemma-to-right-l v₁) ⟩
    (to-right *) [ v₁ ]ₗ ∎
    where
    open SR (Pres-Properties.word-setoid {axioms = _===₁_})

  to-right-wd {w} {v} (right {u} {v₁} x) rewrite lemma-to-right-r u | lemma-to-right-r v₁ = _≈₁_.axiom x
  to-right-wd {w} {v} (mid (emb {m})) rewrite lemma-to-right-r (f m) = _≈₁_.refl

  nf : Word X -> NFPres.NF npa
  nf = NFPres.f npa ∘ (to-right *)

  import Function.Construct.Composition as FCC
  open import Function.Definitions

  to-right*-cong = Star-Congruence.lemma-f*-cong pma pa to-right to-right-wd

  module MA = LeftRightCongruence pm pa Γₛ

  to-right*-inj : Injective _≈_ _≈₁_ (to-right *)
  to-right*-inj {x} {y} eq = begin
    x ≈⟨ to-right*-right x ⟩
    [ (to-right *) x ]ᵣ ≈⟨ MA.rights eq ⟩
    [ (to-right *) y ]ᵣ ≈⟨ sym (to-right*-right y) ⟩
    y ∎
    where
    open SR (Pres-Properties.word-setoid {axioms = _===_})
  nf-homo : Congruent _≈_ _≡_ nf
  nf-homo = FCC.congruent _≈_ _≈₁_ _≡_ to-right*-cong (NFPres.f-cong npa) 

  nf-inj : Injective _≈_ _≡_ nf
  nf-inj = FCC.injective _≈_ _≈₁_ _≡_ to-right*-inj (NFPres.f-injective npa)

  nfpres : NFPres
  nfpres = record { pres = pma ; NF = NFPres.NF npa ; f = nf ; isRelMonomorphism = record {
    isHomomorphism = record { cong = nf-homo } ;
    injective = nf-inj } }
