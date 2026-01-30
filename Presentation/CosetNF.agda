{-# OPTIONS  --safe #-}
open import Relation.Nullary.Decidable using (via-injection)
open import Relation.Binary.PropositionalEquality as Eq renaming ([_] to [_]') using ( _≡_ ; inspect)
open import Relation.Binary using (IsEquivalence ; Setoid ; Rel)

open import Data.Unit using (⊤ ; tt)
open import Data.Sum using ([_,_] ; _⊎_ ; inj₁ ; inj₂)
open import Data.Sum.Properties using (inj₁-injective)
open import Data.Product using (_,_ ; _×_ ; proj₁ ; proj₂ ; map ; ∃)
open import Data.Product.Relation.Binary.Pointwise.NonDependent as PW
open import Data.List hiding ([_] ; map)

open import Function.Definitions using (Injective ; Surjective)
open import Function using (_∘_ ; id)
open import Function.Bundles using (Injection)

import Relation.Binary.Reasoning.Setoid as SR
import Function.Construct.Composition as FCC


open import Word.Base
open import Word.Properties
open import Presentation.Reidemeister-Schreier

import Presentation.Base as PB
import Presentation.Properties as PP
open PP using (NFProperty ; NFProperty')

module Presentation.CosetNF where
module Data
  {X Y : Set}
  (Γ : WRel X)
  (Δ : WRel Y)
  (C : Set)
  (I : C)
  (f : X -> Word Y)
  (h : C -> Y -> Word X × C)
  ([_] : C -> Word Y)
  where

  open PB Γ renaming (_===_ to _===₁_ ; _≈_ to _≈₁_) using ()
  open PB Δ renaming (_===_ to _===₂_ ; _≈_ to _≈₂_) using ()
  open PP Γ renaming (•-ε-monoid to m₁ ; word-setoid to word-setoid₁) using ()
  open PP Δ renaming (•-ε-monoid to m₂ ; word-setoid to word-setoid₂) using ()

  infix 4 _~_
  _~_ = PW.Pointwise _≈₁_ (_≡_ {A = C})

  module Assumptions-And-Theorems
    -- inv-f'-gen : ∀ x c -> inv-f' (f' x c) ~ x c 
    (h=⁻¹f-gen : ∀ (x : X) -> ([ x ]ʷ , I) ~ ((h **) I (f x)))
    (h-wd-ax : ∀ (c : C){u t : Word Y} -> u ===₂ t -> ((h **) c u) ~ ((h **) c t))
    (f-wd-ax : ∀ {w v} -> w ===₁ v -> (f *) w ≈₂ (f *) v)
    ([I]≈ε : [ I ] ≈₂ ε)
    -- inv-h-gen : ∀ c b -> inv-h (h c b) ≈₂ c b. 
    (h=ract :  ∀ c b -> let (b' , c') = h c b in let [_]ₓ = f * in
      [ c ] • [ b ]ʷ ≈₂ [ b' ]ₓ • [ c' ])
    where

    -- Above data gives an injective well-definded map from "Word Y ->
    -- Word X × C". If in addition, Pres X has normal form property,
    -- then so is Pres Y.

    [_]ₓ = f *

    f*-cong : ∀ {w v} -> w ≈₁ v -> (f *) w ≈₂ (f *) v
    f*-cong = Star-Congruence.lemma-f*-cong Γ Δ f f-wd-ax

    nf : Word Y -> Word X × C
    nf = (h **) I

    h**-hyp : ∀ c b -> let (b' , c') = (h **) c b in
        [ c ] • b ≈₂ [ b' ]ₓ • [ c' ]
    h**-hyp c b = Star-Injective-Full.RightAction.lemma-⊛ Γ Δ C I f h f-wd-ax [_] [I]≈ε h=ract c b

    nf-wd : ∀ {u t : Word Y} -> u ≈₂ t -> nf u ~ nf t
    nf-wd {u} {t} = Star-Injective-Full.Reidemeister-Schreier-Full.lemma-hypB Γ Δ C I f h h=⁻¹f-gen h-wd-ax I u t

    h-wd : ∀ c {u t : Word Y} -> u ≈₂ t -> (h **) c u ~ (h **) c t
    h-wd c {u} {t} = Star-Injective-Full.Reidemeister-Schreier-Full.lemma-hypB Γ Δ C I f h h=⁻¹f-gen h-wd-ax c u t

    f-wd : ∀ {w v} -> w ≈₁ v -> (f *) w ≈₂ (f *) v
    f-wd {w} {v} eqv = Star-Injective-Full.RightAction.[]ₓ-wd Γ Δ C I f h f-wd-ax [_] [I]≈ε h=ract eqv


    nf-injective : Injective _≈₂_ _~_ nf
    nf-injective = Star-Injective-Full.RightAction.nf-isInjective Γ Δ C I f h f-wd-ax [_] [I]≈ε h=ract

    inv-nf : Word X × C -> Word Y
    inv-nf (w , c) = (f *) w • [ c ]

    inv-nf-wd : ∀ {u t : Word X × C} -> u ~ t -> inv-nf u ≈₂ inv-nf t
    inv-nf-wd = Star-Injective-Full.RightAction.⁻¹nf-wd Γ Δ C I f h f-wd-ax [_] [I]≈ε h=ract

    inv-nf-surjective : Surjective _~_ _≈₂_ inv-nf
    inv-nf-surjective = Star-Injective-Full.RightAction.⁻¹nf-isSurjective Γ Δ C I f h f-wd-ax [_] [I]≈ε h=ract


    inf-nf∘nf=id : ∀ {w} -> inv-nf (nf w) ≈₂ w
    inf-nf∘nf=id {w} = Star-Injective-Full.RightAction.⁻¹nf-nf=id Γ Δ C I f h f-wd-ax [_] [I]≈ε h=ract

    -- f * is injective due to h ∘ f is identity on Word X, which is
    -- derivable from h=⁻¹f-gen.
    f*-injective : (w v : Word X) -> (f *) w ≈₂ (f *) v -> w ≈₁ v
    f*-injective = Star-Injective-Full.Reidemeister-Schreier-Full.reidemeister-schreier Γ Δ C I f h h=⁻¹f-gen h-wd-ax

    nfx : Word Y -> Word X
    nfx = Star-Injective-Full.Reidemeister-Schreier-Full.g Γ Δ C I f h h=⁻¹f-gen h-wd-ax


    nfp : NFProperty Γ -> NFProperty Δ
    nfp nfp1 = record { NF = NF₁ × C ; nf = nf' ; nf-cong = nf'-cong ; nf-injective = nf'-inj }
      where
        open NFProperty nfp1 renaming (NF to NF₁ ; nf to f₁ ; nf-cong to f₁-cong ; nf-injective to f₁-inj) using ()

        nf' : Word Y -> NF₁ × C
        nf' = map f₁ id ∘ nf

        nf'-inj× : Injective _≈₂_ (PW.Pointwise _≡_ _≡_) nf'
        nf'-inj× {w} {v} = FCC.injective _≈₂_ _~_ (PW.Pointwise _≡_ _≡_) nf-injective (map f₁-inj λ {x} z → z)

        nf'-inj : Injective _≈₂_ _≡_ nf'
        nf'-inj {w} {v} = FCC.injective _≈₂_ (PW.Pointwise _≡_ _≡_) _≡_ nf'-inj× PW.≡⇒≡×≡

        nf-cong : ∀ {w v} -> w ≈₂ v -> nf w ~ nf v
        nf-cong = nf-wd

        nf'-cong : ∀ {w v} -> w ≈₂ v -> nf' w ≡ nf' v
        nf'-cong {w} {v} eq = PW.≡×≡⇒≡ (FCC.congruent _≈₂_ _~_ (PW.Pointwise _≡_ _≡_) nf-cong (map f₁-cong λ {x} z → z) eq)


    nfp' : NFProperty' Γ -> NFProperty' Δ
    nfp' nfp1 = record { NF = NF₁ × C ; nf = nf' ; nf-cong = nf-cong ; inv-nf = gg ; inv-nf∘nf=id = ggnf'=id }
      where
        open NFProperty' nfp1 renaming (hasNFProperty to nfp-Γ' ; NF to NF₁ ; nf to f₁ ; nf-cong to f₁-cong ; nf-injective to f₁-inj ; inv-nf to g₁ ; inv-nf∘nf=id to gf=id) using ()

        open NFProperty (nfp nfp-Γ') renaming (nf to nf')

        gg : NF₁ × C → Word Y
        gg (n , c) = [ g₁ n ]ₓ • [ c ]

        ggnf'=id : {w : Word Y} → gg (nf' w) ≈₂ w
        ggnf'=id  {w} =
          let (w' , c) = nf w in
          begin
          gg (nf' w) ≈⟨ _≈₂_.refl ⟩
          gg ((map f₁ id)(nf w)) ≈⟨ _≈₂_.refl ⟩
          gg ((map f₁ id)(w' , c)) ≈⟨ _≈₂_.refl ⟩
          gg (f₁ w' , c) ≈⟨ _≈₂_.refl ⟩
          [ g₁ (f₁ w') ]ₓ • [ c ] ≈⟨ _≈₂_.cong (f*-cong (gf=id)) _≈₂_.refl ⟩
          [ w' ]ₓ • [ c ] ≈⟨ _≈₂_.sym (h**-hyp I w) ⟩
          [ I ] • w ≈⟨ _≈₂_.cong [I]≈ε _≈₂_.refl ⟩
          ε • w ≈⟨ _≈₂_.left-unit ⟩
          w ∎
          where
            open SR word-setoid₂


module Data-CT
  {M A : Set}
  (P₁ : WRel M)
  (P₂ : WRel A)
  (C : Set)
  (f : M -> Word A)
  (h : C ⊎ ⊤ -> A -> Word M × (C ⊎ ⊤))
  ([_]ₒ : C -> Word A)
  where

  open PB P₁ renaming (_===_ to _===₁_ ; _≈_ to _≈₁_) using ()
  open PP P₁ renaming (•-ε-monoid to m₁ ; word-setoid to word-setoid₁) using ()
  open PB P₂ renaming (_===_ to _===₂_ ; _≈_ to _≈₂_) using ()
  open PP P₂ renaming (•-ε-monoid to m₂ ; word-setoid to word-setoid₂) using ()

  open _≈₂_

  infix 4 _~_
  _~_ = PW.Pointwise _≈₁_ (_≡_ {A = C ⊎ ⊤})

  s1ct : Setoid _ _
  s1ct = PW.×-setoid word-setoid₁ (Eq.setoid (C ⊎ ⊤))

  [_]ₓ = f *

  I : C ⊎ ⊤
  I = inj₂ tt

  [_] : C ⊎ ⊤ -> Word A
  [_] = [_,_] [_]ₒ (λ v → ε)

  module Assumptions-And-Theorems
    --inv-f'-gen : ∀ x c -> inv-f' (f' x c) ~ x c 
    (hcme : ∀ c m -> ∃ \ w -> ∃ \ c' -> ((h **) (inj₁ c) (f m)) ≡ (w , inj₁ c'))
    (htme : ∀ m -> ((h **) (inj₂ tt) (f m)) ≡ ([ m ]ʷ , inj₂ tt))
    (htme~ : ∀ (m : M) -> ([ m ]ʷ , I) ~ ((h **) I (f m)))
    (hcme~ : ∀ (c : C) (m : M) -> let (w' , c' , p) = hcme c m in [ c ]ₒ • f m ≈₂ [ w' ]ₓ • [ c' ]ₒ)
    (h-wd-ax : ∀ (c : C ⊎ ⊤){u t : Word A} -> u ===₂ t -> ((h **) c u) ~ ((h **) c t))
    (f-wd-ax : ∀ {w v} -> w ===₁ v -> (f *) w ≈₂ (f *) v)
    -- inv-h-gen : ∀ c b -> inv-h (h c b) ≈₂ c b. 
    (h=ract :  ∀ c y -> let (m' , c') = h c y in
      [ c ] • [ y ]ʷ ≈₂ [ m' ]ₓ • [ c' ])
    where

    hcm : C -> M -> Word M × C
    hcm c m with hcme c m
    ... | w , c' , hyp = w , c'

    hca : C -> A -> Word M × (C ⊎ ⊤)
    hca c a = h (inj₁ c) a

    hcm' : C ⊎ ⊤ -> M -> Word M × (C ⊎ ⊤)
    hcm' (inj₁ d) m with hcm d m
    ... | (wm , d') = wm , inj₁ d'
    hcm' (inj₂ tt) m = [ m ]ʷ , (inj₂ tt)

    htm : ⊤ -> M -> Word M × ⊤
    htm tt m = [ m ]ʷ , tt

    htm-hyp : ∀ m -> htm tt m ≡ ([ m ]ʷ , tt)
    htm-hyp m = Eq.refl

    hcmw = hcm **
    hcmw' = hcm' **

    h**-hyp : ∀ c w -> let (m' , c') = (h **) c w in
       [ c ] • w ≈₂ [ m' ]ₓ • [ c' ]
    h**-hyp c [ x ]ʷ = h=ract c x
    h**-hyp c ε = _≈₂_.trans _≈₂_.right-unit (_≈₂_.sym _≈₂_.left-unit)
    h**-hyp c (w • v) =
      let (wv' , c2) = (h **) c (w • v) in
      let (w' , c') = (h **) c w in
      let (v' , c'') = (h **) c' v in
      begin
      [ c ] • (w • v) ≈⟨ sym assoc ⟩
      ([ c ] • w) • v ≈⟨ cong (h**-hyp c w) refl ⟩
      ([ w' ]ₓ • [ c' ]) • v ≈⟨ assoc ⟩
      [ w' ]ₓ • [ c' ] • v ≈⟨ cong refl (h**-hyp c' v) ⟩
      [ w' ]ₓ • [ v' ]ₓ • [ c2 ] ≈⟨ sym assoc ⟩
      [ wv' ]ₓ • [ c2 ] ∎
      where
      open SR word-setoid₂

    hcm-hyp :  ∀ c m -> let (m' , c') = hcm c m in
     [ c ]ₒ • f m ≈₂ [ m' ]ₓ • [ c' ]ₒ
    hcm-hyp c m with hcme c m | hcme~ c m | (h**-hyp) (inj₁ c) (f m)
    ... | w , c' , hyp | h2 | h3 rewrite hyp = h3

    hcm'-hyp :  ∀ c m -> let (m' , c') = hcm' c m in
     [ c ] • f m ≈₂ [ m' ]ₓ • [ c' ]
    hcm'-hyp (inj₂ tt) m with htme m | htme~ m | (h**-hyp) (inj₂ tt) (f m)
    ... |  hyp | h2 | h3 rewrite hyp = h3
    hcm'-hyp (inj₁ c) m with hcme c m | hcme~ c m | (h**-hyp) (inj₁ c) (f m)
    ... | w , c' , hyp | h2 | h3 rewrite hyp = h3


    hca-hyp :  ∀ c a -> let (w , c') = hca c a in
     [ c ]ₒ • [ a ]ʷ ≈₂ [ w ]ₓ • [ c' ]
    hca-hyp c a = h=ract (inj₁ c) a


    lemma-**-act3 :
      {Y X D : Set}
      (py : WRel Y) (_⊕_ : D -> X -> Word X × D) ([_] : D -> Word Y) (f : X -> Word Y) ->
      let
          open PB py using (_≈_)
      in
      (hyp : (c : D) (x : X) -> ([ c ] • f x) ≈ (f *) ((c ⊕ x) .proj₁) • [ (c ⊕ x) .proj₂ ])
      -> -- -------------------------------------------------------------------------------------
      ∀ (c : D) (w : Word X) -> let _⊕'_ = _⊕_ ** in [ c ] • (f *) w ≈ (f *) ((c ⊕' w) .proj₁) • [ (c ⊕' w) .proj₂ ]
    lemma-**-act3 {Y} {X} {D} py _⊕_ [_] f hyp c [ x ]ʷ = hyp c x
    lemma-**-act3 {Y} {X} {D} py _⊕_ [_] f hyp c ε = _≈_.trans _≈_.right-unit (_≈_.sym _≈_.left-unit)
      where
        open PB py
    lemma-**-act3 {Y} {X} {D} py _⊕_ [_] f hyp c (w • v)  with (_⊕_ **) c w | inspect (((_⊕_) **) c) w
    ... | (w' , c') | [ Eq.refl ]' with (_⊕_ **) c' v | inspect ((_⊕_ **) c') v
    ... | (v' , c'') | [ Eq.refl ]' = claim
      where
        open PB py
        open PP py renaming (word-setoid to ws) using ()

        -- eval : Word X × D -> Word X
        -- eval wc = (wc .proj₁) • [ wc .proj₂ ]
        infix 4 _⊕'_ 
        _⊕'_ = _⊕_ **

        [_]ₓ' = f *

        open SR ws

        claim : [ c ] • [ w • v ]ₓ' ≈ [ w' • v' ]ₓ' • [ c'' ]
        claim = begin
          [ c ] • [ w • v ]ₓ' ≈⟨ _≈_.sym _≈_.assoc ⟩
          ([ c ] • [ w ]ₓ') • [ v ]ₓ' ≈⟨ _≈_.cong (lemma-**-act3 py _⊕_ [_] f hyp c w) _≈_.refl ⟩
          ([ w' ]ₓ' • [ c' ]) • [ v ]ₓ' ≈⟨ _≈_.assoc ⟩
          [ w' ]ₓ' • [ c' ] • [ v ]ₓ' ≈⟨ _≈_.cong _≈_.refl (lemma-**-act3 py _⊕_ [_] f hyp c' v) ⟩
          [ w' ]ₓ' • [ v' ]ₓ' • [ c'' ] ≈⟨ _≈_.sym _≈_.assoc ⟩
          [ w' • v' ]ₓ' • [ c'' ] ∎



    hcmw-hyp :  ∀ c m -> let (m' , c') = hcmw c m in
       [ c ]ₒ • [ m ]ₓ ≈₂ [ m' ]ₓ • [ c' ]ₒ
    hcmw-hyp c m = lemma-**-act3 P₂ hcm [_]ₒ f hcm-hyp c m

    hcmw'-hyp :  ∀ c m -> let (m' , c') = hcmw' c m in
       [ c ] • [ m ]ₓ ≈₂ [ m' ]ₓ • [ c' ]
    hcmw'-hyp c m = lemma-**-act3 P₂ hcm' [_] f hcm'-hyp c m


    [I]≡ε : [ inj₂ tt ] ≡ ε
    [I]≡ε = Eq.refl

    [I]≈ε : [ I ] ≈₂ ε
    [I]≈ε rewrite [I]≡ε = _≈₂_.refl

    module myData = Data P₁ P₂ (C ⊎ ⊤) (inj₂ tt) f h [_]

    open myData.Assumptions-And-Theorems htme~ h-wd-ax f-wd-ax [I]≈ε h=ract using (f*-injective ; nfx ; h-wd ; f-wd ; nfp') public 


    lemma-h**=hcmw : ∀ c w -> let (w' , c') = hcmw c w in
      (h **) (inj₁ c) [ w ]ₓ ≡ (w' , inj₁ c')
    lemma-h**=hcmw c [ x ]ʷ with hcme c x
    ... | (w , c' , p) = p
    lemma-h**=hcmw c ε = Eq.refl
    lemma-h**=hcmw c (w • w₁) rewrite lemma-h**=hcmw c w | lemma-h**=hcmw (hcmw c w .proj₂) w₁ = Eq.refl

    hcmw-cong : ∀ c w v -> w ≈₁ v -> hcmw c w .proj₁ ≈₁ hcmw c v .proj₁
    hcmw-cong c w v eq =
      begin
      hcmw c w .proj₁ ≡⟨ Eq.sym ( Eq.cong proj₁ (lemma-h**=hcmw c w)) ⟩
      (h **) (inj₁ c) [ w ]ₓ .proj₁ ≈⟨ proj₁ (h-wd (inj₁ c) (f-wd eq)) ⟩
      (h **) (inj₁ c) [ v ]ₓ .proj₁ ≡⟨ Eq.cong proj₁ (lemma-h**=hcmw c v) ⟩
      hcmw c v .proj₁ ∎
      where
      open SR word-setoid₁

    hcmw-cong2 : ∀ c w v -> w ≈₁ v -> hcmw c w .proj₂ ≡ hcmw c v .proj₂
    hcmw-cong2 c w v eq = inj₁-injective ( 
      begin
      inj₁ (hcmw c w .proj₂) ≡⟨ Eq.sym ( Eq.cong proj₂ (lemma-h**=hcmw c w)) ⟩
      (h **) (inj₁ c) [ w ]ₓ .proj₂ ≡⟨ proj₂ (h-wd (inj₁ c) (f-wd eq)) ⟩
      (h **) (inj₁ c) [ v ]ₓ .proj₂ ≡⟨ Eq.cong proj₂ (lemma-h**=hcmw c v) ⟩
      inj₁ (hcmw c v .proj₂) ∎)
      where
      open Eq.≡-Reasoning


    lemma-h**=hcmw' : ∀ c w -> let (w' , c') = hcmw' c w in
      (h **) c [ w ]ₓ ≡ (w' , c')
    lemma-h**=hcmw' (inj₁ c) [ x ]ʷ with hcme c x
    ... | (w , c' , p) = p
    lemma-h**=hcmw' (inj₂ tt) [ x ]ʷ with htme x
    ... | (p) = p
    lemma-h**=hcmw' c ε = Eq.refl
    lemma-h**=hcmw' c (w • w₁) rewrite lemma-h**=hcmw' c w | lemma-h**=hcmw' (hcmw' c w .proj₂) w₁ = Eq.refl


    hcmw-cong' : ∀ c w v -> w ≈₁ v -> hcmw' c w .proj₁ ≈₁ hcmw' c v .proj₁
    hcmw-cong' c w v eq =
      begin
      hcmw' c w .proj₁ ≡⟨ Eq.sym ( Eq.cong proj₁ (lemma-h**=hcmw' c w)) ⟩
      (h **) ( c) [ w ]ₓ .proj₁ ≈⟨ proj₁ (h-wd ( c) (f-wd eq)) ⟩
      (h **) ( c) [ v ]ₓ .proj₁ ≡⟨ Eq.cong proj₁ (lemma-h**=hcmw' c v) ⟩
      hcmw' c v .proj₁ ∎
      where
      open SR word-setoid₁


    hcmw-cong'2 : ∀ c w v -> w ≈₁ v -> hcmw' c w .proj₂ ≡ hcmw' c v .proj₂
    hcmw-cong'2 c w v eq = 
      begin
      hcmw' c w .proj₂ ≡⟨ Eq.sym ( Eq.cong proj₂ (lemma-h**=hcmw' c w)) ⟩
      (h **) ( c) [ w ]ₓ .proj₂ ≡⟨ proj₂ (h-wd ( c) (f-wd eq)) ⟩
      (h **) ( c) [ v ]ₓ .proj₂ ≡⟨ Eq.cong proj₂ (lemma-h**=hcmw' c v) ⟩
      hcmw' c v .proj₂ ∎
      where
      open Eq.≡-Reasoning


    h-wd-m : ∀ (c : C){u t : Word M} -> u ≈₁ t ->
      let (w' , c') = hcmw c u in
      let (w'' , c'') = hcmw c t in
      (w' , inj₁ c') ~ (w'' , inj₁ c'')
    h-wd-m c {u} {t} eqax =
      let (w' , c') = hcmw c u in
      let (w'' , c'') = hcmw c t in
      begin
      (w' , inj₁ c') ≡⟨ Eq.sym (lemma-h**=hcmw c u) ⟩
      ((h **) (inj₁ c) [ u ]ₓ) ≈⟨ h-wd (inj₁ c) (f-wd ( eqax)) ⟩
      ((h **) (inj₁ c) [ t ]ₓ) ≡⟨ (lemma-h**=hcmw c t) ⟩ 
      (w'' , inj₁ c'') ∎
      where open SR s1ct




record CosetNF-CT-Assumptions-And-Theorems-Packed
  {M A : Set}
  (P₁ : WRel M)
  (P₂ : WRel A) : Set₁
  where

  open PB P₁ renaming (_===_ to _===₁_ ; _≈_ to _≈₁_) using ()
  open PP P₁ renaming (•-ε-monoid to m₁ ; word-setoid to word-setoid₁) using ()
  open PB P₂ renaming (_===_ to _===₂_ ; _≈_ to _≈₂_) using ()
  open PP P₂ renaming (•-ε-monoid to m₂ ; word-setoid to word-setoid₂) using ()

  open _≈₂_

  field
    C : Set
    f : M -> Word A
    h : C ⊎ ⊤ -> A -> Word M × (C ⊎ ⊤)
    [_]ₒ : C -> Word A
  
  infix 4 _~_
  _~_ = PW.Pointwise _≈₁_ (_≡_ {A = C ⊎ ⊤})
  
  s1ct : Setoid _ _
  s1ct = PW.×-setoid word-setoid₁ (Eq.setoid (C ⊎ ⊤))

  [_]ₓ = f *
  
  I : C ⊎ ⊤
  I = inj₂ tt
  
  [_] : C ⊎ ⊤ -> Word A
  [_] = [_,_] [_]ₒ (λ v → ε)

  field
    --inv-f'-gen : ∀ x c -> inv-f' (f' x c) ~ x c 
    hcme : ∀ c m -> ∃ \ w -> ∃ \ c' -> ((h **) (inj₁ c) (f m)) ≡ (w , inj₁ c')
    htme : ∀ m -> ((h **) (inj₂ tt) (f m)) ≡ ([ m ]ʷ , inj₂ tt)
    

  field
    htme~ : ∀ (m : M) -> ([ m ]ʷ , I) ~ ((h **) I (f m))
    hcme~ : ∀ (c : C) (m : M) -> let (w' , c' , p) = hcme c m in [ c ]ₒ • f m ≈₂ [ w' ]ₓ • [ c' ]ₒ 
    h-wd-ax : ∀ (c : C ⊎ ⊤){u t : Word A} -> u ===₂ t -> ((h **) c u) ~ ((h **) c t)
    f-wd-ax : ∀ {w v} -> w ===₁ v -> (f *) w ≈₂ (f *) v
    -- inv-h-gen : ∀ c b -> inv-h (h c b) ≈₂ c b. 
    h=ract :  ∀ c y -> let (m' , c') = h c y in
     [ c ] • [ y ]ʷ ≈₂ [ m' ]ₓ • [ c' ]


  module myData2 = Data-CT P₁ P₂ C f h [_]ₒ
  open myData2.Assumptions-And-Theorems hcme htme htme~ hcme~ h-wd-ax f-wd-ax h=ract public
