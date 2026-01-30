{-# OPTIONS  --safe #-}
open import Level using (0ℓ)

open import Relation.Binary.PropositionalEquality as Eq renaming ([_] to [_]') using ( _≡_ ; inspect)
open import Relation.Binary using (IsEquivalence ; Setoid ; Rel)
open import Data.Product.Relation.Binary.Pointwise.NonDependent as PW
open import Function.Definitions using (Injective ; Surjective)
open import Data.Product using (_,_ ; _×_ ; proj₁ ; proj₂)

import Relation.Binary.Reasoning.Setoid as SR


open import Word.Base
open import Word.Properties
import Presentation.Base as PB
import Presentation.Properties as PP

module Presentation.Reidemeister-Schreier where

module Star-Congruence {A B : Set} (Γ : WRel A) (Δ : WRel B) where

  open PB Γ renaming (_===_ to _===₁_ ; _≈_ to _≈₁_)
  open PP Γ renaming (•-ε-monoid to m₁)
  open PB Δ renaming (_===_ to _===₂_ ; _≈_ to _≈₂_)
  open PP Δ renaming (•-ε-monoid to m₂)

  module _
    (f : A -> Word B)
    (f-well-defined  : ∀ {w v} -> w ===₁ v -> (f *) w ≈₂ (f *) v)
    where

    lemma-f*-cong : ∀ {w v : Word A} -> w ≈₁ v -> (f *) w ≈₂ (f *) v
    lemma-f*-cong {w} {v} _≈₁_.refl = _≈₂_.refl
    lemma-f*-cong {w} {v} (sym h) = _≈₂_.sym (lemma-f*-cong h)
    lemma-f*-cong {w} {v} (trans h h₁) = _≈₂_.trans (lemma-f*-cong h) (lemma-f*-cong h₁)
    lemma-f*-cong {w} {v} (cong h h₁) = _≈₂_.cong (lemma-f*-cong h) (lemma-f*-cong h₁)
    lemma-f*-cong {w} {v} assoc = _≈₂_.assoc
    lemma-f*-cong {w} {v} left-unit = _≈₂_.left-unit
    lemma-f*-cong {w} {v} right-unit = _≈₂_.right-unit
    lemma-f*-cong {w} {v} (axiom a) = f-well-defined a


module Star-Injective-Simplified {X Y : Set} (Γ : WRel X) (Δ : WRel Y) where

  open PB Γ renaming (_===_ to _===₁_ ; _≈_ to _≈₁_)
  open PP Γ renaming (•-ε-monoid to m₁ ; word-setoid to word-setoid₁)
  open PB Δ renaming (_===_ to _===₂_ ; _≈_ to _≈₂_)
  open PP Δ renaming (•-ε-monoid to m₂ ; word-setoid to word-setoid₂)

  module Reidemeister-Schreier-Simplified
    (f : X -> Word Y)
    (g : Y -> Word X)
    (well-defined : ∀ {u t : Word Y} -> u ===₂ t -> (g *) u ≈₁ (g *) t)
    (left-inv-gen : ∀ (x : X) -> [ x ]ʷ ≈₁ (g *) (f x))
    where

    left-inv : ∀ (w : Word X) -> w ≈₁ (g *) ((f *) w)
    left-inv ([ x ]ʷ) = left-inv-gen x
    left-inv ε = _≈₁_.refl
    left-inv (w • v) = _≈₁_.cong (left-inv w) (left-inv v)

    lemma-b : ∀ {u t : Word Y} -> u ≈₂ t -> (g *) u ≈₁ (g *) t
    lemma-b = isStar-Congruence.lemma-f*-cong g well-defined
      where
      module isStar-Congruence = Star-Congruence Δ Γ

    g*-surj : Surjective _≈₂_ _≈₁_ (g *)
    g*-surj y = (f *) y , λ x → _≈₁_.trans (lemma-b x) (_≈₁_.sym (left-inv y))

    reidemeister-schreier-simplified : (w v : Word X) -> (f *) w ≈₂ (f *) v -> w ≈₁ v
    reidemeister-schreier-simplified w v hyp = begin
      w      ≈⟨ left-inv w ⟩
      (g *) ((f *) w)      ≈⟨ lemma-b hyp ⟩
      (g *) ((f *) v)      ≈⟨ _≈₁_.sym (left-inv v) ⟩
      v         ∎
      where
        open import Relation.Binary.Reasoning.Setoid word-setoid₁

    f*-inj : Injective _≈₁_ _≈₂_ (f *)
    f*-inj = λ x₁ → reidemeister-schreier-simplified _ _ x₁


module Star-Injective-Full
  {X Y : Set}
  (Γ : WRel X)
  (Δ : WRel Y)
  (C : Set)
  (I : C)
  where

  open PB Γ renaming (_===_ to _===₁_ ; _≈_ to _≈₁_)
  open PP Γ renaming (•-ε-monoid to m₁ ; word-setoid to word-setoid₁)
  open PB Δ renaming (_===_ to _===₂_ ; _≈_ to _≈₂_)
  open PP Δ renaming (•-ε-monoid to m₂ ; word-setoid to word-setoid₂)

  open _≈₂_

  infix 4 _~_
  _~_ = PW.Pointwise _≈₁_ (_≡_ {A = C})

  module _
    (f : X -> Word Y)
    (h : C -> Y -> Word X × C)
    where
    
    nf = (h **) I
    
    module Reidemeister-Schreier-Full
      (h=⁻¹f-gen : ∀ (x : X) -> ([ x ]ʷ , I) ~ ((h **) I (f x)))
      (h-wd : ∀ (c : C){u t : Word Y} -> u ===₂ t -> ((h **) c u) ~ ((h **) c t))
      where

      -- Definition: A word is special if it doesn't leave the "I"-coset.
      special : Word Y -> Set
      special w = proj₂ ((h **) I w) ≡ I

      -- Lemma: ε is special.
      lemma-special-ε : special ε
      lemma-special-ε = Eq.refl

      -- Lemma: The image of f is special.
      lemma-special-f : ∀ (x : X) -> special (f x)
      lemma-special-f x with h=⁻¹f-gen x
      ... | hyp = Eq.sym (proj₂ hyp)

      -- Lemma: Special words are closed under multiplication.
      lemma-special-• : ∀ (w v : Word Y) -> special w -> special v -> special (w • v)
      lemma-special-• w v sw sv with (h **) I w | inspect ((h **) I ) w
      ... | (w' , c') | [ Eq.refl ]' with (h **) c' v | inspect ((h **) c' ) v
      ... | (v' , c'') | [ Eq.refl ]' = lem3
        where
          open Eq.≡-Reasoning

          lem1 : c' ≡ I
          lem1 = sw

          lem2 : (v' , c'') ≡ (h **) I v
          lem2 = begin
            (v' , c'') ≡⟨ Eq.refl ⟩
            (h **) c' v ≡⟨ Eq.cong (\ x -> (h **) x v) lem1 ⟩
            (h **) I v ∎

          lem3 : c'' ≡ I
          lem3 = begin
            c'' ≡⟨ Eq.cong proj₂ lem2 ⟩
            proj₂ ((h **) I v) ≡⟨ sv ⟩
            I ∎

      -- Lemma: The image of (f *) is special.
      lemma-special-f* : ∀ (w : Word X) -> special ((f *) w)
      lemma-special-f* [ x ]ʷ = lemma-special-f x
      lemma-special-f* ε = lemma-special-ε
      lemma-special-f* (w • v) = lemma-special-• ((f *) w) ((f *) v) (lemma-special-f* w) (lemma-special-f* v)

      -- Definition: For special words, there is a translation back.
      g : Word Y -> Word X
      g w = proj₁ ((h **) I w)

      -- Lemma: g preserves ε.
      lemma-g-ε : g ε ≡ ε
      lemma-g-ε = Eq.refl

      -- Lemma: g is a homomorphism on special words.
      lemma-g-• : ∀ (w v : Word Y) -> special w -> g (w • v) ≡ g w • g v
      lemma-g-• w v hyp with (h **) I w | inspect ((h **) I) w
      lemma-g-• w v hyp | (w' , c') | [ eq1 ]' with (h **) c' v | inspect ((h **) c') v
      lemma-g-• w v hyp | (w' , c') | [ eq1 ]' | (v' , c'') | [ eq2 ]' = lem6
        where
          open Eq.≡-Reasoning
          lem1 : c' ≡ I
          lem1 = hyp

          lem2 : (v' , c'') ≡ (h **) I v
          lem2 = begin
            (v' , c'') ≡⟨ Eq.sym eq2 ⟩
            (h **) c' v ≡⟨ Eq.cong (λ □ → (h **) □ v) lem1 ⟩
            (h **) I v ∎

          lem4 : v' ≡ g v
          lem4 = Eq.cong proj₁ lem2 

          lem6 : w' • v' ≡ w' • g v
          lem6 = Eq.cong (λ □ → w' • □) lem4


      -- Lemma: g is a left inverse of f *.
      lemma-a : ∀ (w : Word X) -> w ≈₁ g ((f *) w)
      lemma-a [ x ]ʷ = proj₁ (h=⁻¹f-gen x)
      lemma-a ε = _≈₁_.refl
      lemma-a (w • u) = claim
        where
          open import Relation.Binary.Reasoning.Setoid word-setoid₁
          claim :  w • u ≈₁ g ((f *) (w • u))
          claim = begin
            w • u ≈⟨ _≈₁_.cong (lemma-a w) _≈₁_.refl  ⟩
            g ((f *) w) • u ≈⟨ _≈₁_.cong _≈₁_.refl (lemma-a u) ⟩
            g ((f *) w) • g ((f *) u) ≡⟨ Eq.sym ((lemma-g-• ((f *) w) ((f *) u) (lemma-special-f* w))) ⟩
            g ((f *) w • (f *) u) ∎


      -- Lemma: Hypothesis B can be extended from the elements of Δ to
      -- all consequences of Δ.
      lemma-hypB : ∀ (c : C) (u t : Word Y) -> u ≈₂ t -> (h **) c u ~ (h **) c t
      lemma-hypB c u t (axiom x) = h-wd c x
      lemma-hypB c u .u refl = _≈₁_.refl , Eq.refl
      lemma-hypB c ((u • v) • w) (.u • (.v • .w)) assoc with (h **) c u
      ... | (u' , c') with (h **) c' v
      ... | (v' , c'') with (h **) c'' w
      ... | (w' , c''') = (_≈₁_.assoc , Eq.refl)
      lemma-hypB c (ε • u) .u left-unit with (h **) c u
      ... | (u' , c') = (_≈₁_.left-unit , Eq.refl)
      lemma-hypB c (u • ε) .u right-unit with (h **) c u
      ... | (u' , c') = (_≈₁_.right-unit , Eq.refl)

      lemma-hypB c u t (sym hyp) = (_≈₁_.sym (lemma-hypB c t u hyp .proj₁)) , Eq.sym (lemma-hypB c t u hyp .proj₂)
      lemma-hypB c u t (trans {v = v} hyp1 hyp2) = _≈₁_.trans (lemma-hypB c u v hyp1 .proj₁) (lemma-hypB c v t hyp2 .proj₁) , Eq.trans (lemma-hypB c u v hyp1 .proj₂) (lemma-hypB c v t hyp2 .proj₂)
      lemma-hypB c (u • u') (t • t') (cong hyp1 hyp2)
        with (h **) c u | (h **) c t | lemma-hypB c u t hyp1
      ... | (u'' , c') | (t'' , c'') | (ih1 , ih1')
        rewrite ih1'
        with (h **) c'' u' | (h **) c'' t' | lemma-hypB c'' u' t' hyp2
      ... | (u''' , c''') | (t''' , c'''') | (ih2 , ih2') = (_≈₁_.cong ih1 ih2 , ih2')

      -- Lemma: g preserves relations.
      lemma-b : ∀ (u t : Word Y) -> u ≈₂ t -> g u ≈₁ g t
      lemma-b u t hyp with (h **) I u | (h **) I t | lemma-hypB I u t hyp
      ... | (u' , c') | (t' , c'') | (ih , ih') = ih

      -- Reidemeister-Schreier Theorem.
      reidemeister-schreier : (w v : Word X) -> (f *) w ≈₂ (f *) v -> w ≈₁ v
      reidemeister-schreier w v hyp =
        begin
          w ≈⟨ lemma-a w ⟩
          g ((f *) w) ≈⟨ lemma-b ((f *) w) ((f *) v) hyp ⟩
          g ((f *) v) ≈⟨ _≈₁_.sym (lemma-a v) ⟩
          v ∎
          where
            open import Relation.Binary.Reasoning.Setoid word-setoid₁

      f*-inj : Injective _≈₁_ _≈₂_ (f *)
      f*-inj = λ x₁ → reidemeister-schreier _ _ x₁



    module RightAction
      (f-well-defined : ∀ {w v} -> w ===₁ v -> (f *) w ≈₂ (f *) v)
      ([_] : C -> Word Y)
      ([I]≈ε : [ I ] ≈₂ ε)
      (lemma-ract : ∀ c b -> let (b' , c') = h c b in let [_]ₓ = f * in
        [ c ] • [ b ]ʷ ≈₂ [ b' ]ₓ • [ c' ])
      where

      ract = h
      
      [_]ₓ : Word X -> Word Y
      [_]ₓ = f *

      []ₓ-wd : ∀ {w v} -> w ≈₁ v -> [ w ]ₓ ≈₂ [ v ]ₓ
      []ₓ-wd {w} {v} eqv = Star-Congruence.lemma-f*-cong Γ Δ f f-well-defined eqv
  
      infixl 4 _⊛_
      _⊛_ : C -> Word Y -> Word X × C
      _⊛_ = ract **

      lemma-⊛ : ∀ c w -> let (w' , c') = c ⊛ w in [ c ] • w ≈₂ [ w' ]ₓ • [ c' ]
      lemma-⊛ c [ x ]ʷ = lemma-ract c x
      lemma-⊛ c ε = _≈₂_.trans _≈₂_.right-unit (_≈₂_.sym _≈₂_.left-unit)
      lemma-⊛ c (w • v) with c ⊛ w | inspect (c ⊛_) w
      ... | (w' , c') | [ Eq.refl ]' with c' ⊛ v | inspect (c' ⊛_) v
      ... | (v' , c'') | [ Eq.refl ]' = claim
        where
        claim : [ c ] • (w • v) ≈₂ [ w' • v' ]ₓ • [ c'' ]
        claim = begin
          [ c ] • (w • v) ≈⟨ _≈₂_.sym _≈₂_.assoc ⟩
          ([ c ] • w) • v ≈⟨ _≈₂_.cong (lemma-⊛ _ _) _≈₂_.refl ⟩
          ([ w' ]ₓ • [ c' ]) • v ≈⟨ _≈₂_.assoc ⟩
          [ w' ]ₓ • [ c' ] • v ≈⟨ _≈₂_.cong _≈₂_.refl (lemma-⊛ _ _) ⟩
          [ w' ]ₓ • [ v' ]ₓ • [ c'' ] ≈⟨ _≈₂_.sym _≈₂_.assoc ⟩
          [ w' • v' ]ₓ • [ c'' ] ∎
          where
            open import Relation.Binary.Reasoning.Setoid word-setoid₂

      ⁻¹nf : Word X × C -> Word Y
      ⁻¹nf (a , c) = [ a ]ₓ • [ c ]

      ⁻¹nf-nf=id : ∀ {w} -> ⁻¹nf (nf w) ≈₂ w
      ⁻¹nf-nf=id {w} = _≈₂_.trans (_≈₂_.sym (lemma-⊛ _ _)) (_≈₂_.trans (_≈₂_.cong [I]≈ε _≈₂_.refl) _≈₂_.left-unit)

      nf-isInjective : Injective _≈₂_ (PW.Pointwise _≈₁_ _≡_) nf
      nf-isInjective {x} {y} (eqa , eqc) with nf x | inspect nf x | nf y | inspect nf y
      ... | (a , c) | [ Eq.refl ]' | (a' , c') | [ Eq.refl ]' = begin
        x ≈⟨ _≈₂_.sym ⁻¹nf-nf=id ⟩
        ⁻¹nf (nf x) ≈⟨ _≈₂_.refl ⟩
        [ a ]ₓ • [ c ] ≡⟨ Eq.cong (\ □ -> [ a ]ₓ • [ □ ]) eqc ⟩
        [ a ]ₓ • [ c' ] ≈⟨ _≈₂_.cong (lemma-f*-cong f f-well-defined eqa) _≈₂_.refl ⟩
        [ a' ]ₓ • [ c' ] ≡⟨ Eq.refl ⟩
        ⁻¹nf (nf y) ≈⟨ ⁻¹nf-nf=id ⟩
        y ∎
          where
            open import Relation.Binary.Reasoning.Setoid word-setoid₂
            open Star-Congruence Γ Δ

      ⁻¹nf-wd : ∀ {u t : Word X × C} -> u ~ t -> ⁻¹nf u ≈₂ ⁻¹nf t
      ⁻¹nf-wd {u} {t} (_≈₁_.refl , Eq.refl) = _≈₂_.refl
      ⁻¹nf-wd {u} {t} (_≈₁_.sym fst , Eq.refl) = _≈₂_.cong ([]ₓ-wd (_≈₁_.sym fst)) _≈₂_.refl
      ⁻¹nf-wd {u} {t} (_≈₁_.trans fst fst₁ , Eq.refl) = _≈₂_.cong ([]ₓ-wd (_≈₁_.trans fst fst₁)) _≈₂_.refl
      ⁻¹nf-wd {u} {t} (_≈₁_.cong fst fst₁ , Eq.refl) = _≈₂_.cong ([]ₓ-wd (_≈₁_.cong fst fst₁)) _≈₂_.refl
      ⁻¹nf-wd {u} {t} (_≈₁_.assoc , Eq.refl) = _≈₂_.cong _≈₂_.assoc _≈₂_.refl
      ⁻¹nf-wd {u} {t} (_≈₁_.left-unit , Eq.refl) = _≈₂_.trans _≈₂_.assoc _≈₂_.left-unit
      ⁻¹nf-wd {u} {t} (_≈₁_.right-unit , Eq.refl) = _≈₂_.cong _≈₂_.right-unit _≈₂_.refl
      ⁻¹nf-wd {u} {t} (_≈₁_.axiom x , Eq.refl) = _≈₂_.cong ([]ₓ-wd (_≈₁_.axiom x)) _≈₂_.refl

      ⁻¹nf-isSurjective : Surjective _~_ _≈₂_ ⁻¹nf
      ⁻¹nf-isSurjective y = nf y , claim
        where
          claim : {z : Word X × C} → z ~ nf y → ⁻¹nf z ≈₂ y
          claim {z} eqv = _≈₂_.trans (⁻¹nf-wd eqv) ⁻¹nf-nf=id
      


    module LeftAction
      (f-well-defined : ∀ {w v} -> w ===₁ v -> (f *) w ≈₂ (f *) v)
      ([_] : C -> Word Y)
      ([I]≈ε : [ I ] ≈₂ ε)
      (lact : Y -> C -> C × Word X)
      (lemma-lact : ∀ b c -> let (c' , b') = lact b c in let [_]ₓ = f * in
          [ b ]ʷ • [ c ] ≈₂ [ c' ] • [ b' ]ₓ)
      where

      [_]ₓ = f *


      infixl 4 _⊛_
      _⊛_ : Word Y -> C -> C × Word X
      _⊛_ = lact **'

      lemma-⊛ : ∀ w c -> let (c' , w') = w ⊛ c in w • [ c ] ≈₂ [ c' ] • [ w' ]ₓ
      lemma-⊛ [ x ]ʷ c = lemma-lact x c
      lemma-⊛ ε c = _≈₂_.trans _≈₂_.left-unit (_≈₂_.sym _≈₂_.right-unit)
      lemma-⊛ (w • v) c with v ⊛ c | inspect (v ⊛_) c
      ... | (c' , v') | [ Eq.refl ]' with w ⊛ c' | inspect (w ⊛_) c'
      ... | (c'' , w') | [ Eq.refl ]' = claim
        where
        claim : (w • v) • [ c ] ≈₂ [ c'' ] • [ w' • v' ]ₓ
        claim = begin
          (w • v) • [ c ] ≈⟨ _≈₂_.assoc ⟩
          w • v • [ c ] ≈⟨ _≈₂_.cong _≈₂_.refl (lemma-⊛ v c) ⟩
          w • [ c' ] • [ v' ]ₓ ≈⟨ _≈₂_.sym _≈₂_.assoc ⟩
          (w • [ c' ]) • [ v' ]ₓ ≈⟨ _≈₂_.cong (lemma-⊛ w c') _≈₂_.refl ⟩
          ([ c'' ] • [ w' ]ₓ) • [ v' ]ₓ ≈⟨ _≈₂_.assoc ⟩
          [ c'' ] • [ w' • v' ]ₓ ∎
          where
            open import Relation.Binary.Reasoning.Setoid word-setoid₂


      nfl : Word Y -> C × Word X
      nfl = _⊛ I

      ⁻¹nfl : C × Word X -> Word Y
      ⁻¹nfl (c , a) = [ c ] • [ a ]ₓ

      ⁻¹nfl-nfl=id : ∀ {w} -> ⁻¹nfl (nfl w) ≈₂ w
      ⁻¹nfl-nfl=id {w} = _≈₂_.trans (_≈₂_.sym (lemma-⊛ _ _) ) (_≈₂_.trans (_≈₂_.cong _≈₂_.refl [I]≈ε) _≈₂_.right-unit)

      nfl-isInjective : Injective _≈₂_ (PW.Pointwise _≡_ _≈₁_) nfl
      nfl-isInjective {x} {y} (eqc , eqa) with nfl x | inspect nfl x | nfl y | inspect nfl y
      ... | (c , a) | [ Eq.refl ]' | (c' , a') | [ Eq.refl ]' = begin
        x ≈⟨ _≈₂_.sym ⁻¹nfl-nfl=id ⟩
        ⁻¹nfl (nfl x) ≈⟨ _≈₂_.refl ⟩
        [ c ] • [ a ]ₓ ≡⟨ Eq.cong (\ □ -> [ □ ] • [ a ]ₓ) eqc ⟩
        [ c' ] • [ a ]ₓ ≈⟨ _≈₂_.cong _≈₂_.refl (lemma-f*-cong f f-well-defined eqa) ⟩
        [ c' ] • [ a' ]ₓ ≡⟨ Eq.refl ⟩
        ⁻¹nfl (nfl y) ≈⟨ ⁻¹nfl-nfl=id ⟩
        y ∎
          where
            open import Relation.Binary.Reasoning.Setoid word-setoid₂
            open Star-Congruence Γ Δ



module Star-Injective-Full-Setoid
  {X Y : Set}
  (Γ : WRel X)
  (Δ : WRel Y)
  (Cₛ : Setoid 0ℓ 0ℓ)
  (I : Setoid.Carrier Cₛ)
  where


  open PB Γ renaming (_===_ to _===₁_ ; _≈_ to _≈₁_)
  open PP Γ renaming (•-ε-monoid to m₁ ; word-setoid to word-setoid₁)
  open PB Δ renaming (_===_ to _===₂_ ; _≈_ to _≈₂_)
  open PP Δ renaming (•-ε-monoid to m₂ ; word-setoid to word-setoid₂)

  open Setoid Cₛ renaming (Carrier to C ; isEquivalence to isEquivalenceₛ ; _≈_ to _≈ₛ_) using () public
  open IsEquivalence isEquivalenceₛ renaming (refl to reflₛ ; sym to symₛ ; trans to transₛ) using () public
  
  open _≈₂_

  setoid-WX-Cₛ : Setoid 0ℓ 0ℓ
  setoid-WX-Cₛ = PW.×-setoid word-setoid₁ Cₛ

  open Setoid setoid-WX-Cₛ renaming (refl to refl~ ; sym to sym~ ; trans to trans~ ; _≈_ to _~_) using () public

  module _
    (f : X -> Word Y)
    (h : C -> Y -> Word X × C)
    (h-congₛ-gen : ∀ {c d} y -> c ≈ₛ d -> h c y ~ h d y)
    where

    -- h ** is congruent over C w.r.t a word in Y.
    h-congₛ : ∀ {c d w} -> c ≈ₛ d -> (h **) c w ~ (h **) d w
    h-congₛ {c} {d} {[ x ]ʷ} eq = h-congₛ-gen x eq
    h-congₛ {c} {d} {ε} eq = _≈₁_.refl , eq
    h-congₛ {c} {d} {(w • v)} eq with (h **) c w | inspect ((h **) c) w | (h **) d w | inspect ((h **) d) w
    ... | (wc , c') | [ Eq.refl ]' | (wd , d') | [ Eq.refl ]' with h-congₛ {c} {d} {w} eq | (h **) c' v | inspect ((h **) c') v | (h **) d' v | inspect ((h **) d') v
    ... | ih1 | (vc , c'') | [ Eq.refl ]' | (vd , d'') | [ Eq.refl ]' with h-congₛ {c'} {d'} {v} (ih1 .proj₂)
    ... | ih2 = (_≈₁_.cong (ih1 .proj₁) (ih2 .proj₁)) , ih2 .proj₂


    nf : Word Y -> Word X × C
    nf = (h **) I

    module Reidemeister-Schreier-Full
      (h=⁻¹f-gen : ∀ (x : X) -> ([ x ]ʷ , I) ~ ((h **) I (f x)))
      (h-wd : ∀ (c : C){u t : Word Y} -> u ===₂ t -> ((h **) c u) ~ ((h **) c t))
      where

      -- Definition: A word is special if it doesn't leave the "I"-coset.
      special : Word Y -> Set
      special w = proj₂ ((h **) I w) ≈ₛ I

      -- Lemma: ε is special.
      lemma-special-ε : special ε
      lemma-special-ε = reflₛ

      -- Lemma: The image of f is special.
      lemma-special-f : ∀ (x : X) -> special (f x)
      lemma-special-f x with h=⁻¹f-gen x
      ... | hyp = symₛ (proj₂ hyp)

      -- Lemma: Special words are closed under multiplication.
      lemma-special-• : ∀ (w v : Word Y) -> special w -> special v -> special (w • v)
      lemma-special-• w v sw sv with (h **) I w | inspect ((h **) I ) w
      ... | (w' , c') | [ Eq.refl ]' with (h **) c' v | inspect ((h **) c' ) v
      ... | (v' , c'') | [ Eq.refl ]' = lem3
        where

          lem1 : c' ≈ₛ I
          lem1 = sw

          lem2 : (v' , c'') ~ (h **) I v
          lem2 = begin
            (v' , c'') ≡⟨ Eq.refl ⟩
            (h **) c' v ≈⟨ h-congₛ {w = v} sw ⟩
            (h **) I v ∎
            where open SR setoid-WX-Cₛ

          lem3 : c'' ≈ₛ I
          lem3 = begin
            c'' ≈⟨ proj₂ lem2 ⟩
            proj₂ ((h **) I v) ≈⟨ sv ⟩
            I ∎
            where open SR Cₛ          

      -- Lemma: The image of (f *) is special.
      lemma-special-f* : ∀ (w : Word X) -> special ((f *) w)
      lemma-special-f* [ x ]ʷ = lemma-special-f x
      lemma-special-f* ε = lemma-special-ε
      lemma-special-f* (w • v) = lemma-special-• ((f *) w) ((f *) v) (lemma-special-f* w) (lemma-special-f* v)

      -- Definition: For special words, there is a translation back.
      g : Word Y -> Word X
      g w = proj₁ ((h **) I w)

      -- Lemma: g preserves ε.
      lemma-g-ε : g ε ≡ ε
      lemma-g-ε = Eq.refl

      -- Lemma: g is a homomorphism on special words.
      lemma-g-• : ∀ (w v : Word Y) -> special w -> g (w • v) ≈₁ g w • g v
      lemma-g-• w v hyp with (h **) I w | inspect ((h **) I) w
      lemma-g-• w v hyp | (w' , c') | [ eq1 ]' with (h **) c' v | inspect ((h **) c') v
      lemma-g-• w v hyp | (w' , c') | [ eq1 ]' | (v' , c'') | [ eq2 ]' = lem6
        where

          lem1 : c' ≈ₛ I
          lem1 = hyp

          lem2 : (v' , c'') ~ (h **) I v
          lem2 = begin
            (v' , c'') ≡⟨ Eq.sym eq2 ⟩
            (h **) c' v ≈⟨ h-congₛ {w = v} lem1 ⟩
            (h **) I v ∎
            where open SR setoid-WX-Cₛ

          lem4 : v' ≈₁ g v
          lem4 = proj₁ lem2 

          lem6 : w' • v' ≈₁ w' • g v
          lem6 = _≈₁_.cong _≈₁_.refl lem4


      -- Lemma: g is a left inverse of f *.
      lemma-a : ∀ (w : Word X) -> w ≈₁ g ((f *) w)
      lemma-a [ x ]ʷ = proj₁ (h=⁻¹f-gen x)
      lemma-a ε = _≈₁_.refl
      lemma-a (w • u) = claim
        where
          open import Relation.Binary.Reasoning.Setoid word-setoid₁
          claim :  w • u ≈₁ g ((f *) (w • u))
          claim = begin
            w • u ≈⟨ _≈₁_.cong (lemma-a w) _≈₁_.refl  ⟩
            g ((f *) w) • u ≈⟨ _≈₁_.cong _≈₁_.refl (lemma-a u) ⟩
            g ((f *) w) • g ((f *) u) ≈⟨ _≈₁_.sym ((lemma-g-• ((f *) w) ((f *) u) (lemma-special-f* w))) ⟩
            g ((f *) w • (f *) u) ∎


      -- Lemma: Hypothesis B can be extended from the elements of Δ to
      -- all consequences of Δ.
      lemma-hypB : ∀ (c : C) (u t : Word Y) -> u ≈₂ t -> (h **) c u ~ (h **) c t
      lemma-hypB c u t (axiom x) = h-wd c x
      lemma-hypB c u .u refl = _≈₁_.refl , reflₛ
      lemma-hypB c ((u • v) • w) (.u • (.v • .w)) assoc with (h **) c u
      ... | (u' , c') with (h **) c' v
      ... | (v' , c'') with (h **) c'' w
      ... | (w' , c''') = (_≈₁_.assoc , reflₛ)
      lemma-hypB c (ε • u) .u left-unit with (h **) c u
      ... | (u' , c') = (_≈₁_.left-unit , reflₛ)
      lemma-hypB c (u • ε) .u right-unit with (h **) c u
      ... | (u' , c') = (_≈₁_.right-unit , reflₛ)

      lemma-hypB c u t (sym hyp) = (_≈₁_.sym (lemma-hypB c t u hyp .proj₁)) , symₛ (lemma-hypB c t u hyp .proj₂)
      lemma-hypB c u t (trans {v = v} hyp1 hyp2) = _≈₁_.trans (lemma-hypB c u v hyp1 .proj₁) (lemma-hypB c v t hyp2 .proj₁) , transₛ (lemma-hypB c u v hyp1 .proj₂) (lemma-hypB c v t hyp2 .proj₂)
      lemma-hypB c (u • u') (t • t') (cong hyp1 hyp2)
        with (h **) c u | (h **) c t | inspect ((h **) c) u | inspect ((h **) c) t | lemma-hypB c u t hyp1
      ... | (u'' , c') | (t'' , c'') | [ Eq.refl ]' | [ Eq.refl ]' | (ih1 , ih1')
        with (h **) c'' u' | (h **) c'' t' | inspect ((h **) c'') u' | inspect ((h **) c'') t' | lemma-hypB c'' u' t' hyp2
      ... | (u''' , c''') | (t''' , c'''') | [ Eq.refl ]' | [ Eq.refl ]' | (ih2 , ih2') = (_≈₁_.cong ih1 (proj₁ claim)) , proj₂ claim
        where
        open SR setoid-WX-Cₛ
        claim : (h **) ((h **) c u .proj₂) u' ~ (h **) ((h **) c t .proj₂) t'
        claim = begin
          (h **) ((h **) c u .proj₂) u' ≈⟨ lemma-hypB (((h **) c u .proj₂)) u' t' hyp2 ⟩
          (h **) ((h **) c u .proj₂) t' ≈⟨ h-congₛ {w = t'} ih1' ⟩
          (h **) ((h **) c t .proj₂) t' ∎

      -- Lemma: g preserves relations.
      lemma-b : ∀ (u t : Word Y) -> u ≈₂ t -> g u ≈₁ g t
      lemma-b u t hyp with (h **) I u | (h **) I t | lemma-hypB I u t hyp
      ... | (u' , c') | (t' , c'') | (ih , ih') = ih

      -- Reidemeister-Schreier Theorem.
      reidemeister-schreier : (w v : Word X) -> (f *) w ≈₂ (f *) v -> w ≈₁ v
      reidemeister-schreier w v hyp =
        begin
          w ≈⟨ lemma-a w ⟩
          g ((f *) w) ≈⟨ lemma-b ((f *) w) ((f *) v) hyp ⟩
          g ((f *) v) ≈⟨ _≈₁_.sym (lemma-a v) ⟩
          v ∎
          where
            open import Relation.Binary.Reasoning.Setoid word-setoid₁

      f*-inj : Injective _≈₁_ _≈₂_ (f *)
      f*-inj = λ x₁ → reidemeister-schreier _ _ x₁

    module RightAction
      (f-well-defined : ∀ {w v} -> w ===₁ v -> (f *) w ≈₂ (f *) v)
      ([_] : C -> Word Y)
      ([]-cong : ∀ {c d} -> c ≈ₛ d -> [ c ] ≈₂ [ d ])
      ([I]≈ε : [ I ] ≈₂ ε)
      (lemma-ract : ∀ c b -> let (b' , c') = h c b in let [_]ₓ = f * in
        [ c ] • [ b ]ʷ ≈₂ [ b' ]ₓ • [ c' ])
      where

      [_]ₓ : Word X -> Word Y
      [_]ₓ = f *

      infixl 4 _⊛_
      _⊛_ : C -> Word Y -> Word X × C
      _⊛_ = h **

      lemma-⊛ : ∀ c w -> let (w' , c') = c ⊛ w in [ c ] • w ≈₂ [ w' ]ₓ • [ c' ]
      lemma-⊛ c [ x ]ʷ = lemma-ract c x
      lemma-⊛ c ε = _≈₂_.trans _≈₂_.right-unit (_≈₂_.sym _≈₂_.left-unit)
      lemma-⊛ c (w • v) with c ⊛ w | inspect (c ⊛_) w
      ... | (w' , c') | [ Eq.refl ]' with c' ⊛ v | inspect (c' ⊛_) v
      ... | (v' , c'') | [ Eq.refl ]' = claim
        where
        claim : [ c ] • (w • v) ≈₂ [ w' • v' ]ₓ • [ c'' ]
        claim = begin
          [ c ] • (w • v) ≈⟨ _≈₂_.sym _≈₂_.assoc ⟩
          ([ c ] • w) • v ≈⟨ _≈₂_.cong (lemma-⊛ _ _) _≈₂_.refl ⟩
          ([ w' ]ₓ • [ c' ]) • v ≈⟨ _≈₂_.assoc ⟩
          [ w' ]ₓ • [ c' ] • v ≈⟨ _≈₂_.cong _≈₂_.refl (lemma-⊛ _ _) ⟩
          [ w' ]ₓ • [ v' ]ₓ • [ c'' ] ≈⟨ _≈₂_.sym _≈₂_.assoc ⟩
          [ w' • v' ]ₓ • [ c'' ] ∎
          where
            open import Relation.Binary.Reasoning.Setoid word-setoid₂

      ⁻¹nf : Word X × C -> Word Y
      ⁻¹nf (a , c) = [ a ]ₓ • [ c ]

      ⁻¹nf-nf=id : ∀ {w} -> ⁻¹nf (nf w) ≈₂ w
      ⁻¹nf-nf=id {w} = _≈₂_.trans (_≈₂_.sym (lemma-⊛ _ _)) (_≈₂_.trans (_≈₂_.cong [I]≈ε _≈₂_.refl) _≈₂_.left-unit)

      nf-isInjective : Injective _≈₂_ (PW.Pointwise _≈₁_ _≡_) nf
      nf-isInjective {x} {y} (eqa , eqc) with nf x | inspect nf x | nf y | inspect nf y
      ... | (a , c) | [ Eq.refl ]' | (a' , c') | [ Eq.refl ]' = begin
        x ≈⟨ _≈₂_.sym ⁻¹nf-nf=id ⟩
        ⁻¹nf (nf x) ≈⟨ _≈₂_.refl ⟩
        [ a ]ₓ • [ c ] ≡⟨ Eq.cong (\ □ -> [ a ]ₓ • [ □ ]) eqc ⟩
        [ a ]ₓ • [ c' ] ≈⟨ _≈₂_.cong (lemma-f*-cong f f-well-defined eqa) _≈₂_.refl ⟩
        [ a' ]ₓ • [ c' ] ≡⟨ Eq.refl ⟩
        ⁻¹nf (nf y) ≈⟨ ⁻¹nf-nf=id ⟩
        y ∎
          where
            open import Relation.Binary.Reasoning.Setoid word-setoid₂
            open Star-Congruence Γ Δ


      nf-isInjective' : Injective _≈₂_ (PW.Pointwise _≈₁_ _≈ₛ_) nf
      nf-isInjective' {x} {y} (eqa , eqc) with nf x | inspect nf x | nf y | inspect nf y
      ... | (a , c) | [ Eq.refl ]' | (a' , c') | [ Eq.refl ]' = begin
        x ≈⟨ _≈₂_.sym ⁻¹nf-nf=id ⟩
        ⁻¹nf (nf x) ≈⟨ _≈₂_.refl ⟩
        [ a ]ₓ • [ c ] ≈⟨ _≈₂_.cong _≈₂_.refl ([]-cong eqc) ⟩
        [ a ]ₓ • [ c' ] ≈⟨ _≈₂_.cong (lemma-f*-cong f f-well-defined eqa) _≈₂_.refl ⟩
        [ a' ]ₓ • [ c' ] ≡⟨ Eq.refl ⟩
        ⁻¹nf (nf y) ≈⟨ ⁻¹nf-nf=id ⟩
        y ∎
          where
            open import Relation.Binary.Reasoning.Setoid word-setoid₂
            open Star-Congruence Γ Δ



    module LeftAction
      (f-well-defined : ∀ {w v} -> w ===₁ v -> (f *) w ≈₂ (f *) v)
      ([_] : C -> Word Y)
      ([]-cong : ∀ {c d} -> c ≈ₛ d -> [ c ] ≈₂ [ d ])
      ([I]≈ε : [ I ] ≈₂ ε)
      (lact : Y -> C -> C × Word X)
      (lemma-lact : ∀ b c -> let (c' , b') = lact b c in let [_]ₓ = f * in
          [ b ]ʷ • [ c ] ≈₂ [ c' ] • [ b' ]ₓ)
      where

      [_]ₓ = f *


      infixl 4 _⊛_
      _⊛_ : Word Y -> C -> C × Word X
      _⊛_ = lact **'

      lemma-⊛ : ∀ w c -> let (c' , w') = w ⊛ c in w • [ c ] ≈₂ [ c' ] • [ w' ]ₓ
      lemma-⊛ [ x ]ʷ c = lemma-lact x c
      lemma-⊛ ε c = _≈₂_.trans _≈₂_.left-unit (_≈₂_.sym _≈₂_.right-unit)
      lemma-⊛ (w • v) c with v ⊛ c | inspect (v ⊛_) c
      ... | (c' , v') | [ Eq.refl ]' with w ⊛ c' | inspect (w ⊛_) c'
      ... | (c'' , w') | [ Eq.refl ]' = claim
        where
        claim : (w • v) • [ c ] ≈₂ [ c'' ] • [ w' • v' ]ₓ
        claim = begin
          (w • v) • [ c ] ≈⟨ _≈₂_.assoc ⟩
          w • v • [ c ] ≈⟨ _≈₂_.cong _≈₂_.refl (lemma-⊛ v c) ⟩
          w • [ c' ] • [ v' ]ₓ ≈⟨ _≈₂_.sym _≈₂_.assoc ⟩
          (w • [ c' ]) • [ v' ]ₓ ≈⟨ _≈₂_.cong (lemma-⊛ w c') _≈₂_.refl ⟩
          ([ c'' ] • [ w' ]ₓ) • [ v' ]ₓ ≈⟨ _≈₂_.assoc ⟩
          [ c'' ] • [ w' • v' ]ₓ ∎
          where
            open import Relation.Binary.Reasoning.Setoid word-setoid₂


      nfl : Word Y -> C × Word X
      nfl = _⊛ I

      ⁻¹nfl : C × Word X -> Word Y
      ⁻¹nfl (c , a) = [ c ] • [ a ]ₓ

      ⁻¹nfl-nfl=id : ∀ {w} -> ⁻¹nfl (nfl w) ≈₂ w
      ⁻¹nfl-nfl=id {w} = _≈₂_.trans (_≈₂_.sym (lemma-⊛ _ _) ) (_≈₂_.trans (_≈₂_.cong _≈₂_.refl [I]≈ε) _≈₂_.right-unit)

      nfl-isInjective : Injective _≈₂_ (PW.Pointwise _≡_ _≈₁_) nfl
      nfl-isInjective {x} {y} (eqc , eqa) with nfl x | inspect nfl x | nfl y | inspect nfl y
      ... | (c , a) | [ Eq.refl ]' | (c' , a') | [ Eq.refl ]' = begin
        x ≈⟨ _≈₂_.sym ⁻¹nfl-nfl=id ⟩
        ⁻¹nfl (nfl x) ≈⟨ _≈₂_.refl ⟩
        [ c ] • [ a ]ₓ ≡⟨ Eq.cong (\ □ -> [ □ ] • [ a ]ₓ) eqc ⟩
        [ c' ] • [ a ]ₓ ≈⟨ _≈₂_.cong _≈₂_.refl (lemma-f*-cong f f-well-defined eqa) ⟩
        [ c' ] • [ a' ]ₓ ≡⟨ Eq.refl ⟩
        ⁻¹nfl (nfl y) ≈⟨ ⁻¹nfl-nfl=id ⟩
        y ∎
          where
            open import Relation.Binary.Reasoning.Setoid word-setoid₂
            open Star-Congruence Γ Δ

      nfl-isInjective' : Injective _≈₂_ (PW.Pointwise _≈ₛ_ _≈₁_) nfl
      nfl-isInjective' {x} {y} (eqc , eqa) with nfl x | inspect nfl x | nfl y | inspect nfl y
      ... | (c , a) | [ Eq.refl ]' | (c' , a') | [ Eq.refl ]' = begin
        x ≈⟨ _≈₂_.sym ⁻¹nfl-nfl=id ⟩
        ⁻¹nfl (nfl x) ≈⟨ _≈₂_.refl ⟩
        [ c ] • [ a ]ₓ ≈⟨ _≈₂_.cong ([]-cong eqc) _≈₂_.refl ⟩
        [ c' ] • [ a ]ₓ ≈⟨ _≈₂_.cong _≈₂_.refl (lemma-f*-cong f f-well-defined eqa) ⟩
        [ c' ] • [ a' ]ₓ ≡⟨ Eq.refl ⟩
        ⁻¹nfl (nfl y) ≈⟨ ⁻¹nfl-nfl=id ⟩
        y ∎
          where
            open import Relation.Binary.Reasoning.Setoid word-setoid₂
            open Star-Congruence Γ Δ

