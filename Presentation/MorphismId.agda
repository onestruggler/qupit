{-# OPTIONS --safe #-}
open import Level using (0ℓ)
open import Relation.Binary using (IsEquivalence ; Setoid ; Rel)
open import Data.Product using (_,_ ; proj₂)
open import Relation.Binary.Morphism.Definitions using (Homomorphic₂)
open import Relation.Binary.PropositionalEquality using (_≡_)
import Relation.Binary.PropositionalEquality as Eq

import Relation.Binary.Reasoning.Setoid as SR

open import Function using (id ; _∘_) 
open import Algebra.Morphism.Structures using (module MonoidMorphisms ; module GroupMorphisms)
open import Function.Definitions using (Injective ; Surjective)
open import Algebra.Bundles using (Monoid ; Group)
open import Algebra.Bundles.Raw using (RawGroup)


open import Word.Base
open import Word.Properties
import Presentation.Base as PB
import Presentation.Properties as PP
open import Presentation.Reidemeister-Schreier hiding (module Star-Congruence)

module Presentation.MorphismId {A : Set} (Γ : WRel A) (Δ : WRel A) where

open PB Γ renaming (_===_ to _===₁_ ; _≈_ to _≈₁_ ; refl to refl₁ ; cong to cong₁ ; sym to sym₁ ; refl' to refl'₁)
open PP Γ renaming (•-ε-monoid to m₁)
open PB Δ renaming (_===_ to _===₂_ ; _≈_ to _≈₂_ ; refl to refl₂ ; cong to cong₂ ; sym to sym₂ ; refl' to refl'₂)
open PP Δ renaming (•-ε-monoid to m₂ ; word-setoid to ws₂)

open PB


lemma-id* : ∀ {B : Set} {w : Word B} -> (([_]ʷ ∘ id) *) w ≡ w
lemma-id* {B} {[ x ]ʷ} = Eq.refl
lemma-id* {B} {ε} = Eq.refl
lemma-id* {B} {w • w₁} = Eq.cong₂ _•_ lemma-id* lemma-id*

f : A -> Word A
f = [_]ʷ ∘ id

g : A -> Word A
g = [_]ʷ ∘ id


module Star-Congruence
  (id-well-defined  : ∀ {w v} -> w ===₁ v -> id w ≈₂ id v)
  where

  lemma-id*-cong : ∀ {w v : Word A} -> w ≈₁ v -> id w ≈₂ id v
  lemma-id*-cong {w} {v} _≈₁_.refl = _≈₂_.refl
  lemma-id*-cong {w} {v} (sym h) = _≈₂_.sym (lemma-id*-cong h)
  lemma-id*-cong {w} {v} (trans h h₁) = _≈₂_.trans (lemma-id*-cong h) (lemma-id*-cong h₁)
  lemma-id*-cong {w} {v} (cong h h₁) = _≈₂_.cong (lemma-id*-cong h) (lemma-id*-cong h₁)
  lemma-id*-cong {w} {v} assoc = _≈₂_.assoc
  lemma-id*-cong {w} {v} left-unit = _≈₂_.left-unit
  lemma-id*-cong {w} {v} right-unit = _≈₂_.right-unit
  lemma-id*-cong {w} {v} (axiom a) = id-well-defined a

open MonoidMorphisms (Monoid.rawMonoid m₁) (Monoid.rawMonoid m₂)

-- Standard library lacks of Epimorphism defintion.
record IsMonoidEpimorphism (f : Word A → Word A) : Set  where
  field
    isMonoidHomomorphism : IsMonoidHomomorphism f
    surjective           : Surjective _≈₁_ _≈₂_ f

  open IsMonoidHomomorphism isMonoidHomomorphism public

-- A way to show id* is a monoid homomorphism.
module StarHomomorphism
  (id-well-defined  : ∀ {w v} -> w ===₁ v -> id w ≈₂ id v)
  where

  isMonoidHomomorphism : IsMonoidHomomorphism id
  isMonoidHomomorphism = record {
    isMagmaHomomorphism = record {
      isRelHomomorphism = record {
        cong = lemma-id*-cong id-well-defined } ;
        homo = λ x y → _≈₂_.refl } ;
    ε-homo = _≈₂_.refl }
    where
      open Star-Congruence

-- A way to show id* is a monomorphism.
module StarMonomorphism
  (f-well-defined  : ∀ {w v} -> w ===₁ v -> id w ≈₂ id v)
  (g-well-defined : ∀ {u t : Word A} -> u ===₂ t -> id u ≈₁ id t)
  where


  g-wd : {u t : Word A} → u ===₂ t → (g *) u ≈₁ (g *) t
  g-wd {u} {t} eq rewrite lemma-id* {w = u} | lemma-id* {w = t} = g-well-defined eq
  

  g-linv : (x : A) → [ x ]ʷ ≈₁ (g *) (f x)
  g-linv x rewrite lemma-id* {w = f x} = _≈₁_.refl


  open StarHomomorphism f-well-defined
  open Star-Injective-Simplified Γ Δ
  open Reidemeister-Schreier-Simplified f g g-wd g-linv

  id-inj : Injective  _≈₁_  _≈₂_ id
  id-inj {x} {y} eq = f*-inj eq'
    where
    eq' : (f *) x ≈₂ (g *) y
    eq' =  _≈₂_.trans (refl'₂ lemma-id*) ( _≈₂_.trans eq ( _≈₂_.sym (refl'₂ lemma-id*)))

  isMonoidMonomorphism : IsMonoidMonomorphism id
  isMonoidMonomorphism = record {
    isMonoidHomomorphism = isMonoidHomomorphism ;
    injective = id-inj  }

-- A way to show id* is an isomorphism.
module StarIsomorphism
  (f-well-defined : ∀ {w v} -> w ===₁ v -> id w ≈₂ id v)
  (g-well-defined : ∀ {u t : Word A} -> u ===₂ t -> id u ≈₁ id t)
  where

  f-linv : (x : A) → [ x ]ʷ ≈₂ (f *) (g x)
  f-linv x rewrite lemma-id* {w = f x} = _≈₂_.refl
  
  f-wd : {u t : Word A} → u ===₁ t → (g *) u ≈₂ (g *) t
  f-wd {u} {t} eq rewrite lemma-id* {w = u} | lemma-id* {w = t} = f-well-defined eq

  open StarMonomorphism f-well-defined g-well-defined 
  open Star-Injective-Simplified Δ Γ
  open Reidemeister-Schreier-Simplified g f f-wd f-linv renaming (g*-surj to f*-surj)

  id-surj : Surjective _≈₁_ _≈₂_ id
  id-surj y = y , claim
    where
    claim : {z : Word A} → z ≈₁ y → id z ≈₂ y
    claim {z} = lemma-id*-cong f-well-defined
      where
      open Star-Congruence

  
  isMonoidIsomorphism : IsMonoidIsomorphism id
  isMonoidIsomorphism = record {
    isMonoidMonomorphism = isMonoidMonomorphism ;
    surjective = id-surj  }




open import Presentation.GroupLike

module GroupMorphs
       (group-like₁ : Grouplike _===₁_)
       (group-like₂ : Grouplike _===₂_)
       where
  open Group-Lemmas A _===₁_ group-like₁ renaming (•-ε-group to •-ε-group₁)
  open Group-Lemmas A _===₂_ group-like₂ renaming (•-ε-group to •-ε-group₂ ; lemma-left-inverse-unique to lemma-left-inverse-unique₂ ; lemma-cong-inv to lemma-cong-inv₂)
  
  open GroupMorphisms (Group.rawGroup •-ε-group₁) (Group.rawGroup •-ε-group₂)

  -- A way to show f* is a monoid homomorphism.
  module StarGroupHomomorphism
    (f-well-defined  : ∀ {w v} -> w ===₁ v -> id w ≈₂ id v)
    where

    open Star-Congruence  f-well-defined
    open StarHomomorphism  f-well-defined
    G₁ = Group.rawGroup •-ε-group₁
    G₂ = Group.rawGroup •-ε-group₂
    open RawGroup G₁ renaming
      (_∙_ to _∙_; _⁻¹ to _⁻¹₁)
    open RawGroup G₂ renaming
      (_∙_ to _◦_; _⁻¹ to _⁻¹₂)

    inv-homo : ∀ x → (x ⁻¹₁) ≈₂ (x) ⁻¹₂
    inv-homo [ x ]ʷ = begin
      ([ x ]ʷ ⁻¹₁) ≈⟨ lemma-left-inverse-unique₂ {g = [ x ]ʷ} {h = ([ x ]ʷ ⁻¹₁)} (lemma-id*-cong (group-like₁ x .Data.Product.proj₂)) ⟩
      [ x ]ʷ ⁻¹₂ ∎
      where open SR ws₂
    inv-homo ε = refl₂
    inv-homo (x • y) = begin
      ((x • y) ⁻¹₁) ≈⟨ lemma-id*-cong {(x • y) ⁻¹₁} {y ⁻¹₁ • x ⁻¹₁} refl ⟩
      (y ⁻¹₁ • x ⁻¹₁) ≈⟨ refl ⟩
      (y ⁻¹₁) • (x ⁻¹₁) ≈⟨ cong (inv-homo y) (inv-homo x) ⟩
      (y) ⁻¹₂ • (x) ⁻¹₂ ≈⟨ refl ⟩
      (x • y) ⁻¹₂ ∎
      where open SR ws₂
    
    isGroupHomomorphism : IsGroupHomomorphism id
    isGroupHomomorphism = record { isMonoidHomomorphism = isMonoidHomomorphism ; ⁻¹-homo = inv-homo }


  -- A way to show f* is a monomorphism.
  module StarGroupMonomorphism
    (f-well-defined  : ∀ {w v} -> w ===₁ v -> id w ≈₂ id v)
    (g-well-defined : ∀ {u t : Word A} -> u ===₂ t -> id u ≈₁ id t)
    where

    open StarGroupHomomorphism f-well-defined
    open Star-Injective-Simplified Γ Δ
    
    f-linv : (x : A) → [ x ]ʷ ≈₂ (f *) (g x)
    f-linv x rewrite lemma-id* {w = f x} = _≈₂_.refl

    f-wd : {u t : Word A} → u ===₁ t → (g *) u ≈₂ (g *) t
    f-wd {u} {t} eq rewrite lemma-id* {w = u} | lemma-id* {w = t} = f-well-defined eq

    open StarMonomorphism f-well-defined g-well-defined 

    open Reidemeister-Schreier-Simplified f g g-wd g-linv


    isGroupMonomorphism : IsGroupMonomorphism id
    isGroupMonomorphism = record {
      isGroupHomomorphism = isGroupHomomorphism ;
      injective = id-inj  } -- 



  -- A way to show id* is an isomorphism.
  module StarGroupIsomorphism
    (f-well-defined : ∀ {w v} -> w ===₁ v -> id w ≈₂ id v)
    (g-well-defined : ∀ {u t : Word A} -> u ===₂ t -> id u ≈₁ id t)
    where

    f-linv : (x : A) → [ x ]ʷ ≈₂ (f *) (g x)
    f-linv x rewrite lemma-id* {w = f x} = _≈₂_.refl

    f-wd : {u t : Word A} → u ===₁ t → (g *) u ≈₂ (g *) t
    f-wd {u} {t} eq rewrite lemma-id* {w = u} | lemma-id* {w = t} = f-well-defined eq

    open StarGroupMonomorphism f-well-defined g-well-defined 
    open Star-Injective-Simplified Δ Γ

    id-surj : Surjective _≈₁_ _≈₂_ id
    id-surj y = y , claim
      where
      claim : {z : Word A} → z ≈₁ y → id z ≈₂ y
      claim {z} = lemma-id*-cong f-well-defined
        where
        open Star-Congruence

    isGroupIsomorphism : IsGroupIsomorphism id
    isGroupIsomorphism = record {
      isGroupMonomorphism = isGroupMonomorphism ;
      surjective = id-surj  }
