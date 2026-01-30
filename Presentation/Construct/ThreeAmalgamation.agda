open import Relation.Binary using (Rel ; REL)

open import Level using (0ℓ)
open import Data.Product using (_,_ ; _×_ ; map ; proj₁ ; proj₂ ; Σ ; ∃ ; ∃-syntax)
import Data.Product.Relation.Binary.Pointwise.NonDependent as PW
open import Data.Sum using (_⊎_ ; inj₁ ; inj₂ ; assocʳ ; assocˡ)
open import Data.Nat using (ℕ ; zero ; suc)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤ ; tt)
open import Function using (_∘_ ; _∘₂_ ; id)
open import Relation.Binary.PropositionalEquality using (_≡_ ; inspect ; setoid ; module ≡-Reasoning) renaming ([_] to [_]')
import Relation.Binary.PropositionalEquality as Eq

import Relation.Binary.Reasoning.Setoid as SR

open import Word.Base
open import Word.Properties
open import Presentation.Base
open import Presentation.Reidemeister-Schreier

open import Presentation.Construct.Base
open import Presentation.Construct.Properties.Amalgamation
open import Presentation.Morphism as Morphism
open import Presentation.MorphismId as MorphismId

import Presentation.Base as PB
import Presentation.Properties as PP

open import Algebra.Morphism.Structures using (module MonoidMorphisms)
open import Algebra.Bundles using (Monoid)


module Presentation.Construct.ThreeAmalgamation
  {X Y Z : Set}
  (Γ₁ : WRel (X ⊎ Y))
  (Γ₂ : WRel (X ⊎ Z))
  (Γ₃ : WRel (Y ⊎ Z))
  where

  amal12 : WRel ((X ⊎ Y) ⊎ (X ⊎ Z))
  amal12 = Γ₁ ⸲ Γ₂ ⸲ Γₐ ([_]ʷ ∘ inj₁) ([_]ʷ ∘ inj₁)

  amal23 : WRel ((X ⊎ Z) ⊎ (Y ⊎ Z))
  amal23 = Γ₂ ⸲ Γ₃ ⸲ Γₐ ([_]ʷ ∘ inj₂) ([_]ʷ ∘ inj₂)

  amal13 : WRel ((X ⊎ Y) ⊎ (Y ⊎ Z))
  amal13 = Γ₁ ⸲ Γ₃ ⸲ Γₐ ([_]ʷ ∘ inj₂) ([_]ʷ ∘ inj₁)

  Γ₁' : WRel ((X ⊎ Y) ⊎ Z)
  Γ₁' = Γ₁ ⸲ Γₑ ⸲ Γₑ

  ext1 : (X ⊎ Y) -> X ⊎ Y ⊎ Z
  ext1 (inj₁ x) = inj₁ x
  ext1 (inj₂ y) = inj₂ (inj₁ y)

  ext2 : (X ⊎ Z) -> X ⊎ Y ⊎ Z
  ext2 (inj₁ x) = inj₁ x
  ext2 (inj₂ z) = inj₂ (inj₂ z)

  ext3 : (Y ⊎ Z) -> X ⊎ Y ⊎ Z
  ext3 yz = inj₂ yz

  data Γ₁'' : WRel (X ⊎ Y ⊎ Z) where
    lift : ∀ {w v} -> Γ₁ w v -> Γ₁'' (wmap ext1 w) (wmap ext1 v)
    
  data Γ₂'' : WRel (X ⊎ Y ⊎ Z) where
    lift : ∀ {w v} -> Γ₂ w v -> Γ₂'' (wmap ext2 w) (wmap ext2 v)

  data Γ₃'' : WRel (X ⊎ Y ⊎ Z) where
    lift : ∀ {w v} -> Γ₃ w v -> Γ₃'' (wmap ext3 w) (wmap ext3 v)

  module MX = Morphism (Γ₁'' ∪ Γ₂'') amal12
  
  fx : X ⊎ Y ⊎ Z -> (X ⊎ Y) ⊎ (X ⊎ Z)
  fx (inj₁ x) = inj₁ (inj₁ x)
  fx (inj₂ (inj₁ y)) = inj₁ (inj₂ y)
  fx (inj₂ (inj₂ z)) = inj₂ (inj₂ z)
  
  gx : (X ⊎ Y) ⊎ (X ⊎ Z) -> X ⊎ Y ⊎ Z
  gx (inj₁ (inj₁ x)) = inj₁ x
  gx (inj₁ (inj₂ y)) = inj₂ (inj₁ y)
  gx (inj₂ (inj₁ x)) = inj₁ x
  gx (inj₂ (inj₂ z)) = inj₂ (inj₂ z)

  open PB (Γ₁'' ∪ Γ₂'') renaming (_===_ to _===₁_ ; _≈_ to _≈₁_) using ()
  open PP (Γ₁'' ∪ Γ₂'') renaming (•-ε-monoid to m₁ ; word-setoid to ws₁) using ()
  open PB amal12 renaming (_===_ to _===₂_ ; _≈_ to _≈₂_) using ()
  open PP amal12 renaming (•-ε-monoid to m₂ ; word-setoid to ws₂) using ()
 
  module LRx = LeftRightCongruence Γ₁ Γ₂ (Γₐ ([_]ʷ ∘ inj₁) ([_]ʷ ∘ inj₁))

  fx∘ext1=inj₁ : ∀ {x} -> (fx ∘ ext1) x ≡ inj₁ x
  fx∘ext1=inj₁ {inj₁ x} = Eq.refl
  fx∘ext1=inj₁ {inj₂ y} = Eq.refl

  wmap-fx∘ext1=wmap-inj₁ : ∀ {w} -> wmap (fx ∘ ext1) w ≡ wmap inj₁ w
  wmap-fx∘ext1=wmap-inj₁ {[ x ]ʷ} = Eq.cong [_]ʷ fx∘ext1=inj₁
  wmap-fx∘ext1=wmap-inj₁ {ε} = Eq.refl
  wmap-fx∘ext1=wmap-inj₁ {w • w₁} = Eq.cong₂ _•_ wmap-fx∘ext1=wmap-inj₁ wmap-fx∘ext1=wmap-inj₁

  wmap-fx∘ext2=wmap-inj₁ : ∀ {w} -> wmap (fx ∘ ext2) w ≈₂ wmap inj₂ w
  wmap-fx∘ext2=wmap-inj₁ {[ inj₁ x ]ʷ} = _≈_.axiom (mid amal)
  wmap-fx∘ext2=wmap-inj₁ {[ inj₂ y ]ʷ} = _≈_.refl
  wmap-fx∘ext2=wmap-inj₁ {ε} = _≈_.refl
  wmap-fx∘ext2=wmap-inj₁ {w • w₁} = _≈_.cong wmap-fx∘ext2=wmap-inj₁ wmap-fx∘ext2=wmap-inj₁

  wmap-gx∘inj₁=wmap-ext1 : ∀ {w} -> wmap (gx ∘ inj₁) w ≡ wmap ext1 w
  wmap-gx∘inj₁=wmap-ext1 {[ inj₁ x ]ʷ} = Eq.refl
  wmap-gx∘inj₁=wmap-ext1 {[ inj₂ y ]ʷ} = Eq.refl
  wmap-gx∘inj₁=wmap-ext1 {ε} = Eq.refl
  wmap-gx∘inj₁=wmap-ext1 {w • w₁} = Eq.cong₂ _•_ wmap-gx∘inj₁=wmap-ext1 wmap-gx∘inj₁=wmap-ext1

  wmap-gx∘inj₂=wmap-ext1 : ∀ {w} -> wmap (gx ∘ inj₂) w ≡ wmap ext2 w
  wmap-gx∘inj₂=wmap-ext1 {[ inj₁ x ]ʷ} = Eq.refl
  wmap-gx∘inj₂=wmap-ext1 {[ inj₂ y ]ʷ} = Eq.refl
  wmap-gx∘inj₂=wmap-ext1 {ε} = Eq.refl
  wmap-gx∘inj₂=wmap-ext1 {w • w₁} = Eq.cong₂ _•_ wmap-gx∘inj₂=wmap-ext1 wmap-gx∘inj₂=wmap-ext1


  fx-wd : {w v : Word (X ⊎ Y ⊎ Z)} →  w ===₁ v → (([_]ʷ ∘ fx) *) w ≈₂ (([_]ʷ ∘ fx) *) v
  fx-wd {.(wmap ext1 w)} {.(wmap ext1 v)} (left (lift {w} {v} x)) = begin
    (([_]ʷ ∘ fx) *) (wmap ext1 w) ≡⟨ lemma-* (wmap ext1 w) ⟩
    (wmap fx) (wmap ext1 w) ≡⟨ Eq.sym (wmap-∘ w) ⟩
    wmap (fx ∘ ext1) w ≡⟨ wmap-fx∘ext1=wmap-inj₁ ⟩
    wmap (inj₁) w ≈⟨ LRx.lefts (_≈_.axiom x) ⟩
    wmap (inj₁) v ≡⟨ Eq.sym wmap-fx∘ext1=wmap-inj₁ ⟩
    wmap (fx ∘ ext1) v ≡⟨ wmap-∘ v ⟩
    (wmap fx) (wmap ext1 v) ≡⟨ Eq.sym (lemma-* (wmap ext1 v)) ⟩
    (([_]ʷ ∘ fx) *) (wmap ext1 v) ∎
      where
      open SR ws₂
      
  fx-wd {.(wmap ext2 w)} {.(wmap ext2 v)} (right (lift {w} {v} x)) = begin
    (([_]ʷ ∘ fx) *) (wmap ext2 w) ≡⟨ lemma-* (wmap ext2 w) ⟩
    (wmap fx) (wmap ext2 w) ≡⟨ Eq.sym (wmap-∘ w) ⟩
    wmap (fx ∘ ext2) w ≈⟨ wmap-fx∘ext2=wmap-inj₁ ⟩
    wmap (inj₂) w ≈⟨ LRx.rights (_≈_.axiom x) ⟩
    wmap (inj₂) v ≈⟨ _≈_.sym wmap-fx∘ext2=wmap-inj₁ ⟩
    wmap (fx ∘ ext2) v ≡⟨ wmap-∘ v ⟩
    (wmap fx) (wmap ext2 v) ≡⟨ Eq.sym (lemma-* (wmap ext2 v)) ⟩
    (([_]ʷ ∘ fx) *) (wmap ext2 v) ∎
      where
      open SR ws₂

  gx-wd : {u t : Word ((X ⊎ Y) ⊎ X ⊎ Z)} → u ===₂ t → ((λ x → [ gx x ]ʷ) *) u ≈₁ ((λ x → [ gx x ]ʷ) *) t
  gx-wd {.([ w ]ₗ)} {.([ v ]ₗ)} (left {w} {v} x) = begin
    (([_]ʷ ∘ gx) *) ([ w ]ₗ) ≡⟨ lemma-* ([ w ]ₗ) ⟩
    (wmap gx) ([ w ]ₗ) ≡⟨ Eq.sym (wmap-∘ w) ⟩
    wmap (gx ∘ inj₁) w ≡⟨ wmap-gx∘inj₁=wmap-ext1 ⟩
    wmap (ext1) w ≈⟨ _≈_.axiom (left (lift x)) ⟩
    wmap (ext1) v ≡⟨ Eq.sym wmap-gx∘inj₁=wmap-ext1 ⟩
    wmap (gx ∘ inj₁) v ≡⟨ wmap-∘ v ⟩
    (wmap gx) ([ v ]ₗ) ≡⟨ Eq.sym (lemma-* ([ v ]ₗ)) ⟩
    (([_]ʷ ∘ gx) *) ([ v ]ₗ) ∎
      where
      open SR ws₁

  gx-wd {.([ w ]ᵣ)} {.([ v ]ᵣ)} (right {w} {v} x) = begin
    (([_]ʷ ∘ gx) *) ([ w ]ᵣ) ≡⟨ lemma-* ([ w ]ᵣ) ⟩
    (wmap gx) ([ w ]ᵣ) ≡⟨ Eq.sym (wmap-∘ w) ⟩
    wmap (gx ∘ inj₂) w ≡⟨ wmap-gx∘inj₂=wmap-ext1  ⟩
    wmap ext2 w ≈⟨ _≈_.axiom (right (lift x)) ⟩
    wmap ext2 v ≡⟨ Eq.sym wmap-gx∘inj₂=wmap-ext1 ⟩
    wmap (gx ∘ inj₂) v ≡⟨ wmap-∘ v ⟩
    (wmap gx) ([ v ]ᵣ) ≡⟨ Eq.sym (lemma-* ([ v ]ᵣ)) ⟩
    (([_]ʷ ∘ gx) *) ([ v ]ᵣ) ∎
      where
      open SR ws₁
      
  gx-wd {.([ [ inj₁ m ]ʷ ]ₗ)} {.([ [ inj₁ m ]ʷ ]ᵣ)} (mid (amal {m})) =
    let w = [ inj₁ m ]ʷ in
    let v = [ inj₁ m ]ʷ in
    begin
    (([_]ʷ ∘ gx) *) ([ w ]ᵣ) ≡⟨ Eq.refl ⟩
    (([_]ʷ ∘ gx) *) ([ v ]ᵣ) ∎
      where
      open SR ws₁

  fx-linv : (x : (X ⊎ Y) ⊎ X ⊎ Z) → [ x ]ʷ ≈₂ ((λ x₁ → [ fx x₁ ]ʷ) *) [ gx x ]ʷ
  fx-linv (inj₁ (inj₁ x)) = _≈_.refl
  fx-linv (inj₁ (inj₂ y)) = _≈_.refl
  fx-linv (inj₂ (inj₁ x)) = _≈_.sym (_≈_.axiom (mid amal))
  fx-linv (inj₂ (inj₂ y)) = _≈_.refl

  gx-linv : (x : X ⊎ Y ⊎ Z) → [ x ]ʷ ≈₁ ((λ x₁ → [ gx x₁ ]ʷ) *) [ fx x ]ʷ
  gx-linv (inj₁ x) = _≈_.refl
  gx-linv (inj₂ (inj₁ y)) = _≈_.refl
  gx-linv (inj₂ (inj₂ z)) = _≈_.refl

  module MMx = MonoidMorphisms (Monoid.rawMonoid m₁) (Monoid.rawMonoid m₂)
  isox : MMx.IsMonoidIsomorphism (([_]ʷ ∘ fx) *)
  isox = MX.StarIsomorphism.isMonoidIsomorphism ([_]ʷ ∘ fx) ([_]ʷ ∘ gx) fx-wd fx-linv gx-wd gx-linv


    



  fy : X ⊎ Y ⊎ Z -> (X ⊎ Y) ⊎ (Y ⊎ Z)
  fy (inj₁ x) = inj₁ (inj₁ x)
  fy (inj₂ (inj₁ y)) = inj₂ (inj₁ y)
  fy (inj₂ (inj₂ z)) = inj₂ (inj₂ z)
  
  gy : (X ⊎ Y) ⊎ (Y ⊎ Z) -> X ⊎ Y ⊎ Z
  gy (inj₁ (inj₁ x)) = inj₁ x
  gy (inj₁ (inj₂ y)) = inj₂ (inj₁ y)
  gy (inj₂ (inj₁ y)) = inj₂ (inj₁ y)
  gy (inj₂ (inj₂ z)) = inj₂ (inj₂ z)

  open PB (Γ₁'' ∪ Γ₃'') renaming (_===_ to _===₁₃_ ; _≈_ to _≈₁₃_) using ()
  open PP (Γ₁'' ∪ Γ₃'') renaming (•-ε-monoid to m₁₃ ; word-setoid to ws₁₃) using ()
  open PB amal13 renaming (_===_ to _===₁₃ₐ_ ; _≈_ to _≈₁₃ₐ_) using ()
  open PP amal13 renaming (•-ε-monoid to m₁₃ₐ ; word-setoid to ws₁₃ₐ) using ()


  module LRy = LeftRightCongruence Γ₁ Γ₃ (Γₐ ([_]ʷ ∘ inj₂) ([_]ʷ ∘ inj₁))

  wmap-fy∘ext1=wmap-inj₁ : ∀ {w} -> wmap (fy ∘ ext1) w ≈₁₃ₐ wmap inj₁ w
  wmap-fy∘ext1=wmap-inj₁ {[ inj₂ x ]ʷ} = _≈_.sym (_≈_.axiom (mid amal))
  wmap-fy∘ext1=wmap-inj₁ {[ inj₁ y ]ʷ} = _≈_.refl
  wmap-fy∘ext1=wmap-inj₁ {ε} = _≈_.refl
  wmap-fy∘ext1=wmap-inj₁ {w • w₁} = _≈_.cong wmap-fy∘ext1=wmap-inj₁ wmap-fy∘ext1=wmap-inj₁

  wmap-fy∘ext3=wmap-inj₂ : ∀ {w} -> wmap (fy ∘ ext3) w ≈₁₃ₐ wmap inj₂ w
  wmap-fy∘ext3=wmap-inj₂ {[ inj₁ x ]ʷ} = _≈₁₃ₐ_.refl
  wmap-fy∘ext3=wmap-inj₂ {[ inj₂ y ]ʷ} = _≈₁₃ₐ_.refl
  wmap-fy∘ext3=wmap-inj₂ {ε} = _≈₁₃ₐ_.refl
  wmap-fy∘ext3=wmap-inj₂ {w • w₁} = _≈₁₃ₐ_.cong wmap-fy∘ext3=wmap-inj₂ wmap-fy∘ext3=wmap-inj₂

  fy-wd : {w v : Word (X ⊎ Y ⊎ Z)} → w ===₁₃ v → ((λ x → [ fy x ]ʷ) *) w ≈₁₃ₐ ((λ x → [ fy x ]ʷ) *) v
  fy-wd {.(wmap ext1 w)} {.(wmap ext1 v)} (left (lift {w} {v} x)) = begin
    (([_]ʷ ∘ fy) *) (wmap ext1 w) ≡⟨ lemma-* (wmap ext1 w) ⟩
    (wmap fy) (wmap ext1 w) ≡⟨ Eq.sym (wmap-∘ w) ⟩
    wmap (fy ∘ ext1) w ≈⟨ wmap-fy∘ext1=wmap-inj₁ ⟩
    wmap (inj₁) w ≈⟨ LRy.lefts (_≈_.axiom x) ⟩
    wmap (inj₁) v ≈⟨ _≈_.sym wmap-fy∘ext1=wmap-inj₁ ⟩
    wmap (fy ∘ ext1) v ≡⟨ wmap-∘ v ⟩
    (wmap fy) (wmap ext1 v) ≡⟨ Eq.sym (lemma-* (wmap ext1 v)) ⟩
    (([_]ʷ ∘ fy) *) (wmap ext1 v) ∎
      where
      open SR ws₁₃ₐ
      
  fy-wd {.(wmap ext3 w)} {.(wmap ext3 v)} (right (lift {w} {v} x)) = begin
    (([_]ʷ ∘ fy) *) (wmap ext3 w) ≡⟨ lemma-* (wmap ext3 w) ⟩
    (wmap fy) (wmap ext3 w) ≡⟨ Eq.sym (wmap-∘ w) ⟩
    wmap (fy ∘ ext3) w ≈⟨ wmap-fy∘ext3=wmap-inj₂ ⟩
    wmap (inj₂) w ≈⟨ LRy.rights (_≈_.axiom x) ⟩
    wmap (inj₂) v ≈⟨ _≈_.sym wmap-fy∘ext3=wmap-inj₂ ⟩
    wmap (fy ∘ ext3) v ≡⟨ wmap-∘ v ⟩
    (wmap fy) (wmap ext3 v) ≡⟨ Eq.sym (lemma-* (wmap ext3 v)) ⟩
    (([_]ʷ ∘ fy) *) (wmap ext3 v) ∎
      where
      open SR ws₁₃ₐ

  wmap-gy∘inj₁=wmap-ext1 : ∀ {w} -> wmap (gy ∘ inj₁) w ≡ wmap ext1 w
  wmap-gy∘inj₁=wmap-ext1 {[ inj₁ x ]ʷ} = Eq.refl
  wmap-gy∘inj₁=wmap-ext1 {[ inj₂ y ]ʷ} = Eq.refl
  wmap-gy∘inj₁=wmap-ext1 {ε} = Eq.refl
  wmap-gy∘inj₁=wmap-ext1 {w • w₁} = Eq.cong₂ _•_ wmap-gy∘inj₁=wmap-ext1 wmap-gy∘inj₁=wmap-ext1

  wmap-gy∘inj₂=wmap-ext3 : ∀ {w} -> wmap (gy ∘ inj₂) w ≡ wmap ext3 w
  wmap-gy∘inj₂=wmap-ext3 {[ inj₁ x ]ʷ} = Eq.refl
  wmap-gy∘inj₂=wmap-ext3 {[ inj₂ y ]ʷ} = Eq.refl
  wmap-gy∘inj₂=wmap-ext3 {ε} = Eq.refl
  wmap-gy∘inj₂=wmap-ext3 {w • w₁} = Eq.cong₂ _•_ wmap-gy∘inj₂=wmap-ext3 wmap-gy∘inj₂=wmap-ext3


  gy-wd : {u t : Word ((X ⊎ Y) ⊎ Y ⊎ Z)} → u ===₁₃ₐ t → ((λ x → [ gy x ]ʷ) *) u ≈₁₃ ((λ x → [ gy x ]ʷ) *) t
  gy-wd {.([ w ]ₗ)} {.([ v ]ₗ)} (left {w} {v} x) = begin
    (([_]ʷ ∘ gy) *) ([ w ]ₗ) ≡⟨ lemma-* ([ w ]ₗ) ⟩
    (wmap gy) ([ w ]ₗ) ≡⟨ Eq.sym (wmap-∘ w) ⟩
    wmap (gy ∘ inj₁) w ≡⟨ wmap-gy∘inj₁=wmap-ext1 ⟩
    wmap (ext1) w ≈⟨ _≈_.axiom (left (lift x)) ⟩
    wmap (ext1) v ≡⟨ Eq.sym wmap-gy∘inj₁=wmap-ext1 ⟩
    wmap (gy ∘ inj₁) v ≡⟨ wmap-∘ v ⟩
    (wmap gy) ([ v ]ₗ) ≡⟨ Eq.sym (lemma-* ([ v ]ₗ)) ⟩
    (([_]ʷ ∘ gy) *) ([ v ]ₗ) ∎
      where
      open SR ws₁₃
  gy-wd {.([ w ]ᵣ)} {.([ v ]ᵣ)} (right {w} {v} x) = begin
    (([_]ʷ ∘ gy) *) ([ w ]ᵣ) ≡⟨ lemma-* ([ w ]ᵣ) ⟩
    (wmap gy) ([ w ]ᵣ) ≡⟨ Eq.sym (wmap-∘ w) ⟩
    wmap (gy ∘ inj₂) w ≡⟨ wmap-gy∘inj₂=wmap-ext3  ⟩
    wmap ext3 w ≈⟨ _≈_.axiom (right (lift x)) ⟩
    wmap ext3 v ≡⟨ Eq.sym wmap-gy∘inj₂=wmap-ext3 ⟩
    wmap (gy ∘ inj₂) v ≡⟨ wmap-∘ v ⟩
    (wmap gy) ([ v ]ᵣ) ≡⟨ Eq.sym (lemma-* ([ v ]ᵣ)) ⟩
    (([_]ʷ ∘ gy) *) ([ v ]ᵣ) ∎
      where
      open SR ws₁₃
      
  gy-wd {.([ [ inj₂ m ]ʷ ]ₗ)} {.([ [ inj₁ m ]ʷ ]ᵣ)} (mid (amal {m})) = _≈_.refl

  fy-linv : (x : (X ⊎ Y) ⊎ Y ⊎ Z) → [ x ]ʷ ≈₁₃ₐ ((λ x₁ → [ fy x₁ ]ʷ) *) [ gy x ]ʷ
  fy-linv (inj₁ (inj₁ x)) = _≈_.refl
  fy-linv (inj₁ (inj₂ y)) = _≈₁₃ₐ_.axiom (mid amal)
  fy-linv (inj₂ (inj₁ x)) = _≈₁₃ₐ_.refl
  fy-linv (inj₂ (inj₂ y)) = _≈_.refl

  gy-linv : (x : X ⊎ Y ⊎ Z) → [ x ]ʷ ≈₁₃ ((λ x₁ → [ gy x₁ ]ʷ) *) [ fy x ]ʷ
  gy-linv (inj₁ x) = _≈_.refl
  gy-linv (inj₂ (inj₁ y)) = _≈_.refl
  gy-linv (inj₂ (inj₂ z)) = _≈_.refl

  module MY = Morphism (Γ₁'' ∪ Γ₃'') amal13
  module MMy = MonoidMorphisms (Monoid.rawMonoid m₁₃) (Monoid.rawMonoid m₁₃ₐ)
  isoy : MMy.IsMonoidIsomorphism (([_]ʷ ∘ fy) *)
  isoy = MY.StarIsomorphism.isMonoidIsomorphism ([_]ʷ ∘ fy) ([_]ʷ ∘ gy) fy-wd fy-linv gy-wd gy-linv



  fz : X ⊎ Y ⊎ Z -> (X ⊎ Z) ⊎ (Y ⊎ Z)
  fz (inj₁ x) = inj₁ (inj₁ x)
  fz (inj₂ (inj₁ z)) = inj₂ (inj₁ z)
  fz (inj₂ (inj₂ z)) = inj₂ (inj₂ z)
  
  gz : (X ⊎ Z) ⊎ (Y ⊎ Z) -> X ⊎ Y ⊎ Z
  gz (inj₁ (inj₁ x)) = inj₁ x
  gz (inj₁ (inj₂ z)) = inj₂ (inj₂ z)
  gz (inj₂ (inj₁ y)) = inj₂ (inj₁ y)
  gz (inj₂ (inj₂ z)) = inj₂ (inj₂ z)


  open PB (Γ₂'' ∪ Γ₃'') renaming (_===_ to _===₂₃_ ; _≈_ to _≈₂₃_) using ()
  open PP (Γ₂'' ∪ Γ₃'') renaming (•-ε-monoid to m₂₃ ; word-setoid to ws₂₃) using ()
  open PB amal23 renaming (_===_ to _===₂₃ₐ_ ; _≈_ to _≈₂₃ₐ_) using ()
  open PP amal23 renaming (•-ε-monoid to m₂₃ₐ ; word-setoid to ws₂₃ₐ) using ()


  module LRz = LeftRightCongruence Γ₂ Γ₃ (Γₐ ([_]ʷ ∘ inj₂) ([_]ʷ ∘ inj₂))


  wmap-fz∘ext2=wmap-inj₁ : ∀ {w} -> wmap (fz ∘ ext2) w ≈₂₃ₐ wmap inj₁ w
  wmap-fz∘ext2=wmap-inj₁ {[ inj₂ x ]ʷ} = _≈_.sym (_≈_.axiom (mid amal))
  wmap-fz∘ext2=wmap-inj₁ {[ inj₁ y ]ʷ} = _≈_.refl
  wmap-fz∘ext2=wmap-inj₁ {ε} = _≈_.refl
  wmap-fz∘ext2=wmap-inj₁ {w • w₁} = _≈_.cong wmap-fz∘ext2=wmap-inj₁ wmap-fz∘ext2=wmap-inj₁

  wmap-fz∘ext3=wmap-inj₂ : ∀ {w} -> wmap (fz ∘ ext3) w ≈₂₃ₐ wmap inj₂ w
  wmap-fz∘ext3=wmap-inj₂ {[ inj₁ x ]ʷ} = _≈₂₃ₐ_.refl
  wmap-fz∘ext3=wmap-inj₂ {[ inj₂ y ]ʷ} = _≈₂₃ₐ_.refl
  wmap-fz∘ext3=wmap-inj₂ {ε} = _≈₂₃ₐ_.refl
  wmap-fz∘ext3=wmap-inj₂ {w • w₁} = _≈₂₃ₐ_.cong wmap-fz∘ext3=wmap-inj₂ wmap-fz∘ext3=wmap-inj₂


  fz-wd : {w v : Word (X ⊎ Y ⊎ Z)} → w ===₂₃ v → ((λ x → [ fz x ]ʷ) *) w ≈₂₃ₐ ((λ x → [ fz x ]ʷ) *) v
  fz-wd {.(wmap ext2 w)} {.(wmap ext2 v)} (left (lift {w} {v} x)) = begin
    (([_]ʷ ∘ fz) *) (wmap ext2 w) ≡⟨ lemma-* (wmap ext2 w) ⟩
    (wmap fz) (wmap ext2 w) ≡⟨ Eq.sym (wmap-∘ w) ⟩
    wmap (fz ∘ ext2) w ≈⟨ wmap-fz∘ext2=wmap-inj₁ ⟩
    wmap (inj₁) w ≈⟨ LRz.lefts (_≈_.axiom x) ⟩
    wmap (inj₁) v ≈⟨ _≈_.sym wmap-fz∘ext2=wmap-inj₁ ⟩
    wmap (fz ∘ ext2) v ≡⟨ wmap-∘ v ⟩
    (wmap fz) (wmap ext2 v) ≡⟨ Eq.sym (lemma-* (wmap ext2 v)) ⟩
    (([_]ʷ ∘ fz) *) (wmap ext2 v) ∎
      where
      open SR ws₂₃ₐ
      
  fz-wd {.(wmap ext3 w)} {.(wmap ext3 v)} (right (lift {w} {v} x)) = begin
    (([_]ʷ ∘ fz) *) (wmap ext3 w) ≡⟨ lemma-* (wmap ext3 w) ⟩
    (wmap fz) (wmap ext3 w) ≡⟨ Eq.sym (wmap-∘ w) ⟩
    wmap (fz ∘ ext3) w ≈⟨ wmap-fz∘ext3=wmap-inj₂ ⟩
    wmap (inj₂) w ≈⟨ LRz.rights (_≈_.axiom x) ⟩
    wmap (inj₂) v ≈⟨ _≈_.sym wmap-fz∘ext3=wmap-inj₂ ⟩
    wmap (fz ∘ ext3) v ≡⟨ wmap-∘ v ⟩
    (wmap fz) (wmap ext3 v) ≡⟨ Eq.sym (lemma-* (wmap ext3 v)) ⟩
    (([_]ʷ ∘ fz) *) (wmap ext3 v) ∎
      where
      open SR ws₂₃ₐ

  wmap-gz∘inj₁=wmap-ext2 : ∀ {w} -> wmap (gz ∘ inj₁) w ≡ wmap ext2 w
  wmap-gz∘inj₁=wmap-ext2 {[ inj₁ x ]ʷ} = Eq.refl
  wmap-gz∘inj₁=wmap-ext2 {[ inj₂ y ]ʷ} = Eq.refl
  wmap-gz∘inj₁=wmap-ext2 {ε} = Eq.refl
  wmap-gz∘inj₁=wmap-ext2 {w • w₁} = Eq.cong₂ _•_ wmap-gz∘inj₁=wmap-ext2 wmap-gz∘inj₁=wmap-ext2

  wmap-gz∘inj₂=wmap-ext3 : ∀ {w} -> wmap (gz ∘ inj₂) w ≡ wmap ext3 w
  wmap-gz∘inj₂=wmap-ext3 {[ inj₁ x ]ʷ} = Eq.refl
  wmap-gz∘inj₂=wmap-ext3 {[ inj₂ y ]ʷ} = Eq.refl
  wmap-gz∘inj₂=wmap-ext3 {ε} = Eq.refl
  wmap-gz∘inj₂=wmap-ext3 {w • w₁} = Eq.cong₂ _•_ wmap-gz∘inj₂=wmap-ext3 wmap-gz∘inj₂=wmap-ext3

  gz-wd : {u t : Word ((X ⊎ Z) ⊎ Y ⊎ Z)} → u ===₂₃ₐ t → ((λ x → [ gz x ]ʷ) *) u ≈₂₃ ((λ x → [ gz x ]ʷ) *) t
  gz-wd {.([ w ]ₗ)} {.([ v ]ₗ)} (left {w} {v} x) = begin
    (([_]ʷ ∘ gz) *) ([ w ]ₗ) ≡⟨ lemma-* ([ w ]ₗ) ⟩
    (wmap gz) ([ w ]ₗ) ≡⟨ Eq.sym (wmap-∘ w) ⟩
    wmap (gz ∘ inj₁) w ≡⟨ wmap-gz∘inj₁=wmap-ext2 ⟩
    wmap (ext2) w ≈⟨ _≈_.axiom (left (lift x)) ⟩
    wmap (ext2) v ≡⟨ Eq.sym wmap-gz∘inj₁=wmap-ext2 ⟩
    wmap (gz ∘ inj₁) v ≡⟨ wmap-∘ v ⟩
    (wmap gz) ([ v ]ₗ) ≡⟨ Eq.sym (lemma-* ([ v ]ₗ)) ⟩
    (([_]ʷ ∘ gz) *) ([ v ]ₗ) ∎
      where
      open SR ws₂₃
      
  gz-wd {.([ w ]ᵣ)} {.([ v ]ᵣ)} (right {w} {v} x) = begin
    (([_]ʷ ∘ gz) *) ([ w ]ᵣ) ≡⟨ lemma-* ([ w ]ᵣ) ⟩
    (wmap gz) ([ w ]ᵣ) ≡⟨ Eq.sym (wmap-∘ w) ⟩
    wmap (gz ∘ inj₂) w ≡⟨ wmap-gz∘inj₂=wmap-ext3  ⟩
    wmap ext3 w ≈⟨ _≈_.axiom (right (lift x)) ⟩
    wmap ext3 v ≡⟨ Eq.sym wmap-gz∘inj₂=wmap-ext3 ⟩
    wmap (gz ∘ inj₂) v ≡⟨ wmap-∘ v ⟩
    (wmap gz) ([ v ]ᵣ) ≡⟨ Eq.sym (lemma-* ([ v ]ᵣ)) ⟩
    (([_]ʷ ∘ gz) *) ([ v ]ᵣ) ∎
      where
      open SR ws₂₃

  gz-wd {.([ [ inj₂ m ]ʷ ]ₗ)} {.([ [ inj₂ m ]ʷ ]ᵣ)} (mid (amal {m})) = _≈_.refl

  fz-linv : (x : (X ⊎ Z) ⊎ Y ⊎ Z) → [ x ]ʷ ≈₂₃ₐ ((λ x₁ → [ fz x₁ ]ʷ) *) [ gz x ]ʷ
  fz-linv (inj₁ (inj₁ x)) = _≈_.refl
  fz-linv (inj₁ (inj₂ y)) = _≈₂₃ₐ_.axiom (mid amal)
  fz-linv (inj₂ (inj₁ x)) = _≈₂₃ₐ_.refl
  fz-linv (inj₂ (inj₂ y)) = _≈_.refl

  gz-linv : (x : X ⊎ Y ⊎ Z) → [ x ]ʷ ≈₂₃ ((λ x₁ → [ gz x₁ ]ʷ) *) [ fz x ]ʷ
  gz-linv (inj₁ x) = _≈_.refl
  gz-linv (inj₂ (inj₁ y)) = _≈_.refl
  gz-linv (inj₂ (inj₂ z)) = _≈_.refl


  module MZ = Morphism (Γ₂'' ∪ Γ₃'') amal23
  module MMz = MonoidMorphisms (Monoid.rawMonoid m₂₃) (Monoid.rawMonoid m₂₃ₐ)

  isoz : MMz.IsMonoidIsomorphism (([_]ʷ ∘ fz) *)
  isoz = MZ.StarIsomorphism.isMonoidIsomorphism ([_]ʷ ∘ fz) ([_]ʷ ∘ gz) fz-wd fz-linv gz-wd gz-linv


  module ∪-assoc
    {X : Set}
    (Γ Δ Λ : WRel X)
    where
    
    ll = ((Γ ∪ Δ) ∪ Λ)
    rr = (Γ ∪ Δ ∪ Λ)
    
    module MC = MorphismId ll rr

    open PB ll renaming (_===_ to _===₁ₒ_ ; _≈_ to _≈₁ₒ_) using ()
    open PB rr renaming (_===_ to _===₂ₒ_ ; _≈_ to _≈₂ₒ_) using ()

    wd1 : {w v : Word X} →  w ===₁ₒ v → id w ≈₂ₒ id v
    wd1 {w} {v} (left (left x)) = _≈₂ₒ_.axiom (left x)
    wd1 {w} {v} (left (right x)) = _≈₂ₒ_.axiom (right (left x ))
    wd1 {w} {v} (right x) = _≈₂ₒ_.axiom (right (right x))

    wd2 : {u t : Word X} → u ===₂ₒ t → id u ≈₁ₒ id t
    wd2 {w} {v} (left x) = _≈₁ₒ_.axiom (left (left x))
    wd2 {w} {v} (right (left x)) = _≈₁ₒ_.axiom (left (right x))
    wd2 {w} {v} (right (right x)) = _≈₁ₒ_.axiom (right x)

    open PP ll renaming (•-ε-monoid to mc₁)
    open PP rr renaming (•-ε-monoid to mc₂)
    module MMC = MonoidMorphisms (Monoid.rawMonoid mc₁) (Monoid.rawMonoid mc₂)

    iso-assoc : MMC.IsMonoidIsomorphism id
    iso-assoc = MC.StarIsomorphism.isMonoidIsomorphism wd1 wd2
    
  module ∪-comm
    {X : Set}
    (Γ Δ : WRel X)
    where
    module MC = MorphismId (Γ ∪ Δ) (Δ ∪ Γ)

    open PB (Γ ∪ Δ) renaming (_===_ to _===₁ₒ_ ; _≈_ to _≈₁ₒ_) using ()
    open PB (Δ ∪ Γ) renaming (_===_ to _===₂ₒ_ ; _≈_ to _≈₂ₒ_) using ()

    wd1 : {w v : Word X} →  w ===₁ₒ v → id w ≈₂ₒ id v
    wd1 {w} {v} (left x) = _≈₂ₒ_.axiom (right x)
    wd1 {w} {v} (right x) = _≈₂ₒ_.axiom (left x)

    wd2 : {u t : Word X} → u ===₂ₒ t → id u ≈₁ₒ id t
    wd2 {w} {v} (left x) = _≈₁ₒ_.axiom (right x)
    wd2 {w} {v} (right x) = _≈₁ₒ_.axiom (left x)

    open PP (Γ ∪ Δ) renaming (•-ε-monoid to mc₁)
    open PP (Δ ∪ Γ) renaming (•-ε-monoid to mc₂)
    module MMC = MonoidMorphisms (Monoid.rawMonoid mc₁) (Monoid.rawMonoid mc₂)

    iso-comm : MMC.IsMonoidIsomorphism id
    iso-comm = MC.StarIsomorphism.isMonoidIsomorphism wd1 wd2


  module iso-iso
    {X Y : Set}
    (Γ : WRel X)
    (Δ : WRel Y)
    (ff : Word X -> Word Y)
    (open PP Γ renaming (•-ε-monoid to mi₁ ; word-setoid to w₁))
    (open PP Δ renaming (•-ε-monoid to mi₂ ; word-setoid to w₂))
    (open MonoidMorphisms (Monoid.rawMonoid mi₁) (Monoid.rawMonoid mi₂) using (IsMonoidIsomorphism))
    (iso→ : IsMonoidIsomorphism ff)
    where

    open PB Γ renaming (_===_ to _===₁ₒ_ ; _≈_ to _≈₁ₒ_ ; refl' to refl'₁) using ()
    open PB Δ renaming (_===_ to _===₂ₒ_ ; _≈_ to _≈₂ₒ_) using ()

    open IsMonoidIsomorphism iso→ renaming (injective to inje₁ ; ⟦⟧-cong to ⟦⟧-cong₁) using (surjective ; ε-homo ; homo)

    gg : Word Y -> Word X
    gg y = proj₁ (surjective y)

    open import Function.Definitions using (Surjective ; Injective)
    
    gg-surj : Surjective _≈₂ₒ_ _≈₁ₒ_ gg
    gg-surj x = (ff x) , claim
      where
      open SR w₂
      claim : {y : Word Y} → y ≈₂ₒ ff x → gg y ≈₁ₒ x
      claim {y} eq = inje₁ (begin
        ff (gg y) ≈⟨ proj₂ (surjective y) (refl'₁ Eq.refl) ⟩
        y ≈⟨ eq ⟩
        ff x ∎)
        
    gg-inj : Injective _≈₂ₒ_ _≈₁ₒ_ gg
    gg-inj {x} {y} eq = begin
      x ≈⟨ sym (proj₂ (surjective x) (refl'₁ Eq.refl)) ⟩
      ff (gg x) ≈⟨ ⟦⟧-cong₁ eq ⟩
      ff (gg y) ≈⟨ (proj₂ (surjective y) (refl'₁ Eq.refl)) ⟩
      y ∎
      where
      open SR w₂

    gg-ε : gg ε ≈₁ₒ ε
    gg-ε = inje₁ (
      begin
        ff (gg ε) ≈⟨ (proj₂ (surjective ε) (refl'₁ Eq.refl)) ⟩
        ε ≈⟨ sym ε-homo ⟩
        ff ε ∎)
      where
      open SR w₂

    gg-homo : ∀ x y → gg (x • y) ≈₁ₒ (gg x • gg y)
    gg-homo x y = inje₁ (
      begin
        ff (gg (x • y)) ≈⟨ (proj₂ (surjective (x • y)) (refl'₁ Eq.refl)) ⟩
        (x • y) ≈⟨ cong (sym ((proj₂ (surjective (x)) (refl'₁ Eq.refl)))) (sym ((proj₂ (surjective (y)) (refl'₁ Eq.refl)))) ⟩
        ff (gg x) • ff (gg y) ≈⟨ sym (homo (gg x) (gg y)) ⟩
        ff (gg x • gg y) ∎)
      where
      open SR w₂

    gg-cong : ∀ {x y} → x ≈₂ₒ y -> gg x ≈₁ₒ gg y
    gg-cong {x} {y} eq = inje₁ (
      begin
        ff (gg x) ≈⟨ (proj₂ (surjective x) (refl'₁ Eq.refl)) ⟩
        x ≈⟨ eq ⟩
        y ≈⟨ (sym ((proj₂ (surjective y) (refl'₁ Eq.refl)))) ⟩
        ff (gg y) ∎)
      where
      open SR w₂


  
    wd1 : {w v : Word X} →  w ===₁ₒ v → ff w ≈₂ₒ ff v
    wd1 {w} {v} eq = ⟦⟧-cong₁ (_≈₁ₒ_.axiom eq)

    open PP Γ renaming (•-ε-monoid to mc₁)
    open PP Δ renaming (•-ε-monoid to mc₂)
    module MMC = MonoidMorphisms (Monoid.rawMonoid mc₂) (Monoid.rawMonoid mc₁)

    iso← : MMC.IsMonoidIsomorphism gg
    iso← = record { isMonoidMonomorphism =
      record { isMonoidHomomorphism =
        record { isMagmaHomomorphism = record { isRelHomomorphism = record { cong = gg-cong } ; homo = gg-homo } ; ε-homo = gg-ε } ; injective = gg-inj } ; surjective = gg-surj } --MC.StarIsomorphism.isMonoidIsomorphism wd2 wd1


  module iso-iso-id
    {X : Set}
    (Γ Δ : WRel X)
    (open PP Γ renaming (•-ε-monoid to mi₁))
    (open PP Δ renaming (•-ε-monoid to mi₂))
    (open MonoidMorphisms (Monoid.rawMonoid mi₁) (Monoid.rawMonoid mi₂) using (IsMonoidIsomorphism))
    (iso→ : IsMonoidIsomorphism id)
    where
    module MC = MorphismId Δ Γ

    open PB Γ renaming (_===_ to _===₁ₒ_ ; _≈_ to _≈₁ₒ_) using ()
    open PB Δ renaming (_===_ to _===₂ₒ_ ; _≈_ to _≈₂ₒ_) using ()

    open IsMonoidIsomorphism iso→ renaming (injective to inje₁ ; ⟦⟧-cong to ⟦⟧-cong₁)

    wd1 : {w v : Word X} →  w ===₁ₒ v → id w ≈₂ₒ id v
    wd1 {w} {v} eq = ⟦⟧-cong₁ (_≈₁ₒ_.axiom eq)

    wd2 : {u t : Word X} → u ===₂ₒ t → id u ≈₁ₒ id t
    wd2 {w} {v} eq = inje₁ (_≈_.axiom eq)

    open PP Γ renaming (•-ε-monoid to mc₁)
    open PP Δ renaming (•-ε-monoid to mc₂)
    module MMC = MonoidMorphisms (Monoid.rawMonoid mc₂) (Monoid.rawMonoid mc₁)

    iso← : MMC.IsMonoidIsomorphism id
    iso← = MC.StarIsomorphism.isMonoidIsomorphism wd2 wd1


  module nfp-iso-id
    {X}
    {Γ Δ : WRel X}
    (nfp : PP.NFProperty Γ)
    (open PP (Γ) renaming (•-ε-monoid to mi₁))
    (open PP (Δ) renaming (•-ε-monoid to mi₂))
    (iso : MonoidMorphisms.IsMonoidIsomorphism (Monoid.rawMonoid mi₁) (Monoid.rawMonoid mi₂) id)
    where
    open PP.NFProperty nfp

    iso' = iso-iso-id.iso← Γ Δ iso
    
    open MonoidMorphisms.IsMonoidIsomorphism iso renaming (injective to inje₁ ; ⟦⟧-cong to ⟦⟧-cong₁)
    open MonoidMorphisms.IsMonoidIsomorphism iso' renaming (injective to inje₂ ; ⟦⟧-cong to ⟦⟧-cong₂)

    nfp' : PP.NFProperty Δ
    nfp' = record { NF = NF ; nf = nf ; nf-cong = λ x → nf-cong (⟦⟧-cong₂ x) ; nf-injective = λ x → ⟦⟧-cong₁ (nf-injective x) }


  module nfp-iso
    {X Y : Set}
    {Γ : WRel X}
    {Δ : WRel Y}
    (nfp : PP.NFProperty Γ)
    (f : Word X -> Word Y)
    (open PP (Γ) renaming (•-ε-monoid to mi₁))
    (open PP (Δ) renaming (•-ε-monoid to mi₂))
    (iso : MonoidMorphisms.IsMonoidIsomorphism (Monoid.rawMonoid mi₁) (Monoid.rawMonoid mi₂) f)
    where
    open PP.NFProperty nfp

    open iso-iso Γ Δ f iso using (gg)
    iso' = iso-iso.iso← Γ Δ f iso
    
    open MonoidMorphisms.IsMonoidIsomorphism iso renaming (injective to inje₁ ; ⟦⟧-cong to ⟦⟧-cong₁)

    open MonoidMorphisms.IsMonoidIsomorphism iso' renaming (injective to inje₂ ; ⟦⟧-cong to ⟦⟧-cong₂)

    nfp' : PP.NFProperty Δ
    nfp' = record { NF = NF ; nf = nf ∘ gg ; nf-cong = λ x → nf-cong (⟦⟧-cong₂ x) ; nf-injective = λ x → inje₂ (nf-injective x) }

  module ∪-idem
    {X : Set}
    (Γ : WRel X)
    where
    module MI = MorphismId (Γ ∪ Γ) Γ

    open PB (Γ ∪ Γ) renaming (_===_ to _===₁ₒ_ ; _≈_ to _≈₁ₒ_) using ()
    open PB Γ renaming (_===_ to _===₂ₒ_ ; _≈_ to _≈₂ₒ_) using ()

    open PP (Γ ∪ Γ) renaming (•-ε-monoid to mi₁)
    open PP Γ renaming (•-ε-monoid to mi₂)
    module MMI = MonoidMorphisms (Monoid.rawMonoid mi₁) (Monoid.rawMonoid mi₂)

    wd1 : {w v : Word X} →  w ===₁ₒ v → id w ≈₂ₒ id v
    wd1 {w} {v} (left x) = _≈₂ₒ_.axiom x
    wd1 {w} {v} (right x) = _≈₂ₒ_.axiom x

    wd2 : {u t : Word X} → u ===₂ₒ t → id u ≈₁ₒ id t
    wd2 {w} {v} x = _≈₁ₒ_.axiom (left x)

    iso-idem : MMI.IsMonoidIsomorphism id
    iso-idem = MI.StarIsomorphism.isMonoidIsomorphism wd1 wd2


  module ∪-id
    {X : Set}
    (Γ : WRel X)
    where
    module MI = MorphismId Γ Γ

    open PB Γ renaming (_===_ to _===₁ₒ_ ; _≈_ to _≈₁ₒ_) using ()
    open PB Γ renaming (_===_ to _===₂ₒ_ ; _≈_ to _≈₂ₒ_) using ()

    open PP Γ renaming (•-ε-monoid to mi₁)
    open PP Γ renaming (•-ε-monoid to mi₂)
    module MMI = MonoidMorphisms (Monoid.rawMonoid mi₁) (Monoid.rawMonoid mi₂)

    wd1 : {w v : Word X} →  w ===₁ₒ v → id w ≈₂ₒ id v
    wd1 {w} {v} x = _≈_.axiom x

    wd2 : {u t : Word X} → u ===₂ₒ t → id u ≈₁ₒ id t
    wd2 {w} {v} x = _≈_.axiom x

    iso-id : MMI.IsMonoidIsomorphism id
    iso-id = MI.StarIsomorphism.isMonoidIsomorphism wd1 wd2


  module ∪-cong
    {X : Set}
    (Γ : WRel X)
    (Γ' : WRel X)
    (Δ : WRel X)
    (Δ' : WRel X)
    (open PP (Γ) renaming (•-ε-monoid to mi₁))
    (open PP (Δ) renaming (•-ε-monoid to mi₂))
    (open PP (Γ') renaming (•-ε-monoid to mi₁'))
    (open PP (Δ') renaming (•-ε-monoid to mi₂'))
    (open MonoidMorphisms (Monoid.rawMonoid mi₁) (Monoid.rawMonoid mi₁') renaming (IsMonoidIsomorphism to IsMonoidIsomorphism₁))
    (open MonoidMorphisms (Monoid.rawMonoid mi₂) (Monoid.rawMonoid mi₂') renaming (IsMonoidIsomorphism to IsMonoidIsomorphism₂))
    (iso-comp₁ : IsMonoidIsomorphism₁ id)
    (iso-comp₂ : IsMonoidIsomorphism₂ id)
    where

    ll = (Γ ∪ Δ)
    rr = (Γ' ∪ Δ')

    module MI = MorphismId ll rr

    open PB ll renaming (_===_ to _===₁ₒ_ ; _≈_ to _≈₁ₒ_) using ()
    open PB rr renaming (_===_ to _===₂ₒ_ ; _≈_ to _≈₂ₒ_) using ()

    open PP ll renaming (•-ε-monoid to mi₁ₕ)
    open PP rr renaming (•-ε-monoid to mi₂ₕ)
    module MMI = MonoidMorphisms (Monoid.rawMonoid mi₁ₕ) (Monoid.rawMonoid mi₂ₕ)

    open IsMonoidIsomorphism₁ iso-comp₁ renaming (injective to inje₁ ; ⟦⟧-cong to ⟦⟧-cong₁)
    open IsMonoidIsomorphism₂ iso-comp₂ renaming (injective to inje₂ ; ⟦⟧-cong to ⟦⟧-cong₂)
    wd1 : {w v : Word X} →  w ===₁ₒ v → id w ≈₂ₒ id v
    wd1 {w} {v} (left x) = (lefts (⟦⟧-cong₁ (_≈_.axiom x)))
      where
      open LeftRightCongruence-∪ Γ' Δ'

    wd1 {w} {v} (right x) = (rights (⟦⟧-cong₂ (_≈_.axiom x)))
      where
      open LeftRightCongruence-∪ Γ' Δ'


    wd2 : {w v : Word X} →  w ===₂ₒ v → id w ≈₁ₒ id v
    wd2 {w} {v} (left x) = lefts (inje₁ (_≈_.axiom x))
      where
      open LeftRightCongruence-∪ Γ Δ

    wd2 {w} {v} (right x) = rights ((inje₂ (_≈_.axiom x)))
      where
      open LeftRightCongruence-∪ Γ Δ

    iso-cong : MMI.IsMonoidIsomorphism id
    iso-cong = MI.StarIsomorphism.isMonoidIsomorphism wd1 wd2

  open import Algebra.Morphism.Construct.Composition as MCC


  open PP ((Γ₁'' ∪ Γ₃'') ∪ (Γ₂'' ∪ Γ₃'')) renaming (•-ε-monoid to mc1) using ()
  open PP ((Γ₁'' ∪ Γ₂'') ∪ Γ₃'') renaming (•-ε-monoid to mc1b) using ()
  open PB ((Γ₁'' ∪ Γ₂'') ∪ Γ₃'') renaming (_≈_ to _≈1_) using ()

  -- ((Γ₁'' ∪ Γ₃'') ∪ (Γ₂'' ∪ Γ₃'')) -> ((Γ₁'' ∪ Γ₃'') ∪ (Γ₃'' ∪ Γ₂'')) ->
  -- (Γ₁'' ∪ Γ₃'' ∪ (Γ₃'' ∪ Γ₂'')) -> (Γ₁'' ∪ (Γ₃'' ∪ Γ₃'') ∪ Γ₂'') -> (Γ₁'' ∪ Γ₃'' ∪ Γ₂'') ->
  -- (Γ₁'' ∪ Γ₂'' ∪ Γ₃'') -> ((Γ₁'' ∪ Γ₂'') ∪ Γ₃'')

  iso-3amal1 : MonoidMorphisms.IsMonoidIsomorphism (Monoid.rawMonoid mc1) (Monoid.rawMonoid mc1b) id
  iso-3amal1 =
    MCC.isMonoidIsomorphism _≈1_.trans (∪-cong.iso-cong (Γ₁'' ∪ Γ₃'') (Γ₁'' ∪ Γ₃'') (Γ₂'' ∪ Γ₃'') (Γ₃'' ∪ Γ₂'') (∪-id.iso-id (Γ₁'' ∪ Γ₃'')) (∪-comm.iso-comm Γ₂'' Γ₃''))
    (MCC.isMonoidIsomorphism _≈1_.trans (∪-assoc.iso-assoc Γ₁''  Γ₃'' (Γ₃'' ∪ Γ₂''))
    (MCC.isMonoidIsomorphism _≈1_.trans (∪-cong.iso-cong Γ₁'' Γ₁'' (Γ₃'' ∪ (Γ₃'' ∪ Γ₂'')) ((Γ₃'' ∪ Γ₃'') ∪ Γ₂'') (∪-id.iso-id Γ₁'') (iso-iso-id.iso← ((Γ₃'' ∪ Γ₃'') ∪ Γ₂'') (Γ₃'' ∪ (Γ₃'' ∪ Γ₂''))  (∪-assoc.iso-assoc Γ₃''  Γ₃'' Γ₂'')))
    (MCC.isMonoidIsomorphism _≈1_.trans (∪-cong.iso-cong Γ₁'' Γ₁'' ((Γ₃'' ∪ Γ₃'') ∪ Γ₂'') (Γ₃'' ∪ Γ₂'') (∪-id.iso-id Γ₁'') (∪-cong.iso-cong (Γ₃'' ∪ Γ₃'') Γ₃'' Γ₂'' Γ₂'' (∪-idem.iso-idem Γ₃'') (∪-id.iso-id Γ₂'') ))
    (MCC.isMonoidIsomorphism _≈1_.trans (∪-cong.iso-cong Γ₁'' Γ₁'' ((Γ₃'' ∪ Γ₂'')) (Γ₂'' ∪ Γ₃'') (∪-id.iso-id Γ₁'') (∪-comm.iso-comm Γ₃'' Γ₂'') ) (iso-iso-id.iso← ((Γ₁'' ∪ Γ₂'') ∪ Γ₃'') (Γ₁'' ∪ (Γ₂'' ∪ Γ₃''))  (∪-assoc.iso-assoc Γ₁''  Γ₂'' Γ₃'')))))) 


  open PP ((Γ₁'' ∪ Γ₂'') ∪ (Γ₁'' ∪ Γ₃'') ∪ (Γ₂'' ∪ Γ₃'')) renaming (•-ε-monoid to mc₁) using ()
  open PP (Γ₁'' ∪ Γ₂'' ∪ Γ₃'') renaming (•-ε-monoid to mc₂) using ()
  open PB ((Γ₁'' ∪ Γ₂'') ∪ (Γ₁'' ∪ Γ₂'') ∪ Γ₃'') renaming (_===_ to _===ₑ_ ; _≈_ to _≈ₑ_) using ()
  
  -- (Γ₁'' ∪ Γ₂'') ∪ (Γ₁'' ∪ Γ₃'') ∪ (Γ₂'' ∪ Γ₃'') -> (Γ₁'' ∪ Γ₂'') ∪ (Γ₁'' ∪ Γ₂'') ∪ Γ₃''
  -- -> ((Γ₁'' ∪ Γ₂'') ∪ (Γ₁'' ∪ Γ₂'')) ∪ Γ₃'' -> ((Γ₁'' ∪ Γ₂'')) ∪ Γ₃'' -> Γ₁'' ∪ Γ₂'' ∪ Γ₃''
  
  iso-3amal : MonoidMorphisms.IsMonoidIsomorphism (Monoid.rawMonoid mc₁) (Monoid.rawMonoid mc₂) id
  iso-3amal =
    MCC.isMonoidIsomorphism _≈_.trans ((∪-cong.iso-cong (Γ₁'' ∪ Γ₂'') (Γ₁'' ∪ Γ₂'') ((Γ₁'' ∪ Γ₃'') ∪ (Γ₂'' ∪ Γ₃'')) ((Γ₁'' ∪ Γ₂'') ∪ Γ₃'') (∪-id.iso-id (Γ₁'' ∪ Γ₂'')) (iso-3amal1)))
    (MCC.isMonoidIsomorphism trans (iso-iso-id.iso← (((Γ₁'' ∪ Γ₂'') ∪ (Γ₁'' ∪ Γ₂'')) ∪ Γ₃'') ((Γ₁'' ∪ Γ₂'') ∪ (Γ₁'' ∪ Γ₂'') ∪ Γ₃'') (∪-assoc.iso-assoc ((Γ₁'' ∪ Γ₂'')) (Γ₁'' ∪ Γ₂'') Γ₃''))
    (isMonoidIsomorphism trans (∪-cong.iso-cong (((Γ₁'' ∪ Γ₂'') ∪ (Γ₁'' ∪ Γ₂''))) (((Γ₁'' ∪ Γ₂''))) Γ₃'' Γ₃'' (∪-idem.iso-idem (Γ₁'' ∪ Γ₂'')) (∪-id.iso-id Γ₃'')) (∪-assoc.iso-assoc Γ₁'' Γ₂'' Γ₃''))) 
    where
    open PP ((Γ₁'' ∪ Γ₂'') ∪ (Γ₁'' ∪ Γ₃'') ∪ (Γ₂'' ∪ Γ₃''))  renaming (•-ε-monoid to mi₁)


  open PP (Γ₁'' ∪ Γ₂'' ∪ Γ₃'') renaming (•-ε-monoid to mc₇) using ()


  3amal : WRel (X ⊎ Y ⊎ Z)
  3amal = Γ₁'' ∪ Γ₂'' ∪ Γ₃''
