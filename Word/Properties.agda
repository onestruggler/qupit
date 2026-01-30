{-# OPTIONS --safe #-}
module Word.Properties where

open import Level using (0ℓ)
open import Relation.Binary using (IsEquivalence ; Setoid ; Rel)
open import Data.Product using (_,_)
open import Relation.Binary.Morphism.Definitions using (Homomorphic₂)
open import Relation.Binary.PropositionalEquality as Eq renaming ([_] to [_]') using ( _≡_ ; inspect ; _≗_ )

import Relation.Binary.Reasoning.Setoid as Eqv
import Relation.Binary.Reasoning.Setoid as SR

open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂)
import Data.Product.Relation.Binary.Pointwise.NonDependent as PW
open import Data.Nat using (ℕ ; suc ; zero)
open import Function using (_∘_ ; id)

open import Word.Base

private
  variable
    A B C X Y Z : Set

wmap-∘ : {g : B -> C} -> {f : A -> B} -> wmap (g ∘ f) ≗ wmap g ∘ wmap f
wmap-∘ {g} {f} [ x ]ʷ = Eq.refl
wmap-∘ {g} {f} ε = Eq.refl
wmap-∘ {g} {f} (w • w₁) = Eq.cong₂ _•_ (wmap-∘ w) (wmap-∘ w₁)

wconcatmap-[-]ʷ : (wconcat {A = A} ∘ wmap ([_]ʷ)) ≗ id
wconcatmap-[-]ʷ [ x ]ʷ = Eq.refl
wconcatmap-[-]ʷ ε = Eq.refl
wconcatmap-[-]ʷ (w • w₁) rewrite wconcatmap-[-]ʷ w | wconcatmap-[-]ʷ w₁ = Eq.refl

wconcatmap-[f]ʷ : {f : A -> B} -> (wconcat ∘ wmap ([_]ʷ ∘ f)) ≗ wmap f
wconcatmap-[f]ʷ {f} [ x ]ʷ = Eq.refl
wconcatmap-[f]ʷ {f} ε = Eq.refl
wconcatmap-[f]ʷ {f} (ws • ws₁) = Eq.cong₂ _•_ (wconcatmap-[f]ʷ ws) (wconcatmap-[f]ʷ ws₁)

wconcat-wmap : {f : A -> B} -> wconcat ∘ (wmap (wmap f)) ≗ wmap f ∘ wconcat
wconcat-wmap {f} [ ws ]ʷ = Eq.refl
wconcat-wmap {f} ε = Eq.refl
wconcat-wmap {f} (ws • ws₁) = Eq.cong₂ _•_ (wconcat-wmap ws) (wconcat-wmap ws₁)


open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Nullary using (yes ; no)


≡-dec : DecidableEquality B -> DecidableEquality (Word B)
≡-dec deceqB [ x ]ʷ [ x₁ ]ʷ with deceqB x x₁
... | yes p = yes (Eq.cong [_]ʷ p)
... | no np = no (λ { Eq.refl → np Eq.refl})
≡-dec deceqB [ x ]ʷ ε = no (λ {()})
≡-dec deceqB [ x ]ʷ (y • y₁) = no (λ {()})
≡-dec deceqB ε [ x ]ʷ = no (λ {()})
≡-dec deceqB ε ε = yes Eq.refl
≡-dec deceqB ε (y • y₁) = no (λ {()})
≡-dec deceqB (x • x₁) [ x₂ ]ʷ = no (λ {()})
≡-dec deceqB (x • x₁) ε = no (λ {()})
≡-dec deceqB (x • x₁) (y • y₁) with ≡-dec deceqB x y | ≡-dec deceqB x₁ y₁
... | yes p | yes p' = yes (Eq.cong₂ _•_ p p')
... | yes p | no np' = no (λ { Eq.refl → np' Eq.refl})
... | no np | yes p' = no (λ { Eq.refl → np Eq.refl})
... | no np | no np' = no (λ { Eq.refl → np' Eq.refl})

------------------------------------------------------------------------
-- DEPRECATED
------------------------------------------------------------------------
-- Please use the new names as continuing support for the old names is
-- not guaranteed.

lemma-* : {f : A -> B} -> (w : Word A) -> (([_]ʷ ∘ f) *) w ≡ wmap f w
lemma-* = wconcatmap-[f]ʷ

lemma-*-∘ : (f : A -> Word B) -> (g : B -> C) -> (w : Word A) -> ((wmap g ∘ f) *) w ≡ (wmap g ∘ (f *)) w
lemma-*-∘ f g [ x ]ʷ = Eq.refl
lemma-*-∘ f g ε = Eq.refl
lemma-*-∘ f g (w • w₁) = Eq.cong₂ _•_ (lemma-*-∘ f g w) (lemma-*-∘ f g w₁)

lemma-*-∘-∘ : (g : Z -> A) -> (h : Y -> Z) (w : Word Y) -> (([_]ʷ ∘ g ∘ h) *) w ≡ wmap g ((([_]ʷ ∘ h) *) w)
lemma-*-∘-∘ g h w = Eq.trans (wconcatmap-[f]ʷ w) (Eq.trans (wmap-∘ w) (Eq.cong (wmap g) (Eq.sym (wconcatmap-[f]ʷ w))))
