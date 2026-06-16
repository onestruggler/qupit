{-# OPTIONS  --safe #-}
open import Relation.Binary using (Rel ; REL)

open import Level using (0ℓ)
open import Data.Product using (_,_ ; _×_ ; map ; proj₁ ; proj₂ ; Σ ; ∃ ; ∃-syntax)
import Data.Product.Relation.Binary.Pointwise.NonDependent as PW
open import Data.Sum using (_⊎_ ; inj₁ ; inj₂)
open import Data.Nat using (ℕ ; zero ; suc)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤ ; tt)
open import Function using (_∘_ ; _∘₂_)
open import Relation.Binary.PropositionalEquality using (_≡_ ; inspect ; setoid ; module ≡-Reasoning) renaming ([_] to [_]')
import Relation.Binary.PropositionalEquality as Eq

import Relation.Binary.Reasoning.Setoid as SR

open import Word.Base
open import Word.Properties
open import Presentation.Base
open import Presentation.Construct.Base
open import Presentation.Reidemeister-Schreier

import Presentation.Base as PB
import Presentation.Properties as PP


module Presentation.Construct.Properties where

lemma-[w^n]ₗ=[w]ₗ^n : ∀ {A B : Set} (w : Word A) (n : ℕ) -> [_]ₗ {B = B} (w ^ n) ≡ [ w ]ₗ ^ n
lemma-[w^n]ₗ=[w]ₗ^n {A} {B} w zero = Eq.refl
lemma-[w^n]ₗ=[w]ₗ^n {A} {B} w (suc zero) = Eq.refl
lemma-[w^n]ₗ=[w]ₗ^n {A} {B} w (suc (suc n)) = Eq.cong₂ _•_ Eq.refl (lemma-[w^n]ₗ=[w]ₗ^n {A} {B} w (suc n))

lemma-[w^n]ᵣ=[w]ᵣ^n : ∀ {A B : Set} (w : Word B) (n : ℕ) -> [_]ᵣ {A = A} (w ^ n) ≡ [ w ]ᵣ ^ n
lemma-[w^n]ᵣ=[w]ᵣ^n {A} {B} w zero = Eq.refl
lemma-[w^n]ᵣ=[w]ᵣ^n {A} {B} w (suc zero) = Eq.refl
lemma-[w^n]ᵣ=[w]ᵣ^n {A} {B} w (suc (suc n)) = Eq.cong₂ _•_ Eq.refl (lemma-[w^n]ᵣ=[w]ᵣ^n {A} {B} w (suc n))

