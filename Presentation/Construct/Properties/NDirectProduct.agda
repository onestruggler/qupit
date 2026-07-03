------------------------------------------------------------------------
-- Presentations of groups
--
-- Normal-form properties for N-fold direct products of group presentations.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}

open import Relation.Binary using (Rel ; REL)

open import Level using (0ℓ)
open import Data.Product using (_,_ ; _×_ ; map ; proj₁ ; proj₂ ; Σ ; ∃ ; ∃-syntax)
import Data.Product.Relation.Binary.Pointwise.NonDependent as PW
open import Data.Nat using (ℕ ; suc ; zero)
open import Data.Sum using (_⊎_ ; inj₁ ; inj₂)
open import Function using (_∘_ ; _∘₂_)
open import Relation.Binary.PropositionalEquality using (_≡_ ; inspect ; setoid ; module ≡-Reasoning) renaming ([_] to [_]')
import Relation.Binary.PropositionalEquality as Eq

import Relation.Binary.Reasoning.Setoid as SR

open import Word.Base
open import Word.Properties
import Presentation.Horizontal-Syntactics as PB
import Presentation.Properties as PP
open import Presentation.Properties

open import Presentation.Reidemeister-Schreier
open import Presentation.Construct.Base
import Presentation.Construct.Properties.DirectProduct as DP
import Presentation.Groups.Trivial as Trivial
open import Notations

module Presentation.Construct.Properties.NDirectProduct
  {A : Set}
  (Γ : WRel A)
  where

open PB Γ renaming (_===_ to _===₁_ ; _≈_ to _≈₁_) using ()
open PP Γ renaming (•-ε-monoid to m₁ ; word-setoid to word-setoid₁) using ()

nfp : (n : ℕ) → NFProperty Γ → NFProperty (Γ ⊕^ n)
nfp zero nfpg = Trivial.P1.nfp
nfp (₁₊ zero) nfpg = nfpg
nfp (₂₊ n) nfpg = DP.NFP.nfp Γ (Γ ⊕^ ₁₊ n) nfpg (nfp (₁₊ n) nfpg)

nfp' : (n : ℕ) → NFProperty' Γ → NFProperty' (Γ ⊕^ n)
nfp' zero nfp'g = Trivial.P1.nfp'
nfp' (₁₊ zero) nfp'g = nfp'g
nfp' (₂₊ n) nfp'g = DP.NFP'.nfp' Γ (Γ ⊕^ ₁₊ n) nfp'g (nfp' (₁₊ n) nfp'g)
