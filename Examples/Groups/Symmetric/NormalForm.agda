------------------------------------------------------------------------
-- Presentations of groups
--
-- Symmetric groups Sₙ and their normal form via coset enumeration
-- Adapted to the Circuit / Lift-Relation framework
------------------------------------------------------------------------

{-# OPTIONS --safe #-}

open import Level using (0ℓ)

open import Relation.Binary using (Rel ; Setoid)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Binary.Morphism.Definitions using (Homomorphic₂)
open import Relation.Binary.PropositionalEquality using (_≡_ ; inspect ; module ≡-Reasoning) renaming ([_] to [_]ₑ)
import Relation.Binary.Reasoning.Setoid as SR
import Relation.Binary.PropositionalEquality as Eq
open import Relation.Nullary.Decidable using (yes ; no)

open import Function using (_∘_)
open import Function.Definitions using (Injective)

open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂ ; map₁)
open import Data.Product.Relation.Binary.Pointwise.NonDependent using (≡×≡⇒≡ ; Pointwise ; ≡⇒≡×≡)
open import Data.Product.Relation.Binary.Pointwise.NonDependent as PW
open import Data.Nat using (ℕ ; zero ; suc ; 2+)
open import Data.Fin using (Fin) renaming (zero to fzero ; suc to fsuc)
import Data.Fin.Properties as FP
open import Data.Unit using (⊤ ; tt)

open import Word.Base
open import Word.Properties
import Presentation.Base as PB
import Presentation.Properties as PP
open PP using (NFProperty ; NFProperty')

import Presentation.CosetNF as CA
import Presentation.Reidemeister-Schreier as RS
module RSF = RS.Star-Injective-Full.Reidemeister-Schreier-Full
open import Presentation.GroupLike

open import Notations
import Presentation.Vertical-Syntactics
import Presentation.Normalization

module Examples.Groups.Symmetric.NormalForm where

private variable
  n :  ℕ
  
open import Examples.Groups.Symmetric.Syntactics

------------------------------------------------------------------------
-- Coset type

infixr 10 σ•_
data C : ℕ → Set where
  ε   : C n
  σ•_ : C n → C (₁₊ n)

------------------------------------------------------------------------
-- Section map: C n → Circuit (₁₊ n)
-- (shifted by 1 because gate₂ σ-gate needs ≥ 2 wires)

[_]ᶜ : C n → Circuit (₁₊ n)
[_]ᶜ         ε      = ε
[_]ᶜ {₁₊ n} (σ• c) = σ • ([ c ]ᶜ ↑)

------------------------------------------------------------------------
-- Normal-form type

NF : ℕ → Set
NF 0       = ⊤
NF 1       = ⊤
NF (₂₊ n)  = NF (₁₊ n) × C (₁₊ n)

------------------------------------------------------------------------
-- Decidable equality

lemma-daux : ∀ {n} x y → σ•_ {n} x ≡ σ• y → x ≡ y
lemma-daux x y Eq.refl = Eq.refl

deceqC : DecidableEquality (C n)
deceqC {zero}  ε      ε       = yes Eq.refl
deceqC {₁₊ n} ε      ε       = yes Eq.refl
deceqC {₁₊ n} ε      (σ• y)  = no (λ ())
deceqC {₁₊ n} (σ• x) ε       = no (λ ())
deceqC {₁₊ n} (σ• x) (σ• y) with deceqC x y
... | yes p  = yes (Eq.cong σ•_ p)
... | no  np = no (λ { eq → np (lemma-daux _ _ eq) })

deceq : DecidableEquality (NF n)
deceq {zero}  tt     tt     = yes Eq.refl
deceq {₁₊ zero} tt  tt     = yes Eq.refl
deceq {₂₊ n} (a , b) (a' , b') with deceq a a' | deceqC b b'
... | yes p1 | yes p2 = yes (≡×≡⇒≡ (p1 , p2))
... | yes p1 | no  p2 = no (λ { x → p2 (proj₂ (≡⇒≡×≡ x)) })
... | no  p1 | yes p2 = no (λ { x → p1 (proj₁ (≡⇒≡×≡ x)) })
... | no  p1 | no  p2 = no (λ { x → p2 (proj₂ (≡⇒≡×≡ x)) })


inv-nf : {n : ℕ} → NF n → Circuit n
inv-nf {zero}    _       = ε
inv-nf {(₁₊ zero)} _    = ε
inv-nf {(₂₊ n)} (l , r) = inv-nf {(₁₊ n)} l ↑ • [_]ᶜ r
