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
import Presentation.Horizontal-Syntactics as PB
import Presentation.Properties as PP
open PP using (NFProperty ; NFProperty')

import Presentation.CosetNF as CA
import Presentation.Reidemeister-Schreier as RS
module RSF = RS.Star-Injective-Full.Reidemeister-Schreier-Full
open import Presentation.GroupLike

open import Notations
import Presentation.Vertical-Syntactics
import Presentation.Normalization

module Examples.Groups.Symmetric.Normalization where

private variable
  n :  ℕ
  
open import Examples.Groups.Symmetric.Syntactics

------------------------------------------------------------------------
-- Coset type  (same shape as in Presentation.Groups.Sn)

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

------------------------------------------------------------------------
-- Right coset action
--
-- ract : C (₁₊ n) → Gen (₂₊ n) → Circuit (₁₊ n) × C (₁₊ n)

ract : C (₁₊ n) → Gen (₂₊ n) → Circuit (₁₊ n) × C (₁₊ n)
ract {n}     ε         σ-gen       = ε , σ• ε
ract {n}     (σ• ε)    σ-gen       = ε , ε
ract {₁₊ n}  (σ• σ• c) σ-gen       = (σ {n = n}) , σ• σ• c
ract {n}     ε         (g ↥)   = [ g ]ʷ , ε
ract {0}     (σ• ε)    (gate₁ () ↥)
ract {0}     (σ• ε)    ((() ↥) ↥)
ract {₁₊ n}  (σ• c)    (g ↥)   = proj₁ (ract {n} c g) ↑ , σ• (proj₂ (ract {n} c g))

racts : C (₁₊ n) → Circuit (₂₊ n) → Circuit (₁₊ n) × C (₁₊ n)
racts {n} = ract {n} **

------------------------------------------------------------------------
-- lemma-ract: [c]ᶜ • [b]ʷ ≈ b'.proj₁ ↑ • [c']ᶜ  where (b', c') = ract c b

lemma-ract : ∀ {n} c b →
  let P = _VRel,_===_ (₂₊ n)
  in let (b' , c') = ract {n} c b
  in PB._≈_ P ([ c ]ᶜ • [ b ]ʷ) (b' ↑ • [ c' ]ᶜ)
lemma-ract {n} ε σ-gen = PB._≈_.cong PB._≈_.refl (PB._≈_.sym PB._≈_.right-unit)
  where P = _VRel,_===_ (₂₊ n) ; open PB P
lemma-ract {n} (σ• ε) σ-gen =
  PB._≈_.trans (PB._≈_.cong PB._≈_.right-unit PB._≈_.refl)
               (PB._≈_.trans (PB._≈_.axiom (srel order)) (PB._≈_.sym PB._≈_.right-unit))
  where P = _VRel,_===_ (₂₊ n) ; open PB P ; open PP P
lemma-ract {n} ε (g ↥) =
  PB._≈_.trans PB._≈_.left-unit (PB._≈_.sym PB._≈_.right-unit)
  where P = _VRel,_===_ (₂₊ n) ; open PB P
lemma-ract {₁₊ n} (σ• σ• c) σ-gen = begin
  ([_]ᶜ (σ• σ• c) • σ) ≈⟨ _≈_.assoc ⟩
  σ • ([_]ᶜ (σ• c) ↑) • σ ≡⟨ Eq.refl ⟩
  σ • (σ ↑ • ([_]ᶜ c ↑ ↑)) • σ ≈⟨ _≈_.cong _≈_.refl _≈_.assoc ⟩
  σ • σ ↑ • ([_]ᶜ c ↑ ↑) • σ ≈⟨ cong refl (cong refl (lemma-comm ([_]ᶜ c))) ⟩
  σ • σ ↑ • σ • ([_]ᶜ c ↑ ↑) ≈⟨ _≈_.sym (_≈_.cong _≈_.refl _≈_.assoc) ⟩
  σ • (σ ↑ • σ) • ([_]ᶜ c ↑ ↑) ≈⟨ _≈_.sym _≈_.assoc ⟩
  (σ • (σ ↑ • σ)) • ([_]ᶜ c ↑ ↑) ≈⟨ cong (_≈_.axiom (srel yang-baxter)) refl ⟩
  (σ ↑ • σ • σ ↑) • ([_]ᶜ c ↑ ↑) ≈⟨ _≈_.trans _≈_.assoc (_≈_.cong _≈_.refl _≈_.assoc) ⟩
  σ ↑ • σ • σ ↑ • ([_]ᶜ c ↑ ↑) ≡⟨ Eq.refl ⟩
  σ ↑ • (σ • ([_]ᶜ (σ• c) ↑)) ∎
  where
  P = _VRel,_===_ (₃₊ n)
  open PB P
  open PP P
  open SR word-setoid
lemma-ract {0} (σ• c) ((gate₁ ()) ↥)
lemma-ract {0} (σ• c) (((() ↥)) ↥)
lemma-ract {₁₊ n} (σ• ε) (b@σ-gen ↥) with lemma-ract {n} ε b
... | ih = begin
  [_]ᶜ (σ• ε) • [ b ↥ ]ʷ ≈⟨ _≈_.assoc ⟩
  σ • (ε • [ b ]ʷ) ↑ ≈⟨ cong refl ([⇑]lift (ε • [ b ]ʷ) (b0 ↑ • [_]ᶜ c0) ih) ⟩
  σ • (b0 ↑ • [_]ᶜ c0) ↑ ≡⟨ Eq.refl ⟩
  σ • (b0 ↑ ↑ • [_]ᶜ c0 ↑) ≈⟨ _≈_.sym _≈_.assoc ⟩
  (σ • b0 ↑ ↑) • [_]ᶜ c0 ↑ ≈⟨ cong (PB._≈_.sym (lemma-comm b0)) refl ⟩
  (b0 ↑ ↑ • σ) • [_]ᶜ c0 ↑ ≈⟨ _≈_.assoc ⟩
  b0 ↑ ↑ • [_]ᶜ (σ• c0) ∎
  where
  P0 = _VRel,_===_ (₂₊ n)
  P  = _VRel,_===_ (₃₊ n)
  open PB P
  open PP P
  open SR word-setoid
  b0 = proj₁ (ract {n} ε b)
  c0 = proj₂ (ract {n} ε b)
  [⇑]lift : ∀ {m} (w v : Circuit m) → PB._≈_ (_VRel,_===_ m) w v → PB._≈_ (_VRel,_===_  (₁₊ m)) (w ↑) (v ↑)
  [⇑]lift w v eq = lemma-cong↑ w v eq
lemma-ract {₁₊ n} (σ• ε) (b@(b' ↥) ↥) with lemma-ract {n} ε b
... | ih = begin
  [_]ᶜ (σ• ε) • [ b ↥ ]ʷ ≈⟨ _≈_.assoc ⟩
  σ • (ε • [ b ]ʷ) ↑ ≈⟨ cong refl ([⇑]lift (ε • [ b ]ʷ) (b0 ↑ • [_]ᶜ c0) ih) ⟩
  σ • (b0 ↑ • [_]ᶜ c0) ↑ ≡⟨ Eq.refl ⟩
  σ • (b0 ↑ ↑ • [_]ᶜ c0 ↑) ≈⟨ _≈_.sym _≈_.assoc ⟩
  (σ • b0 ↑ ↑) • [_]ᶜ c0 ↑ ≈⟨ cong (PB._≈_.sym (lemma-comm b0)) refl ⟩
  (b0 ↑ ↑ • σ) • [_]ᶜ c0 ↑ ≈⟨ _≈_.assoc ⟩
  b0 ↑ ↑ • [_]ᶜ (σ• c0) ∎
  where
  P0 = _VRel,_===_ (₂₊ n)
  P  = _VRel,_===_ (₃₊ n)
  open PB P
  open PP P
  open SR word-setoid
  b0 = proj₁ (ract {n} ε b)
  c0 = proj₂ (ract {n} ε b)
  [⇑]lift : ∀ {m} (w v : Circuit m) → PB._≈_ (_VRel,_===_ m) w v → PB._≈_ (_VRel,_===_ (₁₊ m)) (w ↑) (v ↑)
  [⇑]lift w v eq = lemma-cong↑ w v eq
lemma-ract {₁₊ n} (σ• σ• c) (b@σ-gen ↥) with lemma-ract {n} (σ• c) b
... | ih = begin
  [_]ᶜ (σ• σ• c) • [ b ↥ ]ʷ ≈⟨ _≈_.assoc ⟩
  σ • ([_]ᶜ (σ• c) • [ b ]ʷ) ↑ ≈⟨ cong refl ([⇑]lift _ _ ih) ⟩
  σ • (b0 ↑ • [_]ᶜ c0) ↑ ≡⟨ Eq.refl ⟩
  σ • (b0 ↑ ↑ • [_]ᶜ c0 ↑) ≈⟨ _≈_.sym _≈_.assoc ⟩
  (σ • b0 ↑ ↑) • [_]ᶜ c0 ↑ ≈⟨ cong (PB._≈_.sym (lemma-comm b0)) refl ⟩
  (b0 ↑ ↑ • σ) • [_]ᶜ c0 ↑ ≈⟨ _≈_.assoc ⟩
  b0 ↑ ↑ • [_]ᶜ (σ• c0) ∎
  where
  P  = _VRel,_===_ (₃₊ n)
  open PB P
  open PP P
  open SR word-setoid
  b0 = proj₁ (ract {n} (σ• c) b)
  c0 = proj₂ (ract {n} (σ• c) b)
  [⇑]lift : ∀ {m} (w v : Circuit m) → PB._≈_ (_VRel,_===_ m) w v → PB._≈_ (_VRel,_===_ (₁₊ m)) (w ↑) (v ↑)
  [⇑]lift w v eq = lemma-cong↑ w v eq
lemma-ract {₁₊ n} (σ• σ• c) (b@(bb ↥) ↥) with lemma-ract {n} (σ• c) b
... | ih = begin
  [_]ᶜ (σ• σ• c) • [ b ↥ ]ʷ ≈⟨ _≈_.assoc ⟩
  σ • ([_]ᶜ (σ• c) • [ b ]ʷ) ↑ ≈⟨ cong refl ([⇑]lift _ _ ih) ⟩
  σ • (b0 ↑ • [_]ᶜ c0) ↑ ≡⟨ Eq.refl ⟩
  σ • (b0 ↑ ↑ • [_]ᶜ c0 ↑) ≈⟨ _≈_.sym _≈_.assoc ⟩
  (σ • b0 ↑ ↑) • [_]ᶜ c0 ↑ ≈⟨ cong (PB._≈_.sym (lemma-comm b0)) refl ⟩
  (b0 ↑ ↑ • σ) • [_]ᶜ c0 ↑ ≈⟨ _≈_.assoc ⟩
  b0 ↑ ↑ • [_]ᶜ (σ• c0) ∎
  where
  P  = _VRel,_===_ (₃₊ n)
  open PB P
  open PP P
  open SR word-setoid
  b0 = proj₁ (ract {n} (σ• c) b)
  c0 = proj₂ (ract {n} (σ• c) b)
  [⇑]lift : ∀ {m} (w v : Circuit m) → PB._≈_ (_VRel,_===_ m) w v → PB._≈_ (_VRel,_===_ (₁₊ m)) (w ↑) (v ↑)
  [⇑]lift w v eq = lemma-cong↑ w v eq

------------------------------------------------------------------------
-- lemma-racts: extends lemma-ract to words

lemma-racts : ∀ {n} c bs →
  let P : WRel (Gen _)
      P = _VRel,_===_ (₂₊ n)
  in let (bs' , c') = racts {n} c bs
  in PB._≈_ P ([_]ᶜ c • bs) (bs' ↑ • [_]ᶜ c')
lemma-racts {n} c [ x ]ʷ = lemma-ract c x
lemma-racts {n} c ε = PB._≈_.trans PB._≈_.right-unit (PB._≈_.sym PB._≈_.left-unit)
  where P = _VRel,_===_ (₂₊ n) ; open PB P
lemma-racts {n} c (bs • as) with racts c bs | inspect (racts c) bs | lemma-racts c bs
... | (bs' , c') | [ eq1 ]ₑ | ih1 with racts c' as | inspect (racts c') as | lemma-racts c' as
... | (as' , c'') | [ eq2 ]ₑ | ih2 = begin
  [_]ᶜ c • (bs • as) ≈⟨ _≈_.sym _≈_.assoc ⟩
  ([_]ᶜ c • bs) • as ≈⟨ _≈_.cong ih1 _≈_.refl ⟩
  (bs' ↑ • [_]ᶜ c') • as ≈⟨ _≈_.assoc ⟩
  bs' ↑ • [_]ᶜ c' • as ≈⟨ _≈_.cong _≈_.refl ih2 ⟩
  bs' ↑ • as' ↑ • [_]ᶜ c'' ≈⟨ _≈_.sym _≈_.assoc ⟩
  (bs' • as') ↑ • [_]ᶜ c'' ∎
  where
  P = _VRel,_===_ (₂₊ n)
  open PB P
  open PP P
  open SR word-setoid

------------------------------------------------------------------------
-- nf-of, nf-of2

nf-of : Circuit n → NF n
nf-of {0}     w = tt
nf-of {1}     w = tt
nf-of {₂₊ n}   = map₁ (nf-of {₁₊ n}) ∘ racts {n} ε

nf-of2 : Circuit (₂₊ n) → Circuit (₁₊ n) × C (₁₊ n)
nf-of2 {n} = racts {n} ε

------------------------------------------------------------------------
-- ≋  : pointwise relation on (Circuit (₁₊ n) × C (₁₊ n))

infix 4 _≋_
_≋_ : Rel (Circuit (₁₊ n) × C (₁₊ n)) 0ℓ
_≋_ {n} = let _≈₀_ = PB._≈_ (_VRel,_===_ (₁₊ n)) in Pointwise _≈₀_ (_≡_ {A = C (₁₊ n)})

------------------------------------------------------------------------
-- ⁻¹[⇑]-gen': inverse of the generator embedding

⁻¹[⇑]-gen' : let _⊛_ = ract ** in ∀ (x : Gen (₁₊ n)) →
  ([ x ]ʷ , ε) ≋ ε ⊛ [ x ↥ ]ʷ
⁻¹[⇑]-gen' {n} x = PB._≈_.refl , Eq.refl

------------------------------------------------------------------------
-- Auxiliary ract-computation lemmas (all Eq.refl by definition)

lemma-ract-suc : ∀ {n} w → racts {n} ε (w ↑) ≡ (w , ε)
lemma-ract-suc {n} [ x ]ʷ = Eq.refl
lemma-ract-suc {n} ε       = Eq.refl
lemma-ract-suc {n} (w • v) with lemma-ract-suc {n} w
... | ih with lemma-ract-suc {n} v
... | ih' with racts ε (w ↑)
... | (w' , ew) rewrite Eq.cong proj₁ ih | Eq.cong proj₂ ih
                       | Eq.cong proj₁ ih' | Eq.cong proj₂ ih'
              with racts ε (v ↑)
... | (v' , ev) = begin w • v , ε ≡⟨ Eq.refl ⟩ (w • v , ε) ∎
  where open ≡-Reasoning

lemma-ract-suc' : ∀ {n} w → (ract {n} **) ε (w ↑) ≡ (w , ε)
lemma-ract-suc' {n} [ x ]ʷ = Eq.refl
lemma-ract-suc' {n} ε       = Eq.refl
lemma-ract-suc' {n} (w • v) with lemma-ract-suc' {n} w
... | ih with lemma-ract-suc' {n} v
... | ih' with racts ε (w ↑)
... | (w' , ew) rewrite Eq.cong proj₁ ih | Eq.cong proj₂ ih
                       | Eq.cong proj₁ ih' | Eq.cong proj₂ ih'
              with racts ε (v ↑)
... | (v' , ev) = begin w • v , ε ≡⟨ Eq.refl ⟩ (w • v , ε) ∎
  where open ≡-Reasoning

lemma-ract-suc'' : ∀ {n} w → (ract {₂₊ n} **) (σ• ε) (w ↑ ↑ ↑) ≡ (w ↑ ↑ , σ• ε)
lemma-ract-suc'' {n} [ x ]ʷ = Eq.refl
lemma-ract-suc'' {n} ε       = Eq.refl
lemma-ract-suc'' {n} (w • v) with lemma-ract-suc'' {n} w
... | ih with lemma-ract-suc'' {n} v
... | ih' with racts ε (w ↑)
... | (w' , ew) rewrite Eq.cong proj₁ ih | Eq.cong proj₂ ih
                       | Eq.cong proj₁ ih' | Eq.cong proj₂ ih'
              with racts ε (v ↑)
... | (v' , ev) = begin w ↑ ↑ • v ↑ ↑ , σ• ε ≡⟨ Eq.refl ⟩ (w ↑ ↑ • v ↑ ↑ , σ• ε) ∎
  where open ≡-Reasoning

-- Generalisation of lemma-ract-suc'' that works for w : Circuit n for
-- any n.  The auxiliary sub-computation is racts ε (w ↑ ↑) rather than
-- racts ε (w ↑) because case 7 contributes ract {n} ε (x ↥ ↥), not
-- ract {n} ε (x ↥), when the outer implicit is ₁₊ n.
lemma-ract-suc''' : ∀ {n} (w : Circuit n) → (ract {₁₊ n} **) (σ• ε) (w ↑ ↑ ↑) ≡ (w ↑ ↑ , σ• ε)
lemma-ract-suc''' {n} [ x ]ʷ = Eq.refl
lemma-ract-suc''' {n} ε       = Eq.refl
lemma-ract-suc''' {n} (w • v) with lemma-ract-suc''' {n} w
... | ih with lemma-ract-suc''' {n} v
... | ih' with racts ε (w ↑ ↑)
... | (w'' , ew) rewrite Eq.cong proj₁ ih | Eq.cong proj₂ ih
                        | Eq.cong proj₁ ih' | Eq.cong proj₂ ih'
               with racts ε (v ↑ ↑)
... | (v'' , ev) = begin w ↑ ↑ • v ↑ ↑ , σ• ε ≡⟨ Eq.refl ⟩ (w ↑ ↑ • v ↑ ↑ , σ• ε) ∎
  where open ≡-Reasoning

lemma-ract-σ•σ•σ : ∀ {n} (c : C n) →
  racts (σ• σ• c) σ ≡ (σ , σ• σ• c)
lemma-ract-σ•σ•σ {n} c = Eq.refl

lemma-ract-σ•1 : ∀ {n} (c : C (₁₊ n)) (g : Gen (₂₊ n)) →
  let (b' , c') = ract {n} c g
  in ract (σ• c) (g ↥) ≡ (b' ↑ , σ• c')
lemma-ract-σ•1 {n} ε       σ-gen   = Eq.refl
lemma-ract-σ•1 {n} ε       (g' ↥)  = Eq.refl
lemma-ract-σ•1 {n} (σ• c') σ-gen   = Eq.refl
lemma-ract-σ•1 {n} (σ• c') (g' ↥)  = Eq.refl

lemma-ract-σ•1s : ∀ {n} (c : C (₁₊ n)) w →
  let (w' , c') = (ract {n} **) c w
  in (ract {₁₊ n} **) (σ• c) (w ↑) ≡ (w' ↑ , σ• c')
lemma-ract-σ•1s {n} c [ x ]ʷ = lemma-ract-σ•1 c x
lemma-ract-σ•1s {n} c ε       = Eq.refl
lemma-ract-σ•1s {n} c (w • v)
  with lemma-ract-σ•1s c w | (ract **) c w | inspect ((ract **) c) w
... | ih1 | w' , c0 | [ eq1 ]ₑ rewrite ih1 | eq1
  with lemma-ract-σ•1s c0 v | (ract **) c0 v | inspect ((ract **) c0) v
... | ih2 | v' , c1 | [ eq2 ]ₑ rewrite eq2 | Eq.cong proj₁ ih2 | Eq.cong proj₂ ih2 = Eq.refl
  where open ≡-Reasoning

-- ract {n} (σ• ε) ((g ↥) ↥) ≡ ([g ↥]ʷ , σ• ε)
-- Case 7 needs implicit ≥ 1; n=0 is vacuous since Gen 0 = ∅
lemma-ract-σ•ε-gg↥ : ∀ {n} (g : Gen n) → ract {n} (σ• ε) ((g ↥) ↥) ≡ ([ g ↥ ]ʷ , σ• ε)
lemma-ract-σ•ε-gg↥ {zero}  ()
lemma-ract-σ•ε-gg↥ {₁₊ n} g = Eq.refl

------------------------------------------------------------------------
-- ⁻¹[⇑]-wd'': coset action respects raw relations

⁻¹[⇑]-wd'' : ∀ {n} →
  let _⊛_ = ract ** in
  let _===_ = _VRel,_===_ (₂₊ n) in
  ∀ (c : C (₁₊ n)){u t : Circuit (₂₊ n)} → u === t → c ⊛ u ≋ c ⊛ t

-- ε coset
⁻¹[⇑]-wd'' {n} ε (srel order)
  = PB._≈_.left-unit , Eq.refl
⁻¹[⇑]-wd'' {n} ε (comm₂ σ-gate g)
  rewrite lemma-ract-σ•ε-gg↥ g
  = PB._≈_.trans PB._≈_.right-unit (PB._≈_.sym PB._≈_.left-unit) , Eq.refl
⁻¹[⇑]-wd'' {n} ε (srel yang-baxter)
  = PB._≈_.trans PB._≈_.left-unit
      (PB._≈_.trans PB._≈_.left-unit
        (PB._≈_.trans (PB._≈_.sym PB._≈_.right-unit)
          (PB._≈_.cong PB._≈_.refl (PB._≈_.sym PB._≈_.left-unit))))
  , Eq.refl
⁻¹[⇑]-wd'' {n} ε (cong↑ {w = w} {v} eq)
  rewrite lemma-ract-suc' {n} w | lemma-ract-suc' {n} v
  = PB._≈_.axiom eq , Eq.refl

-- σ• ε coset
⁻¹[⇑]-wd'' {n} (σ• ε) (srel order)
  = PB._≈_.left-unit , Eq.refl
⁻¹[⇑]-wd'' {n} (σ• ε) (comm₂ σ-gate g)
  rewrite lemma-ract-σ•ε-gg↥ g
  = PB._≈_.trans PB._≈_.right-unit (PB._≈_.sym PB._≈_.left-unit) , Eq.refl
⁻¹[⇑]-wd'' {n} (σ• ε) (srel yang-baxter)
  = PB._≈_.refl , Eq.refl
⁻¹[⇑]-wd'' {n} (σ• ε) (cong↑ (srel order))
  = PB._≈_.left-unit , Eq.refl
⁻¹[⇑]-wd'' {n} (σ• ε) (cong↑ (comm₂ σ-gate g))
  rewrite lemma-ract-σ•ε-gg↥ g
  = PB._≈_.trans PB._≈_.right-unit (PB._≈_.sym PB._≈_.left-unit) , Eq.refl
⁻¹[⇑]-wd'' {n} (σ• ε) (cong↑ (srel yang-baxter))
  = PB._≈_.trans PB._≈_.left-unit
      (PB._≈_.trans PB._≈_.left-unit
        (PB._≈_.trans (PB._≈_.sym PB._≈_.right-unit)
          (PB._≈_.cong PB._≈_.refl (PB._≈_.sym PB._≈_.left-unit))))
  , Eq.refl
⁻¹[⇑]-wd'' {n} (σ• ε) (cong↑ (cong↑ (srel order)))
  rewrite lemma-ract-σ•1 {₁₊ n} ε σ-gen
  = PB._≈_.axiom (cong↑ (srel order)) , Eq.refl
⁻¹[⇑]-wd'' {n} (σ• ε) (cong↑ (cong↑ (comm₂ σ-gate g)))
  = PB._≈_.axiom (cong↑ (comm₂ σ-gate g)) , Eq.refl
⁻¹[⇑]-wd'' {n} (σ• ε) (cong↑ (cong↑ (srel yang-baxter)))
  rewrite lemma-ract-σ•1 {₁₊ n} ε σ-gen
  = PB._≈_.axiom (cong↑ (srel yang-baxter)) , Eq.refl
⁻¹[⇑]-wd'' {n} (σ• ε) (cong↑ (cong↑ (cong↑ {w = w} {v} eq)))
  rewrite lemma-ract-suc''' w | lemma-ract-suc''' v
  = PB._≈_.axiom (cong↑ (cong↑ eq)) , Eq.refl

-- σ• σ• c coset
⁻¹[⇑]-wd'' {n} (σ• σ• c) (srel order)
  = PB._≈_.axiom (srel order) , Eq.refl
⁻¹[⇑]-wd'' {n} (σ• σ•_ {n₁} ε) (srel yang-baxter)
  = PB._≈_.trans (PB._≈_.cong PB._≈_.refl PB._≈_.right-unit)
      (PB._≈_.trans PB._≈_.right-unit
        (PB._≈_.trans (PB._≈_.sym PB._≈_.left-unit)
          (PB._≈_.cong PB._≈_.refl (PB._≈_.sym PB._≈_.left-unit))))
  , Eq.refl
⁻¹[⇑]-wd'' {n} (σ• σ•_ {n₁} (σ• c)) (srel yang-baxter)
  = PB._≈_.axiom (srel yang-baxter) , Eq.refl
⁻¹[⇑]-wd'' {n} (σ• σ•_ {zero}   c) (comm₂ σ-gate (gate₁ ()))
⁻¹[⇑]-wd'' {n} (σ• σ•_ {zero}   c) (comm₂ σ-gate (() ↥))
⁻¹[⇑]-wd'' {n} (σ• σ•_ {₁₊ m} c) (comm₂ σ-gate g)
  rewrite lemma-ract-σ•σ•σ c | lemma-ract-σ•1 (σ• c) (g ↥) | lemma-ract-σ•1 c g
  = lemma-comm (proj₁ (ract c g)) , Eq.refl
⁻¹[⇑]-wd'' {n} (σ• σ•_ {n₁} c) (cong↑ {w = w} {v} eq)
  with ⁻¹[⇑]-wd'' (σ• c) eq
... | (wv , eq0)
  rewrite lemma-ract-σ•1s (σ• c) w | lemma-ract-σ•1s (σ• c) v
  = lemma-cong↑ _ _ wv , Eq.cong σ•_ eq0

------------------------------------------------------------------------
-- nf and nf2

succ : (Circuit (₁₊ n) × C (₁₊ n)) → (Circuit (₂₊ n) × C (₂₊ n))
succ {n} (w , c) = w ↑ • [_]ᶜ c , ε

succ-cong : ∀ {n} {w v} → _≋_ {n} w v → _≋_ {₁₊ n} (succ w) (succ v)
succ-cong {n} {a , c} {b , d} (l , r) = claim , Eq.refl
  where
  open PB (_VRel,_===_ (₂₊ n))
  open PP (_VRel,_===_ (₂₊ n))
  open SR word-setoid
  claim : succ (a , c) .proj₁ ≈ succ (b , d) .proj₁
  claim = begin
    a ↑ • [_]ᶜ c ≡⟨ Eq.cong (a ↑ •_) (Eq.cong [_]ᶜ r) ⟩
    a ↑ • [_]ᶜ d ≈⟨ cong (lemma-cong↑ a b l) refl ⟩
    b ↑ • [_]ᶜ d ∎

------------------------------------------------------------------------
-- Mutual induction

lemma-nf-cong2 : ∀ {n} →
  let _≈_ = PB._≈_ (_VRel,_===_ (₂₊ n)) in
  let _≈₀_ = PB._≈_ (_VRel,_===_ (₁₊ n)) in
  let _~_ = Pointwise _≈₀_ (_≡_ {A = C (₁₊ n)}) in
  Homomorphic₂ _≈_ _~_ (nf-of2 {n})
lemma-nf-cong2 {zero} = f-cong2
  where
  open PB (_VRel,_===_ 1) renaming (_≈_ to _≈₀_) using ()
  open PB (_VRel,_===_ 2) using (_≈_)
  _~_ = Pointwise _≈₀_ (_≡_ {A = C 1})
  module RSA = RSF (_VRel,_===_ 1) (_VRel,_===_ 2) (C 1) ε
  f = nf-of2 {0}
  f-cong2 : ∀ {a b} → a ≈ b → f a ~ f b
  f-cong2 {a} {b} eq = RSA.lemma-hypB (λ { (gate₁ ()) ; (() ↥) }) ract (λ { (gate₁ ()) ; (() ↥) }) ⁻¹[⇑]-wd'' ε _ _ eq
lemma-nf-cong2 {n@(₁₊ n')} = f-cong2
  where
  open PB (_VRel,_===_ (₁₊ n)) renaming (_≈_ to _≈₀_) using ()
  open PB (_VRel,_===_ (₂₊ n)) using (_≈_)
  _~_ = Pointwise _≈₀_ (_≡_ {A = C (₁₊ n)})
  module RSA = RSF (_VRel,_===_ (₁₊ n)) (_VRel,_===_ (₂₊ n)) (C (₁₊ n)) ε
  f = nf-of2 {n}
  f-cong2 : ∀ {a b} → a ≈ b → f a ~ f b
  f-cong2 {a} {b} eq = RSA.lemma-hypB ([_]ʷ ∘ _↥) ract ⁻¹[⇑]-gen' ⁻¹[⇑]-wd'' ε _ _ eq

lemma-nf-cong : ∀ {n} →
  let _≈_ = PB._≈_ (_VRel,_===_ n) in
  Homomorphic₂ _≈_ _≡_ (nf-of {n})
lemma-nf-cong {zero} = f-cong
  where
  open PB (_VRel,_===_ 0) renaming (_≈_ to _≈₁_)
  f = nf-of {0}
  f-cong : ∀ {a b} → a ≈₁ b → f a ≡ f b
  f-cong {a} {b} eq = Eq.refl
lemma-nf-cong {₁₊ zero} = f-cong
  where
  open PB (_VRel,_===_ 1) renaming (_≈_ to _≈₁_)
  f = nf-of {1}
  f-cong : ∀ {a b} → a ≈₁ b → f a ≡ f b
  f-cong {a} {b} eq = Eq.refl
lemma-nf-cong {₂₊ n} {x} {y} eq with lemma-nf-cong2 {n} eq | lemma-nf-cong {₁₊ n}
... | fst , snd | ih = ≡×≡⇒≡ (ih fst , snd)

lemma-nf-inj : ∀ {n} →
  let _≈_ = PB._≈_ (_VRel,_===_ n) in
  Injective _≈_ _≡_ (nf-of {n})
lemma-nf-inj {zero} = f-inj
  where
  open PB (_VRel,_===_ 0)
  f = nf-of {0}
  singleton : ∀ {a} → a ≈ ε
  singleton {ε}     = refl
  singleton {a • a₁} with singleton {a} | singleton {a₁}
  ... | ih1 | ih2 = trans (cong ih1 ih2) left-unit
  open PP (_VRel,_===_ 0)
  open SR word-setoid
  f-inj : ∀ {a b} → f a ≡ f b → a ≈ b
  f-inj {a} {b} eq = begin a ≈⟨ singleton ⟩ ε ≈⟨ sym singleton ⟩ b ∎
lemma-nf-inj {₁₊ zero} = f-inj
  where
  open PB (_VRel,_===_ 1)
  f = nf-of {1}
  singleton : ∀ {a} → a ≈ ε
  singleton {[ gate₁ () ]ʷ}
  singleton {[ () ↥ ]ʷ}
  singleton {ε}     = refl
  singleton {a • a₁} with singleton {a} | singleton {a₁}
  ... | ih1 | ih2 = trans (cong ih1 ih2) left-unit
  open PP (_VRel,_===_ 1)
  open SR word-setoid
  f-inj : ∀ {a b} → f a ≡ f b → a ≈ b
  f-inj {a} {b} eq = begin a ≈⟨ singleton ⟩ ε ≈⟨ sym singleton ⟩ b ∎
lemma-nf-inj {₂₊ n} with lemma-nf-inj {₁₊ n} | lemma-nf-cong {₁₊ n}
... | ih | ih-cong = f-inj
  where
  open PB (_VRel,_===_ (₂₊ n)) renaming (Alphabet to B)
  f = nf-of {₂₊ n}
  p0 : NFProperty (_VRel,_===_ (₁₊ n))
  p0 = record { NF = NF (₁₊ n) ; nf = nf-of ; nf-cong = ih-cong ; nf-injective = ih }
  open PB (_VRel,_===_ (₁₊ n)) renaming (_≈_ to _≈₀_) using ()
  module M = CA.Data (_VRel,_===_ (₁₊ n)) (_VRel,_===_ (₂₊ n)) (C (₁₊ n)) ε ([_]ʷ ∘ _↥) ract [_]ᶜ
  nfp-1 : NFProperty (_VRel,_===_ (₂₊ n))
  nfp-1 = M.Assumptions-And-Theorems.nfp
    (λ x₁ → _≈₀_.refl , Eq.refl)
    ⁻¹[⇑]-wd''
    (λ x₁ → Eq.subst₂ _≈_ (Eq.sym (lemma-* _)) (Eq.sym (lemma-* _)) (axiom (cong↑ x₁)))
    _≈_.refl
    (λ c b → Eq.subst (λ x → _≈_ ([_]ᶜ c • [ b ]ʷ) (x • [_]ᶜ (ract c b .proj₂)))
                       (Eq.sym (lemma-* (ract c b .proj₁)))
                       (lemma-ract c b))
    p0
  open PP (_VRel,_===_ (₂₊ n))
  open SR word-setoid
  module RSA = RSF (_VRel,_===_ (₁₊ n)) (_VRel,_===_ (₂₊ n)) (C (₁₊ n)) ε
  infix 4 _~_
  _~_ = Pointwise _≈₀_ (_≡_ {A = C (₁₊ n)})
  f-inj : ∀ {a b} → f a ≡ f b → a ≈ b
  f-inj {a} {b} = NFProperty.nf-injective nfp-1

------------------------------------------------------------------------
-- NFProperty and NFProperty'

nfp : (n : ℕ) → NFProperty (_VRel,_===_ n)
nfp n = record
  { NF = NF n ; nf = nf-of ; nf-cong = lemma-nf-cong ; nf-injective = lemma-nf-inj }

inv-f : (n : ℕ) → NF n → Circuit n
inv-f zero    _       = ε
inv-f (₁₊ zero) _    = ε
inv-f (₂₊ n) (l , r) = inv-f (₁₊ n) l ↑ • [_]ᶜ r

lemma-inv-f : (n : ℕ) → let _≈_ = PB._≈_ (_VRel,_===_ n) in {w : Circuit n} →
  inv-f n (nf-of w) ≈ w
lemma-inv-f zero {ε}     = PB._≈_.refl
lemma-inv-f zero {w • w₁} with lemma-inv-f zero {w} | lemma-inv-f zero {w₁}
... | ih1 | ih2 = PB._≈_.trans (PB._≈_.sym PB._≈_.left-unit) (PB._≈_.cong ih1 ih2)
lemma-inv-f (₁₊ zero) {[ gate₁ () ]ʷ}
lemma-inv-f (₁₊ zero) {[ () ↥ ]ʷ}
lemma-inv-f (₁₊ zero) {ε}     = PB._≈_.refl
lemma-inv-f (₁₊ zero) {w • w₁} with lemma-inv-f (₁₊ zero) {w} | lemma-inv-f (₁₊ zero) {w₁}
... | ih1 | ih2 = PB._≈_.trans (PB._≈_.sym PB._≈_.left-unit) (PB._≈_.cong ih1 ih2)
lemma-inv-f (₂₊ n) {w} =
  let (l , r) = racts ε w in begin
  inv-f (₂₊ n) (nf-of w) ≈⟨ _≈_.refl ⟩
  inv-f (₂₊ n) (nf-of l , r) ≈⟨ _≈_.refl ⟩
  inv-f (₁₊ n) (nf-of l) ↑ • [_]ᶜ r ≈⟨ cong (lemma-cong↑ (inv-f (₁₊ n) (nf-of l)) l (lemma-inv-f (₁₊ n) {l})) _≈_.refl ⟩
  l ↑ • [_]ᶜ r ≈⟨ sym (lemma-racts ε w) ⟩
  ε • w ≈⟨ _≈_.left-unit ⟩
  w ∎
  where
  open PB (_VRel,_===_ (₂₊ n))
  open PP (_VRel,_===_ (₂₊ n))
  open SR word-setoid

nfp' : (n : ℕ) → NFProperty' (_VRel,_===_ n)
nfp' n = record
  { NF = NF n ; nf = nf-of ; nf-cong = lemma-nf-cong
  ; inv-nf = inv-f n ; inv-nf∘nf=id = lemma-inv-f n }

------------------------------------------------------------------------
-- Auxiliary lemmas for UniqueNF

-- racts ε (w ↑ • v) = (w • proj₁ (racts ε v), proj₂ (racts ε v))
lemma-racts-↑• : ∀ {n} (w : Circuit (₁₊ n)) (v : Circuit (₂₊ n)) →
  racts {n} ε (w ↑ • v) ≡ (w • proj₁ (racts {n} ε v) , proj₂ (racts {n} ε v))
lemma-racts-↑• {n} w v rewrite lemma-ract-suc {n} w = Eq.refl

-- [_]ᶜ is a section of the coset action:
-- proj₂ (racts ε [r]ᶜ) ≡ r  and  proj₁ (racts ε [r]ᶜ) ≈ ε
lemma-racts-section : ∀ {n} (r : C (₁₊ n)) →
  proj₂ (racts {n} ε [ r ]ᶜ) ≡ r ×
  PB._≈_ (_VRel,_===_ (₁₊ n)) (proj₁ (racts {n} ε [ r ]ᶜ)) ε
lemma-racts-section {n} ε = Eq.refl , PB._≈_.refl
lemma-racts-section {zero} (σ• ε) = Eq.refl , left-unit
  where open PB (_VRel,_===_ 1)
lemma-racts-section {₁₊ m} (σ• c)
  with racts {m} ε [ c ]ᶜ | lemma-racts-section {m} c | lemma-ract-σ•1s {m} ε [ c ]ᶜ
... | (b , d) | (snd≡ , fst≈) | lsuc
  rewrite lsuc
  = Eq.cong σ•_ snd≡ ,
    trans left-unit (lemma-cong↑ b ε fst≈)
  where open PB (_VRel,_===_ (₂₊ m))

-- nf-of is a left inverse of inv-f: nf-of (inv-f n u) ≡ u
lemma-nf-of-inv-f : ∀ (n : ℕ) (u : NF n) → nf-of {n} (inv-f n u) ≡ u
lemma-nf-of-inv-f 0         tt     = Eq.refl
lemma-nf-of-inv-f 1         tt     = Eq.refl
lemma-nf-of-inv-f (₂₊ n') (l , r)
  with lemma-nf-of-inv-f (₁₊ n') l | lemma-racts-section {n'} r
... | ih-l | (snd≡ , fst≈) =
  Eq.trans
    (Eq.cong (map₁ (nf-of {₁₊ n'})) (lemma-racts-↑• {n'} (inv-f (₁₊ n') l) [ r ]ᶜ))
    (≡×≡⇒≡ (nf-step , snd≡))
  where
  open PB (_VRel,_===_ (₁₊ n'))
  b   = proj₁ (racts {n'} ε [ r ]ᶜ)
  nf-step : nf-of {₁₊ n'} (inv-f (₁₊ n') l • b) ≡ l
  nf-step = Eq.trans (lemma-nf-cong (trans (cong refl fst≈) right-unit)) ih-l

------------------------------------------------------------------------
-- UniqueNF

open import Examples.Groups.Symmetric.Semantics as Sem

-- Pointwise setoid on permutations Fin n → Fin n
perm-setoid : (n : ℕ) → Setoid 0ℓ 0ℓ
perm-setoid n = record
  { Carrier = Perm n
  ; _≈_     = λ f g → ∀ k → f k ≡ g k
  ; isEquivalence = record
    { refl  = λ _     → Eq.refl
    ; sym   = λ h k   → Eq.sym (h k)
    ; trans = λ h₁ h₂ k → Eq.trans (h₁ k) (h₂ k)
    }
  }

-- Encode a coset descriptor as a Fin
private
  depth : ∀ {n} → C n → Fin (₁₊ n)
  depth ε      = fzero
  depth (σ• c) = fsuc (depth c)

  depth-inj : ∀ {n} {r r' : C n} → depth r ≡ depth r' → r ≡ r'
  depth-inj {r = ε}    {r' = ε}     _  = Eq.refl
  depth-inj {r = ε}    {r' = σ• _}  ()
  depth-inj {r = σ• _} {r' = ε}     ()
  depth-inj {r = σ• c} {r' = σ• c'} eq =
    Eq.cong σ•_ (depth-inj (FP.suc-injective eq))

  -- ⟦ [r]ᶜ ⟧ fzero ≡ depth r
  lemma-⟦[r]ᶜ⟧-zero : ∀ {n} (r : C n) → ⟦ [ r ]ᶜ ⟧ fzero ≡ depth r
  lemma-⟦[r]ᶜ⟧-zero ε      = Eq.refl
  lemma-⟦[r]ᶜ⟧-zero (σ• c) =
    Eq.trans (⟦↑⟧ ([ c ]ᶜ) (fsuc fzero))
             (Eq.cong fsuc (lemma-⟦[r]ᶜ⟧-zero c))

  -- ⟦ [r]ᶜ ⟧ is injective on fsuc-values
  lemma-[r]ᶜ-suc-inj : ∀ {n} (r : C n) {j₁ j₂ : Fin n}
    → ⟦ [ r ]ᶜ ⟧ (fsuc j₁) ≡ ⟦ [ r ]ᶜ ⟧ (fsuc j₂) → j₁ ≡ j₂
  lemma-[r]ᶜ-suc-inj ε {j₁} {j₂} eq with eq
  ... | Eq.refl = Eq.refl
  lemma-[r]ᶜ-suc-inj (σ• c) {fzero}    {fzero}    _   = Eq.refl
  lemma-[r]ᶜ-suc-inj (σ• c) {fzero}    {fsuc j₂'} eq
    with Eq.trans (Eq.sym (⟦↑⟧ ([ c ]ᶜ) fzero))
                  (Eq.trans eq (⟦↑⟧ ([ c ]ᶜ) (fsuc (fsuc j₂'))))
  ... | ()
  lemma-[r]ᶜ-suc-inj (σ• c) {fsuc j₁'} {fzero}    eq
    with Eq.trans (Eq.trans (Eq.sym (⟦↑⟧ ([ c ]ᶜ) (fsuc (fsuc j₁')))) eq)
                  (⟦↑⟧ ([ c ]ᶜ) fzero)
  ... | ()
  lemma-[r]ᶜ-suc-inj (σ• c) {fsuc j₁'} {fsuc j₂'} eq =
    Eq.cong fsuc (lemma-[r]ᶜ-suc-inj c step)
    where
    step : ⟦ [ c ]ᶜ ⟧ (fsuc j₁') ≡ ⟦ [ c ]ᶜ ⟧ (fsuc j₂')
    step = FP.suc-injective
      (Eq.trans (Eq.sym (⟦↑⟧ ([ c ]ᶜ) (fsuc (fsuc j₁'))))
      (Eq.trans eq  (⟦↑⟧ ([ c ]ᶜ) (fsuc (fsuc j₂')))))

-- Helpers for unique-impl (defined before unique-impl to avoid where-clause cycles)
private
  make-r≡r' : ∀ n (l l' : NF (₁₊ n)) (r r' : C (₁₊ n))
    → (eq : ∀ k → ⟦ inv-f (₂₊ n) (l , r) ⟧ k ≡ ⟦ inv-f (₂₊ n) (l' , r') ⟧ k)
    → r ≡ r'
  make-r≡r' n l l' r r' eq =
    depth-inj
      (Eq.trans (Eq.sym (lemma-⟦[r]ᶜ⟧-zero r))
      (Eq.trans
        (Eq.trans
          (Eq.cong (⟦ [ r ]ᶜ ⟧) (Eq.sym (⟦↑⟧ (inv-f (₁₊ n) l) fzero)))
          (Eq.trans (eq fzero)
          (Eq.cong (⟦ [ r' ]ᶜ ⟧) (⟦↑⟧ (inv-f (₁₊ n) l') fzero))))
        (lemma-⟦[r]ᶜ⟧-zero r')))

  make-eqj : ∀ n (l l' : NF (₁₊ n)) (r r' : C (₁₊ n))
    → r ≡ r'
    → (eq : ∀ k → ⟦ inv-f (₂₊ n) (l , r) ⟧ k ≡ ⟦ inv-f (₂₊ n) (l' , r') ⟧ k)
    → ∀ j → ⟦ inv-f (₁₊ n) l ⟧ j ≡ ⟦ inv-f (₁₊ n) l' ⟧ j
  make-eqj n l l' r r' r≡r' eq j =
    lemma-[r]ᶜ-suc-inj r
      (Eq.trans
        (Eq.cong (⟦ [ r ]ᶜ ⟧) (Eq.sym (⟦↑⟧ (inv-f (₁₊ n) l) (fsuc j))))
        (Eq.trans
          (Eq.subst
            (λ s → ⟦ [ r ]ᶜ ⟧ (⟦ inv-f (₁₊ n) l ↑ ⟧ (fsuc j))
                 ≡ ⟦ [ s ]ᶜ ⟧ (⟦ inv-f (₁₊ n) l' ↑ ⟧ (fsuc j)))
            (Eq.sym r≡r')
            (eq (fsuc j)))
          (Eq.cong (⟦ [ r ]ᶜ ⟧) (⟦↑⟧ (inv-f (₁₊ n) l') (fsuc j)))))

-- Semantic injectivity of inv-f: pointwise-equal denotations imply equal NFs
private
  unique-impl : ∀ n {u v : NF n}
    → (∀ k → ⟦ inv-f n u ⟧ k ≡ ⟦ inv-f n v ⟧ k)
    → u ≡ v
  unique-impl 0       {tt}     {tt}      _   = Eq.refl
  unique-impl 1       {tt}     {tt}      _   = Eq.refl
  unique-impl (₂₊ n') {l , r} {l' , r'} eq  =
    ≡×≡⇒≡ (unique-impl (₁₊ n') (make-eqj n' l l' r r' r≡r' eq) , r≡r')
    where r≡r' = make-r≡r' n' l l' r r' eq

unique-nf : ∀ n →
  Presentation.Normalization.UniqueNF (PP.word-setoid (_VRel,_===_ n)) (NF n) (nf-of {n}) (inv-f n)
                         (Perm-setoid n) (⟦_⟧ {n})
unique-nf n = record
  { nf     = record { f-cong = lemma-nf-cong ; g∘f=id = lemma-inv-f n }
  ; unique = unique-impl n
  }
