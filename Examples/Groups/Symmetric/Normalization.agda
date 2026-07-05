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

module Examples.Groups.Symmetric.Normalization where

private variable
  n :  ℕ
  
open import Examples.Groups.Symmetric.Syntactics
open import Examples.Groups.Symmetric.NormalForm

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

lemma-inv-nf : (n : ℕ) → let _≈_ = PB._≈_ (_VRel,_===_ n) in {w : Circuit n} →
  inv-nf {n} (nf-of w) ≈ w
lemma-inv-nf zero {ε}     = PB._≈_.refl
lemma-inv-nf zero {w • w₁} with lemma-inv-nf zero {w} | lemma-inv-nf zero {w₁}
... | ih1 | ih2 = PB._≈_.trans (PB._≈_.sym PB._≈_.left-unit) (PB._≈_.cong ih1 ih2)
lemma-inv-nf (₁₊ zero) {[ gate₁ () ]ʷ}
lemma-inv-nf (₁₊ zero) {[ () ↥ ]ʷ}
lemma-inv-nf (₁₊ zero) {ε}     = PB._≈_.refl
lemma-inv-nf (₁₊ zero) {w • w₁} with lemma-inv-nf (₁₊ zero) {w} | lemma-inv-nf (₁₊ zero) {w₁}
... | ih1 | ih2 = PB._≈_.trans (PB._≈_.sym PB._≈_.left-unit) (PB._≈_.cong ih1 ih2)
lemma-inv-nf (₂₊ n) {w} =
  let (l , r) = racts ε w in begin
  inv-nf (nf-of w) ≈⟨ _≈_.refl ⟩
  inv-nf (nf-of l , r) ≈⟨ _≈_.refl ⟩
  inv-nf (nf-of l) ↑ • [_]ᶜ r ≈⟨ cong (lemma-cong↑ (inv-nf (nf-of l)) l (lemma-inv-nf (₁₊ n) {l})) _≈_.refl ⟩
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
  ; inv-nf = inv-nf {n} ; inv-nf∘nf=id = lemma-inv-nf n }
