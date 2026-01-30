{-# OPTIONS  --safe #-}
open import Level using (0ℓ)

open import Relation.Binary using (Rel)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Binary.Morphism.Definitions using (Homomorphic₂)
open import Relation.Binary.PropositionalEquality using (_≡_ ; inspect ; setoid ; module ≡-Reasoning) renaming ([_] to [_]ₑ)
import Relation.Binary.Reasoning.Setoid as SR
import Relation.Binary.PropositionalEquality as Eq
open import Relation.Nullary.Decidable using (yes ; no)


open import Function using (_∘_)
open import Function.Definitions using (Injective)

open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂ ; map₁)
open import Data.Product.Relation.Binary.Pointwise.NonDependent using (≡×≡⇒≡ ; Pointwise ; ≡⇒≡×≡)
open import Data.Product.Relation.Binary.Pointwise.NonDependent as PW
import Data.Product.Relation.Binary.Pointwise.Dependent as PWD
open import Data.Nat using (ℕ ; zero ; suc ; 2+)
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

module Presentation.Groups.Sn where

infix 9 _ₛ
-- iso to Fin
data X : ℕ -> Set where
  swap : ∀ {n} -> X (suc n)
  _ₛ : ∀ {n} -> X n -> X (suc n)

[_⇑] : ∀ {n} -> Word (X n) -> Word (X (suc n))
[_⇑] {n} = ([_]ʷ ∘ _ₛ) *

[_⇑]' : ∀ {n} -> Word (X n) -> Word (X (suc n))
[_⇑]' {n} = wmap _ₛ

lemma-[⇑]=[⇑]' : ∀ {n} (w : Word (X n)) -> [ w ⇑] ≡ [ w ⇑]'
lemma-[⇑]=[⇑]' {n} [ x ]ʷ = Eq.refl
lemma-[⇑]=[⇑]' {n} ε = Eq.refl
lemma-[⇑]=[⇑]' {n} (w • w₁) = Eq.cong₂ _•_ (lemma-[⇑]=[⇑]' w) (lemma-[⇑]=[⇑]' w₁)

data rel : (n : ℕ) -> Rel (Word (X n)) 0ℓ where
  order : ∀ {n} ->
    rel (suc n) ([ swap ]ʷ • [ swap ]ʷ) ε
  comm : ∀ {n} {a : X n} ->
    rel (2+ n) ([ swap ]ʷ • [ a ₛ ₛ ]ʷ) ([ a ₛ ₛ ]ʷ • [ swap ]ʷ)
  yang-baxter : ∀ {n} ->
    rel (2+ n) ([ swap ]ʷ • [ swap ₛ ]ʷ • [ swap ]ʷ) ([ swap ₛ ]ʷ • [ swap ]ʷ • [ swap ₛ ]ʷ)
  congₛ : ∀ {n w v} -> rel n w v ->
    rel (suc n) [ w ⇑] [ v ⇑] 
  
infixr 10 swap•_
data C : ℕ -> Set where
  ε : ∀ {n} -> C n
  swap•_ : ∀ {n} -> C n -> C (suc n)

[_] : ∀ {n} -> C n -> Word (X n)
[_] {n} ε = ε
[_] {suc n} (swap• c) = [ swap ]ʷ • [ [ c ] ⇑]

NF : ℕ -> Set
NF zero = ⊤
NF (suc n) = NF n × C (suc n)

lemma-daux : ∀ {n} x y -> swap•_ {n} x ≡ swap• y -> x ≡ y
lemma-daux {n} x y Eq.refl = Eq.refl

deceqC : ∀ {n} -> DecidableEquality (C n)
deceqC {zero} ε ε = yes Eq.refl
deceqC {suc n} ε ε = yes Eq.refl
deceqC {suc n} ε (swap• y) = no (λ ())
deceqC {suc n} (swap• x) ε = no (λ ())
deceqC {suc n} (swap• x) (swap• y) with deceqC x y
... | yes p = yes (Eq.cong swap•_ p)
... | no np = no (λ {x₁ → np (lemma-daux _ _ x₁)})

deceq : ∀ {n} -> DecidableEquality (NF n)
deceq {zero} tt tt = yes Eq.refl
deceq {suc n} (a , b) (a' , b') with deceq a a' | deceqC b b'
... | yes p1 | yes p2 = yes (≡×≡⇒≡ (p1 , p2))
... | yes p1 | no p2 = no (λ {x → p2 ( proj₂ (≡⇒≡×≡ x))})
... | no p1 | yes p2 = no (λ {x → p1 ( proj₁ (≡⇒≡×≡ x))})
... | no p1 | no p2 = no (λ {x → p2 ( proj₂ (≡⇒≡×≡ x))})

pres : (n : ℕ) -> WRel (X n)
pres n = rel n


[⇑]-cong : ∀ {n} w v ->
  let P : WRel (X n)
      P = pres n
  in let P1 : WRel (X (suc n))
         P1 = pres (suc n)
  in PB._≈_ P w v -> PB._≈_ P1 [ w ⇑] [ v ⇑]
[⇑]-cong {n} w v PB.refl = PB._≈_.refl
[⇑]-cong {n} w v (PB.sym eq) = PB._≈_.sym ([⇑]-cong v w eq)
[⇑]-cong {n} w v (PB.trans eq eq₁) = PB._≈_.trans ([⇑]-cong w _ eq) ([⇑]-cong _ v eq₁)
[⇑]-cong {n} w v (PB.cong eq eq₁) = PB._≈_.cong ([⇑]-cong _ _ eq) ([⇑]-cong _ _ eq₁)
[⇑]-cong {n} w v PB.assoc = PB._≈_.assoc
[⇑]-cong {n} w v PB.left-unit = PB._≈_.left-unit
[⇑]-cong {n} w v PB.right-unit = PB._≈_.right-unit
[⇑]-cong {n} w v (PB.axiom order) = PB._≈_.axiom (congₛ order)
[⇑]-cong {n} w v (PB.axiom comm) = PB._≈_.axiom (congₛ comm)
[⇑]-cong {n} w v (PB.axiom yang-baxter) = PB._≈_.axiom (congₛ yang-baxter)
[⇑]-cong {n} w v (PB.axiom (congₛ eq)) = PB._≈_.axiom (congₛ (congₛ eq))

grouplike : ∀ {n} -> Grouplike (rel n)
grouplike {n} swap = [ swap ]ʷ , (PB.axiom order)
grouplike {n} (gen ₛ) with grouplike gen
... | ig , prf = [ ig ⇑] , [⇑]-cong (ig • [ gen ]ʷ) ε prf

ract : ∀ {n} -> C (suc n) -> X (suc n) -> Word (X n) × C (suc n)
ract {n} ε swap = ε , swap• ε
ract {n} (swap• ε) swap = ε , ε
ract {n} (swap• swap• c) swap = [ swap ]ʷ , swap• swap• c

ract {n} ε (b ₛ) = [ b ]ʷ , ε
ract {suc n} (swap• c) (b ₛ) = let ih = ract {n} c b in [ proj₁ ih ⇑] , swap• (proj₂ ih)

racts : ∀ {n} -> C (suc n) -> Word (X (suc n)) -> Word (X n) × C (suc n)
racts {n} = ract {n} **

lemma-comm : ∀ {n} w -> 
  let P : WRel (X (2+ n))
      P = rel (2+ n)
  in PB._≈_ P ([ [ w ⇑] ⇑] • [ swap ]ʷ) ([ swap ]ʷ • [ [ w ⇑] ⇑])
lemma-comm {n} ε = trans left-unit (sym right-unit)
  where
  P = rel (2+ n)
  open PB P
  open PP P
  open SR word-setoid
lemma-comm {n} [ x ]ʷ = begin
  ([ [ [ x ]ʷ ⇑] ⇑] • [ swap ]ʷ) ≈⟨ _≈_.sym (_≈_.axiom comm) ⟩
  ([ swap ]ʷ • [ [ [ x ]ʷ ⇑] ⇑]) ∎
  where
  P = rel (2+ n)
  open PB P
  open PP P
  open SR word-setoid
lemma-comm {n} (w • v) with lemma-comm {n} w | lemma-comm {n} v
... | h1 | h2 = begin
  ([ [ w • v ⇑] ⇑] • [ swap ]ʷ) ≡⟨ Eq.refl ⟩
  ([ [ w  ⇑] ⇑] • [ [ v ⇑] ⇑]) • [ swap ]ʷ ≈⟨ _≈_.assoc ⟩ 
  [ [ w  ⇑] ⇑] • [ [ v ⇑] ⇑] • [ swap ]ʷ ≈⟨ cong refl h2 ⟩
  [ [ w  ⇑] ⇑] • [ swap ]ʷ • [ [ v ⇑] ⇑] ≈⟨ _≈_.sym _≈_.assoc ⟩
  ([ [ w  ⇑] ⇑] • [ swap ]ʷ) • [ [ v ⇑] ⇑] ≈⟨ cong h1 refl ⟩
  ([ swap ]ʷ • [ [ w  ⇑] ⇑]) • [ [ v ⇑] ⇑] ≈⟨ _≈_.assoc ⟩
  ([ swap ]ʷ • [ [ w • v ⇑] ⇑]) ∎
  where
  P = rel (2+ n)
  open PB P
  open PP P
  open SR word-setoid


lemma-ract : ∀ {n} c b ->
  let P = rel (suc n)
  in let (b' , c') = ract {n} c b in PB._≈_ P ([ c ] • [ b ]ʷ) ([ b' ⇑] • [ c' ])
lemma-ract {n} ε swap = _≈_.cong _≈_.refl (_≈_.sym _≈_.right-unit)
  where
  P = rel (suc n)
  open PB P
lemma-ract {n} (swap• ε) swap = _≈_.trans (_≈_.cong right-unit refl) (trans (axiom order) (sym right-unit))
  where
  P = rel (suc n)
  open PB P
lemma-ract {suc n} ε (b ₛ) = _≈_.trans _≈_.left-unit (_≈_.sym _≈_.right-unit)
  where
  P = rel (2+ n)
  open PB P
lemma-ract {suc n} (swap• swap• c) swap = begin
  ([ swap ]ʷ • [ [ swap ]ʷ • [ [ c ] ⇑] ⇑]) • [ swap ]ʷ ≈⟨ _≈_.assoc ⟩
  [ swap ]ʷ • [ [ swap ]ʷ • [ [ c ] ⇑] ⇑] • [ swap ]ʷ ≡⟨ Eq.refl ⟩
  [ swap ]ʷ • ([ [ swap ]ʷ ⇑] • [ [ [ c ] ⇑] ⇑]) • [ swap ]ʷ ≈⟨ _≈_.cong _≈_.refl _≈_.assoc ⟩
  [ swap ]ʷ • [ [ swap ]ʷ ⇑] • [ [ [ c ] ⇑] ⇑] • [ swap ]ʷ ≈⟨ cong refl (cong refl (lemma-comm [ c ])) ⟩
  [ swap ]ʷ • [ [ swap ]ʷ ⇑] • [ swap ]ʷ • [ [ [ c ] ⇑] ⇑] ≈⟨ _≈_.sym (_≈_.cong _≈_.refl _≈_.assoc) ⟩
  [ swap ]ʷ • ([ [ swap ]ʷ ⇑] • [ swap ]ʷ) • [ [ [ c ] ⇑] ⇑] ≈⟨ _≈_.sym _≈_.assoc ⟩
  ([ swap ]ʷ • [ [ swap ]ʷ ⇑] • [ swap ]ʷ) • [ [ [ c ] ⇑] ⇑] ≈⟨ cong (_≈_.axiom yang-baxter) refl ⟩
  ([ [ swap ]ʷ ⇑] • [ swap ]ʷ • [ [ swap ]ʷ ⇑]) • [ [ [ c ] ⇑] ⇑] ≈⟨ _≈_.trans _≈_.assoc (_≈_.cong _≈_.refl _≈_.assoc) ⟩
  ([ [ swap ]ʷ ⇑] • [ swap ]ʷ • [ [ swap ]ʷ • [ [ c ] ⇑] ⇑]) ∎
  where
  P = rel (2+ n)
  open PB P
  open PP P
  open SR word-setoid

lemma-ract {0} (swap• c) (() ₛ)
lemma-ract {suc n} (swap• ε) (b@swap ₛ) with lemma-ract {n} ε b
... | ih = begin
  [ swap• ε ] • [ b ₛ ]ʷ ≈⟨ _≈_.assoc ⟩
  [ swap ]ʷ • [ ε • [ b ]ʷ ⇑] ≈⟨ cong refl ([⇑]-cong (ε • [ b ]ʷ) ([ b0 ⇑] • [ c0 ]) ih) ⟩
  [ swap ]ʷ • [ [ b0 ⇑] • [ c0 ] ⇑] ≈⟨ _≈_.refl ⟩
  [ swap ]ʷ • [ [ b0 ⇑] ⇑] • [ [ c0 ] ⇑] ≈⟨ _≈_.sym _≈_.assoc ⟩
  ([ swap ]ʷ • [ [ b0 ⇑] ⇑]) • [ [ c0 ] ⇑] ≈⟨ cong (sym (lemma-comm (proj₁ (ract ε b)))) refl ⟩
  ([ [ b0 ⇑] ⇑] • [ swap ]ʷ) • [ [ c0 ] ⇑] ≈⟨ _≈_.assoc ⟩
  [ [ b0 ⇑] ⇑] • [ swap• c0 ] ∎
  where
  P0 = rel (suc ( n))
  P = rel (2+ n)
  open PB P
  open PP P
  open SR word-setoid
  b0 = proj₁ (ract {n} ε b)
  c0 = proj₂ (ract {n} ε b)
lemma-ract {suc n} (swap• ε) (b@(b' ₛ) ₛ) with lemma-ract {n} ε b
... | ih = begin
  [ swap• ε ] • [ b ₛ ]ʷ ≈⟨ _≈_.assoc ⟩
  [ swap ]ʷ • [ ε • [ b ]ʷ ⇑] ≈⟨ cong refl ([⇑]-cong (ε • [ b ]ʷ) ([ b0 ⇑] • [ c0 ]) ih) ⟩
  [ swap ]ʷ • [ [ b0 ⇑] • [ c0 ] ⇑] ≈⟨ _≈_.refl ⟩
  [ swap ]ʷ • [ [ b0 ⇑] ⇑] • [ [ c0 ] ⇑] ≈⟨ _≈_.sym _≈_.assoc ⟩
  ([ swap ]ʷ • [ [ b0 ⇑] ⇑]) • [ [ c0 ] ⇑] ≈⟨ cong (sym (lemma-comm (proj₁ (ract ε b)))) refl ⟩
  ([ [ b0 ⇑] ⇑] • [ swap ]ʷ) • [ [ c0 ] ⇑] ≈⟨ _≈_.assoc ⟩
  [ [ b0 ⇑] ⇑] • [ swap• c0 ] ∎
  where
  P0 = rel (suc (n))
  P : WRel (X _)
  P = rel (2+ n)
  open PB P
  open PP P
  open SR word-setoid
  b0 = proj₁ (ract {n} ε b)
  c0 = proj₂ (ract {n} ε b)
lemma-ract {suc n} (swap• swap• c) (b@swap ₛ) with lemma-ract {n} (swap• c) b
... | ih = begin
  [ swap• swap• c ] • [ b ₛ ]ʷ ≈⟨ _≈_.assoc ⟩
  [ swap ]ʷ • [ [ swap• c ] • [ b ]ʷ ⇑] ≈⟨ cong refl ([⇑]-cong ([ swap• c ] • [ b ]ʷ) ([ b0 ⇑] • [ c0 ]) ih) ⟩
  [ swap ]ʷ • [ [ b0 ⇑] • [ c0 ] ⇑] ≈⟨ _≈_.refl ⟩
  [ swap ]ʷ • [ [ b0 ⇑] ⇑] • [ [ c0 ] ⇑] ≈⟨ _≈_.sym _≈_.assoc ⟩
  ([ swap ]ʷ • [ [ b0 ⇑] ⇑]) • [ [ c0 ] ⇑] ≈⟨ cong (sym (lemma-comm (proj₁ (ract (swap• c) b)))) refl ⟩
  ([ [ b0 ⇑] ⇑] • [ swap ]ʷ) • [ [ c0 ] ⇑] ≈⟨ _≈_.assoc ⟩
  [ [ b0 ⇑] ⇑] • [ swap• c0 ] ∎
  where
  P0 = rel (suc ( n))
  P = rel (2+ n) 
  open PB P
  open PP P
  open SR word-setoid
  b0 = proj₁ (ract {n} (swap• c) b)
  c0 = proj₂ (ract {n} (swap• c) b)

lemma-ract {suc n} (swap• swap• c) (b@(bb' ₛ) ₛ) with lemma-ract {n} (swap• c) b
... | ih = begin
  [ swap• swap• c ] • [ b ₛ ]ʷ ≈⟨ _≈_.assoc ⟩
  [ swap ]ʷ • [ [ swap• c ] • [ b ]ʷ ⇑] ≈⟨ cong refl ([⇑]-cong ([ swap• c ] • [ b ]ʷ) ([ b0 ⇑] • [ c0 ]) ih) ⟩
  [ swap ]ʷ • [ [ b0 ⇑] • [ c0 ] ⇑] ≈⟨ _≈_.refl ⟩
  [ swap ]ʷ • [ [ b0 ⇑] ⇑] • [ [ c0 ] ⇑] ≈⟨ _≈_.sym _≈_.assoc ⟩
  ([ swap ]ʷ • [ [ b0 ⇑] ⇑]) • [ [ c0 ] ⇑] ≈⟨ cong (sym (lemma-comm (proj₁ (ract (swap• c) b)))) refl ⟩
  ([ [ b0 ⇑] ⇑] • [ swap ]ʷ) • [ [ c0 ] ⇑] ≈⟨ _≈_.assoc ⟩
  [ [ b0 ⇑] ⇑] • [ swap• c0 ] ∎
  where
  P0 = rel (suc ( n)) 
  P = rel (2+ n) 
  open PB P
  open PP P
  open SR word-setoid
  b0 = proj₁ (ract {n} (swap• c) b)
  c0 = proj₂ (ract {n} (swap• c) b)

lemma-racts : ∀ {n} c bs ->
  let P : WRel (X _)
      P = rel (suc n)
  in let (bs' , c') = racts {n} c bs in PB._≈_ P ([ c ] • bs) ([ bs' ⇑] • [ c' ])
lemma-racts {n} c [ x ]ʷ = lemma-ract c x
lemma-racts {n} c ε = _≈_.trans _≈_.right-unit (_≈_.sym _≈_.left-unit)
  where
  P : WRel (X _)
  P = rel (suc n) 
  open PB P
lemma-racts {n} c (bs • as) with racts c bs | inspect (racts c) bs | lemma-racts c bs
... | (bs' , c') | [ eq1 ]ₑ | ih1 with racts c' as | inspect (racts c') as | lemma-racts c' as
... | (as' , c'') | [ eq2 ]ₑ | ih2 = begin
  [ c ] • (bs • as) ≈⟨ _≈_.sym _≈_.assoc ⟩
  ([ c ] • bs) • as ≈⟨ _≈_.cong ih1 _≈_.refl ⟩
  ([ bs' ⇑] • [ c' ]) • as ≈⟨ _≈_.assoc ⟩
  [ bs' ⇑] • [ c' ] • as ≈⟨ _≈_.cong _≈_.refl ih2 ⟩
  [ bs' ⇑] • [ as' ⇑] • [ c'' ] ≈⟨ _≈_.sym _≈_.assoc ⟩
  [ bs' • as' ⇑] • [ c'' ] ∎
  where
  P : WRel (X _)
  P = rel (suc n) 
  open PB P
  open PP P
  open SR word-setoid


nf-of : ∀ {n} -> Word (X n) -> NF n
nf-of {zero} w = tt
nf-of {suc n} = map₁ (nf-of {n}) ∘ (racts ε)

nf-of2 : ∀ {n} -> Word (X (suc n)) -> Word (X n) × C (suc n)
nf-of2 {n} = racts ε

infix 4 _≋_
_≋_ : ∀ {n} -> Rel (Word (X n) × C (suc n)) 0ℓ
_≋_ {n} = let _≈₀_ = PB._≈_ (pres n) in Pointwise _≈₀_ (_≡_ {A = C (suc n)})

⁻¹[⇑]-gen' : ∀ {n} -> let _⊛_ = ract ** in ∀ (x : X n) -> ([ x ]ʷ , ε) ≋ ε ⊛ [ x ₛ ]ʷ
⁻¹[⇑]-gen' {n} swap = PB._≈_.refl , Eq.refl
⁻¹[⇑]-gen' {n} (x ₛ) = PB._≈_.refl , Eq.refl

succ : ∀ {n} -> (Word (X n) × C (suc n)) -> (Word (X (suc n)) × C (2+ n))
succ {n} (w , c) = [ w ⇑] • [ c ] , ε

succ-cong : ∀ {n} {w v} -> _≋_ {n} w v -> _≋_ {suc n} (succ w) (succ v)
succ-cong {n} {w@(a , c)} {v@(b , d)} eq@(l , r) = claim , Eq.refl
  where
    open PB (pres (suc n))
    open PP (pres (suc n))
    open SR word-setoid
    claim : succ w .proj₁ ≈ succ v .proj₁
    claim = begin
      succ w .proj₁ ≈⟨ _≈_.refl ⟩
      [ a ⇑] • [ c ] ≡⟨ Eq.cong ([ a ⇑] •_) (Eq.cong [_] r) ⟩
      [ a ⇑] • [ d ] ≈⟨ cong ([⇑]-cong a b l) refl ⟩
      [ b ⇑] • [ d ] ≈⟨ _≈_.refl ⟩
      succ v .proj₁ ∎

module CA0 n = CA.Data (pres n) (pres (suc n)) (C (suc n)) ε

lemma-ract-suc : ∀ {n} w -> racts {n} ε [ w ⇑] ≡ (w , ε)
lemma-ract-suc {n} [ x ]ʷ = Eq.refl
lemma-ract-suc {n} ε = Eq.refl
lemma-ract-suc {n} (w • v) with lemma-ract-suc {n} w
... | ih with lemma-ract-suc {n} v
... | ih' with racts ε [ w ⇑]
... | (w' , ew) rewrite Eq.cong proj₁ ih | Eq.cong proj₂ ih | Eq.cong proj₁ ih' | Eq.cong proj₂ ih' with racts ε [ v ⇑]
... | (v' , ev) = begin
  w • v , ε ≡⟨ Eq.refl ⟩
  (w • v , ε) ∎
  where
  open ≡-Reasoning

lemma-ract-suc' : ∀ {n} w -> ((ract {n}) **) ε [ w ⇑] ≡ (w , ε)
lemma-ract-suc' {n} [ x ]ʷ = Eq.refl
lemma-ract-suc' {n} ε = Eq.refl
lemma-ract-suc' {n} (w • v) with lemma-ract-suc' {n} w
... | ih with lemma-ract-suc' {n} v
... | ih' with racts ε [ w ⇑]
... | (w' , ew) rewrite Eq.cong proj₁ ih | Eq.cong proj₂ ih | Eq.cong proj₁ ih' | Eq.cong proj₂ ih' with racts ε [ v ⇑]
... | (v' , ev) = begin
  w • v , ε ≡⟨ Eq.refl ⟩
  (w • v , ε) ∎
  where
  open ≡-Reasoning

lemma-ract-suc'' : ∀ {n} w -> ((ract {2+ n}) **) (swap• ε) [ [ [ w ⇑] ⇑] ⇑] ≡ ([ [ w ⇑] ⇑] , swap• ε)
lemma-ract-suc'' {n} [ x ]ʷ = Eq.refl
lemma-ract-suc'' {n} ε = Eq.refl
lemma-ract-suc'' {n} (w • v) with lemma-ract-suc'' {n} w
... | ih with lemma-ract-suc'' {n} v
... | ih' with racts ε [ w ⇑]
... | (w' , ew) rewrite Eq.cong proj₁ ih | Eq.cong proj₂ ih | Eq.cong proj₁ ih' | Eq.cong proj₂ ih' with racts ε [ v ⇑]
... | (v' , ev) = begin
  [ [ w • v ⇑] ⇑] , swap• ε ≡⟨ Eq.refl ⟩
  [ [ w • v ⇑] ⇑] , swap• ε ∎
  where
  open ≡-Reasoning

lemma-ract-swap•swap• : ∀ {n} (c : C n) -> racts (swap• swap• c) [ swap ]ʷ ≡ ([ swap ]ʷ , swap• swap• c)
lemma-ract-swap•swap• {n} c = Eq.refl
  where
  open ≡-Reasoning

lemma-ract-swap•swap•2 : ∀ {n} c b -> let (b' , c') = ract {n} c b in ract (swap• swap• c) ((b ₛ) ₛ) ≡ ([ [ b' ⇑] ⇑] , swap• swap• c')
lemma-ract-swap•swap•2 {n} ε swap = Eq.refl
lemma-ract-swap•swap•2 {n} ε (b ₛ) = Eq.refl
lemma-ract-swap•swap•2 {n} (swap• c) swap = Eq.refl
lemma-ract-swap•swap•2 {n} (swap• c) (b ₛ) = Eq.refl
  where
  open ≡-Reasoning

lemma-ract-swap•swap•1 : ∀ {n} c b -> let (b' , c') = ract {n} c b in ract (swap• c) (b ₛ) ≡ ([ b' ⇑] , swap• c')
lemma-ract-swap•swap•1 {n} ε swap = Eq.refl
lemma-ract-swap•swap•1 {n} ε (b ₛ) = Eq.refl
lemma-ract-swap•swap•1 {n} (swap• c) swap = Eq.refl
lemma-ract-swap•swap•1 {n} (swap• c) (b ₛ) = Eq.refl
  where
  open ≡-Reasoning

lemma-ract-swap•swap•1s : ∀ {n} c w -> let (w' , c') = (ract {n} **) c w in (ract **) (swap• c) [ w ⇑] ≡ ([ w' ⇑] , swap• c')
lemma-ract-swap•swap•1s {n} c [ x ]ʷ = lemma-ract-swap•swap•1 c x
lemma-ract-swap•swap•1s {n} c ε = Eq.refl
lemma-ract-swap•swap•1s {n} c (w • v) with lemma-ract-swap•swap•1s c w | (ract **) c w | inspect ((ract **) (c)) w
... | ih1 | w' , c0 | [ eq1 ]ₑ rewrite ih1 | eq1 with lemma-ract-swap•swap•1s c0 v | (ract **) (c0) v | inspect ((ract **) (c0)) v
... | ih2 | v' , c1 | [ eq2 ]ₑ rewrite eq2 | Eq.cong proj₁ ih2 | Eq.cong proj₂ ih2 = Eq.refl
  where
  open ≡-Reasoning

⁻¹[⇑]-wd'' : ∀ {n} ->
  let _⊛_ = ract ** in
  let _===_ = PB._===_ (pres (suc n)) in
  ∀ (c : C (suc n)){u t : Word (X (suc n))} -> u === t -> c ⊛ u ≋ c ⊛ t
⁻¹[⇑]-wd'' {n} ε {u} {t} order = PB._≈_.left-unit , Eq.refl
⁻¹[⇑]-wd'' {n} ε {u} {t} comm = PB._≈_.trans PB._≈_.left-unit (PB._≈_.sym PB._≈_.right-unit) , Eq.refl
⁻¹[⇑]-wd'' {n} ε {u} {t} yang-baxter = PB._≈_.trans PB._≈_.left-unit (PB._≈_.trans PB._≈_.left-unit (PB._≈_.trans (PB._≈_.sym (PB._≈_.right-unit)) (PB._≈_.cong PB._≈_.refl (PB._≈_.sym PB._≈_.left-unit)))) , Eq.refl
⁻¹[⇑]-wd'' {suc n} ε {u} {t} (congₛ {w = w} {v} eq) rewrite lemma-ract-suc' {(suc n)} w | lemma-ract-suc' {(suc n)} v = PB._≈_.axiom eq , Eq.refl
⁻¹[⇑]-wd'' {n} (swap• ε) {u} {t} order = PB._≈_.left-unit , Eq.refl
⁻¹[⇑]-wd'' {n} (swap• swap• c) {u} {t} order = PB._≈_.axiom order , Eq.refl
⁻¹[⇑]-wd'' {n} (swap• ε) {u} {t} comm = PB._≈_.trans PB._≈_.left-unit (PB._≈_.sym PB._≈_.right-unit) , Eq.refl
⁻¹[⇑]-wd'' {n} (swap• swap•_ {n₁} c) {u} {t} (comm {a = swap}) rewrite lemma-ract-swap•swap• c | lemma-ract-swap•swap•1 c swap = PB._≈_.sym (lemma-comm ( ract c swap .proj₁)) , Eq.refl
⁻¹[⇑]-wd'' {n} (swap• swap•_ {n₁} c) {u} {t} (comm {a = a ₛ}) rewrite lemma-ract-swap•swap• c | lemma-ract-swap•swap•1 c (a ₛ) = PB._≈_.sym (lemma-comm ( ract c (a ₛ) .proj₁)) , Eq.refl
⁻¹[⇑]-wd'' {n} (swap• ε) {u} {t} yang-baxter = PB._≈_.refl , Eq.refl
⁻¹[⇑]-wd'' {n} (swap• swap•_ {n₁} ε) {u} {t} yang-baxter = PB._≈_.trans (PB._≈_.cong PB._≈_.refl PB._≈_.right-unit) (PB._≈_.trans PB._≈_.right-unit (PB._≈_.trans (PB._≈_.sym PB._≈_.left-unit) (PB._≈_.cong PB._≈_.refl (PB._≈_.sym PB._≈_.left-unit)))) , Eq.refl
⁻¹[⇑]-wd'' {n} (swap• swap•_ {n₁} (swap• c)) {u} {t} yang-baxter = PB._≈_.axiom yang-baxter , Eq.refl
⁻¹[⇑]-wd'' {n} (swap• ε) {u} {t} (congₛ order) = PB._≈_.left-unit , Eq.refl
⁻¹[⇑]-wd'' {n} (swap• ε) {u} {t} (congₛ comm) = PB._≈_.trans PB._≈_.left-unit
                                                  (PB._≈_.sym PB._≈_.right-unit)
                                                  , Eq.refl
⁻¹[⇑]-wd'' {n} (swap• ε) {u} {t} (congₛ (yang-baxter {n₁})) = PB._≈_.trans PB._≈_.left-unit (PB._≈_.trans PB._≈_.left-unit (PB._≈_.trans (PB._≈_.sym PB._≈_.right-unit) (PB._≈_.cong PB._≈_.refl (PB._≈_.sym PB._≈_.left-unit)))) , Eq.refl
⁻¹[⇑]-wd'' {n} (swap• ε) {u} {t} (congₛ (congₛ (order {n₁}))) rewrite lemma-ract-swap•swap•1 {suc n₁} ε (swap ₛ) = PB._≈_.axiom (congₛ order) , Eq.refl
⁻¹[⇑]-wd'' {n} (swap• ε) {u} {t} (congₛ (congₛ (comm {n₁} {a}))) rewrite lemma-ract-swap•swap•1 {suc n₁} ε ((a ₛ) ₛ) = PB._≈_.axiom (congₛ comm) , Eq.refl
⁻¹[⇑]-wd'' {n} (swap• ε) {u} {t} (congₛ (congₛ (yang-baxter {n₁}))) rewrite lemma-ract-swap•swap•1 {suc n₁} ε (swap ₛ) = PB._≈_.axiom (congₛ yang-baxter) , Eq.refl
⁻¹[⇑]-wd'' {n} (swap• ε) {u} {t} (congₛ (congₛ (congₛ {n₁} {w} {v} eq))) rewrite lemma-ract-suc'' w | lemma-ract-suc'' v = PB._≈_.axiom (congₛ (congₛ eq)) , Eq.refl
⁻¹[⇑]-wd'' {n} (swap• swap•_ {n₁} c) {u} {t} (congₛ {w = w} {v} eq) with ⁻¹[⇑]-wd'' (swap• c) eq
... | (wv , eq0) rewrite lemma-ract-swap•swap•1s (swap• c) w | lemma-ract-swap•swap•1s (swap• c) v = [⇑]-cong _ _ wv , Eq.cong swap•_ eq0

mutual

  lemma-nf-inj : ∀ {n} ->
    let _≈_ = PB._≈_ (pres n) in
    Injective _≈_ _≡_ (nf-of {n}) 
  lemma-nf-inj {zero} = f-inj
    where
    open PB (pres 0)

    f = nf-of {0}

    singleton : ∀ {a} -> a ≈ ε
    singleton {ε} = refl
    singleton {a • a₁} with singleton {a} | singleton {a₁}
    ... | ih1 | ih2 = trans (cong ih1 ih2) left-unit

    open PP (pres 0)

    open SR word-setoid

    f-inj :  ∀ {a b} -> f a ≡ f b -> a ≈ b
    f-inj {a} {b} eq = begin
      a ≈⟨ singleton ⟩
      ε ≈⟨ sym singleton ⟩
      b ∎

  lemma-nf-inj {suc n} with lemma-nf-inj {n}
  ... | ih = f-inj
    where
    open PB (pres (suc n)) renaming ( Alphabet to B)

    f = nf-of {suc n}

    p0 : NFProperty (pres n)
    p0 = record { NF = NF n ; nf = nf-of ; nf-cong = lemma-nf-cong ; nf-injective = lemma-nf-inj }

    open PB (pres n) renaming (_≈_ to _≈₀_) using ()
    
    module M = CA.Data (pres n) (pres (suc n)) (C (suc n)) ε ([_]ʷ ∘ _ₛ) ract [_]

    nfp-1 : NFProperty (pres (suc n))
    nfp-1 = M.Assumptions-And-Theorems.nfp (λ x₁ → _≈₀_.refl , Eq.refl) ⁻¹[⇑]-wd'' ((λ x₁ → axiom (congₛ x₁))) _≈_.refl lemma-ract p0

    open PP (pres (suc n))
    open SR word-setoid

    module RSA = RSF (pres n) (pres (suc n)) (C (suc n)) ε 

    infix 4 _~_
    _~_ = Pointwise _≈₀_ (_≡_ {A = C (suc n)})

    f-inj :  ∀ {a b} -> f a ≡ f b -> a ≈ b
    f-inj {a} {b} = NFProperty.nf-injective nfp-1 
  
  lemma-nf-cong : ∀ {n} ->
    let _≈_ = PB._≈_ (pres n) in
    Homomorphic₂ (Word (X n)) (NF n) _≈_ _≡_ (nf-of {n}) 
  lemma-nf-cong {zero} = f-cong
    where
    open PB (pres 0) renaming (_≈_ to _≈₁_)

    f = nf-of {0}
    f-cong : ∀ {a b} -> a ≈₁ b -> f a ≡ f b
    f-cong {a} {b} eq = Eq.refl

  lemma-nf-cong {suc n} {x} {y} eq with lemma-nf-cong2 {n} eq
  ... | fst , snd with  lemma-nf-cong {n}
  ... | ih = ≡×≡⇒≡ (ih fst , snd)
    where
    open PB (pres n) renaming (_≈_ to _≈₀_) using ()
    open PB (pres (suc n)) using (_≈_)
    _~_ = Pointwise _≈₀_ (_≡_ {A = C ((suc n))})

    module RSA = RSF (pres n) (pres (suc n)) (C (suc n)) ε
    
    f = nf-of2 {n}
    f-cong2 : ∀ {a b} -> a ≈ b -> f a ~ f b
    f-cong2 {a} {b} eq = RSA.lemma-hypB ([_]ʷ ∘ _ₛ) ract ⁻¹[⇑]-gen'  ⁻¹[⇑]-wd'' ε _ _ eq

  
  lemma-nf-cong2 : ∀ {n} ->
    let _≈_ = PB._≈_ (pres (suc n)) in
    let _≈₀_ = PB._≈_ (pres (n)) in
    let _~_ = Pointwise _≈₀_ (_≡_ {A = C (suc n)}) in
    Homomorphic₂ (Word (X (suc n))) (Word (X n) × C (suc n)) _≈_ _~_ (nf-of2 {n}) 
  lemma-nf-cong2 {zero} = f-cong2
    where
    open PB (pres 0) renaming (_≈_ to _≈₀_) using ()
    open PB (pres 1) using (_≈_)
    _~_ = Pointwise _≈₀_ (_≡_ {A = C (suc 0)})

    module RSA = RSF (pres 0) (pres 1) (C 1) ε
    
    f = nf-of2 {0}
    f-cong2 : ∀ {a b} -> a ≈ b -> f a ~ f b
    f-cong2 {a} {b} eq = RSA.lemma-hypB (λ ()) ract (λ ()) ⁻¹[⇑]-wd'' ε _ _ eq

  lemma-nf-cong2 {n@(suc n')} = f-cong2
    where
    open PB (pres n) renaming (_≈_ to _≈₀_) using ()
    open PB (pres (suc n)) using (_≈_)
    _~_ = Pointwise _≈₀_ (_≡_ {A = C ((suc n))})

    module RSA = RSF (pres n) (pres (suc n)) (C (suc n)) ε
    
    f = nf-of2 {n}
    f-cong2 : ∀ {a b} -> a ≈ b -> f a ~ f b
    f-cong2 {a} {b} eq = RSA.lemma-hypB ([_]ʷ ∘ _ₛ) ract ⁻¹[⇑]-gen'  ⁻¹[⇑]-wd'' ε _ _ eq

nfp : (n : ℕ) -> NFProperty (pres n)
nfp n = record { NF = NF n ; nf = nf-of ; nf-cong = lemma-nf-cong ; nf-injective = lemma-nf-inj }

inv-f : (n : ℕ) -> NF n -> Word (X n)
inv-f zero = λ z → ε
inv-f (suc n) (l , r) = [ inv-f n l ⇑] • [ r ]


lemma-inv-f : (n : ℕ) -> let _≈_ = PB._≈_ (pres n) in {w : Word (X n)} → inv-f n (nf-of w) ≈ w
lemma-inv-f zero {ε} = PB._≈_.refl
lemma-inv-f zero {w • w₁} with lemma-inv-f zero {w} | lemma-inv-f zero {w₁}
... | ih1 | ih2 = PB._≈_.trans (PB._≈_.sym PB._≈_.left-unit) (PB._≈_.cong ih1 ih2)
lemma-inv-f (suc n) {w} = let (l , r) = racts ε w in begin
  inv-f (suc n) (nf-of w) ≈⟨ _≈_.refl ⟩
  inv-f (suc n) (nf-of l , r) ≈⟨ _≈_.refl ⟩
  [ inv-f n (nf-of l) ⇑] • [ r ] ≈⟨ cong ([⇑]-cong (inv-f n (nf-of l)) l (lemma-inv-f n {l})) _≈_.refl ⟩
  [ l ⇑] • [ r ] ≈⟨ sym (lemma-racts ε w) ⟩
  ε • w ≈⟨ _≈_.left-unit ⟩
  w ∎
    where
    open PB (pres (suc n))
    open PP (pres (suc n))
    open SR word-setoid
       

nfp' : (n : ℕ) -> NFProperty' (pres n)
nfp' n = record
              { NF = NF n ; nf = nf-of ; nf-cong = lemma-nf-cong ; inv-nf = inv-f n ; inv-nf∘nf=id = lemma-inv-f n }
