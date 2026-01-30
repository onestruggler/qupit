{-# OPTIONS  --safe #-}
{-# OPTIONS  --call-by-name #-}
--{-# OPTIONS --termination-depth=2 #-}
open import Level using (0ℓ)

open import Relation.Binary using (Rel)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Binary.Morphism.Definitions using (Homomorphic₂)
open import Relation.Binary.PropositionalEquality using (_≡_ ; _≢_ ; inspect ; setoid ; module ≡-Reasoning ; _≗_) renaming ([_] to [_]')
import Relation.Binary.Reasoning.Setoid as SR
import Relation.Binary.PropositionalEquality as Eq
open import Relation.Nullary.Decidable using (yes ; no)


open import Function using (_∘_ ; id)
open import Function.Definitions using (Injective)

open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂ ; map₁ ; ∃ ; Σ ; Σ-syntax)
open import Data.Product.Relation.Binary.Pointwise.NonDependent as PW using (≡×≡⇒≡ ; Pointwise ; ≡⇒≡×≡)
open import Data.Nat hiding (_^_ ; _+_ ; _*_)
open import Agda.Builtin.Nat using (_-_)
import Data.Nat as Nat
open import Data.Bool hiding (_<_ ; _≤_)
open import Data.List hiding ([_] ; _++_ ; last ; head ; tail ; _∷ʳ_)
open import Data.Vec hiding ([_])
import Data.Vec as Vec
open import Data.Fin hiding (_+_ ; _-_ ; _≤_ ; _<_)

open import Data.Maybe
open import Data.Sum using (_⊎_ ; inj₁ ; inj₂ ; [_,_] ; [_,_]′)
open import Data.Unit using (⊤ ; tt)
open import Data.Empty using (⊥ ; ⊥-elim)

open import Word.Base as WB hiding (wfoldl ; _* ; _^'_)
open import Word.Properties
import Presentation.Base as PB
import Presentation.Properties as PP
open PP using (NFProperty ; NFProperty')
import Presentation.CosetNF as CA
import Presentation.Reidemeister-Schreier as RS
module RSF = RS.Star-Injective-Full.Reidemeister-Schreier-Full

open import Presentation.Construct.Base hiding (_*_ ; _⊕_)
import Presentation.Construct.Properties.SemiDirectProduct2 as SDP2
import Presentation.Construct.Properties.DirectProduct as DP
import Presentation.Groups.Cyclic as Cyclic


open import Data.Fin using (Fin ; toℕ ; suc ; zero ; fromℕ)
open import Data.Fin.Properties using (suc-injective ; toℕ-inject₁ ; toℕ-fromℕ)
import Data.Nat.Properties as NP
open import Presentation.GroupLike
open import Presentation.Tactics hiding ([_])
open import Data.Nat.Primality



module N.LM (p-2 : ℕ) (p-prime : Prime (2+ p-2))  where

pattern auto = Eq.refl

pattern ₀ = zero
pattern ₁ = suc ₀
pattern ₂ = suc ₁
pattern ₃ = suc ₂
pattern ₅ = 5
pattern ₆ = 6
pattern ₇ = 7
pattern ₈ = 8
pattern ₉ = 9
pattern ₁₀ = 10
pattern ₁₁ = 11
pattern ₁₂ = 12
pattern ₁₃ = 13
pattern ₁₄ = 14
pattern ₁₅ = 15

pattern ₁₊ ⱼ = suc ⱼ
pattern ₂₊ ⱼ = suc (suc ⱼ)
pattern ₃₊ ⱼ = suc (suc (suc ⱼ))
pattern ₄₊ ⱼ = suc (suc (suc (suc ⱼ)))


open import Zp.ModularArithmetic
open PrimeModulus p-2 p-prime
open import N.Cosets p-2 p-prime
open import N.Symplectic-Derived p-2 p-prime
open Symplectic-Derived-Gen renaming (M to ZM)
open import N.NF1 p-2 p-prime
open import N.Boxes p-2 p-prime public
open Normal-Form1

open import N.NF2 p-2 p-prime
open LM2

private
  variable
    n : ℕ


-- A box is MC.
[_]ᵃ : ∀ {n} → A → Word (Gen (₁₊ n))
[_]ᵃ {n} ((₀ , ₀), pr) = ⊥-elim (pr auto)
[_]ᵃ {n} ((₀ , b@(₁₊ b-1)), pr) = ⟦ (b , λ ()) ⁻¹ , ε ⟧ₘ₊
[_]ᵃ {n} ((a@(₁₊ a-1) , b), pr) = ⟦ (a , λ ()) ⁻¹ , HS^ -b/a ⟧ₘ₊
  where
  a⁻¹ = ((a , λ ()) ⁻¹) .proj₁
  -b/a = - b * a⁻¹

[_]ᵇ : ∀ {n} → B → Word (Gen (₂₊ n))
[_]ᵇ {n} (₀ , ₀) = Ex
[_]ᵇ {n} (a@₀ , b@(₁₊ b-1)) = Ex • CX • [ (a , b) , (λ ()) ]ᵃ ↑
[_]ᵇ {n} (a@(₁₊ a-1) , b) = Ex • CX • [ (a , b) , (λ ()) ]ᵃ ↑

[_]ᵈ : ∀ {n} → D → Word (Gen (₂₊ n))
[_]ᵈ {n} (₀ , d) = Ex • CZ^ (- d)
[_]ᵈ {n} (a@(₁₊ _) , b) = [ ₀ , ₁ ]ᵈ • [ (a , b) , (λ ()) ]ᵃ

[_]ᵉ : ∀ {n} → E → Word (Gen (₁₊ n))
[_]ᵉ {n} b = S^ (- b)

[_]ᵛᵇ : ∀ {n} → Vec B n → Word (Gen (₁₊ n))
[_]ᵛᵇ {₀} [] = ε
[_]ᵛᵇ {suc n} (x ∷ v) = [ v ]ᵛᵇ ↑ • [ x ]ᵇ

[_]ᵛᵈ : ∀ {n} → Vec D n → Word (Gen (₁₊ n))
[_]ᵛᵈ {₀} [] = ε
[_]ᵛᵈ {suc n} (x ∷ v) = [ x ]ᵈ • [ v ]ᵛᵈ ↑

[_]ᵐ : ∀ {n} → M n → Word (Gen n)
[_]ᵐ {0} _ = ε
[_]ᵐ {1} e = [ e ]ᵉ
[_]ᵐ {₂₊ n} (e , vd) = [ e ]ᵉ • [ vd ]ᵛᵈ

jth-abox : ∀ {j n} → j ≤ n → A → Word (Gen (₁₊ n))
jth-abox {₀} {n} _ a = [ a ]ᵃ
jth-abox {₁₊ j} {₁₊ n} (s≤s j≤n) a = jth-abox {j} {n} (j≤n) a ↑


jth-bbox : ∀ {j n} → j ≤ n → B → Word (Gen (₂₊ n))
jth-bbox {₀} {n} _ a = [ a ]ᵇ
jth-bbox {₁₊ j} {₁₊ n} (s≤s j≤n) a = jth-bbox {j} {n} (j≤n) a ↑

jth-dbox : ∀ {j n} → j ≤ n → B → Word (Gen (₂₊ n))
jth-dbox {₀} {n} _ a = [ a ]ᵈ
jth-dbox {₁₊ j} {₁₊ n} (s≤s j≤n) a = jth-dbox {j} {n} (j≤n) a ↑

jth-ebox : ∀ {j n} → j ≤ n → E → Word (Gen (₁₊ n))
jth-ebox {₀} {n} _ a = [ a ]ᵉ
jth-ebox {₁₊ j} {₁₊ n} (s≤s j≤n) a = jth-ebox {j} {n} (j≤n) a ↑

jth-bboxes : ∀ {j n} → j ≤ n → Vec B (n ∸ j) → Word (Gen (₁₊ n))
jth-bboxes {₀} {n} j≤n v = [ v ]ᵛᵇ
jth-bboxes {₁₊ j} {₁₊ n} (s≤s j≤n) (v) = jth-bboxes j≤n v ↑

lemma-jth-bboxes : ∀ {n} (vb : Vec B n) → jth-bboxes (z≤n {n}) vb ≡ [ vb ]ᵛᵇ
lemma-jth-bboxes {₀} vb = auto
lemma-jth-bboxes {₁₊ j} vb = auto

jth-babox : ∀ {j n} → j ≤ n → Vec B (n ∸ j) -> A → Word (Gen (₁₊ n))
jth-babox {₀} {n} j≤n v a = [ v ]ᵛᵇ • jth-abox j≤n a
jth-babox {₁₊ j} {₁₊ n} (s≤s j≤n) v a = jth-babox j≤n v a ↑

[_]ˡ : ∀ {n} → L n → Word (Gen n)
[_]ˡ {0} _ = ε
[_]ˡ {1} a = [ a ]ᵃ
[_]ˡ {₂₊ n} ((j , j≤n) , bs , a) = jth-babox j≤n bs a

[_]ˡ' : ∀ {n} → L' n → Word (Gen n)
[_]ˡ' {0} l = ε
[_]ˡ' {1} l = [ l ]ᵃ
[_]ˡ' {2} l = ε
[_]ˡ' {₃₊ n} (vb , a) = [ vb ]ᵛᵇ • [ a ]ᵃ

[_]ˡᵐ : ∀ {n} → LM n → Word (Gen n)
[_]ˡᵐ {0} _ = ε
[_]ˡᵐ {1} lm1 = ⟦ lm1 ⟧₁
[_]ˡᵐ {2} lm2 = ⟦ lm2 ⟧₂
[_]ˡᵐ {₃₊ n} (inj₁ (m , l)) = [ m ]ᵐ • [ l ]ˡ'
[_]ˡᵐ {₃₊ n} (inj₂ (d , lm)) = [ d ]ᵈ • [ lm ]ˡᵐ ↑

[_] : ∀ {n} → NF n → Word (Gen n)
[_] {0} tt = ε
[_] {₁₊ n} (nf , lm) = [ nf ] ↑ • [ lm ]ˡᵐ


data BoxType : Set where
  ᵃ : BoxType
  ᵇ : BoxType
  ᵈ : BoxType
  ᵉ : BoxType
  ˡ : BoxType
  ˡ' : BoxType
  ᵐ : BoxType
  ˡᵐ : BoxType
  ᵛᵇ : BoxType
  ᵛᵈ : BoxType
  ⁿᶠ : BoxType

Box : ∀ {n : ℕ} -> BoxType -> Set
Box ᵃ = A
Box ᵇ = B
Box ᵈ = D
Box ᵉ = E
Box {n} ˡ = L n
Box {n} ˡ' = L' n
Box {n} ᵐ = M n
Box {n} ˡᵐ = LM n
Box {n} ᵛᵇ = Vec B n
Box {n} ᵛᵈ = Vec D n
Box {n} ⁿᶠ = NF n

BIndex : BoxType -> Rel ℕ 0ℓ
BIndex ᵃ = _≤_
BIndex ᵉ = _≤_
BIndex ᵇ = _<_
BIndex ᵈ = _<_
BIndex _ = \ _ _ -> ⊤

BWidth : BoxType -> ℕ
BWidth ⁿᶠ = 0
BWidth ˡ = 0
BWidth ˡ' = 0
BWidth ᵐ = 0
BWidth ˡᵐ = 0
BWidth ᵇ = 2
BWidth ᵈ = 2
BWidth _ = 1

-- A unified way to call all box interpretation.
⟦_⟧ : ∀ {j n} (bt : BoxType) -> Box {n} bt -> BIndex bt j n -> Word (Gen (BWidth bt Nat.+ n))
⟦_⟧ {j} {n} ᵃ x j≤n = jth-abox j≤n x
⟦_⟧ {j} {₁₊ n} ᵇ x j<n = jth-bbox j<n x
⟦_⟧ {j} {n} ᵈ x j<n = jth-dbox j<n x
⟦_⟧ {j} {n} ᵉ x j≤n = jth-ebox j≤n x
⟦_⟧ {j} {n} ˡ x j≤n = [ x ]ˡ
⟦_⟧ {j} {n} ˡ' x j≤n = [ x ]ˡ'
⟦_⟧ {j} {n} ᵐ x j≤n = [ x ]ᵐ
⟦_⟧ {j} {n} ˡᵐ x j≤n = [ x ]ˡᵐ
⟦_⟧ {j} {n} ᵛᵇ x j≤n = [ x ]ᵛᵇ
⟦_⟧ {j} {n} ᵛᵈ x j≤n = [ x ]ᵛᵈ
⟦_⟧ {j} {n} ⁿᶠ x j≤n = [ x ]

--open import N.Pauli p-2 p-prime
open import N.Action p-2 p-prime
open import N.Action-Lemmas p-2 p-prime
open import Algebra.Properties.Ring (+-*-ring p-2)

sfrom-pIq=0 : ∀ x -> sform1 pI x ≡ ₀
sfrom-pIq=0 x@(c , d) = begin
  sform1 pI x ≡⟨ auto ⟩
  - ₀ * d + c * ₀ ≡⟨ Eq.cong₂ (\ xx yy -> xx * d + yy) -0#≈0# (*-zeroʳ c) ⟩
  ₀ * d + ₀ ≡⟨ +-identityʳ (₀ * d) ⟩
  ₀ * d ≡⟨ *-zeroˡ d ⟩
  ₀ ∎
  where
  open ≡-Reasoning


lemma-act-CX : ∀ (p@(a , b) q@(c , d) : Pauli1) t ->
  act {₂₊ n} CX (p ∷ q ∷ t) ≡ ((a + c , b) ∷ (c , d + - b) ∷ t)
lemma-act-CX p@(a , b) q@(c , d) t = begin
  act (H ^ ₃ • CZ • H) ((a , b) ∷ (c , d) ∷ t) ≡⟨ auto ⟩
  act (H ^ ₃ • CZ) ((- b , a) ∷ (c , d) ∷ t) ≡⟨ auto ⟩
  act (H ^ ₃) ((- b , a + c * ₁) ∷ (c , d + - b * ₁) ∷ t) ≡⟨  Eq.cong₂ (\ xx yy -> act (H ^ ₃) ((- b , a + xx) ∷ (c , d + yy) ∷ t)) (*-identityʳ (c)) (*-identityʳ (- b))  ⟩
  act (H ^ ₃) ((- b , a + c) ∷ (c , d + - b) ∷ t) ≡⟨ lemma-act-cong _ _ (PB.sym (PB.axiom (derived-H ₃))) (((- b , a + c) ∷ (c , d + - b) ∷ t)) ⟩
  act (H^ ₃) ((- b , a + c) ∷ (c , d + - b) ∷ t) ≡⟨ auto ⟩
  ((a + c , - - b) ∷ (c , d + - b) ∷ t) ≡⟨ Eq.cong (\ xx -> ((a + c , xx) ∷ (c , d + - b) ∷ t)) (-‿involutive b) ⟩
  ((a + c , b) ∷ (c , d + - b) ∷ t) ∎
  where
  open ≡-Reasoning


lemma-act-Ex : ∀ p q t ->
  act {₂₊ n} Ex (p ∷ q ∷ t) ≡ (q ∷ p ∷ t)
lemma-act-Ex p q t = act-Ex (p .proj₁) (p .proj₂) (q .proj₁) (q .proj₂) t

-- lemma-abox' : ∀ (ab@((a , b), neqI) : A) t ->
--   act [ (a , b) , neqI ]ᵃ ((a , b) ∷ t) ≡ {!!}

lemma-abox-01 : ∀ (ps : Pauli (₁₊ n)) →
  act [ (₀ , ₁) , (λ ()) ]ᵃ ps ≡ ps
lemma-abox-01 ps@((a , b) ∷ t) = begin
  act [ (₀ , ₁) , (λ ()) ]ᵃ ps ≡⟨ auto ⟩
  act ⟦ (₁ , λ ()) ⁻¹ , ε ⟧ₘ₊ ps ≡⟨ auto ⟩
  act ⟦ (₁ , λ ()) ⁻¹ ⟧ₘ ps ≡⟨ lemma-M a b t ((₁ , λ ()) ⁻¹) ⟩
  (a * x⁻¹ , b * x) ∷ t ≡⟨ Eq.cong₂ (λ xx yy → (a * xx , b * yy) ∷ t) aux-inv1 inv-₁ ⟩
  (a * ₁ , b * ₁) ∷ t ≡⟨ Eq.cong₂ (\ xx yy -> (xx , yy) ∷ t) (*-identityʳ a) (*-identityʳ b) ⟩
  ps ∎
  where
  open ≡-Reasoning
  x' = (₁ , λ ()) ⁻¹
  x = (x' .proj₁)
  x⁻¹ = ((x' ⁻¹) .proj₁)
  aux-inv1 : x⁻¹ ≡ ₁
  aux-inv1 = Eq.trans (inv-cong (x' ) ((₁ , λ ())) inv-₁) inv-₁
  


lemma-abox : ∀ p (neqI : p ≢ pI)(ps : Pauli n) →
  act [ p , neqI ]ᵃ (p ∷ ps) ≡ (pZ ∷ ps)
lemma-abox (₀ , ₀) neqI ps = ⊥-elim (neqI auto)
lemma-abox (₀ , b@(₁₊ b')) neqI ps = begin
  act ⟦ (b , λ ()) ⁻¹ , ε ⟧ₘ₊ ((₀ , ₁₊ b') ∷ ps) ≡⟨ auto ⟩
  act ⟦ (b , λ ()) ⁻¹ ⟧ₘ ((₀ , ₁₊ b') ∷ ps) ≡⟨ lemma-M ₀ b ps ((b , λ ()) ⁻¹) ⟩
  (₀ * x⁻¹ , (₁₊ b') * x) ∷ ps ≡⟨ Eq.cong₂ (\ xx yy -> (xx , yy) ∷ ps) (*-zeroˡ x⁻¹) (lemma-⁻¹ʳ b {{nztoℕ {y = b} {neq0 = λ ()}}}) ⟩
  pZ ∷ ps ∎
  where
  open ≡-Reasoning
  x = ((b , λ ()) ⁻¹) .proj₁
  x⁻¹ = ((b , λ ()) ⁻¹ ⁻¹) .proj₁
  
lemma-abox (a@(₁₊ a') , b) neqI ps = begin
  act ⟦ (a , λ ()) ⁻¹ , HS^ -b/a ⟧ₘ₊ ((a , b) ∷ ps) ≡⟨ auto ⟩
  act ⟦ (a , λ ()) ⁻¹ ⟧ₘ (act ⟦ HS^ -b/a ⟧ₕₛ ((a , b) ∷ ps)) ≡⟨ Eq.cong (act ⟦ (a , λ ()) ⁻¹ ⟧ₘ) (lemma-HS-x -b/a a b ps) ⟩
  act ⟦ (a , λ ()) ⁻¹ ⟧ₘ ((- (b + a * -b/a) , a) ∷ ps) ≡⟨ Eq.cong (\ xx -> act ⟦ (a , λ ()) ⁻¹ ⟧ₘ ((xx , a) ∷ ps)) (Eq.trans (Eq.cong -_ aux) -0#≈0#) ⟩
  act ⟦ (a , λ ()) ⁻¹ ⟧ₘ ((₀ , a) ∷ ps) ≡⟨ lemma-M ₀ a ps ((a , λ ()) ⁻¹) ⟩
  (₀ * a⁻¹⁻¹  , a * a⁻¹) ∷ ps ≡⟨ Eq.cong (\ xx -> (₀ * a⁻¹⁻¹  , xx) ∷ ps) (lemma-⁻¹ʳ a {{nztoℕ {y = a} {neq0 = λ ()}}}) ⟩
  pZ ∷ ps ∎
  where
  open ≡-Reasoning
  a⁻¹ = ((a , λ ()) ⁻¹) .proj₁
  a⁻¹⁻¹ = ((a , λ ()) ⁻¹ ⁻¹) .proj₁
  -b/a = - b * a⁻¹
  aux : b + a * -b/a ≡ ₀
  aux = begin
    b + a * -b/a ≡⟨ Eq.cong (\ xx -> b + a * xx) (*-comm (- b) a⁻¹) ⟩
    b + a * (a⁻¹ * - b) ≡⟨ Eq.cong (b +_) (Eq.sym (*-assoc a a⁻¹ (- b))) ⟩
    b + a * a⁻¹ * - b ≡⟨ Eq.cong (\ xx -> b + xx * - b) (lemma-⁻¹ʳ a {{nztoℕ {y = a} {neq0 = λ ()}}}) ⟩
    b + ₁ * - b ≡⟨ Eq.cong (b +_) (*-identityˡ (- b)) ⟩
    b + - b ≡⟨ +-inverseʳ b ⟩
    ₀ ∎


lemma-dbox-IZ : ∀ d (t : Pauli n) -> act [ d ]ᵈ (pI ∷ pZ ∷ t) ≡ (pZ ∷ pI ∷ t)
lemma-dbox-IZ {n} (₀ , d) t = begin
  act [ ₀ , d ]ᵈ (pI ∷ pZ ∷ t) ≡⟨ auto ⟩
  act (Ex • CZ^ (- d)) (pI ∷ pZ ∷ t) ≡⟨ auto ⟩
  act Ex (act (CZ^ (- d)) (pI ∷ pZ ∷ t)) ≡⟨ auto ⟩
  act Ex ((₀ , ₀ + ₀ * (- d)) ∷ (₀ , ₁ + ₀ * (- d)) ∷ t) ≡⟨ Eq.cong (\ xx -> act Ex ((₀ , ₀ + xx) ∷ (₀ , ₁ + xx) ∷ t)) (*-zeroˡ (- d)) ⟩
  act Ex ((₀ , ₀ + ₀) ∷ (₀ , ₁ + ₀) ∷ t) ≡⟨ lemma-act-Ex pI pZ t ⟩
  (pZ ∷ pI ∷ t) ∎
  where
  open ≡-Reasoning

lemma-dbox-IZ {n} (c@(₁₊ c') , d) t = begin
  act [ ₁₊ c' , d ]ᵈ (pI ∷ pZ ∷ t) ≡⟨ auto ⟩
  act ([ ₀ , ₁ ]ᵈ • [ (₁₊ c' , d) , (λ ()) ]ᵃ) (pI ∷ pZ ∷ t) ≡⟨ auto ⟩
  act ([ ₀ , ₁ ]ᵈ • ⟦ (₁₊ c' , λ ()) ⁻¹ , HS^ -d/c ⟧ₘ₊) (pI ∷ pZ ∷ t) ≡⟨ Eq.cong (act ([ ₀ , ₁ ]ᵈ • ⟦ (₁₊ c' , λ ()) ⁻¹ ⟧ₘ)) (lemma-HS-x -d/c ₀ ₀ (pZ ∷ t)) ⟩
  act ([ ₀ , ₁ ]ᵈ • ⟦ (₁₊ c' , λ ()) ⁻¹ ⟧ₘ) ((- (₀ + ₀ * -d/c) , ₀) ∷ pZ ∷ t) ≡⟨ Eq.cong (act ([ ₀ , ₁ ]ᵈ • ⟦ (₁₊ c' , λ ()) ⁻¹ ⟧ₘ)) aux2 ⟩
  act ([ ₀ , ₁ ]ᵈ • ⟦ (₁₊ c' , λ ()) ⁻¹ ⟧ₘ) ((₀ , ₀) ∷ pZ ∷ t) ≡⟨ (Eq.cong (act ([ ₀ , ₁ ]ᵈ)) (lemma-M ₀ ₀ (pZ ∷ t) ((₁₊ c' , λ ()) ⁻¹))) ⟩
  act ([ ₀ , ₁ ]ᵈ) ((₀ * c⁻¹⁻¹ , ₀ * c⁻¹) ∷ pZ ∷ t) ≡⟨ (Eq.cong₂ (\ xx yy -> act ([ ₀ , ₁ ]ᵈ) ((xx , yy) ∷ pZ ∷ t)) (*-zeroˡ c⁻¹⁻¹) (*-zeroˡ c⁻¹)) ⟩
  act ([ ₀ , ₁ ]ᵈ) ((₀ , ₀) ∷ pZ ∷ t) ≡⟨ auto ⟩
  act Ex ((₀ , ₀ + ₀ * - ₁) ∷ (₀ , ₁ + ₀ * - ₁) ∷ t) ≡⟨ Eq.cong (\ xx -> act Ex ((₀ , ₀ + xx) ∷ (₀ , ₁ + xx) ∷ t)) (*-zeroˡ (- ₁)) ⟩
  act Ex ((₀ , ₀) ∷ (₀ , ₁ + ₀) ∷ t) ≡⟨ lemma-act-Ex pI pZ t ⟩
  (pZ ∷ pI ∷ t) ∎
  where
  open ≡-Reasoning
  c⁻¹ = ((c , λ ()) ⁻¹) .proj₁
  c⁻¹⁻¹ = ((c , λ ()) ⁻¹ ⁻¹) .proj₁
  -d/c = - d * c⁻¹
  aux : - (₀ + ₀ * -d/c) ≡ ₀
  aux = begin
    - (₀ + ₀ * -d/c) ≡⟨ Eq.cong -_ (Eq.cong (₀ +_) (*-zeroˡ -d/c)) ⟩
    - (₀ + ₀) ≡⟨ -0#≈0# ⟩
    ₀ ∎
  aux2 : _≡_ {A = Pauli (₂₊ n)} ((- (₀ + ₀ * -d/c) , ₀) ∷ pZ ∷ t) ((₀ , ₀) ∷ pZ ∷ t)
  aux2 = (Eq.cong (\ (xx : ℤ ₚ) -> (xx , ₀) ∷ pZ ∷ t) aux )
  

