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
open import Presentation.Tactics using ()
open import Data.Nat.Primality



module N.LM-Lemmas (p-2 : ℕ) (p-prime : Prime (2+ p-2))  where

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
open import N.LM p-2 p-prime
open Normal-Form1

private
  variable
    n : ℕ
    
open import N.Action p-2 p-prime
open import N.Action-Lemmas p-2 p-prime
open import Algebra.Properties.Ring (+-*-ring p-2)
open import N.NF2 p-2 p-prime
open LM2

lemma-dbox : ∀ q (t : Pauli n) -> act [ q ]ᵈ (q ∷ pX ∷ t) ≡ (pX ∷ pI ∷ t)
lemma-dbox {n} q@(c@₀ , d) t = begin
  act [ q ]ᵈ (q ∷ pX ∷ t) ≡⟨ auto ⟩
  act (Ex • CZ^ (- d)) (q ∷ pX ∷ t) ≡⟨ auto ⟩
  act Ex ((c , d + ₁ * - d) ∷ (₁ , ₀ + c * - d) ∷ t) ≡⟨ Eq.cong₂ (\ xx yy -> act Ex ((c , xx) ∷ (₁ , yy) ∷ t)) (Eq.trans (Eq.cong (d +_) (*-identityˡ (- d)) ) (+-inverseʳ d)) (Eq.cong (₀ +_) (*-zeroˡ (- d))) ⟩
  act Ex ((c , ₀) ∷ (₁ , ₀) ∷ t) ≡⟨ lemma-act-Ex pI pX t ⟩
  (pX ∷ pI ∷ t) ∎
  where
  open ≡-Reasoning
lemma-dbox {n} q@(c@(₁₊ c') , d) t = begin
  act {₂₊ n} ([ ₀ , ₁ ]ᵈ • [ (c , d) , (λ ()) ]ᵃ) (q ∷ pX ∷ t) ≡⟨ Eq.cong (act {₂₊ n} ([ ₀ , ₁ ]ᵈ)) (lemma-abox q (λ ()) (pX ∷ t)) ⟩
  act {₂₊ n} ([ ₀ , ₁ ]ᵈ) (pZ ∷ pX ∷ t) ≡⟨ auto ⟩
  act {₂₊ n} (Ex • CZ^ (- ₁)) (pZ ∷ pX ∷ t) ≡⟨ auto ⟩
  act {₂₊ n} (Ex) ((₀ , ₁ + ₁ * - ₁) ∷ (₁ , ₀ + ₀ * - ₁) ∷ t) ≡⟨ Eq.cong₂ (λ xx yy → act {₂₊ n} Ex ((₀ , xx) ∷ (₁ , yy) ∷ t)) (Eq.cong (₁ +_) (*-identityˡ (- ₁))) (Eq.cong (₀ +_) (*-zeroˡ (- ₁))) ⟩
  act {₂₊ n} (Ex) ((₀ , ₁ + - ₁) ∷ (₁ , ₀ + ₀) ∷ t) ≡⟨ Eq.cong (act {₂₊ n} Ex) aux ⟩
  act {₂₊ n} (Ex) ((₀ , ₀) ∷ (₁ , ₀) ∷ t) ≡⟨ lemma-act-Ex pI pX t ⟩
  (pX ∷ pI ∷ t) ∎
  where
  open ≡-Reasoning
  c⁻¹ = ((c , λ ()) ⁻¹) .proj₁
  -d/c = - d * c⁻¹
  aux : _≡_ {A = Pauli (₂₊ n) }((₀ , ₁ + - ₁) ∷ (₁ , ₀ + ₀) ∷ t) ((₀ , ₀) ∷ (₁ , ₀) ∷ t)
  aux = begin
    ((₀ , ₁ + - ₁) ∷ (₁ , ₀ + ₀) ∷ t) ≡⟨ Eq.cong (\ xx -> ((₀ , xx) ∷ (₁ , ₀) ∷ t)) (+-inverseʳ ₁) ⟩
    ((₀ , ₀) ∷ (₁ , ₀) ∷ t) ∎



lemma-dbox-XZ : ∀ q e (t : Pauli n) -> act [ q ]ᵈ (q ∷ pXZ e ∷ t) ≡ (pXZ e ∷ pI ∷ t)
lemma-dbox-XZ {n} q@(c@₀ , d) e t = begin
  act [ q ]ᵈ (q ∷ pXZ e ∷ t) ≡⟨ auto ⟩
  act (Ex • CZ^ (- d)) (q ∷ pXZ e ∷ t) ≡⟨ auto ⟩
  act Ex ((c , d + ₁ * - d) ∷ (₁ , e + c * - d) ∷ t) ≡⟨ Eq.cong₂ (\ xx yy -> act Ex ((c , xx) ∷ (₁ , yy) ∷ t)) (Eq.trans (Eq.cong (d +_) (*-identityˡ (- d)) ) (+-inverseʳ d)) (Eq.trans (Eq.cong (e +_) (*-zeroˡ (- d))) (+-identityʳ e)) ⟩
  act Ex ((c , ₀) ∷ (₁ , e) ∷ t) ≡⟨ lemma-act-Ex pI (pXZ e) t ⟩
  (pXZ e ∷ pI ∷ t) ∎
  where
  open ≡-Reasoning
lemma-dbox-XZ {n} q@(c@(₁₊ c') , d) e t = begin
  act {₂₊ n} ([ ₀ , ₁ ]ᵈ • [ (c , d) , (λ ()) ]ᵃ) (q ∷ pXZ e ∷ t) ≡⟨ Eq.cong (act {₂₊ n} ([ ₀ , ₁ ]ᵈ)) (lemma-abox q (λ ()) (pXZ e ∷ t)) ⟩
  act {₂₊ n} ([ ₀ , ₁ ]ᵈ) (pZ ∷ pXZ e ∷ t) ≡⟨ auto ⟩
  act {₂₊ n} (Ex • CZ^ (- ₁)) (pZ ∷ pXZ e ∷ t) ≡⟨ auto ⟩
  act {₂₊ n} (Ex) ((₀ , ₁ + ₁ * - ₁) ∷ (₁ , e + ₀ * - ₁) ∷ t) ≡⟨ Eq.cong₂ (λ xx yy → act {₂₊ n} Ex ((₀ , xx) ∷ (₁ , yy) ∷ t)) (Eq.cong (₁ +_) (*-identityˡ (- ₁))) (Eq.cong (e +_) (*-zeroˡ (- ₁))) ⟩
  act {₂₊ n} (Ex) ((₀ , ₁ + - ₁) ∷ (₁ , e + ₀) ∷ t) ≡⟨ Eq.cong (act {₂₊ n} Ex) aux ⟩
  act {₂₊ n} (Ex) ((₀ , ₀) ∷ (₁ , e) ∷ t) ≡⟨ lemma-act-Ex pI (pXZ e) t ⟩
  (pXZ e ∷ pI ∷ t) ∎
  where
  open ≡-Reasoning
  c⁻¹ = ((c , λ ()) ⁻¹) .proj₁
  -d/c = - d * c⁻¹
  aux : _≡_ {A = Pauli (₂₊ n) }((₀ , ₁ + - ₁) ∷ (₁ , e + ₀) ∷ t) ((₀ , ₀) ∷ (₁ , e) ∷ t)
  aux = begin
    ((₀ , ₁ + - ₁) ∷ (₁ , e + ₀) ∷ t) ≡⟨ Eq.cong₂ (\ xx yy -> ((₀ , xx) ∷ (₁ , yy) ∷ t)) (+-inverseʳ ₁) (+-identityʳ e) ⟩
    ((₀ , ₀) ∷ (₁ , e) ∷ t) ∎


lemma-bbox : ∀ p (t : Pauli n) -> act [ p ]ᵇ (pZ ∷ p ∷ t) ≡ (pI ∷ pZ ∷ t)
lemma-bbox p@(₀ , ₀) t = begin
  act [ p ]ᵇ (pZ ∷ p ∷ t) ≡⟨ lemma-act-Ex pZ pI t ⟩
  (pI ∷ pZ ∷ t) ∎
  where
  open ≡-Reasoning
lemma-bbox p@(a@₀ , b@(₁₊ b')) t = begin
  act (Ex • CX • [ (a , b) , (λ ()) ]ᵃ ↑) (pZ ∷ p ∷ t) ≡⟨ Eq.cong (act (Ex • CX)) (lemma-act-↑ [ (a , b) , (λ ()) ]ᵃ pZ (p ∷ t)) ⟩
  act (Ex • CX) (pZ ∷ act [ (a , b) , (λ ()) ]ᵃ (p ∷ t)) ≡⟨ Eq.cong (\ xx -> act (Ex • CX) (pZ ∷ xx)) (lemma-abox ((a , b)) (λ ()) t) ⟩
  act (Ex • CX) (pZ ∷ pZ ∷ t) ≡⟨ Eq.cong (act Ex) (lemma-act-CX pZ pZ t) ⟩
  act (Ex) ((₀ , ₁) ∷ (₀ , ₁ + - ₁) ∷ t) ≡⟨ Eq.cong (\ xx -> act (Ex) ((₀ , ₁) ∷ (₀ , xx) ∷ t)) (+-inverseʳ ₁) ⟩
  act (Ex) ((₀ , ₁) ∷ (₀ , ₀) ∷ t) ≡⟨ lemma-act-Ex pZ pI t ⟩
  (pI ∷ pZ ∷ t) ∎
  where
  open ≡-Reasoning
lemma-bbox p@(a@(₁₊ a') , b) t = begin
  act (Ex • CX • [ (a , b) , (λ ()) ]ᵃ ↑) (pZ ∷ p ∷ t) ≡⟨ Eq.cong (act (Ex • CX)) (lemma-act-↑ [ (a , b) , (λ ()) ]ᵃ pZ (p ∷ t)) ⟩
  act (Ex • CX) (pZ ∷ act [ (a , b) , (λ ()) ]ᵃ (p ∷ t)) ≡⟨ Eq.cong (\ xx -> act (Ex • CX) (pZ ∷ xx)) (lemma-abox ((a , b)) (λ ()) t) ⟩
  act (Ex • CX) (pZ ∷ pZ ∷ t) ≡⟨ Eq.cong (act Ex) (lemma-act-CX pZ pZ t) ⟩
  act (Ex) ((₀ , ₁) ∷ (₀ , ₁ + - ₁) ∷ t) ≡⟨ Eq.cong (\ xx -> act (Ex) ((₀ , ₁) ∷ (₀ , xx) ∷ t)) (+-inverseʳ ₁) ⟩
  act (Ex) ((₀ , ₁) ∷ (₀ , ₀) ∷ t) ≡⟨ lemma-act-Ex pZ pI t ⟩
  (pI ∷ pZ ∷ t) ∎
  where
  open ≡-Reasoning

lemma-bboxes : ∀ (ps : Pauli n) -> act [ ps ]ᵛᵇ (pZ ∷ ps) ≡ pZₙ
lemma-bboxes {0} [] = auto
lemma-bboxes {₁₊ n} ps@(b ∷ vb) = begin
  act ([ vb ]ᵛᵇ ↑ • [ b ]ᵇ) (pZ ∷ ps) ≡⟨ Eq.cong (act ([ vb ]ᵛᵇ ↑)) (lemma-bbox b vb) ⟩
  act ([ vb ]ᵛᵇ ↑) (pI ∷ pZ ∷ vb) ≡⟨ lemma-act-↑ [ vb ]ᵛᵇ pI (pZ ∷ vb) ⟩
  pI ∷ act ([ vb ]ᵛᵇ) (pZ ∷ vb) ≡⟨ Eq.cong (pI ∷_) (lemma-bboxes vb) ⟩
  pZₙ ∎
  where
  open ≡-Reasoning

lemma-dboxes : ∀ (ps : Pauli n) -> act [ ps ]ᵛᵈ (ps ∷ʳ pX) ≡ pX₀
lemma-dboxes {0} [] = auto
lemma-dboxes {₁₊ n} ps@(d ∷ vd) = begin
  act [ ps ]ᵛᵈ (ps ∷ʳ pX) ≡⟨ auto ⟩
  act ([ d ]ᵈ • [ vd ]ᵛᵈ ↑) (d ∷ (vd ∷ʳ pX)) ≡⟨ Eq.cong (act ([ d ]ᵈ)) (lemma-act-↑ [ vd ]ᵛᵈ d (vd ∷ʳ pX)) ⟩
  act ([ d ]ᵈ) (d ∷ (act [ vd ]ᵛᵈ (vd ∷ʳ pX))) ≡⟨ Eq.cong (\ xx -> act ([ d ]ᵈ) (d ∷ xx)) (lemma-dboxes vd) ⟩
  act ([ d ]ᵈ) (d ∷ pX₀) ≡⟨ lemma-dbox d pIₙ ⟩
  pX₀ ∎
  where
  open ≡-Reasoning


lemma-dboxes-Z : ∀ (ps : Pauli n) -> act [ ps ]ᵛᵈ (pIₙ {n} ∷ʳ pZ) ≡ pZ₀
lemma-dboxes-Z {0} [] = auto
lemma-dboxes-Z {₁₊ n} ps@(d ∷ vd) = begin
  act [ ps ]ᵛᵈ (pIₙ ∷ʳ pZ) ≡⟨ auto ⟩
  act ([ d ]ᵈ • [ vd ]ᵛᵈ ↑) (pI ∷ (pIₙ ∷ʳ pZ)) ≡⟨ Eq.cong (act ([ d ]ᵈ)) (lemma-act-↑ [ vd ]ᵛᵈ pI (pIₙ ∷ʳ pZ)) ⟩
  act ([ d ]ᵈ) (pI ∷ (act [ vd ]ᵛᵈ (pIₙ ∷ʳ pZ))) ≡⟨ Eq.cong (\ xx -> act ([ d ]ᵈ) (pI ∷ xx)) (lemma-dboxes-Z vd) ⟩
  act ([ d ]ᵈ) (pI ∷ pZ₀) ≡⟨ lemma-dbox-IZ d pIₙ ⟩
  pZ₀ ∎
  where
  open ≡-Reasoning

lemma-ebox : ∀ e y (ps : Pauli n) →
  act [ e ]ᵉ ((₀ , y ) ∷ ps) ≡ (₀ , y ) ∷ ps
lemma-ebox e y ps = begin
  act [ e ]ᵉ ((₀ , y ) ∷ ps) ≡⟨ auto ⟩
  act (S^ e) ((₀ , y ) ∷ ps) ≡⟨ auto ⟩
  (₀ , y + ₀ * e ) ∷ ps ≡⟨ Eq.cong (\ xx -> (₀ , xx) ∷ ps) (Eq.trans (Eq.cong (y +_) (*-zeroˡ e)) (+-identityʳ y)) ⟩
  (₀ , y ) ∷ ps ∎
  where
  open ≡-Reasoning

e-after-abox-q : ∀ (p q : Pauli1) (neqI : p ≢ pI) -> E
e-after-abox-q p@(a@₀ , b@₀) q@(c , d) neqI = ⊥-elim (neqI auto)
e-after-abox-q p@(a@₀ , b@(₁₊ _)) q@(c , d) neqI = d * b⁻¹
  where
  open ≡-Reasoning
  b⁻¹ = ((b , λ ()) ⁻¹) .proj₁

e-after-abox-q p@(a@(₁₊ _) , b) q@(c , d) neqI = c * a⁻¹
  where
  a' = (a , λ ()) ⁻¹
  a⁻¹ = a' .proj₁

lemma-abox-X : ∀ p q (neqI : p ≢ pI)(ps : Pauli n) →
  let e = e-after-abox-q p q neqI in
  act [ p , neqI ]ᵃ (q ∷ ps) ≡ ((sform1 p q , e) ∷ ps)
lemma-abox-X p@(₀ , ₀) q@(c , d) neqI ps = ⊥-elim (neqI auto)
lemma-abox-X p@(a@₀ , b@(₁₊ _)) q@(c , d) neqI ps = claim
  where
  open ≡-Reasoning
  x' = (b , λ ()) ⁻¹
  x = (x' .proj₁)
  b⁻¹ = x
  x⁻¹ = ((x' ⁻¹) .proj₁)
  
  e : E
  e = e-after-abox-q p q neqI
  claim : act [ p , neqI ]ᵃ (q ∷ ps) ≡ ((sform1 p q , e) ∷ ps)
  claim = begin
    act [ p , neqI ]ᵃ (q ∷ ps) ≡⟨ auto ⟩
    act ⟦ (b , λ ()) ⁻¹ , ε ⟧ₘ₊ (q ∷ ps) ≡⟨ lemma-M c d ps ((b , λ ()) ⁻¹) ⟩
    ((c * x⁻¹ , d * x) ∷ ps) ≡⟨ Eq.cong (λ xx → (c * xx , d * x) ∷ ps) (inv-involutive (b , λ ())) ⟩
    ((c * b , d * x) ∷ ps) ≡⟨ Eq.cong (\ xx -> ((xx , d * x) ∷ ps)) (Eq.sym (+-identityˡ (c * b))) ⟩
    ((₀ + c * b , d * b⁻¹) ∷ ps) ≡⟨ Eq.cong (\ xx -> ((xx + c * b , d * b⁻¹) ∷ ps)) (Eq.sym (*-zeroˡ d)) ⟩
    ((₀ * d + c * b , d * b⁻¹) ∷ ps) ≡⟨ Eq.cong (λ xx → (xx * d + c * b , d * b⁻¹) ∷ ps) (Eq.sym -0#≈0#) ⟩
    ((- a * d + c * b , d * b⁻¹) ∷ ps) ≡⟨ auto ⟩
    ((sform1 p q , d * b⁻¹) ∷ ps) ∎

lemma-abox-X p@(a@(₁₊ _) , b) q@(c , d) neqI ps = claim
  where
  open ≡-Reasoning
  a' = (a , λ ()) ⁻¹
  a⁻¹ = a' .proj₁
  -b/a = - b * a⁻¹
  a⁻¹⁻¹ = ((a' ⁻¹) .proj₁)
  e : E
  e = e-after-abox-q p q neqI
  claim : act [ p , neqI ]ᵃ (q ∷ ps) ≡ (sform1 p q , c * a⁻¹) ∷ ps
  claim = begin
    act [ p , neqI ]ᵃ (q ∷ ps) ≡⟨ auto ⟩
    act ⟦ (a , λ ()) ⁻¹ , HS^ -b/a ⟧ₘ₊ (q ∷ ps) ≡⟨ Eq.cong (act ⟦ (a , λ ()) ⁻¹ ⟧ₘ) (lemma-HS-x -b/a c d ps) ⟩
    act ⟦ (a , λ ()) ⁻¹ ⟧ₘ ((- (d + c * -b/a) , c) ∷ ps) ≡⟨ lemma-M (- (d + c * -b/a)) c ps ((a , λ ()) ⁻¹) ⟩
    ((- (d + c * -b/a) * a⁻¹⁻¹ , c * a⁻¹) ∷ ps) ≡⟨ Eq.cong (\ xx -> ((- (d + c * -b/a) * xx , c * a⁻¹) ∷ ps)) (inv-involutive (a , λ ())) ⟩
    ((- (d + c * -b/a) * a , c * a⁻¹) ∷ ps) ≡⟨ Eq.cong (\ xx -> ((xx * a , c * a⁻¹) ∷ ps)) (Eq.sym (-‿+-comm d (c * -b/a))) ⟩
    (((- d + - (c * -b/a)) * a , c * a⁻¹) ∷ ps) ≡⟨ Eq.cong (\ xx -> (((- d + xx) * a , c * a⁻¹) ∷ ps)) (-‿distribʳ-* c -b/a) ⟩
    (((- d + (c * - -b/a)) * a , c * a⁻¹) ∷ ps) ≡⟨ Eq.cong (\ xx -> (((- d + (c * xx)) * a , c * a⁻¹) ∷ ps)) (-‿distribˡ-* (- b) a⁻¹) ⟩
    (((- d + (c * (- - b * a⁻¹))) * a , c * a⁻¹) ∷ ps) ≡⟨ Eq.cong (\ xx -> (((- d + (c * (xx * a⁻¹))) * a , c * a⁻¹) ∷ ps)) (-‿involutive b) ⟩
    (((- d + (c * (b * a⁻¹))) * a , c * a⁻¹) ∷ ps) ≡⟨ Eq.cong (λ xx → ((- d + xx) * a , c * a⁻¹) ∷ ps) (Eq.sym (*-assoc c b a⁻¹)) ⟩
    (((- d + (c * b * a⁻¹)) * a , c * a⁻¹) ∷ ps) ≡⟨ Eq.cong (\ xx -> ((xx , c * a⁻¹) ∷ ps)) (*-distribʳ-+ a (- d) (c * b * a⁻¹)) ⟩
    ((- d * a + (c * b * a⁻¹) * a) , c * a⁻¹) ∷ ps ≡⟨ Eq.cong (\ xx -> ((- d * a + xx) , c * a⁻¹) ∷ ps) (*-assoc (c * b) a⁻¹ a) ⟩
    ((- d * a + (c * b * (a⁻¹ * a))) , c * a⁻¹) ∷ ps ≡⟨ Eq.cong (\ xx -> ((- d * a + (c * b * xx)) , c * a⁻¹) ∷ ps) (lemma-⁻¹ˡ a {{nztoℕ {y = a} {neq0 = λ ()}}}) ⟩
    ((- d * a + (c * b * ₁)) , c * a⁻¹) ∷ ps ≡⟨ Eq.cong (λ xx → (- d * a + xx , c * a⁻¹) ∷ ps) (*-identityʳ (c * b)) ⟩
    ((- d * a + (c * b)) , c * a⁻¹) ∷ ps ≡⟨ Eq.cong (\ xx -> ((xx + (c * b)) , c * a⁻¹) ∷ ps) (Eq.sym (-‿distribˡ-* d a)) ⟩
    ((- (d * a) + (c * b)) , c * a⁻¹) ∷ ps ≡⟨ Eq.cong (λ xx → (- xx + c * b , c * a⁻¹) ∷ ps) (*-comm d a) ⟩
    ((- (a * d) + (c * b)) , c * a⁻¹) ∷ ps ≡⟨ Eq.cong (λ xx → (xx + c * b , c * a⁻¹) ∷ ps) (-‿distribˡ-* a d) ⟩
    (((- a * d) + (c * b)) , c * a⁻¹) ∷ ps ≡⟨ auto ⟩
    (sform1 p q , c * a⁻¹) ∷ ps ∎



e-after-bbox-pq : ∀ (p@(c , d) q : Pauli1) -> E
e-after-bbox-pq p@(c , d) (₀ , ₀) = ₀
e-after-bbox-pq p@(c , d) _ = ₁ + - d

lemma-bbox-X : ∀ (p@(c , d) q : Pauli1) (ps : Pauli n) ->
  act [ q ]ᵇ (p ∷ q ∷ ps) ≡ (₀ , e-after-bbox-pq p q) ∷ p ∷ ps

lemma-bbox-X p@(c , d) q@(a@₀ , b@₀) ps = lemma-act-Ex p pI ps

lemma-bbox-X p@(c , d) q@(a@₀ , b@(₁₊ _)) ps = begin
  act (Ex • CX • [ q , (λ ()) ]ᵃ ↑) (p ∷ q ∷ ps) ≡⟨ Eq.cong (act (Ex • CX)) (lemma-act-↑ [ q , (λ ()) ]ᵃ p (q ∷ ps)) ⟩
  act (Ex • CX) (p ∷ act [ q , (λ ()) ]ᵃ (q ∷ ps)) ≡⟨ Eq.cong (\ xx -> act (Ex • CX) (p ∷ xx)) (lemma-abox q (λ ()) ps) ⟩
  act (Ex • CX) (p ∷ pZ ∷ ps) ≡⟨ Eq.cong (act Ex) (lemma-act-CX p pZ ps) ⟩
  act (Ex) ((c + ₀ , d) ∷ (₀ , ₁ + - d) ∷ ps) ≡⟨ Eq.cong (\ xx -> act (Ex) ((xx , d) ∷ (₀ , ₁ + - d) ∷ ps)) (+-identityʳ c) ⟩
  act (Ex) ((c , d) ∷ (₀ , ₁ + - d) ∷ ps) ≡⟨ lemma-act-Ex p ((₀ , ₁ + - d)) ps ⟩
  (₀ , ₁ + - d) ∷ (c , d) ∷ ps  ∎
  where
  open ≡-Reasoning
lemma-bbox-X p@(c , d) q@(a@(₁₊ _) , b)  ps = begin
  act (Ex • CX • [ q , (λ ()) ]ᵃ ↑) (p ∷ q ∷ ps) ≡⟨ Eq.cong (act (Ex • CX)) (lemma-act-↑ [ q , (λ ()) ]ᵃ p (q ∷ ps)) ⟩
  act (Ex • CX) (p ∷ act [ q , (λ ()) ]ᵃ (q ∷ ps)) ≡⟨ Eq.cong (\ xx -> act (Ex • CX) (p ∷ xx)) (lemma-abox q (λ ()) ps) ⟩
  act (Ex • CX) (p ∷ pZ ∷ ps) ≡⟨ Eq.cong (act Ex) (lemma-act-CX p pZ ps) ⟩
  act (Ex) ((c + ₀ , d) ∷ (₀ , ₁ + - d) ∷ ps) ≡⟨ Eq.cong (\ xx -> act (Ex) ((xx , d) ∷ (₀ , ₁ + - d) ∷ ps)) (+-identityʳ c) ⟩
  act (Ex) ((c , d) ∷ (₀ , ₁ + - d) ∷ ps) ≡⟨ lemma-act-Ex p ((₀ , ₁ + - d)) ps ⟩
  (₀ , ₁ + - d) ∷ (c , d) ∷ ps  ∎
  where
  open ≡-Reasoning


lemma-bboxes-X : ∀ p (ps : Pauli n) -> act [ ps ]ᵛᵇ (p ∷ ps) ≡ Vec.map (\ q -> (₀ , e-after-bbox-pq p q)) ps ∷ʳ p
lemma-bboxes-X {0} p [] = auto
lemma-bboxes-X {₁₊ n} p ps@(b ∷ vb) = begin
  act ([ vb ]ᵛᵇ ↑ • [ b ]ᵇ) (p ∷ ps) ≡⟨ Eq.cong (act ([ vb ]ᵛᵇ ↑)) (lemma-bbox-X p b vb) ⟩
  act ([ vb ]ᵛᵇ ↑) ((₀ , e-after-bbox-pq p q) ∷ p ∷ vb) ≡⟨ lemma-act-↑ [ vb ]ᵛᵇ ((₀ , e-after-bbox-pq p q)) (p ∷ vb) ⟩
  (₀ , e-after-bbox-pq p q) ∷ act ([ vb ]ᵛᵇ) (p ∷ vb) ≡⟨ Eq.cong ((₀ , e-after-bbox-pq p q) ∷_) (lemma-bboxes-X p vb) ⟩
  Vec.map (\ q -> (₀ , e-after-bbox-pq p q)) ps ∷ʳ p ∎
  where
  open ≡-Reasoning
  q = b

act-bbox : ∀ (xy p q : Pauli1) (ps : Pauli n) -> Pauli (₂₊ n)
act-bbox xy@(₀ , ₀) p q ps = q ∷ p ∷ ps
act-bbox xy@(₀ , ₁₊ _) p@(a' , b') q ps = (sq , ea + - b') ∷ (a' + sq , b') ∷ ps
  where
  ea = e-after-abox-q xy q (λ ())
  sq = sform1 xy q
act-bbox xy@(₁₊ _ , _) p@(a' , b') q ps = (sq , ea + - b') ∷ (a' + sq , b') ∷ ps
  where
  ea = e-after-abox-q xy q (λ ())
  sq = sform1 xy q
  


lemma-bbox-X' : ∀ xy (p@(a' , b') q@(c , d) : Pauli1) (ps : Pauli n) ->
  act [ xy ]ᵇ (p ∷ q ∷ ps) ≡ act-bbox xy p q ps
lemma-bbox-X' xy@(x@₀ , y@₀) p q@(c , d)  ps = begin
  act [ xy ]ᵇ (p ∷ q ∷ ps) ≡⟨ lemma-act-Ex p q ps ⟩
  (q ∷ p ∷ ps)  ∎
  where
  open ≡-Reasoning
lemma-bbox-X' xy@(a@₀ , b@(₁₊ _)) p@(a' , b') q@(c , d) ps = begin
  act (Ex • CX • [ (a , b) , (λ ()) ]ᵃ ↑) (p ∷ q ∷ ps) ≡⟨ Eq.cong (act (Ex • CX)) (lemma-act-↑ [ (a , b) , (λ ()) ]ᵃ p (q ∷ ps)) ⟩
  act (Ex • CX) (p ∷ act  [ (a , b) , (λ ()) ]ᵃ (q ∷ ps)) ≡⟨ Eq.cong (\ xx -> act (Ex • CX) (p ∷ xx)) (lemma-abox-X xy q (λ ()) (ps)) ⟩
  act (Ex • CX) (p ∷ (sq , ea) ∷ ps) ≡⟨ Eq.cong (act Ex) (lemma-act-CX p ((sq , ea)) ps) ⟩
  act (Ex) ((a' + sq , b') ∷ (sq , ea + - b') ∷ ps) ≡⟨ lemma-act-Ex ((a' + sq , b') ) ((sq , ea + - b')) ps ⟩
  (sq , ea + - b') ∷ (a' + sq , b') ∷ ps ∎
  where
  open ≡-Reasoning
  ea = e-after-abox-q xy q (λ ())
  sq = sform1 xy q
lemma-bbox-X' xy@(a@(₁₊ _) , b) p@(a' , b') q@(c , d) ps = begin
  act (Ex • CX • [ (a , b) , (λ ()) ]ᵃ ↑) (p ∷ q ∷ ps) ≡⟨ Eq.cong (act (Ex • CX)) (lemma-act-↑ [ (a , b) , (λ ()) ]ᵃ p (q ∷ ps)) ⟩
  act (Ex • CX) (p ∷ act  [ (a , b) , (λ ()) ]ᵃ (q ∷ ps)) ≡⟨ Eq.cong (\ xx -> act (Ex • CX) (p ∷ xx)) (lemma-abox-X xy q (λ ()) (ps)) ⟩
  act (Ex • CX) (p ∷ (sq , ea) ∷ ps) ≡⟨ Eq.cong (act Ex) (lemma-act-CX p ((sq , ea)) ps) ⟩
  act (Ex) ((a' + sq , b') ∷ (sq , ea + - b') ∷ ps) ≡⟨ lemma-act-Ex ((a' + sq , b') ) ((sq , ea + - b')) ps ⟩
  (sq , ea + - b') ∷ (a' + sq , b') ∷ ps ∎
  where
  open ≡-Reasoning
  ea = e-after-abox-q xy q (λ ())
  sq = sform1 xy q


act-bbox' : ∀ (xy p q : Pauli1) -> (Pauli1 × Pauli1)
act-bbox' xy@(₀ , ₀) p q = (q , p)
act-bbox' xy@(₀ , ₁₊ _) p@(a' , b') q = (sq , ea + - b') , (a' + sq , b')
  where
  ea = e-after-abox-q xy q (λ ())
  sq = sform1 xy q
act-bbox' xy@(₁₊ _ , _) p@(a' , b') q = (sq , ea + - b') , (a' + sq , b') 
  where
  ea = e-after-abox-q xy q (λ ())
  sq = sform1 xy q


act-bboxes : ∀ (p0 : Pauli1) (ps qs : Pauli n) -> Pauli (₁₊ n)
act-bboxes p0 [] [] = p0 ∷ []
act-bboxes p0 (p1 ∷ ps) (q1 ∷ qs) = p1' ∷ act-bboxes q1' ps qs
  where
  t = act-bbox p1 p0 q1 qs
  p1' = Vec.head t
  q1' = Vec.head (Vec.tail t)



act-bbox-fix-tail : ∀ xy (p q : Pauli1) (ps : Pauli n) -> Vec.tail (Vec.tail (act-bbox xy p q ps)) ≡ ps
act-bbox-fix-tail xy@(₀ , ₀) p q ps = auto
act-bbox-fix-tail xy@(₀ , ₁₊ _) p q ps = auto
act-bbox-fix-tail xy@(₁₊ _ , _) p q ps = auto

lemma-bboxes-X' : ∀ q (ps qs : Pauli n) -> act [ ps ]ᵛᵇ (q ∷ qs) ≡ act-bboxes q ps qs
lemma-bboxes-X' q [] [] = auto
lemma-bboxes-X' q (x ∷ ps) (x₁ ∷ qs) with act-bbox x q x₁ qs | inspect (act-bbox x q x₁) qs
... | (p1' ∷  q1' ∷ qs') | [ eq ]' = begin
  act [ x ∷ ps ]ᵛᵇ (q ∷ x₁ ∷ qs) ≡⟨ auto ⟩
  act ([ ps ]ᵛᵇ ↑ • [ x ]ᵇ) (q ∷ x₁ ∷ qs) ≡⟨ auto ⟩
  act ([ ps ]ᵛᵇ ↑) (act [ x ]ᵇ (q ∷ x₁ ∷ qs)) ≡⟨ Eq.cong (act ([ ps ]ᵛᵇ ↑)) (lemma-bbox-X' x q x₁ qs ) ⟩
  act ([ ps ]ᵛᵇ ↑) (act-bbox x q x₁ qs) ≡⟨ Eq.cong (act ([ ps ]ᵛᵇ ↑))  eq ⟩
  act ([ ps ]ᵛᵇ ↑) (p1' ∷ q1' ∷ qs') ≡⟨ lemma-act-↑ [ ps ]ᵛᵇ p1' (q1' ∷ qs') ⟩
  p1' ∷ act ([ ps ]ᵛᵇ) (q1' ∷ qs') ≡⟨ Eq.cong (p1' ∷_) (lemma-bboxes-X' q1' ps qs') ⟩
  p1' ∷ act-bboxes q1' ps qs' ≡⟨ Eq.cong (\ xx -> p1' ∷ act-bboxes q1' ps xx) aux ⟩
  p1' ∷ act-bboxes q1' ps qs ∎
  where
  open ≡-Reasoning
  aux : qs' ≡ qs
  aux = begin
    qs' ≡⟨ Eq.sym (Eq.cong Vec.tail (Eq.cong Vec.tail eq)) ⟩
    Vec.tail (Vec.tail (act-bbox x q x₁ qs)) ≡⟨ act-bbox-fix-tail x q x₁ qs ⟩
    qs ∎


lemma-dboxes-XZ : ∀ e (ps : Pauli n) -> act [ ps ]ᵛᵈ (ps ∷ʳ pXZ e) ≡ pX₀Z₀ e
lemma-dboxes-XZ {0} e [] = auto
lemma-dboxes-XZ {₁₊ n} e ps@(d ∷ vd) = begin
  act [ ps ]ᵛᵈ (ps ∷ʳ pXZ e) ≡⟨ auto ⟩
  act ([ d ]ᵈ • [ vd ]ᵛᵈ ↑) (d ∷ (vd ∷ʳ pXZ e)) ≡⟨ Eq.cong (act ([ d ]ᵈ)) (lemma-act-↑ [ vd ]ᵛᵈ d (vd ∷ʳ pXZ e)) ⟩
  act ([ d ]ᵈ) (d ∷ (act [ vd ]ᵛᵈ (vd ∷ʳ pXZ e))) ≡⟨ Eq.cong (\ xx -> act ([ d ]ᵈ) (d ∷ xx)) (lemma-dboxes-XZ e vd) ⟩
  act ([ d ]ᵈ) (d ∷ pX₀Z₀ e) ≡⟨ lemma-dbox-XZ d e pIₙ ⟩
  pX₀Z₀ e ∎
  where
  open ≡-Reasoning

open Normal-Form1

lemma-act-bboxes-last : ∀ (q@(a' , b') : Pauli1) (ps qs : Pauli n) -> Vec.last (act [ ps ]ᵛᵇ (q ∷ qs)) ≡ (a' + sform ps qs , b')
lemma-act-bboxes-last q@(a' , b') [] [] = Eq.cong ((_, b')) (Eq.sym (+-identityʳ a'))
lemma-act-bboxes-last q@(a' , b') (x@(₀ , ₀) ∷ ps) (y ∷ qs) = begin
  Vec.last (act ([ ps ]ᵛᵇ ↑ • [ x ]ᵇ) (q ∷ y ∷ qs)) ≡⟨ auto ⟩
  Vec.last (act ([ ps ]ᵛᵇ ↑) (act [ x ]ᵇ (q ∷ y ∷ qs))) ≡⟨ Eq.cong (\ xx -> Vec.last (act ([ ps ]ᵛᵇ ↑) (xx))) (lemma-bbox-X' x q y qs) ⟩
  Vec.last (act ([ ps ]ᵛᵇ ↑) (act-bbox x q y qs)) ≡⟨ auto ⟩
  Vec.last (act ([ ps ]ᵛᵇ ↑) (y ∷ q ∷ qs)) ≡⟨ Eq.cong Vec.last  (lemma-act-↑ [ ps ]ᵛᵇ y (q ∷ qs)) ⟩
  Vec.last (y ∷ act ([ ps ]ᵛᵇ) (q ∷ qs)) ≡⟨ auto ⟩
  Vec.last (act ([ ps ]ᵛᵇ) (q ∷ qs)) ≡⟨ lemma-act-bboxes-last q ps qs ⟩
  (a' + sform (ps) (qs) , b')  ≡⟨ Eq.cong (\ xx -> (a' + xx , b')) (Eq.sym (+-identityˡ (sform ps qs))) ⟩
  (a' + (₀ + sform ps qs) , b')  ≡⟨ Eq.cong (\ xx -> (a' + (xx + sform ps qs) , b')) (Eq.sym (sform-pI-q=0 y)) ⟩
  (a' + (sform1 x y + sform ps qs) , b')  ≡⟨ auto ⟩
  (a' + sform (x ∷ ps) (y ∷ qs) , b') ∎
  where
  open ≡-Reasoning


lemma-act-bboxes-last q@(a' , b') (x@(₀ , ₁₊ _) ∷ ps) (y ∷ qs) = begin
  Vec.last (act ([ ps ]ᵛᵇ ↑ • [ x ]ᵇ) (q ∷ y ∷ qs)) ≡⟨ auto ⟩
  Vec.last (act ([ ps ]ᵛᵇ ↑) (act [ x ]ᵇ (q ∷ y ∷ qs))) ≡⟨ Eq.cong (\ xx -> Vec.last (act ([ ps ]ᵛᵇ ↑) (xx))) (lemma-bbox-X' x q y qs) ⟩
  Vec.last (act ([ ps ]ᵛᵇ ↑) (act-bbox x q y qs)) ≡⟨ auto ⟩
  Vec.last (act ([ ps ]ᵛᵇ ↑) ((sq , ea + - b') ∷ (a' + sq , b') ∷ qs)) ≡⟨ Eq.cong Vec.last  (lemma-act-↑ [ ps ]ᵛᵇ (sq , ea + - b') ((a' + sq , b') ∷ qs)) ⟩
  Vec.last ((sq , ea + - b') ∷ act ([ ps ]ᵛᵇ) ((a' + sq , b') ∷ qs)) ≡⟨ auto ⟩
  Vec.last (act ([ ps ]ᵛᵇ) ((a' + sq , b') ∷ qs)) ≡⟨ lemma-act-bboxes-last (a' + sq , b') ps qs ⟩
  (a' + sq + sform (ps) (qs) , b')  ≡⟨ Eq.cong (\ xx -> (xx , b')) (+-assoc a' sq (sform ps qs)) ⟩
  (a' + (sq + sform ps qs) , b')  ≡⟨ auto ⟩
  (a' + (sform1 x y + sform ps qs) , b')  ≡⟨ auto ⟩
  (a' + sform (x ∷ ps) (y ∷ qs) , b') ∎
  where
  open ≡-Reasoning
  ea = e-after-abox-q x y (λ ())
  sq = sform1 x y
  
lemma-act-bboxes-last q@(a' , b') (x@(₁₊ _ , _) ∷ ps) (y ∷ qs) = begin
  Vec.last (act ([ ps ]ᵛᵇ ↑ • [ x ]ᵇ) (q ∷ y ∷ qs)) ≡⟨ auto ⟩
  Vec.last (act ([ ps ]ᵛᵇ ↑) (act [ x ]ᵇ (q ∷ y ∷ qs))) ≡⟨ Eq.cong (\ xx -> Vec.last (act ([ ps ]ᵛᵇ ↑) (xx))) (lemma-bbox-X' x q y qs) ⟩
  Vec.last (act ([ ps ]ᵛᵇ ↑) (act-bbox x q y qs)) ≡⟨ auto ⟩
  Vec.last (act ([ ps ]ᵛᵇ ↑) ((sq , ea + - b') ∷ (a' + sq , b') ∷ qs)) ≡⟨ Eq.cong Vec.last  (lemma-act-↑ [ ps ]ᵛᵇ (sq , ea + - b') ((a' + sq , b') ∷ qs)) ⟩
  Vec.last ((sq , ea + - b') ∷ act ([ ps ]ᵛᵇ) ((a' + sq , b') ∷ qs)) ≡⟨ auto ⟩
  Vec.last (act ([ ps ]ᵛᵇ) ((a' + sq , b') ∷ qs)) ≡⟨ lemma-act-bboxes-last (a' + sq , b') ps qs ⟩
  (a' + sq + sform (ps) (qs) , b')  ≡⟨ Eq.cong (\ xx -> (xx , b')) (+-assoc a' sq (sform ps qs)) ⟩
  (a' + (sq + sform ps qs) , b')  ≡⟨ auto ⟩
  (a' + (sform1 x y + sform ps qs) , b')  ≡⟨ auto ⟩
  (a' + sform (x ∷ ps) (y ∷ qs) , b') ∎
  where
  open ≡-Reasoning
  ea = e-after-abox-q x y (λ ())
  sq = sform1 x y
  

lemma-act-bboxes-last' : ∀ (q@(a' , b') : Pauli1) (ps qs : Pauli n) -> Vec.last (act-bboxes q ps qs) ≡ (a' + sform ps qs , b')
lemma-act-bboxes-last' q@(a' , b') ps qs = begin
  Vec.last (act-bboxes q ps qs) ≡⟨ Eq.cong Vec.last (Eq.sym (lemma-bboxes-X' q ps qs)) ⟩
  Vec.last (act [ ps ]ᵛᵇ (q ∷ qs)) ≡⟨ lemma-act-bboxes-last q ps qs ⟩
  (a' + sform ps qs , b') ∎
  where
  open ≡-Reasoning

