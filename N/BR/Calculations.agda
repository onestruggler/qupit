{-# OPTIONS  --safe #-}
{-# OPTIONS  --call-by-name #-}
{-# OPTIONS --termination-depth=4 #-}
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
--open import Data.List using () hiding ([_] ; _++_ ; last ; head ; tail ; _∷ʳ_)
open import Data.Vec hiding ([_])
open import Data.Vec as V
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



module N.BR.Calculations (p-2 : ℕ) (p-prime : Prime (2+ p-2))  where

private
  variable
    n : ℕ
    
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
open import N.Symplectic p-2 p-prime
open Symplectic renaming (M to ZM)
open import N.NF1-Sym p-2 p-prime
open import N.LM-Sym p-2 p-prime

open import N.Action p-2 p-prime
open import N.Action-Lemmas p-2 p-prime
open import Algebra.Properties.Ring (+-*-ring p-2)
open import N.NF2-Sym p-2 p-prime
open LM2


open import Zp.ModularArithmetic
open import N.Lemmas-2Qupit-Sym p-2 p-prime
open import N.NF2-Sym p-2 p-prime
--open Lemmas-2Q 2

open import N.NF1 p-2 p-prime
open import N.Ex-Sym p-2 p-prime
open import N.Ex-Sym1 p-2 p-prime
open import N.Ex-Sym2 p-2 p-prime
open import N.Ex-Sym3 p-2 p-prime
open import N.Ex-Sym4 p-2 p-prime
open import N.Ex-Sym5 p-2 p-prime hiding (module L0)
open import N.Ex-Sym2n p-2 p-prime
open import N.Ex-Sym3n p-2 p-prime

open import N.Lemma-Comm-n p-2 p-prime
open import N.Completeness1-Sym p-2 p-prime renaming (module Completeness to Cp1)
open Lemmas0a
open Lemmas0a1
open Lemmas0b
open Lemmas0c
open Lemmas-Sym
open Duality

open import N.Completeness1-Sym p-2 p-prime renaming (module Completeness to CP1) using ()
open import N.Coset2-Update-Sym p-2 p-prime renaming (module Completeness to CP2) using ()
open import N.Lemmas4-Sym p-2 p-prime
open import N.Pushing.DH p-2 p-prime


open ≡-Reasoning
open Eq

fig-24-3-cal-1 : ∀ (a* b* : ℤ* ₚ) ->
  let
  a = a* .proj₁
  b = b* .proj₁
  b⁻¹ = (b* ⁻¹) .proj₁
  nz : (a , b) ≢ (₀ , ₀)
  nz = aux-a≠0⇒ab≠0 a b (a* .proj₂)
  nz' : (b , - a ) ≢ (₀ , ₀)
  nz' = aux-b≠0⇒ab≠0 b (- a) ((-' a*) .proj₂)
  [ab]⁻¹* = ( a* *' b* ) ⁻¹
  [ab]⁻¹ = [ab]⁻¹* .proj₁
  a⁻¹ = (a* ⁻¹) .proj₁
  -b/a = - b * a⁻¹
  y = a⁻¹
  nzy = ((a*) ⁻¹) .proj₂
  x = -b/a
  nzx = (-' b* *' a* ⁻¹).proj₂
  
  x⁻¹ = ((x , nzx) ⁻¹) .proj₁
  x⁻¹⁻¹ = (((x , nzx) ⁻¹) ⁻¹) .proj₁
  -x⁻¹ = - x⁻¹
  -y/x' = (((y , nzy) *' ((x , nzx) ⁻¹)) *' -'₁)
  -y/x = -y/x' .proj₁
  
  in
  
  -x⁻¹ * (y * y) ≡ [ab]⁻¹ × -y/x ≡ b⁻¹ × -x⁻¹ ≡ - - a * b⁻¹

fig-24-3-cal-1 a* b* = aux'-1 , claim2 , claim3
  where
  a = a* .proj₁
  b = b* .proj₁
  b⁻¹ = (b* ⁻¹) .proj₁
  
  nz : (a , b) ≢ (₀ , ₀)
  nz = aux-a≠0⇒ab≠0 a b (a* .proj₂)
  nz' : (b , - a ) ≢ (₀ , ₀)
  nz' = aux-b≠0⇒ab≠0 b (- a) ((-' a*) .proj₂)
  [ab]⁻¹* = ( a* *' b* ) ⁻¹
  [ab]⁻¹ = [ab]⁻¹* .proj₁
  a⁻¹ = (a* ⁻¹) .proj₁
  -b/a = - b * a⁻¹
  y = a⁻¹
  nzy = ((a*) ⁻¹) .proj₂
  x = -b/a
  nzx = (-' b* *' a* ⁻¹).proj₂
  
  x⁻¹ = ((x , nzx) ⁻¹) .proj₁
  x⁻¹⁻¹ = (((x , nzx) ⁻¹) ⁻¹) .proj₁
  -x⁻¹ = - x⁻¹
  -y/x' = (((y , nzy) *' ((x , nzx) ⁻¹)) *' -'₁)
  -y/x = -y/x' .proj₁
  
  aux'-1 : -x⁻¹ * (y * y) ≡ [ab]⁻¹
  aux'-1 = begin
    -x⁻¹ * (y * y) ≡⟨ Eq.cong (\ xx -> - xx * (y * y)) (inv-distrib (-' b*) (a* ⁻¹)) ⟩
    - (((-' b*) ⁻¹) .proj₁ * (a* ⁻¹ ⁻¹) .proj₁) * (a⁻¹ * a⁻¹) ≡⟨ Eq.cong (_* (a⁻¹ * a⁻¹)) (-‿distribˡ-* (((-' b*) ⁻¹) .proj₁) ((a* ⁻¹ ⁻¹) .proj₁)) ⟩
    (- ((-' b*) ⁻¹) .proj₁ * (a* ⁻¹ ⁻¹) .proj₁) * (a⁻¹ * a⁻¹) ≡⟨ Eq.cong₂ (\ xx yy -> (xx * yy) * (a⁻¹ * a⁻¹)) (Eq.cong -_ (inv-neg-comm b*)) (inv-involutive a*) ⟩
    (- - (b⁻¹) * a) * (a⁻¹ * a⁻¹) ≡⟨ Eq.cong (\ xx -> (xx * a) * (a⁻¹ * a⁻¹)) (-‿involutive ((b⁻¹))) ⟩
    ((b⁻¹) * a) * (a⁻¹ * a⁻¹) ≡⟨ *-assoc b⁻¹ a (a⁻¹ * a⁻¹) ⟩
    (b⁻¹) * (a * (a⁻¹ * a⁻¹)) ≡⟨ Eq.cong ((b⁻¹) *_) (Eq.sym (*-assoc a a⁻¹ a⁻¹)) ⟩
    (b⁻¹) * ((a * a⁻¹) * a⁻¹) ≡⟨ Eq.cong (\ xx -> (b⁻¹) * (xx * a⁻¹)) (lemma-⁻¹ʳ a {{nztoℕ {y = a} {neq0 = a* .proj₂}}} ) ⟩
    (b⁻¹) * (₁ * a⁻¹) ≡⟨ Eq.cong ((b⁻¹) *_) (*-identityˡ ((a⁻¹))) ⟩
    (b⁻¹) * a⁻¹ ≡⟨ *-comm ((b⁻¹)) a⁻¹ ⟩
    a⁻¹ * (b⁻¹) ≡⟨ Eq.sym (inv-distrib a* b*) ⟩
    [ab]⁻¹ ∎


  claim2 : -y/x ≡ b⁻¹
  claim2 = begin
    -y/x ≡⟨ auto ⟩
    a⁻¹ * ((-' b* *' a* ⁻¹) ⁻¹).proj₁ * - ₁ ≡⟨ *-comm (a⁻¹ * ((-' b* *' a* ⁻¹) ⁻¹).proj₁) (- ₁) ⟩
    - ₁ * (a⁻¹ * ((-' b* *' a* ⁻¹) ⁻¹).proj₁) ≡⟨ -1*x≈-x ((a⁻¹ * ((-' b* *' a* ⁻¹) ⁻¹).proj₁)) ⟩
    - (a⁻¹ * ((-' b* *' a* ⁻¹) ⁻¹).proj₁) ≡⟨ Eq.cong (\ xx -> - (a⁻¹ * xx)) (inv-distrib (-' b*) (a* ⁻¹)) ⟩
    - (a⁻¹ * (((-' b*) ⁻¹).proj₁ * (a* ⁻¹ ⁻¹).proj₁)) ≡⟨ Eq.cong (\ xx -> - (a⁻¹ * (((-' b*) ⁻¹).proj₁ * xx))) (inv-involutive a*) ⟩
    - (a⁻¹ * (((-' b*) ⁻¹).proj₁ * a)) ≡⟨ Eq.cong (\ xx -> - (a⁻¹ * xx)) (*-comm (((-' b*) ⁻¹).proj₁) a) ⟩
    - (a⁻¹ * (a * ((-' b*) ⁻¹).proj₁)) ≡⟨ Eq.cong -_ (sym (*-assoc a⁻¹ a (((-' b*) ⁻¹).proj₁))) ⟩
    - (a⁻¹ * a * ((-' b*) ⁻¹).proj₁) ≡⟨ Eq.cong -_  (cong (_* ((-' b*) ⁻¹).proj₁) (lemma-⁻¹ˡ a {{nztoℕ {y = a} {neq0 = a* .proj₂}}})) ⟩
    - (₁ * ((-' b*) ⁻¹).proj₁) ≡⟨ Eq.cong -_ (*-identityˡ (((-' b*) ⁻¹).proj₁)) ⟩
    - (((-' b*) ⁻¹).proj₁) ≡⟨ Eq.cong -_ (inv-neg-comm b*) ⟩
    - - ((( b*) ⁻¹).proj₁) ≡⟨ -‿involutive b⁻¹ ⟩
    b⁻¹ ∎

  claim3 : -x⁻¹ ≡ - - a * b⁻¹
  claim3 = begin
    - ((-' b* *' a* ⁻¹) ⁻¹).proj₁ ≡⟨ Eq.cong -_ (inv-distrib (-' b*) (a* ⁻¹)) ⟩
    - (((-' b*) ⁻¹).proj₁ * (a* ⁻¹ ⁻¹).proj₁) ≡⟨ Eq.cong (\ xx -> - ((((-' b*) ⁻¹).proj₁ * xx))) (inv-involutive a*)  ⟩
    - (((-' b*) ⁻¹).proj₁ * a) ≡⟨ -‿distribˡ-* (((-' b*) ⁻¹).proj₁) a ⟩
    - ((-' b*) ⁻¹).proj₁ * a ≡⟨ cong (_* a) (cong -_ (inv-neg-comm b*)) ⟩
    - - ((b*) ⁻¹).proj₁ * a ≡⟨ cong (_* a) ( -‿involutive b⁻¹) ⟩
    ((b*) ⁻¹).proj₁ * a ≡⟨ *-comm b⁻¹ a ⟩
    a * b⁻¹ ≡⟨ cong (_* b⁻¹) (sym (-‿involutive a)) ⟩
    - - a * b⁻¹ ∎




fig-25-2-cal : ∀ (a*@(a , nza) : ℤ* ₚ) (b : ℤ ₚ) ->
  let
  nz : (a , b) ≢ (₀ , ₀)
  nz = aux-a≠0⇒ab≠0 a b nza
  a⁻¹ = ((a , nza) ⁻¹) .proj₁
  -b/a = - b * a⁻¹
  in
  
  -b/a + ₁ ≡ - (b + - a) * a⁻¹

fig-25-2-cal a*@(a , nza) b = aux
  where
  nz : (a , b) ≢ (₀ , ₀)
  nz = aux-a≠0⇒ab≠0 a b nza
  a⁻¹ = ((a , nza) ⁻¹) .proj₁
  -b/a = - b * a⁻¹
  
  aux : -b/a + ₁ ≡ - (b + - a) * a⁻¹
  aux = Eq.sym ( begin
    - (b + - a) * a⁻¹ ≡⟨ Eq.cong (_* a⁻¹) (Eq.sym (-‿+-comm b (- a))) ⟩
    (- b + - - a) * a⁻¹ ≡⟨ Eq.cong (\ xx -> (- b + xx) * a⁻¹) (-‿involutive a) ⟩
    (- b + a) * a⁻¹ ≡⟨ *-distribʳ-+ a⁻¹ (- b) a ⟩
    - b * a⁻¹ + a * a⁻¹ ≡⟨ Eq.cong (- b * a⁻¹ +_) (lemma-⁻¹ʳ a {{nztoℕ {y = a} {neq0 = nza}}}) ⟩
    - b * a⁻¹ + ₁ ≡⟨ auto ⟩
    -b/a + ₁ ∎
    )


cal-b1-a2 : ∀ (a1 a2 b1 : ℤ ₚ) (nz1 : a1 ≢ ₀) (nz2 : a2 ≢ ₀) ->
  let
  a1⁻¹ = ((a1 , nz1) ⁻¹) .proj₁
  -b1/a1 = - b1 * a1⁻¹
  [a2-b1]/a1 = - (b1 + - a2) * a1⁻¹
  in

  (a2 * a1) * (a1⁻¹ * a1⁻¹) + -b1/a1 ≡ [a2-b1]/a1

cal-b1-a2 a1 a2 b1 nz1 nz2 = begin
  (a2 * a1) * (a1⁻¹ * a1⁻¹) + -b1/a1 ≡⟨ cong (_+ -b1/a1) (*-assoc a2 a1 (a1⁻¹ * a1⁻¹)) ⟩
  a2 * (a1 * (a1⁻¹ * a1⁻¹)) + -b1/a1 ≡⟨ cong (_+ -b1/a1) (cong (a2 *_) (sym (*-assoc a1 a1⁻¹ a1⁻¹))) ⟩
  a2 * (a1 * a1⁻¹ * a1⁻¹) + -b1/a1 ≡⟨ cong (_+ -b1/a1) (cong (\ xx -> a2 * (xx * a1⁻¹)) (lemma-⁻¹ʳ a1 {{nztoℕ {y = a1} {neq0 = nz1}}})) ⟩
  a2 * (₁ * a1⁻¹) + -b1/a1 ≡⟨ cong (_+ -b1/a1) (cong (a2 *_) (*-identityˡ a1⁻¹)) ⟩
  a2 * (a1⁻¹) + -b1/a1 ≡⟨ sym (*-distribʳ-+ a1⁻¹ a2 (- b1)) ⟩
  (a2 + - b1) * (a1⁻¹) ≡⟨ cong (_* (a1⁻¹)) (+-comm a2 (- b1)) ⟩
  (- b1 + a2) * (a1⁻¹) ≡⟨ cong (_* a1⁻¹) (cong (- b1 +_) (sym (-‿involutive a2))) ⟩
  (- b1 + - - a2) * (a1⁻¹) ≡⟨ cong (_* a1⁻¹) ( (-‿+-comm b1 (- a2))) ⟩
  - (b1 + - a2) * (a1⁻¹) ≡⟨ auto ⟩
  [a2-b1]/a1 ∎
  where
  a1⁻¹ = ((a1 , nz1) ⁻¹) .proj₁
  -b1/a1 = - b1 * a1⁻¹
  [a2-b1]/a1 = - (b1 + - a2) * a1⁻¹



cal-b1-a2' : ∀ (a1 a2 b1 : ℤ ₚ) (nz1 : a1 ≢ ₀) (nz2 : a2 ≢ ₀) ->
  let
  a1⁻¹ = ((a1 , nz1) ⁻¹) .proj₁
  -b1/a1 = - b1 * a1⁻¹
  [a2-b1]/a1 = - (b1 + - a2) * a1⁻¹
  in

  a2 * (a1⁻¹) + -b1/a1 ≡ [a2-b1]/a1

cal-b1-a2' a1 a2 b1 nz1 nz2 = begin
  a2 * (a1⁻¹) + -b1/a1 ≡⟨ sym (*-distribʳ-+ a1⁻¹ a2 (- b1)) ⟩
  (a2 + - b1) * (a1⁻¹) ≡⟨ cong (_* (a1⁻¹)) (+-comm a2 (- b1)) ⟩
  (- b1 + a2) * (a1⁻¹) ≡⟨ cong (_* a1⁻¹) (cong (- b1 +_) (sym (-‿involutive a2))) ⟩
  (- b1 + - - a2) * (a1⁻¹) ≡⟨ cong (_* a1⁻¹) ( (-‿+-comm b1 (- a2))) ⟩
  - (b1 + - a2) * (a1⁻¹) ≡⟨ auto ⟩
  [a2-b1]/a1 ∎
  where
  a1⁻¹ = ((a1 , nz1) ⁻¹) .proj₁
  -b1/a1 = - b1 * a1⁻¹
  [a2-b1]/a1 = - (b1 + - a2) * a1⁻¹



cal-b2-a1 : ∀ (a1 a2 b2 : ℤ ₚ) (nz1 : a1 ≢ ₀) (nz2 : a2 ≢ ₀) ->
  let
  a2⁻¹ = ((a2 , nz2) ⁻¹) .proj₁
  -b2/a2 = - b2 * a2⁻¹
  [a1-b2]/a2 = - (b2 + - a1) * a2⁻¹
  in

  (a2 * a1) * (a2⁻¹ * a2⁻¹) + -b2/a2 ≡ [a1-b2]/a2

cal-b2-a1 a1 a2 b2 nz1 nz2 = begin
  (a2 * a1) * (a2⁻¹ * a2⁻¹) + -b2/a2 ≡⟨ cong (_+ -b2/a2) (cong (_* (a2⁻¹ * a2⁻¹)) (*-comm a2 a1)) ⟩
  (a1 * a2) * (a2⁻¹ * a2⁻¹) + -b2/a2 ≡⟨ cong (_+ -b2/a2) (*-assoc a1 a2 (a2⁻¹ * a2⁻¹)) ⟩
  a1 * (a2 * (a2⁻¹ * a2⁻¹)) + -b2/a2 ≡⟨ cong (_+ -b2/a2) (cong (a1 *_) (sym (*-assoc a2 a2⁻¹ a2⁻¹))) ⟩
  a1 * (a2 * a2⁻¹ * a2⁻¹) + -b2/a2 ≡⟨ cong (_+ -b2/a2) (cong (\ xx -> a1 * (xx * a2⁻¹)) (lemma-⁻¹ʳ a2 {{nztoℕ {y = a2} {neq0 = nz2}}})) ⟩
  a1 * (₁ * a2⁻¹) + -b2/a2 ≡⟨ cong (_+ -b2/a2) (cong (a1 *_) (*-identityˡ a2⁻¹)) ⟩
  a1 * (a2⁻¹) + -b2/a2 ≡⟨ sym (*-distribʳ-+ a2⁻¹ a1 (- b2)) ⟩
  (a1 + - b2) * (a2⁻¹) ≡⟨ cong (_* (a2⁻¹)) (+-comm a1 (- b2)) ⟩
  (- b2 + a1) * (a2⁻¹) ≡⟨ cong (_* a2⁻¹) (cong (- b2 +_) (sym (-‿involutive a1))) ⟩
  (- b2 + - - a1) * (a2⁻¹) ≡⟨ cong (_* a2⁻¹) ( (-‿+-comm b2 (- a1))) ⟩
  - (b2 + - a1) * (a2⁻¹) ≡⟨ auto ⟩
  [a1-b2]/a2 ∎
  where
  a2⁻¹ = ((a2 , nz2) ⁻¹) .proj₁
  -b2/a2 = - b2 * a2⁻¹
  [a1-b2]/a2 = - (b2 + - a1) * a2⁻¹



cal-b2-a1' : ∀ (a1 a2 b2 : ℤ ₚ) (nz1 : a1 ≢ ₀) (nz2 : a2 ≢ ₀) ->
  let
  a2⁻¹ = ((a2 , nz2) ⁻¹) .proj₁
  -b2/a2 = - b2 * a2⁻¹
  [a1-b2]/a2 = - (b2 + - a1) * a2⁻¹
  in

  a1 * (a2⁻¹) + -b2/a2 ≡ [a1-b2]/a2

cal-b2-a1' a1 a2 b2 nz1 nz2 = begin
  a1 * (a2⁻¹) + -b2/a2 ≡⟨ sym (*-distribʳ-+ a2⁻¹ a1 (- b2)) ⟩
  (a1 + - b2) * (a2⁻¹) ≡⟨ cong (_* (a2⁻¹)) (+-comm a1 (- b2)) ⟩
  (- b2 + a1) * (a2⁻¹) ≡⟨ cong (_* a2⁻¹) (cong (- b2 +_) (sym (-‿involutive a1))) ⟩
  (- b2 + - - a1) * (a2⁻¹) ≡⟨ cong (_* a2⁻¹) ( (-‿+-comm b2 (- a1))) ⟩
  - (b2 + - a1) * (a2⁻¹) ≡⟨ auto ⟩
  [a1-b2]/a2 ∎
  where
  a2⁻¹ = ((a2 , nz2) ⁻¹) .proj₁
  -b2/a2 = - b2 * a2⁻¹
  [a1-b2]/a2 = - (b2 + - a1) * a2⁻¹



aux-M≡M' : ∀ {n} y y' -> y .proj₁ ≡ y' .proj₁ -> ZM {n = n} y ≡ ZM y'
aux-M≡M' {n} y y' eq = begin
  ZM y ≡⟨ auto ⟩
  S^ x • H • S^ x⁻¹ • H • S^ x • H ≡⟨ Eq.cong₂ (\ xx yy -> S^ xx • H • S^ yy • H • S^ x • H) eq aux-eq ⟩
  S^ x' • H • S^ x'⁻¹ • H • S^ x • H ≡⟨ Eq.cong (\ xx -> S^ x' • H • S^ x'⁻¹ • H • S^ xx • H) eq ⟩
  S^ x' • H • S^ x'⁻¹ • H • S^ x' • H ≡⟨ auto ⟩
  ZM y' ∎
  where
  open ≡-Reasoning
  x = y .proj₁
  x⁻¹ = ((y ⁻¹) .proj₁ )
  x' = y' .proj₁
  x'⁻¹ = ((y' ⁻¹) .proj₁ )
  aux-eq : x⁻¹ ≡ x'⁻¹
  aux-eq  = begin
    x⁻¹ ≡⟨  Eq.sym  (*-identityʳ x⁻¹) ⟩
    x⁻¹ * ₁ ≡⟨ Eq.cong (x⁻¹ *_) (Eq.sym (lemma-⁻¹ʳ x' {{nztoℕ {y = x'} {neq0 = y' .proj₂} }})) ⟩
    x⁻¹ * (x' * x'⁻¹) ≡⟨ Eq.sym (*-assoc x⁻¹ x' x'⁻¹) ⟩
    (x⁻¹ * x') * x'⁻¹ ≡⟨ Eq.cong (\ xx -> (x⁻¹ * xx) * x'⁻¹) (Eq.sym eq) ⟩
    (x⁻¹ * x) * x'⁻¹ ≡⟨ Eq.cong (_* x'⁻¹) (lemma-⁻¹ˡ x {{nztoℕ {y = x} {neq0 = y .proj₂} }}) ⟩
    ₁ * x'⁻¹ ≡⟨ *-identityˡ x'⁻¹ ⟩
    x'⁻¹ ∎


aux--k*-k⁻¹ : ∀ (k*@(k , nz) : ℤ* ₚ) ->
  let
  k⁻¹ = (k* ⁻¹) .proj₁
  in
  
  - k * - k⁻¹ ≡ ₁

aux--k*-k⁻¹ k*@(k , nz) = begin
  - k * - k⁻¹ ≡⟨ sym (-‿distribˡ-* k (- k⁻¹)) ⟩
  - (k * - k⁻¹) ≡⟨ cong -_ (sym (-‿distribʳ-* k k⁻¹)) ⟩
  - - (k * k⁻¹) ≡⟨ -‿involutive (k * k⁻¹) ⟩
  (k * k⁻¹) ≡⟨ lemma-⁻¹ʳ k {{nztoℕ {y = k} {neq0 = nz}}} ⟩
  ₁ ∎
  where
  k⁻¹ = (k* ⁻¹) .proj₁
  

aux--b/a+₁ : ∀ (a*@(a , nz) : ℤ* ₚ) b ->
  let
  a⁻¹ = (a* ⁻¹) .proj₁
  -b/a = - b * a⁻¹
  in
  -b/a + ₁ ≡ - (b + - a) * a⁻¹
  
aux--b/a+₁ a*@(a , nz) b = Eq.sym ( begin
  - (b + - a) * a⁻¹ ≡⟨ Eq.cong (_* a⁻¹) (Eq.sym (-‿+-comm b (- a))) ⟩
  (- b + - - a) * a⁻¹ ≡⟨ Eq.cong (\ xx -> (- b + xx) * a⁻¹) (-‿involutive a) ⟩
  (- b + a) * a⁻¹ ≡⟨ *-distribʳ-+ a⁻¹ (- b) a ⟩
  - b * a⁻¹ + a * a⁻¹ ≡⟨ Eq.cong (- b * a⁻¹ +_) (lemma-⁻¹ʳ a {{nztoℕ {y = a} {neq0 = nz}}}) ⟩
  - b * a⁻¹ + ₁ ≡⟨ auto ⟩
  -b/a + ₁ ∎
  )
  where
  a⁻¹ = (a* ⁻¹) .proj₁
  -b/a = - b * a⁻¹


aux--k⁻¹ : ∀ (a*@(a , nza)  b*@(b , nzb) : ℤ* ₚ) ->
  let
  a⁻¹ = (a* ⁻¹) .proj₁
  b⁻¹ = (b* ⁻¹) .proj₁
  -b/a = - b * a⁻¹
  b/a = b * a⁻¹
  a/b = a* *' b* ⁻¹
  k = -b/a
  k* = -' b* *' a* ⁻¹
  -k⁻¹ = - ((k* ⁻¹) .proj₁)
  l = ((-' k* ⁻¹) ⁻¹) .proj₁
  in
  (-' k* ⁻¹) .proj₁ ≡ a/b .proj₁ ×
  - k ≡ b/a ×
  - a * l ≡ - b ×
  -k⁻¹ ≡ - - a * b⁻¹

aux--k⁻¹ a*@(a , nza) b*@(b , nzb) = claim1 , claim2 , claim3 , claim4
  where
  a⁻¹ = (a* ⁻¹) .proj₁
  b⁻¹ = (b* ⁻¹) .proj₁
  -b/a = - b * a⁻¹
  b/a = b * a⁻¹
  a/b = a* *' b* ⁻¹
  k = -b/a
  k* = -' b* *' a* ⁻¹
  -k⁻¹ = - ((k* ⁻¹) .proj₁)
  l = ((-' k* ⁻¹) ⁻¹) .proj₁
  claim1 : (-' k* ⁻¹) .proj₁ ≡ a/b .proj₁
  claim1 = begin
    (-' (-' b* *' a* ⁻¹) ⁻¹) .proj₁ ≡⟨ auto ⟩
    - ((-' b* *' a* ⁻¹) ⁻¹) .proj₁ ≡⟨ cong -_ (inv-distrib (-' b*) (a* ⁻¹)) ⟩
    - ((-' b*) ⁻¹  *' a* ⁻¹ ⁻¹) .proj₁ ≡⟨ cong -_ (cong (((-' b*) ⁻¹) .proj₁ *_) (inv-involutive a*)) ⟩
    - ((-' b*) ⁻¹  *' a*) .proj₁ ≡⟨ cong -_ (cong (_* a* .proj₁) (inv-neg-comm b*)) ⟩
    - (-' (b*) ⁻¹  *' a*) .proj₁ ≡⟨ auto ⟩
    - (- b⁻¹  * a) ≡⟨ -‿distribˡ-* (- b⁻¹) a ⟩
    - - b⁻¹  * a ≡⟨ cong (_* a) (-‿involutive b⁻¹) ⟩
    b⁻¹  * a ≡⟨ *-comm b⁻¹ a ⟩
    a/b .proj₁ ∎


  claim2 : - k ≡ b/a
  claim2 = begin
    - (- b * a⁻¹) ≡⟨ -‿distribˡ-* (- b) a⁻¹ ⟩
    - - b * a⁻¹ ≡⟨ cong (_* a⁻¹) (-‿involutive b) ⟩
    b * a⁻¹ ≡⟨ auto ⟩
    b/a ∎

  claim3 : - a * l ≡ - b
  claim3 = begin
    - a * ((-' k* ⁻¹) ⁻¹) .proj₁ ≡⟨ (cong (- a *_) (inv-neg-comm (k* ⁻¹))) ⟩
    - a * (-' k* ⁻¹ ⁻¹) .proj₁ ≡⟨ auto ⟩
    - a * - (k* ⁻¹ ⁻¹) .proj₁ ≡⟨ cong (- a *_) (cong -_ (inv-involutive k*)) ⟩
    - a * - (-' b* *' a* ⁻¹) .proj₁ ≡⟨ auto ⟩
    - a * - (- b * a⁻¹) ≡⟨ cong (- a *_) (-‿distribˡ-* (- b) a⁻¹) ⟩
    - a * (- - b * a⁻¹) ≡⟨ cong (- a *_) (cong (_* a⁻¹) (-‿involutive b)) ⟩
    - a * (b * a⁻¹) ≡⟨  cong (- a *_) (*-comm b a⁻¹) ⟩
    - a * (a⁻¹ * b) ≡⟨ sym (*-assoc (- a) a⁻¹ b) ⟩
    - a * a⁻¹ * b ≡⟨ cong (_* b) (sym (-‿distribˡ-* a a⁻¹)) ⟩
    - (a * a⁻¹) * b ≡⟨ cong (_* b) (cong -_ (lemma-⁻¹ʳ a {{nztoℕ {y = a} {neq0 = nza}}})) ⟩
    - (₁) * b ≡⟨ -1*x≈-x b ⟩
    - b ∎

  claim4 : -k⁻¹ ≡ - - a * b⁻¹
  claim4 = begin
    -k⁻¹ ≡⟨ claim1 ⟩
    a * b⁻¹ ≡⟨ sym (cong (_* b⁻¹) (-‿involutive a)) ⟩ 
    - - a * b⁻¹ ∎

aux-lkkk : ∀ (k*@(k , nzk) l*@(l , nzl) : ℤ* ₚ) ->
  let
  k⁻¹ = (k* ⁻¹) .proj₁
  l⁻¹ = (l* ⁻¹) .proj₁
  in
  l * k * (k⁻¹ * k⁻¹) ≡ l * k⁻¹
aux-lkkk k*@(k , nzk) l*@(l , nzl) = begin
  l * k * (k⁻¹ * k⁻¹) ≡⟨ *-assoc l k (k⁻¹ * k⁻¹) ⟩
  l * (k * (k⁻¹ * k⁻¹)) ≡⟨ Eq.cong (l *_) (Eq.sym (*-assoc k k⁻¹ k⁻¹)) ⟩
  l * (k * k⁻¹ * k⁻¹) ≡⟨  Eq.cong (l *_) ( Eq.cong (_* k⁻¹) (lemma-⁻¹ʳ k {{nztoℕ {y = k} {neq0 = nzk}}})) ⟩
  l * (₁ * k⁻¹) ≡⟨ Eq.cong (l *_) (*-identityˡ k⁻¹) ⟩
  l * k⁻¹ ∎
  where
  k⁻¹ = (k* ⁻¹) .proj₁
  l⁻¹ = (l* ⁻¹) .proj₁
  open ≡-Reasoning


aux-lkkk' : ∀ (k*@(k , nzk) : ℤ* ₚ) l ->
  let
  k⁻¹ = (k* ⁻¹) .proj₁
  in
  l * k * (k⁻¹ * k⁻¹) ≡ l * k⁻¹
aux-lkkk' k*@(k , nzk) l = begin
  l * k * (k⁻¹ * k⁻¹) ≡⟨ *-assoc l k (k⁻¹ * k⁻¹) ⟩
  l * (k * (k⁻¹ * k⁻¹)) ≡⟨ Eq.cong (l *_) (Eq.sym (*-assoc k k⁻¹ k⁻¹)) ⟩
  l * (k * k⁻¹ * k⁻¹) ≡⟨  Eq.cong (l *_) ( Eq.cong (_* k⁻¹) (lemma-⁻¹ʳ k {{nztoℕ {y = k} {neq0 = nzk}}})) ⟩
  l * (₁ * k⁻¹) ≡⟨ Eq.cong (l *_) (*-identityˡ k⁻¹) ⟩
  l * k⁻¹ ∎
  where
  k⁻¹ = (k* ⁻¹) .proj₁
  open ≡-Reasoning

aux-lkkk'' : ∀ (k*@(k , nzk) : ℤ* ₚ) l ->
  let
  k⁻¹ = (k* ⁻¹) .proj₁
  in
  l * k⁻¹ * (k * k) ≡ l * k
aux-lkkk'' k*@(k , nzk) l = begin
  l * k⁻¹ * (k * k) ≡⟨ *-assoc l k⁻¹ (k * k) ⟩
  l * (k⁻¹ * (k * k)) ≡⟨ Eq.cong (l *_) (Eq.sym (*-assoc k⁻¹ k k)) ⟩
  l * (k⁻¹ * k * k) ≡⟨  Eq.cong (l *_) ( Eq.cong (_* k) (lemma-⁻¹ˡ k {{nztoℕ {y = k} {neq0 = nzk}}})) ⟩
  l * (₁ * k) ≡⟨ Eq.cong (l *_) (*-identityˡ k) ⟩
  l * k ∎
  where
  k⁻¹ = (k* ⁻¹) .proj₁
  open ≡-Reasoning

