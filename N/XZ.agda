{-# OPTIONS  --safe #-}
{-# OPTIONS --termination-depth=2 #-}
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
open import Data.Fin hiding (_+_ ; _-_)

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



module N.XZ (p-2 : ℕ) (p-prime : Prime (2+ p-2))  where

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

{-
module XZ where

  Gen = Cyclic.X ⊎ Cyclic.X

  infix 4 _===_
  _===_ : WRel Gen
  _===_ = (Cyclic.pres p ⸲ Cyclic.pres p ⸲ Γₓ)

  pattern X-gen = inj₁ tt
  pattern Z-gen = inj₂ tt

  pattern order-X = left Cyclic.order
  pattern order-Z = right Cyclic.order
  pattern comm-Z-X = mid (comm tt tt)

  X : Word Gen
  X = [ X-gen ]ʷ

  Z : Word Gen
  Z = [ Z-gen ]ʷ

  nfp' : NFProperty' _===_
  nfp' = DP.NFP'.nfp' (Cyclic.pres p) (Cyclic.pres p) (Cyclic.nfp' p) (Cyclic.nfp' p)
-}


data Gen : ℕ → Set where
  X-gen : ∀ {n} → Gen (₁₊ n)
  Z-gen : ∀ {n} → Gen (₁₊ n)
  _↥ : ∀ {n} → Gen n → Gen (suc n)

[_⇑] : ∀ {n} → Word (Gen n) → Word (Gen (suc n))
[_⇑] {n} = ([_]ʷ ∘ _↥) WB.*

[_⇑]' : ∀ {n} → Word (Gen n) → Word (Gen (suc n))
[_⇑]' {n} = wmap _↥

_↑ : ∀ {n} → Word (Gen n) → Word (Gen (suc n))
_↑ = wmap _↥

_↓ : ∀ {n} → Word (Gen n) → Word (Gen ( n))
_↓ {n} x = x 


lemma-[⇑]=[⇑]' : ∀ {n} (w : Word (Gen n)) → [ w ⇑] ≡ [ w ⇑]'
lemma-[⇑]=[⇑]' {n} [ x ]ʷ = Eq.refl
lemma-[⇑]=[⇑]' {n} ε = Eq.refl
lemma-[⇑]=[⇑]' {n} (w • w₁) = Eq.cong₂ _•_ (lemma-[⇑]=[⇑]' w) (lemma-[⇑]=[⇑]' w₁)

X : ∀ {n} → Word (Gen (₁₊ n))
X = [ X-gen ]ʷ

Z : ∀ {n} → Word (Gen (₁₊ n))
Z = [ Z-gen ]ʷ

infix 4 _QRel,_===_
data _QRel,_===_ : (n : ℕ) → WRel (Gen n) where

  order-X :      ∀ {n} → (₁₊ n) QRel,  X ^ p === ε
  order-Z :      ∀ {n} → (₁₊ n) QRel,  Z ^ p === ε
  comm-Z-X :     ∀ {n} → (₁₊ n) QRel,  Z • X === X • Z

  comm-X :    ∀ {n}{g} → (₂₊ n) QRel,  [ g ↥ ]ʷ • X === X • [ g ↥ ]ʷ
  comm-Z :    ∀ {n}{g} → (₂₊ n) QRel,  [ g ↥ ]ʷ • Z === Z • [ g ↥ ]ʷ

  cong↑ : ∀ {n w v} → n QRel,  w === v → (₁₊ n) QRel,  w ↑ === v ↑

lemma-cong↑ : ∀ {n} w v →
  let open PB (n QRel,_===_) using (_≈_) in
  let open PB ((suc n) QRel,_===_) renaming (_≈_ to _≈↑_) using () in
  w ≈ v → w ↑ ≈↑ v ↑
lemma-cong↑ {n} w v PB.refl = PB.refl
lemma-cong↑ {n} w v (PB.sym eq) = PB.sym (lemma-cong↑ v w eq)
lemma-cong↑ {n} w v (PB.trans eq eq₁) = PB.trans (lemma-cong↑ _ _ eq) (lemma-cong↑ _ _ eq₁)
lemma-cong↑ {n} w v (PB.cong eq eq₁) = PB.cong (lemma-cong↑ _ _ eq) (lemma-cong↑ _ _ eq₁)
lemma-cong↑ {n} w v PB.assoc = PB.assoc
lemma-cong↑ {n} w v PB.left-unit = PB.left-unit
lemma-cong↑ {n} w v PB.right-unit = PB.right-unit
lemma-cong↑ {n} w v (PB.axiom x) = PB.axiom (cong↑ x)


import Data.Nat.Literals as NL
open import Agda.Builtin.FromNat
open import Data.Unit.Base using (⊤)
open import Data.Fin.Literals
import Data.Nat.Literals as NL


lemma-^-↑ : ∀ {n} (w : Word (Gen n)) k → w ↑ ^ k ≡ (w ^ k) ↑
lemma-^-↑ w ₀ = auto
lemma-^-↑ w ₁ = auto
lemma-^-↑ w (₂₊ k) = begin
  (w ↑) • (w ↑) ^ ₁₊ k ≡⟨ Eq.cong ((w ↑) •_) (lemma-^-↑ w (suc k)) ⟩
  (w ↑) • (w ^ ₁₊ k) ↑ ≡⟨ auto ⟩
  ((w • w ^ ₁₊ k) ↑) ∎
  where open ≡-Reasoning


instance
  Numℕ' : Number ℕ
  Numℕ' = NL.number 

instance
  NumFin' : Number (Fin p)
  NumFin' = number p

lemma-comm-X-w↑ : ∀ {n} w → let open PB ((₂₊ n) QRel,_===_) in

  X • w ↑ ≈ w ↑ • X

lemma-comm-X-w↑ {n} [ x ]ʷ = sym (axiom comm-X)
  where
  open PB ((₂₊ n) QRel,_===_)
lemma-comm-X-w↑ {n} ε = trans right-unit (sym left-unit)
  where
  open PB ((₂₊ n) QRel,_===_)
lemma-comm-X-w↑ {n} (w • w₁) = begin
  X • ((w • w₁) ↑) ≈⟨ refl ⟩
  X • (w ↑ • w₁ ↑) ≈⟨ sym assoc ⟩
  (X • w ↑) • w₁ ↑ ≈⟨ cong (lemma-comm-X-w↑ w) refl ⟩
  (w ↑ • X) • w₁ ↑ ≈⟨ assoc ⟩
  w ↑ • X • w₁ ↑ ≈⟨ cong refl (lemma-comm-X-w↑ w₁) ⟩
  w ↑ • w₁ ↑ • X ≈⟨ sym assoc ⟩
  ((w • w₁) ↑) • X ∎
  where
  open PB ((₂₊ n) QRel,_===_)
  open PP ((₂₊ n) QRel,_===_)
  open SR word-setoid

lemma-comm-Xᵏ-w↑ : ∀ {n} k w → let open PB ((₂₊ n) QRel,_===_) in

  X ^ k • w ↑ ≈ w ↑ • X ^ k

lemma-comm-Xᵏ-w↑ {n} ₀ w = trans left-unit (sym right-unit)
  where
  open PB ((₂₊ n) QRel,_===_)
lemma-comm-Xᵏ-w↑ {n} ₁ w = lemma-comm-X-w↑ w
  where
  open PB ((₂₊ n) QRel,_===_)
lemma-comm-Xᵏ-w↑ {n} (₂₊ k) w = begin
  (X • X ^ ₁₊ k) • (w ↑) ≈⟨ assoc ⟩
  X • X ^ ₁₊ k • (w ↑) ≈⟨ cong refl (lemma-comm-Xᵏ-w↑ (₁₊ k) w) ⟩
  X • (w ↑) • X ^ ₁₊ k ≈⟨ sym assoc ⟩
  (X • w ↑) • X ^ ₁₊ k ≈⟨ cong (lemma-comm-X-w↑ w) refl ⟩
  (w ↑ • X) • X ^ ₁₊ k ≈⟨ assoc ⟩
  (w ↑) • X • X ^ ₁₊ k ∎
  where
  open PB ((₂₊ n) QRel,_===_)
  open PP ((₂₊ n) QRel,_===_)
  open SR word-setoid


lemma-comm-Z-w↑ : ∀ {n} w → let open PB ((₂₊ n) QRel,_===_) in

  Z • w ↑ ≈ w ↑ • Z

lemma-comm-Z-w↑ {n} [ x ]ʷ = sym (axiom comm-Z)
  where
  open PB ((₂₊ n) QRel,_===_)
lemma-comm-Z-w↑ {n} ε = trans right-unit (sym left-unit)
  where
  open PB ((₂₊ n) QRel,_===_)
lemma-comm-Z-w↑ {n} (w • w₁) = begin
  Z • ((w • w₁) ↑) ≈⟨ refl ⟩
  Z • (w ↑ • w₁ ↑) ≈⟨ sym assoc ⟩
  (Z • w ↑) • w₁ ↑ ≈⟨ cong (lemma-comm-Z-w↑ w) refl ⟩
  (w ↑ • Z) • w₁ ↑ ≈⟨ assoc ⟩
  w ↑ • Z • w₁ ↑ ≈⟨ cong refl (lemma-comm-Z-w↑ w₁) ⟩
  w ↑ • w₁ ↑ • Z ≈⟨ sym assoc ⟩
  ((w • w₁) ↑) • Z ∎
  where
  open PB ((₂₊ n) QRel,_===_)
  open PP ((₂₊ n) QRel,_===_)
  open SR word-setoid


lemma-comm-Zᵏ-w↑ : ∀ {n} k w → let open PB ((₂₊ n) QRel,_===_) in

  Z ^ k • w ↑ ≈ w ↑ • Z ^ k

lemma-comm-Zᵏ-w↑ {n} ₀ w = trans left-unit (sym right-unit)
  where
  open PB ((₂₊ n) QRel,_===_)
lemma-comm-Zᵏ-w↑ {n} ₁ w = lemma-comm-Z-w↑ w
  where
  open PB ((₂₊ n) QRel,_===_)
lemma-comm-Zᵏ-w↑ {n} (₂₊ k) w = begin
  (Z • Z ^ ₁₊ k) • (w ↑) ≈⟨ assoc ⟩
  Z • Z ^ ₁₊ k • (w ↑) ≈⟨ cong refl (lemma-comm-Zᵏ-w↑ (₁₊ k) w) ⟩
  Z • (w ↑) • Z ^ ₁₊ k ≈⟨ sym assoc ⟩
  (Z • w ↑) • Z ^ ₁₊ k ≈⟨ cong (lemma-comm-Z-w↑ w) refl ⟩
  (w ↑ • Z) • Z ^ ₁₊ k ≈⟨ assoc ⟩
  (w ↑) • Z • Z ^ ₁₊ k ∎
  where
  open PB ((₂₊ n) QRel,_===_)
  open PP ((₂₊ n) QRel,_===_)
  open SR word-setoid


module XZ-GroupLike where

  private
    variable
      n : ℕ

  grouplike : Grouplike (n QRel,_===_)
  grouplike {₁₊ n} (X-gen) = (X) ^ p-1 ,  claim
    where
    open PB ((₁₊ n) QRel,_===_)
    open PP ((₁₊ n) QRel,_===_)
    open SR word-setoid
    claim : (X) ^ p-1 • X ≈ ε
    claim = begin
      (X) ^ p-1 • X ≈⟨ sym (lemma-^-+ (X) p-1 1) ⟩
      (X) ^ (p-1 Nat.+ 1) ≡⟨ Eq.cong (X ^_) ( NP.+-comm p-1 1) ⟩
      (X ^ p) ≈⟨ (axiom order-X) ⟩
      (ε) ∎

  grouplike {₁₊ n} (Z-gen) = (Z) ^ p-1 ,  claim
    where
    open PB ((₁₊ n) QRel,_===_)
    open PP ((₁₊ n) QRel,_===_)
    open SR word-setoid
    claim : (Z) ^ p-1 • Z ≈ ε
    claim = begin
      (Z) ^ p-1 • Z ≈⟨ sym (lemma-^-+ (Z) p-1 1) ⟩
      (Z) ^ (p-1 Nat.+ 1) ≡⟨ Eq.cong (Z ^_) ( NP.+-comm p-1 1) ⟩
      (Z ^ p) ≈⟨ (axiom order-Z) ⟩
      (ε) ∎

  grouplike {₂₊ n} (g ↥) with grouplike g
  ... | ig , prf = (ig ↑) , lemma-cong↑ (ig • [ g ]ʷ) ε prf
    where
    open PB ((₂₊ n) QRel,_===_)
    open PP ((₂₊ n) QRel,_===_)

-- ----------------------------------------------------------------------
-- * Data required for applying word tactics to Symplectic generators

module CommData where
  private
    variable
      n : ℕ

  -- Commutativity.
  commute : (x y : Gen (₂₊ n)) → let open PB ((₂₊ n) QRel,_===_) in Maybe (([ x ]ʷ • [ y ]ʷ) ≈ ([ y ]ʷ • [ x ]ʷ))
  commute {n} Z-gen (y ↥) = just (PB.sym (PB.axiom comm-Z))
  commute {n} (x ↥) Z-gen = just (PB.axiom comm-Z)
  commute {n} X-gen (y ↥) = just (PB.sym (PB.axiom comm-X))
  commute {n} (x ↥) X-gen = just (PB.axiom comm-X)
  
  commute {n@(suc n')} (x ↥) (y ↥) with commute x y
  ... | nothing = nothing
  ... | just eq = just (lemma-cong↑ ([ x ]ʷ • [ y ]ʷ) ([ y ]ʷ • [ x ]ʷ) eq)

  commute {n} _ _ = nothing


  -- We number the generators for the purpose of ordering them.
  ord : Gen (₁₊ n) → ℕ
  ord {n}(X-gen) = 0
  ord {n} (Z-gen) = 1
  ord {suc n} (g ↥) = 2 Nat.+ ord g

  -- Ordering of generators.
  les : Gen (₂₊ n) → Gen (₂₊ n) → Bool
  les x y with ord x Nat.<? ord y
  les x y | yes _ = true
  les x y | no _ = false

module Commuting-Symplectic (n : ℕ) where
  open CommData
  open Commuting (((₂₊ n) QRel,_===_) ) commute les public

