{-# OPTIONS  --safe #-}
{-# OPTIONS  --call-by-name #-}
import Data.Integer as Integer

module Zp.ModularArithmetic where

open import Algebra.Structures

-- open Integer hiding (+_; _-_) -- using (_+_; _*_; -_; +0)
-- open import Data.Integer.GCD
-- open import Data.Integer.Properties hiding (*-1-isMonoid; *-1-isCommutativeMonoid; +-*-isCommutativeRing ; +-0-isAbelianGroup)
-- open import Data.Integer.Tactic.RingSolver

open import Data.Product

open import Relation.Binary
open import Relation.Binary.PropositionalEquality as ≡
open import Relation.Binary.PropositionalEquality as Eq
open import Data.Nat.Divisibility

import Data.Fin as Fin
open import Data.Fin hiding (_+_ ; _-_ )
open import Data.Fin.Properties

infixl 6 _+_ _＊_
infixl 7 _*_
infixl 8 _^′_
infixr 8 -_

open import Data.Nat as ℕ hiding (_+_ ; _*_ ; _^_)
open import Data.Fin.Literals
import Data.Nat.Literals as NL
open import Agda.Builtin.FromNat
open import Data.Unit.Base using (⊤)
open import Data.Nat.DivMod
open import Data.Nat.Properties as NP using (n<1+n)
open import Data.Fin.Properties as FP

private
  variable
    n : ℕ
    
instance
  Numℕ : Number ℕ
  Numℕ = NL.number 

instance
  NumFin : Number (Fin 3)
  NumFin = number 3

instance
  NumFinN : Number (Fin n)
  NumFinN {n} = number n

pattern auto = Eq.refl

pattern ₀ = zero
pattern ₁ = suc ₀
pattern ₂ = suc ₁
pattern ₃ = suc ₂
pattern ₄ = suc ₃

pattern ₁₊ n = suc n
pattern ₂₊ n = suc (suc n)
pattern ₃₊ n = suc (₂₊ n)
pattern ₄₊ n = suc (₃₊ n)


ℤ : ℕ -> Set
ℤ n = Fin n

ℤ* : ℕ -> Set
ℤ* ₀ = ℤ ₀
ℤ* n@(suc _) = Σ[ a ∈ ℤ n ] (a ≢ ₀)

succ : ℤ n -> ℤ n
succ {suc n} ₀ = ₀
succ {2+ n} (suc a) = inject₁ (succ a)

cong-succ : ∀ {a b : ℤ n} -> a ≡ b -> succ a ≡ succ b
cong-succ {n} {a} {b} eq rewrite eq = refl

-- lemma : ∀ {a : ℤ (₁₊ n)} -> (toℕ a) ∣ n -> a ≡ ₀

_+_ : ℤ n → ℤ n → ℤ n
_+_ {suc n} a b = fromℕ< (m%n<n (toℕ a ℕ.+ toℕ b) (suc n))

_*_ : ℤ n → ℤ n → ℤ n
_*_ {suc n} a b = fromℕ< (m%n<n (toℕ a ℕ.* toℕ b) (suc n))

₋₁ : ℤ (₁₊ n)
₋₁ {n} = fromℕ< (n<1+n n)

₊₁ : ℤ (₂₊ n)
₊₁ {n} = ₁

0₂₊ₙ : ℤ (₂₊ n)
0₂₊ₙ {n} = ₀

-_ : ℤ n → ℤ n
-_ {suc n} a = ₋₁ * a

_^′_ : ℤ (₂₊ n) → ℕ → ℤ (₂₊ n)
_^′_ {n} a ₀ = ₁
_^′_ {n} a (₁₊ k) = a * (a ^′ k)


_＊_ : ℕ → ℤ (₁₊ n) → ℤ (₁₊ n)
_＊_ {n} ₀ a = ₀
_＊_ {n} (₁₊ k) a = a + (k ＊ a)

lemma-0^′k : ∀ k -> _^′_ {n} 0₂₊ₙ (suc k) ≡ 0₂₊ₙ
lemma-0^′k k = refl

lemma-toℕ₋₁ : toℕ (₋₁ {n}) ≡ n
lemma-toℕ₋₁ {n@0} = auto
lemma-toℕ₋₁ {n@(₁₊ n')} = begin
  toℕ ₋₁ ≡⟨ cong ₁₊ lemma-toℕ₋₁ ⟩
  n ∎
  where
  open ≡-Reasoning


open import Algebra.Definitions

+-cong : Congruent₂ (_≡_ {A = ℤ n}) _+_
+-cong {x} {y} {u} {v} ≡.refl ≡.refl = ≡.refl

+-identityˡ : LeftIdentity (_≡_ {A = ℤ (₁₊ n)}) 0 _+_
+-identityˡ {n} a = begin
  fromℕ< ((m%n<n (0 ℕ.+ toℕ a) (₁₊ n))) ≡⟨ refl ⟩
  fromℕ< ((m%n<n (toℕ a) (₁₊ n))) ≡⟨ fromℕ<-cong ((toℕ a) % (₁₊ n)) (toℕ a) (m<n⇒m%n≡m (toℕ<n a)) ((m%n<n (toℕ a) (₁₊ n))) (toℕ<n a) ⟩
  fromℕ< (toℕ<n a) ≡⟨ fromℕ<-toℕ a (toℕ<n a) ⟩
  a ∎
  where open Eq.≡-Reasoning

+-assoc : Associative (_≡_ {A = ℤ n}) _+_
+-assoc {suc n} a b c = begin
  a + b + c ≡⟨ refl ⟩
  fromℕ< ((m%n<n (toℕ a ℕ.+ toℕ b) (₁₊ n))) + c ≡⟨ refl ⟩
  fromℕ< (((m%n<n (toℕ (fromℕ< ((m%n<n (toℕ a ℕ.+ toℕ b) (₁₊ n)))) ℕ.+ toℕ c) (₁₊ n)))) ≡⟨ cong (\ x -> fromℕ< (((m%n<n (x ℕ.+ toℕ c) (₁₊ n))))) (toℕ-fromℕ< (m%n<n (toℕ a ℕ.+ toℕ b) (₁₊ n))) ⟩
  fromℕ< (((m%n<n ((toℕ a ℕ.+ toℕ b) % (₁₊ n) ℕ.+ toℕ c) (₁₊ n)))) ≡⟨ cong (\ x -> fromℕ< (((m%n<n (x ℕ.+ toℕ c) (₁₊ n))))) (%-distribˡ-+ (toℕ a) (toℕ b) (₁₊ n)) ⟩
  fromℕ< (((m%n<n ((toℕ a % (₁₊ n) ℕ.+ toℕ b % (₁₊ n)) % (₁₊ n) ℕ.+ toℕ c) (₁₊ n)))) ≡⟨ cong (\ x -> fromℕ< (((m%n<n ((toℕ a % (₁₊ n) ℕ.+ toℕ b % (₁₊ n)) % (₁₊ n) ℕ.+ x) (₁₊ n))))) (sym (m<n⇒m%n≡m (toℕ<n c))) ⟩
  fromℕ< (((m%n<n ((toℕ a % (₁₊ n) ℕ.+ toℕ b % (₁₊ n)) % (₁₊ n) ℕ.+ toℕ c % (₁₊ n)) (₁₊ n)))) ≡⟨ fromℕ<-cong (((toℕ a % (₁₊ n) ℕ.+ toℕ b % (₁₊ n)) % (₁₊ n) ℕ.+ toℕ c % (₁₊ n)) % (₁₊ n)) (((toℕ a % (₁₊ n) ℕ.+ toℕ b % (₁₊ n))  ℕ.+ toℕ c) % (₁₊ n)) (sym (%-distribˡ-+ ((toℕ a % (₁₊ n) ℕ.+ toℕ b % (₁₊ n))) (toℕ c) ((₁₊ n)))) (m%n<n ((toℕ a % (₁₊ n) ℕ.+ toℕ b % (₁₊ n)) % (₁₊ n) ℕ.+ toℕ c % (₁₊ n)) (₁₊ n)) (m%n<n ((toℕ a % (₁₊ n) ℕ.+ toℕ b % (₁₊ n))  ℕ.+ toℕ c) (₁₊ n)) ⟩
  fromℕ< (((m%n<n ((toℕ a % (₁₊ n) ℕ.+ toℕ b % (₁₊ n)) ℕ.+ toℕ c) (₁₊ n)))) ≡⟨ (Eq.cong (\ x -> fromℕ< (((m%n<n (x) (₁₊ n))))) (NP.+-assoc ( toℕ a % (₁₊ n)) (toℕ b % (₁₊ n)) (toℕ c))) ⟩
  fromℕ< (((m%n<n (toℕ a % (₁₊ n) ℕ.+ (toℕ b % (₁₊ n) ℕ.+ toℕ c)) (₁₊ n)))) ≡⟨ cong₂ (\ x y -> fromℕ< (((m%n<n (x ℕ.+ (toℕ b % (₁₊ n) ℕ.+ y)) (₁₊ n))))) ( (m<n⇒m%n≡m (toℕ<n a))) (sym (m<n⇒m%n≡m (toℕ<n c))) ⟩
  fromℕ< ((m%n<n (toℕ a ℕ.+ (toℕ b % (₁₊ n) ℕ.+ toℕ c % (₁₊ n))) (₁₊ n))) ≡⟨ sym (fromℕ<-cong ((toℕ a % (₁₊ n) ℕ.+ (toℕ b % (₁₊ n) ℕ.+ toℕ c % (₁₊ n)) % (₁₊ n)) % (₁₊ n)) ((toℕ a ℕ.+ (toℕ b % (₁₊ n) ℕ.+ toℕ c % (₁₊ n))) % (₁₊ n)) (sym (%-distribˡ-+ (toℕ a) ((toℕ b % (₁₊ n) ℕ.+ toℕ c % (₁₊ n))) ((₁₊ n)))) (m%n<n (toℕ a % (₁₊ n) ℕ.+ (toℕ b % (₁₊ n) ℕ.+ toℕ c % (₁₊ n)) % (₁₊ n)) (₁₊ n)) (m%n<n (toℕ a ℕ.+ (toℕ b % (₁₊ n) ℕ.+ toℕ c % (₁₊ n))) (₁₊ n))) ⟩
  fromℕ< ((m%n<n (toℕ a % (₁₊ n) ℕ.+ (toℕ b % (₁₊ n) ℕ.+ toℕ c % (₁₊ n)) % (₁₊ n)) (₁₊ n))) ≡⟨ cong (\ x -> fromℕ< ((m%n<n (x ℕ.+ (toℕ b % (₁₊ n) ℕ.+ toℕ c % (₁₊ n)) % (₁₊ n)) (₁₊ n)))) (m<n⇒m%n≡m (toℕ<n a)) ⟩
  fromℕ< ((m%n<n (toℕ a ℕ.+ (toℕ b % (₁₊ n) ℕ.+ toℕ c % (₁₊ n)) % (₁₊ n)) (₁₊ n))) ≡⟨ sym (cong (\ x -> fromℕ< ((m%n<n (toℕ a ℕ.+ x) (₁₊ n)))) (%-distribˡ-+ (toℕ b) (toℕ c) (₁₊ n))) ⟩
  fromℕ< ((m%n<n (toℕ a ℕ.+ (toℕ b ℕ.+ toℕ c) % (₁₊ n)) (₁₊ n))) ≡⟨ sym (cong (\ x -> fromℕ< ((m%n<n (toℕ a ℕ.+ x) (₁₊ n)))) (toℕ-fromℕ< (m%n<n (toℕ b ℕ.+ toℕ c) (₁₊ n)))) ⟩
  fromℕ< ((m%n<n (toℕ a ℕ.+ toℕ (fromℕ< ((m%n<n (toℕ b ℕ.+ toℕ c) (₁₊ n))))) (₁₊ n))) ≡⟨ refl ⟩
  a + fromℕ< ((m%n<n (toℕ b ℕ.+ toℕ c) (₁₊ n))) ≡⟨ refl ⟩
  a + (b + c) ∎
  where open Eq.≡-Reasoning

+-comm : Commutative (_≡_ {A = ℤ n }) _+_
+-comm {suc n} a b = begin
  fromℕ< ((m%n<n (toℕ a ℕ.+ toℕ b) (₁₊ n))) ≡⟨ cong (\ x -> fromℕ< ((m%n<n (x) (₁₊ n)))) (NP.+-comm (toℕ a) (toℕ b)) ⟩
  fromℕ< ((m%n<n (toℕ b ℕ.+ toℕ a) (₁₊ n))) ∎
  where open Eq.≡-Reasoning

+-identityʳ : RightIdentity (_≡_ {A = ℤ (₁₊ n)}) 0 _+_
+-identityʳ = comm∧idˡ⇒idʳ +-comm +-identityˡ
  where open import Algebra.Consequences.Propositional

+-identity : Identity (_≡_ {A = ℤ (₁₊ n)}) 0 _+_
+-identity = +-identityˡ , +-identityʳ

*-identityˡ : LeftIdentity (_≡_ {A = ℤ (₂₊ n)}) 1 _*_
*-identityˡ {n} a = begin
  fromℕ< ((m%n<n (1 ℕ.* toℕ a) (₂₊ n))) ≡⟨ cong (\ x -> fromℕ< ((m%n<n (x) (₂₊ n)))) (NP.*-identityˡ (toℕ a)) ⟩
  fromℕ< ((m%n<n (toℕ a) (₂₊ n))) ≡⟨ fromℕ<-cong ((toℕ a) % (₂₊ n)) (toℕ a) (m<n⇒m%n≡m (toℕ<n a)) ((m%n<n (toℕ a) (₂₊ n))) (toℕ<n a) ⟩
  fromℕ< (toℕ<n a) ≡⟨ fromℕ<-toℕ a (toℕ<n a) ⟩
  a ∎
  where open Eq.≡-Reasoning

*-assoc : Associative (_≡_ {A = ℤ n}) _*_
*-assoc {suc n} a b c = begin
  a * b * c ≡⟨ refl ⟩
  fromℕ< ((m%n<n (toℕ a ℕ.* toℕ b) (₁₊ n))) * c ≡⟨ refl ⟩
  fromℕ< (((m%n<n (toℕ (fromℕ< ((m%n<n (toℕ a ℕ.* toℕ b) (₁₊ n)))) ℕ.* toℕ c) (₁₊ n)))) ≡⟨ cong (\ x -> fromℕ< (((m%n<n (x ℕ.* toℕ c) (₁₊ n))))) (toℕ-fromℕ< (m%n<n (toℕ a ℕ.* toℕ b) (₁₊ n))) ⟩
  fromℕ< (((m%n<n ((toℕ a ℕ.* toℕ b) % (₁₊ n) ℕ.* toℕ c) (₁₊ n)))) ≡⟨ cong (\ x -> fromℕ< (((m%n<n (x ℕ.* toℕ c) (₁₊ n))))) (%-distribˡ-* (toℕ a) (toℕ b) (₁₊ n)) ⟩
  fromℕ< (((m%n<n (((toℕ a % (₁₊ n)) ℕ.* (toℕ b % (₁₊ n))) % (₁₊ n) ℕ.* toℕ c) (₁₊ n)))) ≡⟨ cong (\ x -> fromℕ< (((m%n<n (((toℕ a % (₁₊ n)) ℕ.* (toℕ b % (₁₊ n))) % (₁₊ n) ℕ.* x) (₁₊ n))))) (sym (m<n⇒m%n≡m (toℕ<n c))) ⟩
  fromℕ< (((m%n<n (((toℕ a % (₁₊ n)) ℕ.* (toℕ b % (₁₊ n))) % (₁₊ n) ℕ.* (toℕ c % (₁₊ n))) (₁₊ n)))) ≡⟨ fromℕ<-cong ((((toℕ a % (₁₊ n)) ℕ.* (toℕ b % (₁₊ n))) % (₁₊ n) ℕ.* (toℕ c % (₁₊ n))) % (₁₊ n)) ((((toℕ a % (₁₊ n)) ℕ.* (toℕ b % (₁₊ n)))  ℕ.* toℕ c) % (₁₊ n)) (sym (%-distribˡ-* (((toℕ a % (₁₊ n)) ℕ.* (toℕ b % (₁₊ n)))) (toℕ c) ((₁₊ n)))) (m%n<n (((toℕ a % (₁₊ n)) ℕ.* (toℕ b % (₁₊ n))) % (₁₊ n) ℕ.* (toℕ c % (₁₊ n))) (₁₊ n)) (m%n<n (((toℕ a % (₁₊ n)) ℕ.* (toℕ b % (₁₊ n)))  ℕ.* toℕ c) (₁₊ n)) ⟩
  fromℕ< (((m%n<n (((toℕ a % (₁₊ n)) ℕ.* (toℕ b % (₁₊ n))) ℕ.* toℕ c) (₁₊ n)))) ≡⟨ (Eq.cong (\ x -> fromℕ< (((m%n<n (x) (₁₊ n))))) (NP.*-assoc ( (toℕ a % (₁₊ n))) ((toℕ b % (₁₊ n))) (toℕ c))) ⟩
  fromℕ< (((m%n<n ((toℕ a % (₁₊ n)) ℕ.* ((toℕ b % (₁₊ n)) ℕ.* toℕ c)) (₁₊ n)))) ≡⟨ cong₂ (\ x y -> fromℕ< (((m%n<n (x ℕ.* ((toℕ b % (₁₊ n)) ℕ.* y)) (₁₊ n))))) ( (m<n⇒m%n≡m (toℕ<n a))) (sym (m<n⇒m%n≡m (toℕ<n c))) ⟩
  fromℕ< ((m%n<n (toℕ a ℕ.* ((toℕ b % (₁₊ n)) ℕ.* (toℕ c % (₁₊ n)))) (₁₊ n))) ≡⟨ sym (fromℕ<-cong (((toℕ a % (₁₊ n)) ℕ.* (((toℕ b % (₁₊ n)) ℕ.* (toℕ c % (₁₊ n))) % (₁₊ n))) % (₁₊ n)) ((toℕ a ℕ.* ((toℕ b % (₁₊ n)) ℕ.* (toℕ c % (₁₊ n)))) % (₁₊ n)) (sym (%-distribˡ-* (toℕ a) ((((toℕ b % (₁₊ n))) ℕ.* ((toℕ c % (₁₊ n))))) ((₁₊ n)))) (m%n<n ((toℕ a % (₁₊ n)) ℕ.* (((toℕ b % (₁₊ n)) ℕ.* (toℕ c % (₁₊ n))) % (₁₊ n))) (₁₊ n)) (m%n<n (toℕ a ℕ.* ((toℕ b % (₁₊ n)) ℕ.* (toℕ c % (₁₊ n)))) (₁₊ n))) ⟩
  fromℕ< ((m%n<n (((toℕ a % (₁₊ n))) ℕ.* (((toℕ b % (₁₊ n)) ℕ.* (toℕ c % (₁₊ n))) % (₁₊ n))) (₁₊ n))) ≡⟨ cong (\ x -> fromℕ< ((m%n<n (x ℕ.* (((toℕ b % (₁₊ n)) ℕ.* (toℕ c % (₁₊ n))) % (₁₊ n))) (₁₊ n)))) (m<n⇒m%n≡m (toℕ<n a)) ⟩
  fromℕ< ((m%n<n (toℕ a ℕ.* ((((toℕ b % (₁₊ n)) ℕ.* (toℕ c % (₁₊ n))) % (₁₊ n)))) (₁₊ n))) ≡⟨ sym (cong (\ x -> fromℕ< ((m%n<n (toℕ a ℕ.* x) (₁₊ n)))) (%-distribˡ-* (toℕ b) (toℕ c) (₁₊ n))) ⟩
  fromℕ< ((m%n<n (toℕ a ℕ.* ((toℕ b ℕ.* toℕ c) % (₁₊ n))) (₁₊ n))) ≡⟨ sym (cong (\ x -> fromℕ< ((m%n<n (toℕ a ℕ.* x) (₁₊ n)))) (toℕ-fromℕ< (m%n<n (toℕ b ℕ.* toℕ c) (₁₊ n)))) ⟩
  fromℕ< ((m%n<n (toℕ a ℕ.* toℕ (fromℕ< ((m%n<n (toℕ b ℕ.* toℕ c) (₁₊ n))))) (₁₊ n))) ≡⟨ refl ⟩
  a * fromℕ< ((m%n<n (toℕ b ℕ.* toℕ c) (₁₊ n))) ≡⟨ refl ⟩
  a * (b * c) ∎
  where open Eq.≡-Reasoning

*-comm : Commutative (_≡_ {A = ℤ n }) _*_
*-comm {suc n} a b = begin
  fromℕ< ((m%n<n (toℕ a ℕ.* toℕ b) (₁₊ n))) ≡⟨ cong (\ x -> fromℕ< ((m%n<n (x) (₁₊ n)))) (NP.*-comm (toℕ a) (toℕ b)) ⟩
  fromℕ< ((m%n<n (toℕ b ℕ.* toℕ a) (₁₊ n))) ∎
  where open Eq.≡-Reasoning

*-identityʳ : RightIdentity (_≡_ {A = ℤ (₂₊ n)}) 1 _*_
*-identityʳ = comm∧idˡ⇒idʳ *-comm *-identityˡ
  where open import Algebra.Consequences.Propositional

*-identity : Identity (_≡_ {A = ℤ (₂₊ n)}) 1 _*_
*-identity = *-identityˡ , *-identityʳ


*-distribˡ-+ : _DistributesOverˡ_ (_≡_ {A = ℤ n}) _*_ _+_
*-distribˡ-+ {suc n} a b c = begin
  a * (b + c) ≡⟨ refl ⟩
  fromℕ< (m%n<n (toℕ a ℕ.* toℕ (fromℕ< ((m%n<n (toℕ b ℕ.+ toℕ c) (₁₊ n))))) (₁₊ n)) ≡⟨ cong (\ x -> fromℕ< (m%n<n (toℕ a ℕ.* x) (₁₊ n))) (toℕ-fromℕ< (m%n<n (toℕ b ℕ.+ toℕ c) (₁₊ n))) ⟩
  fromℕ< (m%n<n (toℕ a ℕ.* ((toℕ b ℕ.+ toℕ c) % (₁₊ n))) (₁₊ n)) ≡⟨ sym (cong (\ x -> fromℕ< (m%n<n (x ℕ.* ((toℕ b ℕ.+ toℕ c) % (₁₊ n))) (₁₊ n))) (m<n⇒m%n≡m (toℕ<n a))) ⟩
  fromℕ< (m%n<n (toℕ a % (₁₊ n) ℕ.* ((toℕ b ℕ.+ toℕ c) % (₁₊ n))) (₁₊ n)) ≡⟨ fromℕ<-cong ((toℕ a % (₁₊ n) ℕ.* ((toℕ b ℕ.+ toℕ c) % (₁₊ n))) % (₁₊ n)) ((toℕ a ℕ.* (toℕ b ℕ.+ toℕ c)) % (₁₊ n)) (sym (%-distribˡ-* (toℕ a) ((toℕ b ℕ.+ toℕ c)) ((₁₊ n)))) (m%n<n (toℕ a % (₁₊ n) ℕ.* ((toℕ b ℕ.+ toℕ c) % (₁₊ n))) (₁₊ n)) (m%n<n (toℕ a ℕ.* (toℕ b ℕ.+ toℕ c)) (₁₊ n)) ⟩
  fromℕ< (m%n<n (toℕ a ℕ.* (toℕ b ℕ.+ toℕ c)) (₁₊ n)) ≡⟨ cong (\ x -> fromℕ< (m%n<n (x) (₁₊ n))) (NP.*-distribˡ-+ (toℕ a) (toℕ b) (toℕ c)) ⟩
  fromℕ< (m%n<n (toℕ a ℕ.* toℕ b ℕ.+ toℕ a ℕ.* toℕ c) (₁₊ n)) ≡⟨ fromℕ<-cong ((toℕ a ℕ.* toℕ b ℕ.+ toℕ a ℕ.* toℕ c) % (₁₊ n)) ((toℕ a ℕ.* toℕ b % (₁₊ n) ℕ.+ toℕ a ℕ.* toℕ c %(₁₊ n)) % (₁₊ n)) (%-distribˡ-+ (toℕ a ℕ.* toℕ b) (toℕ a ℕ.* toℕ c) ((₁₊ n))) (m%n<n (toℕ a ℕ.* toℕ b ℕ.+ toℕ a ℕ.* toℕ c) (₁₊ n)) (m%n<n (toℕ a ℕ.* toℕ b % (₁₊ n) ℕ.+ toℕ a ℕ.* toℕ c %(₁₊ n)) (₁₊ n)) ⟩
  fromℕ< (m%n<n (toℕ a ℕ.* toℕ b % (₁₊ n) ℕ.+ toℕ a ℕ.* toℕ c %(₁₊ n)) (₁₊ n)) ≡⟨ refl ⟩
  fromℕ< (m%n<n ((toℕ a ℕ.* toℕ b) % (₁₊ n) ℕ.+ (toℕ a ℕ.* toℕ c) % (₁₊ n)) (₁₊ n)) ≡⟨ sym (cong₂ (\ x y -> fromℕ< (m%n<n (x ℕ.+ y) (₁₊ n))) (toℕ-fromℕ< (m%n<n (toℕ (a) ℕ.* toℕ (b)) (₁₊ n))) (toℕ-fromℕ< (m%n<n (toℕ (a) ℕ.* toℕ (c)) (₁₊ n)))) ⟩
  fromℕ< (m%n<n (toℕ (fromℕ< (m%n<n (toℕ (a) ℕ.* toℕ (b)) (₁₊ n))) ℕ.+ toℕ (fromℕ< (m%n<n (toℕ (a) ℕ.* toℕ (c)) (₁₊ n)))) (₁₊ n)) ≡⟨ refl ⟩
  fromℕ< (m%n<n (toℕ (a * b) ℕ.+ toℕ (a * c)) (₁₊ n)) ≡⟨ refl ⟩
  a * b + a * c ∎
  where open Eq.≡-Reasoning


*-distribʳ-+ : _DistributesOverʳ_ (_≡_ {A = ℤ n}) _*_ _+_
*-distribʳ-+ = comm∧distrˡ⇒distrʳ *-comm *-distribˡ-+
  where open import Algebra.Consequences.Propositional

*-distrib-+ : _DistributesOver_ (_≡_ {A = ℤ n}) _*_ _+_
*-distrib-+ = *-distribˡ-+ , *-distribʳ-+

₊₁+₋₁≡₀ : ₊₁ {n} + ₋₁ ≡ ₀
₊₁+₋₁≡₀ {n} = begin
  ₊₁ {n} + ₋₁ ≡⟨ refl ⟩
  (fromℕ< (m%n<n (toℕ (₊₁ {n}) ℕ.+ toℕ (₋₁ {₁₊ n})) (₂₊ n))) ≡⟨ refl ⟩
  (fromℕ< (m%n<n (toℕ (₊₁ {n}) ℕ.+ toℕ (fromℕ< (n<1+n (₁₊ n)))) (₂₊ n))) ≡⟨ cong (\ x -> (fromℕ< (m%n<n (toℕ (₊₁ {n}) ℕ.+ x) (₂₊ n)))) (toℕ-fromℕ< (n<1+n (₁₊ n))) ⟩
  (fromℕ< (m%n<n (toℕ (₊₁ {n}) ℕ.+ (₁₊ n)) (₂₊ n))) ≡⟨ refl ⟩
  (fromℕ< (m%n<n (1 ℕ.+ (₁₊ n)) (₂₊ n))) ≡⟨ refl ⟩
  (fromℕ< (m%n<n (₂₊ n) (₂₊ n))) ≡⟨ fromℕ<-cong ((₂₊ n) % (₂₊ n)) ₀ (n%n≡0 (₂₊ n)) (m%n<n (₂₊ n) (₂₊ n)) (NP.0<1+n {₁₊ n}) ⟩
  fromℕ< (NP.0<1+n {₁₊ n}) ≡⟨ refl ⟩
  ₀ ∎
  where open Eq.≡-Reasoning

₋₁+₊₁≡₀ : ₋₁ {₁₊ n} + ₊₁ ≡ ₀
₋₁+₊₁≡₀ {n} = begin
  ₋₁ + ₊₁ {n} ≡⟨ +-comm ₋₁ ₊₁ ⟩
  ₊₁ {n} + ₋₁ ≡⟨ ₊₁+₋₁≡₀ ⟩
  ₀ ∎
  where open Eq.≡-Reasoning

+-inverseˡ : LeftInverse (_≡_ {A = ℤ (₂₊ n)}) 0 -_ _+_
+-inverseˡ {n} a = begin
  - a + a ≡⟨ cong (\ x -> - a + x) (sym (*-identityˡ a)) ⟩
  - a + ₁ * a ≡⟨ sym (*-distribʳ-+ a ₋₁ ₁) ⟩
  (₋₁ + ₁) * a ≡⟨ cong (_* a) ₋₁+₊₁≡₀ ⟩
  ₀ * a ≡⟨ refl ⟩
  0 ∎
  where
  open Eq.≡-Reasoning


+-inverseʳ : RightInverse (_≡_ {A = ℤ (₂₊ n)}) 0 -_ _+_
+-inverseʳ = comm∧invˡ⇒invʳ +-comm +-inverseˡ
  where open import Algebra.Consequences.Propositional

+-inverse : Inverse (_≡_ {A = ℤ (₂₊ n)}) 0 -_ _+_
+-inverse = +-inverseˡ , +-inverseʳ

neg-cong : Congruent₁ (_≡_ {A = ℤ (₁₊ n)}) -_
neg-cong ≡.refl = ≡.refl

+-0-isAbelianGroup : IsAbelianGroup (_≡_ {A = ℤ (₂₊ n)}) _+_ 0 -_
+-0-isAbelianGroup = record
  { isGroup = record
    { isMonoid = record
      { isSemigroup = record
        { isMagma = record
          { isEquivalence = ≡.isEquivalence
          ; ∙-cong = +-cong
          }
        ; assoc = +-assoc
        }
      ; identity = +-identity
      }
    ; inverse = +-inverse
    ; ⁻¹-cong = neg-cong
    }
  ; comm = +-comm
  }

+-*-isCommutativeRing : IsCommutativeRing (_≡_ {A = ℤ (₂₊ n)}) _+_ _*_ -_ 0 1
+-*-isCommutativeRing = record
  { isRing = record
              { +-isAbelianGroup = +-0-isAbelianGroup
              ; *-cong = cong₂ _*_
              ; *-assoc = *-assoc
              ; *-identity = *-identity 
              ; distrib = *-distrib-+
              }
  ; *-comm = *-comm
  }

*-zeroˡ : LeftZero (_≡_ {A = ℤ (₁₊ n)}) 0 _*_
*-zeroˡ {n} a = refl

*-zeroʳ : RightZero (_≡_ {A = ℤ (₁₊ n)}) 0 _*_
*-zeroʳ = comm∧zeˡ⇒zeʳ *-comm *-zeroˡ
  where open import Algebra.Consequences.Propositional


open import Algebra.Bundles
open import Level

+-*-commutativeRing : ℕ -> CommutativeRing 0ℓ 0ℓ
+-*-commutativeRing n = record
  { isCommutativeRing = +-*-isCommutativeRing {n}
  }

+-*-ring : ℕ -> Ring 0ℓ 0ℓ
+-*-ring n = record
  { isRing = IsCommutativeRing.isRing (+-*-isCommutativeRing {n})
  }




1＊x=x : ∀ (x : ℤ (₁₊ n)) -> ₁ ＊ x ≡ x
1＊x=x x = +-identityʳ x




module Sol (m : ℕ) where

  open import Tactic.RingSolver
  open import Tactic.RingSolver.Core.AlmostCommutativeRing
  open import Data.Maybe

  meq0 : (x : ℤ (₂₊ m)) → Maybe (₀ ≡ x)
  meq0 ₀ = just refl
  meq0 (₁₊ x) = nothing

  aring : AlmostCommutativeRing _ _
  aring = fromCommutativeRing (+-*-commutativeRing m) meq0

  open import Tactic.RingSolver.NonReflective (aring) using (solve ; solve₁) public
--  open import Tactic.RingSolver using (solve) public
  open import Tactic.RingSolver.Core.Expression public

  -- lemma : ∀ (x : ℤ (₂₊ m)) → x + ₀ ≡ ₀ + x
  -- lemma = {!AlmostCommutativeRing.Carrier aring!}


  open import Data.List
  
  -- lemma-sform-aux-s' : (a b c d : ℤ ₃) -> (- a) * d + c * b ≡  (- a) * (c + d) + c * (a + b)
  -- lemma-sform-aux-s' a b c d = {!!} -- solve (a ∷ b ∷ c ∷ d ∷ []) aring

  -- lemma-3 : ∀ a b -> a + (a + (a + b)) ≡ b
  -- lemma-3 a b = ? -- solve (a ∷ b ∷ []) aring


open Sol public

dkw-s : ∀ (a b :  ℤ ₃) -> a + b ≡ b + a
dkw-s = solve 1 2 (\ a b -> ((a ⊕ b) , (b ⊕ a))) λ {x} {x = x₁} → Eq.refl


open import Data.Nat.Primality
open import Data.Nat.Coprimality hiding (sym)
open import Data.Nat.GCD
open Bézout
open import Data.Empty
open import Algebra.Properties.Group

module PrimeModulus (p-2 : ℕ) (p-prime : Prime (₂₊ p-2)) where

  open import Algebra.Properties.Ring (+-*-ring p-2)

  p-1 : ℕ
  p-1 = ₁₊ p-2

  
  ₚ : ℕ
  ₚ = ₁₊ p-1
  p = ₚ

  ₚ₋₁ = fromℕ< (NP.≤-refl {p})
  -- not the same
  ₚ-₁ : ℕ
  ₚ-₁ = p-1

  ₀ₚ : ℤ ₚ
  ₀ₚ = ₀

  0ₚ : ℤ ₚ
  0ₚ = ₀

  1ₚ : ℤ ₚ
  1ₚ = ₁

  ₁ₚ : ℤ* ₚ
  ₁ₚ = ₁ , λ ()

  0ₚ≢1ₚ : 0ₚ ≢ 1ₚ
  0ₚ≢1ₚ ()

  p-1=-1ₚ : fromℕ< (NP.≤-refl {p}) ≡ - 1ₚ
  p-1=-1ₚ = +-cancelˡ 1ₚ (fromℕ< (NP.≤-refl {p})) (- 1ₚ) (trans claim1 (sym claim2))
    where
    open ≡-Reasoning
    claim1 : 1ₚ + fromℕ< (NP.≤-refl {p}) ≡ 0ₚ
    claim1 = begin
      1ₚ + fromℕ< (NP.≤-refl {p}) ≡⟨ refl ⟩
      fromℕ< (m%n<n (1 ℕ.+ toℕ (fromℕ< (NP.≤-refl {p}))) p) ≡⟨ cong (\ xx -> fromℕ< (m%n<n (1 ℕ.+ xx) p)) (toℕ-fromℕ< (NP.≤-refl {p})) ⟩
      fromℕ< (m%n<n (1 ℕ.+ p-1) p) ≡⟨ refl ⟩
      fromℕ< (m%n<n p p) ≡⟨ fromℕ<-cong (p % p) 0 (n%n≡0 p) (m%n<n p p) (NP.0<1+n {p-1}) ⟩
      fromℕ< (NP.0<1+n {p-1}) ≡⟨ refl ⟩
      0ₚ ∎

    claim2 : 1ₚ + - 1ₚ ≡ 0ₚ
    claim2 = +-inverseʳ 1ₚ

  aux-₋₁=-1 : ₋₁ ≡ - 1ₚ
  aux-₋₁=-1 = p-1=-1ₚ

  aux-₋₁*₋₁=₁ : ₋₁ * ₋₁ ≡ 1ₚ
  aux-₋₁*₋₁=₁ = begin
    ₋₁ * ₋₁ ≡⟨ cong₂ _*_ p-1=-1ₚ p-1=-1ₚ ⟩
    - ₁ * - ₁ ≡⟨ sym (-‿distribˡ-* ₁ (- ₁)) ⟩
    - (₁ * - ₁) ≡⟨ sym (cong -_ (-‿distribʳ-* ₁ ₁)) ⟩
    - - (₁ * ₁) ≡⟨ -‿involutive 1ₚ ⟩
    ₁ ∎
    where
    open ≡-Reasoning
  
  0ₚ≢p-1 : 0ₚ ≢ fromℕ< (NP.≤-refl {p})
  0ₚ≢p-1 ()

  0ₚ≢-1ₚ : 0ₚ ≢ - 1ₚ
  0ₚ≢-1ₚ eq with 0ₚ≢p-1 (trans eq (sym p-1=-1ₚ))
  ... | ()

  lemma-toℕ-ₚ₋₁ : toℕ ₚ₋₁ ≡ p-1
  lemma-toℕ-ₚ₋₁ = toℕ-fromℕ< (NP.≤-refl {p})

  lemma-toℕ-1ₚ : toℕ (- 1ₚ) ≡ p-1
  lemma-toℕ-1ₚ = trans (cong toℕ (sym p-1=-1ₚ)) lemma-toℕ-ₚ₋₁


{-
  test-aux : ∀ a b c d -> (- a) * d + c * b ≡ - ((- c) * b + a * d)
  test-aux = solve 1 4 (\ a b c d -> (⊝ a) ⊗ d ⊕ c ⊗ b , ⊝ ((⊝ c) ⊗ b ⊕ a ⊗ d)) λ {x} {x = x₁} {x = x₂} {x = x₃} → Eq.refl
    where open Sol

  test-aux-a : ∀ a b c d -> - ((- c) * b + a * d) ≡ - (- c) * b + - a * d
  test-aux-a = solve 1 4 (\ a b c d ->  ⊝ ((⊝ c) ⊗ b ⊕ a ⊗ d) , ⊝ (⊝ c) ⊗ b ⊕ ⊝ a ⊗ d) λ {x} {x = x₁} {x = x₂} {x = x₃} → Eq.refl
    where open Sol
-}


  open import Data.Nat using (NonZero)

  instance
    nztoℕ : ∀ {y : ℤ (₁₊ n)} → {neq0 : y ≢ ₀} -> NonZero (toℕ y)
    nztoℕ {n} {₀} {neq0} with neq0 refl
    ... | ()
    nztoℕ {n} {₁₊ y} {neq0} = record { nonZero = Data.Unit.Base.tt }
  {-# OVERLAPS nztoℕ #-}

  -- *-cancelˡ-nonZero : AlmostLeftCancellative (_≡_ {A = ℤ ₚ}) 0 _*_
  -- *-cancelˡ-nonZero x y z xnz eq with coprime-Bézout (prime⇒coprime p-prime {{nztoℕ {y = x} {neq0 = xnz}}} (toℕ<n x) )
  -- ... | +- x₁ y₁ eq₁ = {!!}
  -- ... | -+ x₁ y₁ eq₁ = {!!}



  infixl 9 _⁻¹  _⁻¹' _⁻¹'' --[-_]⁻¹
  
  _⁻¹' : (x : ℤ ₚ) -> {{NonZero (toℕ x)}} -> ℤ ₚ
  _⁻¹' x {{nz}} with coprime-Bézout (prime⇒coprime p-prime {{nz}} (toℕ<n x) )
  ... | +- x₁ y eq = - fromℕ< (m%n<n y p)
  ... | -+ x₁ y eq = fromℕ< (m%n<n y p)
  
  lemma-⁻¹ˡ : ∀ (x : ℤ ₚ) -> {{nz : NonZero (toℕ x)}} ->
    let xinv = (_⁻¹' x {{nz}}) in
    
    xinv * x ≡ ₁
    
  lemma-⁻¹ˡ x {{nz}} with coprime-Bézout (prime⇒coprime p-prime {{nz}} (toℕ<n x) )
  ... | +- x₁ y eq = claim1
    where
    open Eq.≡-Reasoning
    -xinv = fromℕ< (m%n<n y p)
    xinv = - -xinv

    +-group = Ring.+-group (+-*-ring (p-2))
    
    eq' : ₁₊ (y ℕ.* toℕ x) % p ≡ ₀
    eq' = begin
      ₁₊ (y ℕ.* toℕ x) % p ≡⟨ cong (_% p) eq ⟩
      x₁ ℕ.* p % p ≡⟨ m*n%n≡0 x₁ p ⟩
      ₀ ∎


    aux1 : xinv * x + -xinv * x ≡ ₀
    aux1 = begin
      xinv * x + -xinv * x ≡⟨ sym (*-distribʳ-+ x xinv -xinv) ⟩
      (xinv + -xinv) * x ≡⟨ cong (_* x) (+-inverseˡ -xinv) ⟩
      ₀ * x ≡⟨ refl ⟩
      ₀ ∎

    aux2 : ₁ + -xinv * x ≡ ₀
    aux2 = begin
      ₁ + -xinv * x ≡⟨ refl ⟩
      ₁ + fromℕ< (m%n<n y p) * x ≡⟨ refl ⟩
      ₁ + fromℕ< (m%n<n (toℕ (fromℕ< (m%n<n y p)) ℕ.* toℕ x) p) ≡⟨ refl ⟩
      fromℕ< (m%n<n (toℕ 1ₚ ℕ.+ toℕ (fromℕ< (m%n<n (toℕ (fromℕ< (m%n<n y p)) ℕ.* toℕ x) p))) p) ≡⟨ cong (\ □ -> fromℕ< (m%n<n (toℕ 1ₚ ℕ.+ □) p)) (toℕ-fromℕ< ((m%n<n (toℕ (fromℕ< (m%n<n y p)) ℕ.* toℕ x) p))) ⟩
      fromℕ< (m%n<n (toℕ 1ₚ ℕ.+  (toℕ (fromℕ< (m%n<n y p)) ℕ.* toℕ x) % p) p) ≡⟨ cong (\ □ -> fromℕ< (m%n<n (toℕ 1ₚ ℕ.+  ( □ ℕ.* toℕ x) % p) p)) (toℕ-fromℕ< (m%n<n y p)) ⟩
      fromℕ< (m%n<n (toℕ 1ₚ ℕ.+  ( (y % p) ℕ.* toℕ x) % p) p) ≡⟨ cong₂ (\ □₁ □₂ -> fromℕ< (m%n<n (□₁ ℕ.+  ( (y % p) ℕ.* □₂) % p) p)) (m<n⇒m%n≡m (s≤s (NP.0<1+n {p-1}))) (sym (m<n⇒m%n≡m (toℕ<n x))) ⟩
      fromℕ< (m%n<n (toℕ 1ₚ % p ℕ.+  ( (y % p) ℕ.* (toℕ x % p)) % p) p) ≡⟨ cong (\ □ -> fromℕ< (m%n<n (toℕ 1ₚ % p ℕ.+  □) p)) (sym (%-distribˡ-* y (toℕ x) p)) ⟩
      fromℕ< (m%n<n (toℕ 1ₚ % p ℕ.+  (y ℕ.* toℕ x) % p) p) ≡⟨ fromℕ<-cong ((toℕ 1ₚ % p ℕ.+  (y ℕ.* toℕ x) % p) % p) ((toℕ 1ₚ ℕ.+ (y ℕ.* toℕ x)) % p) (sym (%-distribˡ-+ (toℕ 1ₚ) ((y ℕ.* toℕ x)) p)) (m%n<n (toℕ 1ₚ % p ℕ.+  (y ℕ.* toℕ x) % p) p) (m%n<n (toℕ 1ₚ ℕ.+ (y ℕ.* toℕ x)) p) ⟩
      fromℕ< (m%n<n (toℕ 1ₚ ℕ.+ (y ℕ.* toℕ x)) p) ≡⟨ fromℕ<-cong ((toℕ 1ₚ ℕ.+ (y ℕ.* toℕ x)) % p) 0 eq' (m%n<n (toℕ 1ₚ ℕ.+ (y ℕ.* toℕ x)) p) (NP.0<1+n {p-1}) ⟩
      fromℕ< (NP.0<1+n {p-1}) ≡⟨ refl ⟩
      ₀ ∎

    claim1 : (xinv * x) ≡ ₁
    claim1 = begin
      (xinv * x) ≡⟨ ∙-cancelʳ +-group (-xinv * x) ((xinv * x)) ₁ (trans aux1 (sym aux2)) ⟩
      ₁ ∎


  ... | -+ x₁ y eq = claim1
    where
    open Eq.≡-Reasoning
    xinv = fromℕ< (m%n<n y p)
    
    claim : (y ℕ.* toℕ x) % p ≡ ₁ % p
    claim = begin
      (y ℕ.* toℕ x) % p ≡⟨ cong (_% p) (Eq.sym eq) ⟩
      (₁ ℕ.+ (x₁ ℕ.* ₂₊ p-2)) % p ≡⟨ (%-distribˡ-+ ₁ (x₁ ℕ.* ₂₊ p-2) p) ⟩
      (₁ % p ℕ.+ (x₁ ℕ.* ₂₊ p-2) % p) % p ≡⟨ cong (\ □ -> (₁ % p ℕ.+ □) % p) (%-distribˡ-* x₁ p p) ⟩
      (₁ % p ℕ.+ (x₁ % p ℕ.* (₂₊ p-2 % p)) % p) % p ≡⟨ cong (\ □ -> (₁ % p ℕ.+ □) % p) (cong (\ □ -> (x₁ % p ℕ.* □) % p) (n%n≡0 p)) ⟩
      (₁ % p ℕ.+ (x₁ % p ℕ.* 0) % p) % p ≡⟨ cong (\ □ -> (₁ % p ℕ.+ □) % p) (cong (_% p) (NP.*-zeroʳ (x₁ % p))) ⟩
      ₁ % p ℕ.+ 0 % p ≡⟨ refl ⟩
      ₁ % p ∎

    claim0 : ((y % p) ℕ.* toℕ x) % p ≡ ₁ % p
    claim0 = begin
      ((y % p) ℕ.* toℕ x) % p ≡⟨ %-distribˡ-* (y % p) (toℕ x) p ⟩
      ((y % p % p) ℕ.* (toℕ x % p)) % p ≡⟨ cong (\ □ -> (□ ℕ.* (toℕ x % p)) % p) (m%n%n≡m%n y p) ⟩
      ((y % p) ℕ.* (toℕ x % p)) % p ≡⟨ Eq.sym ( %-distribˡ-* y (toℕ x) p) ⟩
      ((y) ℕ.* (toℕ x)) % p ≡⟨ claim ⟩
      ₁ % p ∎

    claim1 : (xinv * x) ≡ ₁
    claim1 = begin
      (xinv * x) ≡⟨ refl ⟩
      fromℕ< (m%n<n (toℕ (fromℕ< (m%n<n y p)) ℕ.* toℕ x) p) ≡⟨ cong (\ □ -> fromℕ< (m%n<n (□ ℕ.* toℕ x) p)) (toℕ-fromℕ< (m%n<n y p)) ⟩
      fromℕ< (m%n<n ((y % p) ℕ.* toℕ x) p) ≡⟨ fromℕ<-cong (((y % p) ℕ.* toℕ x) % p) 1 claim0 (m%n<n ((y % p) ℕ.* toℕ x) p) (s≤s (NP.0<1+n {p-2})) ⟩
      fromℕ< (s≤s (NP.0<1+n {p-2})) ≡⟨ refl ⟩
      ₁ ∎

  lemma-⁻¹ʳ : ∀ (x : ℤ ₚ) -> {{nz : NonZero (toℕ x)}} ->
    let xinv = (_⁻¹' x {{nz}}) in
    
    x * xinv ≡ ₁
    
  lemma-⁻¹ʳ x {{nz}} = begin
    x * xinv ≡⟨ *-comm x xinv ⟩
    xinv * x ≡⟨ lemma-⁻¹ˡ x ⟩
    ₁ ∎
    where
    open Eq.≡-Reasoning
    xinv = _⁻¹' x {{nz}}


  lemma-⁻¹-nz : ∀ (x : ℤ ₚ) -> {{nz : NonZero (toℕ x)}} -> 
    let xinv = (_⁻¹' x {{nz}}) in

    xinv ≢ 0    
    
  lemma-⁻¹-nz x {{nz}} eq0 = 0ₚ≢1ₚ (trans (sym (claim2 eq0)) claim1)
    where
    open Eq.≡-Reasoning
    xinv = _⁻¹' x {{nz}}
    
    claim1 : (xinv * x) ≡ ₁
    claim1 = lemma-⁻¹ˡ x {{nz}}

    claim2 : xinv ≡ 0 -> (xinv * x) ≡ ₀
    claim2 eq0 = begin
      (xinv * x) ≡⟨ cong (_* x) eq0 ⟩
      (0 * x) ≡⟨ refl ⟩
      ₀ ∎



  _⁻¹'' : ℤ ₚ -> ℤ ₚ
  zero ⁻¹'' = 0
  suc x ⁻¹'' = _⁻¹' (₁₊ x) {{record { nonZero = Data.Unit.Base.tt }}}

  [-_]⁻¹ : ℤ ₚ -> ℤ ₚ
  [- x ]⁻¹ = (- x) ⁻¹''


  _⁻¹ : ∀ (x : ℤ* ₚ) -> ℤ* ₚ
  _⁻¹ (x , nz) = (_⁻¹' x {{nztoℕ {y = x} {neq0 = nz}}}) , lemma-⁻¹-nz x {{nztoℕ {y = x} {neq0 = nz}}}





  lemma-⁻¹ˡ' : ∀ (x : ℤ ₚ) -> {{nz : NonZero (toℕ x)}} ->
    let xinv = (_⁻¹' x {{nz}}) in
    
    toℕ xinv ℕ.* toℕ x % ₚ ≡ ₁
    
  lemma-⁻¹ˡ' x {{nz}} = begin
    toℕ xinv ℕ.* toℕ x % ₚ ≡⟨ Eq.sym (toℕ-fromℕ< (m%n<n (toℕ xinv ℕ.* toℕ x) ₚ)) ⟩
    toℕ (fromℕ< (m%n<n (toℕ xinv ℕ.* toℕ x) ₚ)) ≡⟨ refl ⟩
    toℕ (xinv * x) ≡⟨ cong toℕ (lemma-⁻¹ˡ x {{nz}}) ⟩
    ₁ ∎
    where
    open Eq.≡-Reasoning
    xinv = (_⁻¹' x {{nz}})
  lemma-⁻¹ʳ' : ∀ (x : ℤ ₚ) -> {{nz : NonZero (toℕ x)}} ->
    let xinv = (_⁻¹' x {{nz}}) in
    
    toℕ x ℕ.* toℕ xinv % ₚ ≡ ₁
    
  lemma-⁻¹ʳ' x {{nz}} = begin
    toℕ x ℕ.* toℕ xinv % ₚ ≡⟨ cong (_% ₚ) (NP.*-comm (toℕ x) (toℕ xinv)) ⟩
    toℕ xinv ℕ.* toℕ x % ₚ ≡⟨ lemma-⁻¹ˡ' x ⟩
    ₁ ∎
    where
    open Eq.≡-Reasoning
    xinv = _⁻¹' x {{nz}}


  infixl 7 _*'_
  infixr 8 -'_


  _*'_ : ℤ* p → ℤ* p → ℤ* p
  _*'_ (a , nza) (b , nzb) = (a * b) , claim
    where
    ainv = _⁻¹' a {{nztoℕ {y = a} {neq0 = nza}}}
    binv = _⁻¹' b {{nztoℕ {y = b} {neq0 = nzb}}}
    
    claim : a * b ≢ ₀
    claim eq0 = 0ₚ≢1ₚ 0=1
      where
      open Eq.≡-Reasoning
      0=1 : 0ₚ ≡ 1ₚ
      0=1 = begin
        0ₚ ≡⟨ refl ⟩
        0ₚ * (binv * ainv) ≡⟨ cong (_* (binv * ainv)) (sym eq0) ⟩
        a * b * (binv * ainv) ≡⟨ *-assoc a b (binv * ainv) ⟩
        a * (b * (binv * ainv)) ≡⟨ cong (a *_) (sym (*-assoc b binv ainv)) ⟩
        a * ((b * binv) * ainv) ≡⟨ cong (a *_) (cong (_* ainv) (lemma-⁻¹ʳ b {{nztoℕ {y = b} {neq0 = nzb}}} )) ⟩
        a * (₁ * ainv) ≡⟨ cong (a *_) (*-identityˡ ainv) ⟩
        a * ainv ≡⟨ lemma-⁻¹ʳ a {{nztoℕ {y = a} {neq0 = nza}}} ⟩
        1ₚ ∎


  -'_ : ℤ* p → ℤ* p
  -'_ (a , nza) = - a , claim
    where
    ainv = _⁻¹' a {{nztoℕ {y = a} {neq0 = nza}}}
    open Eq.≡-Reasoning

    claim : - a ≢ ₀
    claim eq0 = 0ₚ≢-1ₚ 0=-1
      where
      0=-1 : 0ₚ ≡ - 1ₚ
      0=-1 = begin
        0ₚ ≡⟨ refl ⟩
        0ₚ * ainv ≡⟨ cong (_* ainv) (sym eq0) ⟩
        - a * ainv ≡⟨ sym (-‿distribˡ-* a ainv) ⟩
        - (a * ainv) ≡⟨ cong -_ (lemma-⁻¹ʳ a {{nztoℕ {y = a} {neq0 = nza}}}) ⟩
        - ₁ ≡⟨ refl ⟩
        - 1ₚ ∎


  inv-involutive : ∀ x -> (x ⁻¹ ⁻¹) .proj₁ ≡ x .proj₁
  inv-involutive x = begin
    (x ⁻¹ ⁻¹) .proj₁ ≡⟨ sym (*-identityˡ ((x ⁻¹ ⁻¹) .proj₁)) ⟩
    1ₚ * (x ⁻¹ ⁻¹) .proj₁ ≡⟨ sym (cong (_* (x ⁻¹ ⁻¹) .proj₁) (lemma-⁻¹ʳ (x .proj₁) {{nztoℕ {y = x .proj₁} {neq0 = x .proj₂} }})) ⟩
    (x .proj₁ * (x ⁻¹) .proj₁) * (x ⁻¹ ⁻¹) .proj₁ ≡⟨ *-assoc ( (x) .proj₁) ((x ⁻¹) .proj₁) ((x ⁻¹ ⁻¹) .proj₁) ⟩
    x .proj₁ * ((x ⁻¹) .proj₁ * (x ⁻¹ ⁻¹) .proj₁) ≡⟨ cong (x .proj₁ *_) (trans c1 (sym c2)) ⟩
    x .proj₁ * ((x ⁻¹) .proj₁ * (x) .proj₁) ≡⟨ sym (*-assoc ( (x) .proj₁) ((x ⁻¹) .proj₁) ((x) .proj₁)) ⟩
    (x .proj₁ * (x ⁻¹) .proj₁) * (x) .proj₁ ≡⟨ cong (_* (x) .proj₁) (lemma-⁻¹ʳ (x .proj₁) {{nztoℕ {y = x .proj₁} {neq0 = x .proj₂} }}) ⟩
    1ₚ * x .proj₁ ≡⟨ *-identityˡ (x .proj₁) ⟩
    x .proj₁ ∎
    where
    open Eq.≡-Reasoning
    c1 : (x ⁻¹) .proj₁ * (x ⁻¹ ⁻¹) .proj₁ ≡ 1ₚ
    c1 = lemma-⁻¹ʳ ((x ⁻¹) .proj₁) {{nztoℕ {y = (x ⁻¹) .proj₁} {neq0 = lemma-⁻¹-nz (x .proj₁) {{nztoℕ {y = (x) .proj₁} {neq0 = x .proj₂}}}}}}
    c2 : (x ⁻¹) .proj₁ * x .proj₁ ≡ 1ₚ
    c2 = lemma-⁻¹ˡ (x .proj₁) {{nztoℕ {y = x .proj₁} {neq0 = x .proj₂} }}

  inv-₁ : ((₁ , λ ()) ⁻¹) .proj₁ ≡ ₁
  inv-₁ = begin
    ((₁ , λ ()) ⁻¹) .proj₁ ≡⟨ sym (*-identityˡ (((₁ , λ ()) ⁻¹) .proj₁)) ⟩
    ₁ * ((₁ , λ ()) ⁻¹) .proj₁ ≡⟨ lemma-⁻¹ʳ ₁ {{nztoℕ {y = 1ₚ} {neq0 = λ ()}}} ⟩
    ₁ ∎
    where
    open Eq.≡-Reasoning

  inv-cong : ∀ k* l* -> k* .proj₁ ≡ l* .proj₁ -> (k* ⁻¹) .proj₁ ≡ (l* ⁻¹) .proj₁
  inv-cong k*@(k , nzk) l*@(l , nzl) eq = begin
    (k* ⁻¹) .proj₁ ≡⟨ auto ⟩
    _⁻¹' k {{nztoℕ {neq0 = nzk}}}  ≡⟨ HE.≅-to-≡ aux ⟩
    _⁻¹' l {{nztoℕ {neq0 = nzl}}}  ≡⟨ auto ⟩
    (l* ⁻¹) .proj₁ ∎
    where
    open import Relation.Binary.HeterogeneousEquality as HE
    nzk=nzl : nzk ≅ nzl
    nzk=nzl = ≡-subst-removable (\ x -> x ≢ ₀) (Eq.sym eq) nzl
    
    aux : _⁻¹' k {{nztoℕ {neq0 = nzk}}} ≅ _⁻¹' l {{nztoℕ {neq0 = nzl}}}
    aux = HE.cong₂ (\ xx yy -> _⁻¹' xx {{nztoℕ {neq0 = yy}}}) (reflexive eq) nzk=nzl

    open Eq.≡-Reasoning


  aux-inv-xy : ∀ x y -> (y ⁻¹ *' x ⁻¹) .proj₁ * (x *' y) .proj₁ ≡ ₁
  aux-inv-xy x y = begin
    (y ⁻¹ *' x ⁻¹) .proj₁ * (x *' y) .proj₁ ≡⟨ *-assoc ((y ⁻¹) .proj₁) ((x ⁻¹) .proj₁) ((x *' y) .proj₁) ⟩
    (y ⁻¹) .proj₁ * ((x ⁻¹) .proj₁ * (x .proj₁ * y .proj₁)) ≡⟨ cong ((y ⁻¹) .proj₁ *_) (sym (*-assoc ((x ⁻¹) .proj₁) (x .proj₁) (y .proj₁))) ⟩
    (y ⁻¹) .proj₁ * ((x ⁻¹) .proj₁ * x .proj₁ * y .proj₁) ≡⟨ cong ((y ⁻¹) .proj₁ *_) (cong (_* y .proj₁) (lemma-⁻¹ˡ ( x .proj₁) {{nztoℕ {y = x .proj₁} {neq0 = x .proj₂}}})) ⟩
    (y ⁻¹) .proj₁ * (₁ * y .proj₁) ≡⟨ cong ((y ⁻¹) .proj₁ *_) (*-identityˡ (y .proj₁)) ⟩
    (y ⁻¹) .proj₁ * y .proj₁ ≡⟨ lemma-⁻¹ˡ (y .proj₁) {{nztoℕ {y = y .proj₁} {neq0 = y .proj₂}}} ⟩
    ₁ ∎
    where
    open Eq.≡-Reasoning

  inv-distrib : ∀ x y -> ((x *' y) ⁻¹) .proj₁ ≡ (x ⁻¹ *' y ⁻¹) .proj₁
  inv-distrib x y = begin
    ((x *' y) ⁻¹) .proj₁ ≡⟨ sym (*-identityˡ (((x *' y) ⁻¹) .proj₁)) ⟩
    1ₚ * ((x *' y) ⁻¹) .proj₁ ≡⟨ sym (cong (_* ((x *' y) ⁻¹) .proj₁) (aux-inv-xy x y)) ⟩
    (y ⁻¹ *' x ⁻¹) .proj₁ * (x *' y) .proj₁ * ((x *' y) ⁻¹) .proj₁ ≡⟨ *-assoc ((y ⁻¹ *' x ⁻¹) .proj₁) ((x *' y) .proj₁) (((x *' y) ⁻¹) .proj₁) ⟩
    (y ⁻¹ *' x ⁻¹) .proj₁ * ((x *' y) .proj₁ * ((x *' y) ⁻¹) .proj₁) ≡⟨ cong ((y ⁻¹ *' x ⁻¹) .proj₁ *_) ((lemma-⁻¹ʳ ((x *' y) .proj₁)) {{nztoℕ {y = (x *' y) .proj₁} {neq0 = (x *' y) .proj₂}}}) ⟩
    (y ⁻¹ *' x ⁻¹) .proj₁ * 1ₚ ≡⟨ *-identityʳ ((y ⁻¹ *' x ⁻¹) .proj₁) ⟩
    (y ⁻¹ *' x ⁻¹) .proj₁ ≡⟨ *-comm ((y ⁻¹) .proj₁) ((x ⁻¹) .proj₁) ⟩
    (x ⁻¹ *' y ⁻¹) .proj₁ ∎
    where
    open Eq.≡-Reasoning



  -1⁻¹ = - (((₁ , λ ())) ⁻¹) .proj₁
  -'₁ = -' (₁ , λ ())
  
  inv-neg₁ : -1⁻¹ ≡ - ₁
  inv-neg₁ = begin
    -1⁻¹ ≡⟨ cong -_ inv-₁ ⟩
    - ₁ ∎
    where
    open Eq.≡-Reasoning

  aux-₁² : - ₁ * - ₁ ≡ ₁
  aux-₁² = begin
    - ₁ * - ₁ ≡⟨ sym (-‿distribˡ-* ₁ (- ₁)) ⟩
    - (₁ * - ₁) ≡⟨ cong -_ (sym (-‿distribʳ-* ₁ ₁)) ⟩
    - - (₁ * ₁) ≡⟨ -‿involutive ₁ ⟩
    ₁ ∎
    where
    open Eq.≡-Reasoning

  aux-₁⁻¹ : let -'₁ = -' ((₁ , λ ())) in let -₁ = -'₁ .proj₁ in let -₁⁻¹ = (-'₁ ⁻¹) .proj₁ in
    -₁⁻¹ ≡ -₁
  aux-₁⁻¹ = begin
    -₁⁻¹ ≡⟨ sym (*-identityˡ -₁⁻¹) ⟩
    ₁ * -₁⁻¹ ≡⟨ cong (_* -₁⁻¹) (sym aux-₁²) ⟩
    (- ₁ * - ₁) * -₁⁻¹ ≡⟨ refl ⟩
    (-₁ * -₁) * -₁⁻¹ ≡⟨ *-assoc -₁ -₁ -₁⁻¹ ⟩
    -₁ * (-₁ * -₁⁻¹) ≡⟨ cong (-₁ *_) (lemma-⁻¹ʳ -₁ {{nztoℕ {y = -₁} {neq0 = -'₁ .proj₂}}}) ⟩
    -₁ * ₁ ≡⟨ *-identityʳ -₁ ⟩
    -₁ ∎
    where
    open Eq.≡-Reasoning

    -₁ = -'₁ .proj₁
    -₁⁻¹ = (-'₁ ⁻¹) .proj₁


  aux₁⁻¹' : let ₁⁻¹ = ((₁ , λ ()) ⁻¹) .proj₁ in
    ₁⁻¹ ≡ ₁
  aux₁⁻¹' = begin
    ₁⁻¹ ≡⟨ sym (*-identityˡ ₁⁻¹) ⟩
    ₁ * ₁⁻¹ ≡⟨ lemma-⁻¹ʳ ₁ {{nztoℕ {y = 1ₚ} {neq0 = λ ()}}} ⟩
    ₁ ∎
    where
    open Eq.≡-Reasoning

    ₁⁻¹ = ((₁ , λ ()) ⁻¹) .proj₁

  aux-1=-1 : (-'₁ .proj₁) ≡ ₋₁
  aux-1=-1 = Eq.sym p-1=-1ₚ

  aux-'x=-x : ∀ (x : ℤ* ₚ) -> ((-' x) .proj₁) ≡ - (x .proj₁)
  aux-'x=-x x = begin
    ((-' x) .proj₁) ≡⟨ refl ⟩
    - (x .proj₁) ∎
    where
    open Eq.≡-Reasoning


  inv-neg-comm : ∀ x -> ((-' x) ⁻¹) .proj₁ ≡ - (x ⁻¹) .proj₁
  inv-neg-comm x@(x' , nz) = begin
    ((-' x) ⁻¹) .proj₁ ≡⟨ sym (*-identityˡ (((-' x) ⁻¹) .proj₁)) ⟩
    ₁ * ((-' x) ⁻¹) .proj₁ ≡⟨ cong (_* ((-' x) ⁻¹) .proj₁) (sym aux) ⟩
    (- (x ⁻¹) .proj₁ * - x .proj₁) * ((-' x) ⁻¹) .proj₁  ≡⟨ *-assoc (- (x ⁻¹) .proj₁) (- x .proj₁) (((-' x) ⁻¹) .proj₁) ⟩
    - (x ⁻¹) .proj₁ * (- x .proj₁ * ((-' x) ⁻¹) .proj₁)  ≡⟨ cong (\ xx -> - (x ⁻¹) .proj₁ * (xx * ((-' x) ⁻¹) .proj₁)) (sym (aux-'x=-x x)) ⟩
    - (x ⁻¹) .proj₁ * ((-' x) .proj₁ * ((-' x) ⁻¹) .proj₁)  ≡⟨ cong (- (x ⁻¹) .proj₁ *_) (lemma-⁻¹ʳ ((-' x) .proj₁) {{nztoℕ {y = (-' x) .proj₁} {neq0 = (-' x) .proj₂}}}) ⟩
    - (x ⁻¹) .proj₁ * ₁  ≡⟨ *-identityʳ (- (x ⁻¹) .proj₁) ⟩
    - (x ⁻¹) .proj₁ ∎
    where
    open Eq.≡-Reasoning
    aux : (- (x ⁻¹) .proj₁ * - x .proj₁) ≡ ₁
    aux = begin
      (- (x ⁻¹) .proj₁ * - x .proj₁) ≡⟨ sym (-‿distribˡ-* ((x ⁻¹) .proj₁) (- x .proj₁)) ⟩
      - ((x ⁻¹) .proj₁ * - x .proj₁) ≡⟨ sym (cong -_ (-‿distribʳ-* ((x ⁻¹) .proj₁) (x .proj₁))) ⟩
      - - ((x ⁻¹) .proj₁ * x .proj₁) ≡⟨ -‿involutive (((x ⁻¹) .proj₁ * x .proj₁)) ⟩
      ((x ⁻¹) .proj₁ * x .proj₁) ≡⟨ lemma-⁻¹ˡ (x .proj₁) {{nztoℕ {y = x .proj₁} {neq0 = nz}}} ⟩
      ₁ ∎

  inv-inv-neg : ∀ x -> ((-' x ⁻¹) ⁻¹) .proj₁ ≡ - x .proj₁
  inv-inv-neg x = begin
    ((-' x ⁻¹) ⁻¹) .proj₁ ≡⟨ inv-neg-comm (x ⁻¹) ⟩
    - (x ⁻¹ ⁻¹) .proj₁ ≡⟨ cong -_ (inv-involutive x) ⟩
    - x .proj₁ ∎
    where
    open Eq.≡-Reasoning


  aux--b*-b⁻¹ : ∀ b' ->
    let 
      b = b' .proj₁
      -b⁻¹ = - ((b' ⁻¹) .proj₁)
      b⁻¹ = ((b' ⁻¹) .proj₁)
      -b = - b
    in -b * -b⁻¹ ≡ ₁
  aux--b*-b⁻¹ b' =
    let 
      b = b' .proj₁
      -b⁻¹ = - ((b' ⁻¹) .proj₁)
      b⁻¹ = ((b' ⁻¹) .proj₁)
      -b = - b
    in begin
      -b * -b⁻¹ ≡⟨ sym (-‿distribˡ-* b -b⁻¹) ⟩
      -(b * -b⁻¹) ≡⟨ cong -_ (sym (-‿distribʳ-* b b⁻¹)) ⟩
      - -(b * b⁻¹) ≡⟨ -‿involutive ((b * b⁻¹)) ⟩
      (b * b⁻¹) ≡⟨ lemma-⁻¹ʳ b {{nztoℕ {y = b} {neq0 = b' .proj₂} }} ⟩
      ₁ ∎
    where
    open Eq.≡-Reasoning


  aux-xxxx : ∀ x -> ((x ⁻¹ *' x ⁻¹) *' (x *' x)) .proj₁ ≡ ₁
  aux-xxxx x@(x0 , nz) = begin
    ((x ⁻¹ *' x ⁻¹) *' (x *' x)) .proj₁ ≡⟨ *-assoc x⁻¹ x⁻¹ (x0 * x0) ⟩
    (x ⁻¹ *' (x ⁻¹ *' (x *' x))) .proj₁ ≡⟨ cong ((x⁻¹ *_)) (sym (*-assoc x⁻¹ x0 x0)) ⟩
    (x ⁻¹ *' ((x ⁻¹ *' x) *' x)) .proj₁ ≡⟨ cong (\ xx -> x⁻¹ * (xx * x0)) (lemma-⁻¹ˡ x0 {{nztoℕ {y = x0} {neq0 = x .proj₂} }}) ⟩
    (x ⁻¹) .proj₁ * (₁ * x .proj₁) ≡⟨ cong ((x⁻¹ *_)) (*-identityˡ x0) ⟩
    (x ⁻¹) .proj₁ * x .proj₁ ≡⟨ lemma-⁻¹ˡ x0 {{nztoℕ {y = x0} {neq0 = x .proj₂} }} ⟩
    ₁ ∎
    where
    open Eq.≡-Reasoning
    x⁻¹ = (x ⁻¹) .proj₁

  aux--b⁻¹*-b : ∀ b' ->
    let 
      b = b' .proj₁
      -b⁻¹ = - ((b' ⁻¹) .proj₁)
      b⁻¹ = ((b' ⁻¹) .proj₁)
      -b = - b
    in -b⁻¹ * -b ≡ ₁

  aux--b⁻¹*-b b' = 
    let 
      b = b' .proj₁
      -b⁻¹ = - ((b' ⁻¹) .proj₁)
      b⁻¹ = ((b' ⁻¹) .proj₁)
      -b = - b
    in begin
      -b⁻¹ * -b ≡⟨ *-comm -b⁻¹ -b ⟩
      -b * -b⁻¹ ≡⟨ aux--b*-b⁻¹ b' ⟩
      ₁ ∎
    where
    open Eq.≡-Reasoning

  aux-k*-[-k]⁻¹ : ∀ k -> (k *' -' (-' k) ⁻¹) .proj₁ ≡ ₁
  aux-k*-[-k]⁻¹ k = begin
    (k *' -' (-' k) ⁻¹) .proj₁ ≡⟨ auto ⟩
    k .proj₁ * (-' (-' k) ⁻¹) .proj₁ ≡⟨ auto ⟩
    k .proj₁ * - (((-' k) ⁻¹) .proj₁) ≡⟨ cong (\ xx -> k .proj₁ * - xx) (inv-neg-comm k) ⟩
    k .proj₁ * - - ((k ⁻¹) .proj₁) ≡⟨ cong (k .proj₁ *_) (-‿involutive ((k ⁻¹) .proj₁)) ⟩
    k .proj₁ * ((k ⁻¹) .proj₁) ≡⟨ lemma-⁻¹ʳ (k .proj₁) {{nztoℕ {y = k .proj₁} {neq0 = k .proj₂}}} ⟩
    ₁ ∎
    where
    open Eq.≡-Reasoning

  aux-k⁻¹=-[-k⁻¹] : ∀ k -> (k ⁻¹) .proj₁ ≡ - (((-' k) ⁻¹) .proj₁)
  aux-k⁻¹=-[-k⁻¹] k = begin
    (k ⁻¹) .proj₁ ≡⟨ auto ⟩
    ( k ⁻¹) .proj₁ ≡⟨ sym (-‿involutive ( (k ⁻¹) .proj₁)) ⟩
    - - ( k ⁻¹) .proj₁ ≡⟨ Eq.cong -_ (sym (inv-neg-comm k)) ⟩
    - (((-' k) ⁻¹) .proj₁) ∎
    where
    open Eq.≡-Reasoning


  aux-₁-b : ∀ k* a* ->
    let
      a⁻¹ = (a* ⁻¹) .proj₁
      k = k* .proj₁
      -k = - k
      k⁻¹ = ((k* ⁻¹) .proj₁)
      -k⁻¹ = - k⁻¹
      b' = -' (k* ⁻¹) *' a*
      b = b' .proj₁
      -b = - b
      -b⁻¹* =  -' b' ⁻¹
      -b⁻¹ =  -b⁻¹* .proj₁
    in - ₁ * -b⁻¹ ≡ -k * a⁻¹
  aux-₁-b k* a* = begin
    - ₁ * -b⁻¹ ≡⟨ auto ⟩
    - ₁ * (-' (-' (k* ⁻¹) *' a*) ⁻¹) .proj₁ ≡⟨ -1*x≈-x ((-' (-' (k* ⁻¹) *' a*) ⁻¹) .proj₁) ⟩
    - (-' (-' (k* ⁻¹) *' a*) ⁻¹) .proj₁ ≡⟨ auto ⟩
    - - ((-' (k* ⁻¹) *' a*) ⁻¹) .proj₁ ≡⟨ -‿involutive (((-' (k* ⁻¹) *' a*) ⁻¹) .proj₁ ) ⟩
    ((-' (k* ⁻¹) *' a*) ⁻¹) .proj₁ ≡⟨ inv-distrib (-' (k* ⁻¹)) a* ⟩
    ((-' (k* ⁻¹)) ⁻¹ *' a* ⁻¹) .proj₁ ≡⟨ auto ⟩
    ((-' (k* ⁻¹)) ⁻¹) .proj₁ * (a* ⁻¹) .proj₁ ≡⟨ cong (_* (a* ⁻¹) .proj₁) (inv-neg-comm (k* ⁻¹)) ⟩
    - (( (k* ⁻¹)) ⁻¹) .proj₁ * (a* ⁻¹) .proj₁ ≡⟨ cong (_* (a* ⁻¹) .proj₁) (cong -_ (inv-involutive k*)) ⟩
    - k * (a* ⁻¹) .proj₁ ≡⟨ auto ⟩
    - k * a⁻¹ ∎
    where
    open Eq.≡-Reasoning
    a⁻¹ = (a* ⁻¹) .proj₁
    k = k* .proj₁
    -k = - k
    k⁻¹ = ((k* ⁻¹) .proj₁)
    -k⁻¹ = - k⁻¹
    b' = -' (k* ⁻¹) *' a*
    b = b' .proj₁
    -b = - b
    -b⁻¹* =  -' b' ⁻¹
    -b⁻¹ =  -b⁻¹* .proj₁


  aux--b⁻¹ : ∀ k* a* ->
    let
      a⁻¹ = (a* ⁻¹) .proj₁
      k = k* .proj₁
      -k = - k
      k⁻¹ = ((k* ⁻¹) .proj₁)
      -k⁻¹ = - k⁻¹
      b' = -' (k* ⁻¹) *' a*
      b = b' .proj₁
      -b = - b
      -b⁻¹* =  -' b' ⁻¹
      -b⁻¹ =  -b⁻¹* .proj₁
    in -b⁻¹ ≡ a⁻¹ * k
  aux--b⁻¹ k* a* = begin
    -b⁻¹ ≡⟨ auto ⟩
    (-' (-' (k* ⁻¹) *' a*) ⁻¹) .proj₁ ≡⟨ auto ⟩
    - (((-' (k* ⁻¹) *' a*) ⁻¹) .proj₁) ≡⟨ cong -_ (inv-distrib (-' (k* ⁻¹)) a*) ⟩
    - (((-' (k* ⁻¹)) ⁻¹ *' a* ⁻¹) .proj₁) ≡⟨ auto ⟩
    - (((-' (k* ⁻¹)) ⁻¹) .proj₁ * (a* ⁻¹) .proj₁) ≡⟨ cong -_ (cong (_* (a* ⁻¹) .proj₁) (inv-neg-comm (k* ⁻¹))) ⟩
    - (- (( (k* ⁻¹)) ⁻¹) .proj₁ * (a* ⁻¹) .proj₁) ≡⟨ cong -_ (cong (_* (a* ⁻¹) .proj₁) (cong -_ (inv-involutive k*))) ⟩
    - (- k * (a* ⁻¹) .proj₁) ≡⟨ -‿distribˡ-* (- k) ((a* ⁻¹) .proj₁) ⟩
    - - k * (a* ⁻¹) .proj₁ ≡⟨ cong (_* (a* ⁻¹) .proj₁) (-‿involutive k) ⟩
    k * (a* ⁻¹) .proj₁ ≡⟨ *-comm k a⁻¹ ⟩
    a⁻¹ * k ∎
    where
    open Eq.≡-Reasoning
    a⁻¹ = (a* ⁻¹) .proj₁
    k = k* .proj₁
    -k = - k
    k⁻¹ = ((k* ⁻¹) .proj₁)
    -k⁻¹ = - k⁻¹
    b' = -' (k* ⁻¹) *' a*
    b = b' .proj₁
    -b = - b
    -b⁻¹* =  -' b' ⁻¹
    -b⁻¹ =  -b⁻¹* .proj₁



  aux-a*-b⁻¹ : ∀ k* a* ->
    let
      a⁻¹ = (a* ⁻¹) .proj₁
      a = a* .proj₁
      -a = - a
      k = k* .proj₁
      k² = k * k
      -k = - k
      k⁻¹ = ((k* ⁻¹) .proj₁)
      -k⁻¹ = - k⁻¹
      b' = -' (k* ⁻¹) *' a*
      b = b' .proj₁
      -b = - b
      -b⁻¹* =  -' b' ⁻¹
      -b⁻¹ =  -b⁻¹* .proj₁
    in -a * -b⁻¹ ≡ -k
  aux-a*-b⁻¹ k* a* = begin
    -a * -b⁻¹ ≡⟨ cong (-a *_) (aux--b⁻¹ k* a*) ⟩
    -a * (a⁻¹ * k) ≡⟨ sym (*-assoc -a a⁻¹ k) ⟩
    -a * a⁻¹ * k ≡⟨ cong (_* k) (sym (-‿distribˡ-* a a⁻¹)) ⟩
    -(a * a⁻¹) * k ≡⟨ cong (_* k) (cong -_ (lemma-⁻¹ʳ a {{nztoℕ {y = a} {neq0 = a* .proj₂}}})) ⟩
    - ₁ * k ≡⟨ -1*x≈-x k ⟩
    - k ∎
    where
    open Eq.≡-Reasoning
    a⁻¹ = (a* ⁻¹) .proj₁
    a = a* .proj₁
    -a = - a
    k = k* .proj₁
    -k = - k
    k⁻¹ = ((k* ⁻¹) .proj₁)
    -k⁻¹ = - k⁻¹
    b' = -' (k* ⁻¹) *' a*
    b = b' .proj₁
    -b = - b
    -b⁻¹* =  -' b' ⁻¹
    -b⁻¹ =  -b⁻¹* .proj₁



  lemma-toℕ-% : ∀ (a b : ℤ ₚ) -> (toℕ a ℕ.* toℕ b) % p ≡ toℕ (a * b)
  lemma-toℕ-% a b = begin
    (toℕ a ℕ.* toℕ b) % p ≡⟨ sym (toℕ-fromℕ< (m%n<n (toℕ a ℕ.* toℕ b) p)) ⟩
    toℕ (a * b) ∎
    where
    open Eq.≡-Reasoning


  lemma-x^′1=x : ∀ (x : ℤ ₚ) -> x ^′ 1 ≡ x
  lemma-x^′1=x x@₀ = auto
  lemma-x^′1=x x@(₁₊ _) = begin
    x ^′ 1 ≡⟨ auto ⟩
    x * (x ^′ 0) ≡⟨ auto ⟩
    x * ₁ ≡⟨ *-identityʳ x ⟩
    x ∎
    where
    open ≡-Reasoning

  lemma-x^′k≠0 : ∀ x k -> x ≢ ₀ -> x ^′ k ≢ 0ₚ
  lemma-x^′k≠0 x ₀ nz = λ ()
  lemma-x^′k≠0 x (₁₊ k) nz = xx .proj₂
    where
    xx = (x , nz) *' (x ^′ k , lemma-x^′k≠0 x k nz)

  infixr 8 _^'_
  _^'_ : ℤ* ₚ → ℕ → ℤ* ₚ 
  _^'_ (x , nz) k = (x ^′ k) , (lemma-x^′k≠0 x k nz)


  *-^′-distribʳ : ∀ (x y : ℤ ₚ) k -> (x * y) ^′ k ≡ x ^′ k * y ^′ k
  *-^′-distribʳ x y 0 = auto
  *-^′-distribʳ x y k@(₁₊ k') = begin
    (x * y) ^′ k ≡⟨ auto ⟩
    (x * y) * (x * y) ^′ k' ≡⟨ Eq.cong ((x * y) *_) ( *-^′-distribʳ x y k') ⟩
    (x * y) * (x ^′ k' * y ^′ k') ≡⟨ *-assoc x y (x ^′ k' * y ^′ k') ⟩
    x * (y * (x ^′ k' * y ^′ k')) ≡⟨ Eq.sym (Eq.cong (x *_) (*-assoc y (x ^′ k') (y ^′ k'))) ⟩
    x * ((y * x ^′ k') * y ^′ k') ≡⟨ Eq.cong (\ xx -> x * ((xx) * y ^′ k')) (*-comm y (x ^′ k')) ⟩
    x * ((x ^′ k' * y) * y ^′ k') ≡⟨ Eq.cong (x *_) (*-assoc (x ^′ k') y (y ^′ k')) ⟩
    x * (x ^′ k' * (y * y ^′ k')) ≡⟨ Eq.sym (*-assoc x (x ^′ k') (y * y ^′ k')) ⟩
    (x * x ^′ k') * (y * y ^′ k') ≡⟨ auto ⟩
    x ^′ k * y ^′ k ∎
    where
    open ≡-Reasoning

  +-^′-distribʳ : ∀ (x : ℤ ₚ) k l -> x ^′ k * x ^′ l ≡ x ^′ (k ℕ.+ l)
  +-^′-distribʳ x k@0 l = begin
    x ^′ k * x ^′ l ≡⟨ auto ⟩
    ₁ * x ^′ l ≡⟨ *-identityˡ (x ^′ l) ⟩
    x ^′ (k ℕ.+ l) ∎
    where
    open ≡-Reasoning
  +-^′-distribʳ x k@(₁₊ k') l = begin
    x ^′ k * x ^′ l ≡⟨ *-assoc x (x ^′ k') (x ^′ l) ⟩
    x * (x ^′ k' * x ^′ l) ≡⟨ Eq.cong (x *_) (+-^′-distribʳ x k' l) ⟩
    x * (x ^′ (k' ℕ.+ l)) ≡⟨ auto ⟩
    (x ^′ ₁₊ (k' ℕ.+ l)) ≡⟨ auto ⟩
    x ^′ (k ℕ.+ l) ∎
    where
    open ≡-Reasoning

  1^k=1 : ∀ k -> ₁ ^′ k ≡ 1ₚ
  1^k=1 k@0 = auto
  1^k=1 k@(₁₊ k') = begin
    ₁ ^′ k ≡⟨ auto ⟩
    ₁ * ₁ ^′ k' ≡⟨ *-identityˡ (₁ ^′ k') ⟩
    ₁ ^′ k' ≡⟨ 1^k=1 k' ⟩
    ₁ ∎
    where
    open ≡-Reasoning


  x^1=x : ∀ (x : ℤ ₚ) -> x ^′ 1 ≡ x
  x^1=x x = begin
    x * x ^′ 0 ≡⟨ Eq.cong (x *_) auto ⟩
    x * ₁ ≡⟨ *-identityʳ x ⟩
    x ∎
    where
    open ≡-Reasoning

  lemma-^^-comm : ∀ (x : ℤ ₚ) k l -> x ^′ l ^′ k ≡ x ^′ k ^′ l
  lemma-^^-* : ∀ (x : ℤ ₚ) k l -> x ^′ (k ℕ.* l) ≡ x ^′ k ^′ l

  lemma-^^-comm x k@0 l = begin
    x ^′ l ^′ k ≡⟨ auto ⟩
    ₁ ≡⟨ Eq.sym (1^k=1 l) ⟩
    ₁ ^′ l ≡⟨ auto ⟩
    x ^′ k ^′ l ∎
    where
    open ≡-Reasoning
  lemma-^^-comm x k@(₁₊ k') l = begin
    x ^′ l ^′ k ≡⟨ auto ⟩
    x ^′ l * x ^′ l ^′ k' ≡⟨ Eq.cong (x ^′ l *_) (lemma-^^-comm x k' l) ⟩
    (x ^′ l) * (x ^′ k') ^′ l  ≡⟨ Eq.sym (*-^′-distribʳ x (x ^′ k') l) ⟩
    (x * x ^′ k') ^′ l  ≡⟨ auto ⟩
    x ^′ k ^′ l ∎
    where
    open ≡-Reasoning

  lemma-^^-* x ₀ l = Eq.sym (1^k=1 l)
  lemma-^^-* x k@(₁₊ k') l = begin
    x ^′ (k ℕ.* l) ≡⟨ auto ⟩
    x ^′ (l ℕ.+ k' ℕ.* l) ≡⟨ Eq.sym (+-^′-distribʳ x l (k' ℕ.* l)) ⟩
    x ^′ l * x ^′ (k' ℕ.* l) ≡⟨ Eq.cong (x ^′ l *_) (lemma-^^-* x k' l) ⟩
    x ^′ l * x ^′ k' ^′ l ≡⟨ Eq.cong (x ^′ l *_) (lemma-^^-comm x l k') ⟩
    x ^′ l * x ^′ l ^′ k' ≡⟨ Eq.cong (_* x ^′ l ^′ k') (Eq.sym (x^1=x (x ^′ l))) ⟩
    x ^′ l ^′ 1 * x ^′ l ^′ k' ≡⟨ +-^′-distribʳ (x ^′ l) 1 k' ⟩
    x ^′ l ^′ ₁₊ k' ≡⟨ lemma-^^-comm x k l ⟩
    x ^′ k ^′ l ∎
    where
    open ≡-Reasoning

{-

module PrimeModulus' (p-3 : ℕ) (p-prime : Prime (₃₊ p-3)) where
  p-2 : ℕ
  p-2 = ₁₊ p-3

  open PrimeModulus p-2 p-prime public


  module Primitive-Root-Modp
    (g : ℤ ₚ)
    (g-gen : ∀ ((x , _) : ℤ* ₚ) -> ∃ \ (k : ℤ ₚ-₁) -> x ≡ g ^′ toℕ k )
    (Fermat's-little-theorem : g ^′ p-1 ≡ 1ₚ)
    where

    g-gen1 = g-gen (₁ , λ ())
    g-gen2 = g-gen (₂ , λ ())
    g≠0 : g ≢ ₀
    g≠0 eq0 with g-gen2
    g≠0 eq0 | (suc k , eq) rewrite eq0 | lemma-0^′k {p-2} (toℕ k) with eq
    g≠0 eq0 | (suc k , eq) | ()
    g≠0 eq0 | (₀ , eq) with eq
    g≠0 eq0 | (₀ , eq) | ()

    lemma-g^′k≠0 : ∀ k -> g ^′ k ≢ 0ₚ
    lemma-g^′k≠0 k = lemma-x^′k≠0 g k g≠0


    lemma-g^′1=g : g ^′ 1 ≡ g
    lemma-g^′1=g = lemma-x^′1=x g


    g′ : ℤ* ₚ
    g′ = (g , g≠0)

    g^_ : ∀ (k : ℤ ₚ) -> ℤ* ₚ
    g^_ k = (g ^′ toℕ k , lemma-g^′k≠0 (toℕ k))

    g^′_ : ∀ k -> ℤ* ₚ
    g^′_ k = (g ^′ k , lemma-g^′k≠0 k)


    open import Algebra.Properties.Ring (+-*-ring p-2)

    aux-g^′-% : ∀ k -> g ^′ k ≡ g ^′ (k ℕ.% p-1)
    aux-g^′-% k = begin
      g ^′ k ≡⟨ Eq.cong (g ^′_) ( m≡m%n+[m/n]*n k p-1) ⟩
      g ^′ (k%p-1 ℕ.+ k/p-1 ℕ.* p-1) ≡⟨ Eq.sym (+-^′-distribʳ g k%p-1 ((k/p-1 ℕ.* p-1))) ⟩
      g ^′ k%p-1 * g ^′ (k/p-1 ℕ.* p-1) ≡⟨ Eq.cong (\ xx -> g ^′ k%p-1 * g ^′ xx) (NP.*-comm k/p-1 p-1) ⟩
      g ^′ k%p-1 * g ^′ (p-1 ℕ.* k/p-1) ≡⟨ Eq.cong (g ^′ k%p-1 *_) ( (lemma-^^-* g p-1 k/p-1)) ⟩
      g ^′ k%p-1 * (g ^′ p-1) ^′ k/p-1 ≡⟨ Eq.cong (\ xx -> g ^′ k%p-1 * xx ^′ k/p-1) Fermat's-little-theorem ⟩
      g ^′ k%p-1 * 1ₚ ^′ k/p-1 ≡⟨ Eq.cong (\ xx -> g ^′ k%p-1 * xx) (1^k=1 k/p-1) ⟩
      g ^′ k%p-1 * 1ₚ ≡⟨ *-identityʳ (g ^′ k%p-1) ⟩
      g ^′ k%p-1 ≡⟨ auto ⟩
      g ^′ (k ℕ.% p-1) ∎
      where
      open ≡-Reasoning
      k%p-1 = k ℕ.% p-1
      k/p-1 = k ℕ./ p-1


    log : ℤ* ₚ -> ℤ ₚ-₁
    log  x = g-gen x .proj₁


    lemma-inject : ∀ (x : ℤ ₚ-₁) -> g ^′ toℕ x ≡ (g^ (inject₁ x)) .proj₁
    lemma-inject  x = begin
      g ^′ toℕ x ≡⟨ Eq.cong (g ^′_) (Eq.sym (toℕ-inject₁ x) ) ⟩
      g ^′ toℕ (inject₁ x) ≡⟨ auto ⟩
      (g^ inject₁ x) .proj₁ ∎
      where
      open ≡-Reasoning

    lemma-log-inject : ∀ (x : ℤ* ₚ) -> (g^ (inject₁ (log x))) .proj₁ ≡ x .proj₁
    lemma-log-inject x = begin
      (g^ (inject₁ (log x))) .proj₁ ≡⟨ Eq.sym (lemma-inject (log x)) ⟩
      g ^′ toℕ (log x) ≡⟨ Eq.sym (g-gen x .proj₂) ⟩
      x .proj₁ ∎
      where
      open ≡-Reasoning


    Fermat's-little-theorem : g ^′ p-1 ≡ 1ₚ
    Fermat's-little-theorem with g-gen (g ^′ p-1 , {!!}) -- lemma-g^′k≠0 p-1
    ... | k@₀ , eq = begin
      g ^′ p-1 ≡⟨ eq ⟩
      g ^′ toℕ k ≡⟨ auto ⟩
      1ₚ ∎
      where
      open ≡-Reasoning
    ... | k@(₁₊ _) , eq = {!aux-5!}
      where
      open ≡-Reasoning
      aux-1 : g ^′ p-1 + - (g ^′ toℕ k) ≡ 0ₚ
      aux-1 = begin
        g ^′ p-1 + - (g ^′ toℕ k) ≡⟨ Eq.cong (\ xx -> g ^′ p-1 + - (xx)) (Eq.sym eq) ⟩
        g ^′ p-1 + - (g ^′ p-1) ≡⟨ +-inverseʳ (g ^′ p-1) ⟩
        0ₚ ∎
      l = toℕ k
      aux-2 : (g ^′ (p-1 ∸ l)  + - 1ₚ) * (g ^′ l) ≡ 0ₚ
      aux-2 = begin
        (g ^′ (p-1 ∸ l)  + - 1ₚ) * (g ^′ l) ≡⟨ *-distribʳ-+ (g ^′ l) (g ^′ (p-1 ∸ l)) (- 1ₚ) ⟩
        g ^′ (p-1 ∸ l) * (g ^′ l)  + - 1ₚ * (g ^′ l) ≡⟨ Eq.cong₂ _+_ (+-^′-distribʳ g (p-1 ∸ l) l) (-1*x≈-x (g ^′ l)) ⟩
        g ^′ ((p-1 ∸ l) ℕ.+ l)  + - ((g ^′ l)) ≡⟨ Eq.cong (\ xx -> g ^′ xx  + - ((g ^′ l))) (Eq.sym (NP.+-∸-comm l (FP.toℕ≤n k))) ⟩
        g ^′ ((p-1 ℕ.+ l) ∸ l )  + - ((g ^′ l)) ≡⟨ Eq.cong (\ xx -> g ^′ xx  + - ((g ^′ l))) (NP.m+n∸n≡m p-1 l) ⟩
        g ^′ (p-1) + - ((g ^′ l)) ≡⟨ aux-1 ⟩
        0ₚ ∎
      aux-3 : (g ^′ (p-1 ∸ l)  + - 1ₚ)  ≡ 0ₚ
      aux-3 = begin
        (g ^′ (p-1 ∸ l)  + - 1ₚ) ≡⟨ Eq.sym (*-identityʳ (g ^′ (p-1 ∸ l)  + - 1ₚ)) ⟩
        (g ^′ (p-1 ∸ l)  + - 1ₚ) * ₁ ≡⟨ Eq.cong ((g ^′ (p-1 ∸ l)  + - 1ₚ) *_) (Eq.sym (lemma-⁻¹ʳ (g ^′ l) {{nztoℕ {y = g ^′ l} {neq0 = lemma-g^′k≠0 l}}})) ⟩
        (g ^′ (p-1 ∸ l)  + - 1ₚ) * ((g ^′ l) * glinv)  ≡⟨ Eq.sym (*-assoc ((g ^′ (p-1 ∸ l)  + - 1ₚ)) ((g ^′ l)) glinv) ⟩
        ((g ^′ (p-1 ∸ l)  + - 1ₚ) * g ^′ l) * glinv  ≡⟨ Eq.cong (_* glinv) aux-2 ⟩
        0ₚ * glinv  ≡⟨ *-zeroˡ glinv ⟩
        0ₚ ∎
        where
        glinv = _⁻¹' (g ^′ l) {{nztoℕ {y = g ^′ l} {neq0 = lemma-g^′k≠0 l}}}

      aux-3b : (g ^′ (p-1 ∸ l)  + - 1ₚ)  ≡ 1ₚ + - 1ₚ
      aux-3b = Eq.trans aux-3 (Eq.sym (+-inverseʳ 1ₚ))

      aux-4 : g ^′ (p-1 ∸ l) ≡ 1ₚ
      aux-4 = begin
        g ^′ (p-1 ∸ l) ≡⟨ +-cancelʳ (- 1ₚ) (g ^′ (p-1 ∸ l)) 1ₚ aux-3b ⟩
        1ₚ ∎

      aux-5 : g ^′ (p-1 ∸ l) ^′ l ≡ 1ₚ
      aux-5 = begin
        g ^′ (p-1 ∸ l) ^′ l ≡⟨ Eq.cong (_^′ l) aux-4 ⟩
        1ₚ ^′ l ≡⟨ 1^k=1 l ⟩
        1ₚ ∎

  --    ok = _⁻¹' (p-1 ∸ l) {{?}} *  = p-1
      aux-6 : g ^′ p-1 ≡ 1ₚ
      aux-6 = begin
        g ^′ p-1 ≡⟨ Eq.cong (g ^′_) (Eq.sym (NP.m+n∸n≡m p-1 l)) ⟩
        g ^′ ((p-1 ℕ.+ l) ∸ l) ≡⟨ Eq.cong (g ^′_) (NP.+-∸-comm l (FP.toℕ≤n k)) ⟩
        g ^′ ((p-1 ∸ l) ℕ.+ l) ≡⟨ {!!} ⟩
        g ^′ (p-1 ∸ l) ^′ l ≡⟨ {!!} ⟩
        1ₚ ∎

    lemma-g^′p-1 : g ^′ p-1 ≡ 1ₚ
    lemma-g^′p-1 = begin
      g ^′ p-1 ≡⟨ {!!} ⟩
      1ₚ ∎
      where
      open ≡-Reasoning
  -}

