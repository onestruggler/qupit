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

open import Word.Base as WB hiding (wfoldl ; _*)
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



module N.Pauli (p-2 : ℕ) (p-prime : Prime (2+ p-2))  where

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


open import Zp.ModularArithmetic
open PrimeModulus p-2 p-prime


Pauli1 = ℤ ₚ × ℤ ₚ

Pauli : ℕ → Set
Pauli n = Vec Pauli1 n

sform1 : Pauli1 → Pauli1 → ℤ ₚ
sform1 (a , b) (c , d) = (- a) * d + c * b

sform : ∀ {n} → Pauli n → Pauli n → ℤ ₚ
sform {₀} [] [] = ₀
sform {₁₊ n} (x ∷ ps) (y ∷ qs) = sform1 x y + sform ps qs


cong₃ : ∀ {A B C D : Set}(f : A → B → C → D) {x y u v a b} → x ≡ y → u ≡ v → a ≡ b → f x u a  ≡ f y v b
cong₃ f Eq.refl Eq.refl Eq.refl = Eq.refl


pIₙ : ∀ {n} → Pauli n
pIₙ {₀} = []
pIₙ {₁₊ n} = (₀ , ₀) ∷ pIₙ {n}

pZ : Pauli1
pZ = (₀ , ₁)

pX : Pauli1
pX = (₁ , ₀)

pI : Pauli1
pI = (₀ , ₀)

pZₙ : ∀ {n} → Pauli n
pZₙ {₀} = []
pZₙ {₁} = pZ ∷ []
pZₙ {₁₊ n} = pI ∷ pZₙ

pXₙ : ∀ {n} → Pauli n
pXₙ {₀} = []
pXₙ {₁} = pX ∷ []
pXₙ {₁₊ n} = pI ∷ pXₙ

pX₀ : ∀ {n} → Pauli n
pX₀ {₀} = []
pX₀ {₁₊ n} = pX ∷ pIₙ

pZ₀ : ∀ {n} → Pauli n
pZ₀ {₀} = []
pZ₀ {₁₊ n} = pZ ∷ pIₙ

pX₀Z₀ : ∀ {n} (e : ℤ ₚ) → Pauli n
pX₀Z₀ {₀} e = []
pX₀Z₀ {₁₊ n} e = (₁ , e) ∷ pIₙ

pXₙZₙ : ∀ {n} (e : ℤ ₚ) → Pauli n
pXₙZₙ {₀} e = []
pXₙZₙ {₁} e = (₁ , e) ∷ []
pXₙZₙ {₁₊ n} e = pI ∷ pXₙZₙ e

pXZ : ∀ (e : ℤ ₚ) → Pauli1
pXZ e = (₁ , e)


open import Algebra.Properties.Ring (+-*-ring p-2)

sform1-antisym : ∀ (p q : Pauli1) -> sform1 p q ≡ - sform1 q p
sform1-antisym p@(a , b) q@(c , d) = begin
  sform1 (a , b) (c , d) ≡⟨ auto ⟩
  (- a) * d + c * b ≡⟨ +-comm (- a * d) (c * b) ⟩
  (c * b) + - a * d ≡⟨ Eq.cong (_+ - a * d) (Eq.cong (_* b) (Eq.sym (-‿involutive c))) ⟩
  (- - c * b) + - a * d ≡⟨ Eq.cong₂ _+_ (Eq.sym (-‿distribˡ-* (- c) b)) (Eq.sym (-‿distribˡ-* a d)) ⟩
  - (- c * b) + - (a * d) ≡⟨ (-‿+-comm (- c * b) (a * d)) ⟩
  - ((- c) * b + a * d) ≡⟨ auto ⟩
  - sform1 (c , d) (a , b) ∎
  where
  open ≡-Reasoning

sform-antisym1 : ∀ (p q : Pauli 1) -> sform p q ≡ - sform q p
sform-antisym1 p@((a , b) ∷ []) q@((c , d) ∷ []) = begin
  sform1 (a , b) (c , d) + ₀ ≡⟨ +-identityʳ (sform1 (a , b) (c , d)) ⟩
  sform1 (a , b) (c , d) ≡⟨ sform1-antisym (a , b) (c , d) ⟩
  - sform1 (c , d) (a , b) ≡⟨ Eq.cong -_ (Eq.sym (+-identityʳ (sform1 (c , d) (a , b)))) ⟩
  - (sform1 (c , d) (a , b) + ₀) ∎
  where
  open ≡-Reasoning
