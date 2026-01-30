{-# OPTIONS  --safe #-}
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



module N.Ex-Sym4n4 (p-2 : ℕ) (p-prime : Prime (2+ p-2))  where

private
  variable
    n : ℕ

pattern auto = Eq.refl

pattern ₀ = zero
pattern ₁ = suc ₀
pattern ₂ = suc ₁
pattern ₃ = suc ₂
pattern ₄ = 4
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
open import N.Symplectic p-2 p-prime
open import N.Lemmas-2Qupit-Sym p-2 p-prime
open import N.NF2-Sym p-2 p-prime
open import N.Cosets p-2 p-prime

open Symplectic
open import N.NF1-Sym p-2 p-prime
open import N.Ex-Sym p-2 p-prime
open import N.Ex-Sym1 p-2 p-prime
open import N.Ex-Sym2 p-2 p-prime
open import N.Ex-Sym3 p-2 p-prime
open import N.Ex-Sym3n p-2 p-prime
open import N.Ex-Sym4n p-2 p-prime as Sym4n
open import N.Ex-Sym4n2 p-2 p-prime as Sym4n2
open import N.Ex-Sym4n3 p-2 p-prime as Sym4n3
open import N.Ex-Sym2n p-2 p-prime as Sym2n hiding (lemma-XCS^k')

open import N.Ex-Rewriting p-2 p-prime

open import N.Lemma-Comm p-2 p-prime
open import N.Lemma-Postfix p-2 p-prime
open import N.Lemmas4-Sym p-2 p-prime
open import N.Duality p-2 p-prime hiding (module L0)
open Lemmas0a
open Lemmas0a1
open Lemmas0b
open Lemmas0c
open import N.LM-Sym p-2 p-prime

open LM2
open import N.Completeness1-Sym p-2 p-prime renaming (module Completeness to CP1) using ()


open Symplectic
open Lemmas-Sym
open Symplectic-GroupLike

open import Data.Nat.DivMod
open import Data.Fin.Properties
open Duality

open import Algebra.Properties.Ring (+-*-ring p-2)

lemma-semi-CZ^k-CX : let open PB ((₂₊ n) QRel,_===_) in ∀ (k : ℤ ₚ) ->

  CZ^ k • CX ≈ S^ (k + k) ↑ • CX • CZ^ k

lemma-semi-CZ^k-CX  {n} k = bbc (S^ (- k + - k) ↑) ε claim
  where
  aux : - k + - k + (k + k) ≡ ₀
  aux = begin
    - k + - k + (k + k) ≡⟨ +-assoc (- k) (- k) (k + k) ⟩
    - k + (- k + (k + k)) ≡⟨ Eq.cong (- k +_) (Eq.sym (+-assoc (- k) k k)) ⟩
    - k + (- k + k + k) ≡⟨ Eq.cong (- k +_) (Eq.cong (_+ k) (+-inverseˡ k)) ⟩
    - k + (₀ + k) ≡⟨ Eq.cong (- k +_)  (+-identityˡ k) ⟩
    - k + k ≡⟨ +-inverseˡ k ⟩
    ₀ ∎
    where
    open ≡-Reasoning
    
  open PB ((₂₊ n) QRel,_===_)
  open PP ((₂₊ n) QRel,_===_)
  open SR word-setoid
  open Lemmas0 n
  open Basis-Change _ ((₂₊ n) QRel,_===_) grouplike
  claim : S^ (- k + - k) ↑ • (CZ^ k • CX) • ε ≈ S^ (- k + - k) ↑ • (S^ (k + k) ↑ • CX • CZ^ k) • ε
  claim = begin
    S^ (- k + - k) ↑ • (CZ^ k • CX) • ε ≈⟨ (cright right-unit) ⟩
    S^ (- k + - k) ↑ • (CZ^ k • CX) ≈⟨ sym (lemma-semi-CXCZ^ k) ⟩
    CX • CZ^ k ≈⟨ sym left-unit ⟩
    S^ ₀ ↑ • CX • CZ^ k ≈⟨ (cleft refl' (Eq.cong (\ xx -> S^ xx ↑) (Eq.sym aux))) ⟩
    S^ (- k + - k + (k + k)) ↑ • CX • CZ^ k ≈⟨ sym (cleft lemma-cong↑ _ _ ( lemma-S^k+l (- k + - k) (k + k))) ⟩
    (S^ (- k + - k) ↑ • S^ (k + k) ↑) • CX • CZ^ k ≈⟨ assoc ⟩
    S^ (- k + - k) ↑ • (S^ (k + k) ↑ • CX • CZ^ k) ≈⟨ (cright sym right-unit) ⟩
    S^ (- k + - k) ↑ • (S^ (k + k) ↑ • CX • CZ^ k) • ε ∎

lemma-CZ^k-CX : let open PB ((₂₊ n) QRel,_===_) in ∀ (k : ℤ ₚ) ->

  CZ^ k • CX ≈ S^ k • CX • S^ (- k) • S^ k ↑

lemma-CZ^k-CX {n} k = begin
  CZ^ k • CX ≈⟨ lemma-semi-CZ^k-CX k ⟩
  S^ (k + k) ↑ • CX • CZ^ k ≈⟨ (cright lemma-semi-CXCZ^-alt k) ⟩
  S^ (k + k) ↑ • S^ k • CX • S^ (- k) • S^ (- k) ↑ ≈⟨ sym assoc ⟩
  (S^ (k + k) ↑ • S^ k) • CX • S^ (- k) • S^ (- k) ↑ ≈⟨ (cleft sym (lemma-comm-Sᵏ-w↑ (toℕ k) (S^ (k + k)))) ⟩
  (S^ k • S^ (k + k) ↑) • CX • S^ (- k) • S^ (- k) ↑ ≈⟨ special-assoc (□ ^ 2 • □ ^ 2) (□ • □ ^ 2 • □) auto ⟩
  S^ k • (S^ (k + k) ↑ • CX) • S^ (- k) • S^ (- k) ↑ ≈⟨ (cright cleft sym (aux-comm-CX-S^k↑ n (k + k))) ⟩
  S^ k • (CX • S^ (k + k) ↑) • S^ (- k) • S^ (- k) ↑ ≈⟨ (cright special-assoc (□ ^ 2 • □ ^ 2) (□ • □ ^ 2 • □) auto) ⟩
  S^ k • CX • (S^ (k + k) ↑ • S^ (- k)) • S^ (- k) ↑ ≈⟨ (cright cright cleft sym (lemma-comm-Sᵏ-w↑ (toℕ (- k)) (S^ (k + k)))) ⟩
  S^ k • CX • (S^ (- k) • S^ (k + k) ↑) • S^ (- k) ↑ ≈⟨ (cright cright assoc) ⟩
  S^ k • CX • S^ (- k) • S^ (k + k) ↑ • S^ (- k) ↑ ≈⟨ (cright cright cright lemma-cong↑ _ _ (lemma-S^k+l (k + k) (- k))) ⟩
  S^ k • CX • S^ (- k) • S^ (k + k + - k) ↑ ≈⟨ (cright cright cright refl' (Eq.cong (\ xx -> S^ xx ↑) (Eq.trans (Eq.trans (+-assoc k k (- k)) (Eq.cong (k +_) (+-inverseʳ k))) (+-identityʳ k)))) ⟩
  S^ k • CX • S^ (- k) • S^ k ↑ ∎
  where
  open PB ((₂₊ n) QRel,_===_)
  open PP ((₂₊ n) QRel,_===_)
  open SR word-setoid
  open Pattern-Assoc
  open Lemmas0 n

lemma-CZ^k-CX-alt : let open PB ((₂₊ n) QRel,_===_) in ∀ (k : ℤ ₚ) ->

  CZ^ k • CX ≈ S^ k ↑ • S^ k • CX • S^ (- k)

lemma-CZ^k-CX-alt {n} k = begin
  CZ^ k • CX ≈⟨ lemma-CZ^k-CX k ⟩
  S^ k • CX • S^ (- k) • S^ k ↑ ≈⟨ (cright cright lemma-comm-Sᵏ-w↑ (toℕ (- k)) (S^ k)) ⟩
  S^ k • CX • S^ k ↑ • S^ (- k) ≈⟨ sym (cong refl assoc) ⟩
  S^ k • (CX • S^ k ↑) • S^ (- k) ≈⟨ (cright cleft aux-comm-CX-S^k↑ n k) ⟩
  S^ k • (S^ k ↑ • CX) • S^ (- k) ≈⟨ sym (special-assoc (□ ^ 2 • □ ^ 2) (□ • □ ^ 2 • □) auto) ⟩
  (S^ k • S^ k ↑) • CX • S^ (- k) ≈⟨ (cleft lemma-comm-Sᵏ-w↑ (toℕ (k)) (S^ k)) ⟩
  (S^ k ↑ • S^ k) • CX • S^ (- k) ≈⟨ assoc ⟩
  S^ k ↑ • S^ k • CX • S^ (- k) ∎
  where
  open PB ((₂₊ n) QRel,_===_)
  open PP ((₂₊ n) QRel,_===_)
  open SR word-setoid
  open Pattern-Assoc
  open Lemmas0 n
