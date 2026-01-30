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



module N.BR2.Three.Lemmas4 (p-2 : ℕ) (p-prime : Prime (2+ p-2))  where

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
open import N.Lemmas-2Qupit-Sym3 p-2 p-prime
open import N.NF2-Sym p-2 p-prime
--open Lemmas-2Q 2

open import N.NF1 p-2 p-prime
open import N.Ex-Sym p-2 p-prime
open import N.Ex-Sym1 p-2 p-prime
open import N.Ex-Sym2 p-2 p-prime
open import N.Ex-Sym3 p-2 p-prime
open import N.Ex-Sym4 p-2 p-prime hiding (lemma-Ex-S^ᵏ↑)
open import N.Ex-Sym5 p-2 p-prime hiding (module L0)
open import N.Ex-Sym2n p-2 p-prime
open import N.Ex-Sym3n p-2 p-prime
open import N.Ex-Sym4n p-2 p-prime
open import N.Ex-Sym4n2 p-2 p-prime
open import N.Ex-Sym4n3 p-2 p-prime
open import N.Ex-Sym4n4 p-2 p-prime

open import N.Lemma-Comm-n p-2 p-prime 0
open import N.Completeness1-Sym p-2 p-prime renaming (module Completeness to Cp1)
open Lemmas0a
open Lemmas0a1
open Lemmas0b
open Lemmas0c
open Lemmas-Sym
open Duality

open import N.Completeness1-Sym p-2 p-prime renaming (module Completeness to CP1) using ()
open import N.Coset2-Update-Sym p-2 p-prime renaming (module Completeness to CP2) using ()
open import N.Lemmas4-Sym p-2 p-prime as L4
open import N.Lemmas-3Q p-2 p-prime
open import N.Pushing.DH p-2 p-prime
open import N.Duality p-2 p-prime
open import N.BR2.Calculations p-2 p-prime
open import N.BR2.Three.Lemmas p-2 p-prime
open import N.BR2.Three.Lemmas2 p-2 p-prime
open import N.BR2.Three.Lemmas3 p-2 p-prime

open PB (3 QRel,_===_)
open PP (3 QRel,_===_)
-- module B2 = PB (2 QRel,_===_)
-- module P2 = PP (2 QRel,_===_)
-- module B1 = PB (1 QRel,_===_)
-- module P1 = PP (1 QRel,_===_)
open SR word-setoid
open Pattern-Assoc
open Lemmas0 1
--module L02 = Lemmas0 2
open Lemmas-2Q 1
--module L2Q0 = Lemmas-2Q 0
open Sym0-Rewriting 2
module Sym01 = Sym0-Rewriting 1
open Rewriting-Powers 2
open Rewriting-Swap 2
open Rewriting-Swap0 2
open Symplectic-GroupLike
open Basis-Change _ (3 QRel,_===_) grouplike
open import N.EX-Rewriting p-2 p-prime
open Rewriting-EX 2
open Homo 2 renaming (lemma-f* to lemma-f*-EX)
open Commuting-Symplectic 1
open import Data.List
open import N.BR2.TwoQupit p-2 p-prime
open import N.Embeding-2n p-2 p-prime 1
open import N.EX-Rewriting p-2 p-prime

CX02 : ∀ {n} → Word (Gen (₃₊ n))
CX02 = H ^ 3 • CZ02 • H

lemma-CX↑-CZ^k' : 
  ∀ k -> CX ↑ • CZ^ k ≈ CZ^ k • CZ02^ (- k) • CX ↑
lemma-CX↑-CZ^k' k = begin
  CX ↑ • CZ^ k ≈⟨ lemma-CX↑-CZ^k (toℕ k) ⟩
  CZ^ k • (CZ02⁻ᵏ (toℕ (k))) • CX ↑ ≈⟨ cright cleft (cright cleft aux-CZ⁻¹↑^k-CZ↑^-k k) ⟩
  CZ^ k • (CZ02k (toℕ (- k))) • CX ↑ ≈⟨ cright cleft cright cleft refl' (lemma-^-↑ CZ (toℕ (- k))) ⟩
  CZ^ k • CZ02^ (- k) • CX ↑ ∎

lemma-CX02-CZ^k : 
  ∀ k -> CX02 • CZ^ k ≈ CZ^ k • CZ^ (- k) ↑ • CX02
lemma-CX02-CZ^k k = bbc Ex ε claim
  where
  claim : Ex • (CX02 • CZ^ k) • ε ≈ Ex • (CZ^ k • CZ^ (- k) ↑ • CX02) • ε
  claim = begin
    Ex • (CX02 • CZ^ k) • ε ≈⟨ cong refl right-unit ⟩
    Ex • (CX02 • CZ^ k) ≈⟨ sym assoc ⟩
    (Ex • CX02) • CZ^ k ≈⟨ cleft rewrite-swap 100 auto ⟩
    (CX ↑ • Ex) • CZ^ k ≈⟨ assoc ⟩
    CX ↑ • Ex • CZ^ k ≈⟨ cright word-comm 1 (toℕ k) (sym lemma-comm-Ex-CZ-n) ⟩
    CX ↑ • CZ^ k • Ex ≈⟨ sym assoc ⟩
    (CX ↑ • CZ^ k) • Ex ≈⟨ cleft lemma-CX↑-CZ^k' k ⟩
    (CZ^ k • CZ02^ (- k) • CX ↑) • Ex ≈⟨ sa (□ ^ 3 • □) (□ ^ 4) auto ⟩
    CZ^ k • CZ02^ (- k) • CX ↑ • Ex ≈⟨ cright cright sym (rewrite-swap 100 auto) ⟩
    CZ^ k • CZ02^ (- k) • Ex • CX02 ≈⟨ sa (□ • □ ^ 3 • □ ^ 2) (□ ^ 2 • □ • □ ^ 2 • □) auto ⟩
    (CZ^ k • Ex) • CZ^ (- k) ↑ • (Ex • Ex) • CX02 ≈⟨ cright cright cleft rewrite-swap 100 auto ⟩
    (CZ^ k • Ex) • CZ^ (- k) ↑ • ε • CX02 ≈⟨ cright cright left-unit ⟩
    (CZ^ k • Ex) • CZ^ (- k) ↑ • CX02 ≈⟨ cleft word-comm (toℕ k) 1 lemma-comm-Ex-CZ-n ⟩
    (Ex • CZ^ k) • CZ^ (- k) ↑ • CX02 ≈⟨ sa (□ ^ 2 • □ ^ 2) (□ ^ 4) auto ⟩
    Ex • (CZ^ k • CZ^ (- k) ↑ • CX02) ≈⟨ cright sym right-unit ⟩
    Ex • (CZ^ k • CZ^ (- k) ↑ • CX02) • ε ∎


lemma-CX02-CZ02^k : ∀ k -> CX02 • CZ02^ k ≈ S^ (- k + - k) ↑ ↑ • CZ02^ k • CX02
lemma-CX02-CZ02^k k = bbc (Ex ↑) ε claim
  where
  claim : Ex ↑ • (CX02 • CZ02^ k) • ε ≈ Ex ↑ • (S^ (- k + - k) ↑ ↑ • CZ02^ k • CX02) • ε
  claim = begin
    Ex ↑ • (CX02 • CZ02^ k) • ε ≈⟨ cong refl right-unit ⟩
    Ex ↑ • (CX02 • CZ02^ k) ≈⟨ sym assoc ⟩
    (Ex ↑ • CX02) • CZ02^ k ≈⟨ cleft rewrite-swap 100 auto ⟩
    (CX • Ex ↑) • CZ02^ k ≈⟨ cright aux-CZ02^-alt k ⟩
    (CX • Ex ↑) •  Ex ↑ • CZ^ k • Ex ↑ ≈⟨ sa (□ ^ 2 • □ ^ 3) (□ • □ ^ 2 • □ ^ 2) auto ⟩
    CX • (Ex ↑ • Ex ↑) • CZ^ k • Ex ↑ ≈⟨ cright cleft rewrite-swap 100 auto ⟩
    CX • ε • CZ^ k • Ex ↑ ≈⟨ cong refl left-unit ⟩
    CX • CZ^ k • Ex ↑ ≈⟨ sym assoc ⟩
    (CX • CZ^ k) • Ex ↑ ≈⟨ cleft lemma-semi-CXCZ^ k ⟩

    (S^ (- k + - k) ↑ • CZ^ k • CX) • Ex ↑ ≈⟨ trans assoc (cong refl assoc) ⟩
    S^ (- k + - k) ↑ • CZ^ k • CX • Ex ↑ ≈⟨ cright sym left-unit ⟩
    S^ (- k + - k) ↑ • ε • CZ^ k • CX • Ex ↑ ≈⟨ cright cong (rewrite-swap 100 auto) (cright rewrite-swap 100 auto) ⟩
    S^ (- k + - k) ↑ • (Ex ↑ • Ex ↑) • CZ^ k • Ex ↑ • CX02 ≈⟨ sa (□ • □ ^ 2 • □ ^ 3) (□ ^ 2 • □ ^ 3 • □) auto ⟩
    (S^ (- k + - k) ↑ • Ex ↑) • (Ex ↑ • CZ^ k • Ex ↑) • CX02 ≈⟨ cright cleft sym (aux-CZ02^-alt k) ⟩
    (S^ (- k + - k) ↑ • Ex ↑) • CZ02^ k • CX02 ≈⟨ cleft sym (lemma-cong↑ _ _ (lemma-Induction lemma-Ex-S↑ (toℕ (- k + - k)))) ⟩
    (Ex ↑ • (S ↑ ^ toℕ (- k + - k)) ↑) • CZ02^ k • CX02 ≈⟨ cleft cright lemma-cong↑ _ _ (B2.refl' (lemma-^-↑ S (toℕ (- k + - k)))) ⟩
    (Ex ↑ • (S^ (- k + - k)) ↑ ↑) • CZ02^ k • CX02 ≈⟨ sa (□ ^ 2 • □ ^ 2) (□ ^ 4) auto ⟩
    Ex ↑ • (S^ (- k + - k) ↑ ↑ • CZ02^ k • CX02) ≈⟨ sym (cong refl right-unit) ⟩
    Ex ↑ • (S^ (- k + - k) ↑ ↑ • CZ02^ k • CX02) • ε ∎


lemma-CX02-CZ02^k-alt : ∀ k -> CX02 • CZ02^ k ≈ S^ k • CX02 • S^ (- k) • S^ (- k) ↑ ↑ 
lemma-CX02-CZ02^k-alt k = bbc (Ex ↑) ε claim
  where
  claim : Ex ↑ • (CX02 • CZ02^ k) • ε ≈ Ex ↑ • (S^ k • CX02 • S^ (- k) • S^ (- k) ↑ ↑ ) • ε
  claim = begin
    Ex ↑ • (CX02 • CZ02^ k) • ε ≈⟨ cong refl right-unit ⟩
    Ex ↑ • (CX02 • CZ02^ k) ≈⟨ sym assoc ⟩
    (Ex ↑ • CX02) • CZ02^ k ≈⟨ cleft rewrite-swap 100 auto ⟩
    (CX • Ex ↑) • CZ02^ k ≈⟨ cright aux-CZ02^-alt k ⟩
    (CX • Ex ↑) •  Ex ↑ • CZ^ k • Ex ↑ ≈⟨ sa (□ ^ 2 • □ ^ 3) (□ • □ ^ 2 • □ ^ 2) auto ⟩
    CX • (Ex ↑ • Ex ↑) • CZ^ k • Ex ↑ ≈⟨ cright cleft rewrite-swap 100 auto ⟩
    CX • ε • CZ^ k • Ex ↑ ≈⟨ cong refl left-unit ⟩
    CX • CZ^ k • Ex ↑ ≈⟨ sym assoc ⟩
    (CX • CZ^ k) • Ex ↑ ≈⟨ cleft lemma-semi-CXCZ^-alt k ⟩

    (S^ k • CX • S^ (- k) • S^ (- k) ↑) • Ex ↑ ≈⟨ sa (□ ^ 4 • □) (□ ^ 5) auto ⟩
    S^ k • CX • S^ (- k) • S^ (- k) ↑ • Ex ↑ ≈⟨ cright cright cright sym (lemma-cong↑ _ _ (lemma-Ex-S^ᵏ↑ 0 (- k)) ) ⟩
    S^ k • CX • S^ (- k) • Ex ↑ • S^ (- k) ↑ ↑ ≈⟨ cright cright sym assoc ⟩
    S^ k • CX • (S^ (- k) • Ex ↑) • S^ (- k) ↑ ↑ ≈⟨ cright cright cleft lemma-comm-Sᵏ-w↑ (toℕ (- k)) Ex ⟩
    S^ k • CX • (Ex ↑ • S^ (- k)) • S^ (- k) ↑ ↑ ≈⟨ sym (cright sa (□ ^ 2 • □ ^ 2) (□ • □ ^ 2 • □) auto) ⟩
    S^ k • (CX • Ex ↑) • S^ (- k) • S^ (- k) ↑ ↑ ≈⟨ cright cleft rewrite-swap 100 auto ⟩
    S^ k • (Ex ↑ • CX02) • S^ (- k) • S^ (- k) ↑ ↑ ≈⟨ sa (□ • □ ^ 2 • □) (□ ^ 2 • □ ^ 2) auto ⟩
    (S^ k • Ex ↑) • CX02 • S^ (- k) • S^ (- k) ↑ ↑ ≈⟨ cleft lemma-comm-Sᵏ-w↑ (toℕ (k)) Ex ⟩
    (Ex ↑ • S^ k) • CX02 • S^ (- k) • S^ (- k) ↑ ↑ ≈⟨ sa (□ ^ 2 • □ ^ 3) (□ ^ 5) auto ⟩
    Ex ↑ • (S^ k • CX02 • S^ (- k) • S^ (- k) ↑ ↑ ) ≈⟨ sym (cong refl right-unit) ⟩
    Ex ↑ • (S^ k • CX02 • S^ (- k) • S^ (- k) ↑ ↑ ) • ε ∎


lemma-Ex-Ex↑-CZ^k : ∀ k -> (Ex • Ex ↑) • CZ^ k ≈ CZ^ k ↑ • Ex • Ex ↑
lemma-Ex-Ex↑-CZ^k k = begin
  (Ex • Ex ↑) • CZ^ k ≈⟨ lemma-Induction lemma-[Ex-Ex↑]-CZ (toℕ k) ⟩
  CZ ↑ ^ toℕ k • Ex • Ex ↑ ≈⟨ cleft refl' (lemma-^-↑ CZ (toℕ k)) ⟩
  CZ^ k ↑ • Ex • Ex ↑ ∎

lemma-comm-CZ02-H↑' : ∀ k -> CZ02^ k • H ↑ ≈ H ↑ • CZ02^ k
lemma-comm-CZ02-H↑' k = begin
  CZ02^ k • H ↑ ≈⟨ cleft (cright cleft sym (refl' (lemma-^-↑ CZ (toℕ k))))  ⟩
  CZ02k (toℕ k) • H ↑ ≈⟨ lemma-comm-CZ02-H↑ 0 (toℕ k) ⟩
  H ↑ • CZ02k (toℕ k) ≈⟨ cright (  cright cleft refl' (lemma-^-↑ CZ (toℕ k))) ⟩
  H ↑ • CZ02^ k ∎


lemma-comm-CX02-H↑' : ∀ k -> CX02^ k • H ↑ ≈ H ↑ • CX02^ k
lemma-comm-CX02-H↑' k = begin
  (H ^ 3 • CZ02^ k • H) • H ↑ ≈⟨ sa (□ ^ 3 • □) (□ ^ 2 • □ ^ 2) auto ⟩
  (H ^ 3 • CZ02^ k) • H • H ↑ ≈⟨ cright general-comm auto ⟩
  (H ^ 3 • CZ02^ k) • H ↑ • H ≈⟨ sa (□ ^ 2 • □ ^ 2) (□ • □ ^ 2 • □) auto ⟩
  H ^ 3 • (CZ02^ k • H ↑) • H ≈⟨ cright cleft lemma-comm-CZ02-H↑' k ⟩
  H ^ 3 • (H ↑ • CZ02^ k) • H ≈⟨ sym (sa (□ ^ 2 • □ ^ 2) (□ • □ ^ 2 • □) auto) ⟩
  (H ^ 3 • H ↑) • CZ02^ k • H ≈⟨ cleft general-comm auto ⟩
  (H ↑ • H ^ 3) • CZ02^ k • H ≈⟨ assoc ⟩
  H ↑ • CX02^ k ∎


lemma-CX02-CX↑-CZ^k : ∀ k -> CX02 • CX ↑ • CZ^ k ≈ (CZ^ k • CZ^ (- k) ↑ • S^ (k + k) ↑ ↑ • CZ02^ (- k)) • CX02 • CX ↑
lemma-CX02-CX↑-CZ^k k = begin
  CX02 • CX ↑ • CZ^ k ≈⟨  cright lemma-CX↑-CZ^k' k ⟩
  CX02 • CZ^ k • CZ02^ (- k) • CX ↑ ≈⟨  sym assoc ⟩
  (CX02 • CZ^ k) • CZ02^ (- k) • CX ↑ ≈⟨  cleft lemma-CX02-CZ^k k ⟩
  (CZ^ k • CZ^ (- k) ↑ • CX02) • CZ02^ (- k) • CX ↑ ≈⟨  sa (□ ^ 3 • □ ^ 2) (□ ^ 2 • □ ^ 2 • □) auto ⟩
  (CZ^ k • CZ^ (- k) ↑) • (CX02 • CZ02^ (- k)) • CX ↑ ≈⟨  cong (cright refl) (cleft lemma-CX02-CZ02^k (- k)) ⟩
  (CZ^ k • CZ^ (- k) ↑) • (S^ (- - k + - - k) ↑ ↑ • CZ02^ (- k) • CX02) • CX ↑ ≈⟨ cright cleft cleft refl' (Eq.cong (\ xx -> S^ xx ↑ ↑) (Eq.cong (\ xx -> xx + xx) (-‿involutive k))) ⟩
  (CZ^ k • CZ^ (- k) ↑) • (S^ (k + k) ↑ ↑ • CZ02^ (- k) • CX02) • CX ↑ ≈⟨ sa (□ ^ 2 • □ ^ 3 • □) (□ ^ 4 • □ ^ 2) auto ⟩
  (CZ^ k • CZ^ (- k) ↑ • S^ (k + k) ↑ ↑ • CZ02^ (- k)) • CX02 • CX ↑ ∎

aux-comm-CX02-CZ↑ : CX02 • CZ ↑ ≈ CZ ↑ • CX02
aux-comm-CX02-CZ↑ = begin
  CX02 • CZ ↑ ≈⟨ general-comm auto ⟩
  H ^ 3 • (CZ02 • CZ ↑) • H ≈⟨ cright cleft sym lemma-comm-CZ↑-CZ02 ⟩
  H ^ 3 • (CZ ↑ • CZ02) • H ≈⟨ general-comm auto ⟩
  CZ ↑ • CX02 ∎

lemma-CX02-CX↑-CZ^k-alt : ∀ k -> CX02 • CX ↑ • CZ^ k ≈ (CZ^ k) • (S^ (- k) • CX02 • S^ k) • (S^ (- k) • CX • S^ k) ↑
lemma-CX02-CX↑-CZ^k-alt k = begin
  CX02 • CX ↑ • CZ^ k ≈⟨  cright lemma-CX↑-CZ^k' k ⟩
  CX02 • CZ^ k • CZ02^ (- k) • CX ↑ ≈⟨  sym assoc ⟩
  (CX02 • CZ^ k) • CZ02^ (- k) • CX ↑ ≈⟨  cleft lemma-CX02-CZ^k k ⟩
  (CZ^ k • CZ^ (- k) ↑ • CX02) • CZ02^ (- k) • CX ↑ ≈⟨  sa (□ ^ 3 • □ ^ 2) (□ ^ 2 • □ ^ 2 • □) auto ⟩
  (CZ^ k • CZ^ (- k) ↑) • (CX02 • CZ02^ (- k)) • CX ↑ ≈⟨  cong (cright refl) (cleft lemma-CX02-CZ02^k-alt (- k)) ⟩
  (CZ^ k • CZ^ (- k) ↑) • (S^ (- k) • CX02 • S^ (- - k) • S^ (- - k) ↑ ↑ ) • CX ↑ ≈⟨ cright cleft cright cright refl' (Eq.cong (\ xx -> S^ (xx) • S^ (xx) ↑ ↑ ) (-‿involutive k)) ⟩
  (CZ^ k • CZ^ (- k) ↑) • (S^ (- k) • CX02 • S^ k • S^ k ↑ ↑ ) • CX ↑ ≈⟨ sa (□ ^ 2 • □ ^ 4 • □) (□ • □ ^ 2 • □ ^ 4) auto ⟩
  CZ^ k • (CZ^ (- k) ↑ • S^ (- k)) • CX02 • S^ k • S^ k ↑ ↑ • CX ↑ ≈⟨ cright cleft sym (lemma-comm-Sᵏ-w↑ (toℕ (- k)) (CZ^ (- k))) ⟩
  CZ^ k • (S^ (- k) • CZ^ (- k) ↑) • CX02 • S^ k • S^ k ↑ ↑ • CX ↑ ≈⟨ cright sa (□ ^ 2 • □ ^ 2) (□ • □ ^ 2 • □ ) auto ⟩
  CZ^ k • S^ (- k) • (CZ^ (- k) ↑ • CX02) • S^ k • S^ k ↑ ↑ • CX ↑ ≈⟨ sym (cright cright cleft cleft refl' (lemma-^-↑ CZ (toℕ (- k))) )⟩
  CZ^ k • S^ (- k) • (CZ ↑ ^ toℕ (- k) • CX02) • S^ k • S^ k ↑ ↑ • CX ↑ ≈⟨ cright cright cleft word-comm (toℕ (- k)) 1 (sym aux-comm-CX02-CZ↑) ⟩
  CZ^ k • S^ (- k) • (CX02 • CZ ↑ ^ toℕ (- k)) • S^ k • S^ k ↑ ↑ • CX ↑ ≈⟨ cright cright sa (□ ^ 2 • □ ^ 2) (□ • □ ^ 2 • □ ) auto ⟩
  CZ^ k • S^ (- k) • CX02 • (CZ ↑ ^ toℕ (- k) • S^ k) • S^ k ↑ ↑ • CX ↑ ≈⟨ cright cright cright cleft word-comm (toℕ (- k)) 1 (sym (lemma-comm-Sᵏ-w↑ (toℕ k) CZ)) ⟩
  CZ^ k • S^ (- k) • CX02 • (S^ k • CZ ↑ ^ toℕ (- k)) • S^ k ↑ ↑ • CX ↑ ≈⟨ cright cright cright sa (□ ^ 2 • □ ^ 2) (□ • □ ^ 2 • □ ) auto ⟩
  CZ^ k • S^ (- k) • CX02 • S^ k • (CZ ↑ ^ toℕ (- k) • S^ k ↑ ↑) • CX ↑ ≈⟨ cright cright cright cright cleft word-comm (toℕ (- k)) 1 (lemma-cong↑  _ _ (aux-comm-CZ-S^k↑ k)) ⟩
  CZ^ k • S^ (- k) • CX02 • S^ k • (S^ k ↑ ↑ • CZ ↑ ^ toℕ (- k)) • CX ↑ ≈⟨ cright sa (□ • □ • □ • □ ^ 2 • □) (□ ^ 4 • □ ^ 2) auto ⟩
  CZ^ k • (S^ (- k) • CX02 • S^ k • S^ k ↑ ↑) • CZ ↑ ^ toℕ (- k) • CX ↑ ≈⟨ cright cright cleft refl' (lemma-^-↑ CZ (toℕ (- k))) ⟩
  (CZ^ k) • (S^ (- k) • CX02 • S^ k • S^ k ↑ ↑ ) • CZ^ (- k) ↑ • CX ↑ ≈⟨ cright (cright lemma-cong↑ _ _ (lemma-CZ^k-CX-alt (- k) )) ⟩
  (CZ^ k) • (S^ (- k) • CX02 • S^ k • S^ k ↑ ↑ ) • (S^ (- k) ↑ • S^ (- k) • CX • S^ (- - k)) ↑ ≈⟨ cright cright cright cright cright refl' (Eq.cong (\ xx -> S^ xx ↑) (-‿involutive k)) ⟩
  (CZ^ k) • (S^ (- k) • CX02 • S^ k • S^ k ↑ ↑ ) • (S^ (- k) ↑ • S^ (- k) • CX • S^ k) ↑ ≈⟨ cright sa (□ ^ 4 • □ ^ 4) (□ ^ 3 • □ ^ 2 • □ ^ 3) auto ⟩
  (CZ^ k) • (S^ (- k) • CX02 • S^ k) • (S^ k ↑ ↑ • S^ (- k) ↑ ↑) • (S^ (- k) • CX • S^ k) ↑ ≈⟨ cright cright  (cleft lemma-cong↑  _ _ (lemma-cong↑ _ _ (L00.lemma-S^k+l k (- k)))) ⟩
  (CZ^ k) • (S^ (- k) • CX02 • S^ k) • S^ (k + - k) ↑ ↑ • (S^ (- k) • CX • S^ k) ↑ ≈⟨ cright cright cleft refl' (Eq.cong (\ xx -> S^ xx ↑ ↑) (+-inverseʳ k)) ⟩
  (CZ^ k) • (S^ (- k) • CX02 • S^ k) • S^ ₀ ↑ ↑ • (S^ (- k) • CX • S^ k) ↑ ≈⟨ cright cright left-unit ⟩
  (CZ^ k) • (S^ (- k) • CX02 • S^ k) • (S^ (- k) • CX • S^ k) ↑ ∎




aux-HH↓-CZ02 : ∀ k -> H ^ 2 • CZ02^ k ≈ CZ02^ (- k) • H ^ 2
aux-HH↓-CZ02 k = begin
  H ^ 2 • Ex • CZ^ k ↑ • Ex ≈⟨ sym assoc ⟩
  (H ^ 2 • Ex) • CZ^ k ↑ • Ex ≈⟨ cleft rewrite-swap 100 auto ⟩
  (Ex • H ↑ ^ 2) • CZ^ k ↑ • Ex ≈⟨ sa (□ ^ 2 • □ ^ 2) (□ • □ ^ 2 • □ ) auto ⟩
  Ex • (H ↑ ^ 2 • CZ^ k ↑) • Ex ≈⟨ cright cleft lemma-cong↑ _ _ (L2Q0.lemma-semi-HH↓-CZ^k' k) ⟩
  Ex • (CZ^ (- k) ↑ • H ↑ ^ 2) • Ex ≈⟨ sa (□ • □ ^ 2 • □ ) (□ ^ 4) auto ⟩
  Ex • CZ^ (- k) ↑ • H ↑ ^ 2 • Ex ≈⟨ cright cright rewrite-swap 100 auto ⟩
  Ex • CZ^ (- k) ↑ • Ex • H ^ 2 ≈⟨ sa (□ ^ 4) (□ ^ 3 • □) auto ⟩
  CZ02^ (- k) • H ^ 2 ∎

aux-HH↓-CX02 : ∀ k -> H ^ 2 • CX02^ k ≈ CX02^ (- k) • H ^ 2
aux-HH↓-CX02 k = begin
  H ^ 2 • CX02^ k ≈⟨ rewrite-sym0 100 auto ⟩
  H ^ 3 • (H ^ 2 • CZ02^ k) • H ≈⟨ cright cleft aux-HH↓-CZ02 k ⟩
  H ^ 3 • (CZ02^ (- k) • H ^ 2) • H ≈⟨ cong refl assoc ⟩
  H ^ 3 • CZ02^ (- k) • H ^ 2 • H ≈⟨ rewrite-sym0 100 auto ⟩
  H ^ 3 • CZ02^ (- k) • H • H ^ 2 ≈⟨ sa (□ ^ 4) (□ ^ 3 • □) auto ⟩
  CX02^ (- k) • H ^ 2 ∎

aux-HH↓-CX02⁻ : ∀ k -> CX02^ k • H ^ 2 ≈ H ^ 2 • CX02^ (- k)
aux-HH↓-CX02⁻ k = bbc (H ^ 2) (H ^ 2) claim
  where
  claim : H ^ 2 • (CX02^ k • H ^ 2) • H ^ 2 ≈ H ^ 2 • (H ^ 2 • CX02^ (- k)) • H ^ 2
  claim = begin
    H ^ 2 • (CX02^ k • H ^ 2) • H ^ 2 ≈⟨ sa (□ ^ 2 • (□ • □ ^ 2) • □ ^ 2) (□ ^ 2 • □ • □ ^ 4) auto ⟩
    H ^ 2 • CX02^ k • H ^ 4 ≈⟨ cright trans (cright axiom order-H) right-unit ⟩
    H ^ 2 • CX02^ k  ≈⟨ aux-HH↓-CX02 k ⟩
    CX02^ (- k) • H ^ 2 ≈⟨ sym (trans (cleft axiom order-H) left-unit) ⟩
    H ^ 4 • CX02^ (- k) • H ^ 2 ≈⟨ sa (□ ^ 4 • □ • □ ^ 2 ) (□ ^ 2 • (□ ^ 2 • □) • □ ^ 2) auto ⟩
    H ^ 2 • (H ^ 2 • CX02^ (- k)) • H ^ 2 ∎



lemma-CZ02⁻¹-CZ⁻¹↑-CZ^k : ∀ k -> CZ02^ (- ₁) • H • CZ^ (- ₁) ↑ • H ↑ • CZ^ k ≈ H • H ↑ • CZ^ k • S^ (- k) • CX02^ (- ₁) • S^ k • (S^ (- k) ↑ • CX^ (- ₁) ↑ • S^ k ↑)
lemma-CZ02⁻¹-CZ⁻¹↑-CZ^k k = bbc (H • H ↑) ε claim
  where
  claim : (H • H ↑) • (CZ02^ (- ₁) • H • CZ^ (- ₁) ↑ • H ↑ • CZ^ k) • ε ≈ (H • H ↑) • (H • H ↑ • CZ^ k • S^ (- k) • CX02^ (- ₁) • S^ k • (S^ (- k) ↑ • CX^ (- ₁) ↑ • S^ k ↑)) • ε
  claim = begin
    (H • H ↑) • (CZ02^ (- ₁) • H • CZ^ (- ₁) ↑ • H ↑ • CZ^ k) • ε ≈⟨ cright right-unit ⟩
    (H • H ↑) • (CZ02^ (- ₁) • H • CZ^ (- ₁) ↑ • H ↑ • CZ^ k) ≈⟨ cleft rewrite-sym0 100 auto ⟩
    (H ^ 3 • H ↑ ^ 3 • H ↑ ^ 2 • H ^ 2) • (CZ02^ (- ₁) • H • CZ^ (- ₁) ↑ • H ↑ • CZ^ k) ≈⟨ sa (□ ^ 4 • □ ^ 3) (□ ^ 3 • □ ^ 2 • □ ^ 2) auto ⟩
    (H ^ 3 • H ↑ ^ 3 • H ↑ ^ 2) • (H ^ 2 • CZ02^ (- ₁)) • H • CZ^ (- ₁) ↑ • H ↑ • CZ^ k ≈⟨ cright cleft aux-HH↓-CZ02 (- ₁) ⟩
    (H ^ 3 • H ↑ ^ 3 • H ↑ ^ 2) • (CZ02^ (- - ₁) • H ^ 2) • H • CZ^ (- ₁) ↑ • H ↑ • CZ^ k ≈⟨ cright cleft cleft refl' (Eq.cong CZ02^ (-‿involutive ₁)) ⟩
    (H ^ 3 • H ↑ ^ 3 • H ↑ ^ 2) • (CZ02 • H ^ 2) • H • CZ^ (- ₁) ↑ • H ↑ • CZ^ k ≈⟨ cright sa (□ ^ 2 • □ ^ 4) (□ • □ ^ 4 • □) auto ⟩
    (H ^ 3 • H ↑ ^ 3 • H ↑ ^ 2) • CZ02 • (H ^ 2 • H • CZ^ (- ₁) ↑ • H ↑) • CZ^ k ≈⟨ cright cright  by-assoc auto ⟩
    (H ^ 3 • H ↑ ^ 3 • H ↑ ^ 2) • CZ02 • (H • H ^ 2 • CZ^ (- ₁) ↑ • H ↑) • CZ^ k ≈⟨ cright cright cleft cright lemma-comm-Hᵏ-w↑ 2 (CZ^ (- ₁) • H) ⟩
    (H ^ 3 • H ↑ ^ 3 • H ↑ ^ 2) • CZ02 • (H • (CZ^ (- ₁) ↑ • H ↑) • H ^ 2) • CZ^ k ≈⟨ cright cright  sa ((□ • □ ^ 2 • □) • □) (□ ^ 5) auto ⟩
    (H ^ 3 • H ↑ ^ 3 • H ↑ ^ 2) • CZ02 • H • CZ^ (- ₁) ↑ • H ↑ • H ^ 2 • CZ^ k ≈⟨ cright cright cright cright  (cright lemma-semi-HH↓-CZ^k' k) ⟩
    (H ^ 3 • H ↑ ^ 3 • H ↑ ^ 2) • CZ02 • H • CZ^ (- ₁) ↑ • H ↑ • CZ^ (- k) • H ^ 2 ≈⟨ sa (□ ^ 3 • □ ^ 2) (□ ^ 2 • □ ^ 2 • □) auto ⟩
    (H ^ 3 • H ↑ ^ 3) • (H ↑ ^ 2 • CZ02) • H • CZ^ (- ₁) ↑ • H ↑ • CZ^ (- k) • H ^ 2 ≈⟨ cright cleft word-comm 2 1 (sym (lemma-comm-CZ02-H↑ 0 ₁)) ⟩
    (H ^ 3 • H ↑ ^ 3) • (CZ02 • H ↑ ^ 2) • H • CZ^ (- ₁) ↑ • H ↑ • CZ^ (- k) • H ^ 2 ≈⟨ cright sa (□ ^ 2 • □ ^ 5) (□ • (□ ^ 2 • □) • □ ^ 3) auto ⟩
    (H ^ 3 • H ↑ ^ 3) • CZ02 • ((H ↑ ^ 2 • H) • CZ^ (- ₁) ↑) • H ↑ • CZ^ (- k) • H ^ 2 ≈⟨ cright cright cleft (cleft general-comm auto) ⟩ 
    (H ^ 3 • H ↑ ^ 3) • CZ02 • ((H • H ↑ ^ 2) • CZ^ (- ₁) ↑) • H ↑ • CZ^ (- k) • H ^ 2 ≈⟨ cright cright cleft assoc ⟩
    (H ^ 3 • H ↑ ^ 3) • CZ02 • (H • H ↑ ^ 2 • CZ^ (- ₁) ↑) • H ↑ • CZ^ (- k) • H ^ 2 ≈⟨ cright cright cleft cright  lemma-cong↑ _ _ (L2Q0.lemma-semi-CZ-HH↓') ⟩
    (H ^ 3 • H ↑ ^ 3) • CZ02 • (H • CZ ↑ • H ↑ ^ 2) • H ↑ • CZ^ (- k) • H ^ 2 ≈⟨ cright cright sa (□ ^ 3 • □ ^ 3) (□ • □ ^ 2 • □ ^ 3) auto ⟩
    (H ^ 3 • H ↑ ^ 3) • CZ02 • H • (CZ ↑ • H ↑ ^ 2) • H ↑ • CZ^ (- k) • H ^ 2 ≈⟨ cright cright  cright sa (□ ^ 2 • □ ^ 3) (□ • □ ^ 3 • □) auto ⟩
    (H ^ 3 • H ↑ ^ 3) • CZ02 • H • CZ ↑ • (H ↑ ^ 2 • H ↑ ^ 1 • CZ^ (- k)) • H ^ 2 ≈⟨ cright cright cright cright (cleft rewrite-sym0 100 auto) ⟩
    (H ^ 3 • H ↑ ^ 3) • CZ02 • H • CZ ↑ • (H ↑ • H ↑ ^ 2 • CZ^ (- k)) • H ^ 2 ≈⟨ cright cright cright cright cleft cright lemma-semi-HH↑-CZ^k'' k ⟩

    (H ^ 3 • H ↑ ^ 3) • CZ02 • H • CZ ↑ • (H ↑ • CZ^ k • H ↑ ^ 2 ) • H ^ 2 ≈⟨ cong (rewrite-sym0 100 auto) (cright cright cright sa (□ ^ 3 • □) (□ • □ ^ 2 • □) auto) ⟩
    (H ^ 3 • H ↑ ^ 3) • CZ02 • H • CZ ↑ • H ↑ • (CZ^ k • H ↑ ^ 2 ) • H ^ 2 ≈⟨ sa (□ ^ 2 • □ ^ 2) (□ • □ ^ 2 • □) auto ⟩
    H ^ 3 • (H ↑ ^ 3 • CZ02) • H • CZ ↑ • H ↑ • (CZ^ k • H ↑ ^ 2 ) • H ^ 2 ≈⟨ cright cleft word-comm 3 1 (sym (lemma-comm-CZ02-H↑' ₁)) ⟩
    H ^ 3 • (CZ02 • H ↑ ^ 3) • H • CZ ↑ • H ↑ • (CZ^ k • H ↑ ^ 2 ) • H ^ 2 ≈⟨ sa (□ • □ ^ 2 • □ ^ 2) (□ ^ 2 • □ ^ 2 • □) auto ⟩
    (H ^ 3 • CZ02) • (H ↑ ^ 3 • H) • CZ ↑ • H ↑ • (CZ^ k • H ↑ ^ 2 ) • H ^ 2 ≈⟨ cright cleft general-comm auto ⟩
    (H ^ 3 • CZ02) • (H • H ↑ ^ 3) • CZ ↑ • H ↑ • (CZ^ k • H ↑ ^ 2 ) • H ^ 2 ≈⟨ sa (□ ^ 2 • □ ^ 2 • □ ^ 3) (□ ^ 3 • □ ^ 3 • □) auto ⟩
    (H ^ 3 • CZ02 • H) • (H ↑ ^ 3 • CZ ↑ • H ↑) • (CZ^ k • H ↑ ^ 2 ) • H ^ 2 ≈⟨ sa (□ • □ • □ ^ 2 • □) (□ ^ 3 • □ ^ 2) auto ⟩
    (CX02 • CX ↑ • CZ^ k) • H ↑ ^ 2 • H ^ 2 ≈⟨ cleft lemma-CX02-CX↑-CZ^k-alt k ⟩
    (CZ^ k • (S^ (- k) • CX02 • S^ k) • (S^ (- k) • CX • S^ k) ↑) • H ↑ ^ 2 • H ^ 2 ≈⟨ sa (□ ^ 5 • □ ^ 2) (□ ^ 4 • □ ^ 2 • □) auto ⟩
    (CZ^ k • (S^ (- k) • CX02 • S^ k) • (S^ (- k) • CX) ↑) • (S^ k ↑ • H ↑ ^ 2) • H ^ 2 ≈⟨ cright cleft lemma-cong↑ _ _ (P2.word-comm (toℕ k) 1 ( Sym01.rewrite-sym0 100 auto)) ⟩
    (CZ^ k • (S^ (- k) • CX02 • S^ k) • (S^ (- k) • CX) ↑) • (H ↑ ^ 2 • S^ k ↑) • H ^ 2 ≈⟨ sa (□ ^ 4 • □ ^ 2 • □) (□ ^ 3 • □ ^ 2 • □ ^ 2) auto ⟩
    (CZ^ k • (S^ (- k) • CX02 • S^ k) • S^ (- k) ↑) • (CX ↑ • H ↑ ^ 2) • S^ k ↑ • H ^ 2 ≈⟨ cright cleft lemma-cong↑ _ _ (B2.sym lemma-semi-HH↓-CX⁻¹)  ⟩
    (CZ^ k • (S^ (- k) • CX02 • S^ k) • S^ (- k) ↑) • (H ↑ ^ 2 • CX^ (- ₁) ↑) • S^ k ↑ • H ^ 2 ≈⟨ sa (□ ^ 3 • □ ^ 2 • □) (□ ^ 2 • □ ^ 2 • □ ^ 2) auto ⟩
    (CZ^ k • (S^ (- k) • CX02 • S^ k)) • (S^ (- k) ↑ • H ↑ ^ 2) • CX^ (- ₁) ↑ • S^ k ↑ • H ^ 2 ≈⟨ cright cong (lemma-cong↑ _ _ (P2.word-comm (toℕ (- k)) 1 ( Sym01.rewrite-sym0 100 auto))) refl ⟩
    (CZ^ k • (S^ (- k) • CX02 • S^ k)) • (H ↑ ^ 2 • S^ (- k) ↑) • CX^ (- ₁) ↑ • S^ k ↑ • H ^ 2 ≈⟨ sa (□ ^ 4 • □ ^ 2 • □ ^ 3) (□ ^ 3 • □ ^ 2 • □ ^ 3 • □) auto ⟩
    (CZ^ k • S^ (- k) • CX02) • (S^ k • H ↑ ^ 2) • (S^ (- k) ↑ • CX^ (- ₁) ↑ • S^ k ↑) • H ^ 2 ≈⟨ cright cong (lemma-comm-Sᵏ-w↑ (toℕ k) (H ^ 2)) (sym (lemma-comm-Hᵏ-w↑ 2 (S^ (- k) • CX^ (- ₁) • S^ k))) ⟩
    (CZ^ k • S^ (- k) • CX02) • (H ↑ ^ 2 • S^ k) • H ^ 2 • (S^ (- k) ↑ • CX^ (- ₁) ↑ • S^ k ↑) ≈⟨ sa (□ ^ 3 • □ ^ 2 • □ ^ 2) (□ ^ 2 • □ ^ 2 • □ ^ 2 • □) auto ⟩
    (CZ^ k • S^ (- k)) • (CX02 • H ↑ ^ 2) • (S^ k • H ^ 2) • (S^ (- k) ↑ • CX^ (- ₁) ↑ • S^ k ↑) ≈⟨ cright cong (word-comm 1 2 (lemma-comm-CX02-H↑' ₁)) (cleft word-comm (toℕ (k)) 1 ( rewrite-sym0 100 auto)) ⟩
    (CZ^ k • S^ (- k)) • (H ↑ ^ 2 • CX02) • (H ^ 2 • S^ k) • (S^ (- k) ↑ • CX^ (- ₁) ↑ • S^ k ↑) ≈⟨ sa (□ ^ 2 • □ ^ 2 • □ ^ 2 • □) (□ • □ ^ 2 • □ ^ 2 • □ ^ 2) auto ⟩
    CZ^ k • (S^ (- k) • H ↑ ^ 2) • (CX02 • H ^ 2) • S^ k • (S^ (- k) ↑ • CX^ (- ₁) ↑ • S^ k ↑) ≈⟨ cright cong (lemma-comm-Sᵏ-w↑ (toℕ (- k)) (H ^ 2)) (cleft aux-HH↓-CX02⁻ ₁) ⟩
    CZ^ k • (H ↑ ^ 2 • S^ (- k)) • (H ^ 2 • CX02^ (- ₁)) • S^ k • (S^ (- k) ↑ • CX^ (- ₁) ↑ • S^ k ↑) ≈⟨ sa (□ • □ ^ 2 • □ ^ 2 • □) (□ ^ 2 • □ ^ 2 • □ ^ 2) auto ⟩
    (CZ^ k • H ↑ ^ 2) • (S^ (- k) • H ^ 2) • CX02^ (- ₁) • S^ k • (S^ (- k) ↑ • CX^ (- ₁) ↑ • S^ k ↑) ≈⟨ cong (sym (lemma-semi-HH↑-CZ^k'' k)) (cleft word-comm (toℕ (- k)) 1 ( rewrite-sym0 100 auto)) ⟩
    (H ↑ ^ 2 • CZ^ (- k)) • (H ^ 2 • S^ (- k)) • CX02^ (- ₁) • S^ k • (S^ (- k) ↑ • CX^ (- ₁) ↑ • S^ k ↑) ≈⟨ sa (□ ^ 2 • □ ^ 2 • □) (□ • □ ^ 2 • □ ^ 2) auto ⟩
    H ↑ ^ 2 • (CZ^ (- k) • H ^ 2) • S^ (- k) • CX02^ (- ₁) • S^ k • (S^ (- k) ↑ • CX^ (- ₁) ↑ • S^ k ↑) ≈⟨ cright (cleft sym (lemma-semi-HH↓-CZ^k' k)) ⟩
    H ↑ ^ 2 • (H ^ 2 • CZ^ k) • S^ (- k) • CX02^ (- ₁) • S^ k • (S^ (- k) ↑ • CX^ (- ₁) ↑ • S^ k ↑) ≈⟨ sa (□ • □ ^ 2 • □) (□ ^ 2 • □ ^ 2) auto ⟩
    (H ↑ ^ 2 • H ^ 2) • CZ^ k • S^ (- k) • CX02^ (- ₁) • S^ k • (S^ (- k) ↑ • CX^ (- ₁) ↑ • S^ k ↑) ≈⟨ cleft general-comm auto ⟩
    (H • H ↑ • H • H ↑) • CZ^ k • S^ (- k) • CX02^ (- ₁) • S^ k • (S^ (- k) ↑ • CX^ (- ₁) ↑ • S^ k ↑) ≈⟨ sa (□ ^ 4 • □) (□ ^ 2 • □ ^ 3) auto ⟩
    (H • H ↑) • (H • H ↑ • CZ^ k • S^ (- k) • CX02^ (- ₁) • S^ k • (S^ (- k) ↑ • CX^ (- ₁) ↑ • S^ k ↑)) ≈⟨ cright sym right-unit ⟩

    (H • H ↑) • (H • H ↑ • CZ^ k • S^ (- k) • CX02^ (- ₁) • S^ k • (S^ (- k) ↑ • CX^ (- ₁) ↑ • S^ k ↑)) • ε ∎



aux-MHS↑-CZ : ∀ m k l -> ⟦ m ⁻¹ , HS^ k ⟧ₘ₊ ↑ • CZ^ l ≈ H ↑ • CZ^ (l * m .proj₁) • ZM m ↑ • S^ k ↑
aux-MHS↑-CZ m k l = begin
  ⟦ m ⁻¹ , HS^ k ⟧ₘ₊ ↑ • CZ^ l ≈⟨ sa (□ ^ 3 • □) (□ ^ 2 • □ ^ 2) auto ⟩
  (⟦ m ⁻¹ ⟧ₘ ↑ • H ↑) • S^ k ↑ • CZ^ l ≈⟨ cong (sym (lemma-cong↑ _ _ (semi-HM m))) (sym (word-comm (toℕ l) 1 (aux-comm-CZ-S^k↑ k))) ⟩
  (H ↑ • ⟦ m ⟧ₘ ↑) • CZ^ l • S^ k ↑ ≈⟨ sa (□ ^ 2 • □ ^ 2) (□ • □ ^ 2 • □) auto ⟩
  H ↑ • (⟦ m ⟧ₘ ↑ • CZ^ l) • S^ k ↑ ≈⟨ cright cleft (lemma-M↑CZ^k (m .proj₁) l (m .proj₂)) ⟩
  H ↑ • (CZ^ (l * m .proj₁) • ⟦ m ⟧ₘ ↑) • S^ k ↑ ≈⟨ sa (□ • □ ^ 2 • □) (□ ^ 4) auto ⟩
  H ↑ • CZ^ (l * m .proj₁) • ZM m ↑ • S^ k ↑ ∎


aux-MHS↓-CZ : ∀ m k l -> ⟦ m ⁻¹ , HS^ k ⟧ₘ₊ ↓ • CZ^ l ≈ H ↓ • CZ^ (l * m .proj₁) • ZM m ↓ • S^ k ↓
aux-MHS↓-CZ m k l = begin
  ⟦ m ⁻¹ , HS^ k ⟧ₘ₊ ↓ • CZ^ l ≈⟨ sa (□ ^ 3 • □) (□ ^ 2 • □ ^ 2) auto ⟩
  (⟦ m ⁻¹ ⟧ₘ ↓ • H ↓) • S^ k ↓ • CZ^ l ≈⟨ cong (sym ((L02.semi-HM m))) (sym (word-comm (toℕ l) 1 (word-comm 1 (toℕ k) (axiom comm-CZ-S↓)))) ⟩
  (H ↓ • ⟦ m ⟧ₘ ↓) • CZ^ l • S^ k ↓ ≈⟨ sa (□ ^ 2 • □ ^ 2) (□ • □ ^ 2 • □) auto ⟩
  H ↓ • (⟦ m ⟧ₘ ↓ • CZ^ l) • S^ k ↓ ≈⟨ cright cleft (lemma-M↓CZ^k (m .proj₁) l (m .proj₂)) ⟩
  H ↓ • (CZ^ (l * m .proj₁) • ⟦ m ⟧ₘ ↓) • S^ k ↓ ≈⟨ sa (□ • □ ^ 2 • □) (□ ^ 4) auto ⟩
  H ↓ • CZ^ (l * m .proj₁) • ZM m ↓ • S^ k ↓ ∎

