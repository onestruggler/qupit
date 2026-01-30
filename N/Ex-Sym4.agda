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



module N.Ex-Sym4 (p-2 : ℕ) (p-prime : Prime (2+ p-2)) where

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

private
  n : ℕ
  n = 0

open import Zp.ModularArithmetic
open PrimeModulus p-2 p-prime
open import N.Symplectic p-2 p-prime
open import N.Lemmas-2Qupit-Sym p-2 p-prime
open import N.NF2-Sym p-2 p-prime
open import N.Cosets p-2 p-prime

open Lemmas-2Q 0
open Symplectic
open import N.NF1-Sym p-2 p-prime
open import N.Ex-Sym p-2 p-prime
open import N.Ex-Sym1 p-2 p-prime
open import N.Ex-Sym2 p-2 p-prime
open import N.Ex-Sym3 p-2 p-prime
open import N.Ex-Sym3n p-2 p-prime
open import N.Ex-Sym4n p-2 p-prime as Sym4n
open import N.Ex-Sym2n p-2 p-prime as Sym2n hiding (lemma-XCS^k')

open import N.Ex-Rewriting p-2 p-prime
open Rewriting-Ex n

open import N.Lemma-Comm p-2 p-prime 0
open import N.Lemma-Postfix p-2 p-prime
open import N.Duality p-2 p-prime hiding (module L0)
open Lemmas0a
open Lemmas0a1
open Lemmas0b
open Lemmas0c

open LM2
open import N.Completeness1-Sym p-2 p-prime renaming (module Completeness to CP1) using ()


open Symplectic
open Lemmas-Sym
open Symplectic-GroupLike

open import Data.Nat.DivMod
open import Data.Fin.Properties
open Duality


lemma-Ex-S^ᵏ : ∀ k → let open PB ((₂₊ n) QRel,_===_) in 

  Ex • S^ k ≈ S^ k ↑ • Ex

lemma-Ex-S^ᵏ k = begin
  Ex • S^ k ≈⟨ lemma-Ex-Sᵏ (toℕ k) ⟩
  S ↑ ^ toℕ k • Ex ≈⟨ (cleft refl' (aux-↑ S (toℕ k))) ⟩
  S^ k ↑ • Ex ∎
  where
  open PB ((₂₊ n) QRel,_===_)
  open PP ((₂₊ n) QRel,_===_)
  open SR word-setoid




open import Algebra.Properties.Ring (+-*-ring p-2)
open PB ((₂₊ n) QRel,_===_)
open PP ((₂₊ n) QRel,_===_)
open SR word-setoid
open Pattern-Assoc
open Lemmas0 (₁₊ n)
open Commuting-Symplectic n
open Sym0-Rewriting (₁₊ n)
open Basis-Change _ ((₂₊ n) QRel,_===_) grouplike
import N.Duality p-2 p-prime as ND

lemma-Ex-M : ∀ m -> Ex • M m ≈ M m ↑ • Ex
lemma-Ex-M m@x' = begin
  Ex • M m ≈⟨ refl ⟩
  Ex • S^ x • H • S^ x⁻¹ • H • S^ x • H ≈⟨ sym assoc ⟩
  (Ex • S^ x) • H • S^ x⁻¹ • H • S^ x • H ≈⟨ cleft lemma-Ex-S^ᵏ (m .proj₁) ⟩
  (S^ x ↑ • Ex) • H • S^ x⁻¹ • H • S^ x • H ≈⟨ special-assoc (□ ^ 2 • □ ^ 2) (□ • □ ^ 2 • □) auto ⟩
  S^ x ↑ • (Ex • H) • S^ x⁻¹ • H • S^ x • H ≈⟨ cright cleft sym lemma-comm-Ex-H-n ⟩
  S^ x ↑ • (H ↑ • Ex) • S^ x⁻¹ • H • S^ x • H ≈⟨ cright special-assoc (□ ^ 2 • □ ^ 2) (□ • □ ^ 2 • □) auto ⟩
  S^ x ↑ • H ↑ • (Ex • S^ x⁻¹) • H • S^ x • H ≈⟨ cright cright cleft lemma-Ex-S^ᵏ ((m ⁻¹) .proj₁) ⟩
  S^ x ↑ • H ↑ • (S^ x⁻¹ ↑ • Ex) • H • S^ x • H ≈⟨ cright cright special-assoc (□ ^ 2 • □ ^ 2) (□ • □ ^ 2 • □) auto ⟩
  S^ x ↑ • H ↑ • S^ x⁻¹ ↑ • (Ex • H) • S^ x • H ≈⟨ cright cright cright cleft sym lemma-comm-Ex-H-n ⟩
  S^ x ↑ • H ↑ • S^ x⁻¹ ↑ • (H ↑ • Ex) • S^ x • H ≈⟨ cright cright cright special-assoc (□ ^ 2 • □ ^ 2) (□ • □ ^ 2 • □) auto  ⟩
  S^ x ↑ • H ↑ • S^ x⁻¹ ↑ • H ↑ • (Ex • S^ x) • H ≈⟨ cright cright cright cright cleft lemma-Ex-S^ᵏ ((m) .proj₁) ⟩
  S^ x ↑ • H ↑ • S^ x⁻¹ ↑ • H ↑ • (S^ x ↑ • Ex) • H ≈⟨  cright cright cright cright assoc ⟩
  S^ x ↑ • H ↑ • S^ x⁻¹ ↑ • H ↑ • S^ x ↑ • Ex • H ≈⟨  cright cright cright cright cright sym lemma-comm-Ex-H-n ⟩
  S^ x ↑ • H ↑ • S^ x⁻¹ ↑ • H ↑ • S^ x ↑ • H ↑ • Ex ≈⟨ special-assoc (□ ^ 7) (□ ^ 6 • □) auto ⟩
  M m ↑ • Ex ∎
    where
    x = x' .proj₁
    x⁻¹ = ((x' ⁻¹) .proj₁ )


aux-CZ-CZ^₋₁ : CZ • CZ^ ₋₁ ≈ ε
aux-CZ-CZ^₋₁ = begin
  CZ • CZ^ ₋₁ ≈⟨ refl ⟩
  CZ • CZ ^ toℕ ₚ₋₁ ≈⟨ cright refl' (Eq.cong (CZ ^_) lemma-toℕ₋₁) ⟩
  CZ • CZ ^ p-1 ≈⟨ axiom order-CZ ⟩
  ε ∎

aux-Ex1 : Ex • CZ^ ₋₁ • H^ ₃ ↑ • H^ ₃ • CZ^ ₋₁ • H ↑ ^ 3 • H ^ 3 ≈ H • H ↑ • CZ
aux-Ex1 = begin
  Ex • CZ^ ₋₁ • H^ ₃ ↑ • H^ ₃ • CZ^ ₋₁ • H ↑ ^ 3 • H ^ 3 ≈⟨ cleft lemma-comm-Ex-CZ'-n ⟩
  ((H ↓ • H ↑ • CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑) • CZ) • CZ^ ₋₁ • H^ ₃ ↑ • H^ ₃ • CZ^ ₋₁ • H ↑ ^ 3 • H ^ 3 ≈⟨ special-assoc (□ ^ 2 • □ ^ 2) (□ • □ ^ 2 • □) auto ⟩
  (H ↓ • H ↑ • CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑) • (CZ • CZ^ ₋₁) • H^ ₃ ↑ • H^ ₃ • CZ^ ₋₁ • H ↑ ^ 3 • H ^ 3 ≈⟨ cright cleft aux-CZ-CZ^₋₁ ⟩
  (H ↓ • H ↑ • CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑) • ε • H^ ₃ ↑ • H^ ₃ • CZ^ ₋₁ • H ↑ ^ 3 • H ^ 3 ≈⟨ by-assoc auto ⟩
  (H ↓ • H ↑ • CZ • H ↓ • H ↑ • CZ • H ↓) • H ↑ ^ 4 • H^ ₃ • CZ^ ₋₁ • H ↑ ^ 3 • H ^ 3 ≈⟨ cright cleft axiom (cong↑ order-H) ⟩
  (H ↓ • H ↑ • CZ • H ↓ • H ↑ • CZ • H ↓) • ε • H^ ₃ • CZ^ ₋₁ • H ↑ ^ 3 • H ^ 3 ≈⟨ by-assoc auto ⟩
  (H ↓ • H ↑ • CZ • H ↓ • H ↑ • CZ) • H ↓ ^ 4 • CZ^ ₋₁ • H ↑ ^ 3 • H ^ 3 ≈⟨ cright cleft axiom order-H ⟩
  (H ↓ • H ↑ • CZ • H ↓ • H ↑ • CZ) • ε • CZ^ ₋₁ • H ↑ ^ 3 • H ^ 3 ≈⟨ by-assoc auto ⟩
  (H ↓ • H ↑ • CZ • H ↓ • H ↑) • (CZ • CZ^ ₋₁) • H ↑ ^ 3 • H ^ 3 ≈⟨ cright cleft aux-CZ-CZ^₋₁ ⟩
  (H ↓ • H ↑ • CZ • H ↓ • H ↑) • ε • H ↑ ^ 3 • H ^ 3 ≈⟨ by-assoc auto ⟩
  (H ↓ • H ↑ • CZ • H ↓) • H ↑ ^ 4 • H ^ 3 ≈⟨  cright cleft axiom (cong↑ order-H) ⟩
  (H ↓ • H ↑ • CZ • H ↓) • ε • H ^ 3 ≈⟨ by-assoc auto ⟩
  (H ↓ • H ↑ • CZ) • H ↓ ^ 4 ≈⟨ cright axiom order-H ⟩
  (H ↓ • H ↑ • CZ) • ε ≈⟨ right-unit ⟩
  H • H ↑ • CZ ∎


aux-Ex-inv : CZ^ ₋₁ • H^ ₃ ↑ • H^ ₃ • CZ^ ₋₁ • H ↑ ^ 3 • H ^ 3 ≈ Ex • H • H ↑ • CZ
aux-Ex-inv = bbc Ex ε claim
  where
  claim : Ex • (CZ^ ₋₁ • H^ ₃ ↑ • H^ ₃ • CZ^ ₋₁ • H ↑ ^ 3 • H ^ 3) • ε ≈ Ex • (Ex • H • H ↑ • CZ) • ε
  claim = begin
    Ex • (CZ^ ₋₁ • H^ ₃ ↑ • H^ ₃ • CZ^ ₋₁ • H ↑ ^ 3 • H ^ 3) • ε ≈⟨ cong refl right-unit ⟩
    Ex • (CZ^ ₋₁ • H^ ₃ ↑ • H^ ₃ • CZ^ ₋₁ • H ↑ ^ 3 • H ^ 3) ≈⟨ aux-Ex1 ⟩
    H • H ↑ • CZ ≈⟨ sym left-unit ⟩
    ε • H • H ↑ • CZ ≈⟨ cleft sym lemma-order-Ex-n ⟩
    (Ex • Ex) • H • H ↑ • CZ ≈⟨ assoc ⟩
    Ex • (Ex • H • H ↑ • CZ) ≈⟨ sym (cong refl right-unit) ⟩
    Ex • (Ex • H • H ↑ • CZ) • ε ∎

aux-Ex2 : Ex • H ↑ ^ 3 • H ^ 3 • CZ^ ₋₁ • H ↑ ^ 3 ≈ CZ • H • H ↑ • CZ • H
aux-Ex2 = begin
  Ex • H ↑ ^ 3 • H ^ 3 • CZ^ ₋₁ • H ↑ ^ 3 ≈⟨ refl ⟩
  (CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑) • H ↑ ^ 3 • H ^ 3 • CZ^ ₋₁ • H ↑ ^ 3 ≈⟨ rewrite-sym0 100 auto ⟩
  (CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑ • CZ) • (H ↓ • H ↑ • H ↑ ^ 3 • H ^ 3) • CZ^ ₋₁ • H ↑ ^ 3 ≈⟨ cright cleft rewrite-sym0 100 auto ⟩
  (CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑ • CZ) • ε • CZ^ ₋₁ • H ↑ ^ 3 ≈⟨ by-assoc auto ⟩
  (CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑) • (CZ • CZ^ ₋₁) • H ↑ ^ 3 ≈⟨ cright cleft aux-CZ-CZ^₋₁ ⟩
  (CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑) • ε • H ↑ ^ 3 ≈⟨ by-assoc auto ⟩
  (CZ • H ↓ • H ↑ • CZ) • H ↓ • H ↑ • ε • H ↑ ^ 3 ≈⟨ cright rewrite-sym0 100 auto ⟩
  (CZ • H ↓ • H ↑ • CZ) • H ≈⟨ by-assoc auto ⟩
  CZ • H • H ↑ • CZ • H ∎

lemma-comm-Ex-H↑ : 
  H • Ex ≈ Ex • H ↑ 
lemma-comm-Ex-H↑ = bbc Ex Ex claim
  where
  claim : Ex • (H • Ex) • Ex ≈ Ex • (Ex • H ↑) • Ex
  claim = begin
    Ex • (H • Ex) • Ex ≈⟨ by-assoc auto ⟩
    (Ex • H) • Ex • Ex ≈⟨ cright lemma-order-Ex-n ⟩
    (Ex • H) • ε ≈⟨ right-unit ⟩
    (Ex • H) ≈⟨ sym lemma-comm-Ex-H-n ⟩
    H ↑ • Ex ≈⟨ sym left-unit ⟩
    ε • H ↑ • Ex ≈⟨ cleft sym lemma-order-Ex-n ⟩
    (Ex • Ex) • H ↑ • Ex ≈⟨ by-assoc auto ⟩
    Ex • (Ex • H ↑) • Ex ∎


lemma-comm-Ex-S↑ : 
  S • Ex ≈ Ex • S ↑ 
lemma-comm-Ex-S↑ = bbc Ex Ex claim
  where
  claim : Ex • (S • Ex) • Ex ≈ Ex • (Ex • S ↑) • Ex
  claim = begin
    Ex • (S • Ex) • Ex ≈⟨ by-assoc auto ⟩
    (Ex • S) • Ex • Ex ≈⟨ cright lemma-order-Ex-n ⟩
    (Ex • S) • ε ≈⟨ right-unit ⟩
    (Ex • S) ≈⟨ sym lemma-comm-Ex-S ⟩
    S ↑ • Ex ≈⟨ sym left-unit ⟩
    ε • S ↑ • Ex ≈⟨ cleft sym lemma-order-Ex-n ⟩
    (Ex • Ex) • S ↑ • Ex ≈⟨ by-assoc auto ⟩
    Ex • (Ex • S ↑) • Ex ∎


aux-NF2 : ∀ l (pf : Postfix) -> let (sp , mc2 , mc1) = pf in let pf' = (sp + l , mc1 , mc2) in let w = H • S^ l in
  ⟦ case-|| (₁ , λ ()) l pf ⟧₂ ≈ w ↑ • Ex • dual ⟦ case-||ₐ (- l) pf' ⟧₂
aux-NF2 l pf@(sp , mc2 , mc1) = claim
  where
  pf' = (sp + l , mc1 , mc2)
  w = H • S^ l
  claim : ⟦ case-|| (₁ , (λ ())) l pf ⟧₂ ≈ w ↑ • Ex • dual ⟦ case-||ₐ (- l) pf' ⟧₂
  claim = begin
    ⟦ case-|| (₁ , (λ ())) l pf ⟧₂ ≈⟨ refl ⟩
    CZ • H^ ₃ ↑ • S^ l ↑ • ⟦ pf ⟧ₚ ≈⟨ refl ⟩
    CZ • H^ ₃ ↑ • S^ l ↑ • S^ sp • (H^ ₃ • CZ • H) • ⟦ mc2 ⟧ₘ₊ ↑ • ⟦ mc1 ⟧ₘ₊ ≈⟨ cright sym (cong refl assoc) ⟩
    CZ • H^ ₃ ↑ • (S^ l ↑ • S^ sp) • (H^ ₃ • CZ • H) • ⟦ mc2 ⟧ₘ₊ ↑ • ⟦ mc1 ⟧ₘ₊ ≈⟨ cright cright cleft sym (lemma-comm-Sᵏ-w↑ (toℕ sp) (S^ l)) ⟩
    CZ • H^ ₃ ↑ • (S^ sp • S^ l ↑) • (H^ ₃ • CZ • H) • ⟦ mc2 ⟧ₘ₊ ↑ • ⟦ mc1 ⟧ₘ₊ ≈⟨ cright special-assoc (□ • □ ^ 2 • □ ^ 3 • □) (□ ^ 2 • □ ^ 2 • □ ^ 2 • □) auto ⟩
    CZ • (H^ ₃ ↑ • S^ sp) • (S^ l ↑ • H^ ₃) • (CZ • H) • ⟦ mc2 ⟧ₘ₊ ↑ • ⟦ mc1 ⟧ₘ₊ ≈⟨ cright cong (sym (lemma-comm-Sᵏ-w↑ (toℕ sp) (H^ ₃))) (cleft sym (lemma-comm-Hᵏ-w↑ 3 (S^ l))) ⟩
    CZ • (S^ sp • H^ ₃ ↑) • (H^ ₃ • S^ l ↑) • (CZ • H) • ⟦ mc2 ⟧ₘ₊ ↑ • ⟦ mc1 ⟧ₘ₊ ≈⟨ special-assoc (□ • □ ^ 2 • □ ^ 2 • □ ^ 2 • □ ^ 2) (□ ^ 2 • □  • □ • □ ^ 2 • □ ^ 3) auto ⟩
    (CZ • S^ sp) • H^ ₃ ↑ • H^ ₃ • (S^ l ↑ • CZ) • H • ⟦ mc2 ⟧ₘ₊ ↑ • ⟦ mc1 ⟧ₘ₊ ≈⟨ cong (word-comm 1 (toℕ sp) (axiom comm-CZ-S↓)) (cright cright (cleft sym (aux-comm-CZ^a-S^b↑ ₁ l))) ⟩
    (S^ sp • CZ) • H^ ₃ ↑ • H^ ₃ • (CZ • S^ l ↑) • H • ⟦ mc2 ⟧ₘ₊ ↑ • ⟦ mc1 ⟧ₘ₊ ≈⟨ special-assoc (□ ^ 2 • □  • □ • □ ^ 2 • □ ^ 3) (□ • □ ^ 4 • □ ^ 2 • □ ^ 2) auto ⟩
    S^ sp • (CZ • H^ ₃ ↑ • H^ ₃ • CZ) • (S^ l ↑ • H) • ⟦ mc2 ⟧ₘ₊ ↑ • ⟦ mc1 ⟧ₘ₊ ≈⟨ cright cright cleft sym (lemma-comm-Hᵏ-w↑ 1 (S^ l)) ⟩
    S^ sp • (CZ • H^ ₃ ↑ • H^ ₃ • CZ) • (H • S^ l ↑) • ⟦ mc2 ⟧ₘ₊ ↑ • ⟦ mc1 ⟧ₘ₊ ≈⟨ by-assoc auto ⟩
    S^ sp • (CZ • H^ ₂ ↑) • (H ↑ • H^ ₃ • CZ) • (H • S^ l ↑) • ⟦ mc2 ⟧ₘ₊ ↑ • ⟦ mc1 ⟧ₘ₊ ≈⟨ cright cong ( lemma-semi-CZ-HH↑) (cleft general-comm auto) ⟩
    S^ sp • (H^ ₂ ↑ • CZ^ ₋₁) • (H^ ₂ • H • H ↑ • CZ) • (H • S^ l ↑) • ⟦ mc2 ⟧ₘ₊ ↑ • ⟦ mc1 ⟧ₘ₊ ≈⟨ special-assoc (□ • □ ^ 2 • □ ^ 4 • □) (□ • □ • □ ^ 2 • □ ^ 3 • □) auto ⟩
    S^ sp • H^ ₂ ↑ • (CZ^ ₋₁ • H^ ₂) • (H • H ↑ • CZ) • (H • S^ l ↑) • ⟦ mc2 ⟧ₘ₊ ↑ • ⟦ mc1 ⟧ₘ₊ ≈⟨ cright cright cleft sym lemma-semi-HH↓-CZ ⟩
    S^ sp • H^ ₂ ↑ • (H^ ₂ • CZ) • (H • H ↑ • CZ) • (H • S^ l ↑) • ⟦ mc2 ⟧ₘ₊ ↑ • ⟦ mc1 ⟧ₘ₊ ≈⟨ special-assoc (□ • □ • □ ^ 2 • □ ^ 3 • □ ^ 2 • □) (□ ^ 3 • □ ^ 5 • □ • □) auto ⟩
    (S^ sp • H^ ₂ ↑ • H^ ₂) • (CZ • H • H ↑ • CZ • H) • S^ l ↑ • ⟦ mc2 ⟧ₘ₊ ↑ • ⟦ mc1 ⟧ₘ₊ ≈⟨ cright cleft sym aux-Ex2 ⟩
    (S^ sp • H^ ₂ ↑ • H^ ₂) • (Ex • H ↑ ^ 3 • H ^ 3 • CZ^ ₋₁ • H ↑ ^ 3) • S^ l ↑ • ⟦ mc2 ⟧ₘ₊ ↑ • ⟦ mc1 ⟧ₘ₊ ≈⟨ cright by-assoc auto ⟩
    (S^ sp • H^ ₂ ↑ • H^ ₂) • (Ex • H ↑ ^ 2) • (H ↑ • H ^ 3) • (CZ^ ₋₁ • H ↑ ^ 3) • S^ l ↑ • ⟦ mc2 ⟧ₘ₊ ↑ • ⟦ mc1 ⟧ₘ₊ ≈⟨ cright cong (lemma-Induction (sym lemma-comm-Ex-H↑) 2) (cong (word-comm 1 3 (axiom comm-H)) (special-assoc (□ ^ 4 • □) (□ ^ 3 • □ • □) auto)) ⟩
    (S^ sp • H^ ₂ ↑ • H^ ₂) • (H ^ 2 • Ex) • (H ^ 3 • H ↑) • (CZ^ ₋₁ • H ↑ ^ 2) • H ↑ • S^ l ↑ • ⟦ mc2 ⟧ₘ₊ ↑ • ⟦ mc1 ⟧ₘ₊ ≈⟨ cright cright cright cleft sym lemma-semi-HH↑-CZ ⟩
    (S^ sp • H^ ₂ ↑ • H^ ₂) • (H ^ 2 • Ex) • (H ^ 3 • H ↑) • (H ↑ ^ 2 • CZ) • H ↑ • S^ l ↑ • ⟦ mc2 ⟧ₘ₊ ↑ • ⟦ mc1 ⟧ₘ₊ ≈⟨ special-assoc (□ ^ 3 • □ ^ 2 • □ ^ 2 • (□ ^ 2 • □) • □) (□ ^ 4 • □ ^ 2 • (□ ^ 3 • □) • □) auto ⟩
    (S^ sp • H^ ₂ ↑ • H^ ₂ • H ^ 2) • (Ex • H ^ 3) • (H ↑ ^ 3 • CZ) • H ↑ • S^ l ↑ • ⟦ mc2 ⟧ₘ₊ ↑ • ⟦ mc1 ⟧ₘ₊ ≈⟨ cong (cright rewrite-sym0 100 auto) (cleft lemma-Induction (sym lemma-comm-Ex-H) 3) ⟩
    (S^ sp • H^ ₂ ↑) • (H ↑ ^ 3 • Ex) • (H ↑ ^ 3 • CZ) • H ↑ • S^ l ↑ • ⟦ mc2 ⟧ₘ₊ ↑ • ⟦ mc1 ⟧ₘ₊ ≈⟨ special-assoc (□ ^ 3 • (□ ^ 3 • □) • □ ^ 2 • □ ^ 3) (□ ^ 6 • □ • (□ ^ 3 • □) • □) auto ⟩
    (S^ sp • H ↑ ^ 5) • Ex • ((H ↑ ^ 3 • CZ • H ↑) • S^ l ↑) • ⟦ mc2 ⟧ₘ₊ ↑ • ⟦ mc1 ⟧ₘ₊ ≈⟨ cong (cright rewrite-sym0 100 auto) (cright cleft sym (lemma-XCS^k' l)) ⟩
    (S^ sp • H ↑) • Ex • (S^ l ↑ • S^ l • CZ^ (- l) • H ↑ ^ 3 • CZ • H ↑) • ⟦ mc2 ⟧ₘ₊ ↑ • ⟦ mc1 ⟧ₘ₊ ≈⟨ cright (cright cleft special-assoc (□ ^ 6 ) (□ ^ 2 • □ ^ 4) auto) ⟩
    (S^ sp • H ↑) • Ex • ((S^ l ↑ • S^ l) • (CZ^ (- l) • H ↑ ^ 3 • CZ • H ↑)) • ⟦ mc2 ⟧ₘ₊ ↑ • ⟦ mc1 ⟧ₘ₊ ≈⟨ cright cright cleft cleft sym (lemma-comm-Sᵏ-w↑ (toℕ l) (S^ l)) ⟩
    (S^ sp • H ↑) • Ex • ((S^ l • S^ l ↑) • (CZ^ (- l) • H ↑ ^ 3 • CZ • H ↑)) • ⟦ mc2 ⟧ₘ₊ ↑ • ⟦ mc1 ⟧ₘ₊ ≈⟨ cong (lemma-comm-Sᵏ-w↑ (toℕ sp) H) (special-assoc (□ • (□ ^ 2 • □) • □) (□ ^ 2 • □ ^ 2 • □) auto) ⟩
    (H ↑ • S^ sp) • (Ex • S^ l) • (S^ l ↑ • (CZ^ (- l) • H ↑ ^ 3 • CZ • H ↑)) • ⟦ mc2 ⟧ₘ₊ ↑ • ⟦ mc1 ⟧ₘ₊ ≈⟨ cright cong (lemma-Induction (sym lemma-comm-Ex-S) (toℕ l)) (special-assoc ((□ • □ ^ 2) • □) (□ ^ 2 • □ • □) auto) ⟩
    (H ↑ • S^ sp) • (S ↑ ^ toℕ l • Ex) • (S^ l ↑ • CZ^ (- l)) • (H ↑ ^ 3 • CZ • H ↑) • ⟦ mc2 ⟧ₘ₊ ↑ • ⟦ mc1 ⟧ₘ₊ ≈⟨ special-assoc (□ ^ 2 • □ ^ 2 • □) (□ • □ ^ 2 • □ • □) auto ⟩
    H ↑ • (S^ sp • S ↑ ^ toℕ l) • Ex • (S^ l ↑ • CZ^ (- l)) • (H ↑ ^ 3 • CZ • H ↑) • ⟦ mc2 ⟧ₘ₊ ↑ • ⟦ mc1 ⟧ₘ₊ ≈⟨ cright cong (word-comm (toℕ sp) (toℕ l) (sym (axiom comm-S))) (cright (cleft sym (refl))) ⟩
    H ↑ • (S ↑ ^ toℕ l • S^ sp) • Ex • (S^ l ↑ • CZ^ (- l)) • (H ↑ ^ 3 • CZ • H ↑) • ⟦ mc2 ⟧ₘ₊ ↑ • ⟦ mc1 ⟧ₘ₊ ≈⟨ special-assoc (□ • □ ^ 2 • □ • □) (□ ^ 2 • □ ^ 2 • □) auto ⟩
    (H ↑ • S ↑ ^ toℕ l) • (S^ sp • Ex) • (S^ l ↑ • CZ^ (- l)) • (H ↑ ^ 3 • CZ • H ↑) • ⟦ mc2 ⟧ₘ₊ ↑ • ⟦ mc1 ⟧ₘ₊ ≈⟨ cong (cright refl' (aux-↑ S (toℕ l))) (cleft sym (lemma-Induction (sym lemma-comm-Ex-S↑) (toℕ sp))) ⟩
    (H ↑ • S^ l ↑) • (Ex • S ↑ ^ toℕ sp) • (S^ l ↑ • CZ^ (- l)) • (H ↑ ^ 3 • CZ • H ↑) • ⟦ mc2 ⟧ₘ₊ ↑ • ⟦ mc1 ⟧ₘ₊ ≈⟨ cright cleft cright refl' (aux-↑ S (toℕ sp)) ⟩
    (H ↑ • S^ l ↑) • (Ex • S^ sp ↑) • (S^ l ↑ • CZ^ (- l)) • (H ↑ ^ 3 • CZ • H ↑) • ⟦ mc2 ⟧ₘ₊ ↑ • ⟦ mc1 ⟧ₘ₊ ≈⟨ cright special-assoc (□ ^ 2 • □ ^ 2 • □) (□ • □ ^ 2 • □ • □) auto ⟩
    (H ↑ • S^ l ↑) • Ex • (S^ sp ↑ • S^ l ↑) • CZ^ (- l) • (H ↑ ^ 3 • CZ • H ↑) • ⟦ mc2 ⟧ₘ₊ ↑ • ⟦ mc1 ⟧ₘ₊ ≈⟨ cright cright cleft lemma-cong↑ _ _ (L0.lemma-S^k+l sp l) ⟩
    (H ↑ • S^ l ↑) • Ex • S^ (sp + l) ↑ • CZ^ (- l) • (H ↑ ^ 3 • CZ • H ↑) • ⟦ mc2 ⟧ₘ₊ ↑ • ⟦ mc1 ⟧ₘ₊ ≈⟨ cright cright sym assoc ⟩
    (H ↑ • S^ l ↑) • Ex • (S^ (sp + l) ↑ • CZ^ (- l)) • (H ↑ ^ 3 • CZ • H ↑) • ⟦ mc2 ⟧ₘ₊ ↑ • ⟦ mc1 ⟧ₘ₊ ≈⟨ cright cright cleft sym (aux-comm-CZ^a-S^b↑ (fromℕ< _) (fromℕ< _)) ⟩
    (H ↑ • S^ l ↑) • Ex • (CZ^ (- l) • S^ (sp + l) ↑) • (H ↑ ^ 3 • CZ • H ↑) • ⟦ mc2 ⟧ₘ₊ ↑ • ⟦ mc1 ⟧ₘ₊ ≈⟨ cright cright cright cright sym (aux-comm-MCMC (mc1 .proj₁) (mc1 .proj₂) (mc2 .proj₁) (mc2 .proj₂)) ⟩
    (H ↑ • S^ l ↑) • Ex • (CZ^ (- l) • S^ (sp + l) ↑) • (H ↑ ^ 3 • CZ • H ↑) • ⟦ mc1 ⟧ₘ₊ • ⟦ mc2 ⟧ₘ₊ ↑ ≈⟨ cright cright assoc ⟩
    (H ↑ • S^ l ↑) • Ex • CZ^ (- l) • S^ (sp + l) ↑ • (H ↑ ^ 3 • CZ • H ↑) • ⟦ mc1 ⟧ₘ₊ • ⟦ mc2 ⟧ₘ₊ ↑ ≈⟨ cright cright cong (sym (refl' (aux-dual-CZ^k (toℕ (- l))))) (cong (sym (refl' (aux-dual-S^k (toℕ (sp + l))))) (cright cong (sym (refl' (ND.aux-dual-MC↑ mc1))) (sym (refl' (ND.aux-dual-MC mc2))))) ⟩
    (H ↑ • S^ l ↑) • Ex • dual (CZ^ (- l)) • dual (S^ (sp + l)) • dual (H ^ 3 • CZ • H) • dual (⟦ mc1 ⟧ₘ₊ ↑) • dual (⟦ mc2 ⟧ₘ₊) ≈⟨ cright cright refl ⟩

    w ↑ • Ex • dual ⟦ case-||ₐ (- l) pf' ⟧₂ ∎
    where
    module L0 = Lemmas0 0



aux-NF2' : ∀ l (pf : Postfix) -> let (sp , mc2 , mc1) = pf in let pf' = (sp + l , mc1 , mc2) in let w = S^ (- l) • H ^ 3 in
  w ↑ • ⟦ case-|| (₁ , λ ()) l pf ⟧₂ ≈ Ex • dual ⟦ case-||ₐ (- l) pf' ⟧₂
aux-NF2' l pf@(sp , mc2 , mc1) = bbc (H ↑ • S^ l ↑) ε aux
  where
  w = (S^ (- l) • H ^ 3)
  pf' = (sp + l , mc1 , mc2)

  aux : (H ↑ • S^ l ↑) • (w ↑ • ⟦ case-|| (₁ , λ ()) l pf ⟧₂) • ε ≈ (H ↑ • S^ l ↑) • (Ex • dual ⟦ case-||ₐ (- l) pf' ⟧₂) • ε
  aux = begin
    (H ↑ • S^ l ↑) • (w ↑ • ⟦ case-|| (₁ , λ ()) l pf ⟧₂) • ε ≈⟨ cong refl right-unit ⟩
    (H ↑ • S^ l ↑) • (w ↑ • ⟦ case-|| (₁ , λ ()) l pf ⟧₂)  ≈⟨ special-assoc (□ ^ 2 • □ ^ 2) (□ ^ 3 • □) auto ⟩
    (H ↑ • S^ l ↑ • w ↑) • ⟦ case-|| (₁ , λ ()) l pf ⟧₂ ≈⟨ cong (sym (cong refl assoc)) (aux-NF2 l pf) ⟩
    (H ↑ • (S^ l ↑ • S^ (- l) ↑) • H ↑ ^ 3) • (H ↑ • S^ l ↑) • Ex • dual ⟦ case-||ₐ (- l) pf' ⟧₂ ≈⟨ cleft (cright cleft lemma-cong↑ _ _ (L0.lemma-S^k-k l)) ⟩
    (H ↑ • ε • H ↑ ^ 3) • (H ↑ • S^ l ↑) • Ex • dual ⟦ case-||ₐ (- l) pf' ⟧₂ ≈⟨ cleft rewrite-sym0 100 auto ⟩
    ε • (H ↑ • S^ l ↑) • Ex • dual ⟦ case-||ₐ (- l) pf' ⟧₂ ≈⟨ left-unit ⟩
    (H ↑ • S^ l ↑) • Ex • dual ⟦ case-||ₐ (- l) pf' ⟧₂ ≈⟨ sym (cong refl right-unit) ⟩
    (H ↑ • S^ l ↑) • (Ex • dual ⟦ case-||ₐ (- l) pf' ⟧₂) • ε ∎
    where
    module L0 = Lemmas0 0

open import Zp.Mod-Lemmas p-2 p-prime




aux-NF2'' : ∀ l (pf : Postfix) -> let (sp , mc2 , mc1) = pf in let pf' = (sp + l , mc1 , mc2) in let w = S^ l • H ^ 3 in
  w ↑ • ⟦ case-|| (₁ , λ ()) (- l) pf' ⟧₂ ≈ Ex • dual ⟦ case-||ₐ l pf ⟧₂
aux-NF2'' l pf@(sp , mc2 , mc1) = begin
  w ↑ • ⟦ case-|| (₁ , λ ()) (- l) pf' ⟧₂ ≈⟨ cleft (cleft refl' (Eq.cong (\ xx -> S^ xx ↑) (Eq.sym (-‿involutive l)))) ⟩
  w' ↑ • ⟦ case-|| (₁ , λ ()) (- l) pf' ⟧₂ ≈⟨ aux-NF2' (- l) pf' ⟩
  Ex • dual ⟦ case-||ₐ (- - l) pf'' ⟧₂ ≈⟨ cright refl' (Eq.cong₂ (\ xx yy -> dual ⟦ case-||ₐ xx yy ⟧₂) (-‿involutive l) (Eq.cong ((_, mc2 , mc1)) aux)) ⟩
  Ex • dual ⟦ case-||ₐ l pf ⟧₂ ∎
  where
  w = (S^ l • H ^ 3)
  w' = (S^ (- - l) • H ^ 3)
  pf' = (sp + l , mc1 , mc2)
  pf'' = (sp + l + - l , mc2 , mc1)
  aux : sp + l + - l ≡ sp
  aux = Eq.trans (+-assoc sp l (- l)) (Eq.trans (Eq.cong (sp +_) (+-inverseʳ l)) (+-identityʳ sp))
  

lemma-CZ^-pred : ∀ (k* : ℤ* ₚ) ->
  let
  (k , nzk) = k*
  kp = prede k*
  in
  CZ^ k ≈ CZ^ kp • CZ
lemma-CZ^-pred k*@(₀ , nzk) with nzk auto
... | ()
lemma-CZ^-pred k*@(₁₊ k , nzk) = begin
  CZ^ (₁₊ k) ≈⟨ sym (aux-ww^k CZ (toℕ k)) ⟩
  CZ • CZ ^ (toℕ k) ≈⟨ word-comm 1 (toℕ k) refl ⟩
  CZ ^ (toℕ k) • CZ ≈⟨ cleft refl' (Eq.cong (CZ ^_) (Eq.sym (toℕ-inject₁ k))) ⟩
  CZ^ kp • CZ ∎
  where
  kp = prede k*

Ex' : ∀ {n} → Word (Gen (₂₊ n))
Ex' = H ↓ • H ↑ • CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑ • CZ

aux-Ex-Ex' : Ex ≈ Ex'
aux-Ex-Ex' = begin
  Ex ≈⟨ lemma-comm-Ex-CZ' ⟩
  (H ↓ • H ↑ • CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑) • CZ ≈⟨ general-comm auto ⟩
  Ex' ∎

aux-hEx' : CZ • H • H ↑ • CZ ≈ H ↑ ^ 3 • H ^ 3 • CZ⁻¹ • H ↑ ^ 3 • H ^ 3 • Ex
aux-hEx' = bbc (H • H ↑ • CZ • H • H ↑) ε aux
  where
  aux : (H • H ↑ • CZ • H • H ↑) • (CZ • H • H ↑ • CZ) • ε ≈ (H • H ↑ • CZ • H • H ↑) • (H ↑ ^ 3 • H ^ 3 • CZ⁻¹ • H ↑ ^ 3 • H ^ 3 • Ex) • ε
  aux = begin
    (H • H ↑ • CZ • H • H ↑) • (CZ • H • H ↑ • CZ) • ε ≈⟨ cright right-unit ⟩
    (H • H ↑ • CZ • H • H ↑) • (CZ • H • H ↑ • CZ) ≈⟨ by-assoc auto ⟩
    Ex' ≈⟨ sym aux-Ex-Ex' ⟩
    Ex ≈⟨ rewrite-sym0 100 auto ⟩
    (H • H ↑) • (ε) • H ↑ ^ 3 • H ^ 3 • Ex ≈⟨  cright cleft sym (axiom order-CZ) ⟩
    (H • H ↑) • (CZ • CZ⁻¹) • H ↑ ^ 3 • H ^ 3 • Ex ≈⟨  special-assoc (□ ^ 2 • □ ^ 2 • □) (□ ^ 3 • □ ^ 2) auto ⟩
    (H • H ↑ • CZ) • CZ⁻¹ • H ↑ ^ 3 • H ^ 3 • Ex ≈⟨ cleft rewrite-sym0 100 auto ⟩
    (H • H ↑ • CZ • H • H ↑ • H ↑ ^ 3 • H ^ 3) • CZ⁻¹ • H ↑ ^ 3 • H ^ 3 • Ex ≈⟨ by-assoc auto ⟩
    (H • H ↑ • CZ • H • H ↑) • (H ↑ ^ 3 • H ^ 3 • CZ⁻¹ • H ↑ ^ 3 • H ^ 3 • Ex) ≈⟨ cright sym right-unit ⟩
    (H • H ↑ • CZ • H • H ↑) • (H ↑ ^ 3 • H ^ 3 • CZ⁻¹ • H ↑ ^ 3 • H ^ 3 • Ex) • ε ∎

aux-hEx : CZ • H^ ₃ ↑ • H^ ₃ • CZ • H ≈ H ↑ • H ^ 3 • CZ • H • Ex 
aux-hEx = begin
  CZ • H^ ₃ ↑ • H^ ₃ • CZ • H ≈⟨ general-comm auto ⟩
  (CZ • HH ↑) • (H ↑ • HH) • H • CZ • H ≈⟨ cong lemma-semi-CZ-HH↑ (general-comm auto) ⟩
  (HH ↑ • CZ^ (₋₁)) • (HH • H ↑) • H • CZ • H ≈⟨ special-assoc (□ ^ 2 • □ ^ 2 • □) (□ • □ ^ 2 • □ ^ 2) auto ⟩
  HH ↑ • (CZ^ (₋₁) • HH) • H ↑ • H • CZ • H ≈⟨ cright cleft sym lemma-semi-HH↓-CZ ⟩
  HH ↑ • (HH • CZ) • H ↑ • H •  CZ • H ≈⟨ general-comm auto ⟩
  HH ↑ • HH • (CZ • H • H ↑ • CZ) • H ≈⟨ cright cright cleft sym (sym aux-hEx') ⟩
  HH ↑ • HH • (H ↑ ^ 3 • H ^ 3 • CZ⁻¹ • H ↑ ^ 3 • H ^ 3 • Ex) • H ≈⟨ special-assoc (□ • □ • □ ^ 6 • □) (□ ^ 4 • □ ^ 4 • □) auto ⟩
  (HH ↑ • HH • H ↑ ^ 3 • H ^ 3) • (CZ⁻¹ • H ↑ ^ 3 • H ^ 3 • Ex) • H ≈⟨ cleft rewrite-sym0 100 auto ⟩
  (H ↑ • H) • (CZ⁻¹ • H ↑ ^ 3 • H ^ 3 • Ex) • H ≈⟨ cright cleft cright rewrite-sym0 100 auto ⟩
  (H ↑ • H) • (CZ⁻¹ • HH • H • H ↑ ^ 3 • Ex) • H ≈⟨ cright special-assoc (□ ^ 5 • □) (□ ^ 2 • □ ^ 4) auto ⟩
  (H ↑ • H) • (CZ⁻¹ • HH) • H • H ↑ ^ 3 • Ex • H ≈⟨ cright cleft (cleft refl' (Eq.cong (CZ ^_) (Eq.sym lemma-toℕ-ₚ₋₁))) ⟩
  (H ↑ • H) • (CZ^ ₋₁ • HH) • H • H ↑ ^ 3 • Ex • H ≈⟨ cright cleft sym lemma-semi-HH↓-CZ ⟩
  (H ↑ • H) • (HH • CZ) • H • H ↑ ^ 3 • Ex • H ≈⟨ general-comm auto ⟩
  (H ↑ • H ^ 3 • CZ • H • H ↑ ^ 3) • Ex • H ≈⟨ cright rewrite-ex 100 auto ⟩
  (H ↑ • H ^ 3 • CZ • H • H ↑ ^ 3) • H ↑ • Ex ≈⟨ rewrite-sym0 100 auto ⟩
  H ↑ • H ^ 3 • CZ • H • Ex  ∎


aux-hEx′ : CZ • H^ ₃ ↑ • H^ ₃ • CZ ≈ H ↑ • H ^ 3 • CZ • H • H ↑ ^ 3 •  Ex 
aux-hEx′ = bbc ε (H) aux
  where
  aux : ε • (CZ • H^ ₃ ↑ • H^ ₃ • CZ) • H ≈ ε • (H ↑ • H ^ 3 • CZ • H • H ↑ ^ 3 •  Ex) • H
  aux = begin
    ε • (CZ • H^ ₃ ↑ • H^ ₃ • CZ) • H ≈⟨ by-assoc auto ⟩
    CZ • H^ ₃ ↑ • H^ ₃ • CZ • H ≈⟨ aux-hEx ⟩
    H ↑ • H ^ 3 • CZ • H • Ex ≈⟨ by-assoc auto ⟩
    (H ↑ • H ^ 3 • CZ • H) • Ex ≈⟨ cright sym (trans (cong refl (axiom order-H)) right-unit) ⟩
    (H ↑ • H ^ 3 • CZ • H) • Ex • H ^ 4 ≈⟨ cright rewrite-ex 100 auto ⟩
    (H ↑ • H ^ 3 • CZ • H) • (H ↑ ^ 3 • Ex) • H ≈⟨ by-assoc auto ⟩
    ε • (H ↑ • H ^ 3 • CZ • H • H ↑ ^ 3 •  Ex) • H ∎



               
aux-NF2′ : ∀ l (pf : Postfix) -> let (sp , mc2 , mc1) = pf in let pf' = (sp + l , mc1 , mc2) in let w = H • S^ l in
  ⟦ case-|| (₁ , λ ()) l pf ⟧₂ ≈ w ↑ • ⟦ case-||ₐ (- l) pf' ⟧₂ • Ex
aux-NF2′ l pf@(sp , mc2 , mc1) = begin
  ⟦ case-|| (₁ , λ ()) l pf ⟧₂ ≈⟨ aux-NF2 l pf ⟩
  w ↑ • Ex • dual ⟦ case-||ₐ (- l) pf' ⟧₂ ≈⟨ cright cright lemma-Ex-dual ⟦ case-||ₐ (- l) pf' ⟧₂ ⟩
  w ↑ • Ex • Ex • ⟦ case-||ₐ (- l) pf' ⟧₂ • Ex ≈⟨ cright sym assoc ⟩
  w ↑ • (Ex • Ex) • ⟦ case-||ₐ (- l) pf' ⟧₂ • Ex ≈⟨ cright cleft lemma-order-Ex ⟩
  w ↑ • ε • ⟦ case-||ₐ (- l) pf' ⟧₂ • Ex ≈⟨ cright left-unit ⟩
  w ↑ • ⟦ case-||ₐ (- l) pf' ⟧₂ • Ex ∎
  where
  pf' = (sp + l , mc1 , mc2)
  w = H • S^ l

aux-|| : ∀ k* l* sp pf -> k* .proj₁ ≡ l* .proj₁ -> ⟦ case-|| k* sp pf ⟧₂ ≈ ⟦ case-|| l*  sp pf ⟧₂
aux-|| k*@(k , _) l*@(l , _) sp pf eq = begin
  ⟦ case-|| k* sp pf ⟧₂ ≈⟨ refl ⟩
  CZ^ k • H^ ₃ ↑ • S^ sp ↑ • ⟦ pf ⟧ₚ ≈⟨ cleft refl' (Eq.cong CZ^ eq) ⟩
  CZ^ l • H^ ₃ ↑ • S^ sp ↑ • ⟦ pf ⟧ₚ ≈⟨ refl ⟩
  ⟦ case-|| l*  sp pf ⟧₂ ∎


case-duality' : ∀ mc nf1 -> Ex • dual ⟦ case-| mc nf1 ⟧₂ ≈ ⟦ case-Ex-| nf1 mc ⟧₂
case-duality' mc nf1 = begin
  Ex • dual ⟦ case-| mc nf1 ⟧₂ ≈⟨ cright cright cong (refl' (aux-dual-MC↑ mc)) (refl' (aux-dual-SMC nf1)) ⟩
  Ex • CZ • ⟦ mc ⟧ₘ₊ • ⟦ nf1 ⟧₁ ↑ ≈⟨ cright cright aux-comm-MCSMC mc nf1 ⟩
  Ex • CZ • ⟦ nf1 ⟧₁ ↑ • ⟦ mc ⟧ₘ₊ ≈⟨ refl ⟩
  ⟦ case-Ex-| nf1 mc ⟧₂ ∎


case-duality : ∀ mc nf1 -> ⟦ case-Ex-| nf1 mc ⟧₂ ≈ ⟦ case-| mc nf1 ⟧₂ • Ex
case-duality mc nf1 = begin
  ⟦ case-Ex-| nf1 mc ⟧₂ ≈⟨ sym (case-duality' mc nf1) ⟩
  Ex • dual ⟦ case-| mc nf1 ⟧₂ ≈⟨ cright lemma-Ex-dual ⟦ case-| mc nf1 ⟧₂ ⟩
  Ex • Ex • ⟦ case-| mc nf1 ⟧₂ • Ex ≈⟨ sym assoc ⟩
  (Ex • Ex) • ⟦ case-| mc nf1 ⟧₂ • Ex ≈⟨ cleft lemma-order-Ex ⟩
  ε • ⟦ case-| mc nf1 ⟧₂ • Ex ≈⟨ left-unit ⟩
  ⟦ case-| mc nf1 ⟧₂ • Ex ∎

lemma-Ex-M' : ∀ m -> Ex • M m ↑ ≈ M m • Ex
lemma-Ex-M' m = by-duality' (lemma-Ex-M m) aux1 aux2
  where
  aux1 : dual (Ex • M m) ≈ Ex • M m ↑
  aux1 = cong aux-dual-Ex (refl' (aux-dual-Mx m))
  aux2 : dual (M m ↑ • Ex) ≈ M m • Ex
  aux2 = cong (refl' (aux-dual-Mx↑ m)) aux-dual-Ex

lemma-Ex-S^ᵏ↑ : ∀ k ->

  Ex • S^ k ↑ ≈ S^ k • Ex

lemma-Ex-S^ᵏ↑ k = by-duality' (lemma-Ex-S^ᵏ k) aux1 aux2
  where
  aux1 : dual (Ex • S^ k) ≈ Ex • S^ k ↑
  aux1 = cong aux-dual-Ex (refl' (aux-dual-S^k (toℕ k)))
  aux2 : dual (S^ k ↑ • Ex) ≈ S^ k • Ex
  aux2 = cong (refl' (aux-dual-S^k↑ (toℕ k))) aux-dual-Ex



lemma-Ex-C : ∀ c -> Ex • ⟦ c ⟧ₕₛ ≈ ⟦ c ⟧ₕₛ ↑ • Ex
lemma-Ex-C c@ε = trans right-unit (sym left-unit)
lemma-Ex-C c@(HS^ k) = begin
  Ex • ⟦ c ⟧ₕₛ ≈⟨ sym assoc ⟩
  (Ex • H) • S^ k ≈⟨ cleft sym lemma-comm-Ex-H  ⟩
  (H ↑ • Ex) • S^ k ≈⟨ assoc ⟩
  H ↑ • Ex • S^ k ≈⟨ cright lemma-Ex-S^ᵏ k ⟩
  H ↑ • S^ k ↑ • Ex ≈⟨ sym assoc ⟩
  ⟦ c ⟧ₕₛ ↑ • Ex ∎

lemma-Ex-C↑ : ∀ c -> Ex • ⟦ c ⟧ₕₛ ↑ ≈ ⟦ c ⟧ₕₛ • Ex
lemma-Ex-C↑ c@ε = trans right-unit (sym left-unit)
lemma-Ex-C↑ c@(HS^ k) = begin
  Ex • ⟦ c ⟧ₕₛ ↑ ≈⟨ sym assoc ⟩
  (Ex • H ↑) • S^ k ↑ ≈⟨ cleft sym lemma-comm-Ex-H↑  ⟩
  (H • Ex) • S^ k ↑ ≈⟨ assoc ⟩
  H • Ex • S^ k ↑ ≈⟨ cright lemma-Ex-S^ᵏ↑ k ⟩
  H • S^ k • Ex ≈⟨ sym assoc ⟩
  ⟦ c ⟧ₕₛ • Ex ∎




lemma-Ex-MC : ∀ mc -> Ex • ⟦ mc ⟧ₘ₊ ≈ ⟦ mc ⟧ₘ₊ ↑ • Ex
lemma-Ex-MC mc@(m , c) = begin
  Ex • ⟦ mc ⟧ₘ₊ ≈⟨ sym assoc ⟩
  (Ex • ⟦ m ⟧ₘ) • ⟦ c ⟧ₕₛ ≈⟨ cleft lemma-Ex-M m ⟩
  (⟦ m ⟧ₘ ↑ • Ex) • ⟦ c ⟧ₕₛ ≈⟨ assoc ⟩
  ⟦ m ⟧ₘ ↑ • Ex • ⟦ c ⟧ₕₛ ≈⟨ cright lemma-Ex-C c ⟩
  ⟦ m ⟧ₘ ↑ • ⟦ c ⟧ₕₛ ↑ • Ex ≈⟨ sym assoc ⟩
  ⟦ mc ⟧ₘ₊ ↑ • Ex ∎



lemma-Ex-MC↑ : ∀ mc -> Ex • ⟦ mc ⟧ₘ₊ ↑ ≈ ⟦ mc ⟧ₘ₊ • Ex
lemma-Ex-MC↑ mc@(m , c) = begin
  Ex • ⟦ mc ⟧ₘ₊ ↑ ≈⟨ sym assoc ⟩
  (Ex • ⟦ m ⟧ₘ ↑) • ⟦ c ⟧ₕₛ ↑ ≈⟨ cleft lemma-Ex-M' m ⟩
  (⟦ m ⟧ₘ • Ex) • ⟦ c ⟧ₕₛ ↑ ≈⟨ assoc ⟩
  ⟦ m ⟧ₘ • Ex • ⟦ c ⟧ₕₛ ↑ ≈⟨ cright lemma-Ex-C↑ c ⟩
  ⟦ m ⟧ₘ • ⟦ c ⟧ₕₛ • Ex ≈⟨ sym assoc ⟩
  ⟦ mc ⟧ₘ₊ • Ex ∎


lemma-Ex-SMC : ∀ nf1 -> ⟦ case-Ex-nf1 nf1 ⟧₂ ≈ ⟦ case-nf1 nf1 ⟧₂ • Ex
lemma-Ex-SMC nf1@(s , mc) = begin
  ⟦ case-Ex-nf1 nf1 ⟧₂ ≈⟨ sym assoc ⟩
  (Ex • S^ s ↑) • ⟦ mc ⟧ₘ₊ ↑ ≈⟨ cleft lemma-Ex-S^ᵏ↑ s ⟩
  (S^ s • Ex) • ⟦ mc ⟧ₘ₊ ↑ ≈⟨ assoc ⟩
  S^ s • Ex • ⟦ mc ⟧ₘ₊ ↑ ≈⟨ cright lemma-Ex-MC↑ mc ⟩
  S^ s • ⟦ mc ⟧ₘ₊ • Ex ≈⟨ sym assoc ⟩
  ⟦ case-nf1 nf1 ⟧₂ • Ex ∎

aux-hEx'' : CZ • H • H ↑ • CZ ≈ H ↑ • H • CZ⁻¹ • H ↑ • H • Ex
aux-hEx'' = begin
  CZ • H • H ↑ • CZ ≈⟨ aux-hEx' ⟩
  H ↑ ^ 3 • H ^ 3 • CZ⁻¹ • H ↑ ^ 3 • H ^ 3 • Ex ≈⟨ cright cright cleft refl' (Eq.cong (CZ ^_) (Eq.sym lemma-toℕ-ₚ₋₁)) ⟩
  H ↑ ^ 3 • H ^ 3 • CZ^ ₋₁ • H ↑ ^ 3 • H ^ 3 • Ex ≈⟨ special-assoc (□ • □ ^ 3 • □ ^ 4) (□ • □ • (□ ^ 2 • □) • □ ^ 3) auto ⟩
  H ↑ ^ 3 • H • (HH • CZ^ ₋₁) • H ↑ ^ 3 • H ^ 3 • Ex ≈⟨ cright cright cleft sym lemma-semi-CZ-HH↓ ⟩
  H ↑ ^ 3 • H • (CZ^ ₁ • HH) • H ↑ ^ 3 • H ^ 3 • Ex ≈⟨ special-assoc (□ • □ • □ ^ 2 • □ ^ 3) (□ ^ 3 • □ ^ 4) auto ⟩
  (H ↑ ^ 3 • H • CZ^ ₁) • HH • H ↑ ^ 3 • H ^ 3 • Ex ≈⟨ cright rewrite-sym0 100 auto ⟩
  (H ↑ ^ 3 • H • CZ^ ₁) • HH ↑ • H ↑ • H • Ex ≈⟨ special-assoc (□ ^ 3 • □ ^ 4) (□ ^ 2 • □ ^ 2 • □ ^ 3) auto ⟩
  (H ↑ ^ 3 • H) • (CZ^ ₁ • HH ↑) • H ↑ • H • Ex ≈⟨ cright cleft lemma-semi-CZ-HH↑ ⟩
  (H ↑ ^ 3 • H) • (HH ↑ • CZ^ ₋₁) • H ↑ • H • Ex ≈⟨ special-assoc (□ ^ 2 • □ ^ 2 • □ ^ 3) (□ ^ 3 • □ ^ 4) auto ⟩
  (H ↑ ^ 3 • H • HH ↑) • CZ^ ₋₁ • H ↑ • H • Ex ≈⟨ cleft rewrite-sym0 100 auto ⟩
  (H ↑ • H) • CZ^ ₚ₋₁ • H ↑ • H • Ex ≈⟨ cright cleft refl' (Eq.cong (CZ ^_) ( lemma-toℕ-ₚ₋₁)) ⟩
  (H ↑ • H) • CZ⁻¹ • H ↑ • H • Ex ≈⟨ assoc ⟩
  H ↑ • H • CZ⁻¹ • H ↑ • H • Ex ∎


aux-hEx''' : CZ • H • H ↑ • CZ ≈ Ex • H • H ↑ • CZ⁻¹ • H • H ↑
aux-hEx''' = begin
  CZ • H • H ↑ • CZ ≈⟨ aux-hEx'' ⟩
  H ↑ • H • CZ⁻¹ • H ↑ • H • Ex ≈⟨ sym (lemma-Ex-dual' (H ↑ • H • CZ⁻¹ • H ↑ • H • Ex)) ⟩
  Ex • dual (H ↑ • H • CZ⁻¹ • H ↑ • H • Ex) • Ex ≈⟨ cright cleft (cright cright cong (refl' (aux-dual-CZ^k p-1)) (cright cright aux-dual-Ex)) ⟩
  Ex • (H • H ↑ • CZ⁻¹ • H • H ↑ • Ex) • Ex ≈⟨ special-assoc (□ • □ ^ 6 • □) (□ ^ 6 • □ ^ 2) auto ⟩
  (Ex • H • H ↑ • CZ⁻¹ • H • H ↑) • Ex • Ex ≈⟨ cright lemma-order-Ex ⟩
  (Ex • H • H ↑ • CZ⁻¹ • H • H ↑) • ε ≈⟨ right-unit ⟩
  Ex • H • H ↑ • CZ⁻¹ • H • H ↑ ∎



