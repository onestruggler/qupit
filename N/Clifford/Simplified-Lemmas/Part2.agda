{-# OPTIONS --termination-depth=20 #-}
{-# OPTIONS --inversion-max-depth=1000 #-}

open import Level using (0ℓ)
open import Relation.Binary.PropositionalEquality using (_≡_ ; _≢_ ; module ≡-Reasoning) renaming ([_] to [_]')
import Relation.Binary.Reasoning.Setoid as SR
import Relation.Binary.PropositionalEquality as Eq
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂ ; ∃)
open import Data.Nat hiding (_^_ ; _+_ ; _*_ ; _%_ ; _/_)
import Data.Nat as Nat
open import Data.Fin hiding (_+_ ; _-_)
open import Word.Base as WB hiding (wfoldl ; _* ; _^'_)
import Presentation.Base as PB
import Presentation.Properties as PP
open import Presentation.Construct.Base hiding (_*_)
open import Presentation.GroupLike
open import Presentation.Tactics
import Data.Nat.Properties as NP
open import Data.Nat.DivMod
open import Data.Fin.Properties using (toℕ-inject₁ ; toℕ-fromℕ ; toℕ-fromℕ<)
open import Data.Nat.Primality
open import Zp.ModularArithmetic
open import Zp.Fermats-little-theorem
open import Notations

module N.Clifford.Simplified-Lemmas.Part2
  (p-3 : ℕ)
  (let p-2 = ₁₊ p-3)
  (p-prime : Prime (suc (₁₊ p-2)))
  (let open PrimeModulus' p-2 p-prime)
  (g*@(g , g≠0) : ℤ* ₚ)
  (g-gen : ∀ ((x , _) : ℤ* ₚ) -> ∃ \ (k : ℤ ₚ-₁) -> x ≡ g ^′ toℕ k )
  where


open Primitive-Root-Modp' g* g-gen

open import N.Clifford.Clifford-Mod-Scalar p-3 p-prime g* g-gen
open Clifford-Relations hiding
  ( _QRel,_===_ ; order-S ; order-H ; M-power ; semi-M𝑠 ; order-SH ; comm-HHSHHS
  ; comm-X-Z ; semi-M↑CZ ; semi-M↓CZ ; rel-X↑-CZ ; rel-X↓-CZ ; order-CZ
  ; comm-CZ-S↓ ; comm-CZ-S↑ ; selinger-c10 ; selinger-c11 ; selinger-c12
  ; selinger-c13 ; selinger-c14 ; selinger-c15 ; comm-H ; comm-S ; comm-CZ ; cong↑ )
open import N.Clifford.Clifford-Mod-Scalars-Simplified p-3 p-prime g* g-gen
open Simplified-Relations
open import N.Clifford.Simplified-Lemmas.Part1 p-3 p-prime g* g-gen public

-- Lemmas-Clifford-S : copy of Clifford-Mod-Scalar.Lemmas-Clifford
-- (lemma-cong↑, lemma-↑^, lemma-Induction, lemma-comm-*-w↑, …)
-- ====================================================================
module Lemmas-Clifford-S where

  lemma-cong↑ : ∀ {n} w v →
    let open PB (n QRel,_===_) using (_≈_) in
    let open PB ((₁₊ n) QRel,_===_) renaming (_≈_ to _≈↑_) using () in
    w ≈ v → w ↑ ≈↑ v ↑
  lemma-cong↑ {n} w v PB.refl = PB.refl
  lemma-cong↑ {n} w v (PB.sym eq) = PB.sym (lemma-cong↑ v w eq)
  lemma-cong↑ {n} w v (PB.trans eq eq₁) = PB.trans (lemma-cong↑ _ _ eq) (lemma-cong↑ _ _ eq₁)
  lemma-cong↑ {n} w v (PB.cong eq eq₁) = PB.cong (lemma-cong↑ _ _ eq) (lemma-cong↑ _ _ eq₁)
  lemma-cong↑ {n} w v PB.assoc = PB.assoc
  lemma-cong↑ {n} w v PB.left-unit = PB.left-unit
  lemma-cong↑ {n} w v PB.right-unit = PB.right-unit
  lemma-cong↑ {n} w v (PB.axiom x) = PB.axiom (cong↑ x)


  lemma-^-↑ : ∀ {n} (w : Word (Gen n)) k → w ↑ ^ k ≡ (w ^ k) ↑
  lemma-^-↑ w ₀ = auto
  lemma-^-↑ w ₁ = auto
  lemma-^-↑ w (₂₊ k) = begin
    (w ↑) • (w ↑) ^ ₁₊ k ≡⟨ Eq.cong ((w ↑) •_) (lemma-^-↑ w (₁₊ k)) ⟩
    (w ↑) • (w ^ ₁₊ k) ↑ ≡⟨ auto ⟩
    ((w • w ^ ₁₊ k) ↑) ∎
    where open ≡-Reasoning


  lemma-cong↓-S^ : ∀ {n} k -> let open PB ((₂₊ n) QRel,_===_) renaming (_≈_ to _≈↓_) using () in
    (S ^ k) ↓ ≈↓ S ^ k
  lemma-cong↓-S^ {n} ₀ = PB.refl
  lemma-cong↓-S^ {n} ₁ = PB.refl
  lemma-cong↓-S^ {n} (₂₊ k) = PB.cong PB.refl (lemma-cong↓-S^ {n} (₁₊ k))

  lemma-cong↑-S^ : ∀ {n} k -> let open PB ((₂₊ n) QRel,_===_) renaming (_≈_ to _≈↑_) using () in
    (S ^ k) ↑ ≈↑ S ↑ ^ k
  lemma-cong↑-S^ {n} ₀ = PB.refl
  lemma-cong↑-S^ {n} ₁ = PB.refl
  lemma-cong↑-S^ {n} (₂₊ k) = PB.cong PB.refl (lemma-cong↑-S^ {n} (₁₊ k))


  lemma-cong↓-S↓^ : ∀ {n} k -> let open PB ((₃₊ n) QRel,_===_) renaming (_≈_ to _≈↓_) using () in
    (S ↓ ^ k) ↓ ≈↓ S ↓ ^ k
  lemma-cong↓-S↓^ {n} ₀ = PB.refl
  lemma-cong↓-S↓^ {n} ₁ = PB.refl
  lemma-cong↓-S↓^ {n} (₂₊ k) = PB.cong PB.refl (lemma-cong↓-S↓^ {n} (₁₊ k))

  lemma-cong↓-S↑^ : ∀ {n} k -> let open PB ((₃₊ n) QRel,_===_) renaming (_≈_ to _≈↓_) using () in
    ((S ↑) ^ k) ↓ ≈↓ (S ↑) ^ k
  lemma-cong↓-S↑^ {n} ₀ = PB.refl
  lemma-cong↓-S↑^ {n} ₁ = PB.refl
  lemma-cong↓-S↑^ {n} (₂₊ k) = PB.cong PB.refl (lemma-cong↓-S↑^ {n} (₁₊ k))


  lemma-cong↓-S^↓ : ∀ {n} k -> let open PB ((₃₊ n) QRel,_===_) renaming (_≈_ to _≈↓_) using () in
    (S ^ k) ↓ ↓ ≈↓ (S ^ k) ↓
  lemma-cong↓-S^↓ {n} ₀ = PB.refl
  lemma-cong↓-S^↓ {n} ₁ = PB.refl
  lemma-cong↓-S^↓ {n} (₂₊ k) = PB.cong PB.refl (lemma-cong↓-S^↓ {n} (₁₊ k))

  lemma-cong↓-S^↑ : ∀ {n} k -> let open PB ((₃₊ n) QRel,_===_) renaming (_≈_ to _≈↓_) using () in
    (S ^ k) ↑ ↓ ≈↓ (S ^ k) ↑
  lemma-cong↓-S^↑ {n} ₀ = PB.refl
  lemma-cong↓-S^↑ {n} ₁ = PB.refl
  lemma-cong↓-S^↑ {n} (₂₊ k) = PB.cong PB.refl (lemma-cong↓-S^↑ {n} (₁₊ k))

  lemma-cong↓-H^ : ∀ {n} k -> let open PB ((₂₊ n) QRel,_===_) renaming (_≈_ to _≈↓_) using () in
    (H ^ k) ↓ ≈↓ H ^ k
  lemma-cong↓-H^ {n} ₀ = PB.refl
  lemma-cong↓-H^ {n} ₁ = PB.refl
  lemma-cong↓-H^ {n} (₂₊ k) = PB.cong PB.refl (lemma-cong↓-H^ {n} (₁₊ k))

  lemma-cong↓-CZ^ : ∀ {n} k -> let open PB ((₃₊ n) QRel,_===_) renaming (_≈_ to _≈↓_) using () in
    (CZ ^ k) ↓ ≈↓ CZ ^ k
  lemma-cong↓-CZ^ {n} ₀ = PB.refl
  lemma-cong↓-CZ^ {n} ₁ = PB.refl
  lemma-cong↓-CZ^ {n} (₂₊ k) = PB.cong PB.refl (lemma-cong↓-CZ^ {n} (₁₊ k))

  lemma-↑↓ : ∀ {n} (w : Word (Gen n)) → w ↑ ↓ ≡ w ↓ ↑
  lemma-↑↓ [ x ]ʷ = auto
  lemma-↑↓ ε = auto
  lemma-↑↓ (w • w₁) = Eq.cong₂ _•_ (lemma-↑↓ w) (lemma-↑↓ w₁)

  lemma-↑^ : ∀ {n} k (w : Word (Gen n)) → (w ^ k) ↑ ≡ w ↑ ^ k
  lemma-↑^ {n} ₀ w = auto
  lemma-↑^ {n} ₁ w = auto
  lemma-↑^ {n} (₂₊ k) w = Eq.cong₂ _•_ auto (lemma-↑^ {n} (₁₊ k) w)


  lemma-↓^ : ∀ {n} k (w : Word (Gen n)) → (w ^ k) ↓ ≡ w ↓ ^ k
  lemma-↓^ {n} ₀ w = auto
  lemma-↓^ {n} ₁ w = auto
  lemma-↓^ {n} (₂₊ k) w = Eq.cong₂ _•_ auto (lemma-↓^ {n} (₁₊ k) w)


  lemma-comm-S-w↑ : ∀ {n} w → let open PB ((₂₊ n) QRel,_===_) in
    
    S • w ↑ ≈ w ↑ • S
    
  lemma-comm-S-w↑ {n} [ x ]ʷ = sym (axiom comm-S)
    where
    open PB ((₂₊ n) QRel,_===_)
  lemma-comm-S-w↑ {n} ε = trans right-unit (sym left-unit)
    where
    open PB ((₂₊ n) QRel,_===_)
  lemma-comm-S-w↑ {n} (w • w₁) = begin
    S • ((w • w₁) ↑) ≈⟨ refl ⟩
    S • (w ↑ • w₁ ↑) ≈⟨ sym assoc ⟩
    (S • w ↑) • w₁ ↑ ≈⟨ cong (lemma-comm-S-w↑ w) refl ⟩
    (w ↑ • S) • w₁ ↑ ≈⟨ assoc ⟩
    w ↑ • S • w₁ ↑ ≈⟨ cong refl (lemma-comm-S-w↑ w₁) ⟩
    w ↑ • w₁ ↑ • S ≈⟨ sym assoc ⟩
    ((w • w₁) ↑) • S ∎
    where
    open PB ((₂₊ n) QRel,_===_)
    open PP ((₂₊ n) QRel,_===_)
    open SR word-setoid

  lemma-comm-Sᵏ-w↑ : ∀ {n} k w → let open PB ((₂₊ n) QRel,_===_) in
    
    S ^ k • w ↑ ≈ w ↑ • S ^ k
    
  lemma-comm-Sᵏ-w↑ {n} ₀ w = trans left-unit (sym right-unit)
    where
    open PB ((₂₊ n) QRel,_===_)
  lemma-comm-Sᵏ-w↑ {n} ₁ w = lemma-comm-S-w↑ w
    where
    open PB ((₂₊ n) QRel,_===_)
  lemma-comm-Sᵏ-w↑ {n} (₂₊ k) w = begin
    (S • S ^ ₁₊ k) • (w ↑) ≈⟨ assoc ⟩
    S • S ^ ₁₊ k • (w ↑) ≈⟨ cong refl (lemma-comm-Sᵏ-w↑ (₁₊ k) w) ⟩
    S • (w ↑) • S ^ ₁₊ k ≈⟨ sym assoc ⟩
    (S • w ↑) • S ^ ₁₊ k ≈⟨ cong (lemma-comm-S-w↑ w) refl ⟩
    (w ↑ • S) • S ^ ₁₊ k ≈⟨ assoc ⟩
    (w ↑) • S • S ^ ₁₊ k ∎
    where
    open PB ((₂₊ n) QRel,_===_)
    open PP ((₂₊ n) QRel,_===_)
    open SR word-setoid


  lemma-comm-H-w↑ : ∀ {n} w → let open PB ((₂₊ n) QRel,_===_) in
    
    H • w ↑ ≈ w ↑ • H
    
  lemma-comm-H-w↑ {n} [ x ]ʷ = sym (axiom comm-H)
    where
    open PB ((₂₊ n) QRel,_===_)
  lemma-comm-H-w↑ {n} ε = trans right-unit (sym left-unit)
    where
    open PB ((₂₊ n) QRel,_===_)
  lemma-comm-H-w↑ {n} (w • w₁) = begin
    H • ((w • w₁) ↑) ≈⟨ refl ⟩
    H • (w ↑ • w₁ ↑) ≈⟨ sym assoc ⟩
    (H • w ↑) • w₁ ↑ ≈⟨ cong (lemma-comm-H-w↑ w) refl ⟩
    (w ↑ • H) • w₁ ↑ ≈⟨ assoc ⟩
    w ↑ • H • w₁ ↑ ≈⟨ cong refl (lemma-comm-H-w↑ w₁) ⟩
    w ↑ • w₁ ↑ • H ≈⟨ sym assoc ⟩
    ((w • w₁) ↑) • H ∎
    where
    open PB ((₂₊ n) QRel,_===_)
    open PP ((₂₊ n) QRel,_===_)
    open SR word-setoid



  lemma-comm-Hᵏ-w↑ : ∀ {n} k w → let open PB ((₂₊ n) QRel,_===_) in
    
    H ^ k • w ↑ ≈ w ↑ • H ^ k
    
  lemma-comm-Hᵏ-w↑ {n} ₀ w = trans left-unit (sym right-unit)
    where
    open PB ((₂₊ n) QRel,_===_)
  lemma-comm-Hᵏ-w↑ {n} ₁ w = lemma-comm-H-w↑ w
    where
    open PB ((₂₊ n) QRel,_===_)
  lemma-comm-Hᵏ-w↑ {n} (₂₊ k) w = begin
    (H • H ^ ₁₊ k) • (w ↑) ≈⟨ assoc ⟩
    H • H ^ ₁₊ k • (w ↑) ≈⟨ cong refl (lemma-comm-Hᵏ-w↑ (₁₊ k) w) ⟩
    H • (w ↑) • H ^ ₁₊ k ≈⟨ sym assoc ⟩
    (H • w ↑) • H ^ ₁₊ k ≈⟨ cong (lemma-comm-H-w↑ w) refl ⟩
    (w ↑ • H) • H ^ ₁₊ k ≈⟨ assoc ⟩
    (w ↑) • H • H ^ ₁₊ k ∎
    where
    open PB ((₂₊ n) QRel,_===_)
    open PP ((₂₊ n) QRel,_===_)
    open SR word-setoid


  lemma-comm-Z-w↑ : ∀ {n} w → let open PB ((₂₊ n) QRel,_===_) in
    
    Z • w ↑ ≈ w ↑ • Z
    
  lemma-comm-Z-w↑ {n} w = begin
    (H • H • S • H • H • S⁻¹) • w ↑ ≈⟨ by-assoc auto ⟩
    (H • H • S • H • H) • S⁻¹ • w ↑ ≈⟨ (cright lemma-comm-Sᵏ-w↑ p-1 w) ⟩
    (H • H • S • H • H) • w ↑ • S⁻¹ ≈⟨ by-assoc auto ⟩
    (H • H • S) • (H ^ 2 • w ↑) • S⁻¹ ≈⟨ (cright cleft lemma-comm-Hᵏ-w↑ 2 w) ⟩
    (H • H • S) • (w ↑ • H ^ 2) • S⁻¹ ≈⟨ special-assoc (□ ^ 3 • □ ^ 2 • □) (□ ^ 2 • □ ^ 2 • □ ^ 2) auto ⟩
    H ^ 2 • (S • w ↑) • H ^ 2 • S⁻¹ ≈⟨ (cright cleft lemma-comm-Sᵏ-w↑ 1 w) ⟩
    H ^ 2 • (w ↑ • S) • H ^ 2 • S⁻¹ ≈⟨ trans (by-assoc auto) assoc ⟩
    (H ^ 2 • w ↑) • S • H ^ 2 • S⁻¹ ≈⟨ (cleft lemma-comm-Hᵏ-w↑ 2 w) ⟩
    (w ↑ • H ^ 2) • S • H ^ 2 • S⁻¹ ≈⟨ special-assoc (□ ^ 3 • □ • □ ^ 2 • □) (□ • □ ^ 6 ) auto ⟩
    w ↑ • Z ∎
    where
    open PB ((₂₊ n) QRel,_===_)
    open PP ((₂₊ n) QRel,_===_)
    open SR word-setoid
    open Pattern-Assoc


  lemma-comm-X-w↑ : ∀ {n} w → let open PB ((₂₊ n) QRel,_===_) in
    
    X • w ↑ ≈ w ↑ • X
    
  lemma-comm-X-w↑ {n} w = begin
    (H • S • H • H • S⁻¹ • H) • w ↑ ≈⟨ special-assoc (□ ^ 6 • □) (□ ^ 5 • □ ^ 2) auto ⟩
    (H • S • H • H • S⁻¹) • H • w ↑ ≈⟨ (cright lemma-comm-Hᵏ-w↑ 1 w) ⟩
    (H • S • H • H • S⁻¹) • w ↑ • H ≈⟨ special-assoc (□ ^ 5 • □ ^ 2) (□ ^ 4 • □ ^ 2 • □) auto ⟩
    (H • S • H • H) • (S⁻¹ • w ↑) • H ≈⟨ (cright cleft lemma-comm-Sᵏ-w↑ p-1 w) ⟩
    (H • S • H • H) • (w ↑ • S⁻¹) • H ≈⟨ special-assoc (□ ^ 4 • □ ^ 2 • □) (□ ^ 2 • (□ ^ 2 • □) • □ ^ 2) auto ⟩
    (H • S) • (H ^ 2 • w ↑) • S⁻¹ • H ≈⟨ (cright cleft lemma-comm-Hᵏ-w↑ 2 w) ⟩
    (H • S) • (w ↑ • H ^ 2) • S⁻¹ • H ≈⟨ special-assoc (□ ^ 2 • □ ^ 2 • □ ^ 2) (□ • □ ^ 2 • □ • □ ^ 2) auto ⟩
    H • (S • w ↑) • H ^ 2 • S⁻¹ • H ≈⟨ (cright cleft lemma-comm-Sᵏ-w↑ 1 w) ⟩
    H • (w ↑ • S) • H ^ 2 • S⁻¹ • H ≈⟨ trans (by-assoc auto) assoc ⟩
    (H • w ↑) • S • H ^ 2 • S⁻¹ • H ≈⟨ (cleft lemma-comm-Hᵏ-w↑ 1 w) ⟩
    (w ↑ • H) • S • H ^ 2 • S⁻¹ • H ≈⟨ special-assoc (□ ^ 2 • □ • □ ^ 2 • □ ^ 2) (□ • □ ^ 6) auto ⟩
    w ↑ • X ∎
    where
    open PB ((₂₊ n) QRel,_===_)
    open PP ((₂₊ n) QRel,_===_)
    open SR word-setoid
    open Pattern-Assoc



  lemma-comm-CZ-w↑ : ∀ {n} w → let open PB ((₃₊ n) QRel,_===_) in
    
    CZ • w ↑ ↑ ≈ w ↑ ↑ • CZ
    
  lemma-comm-CZ-w↑ {n} [ x ]ʷ = sym (axiom comm-CZ)
    where
    open PB ((₃₊ n) QRel,_===_)
  lemma-comm-CZ-w↑ {n} ε = trans right-unit (sym left-unit)
    where
    open PB ((₃₊ n) QRel,_===_)
  lemma-comm-CZ-w↑ {n} (w • w₁) = begin
    CZ • ((w • w₁) ↑ ↑) ≈⟨ refl ⟩
    CZ • (w ↑ ↑ • w₁ ↑ ↑) ≈⟨ sym assoc ⟩
    (CZ • w ↑ ↑) • w₁ ↑ ↑ ≈⟨ cong (lemma-comm-CZ-w↑ w) refl ⟩
    (w ↑ ↑ • CZ) • w₁ ↑ ↑ ≈⟨ assoc ⟩
    w ↑ ↑ • CZ • w₁ ↑ ↑ ≈⟨ cong refl (lemma-comm-CZ-w↑ w₁) ⟩
    w ↑ ↑ • w₁ ↑ ↑ • CZ ≈⟨ sym assoc ⟩
    ((w • w₁) ↑ ↑) • CZ ∎
    where
    open PB ((₃₊ n) QRel,_===_)
    open PP ((₃₊ n) QRel,_===_)
    open SR word-setoid

  aux-MM : ∀ {n} -> let open PB ((₁₊ n) QRel,_===_) in ∀ {x y : ℤ ₚ} (nzx : x ≢ ₀) (nzy : y ≢ ₀) -> x ≡ y -> M (x , nzx) ≈ M (y , nzy)
  aux-MM {n} {x} {y} nz1 nz2 eq rewrite eq = refl
    where
    open PB ((₁₊ n) QRel,_===_)



  lemma-Induction : ∀ {n} -> let open PB ((₁₊ n) QRel,_===_) in ∀ {w v v'} -> w • v ≈ v' • w -> ∀ k -> w • v ^ k ≈ v' ^ k • w
  lemma-Induction {n} {w} {v} {v'} eq k@0 = trans right-unit (sym left-unit)
    where open PB ((₁₊ n) QRel,_===_)
  lemma-Induction {n} {w} {v} {v'} eq k@1 = eq
  lemma-Induction {n} {w} {v} {v'} eq k@(₂₊ k') = begin
    w • v ^ k ≈⟨ sym assoc ⟩
    (w • v) • v ^ (₁₊ k') ≈⟨ (cleft eq) ⟩
    (v' • w) • v ^ (₁₊ k') ≈⟨ assoc ⟩
    v' • w • v ^ (₁₊ k') ≈⟨ (cright lemma-Induction eq (₁₊ k')) ⟩
    v' • v' ^ (₁₊ k') • w ≈⟨ sym assoc ⟩
    v' ^ k • w ∎
    where
    open PP ((₁₊ n) QRel,_===_)
    open PB ((₁₊ n) QRel,_===_)
    open SR word-setoid


  lemma-Inductionˡ : ∀ {n} -> let open PB ((₁₊ n) QRel,_===_) in ∀ {w w' v} -> w • v ≈ v • w' -> ∀ k -> w ^ k • v ≈ v • w' ^ k
  lemma-Inductionˡ {n} {w} {w'} {v} eq k@0 = trans left-unit (sym right-unit)
    where open PB ((₁₊ n) QRel,_===_)
  lemma-Inductionˡ {n} {w} {w'} {v} eq k@1 = eq
  lemma-Inductionˡ {n} {w} {w'} {v} eq k@(₁₊ k'@(₁₊ k'')) = begin
    w ^ k • v ≈⟨ assoc ⟩
    w • w ^ k' • v ≈⟨ (cright lemma-Inductionˡ eq k') ⟩
    w • v • w' ^ k' ≈⟨ sym assoc ⟩
    (w • v) • w' ^ k' ≈⟨ (cleft eq) ⟩
    (v • w') • w' ^ k' ≈⟨ assoc ⟩
    v • w' ^ k ∎
    where
    open PP ((₁₊ n) QRel,_===_)
    open PB ((₁₊ n) QRel,_===_)
    open SR word-setoid


-- ====================================================================
-- Simplified-GroupLike-S : copy of Clifford-GroupLike for Simplified.
-- ====================================================================
module Simplified-GroupLike-S where

  private
    variable
      n : ℕ

  open Lemmas-Clifford-S

  grouplike : Grouplike (n QRel,_===_)
  grouplike {₁₊ n} (H-gen) = (H ) ^ 3 , claim
    where
    open PB ((₁₊ n) QRel,_===_)
    open PP ((₁₊ n) QRel,_===_)
    open SR word-setoid
    open Lemmas1-S n
    claim : (H ) ^ 3 • H ≈ ε
    claim = begin
      (H) ^ 3 • H ≈⟨ by-assoc auto ⟩
      (H) ^ 4 ≈⟨ lemma-order-H ⟩
      ε ∎

  grouplike {₁₊ n} (S-gen) = (S) ^ p-1 ,  claim
    where
    open PB ((₁₊ n) QRel,_===_)
    open PP ((₁₊ n) QRel,_===_)
    open SR word-setoid
    claim : (S) ^ p-1 • S ≈ ε
    claim = begin
      (S) ^ p-1 • S ≈⟨ sym (lemma-^-+ (S) p-1 1) ⟩
      (S) ^ (p-1 Nat.+ 1) ≡⟨ Eq.cong (S ^_) ( NP.+-comm p-1 1) ⟩
      (S ^ p) ≈⟨ (axiom order-S) ⟩
      (ε) ∎

  grouplike {₂₊ n} (CZ-gen) = (CZ) ^ p-1 ,  claim
    where
    open PB ((₂₊ n) QRel,_===_)
    open PP ((₂₊ n) QRel,_===_)
    open SR word-setoid
    claim : (CZ) ^ p-1 • CZ ≈ ε
    claim = begin
      (CZ) ^ p-1 • CZ ≈⟨ sym (lemma-^-+ (CZ) p-1 1) ⟩
      (CZ) ^ (p-1 Nat.+ 1) ≡⟨ Eq.cong (CZ ^_) ( NP.+-comm p-1 1) ⟩
      (CZ ^ p) ≈⟨ (axiom order-CZ) ⟩
      (ε) ∎

  grouplike {₂₊ n} (g ↥) with grouplike g
  ... | ig , prf = (ig ↑) , lemma-cong↑ (ig • [ g ]ʷ) ε prf
    where
    open PB ((₂₊ n) QRel,_===_)
    open PP ((₂₊ n) QRel,_===_)



-- ----------------------------------------------------------------------
-- * Data required for applying word tactics to Symplectic generators


module Lemmas1b-S (n : ℕ) where


  open Lemmas-Clifford-S
  open Lemmas1-S n

  open PB ((₁₊ n) QRel,_===_) hiding (_===_)
  open PP ((₁₊ n) QRel,_===_)
  open SR word-setoid
  open Pattern-Assoc
  open Simplified-GroupLike-S
  open import Data.Nat.DivMod
  open import Data.Fin.Properties


  aux-S⁻¹⁻¹ : 
    S⁻¹ ^ p-1 ≈ S
  aux-S⁻¹⁻¹ = lemma-right-cancel {h = S⁻¹} aux00
    where
    open Basis-Change _ ((₁₊ n) QRel,_===_) grouplike
    open Group-Lemmas _ ((₁₊ n) QRel,_===_) grouplike renaming (_⁻¹ to _⁻¹′)
    aux00 : S⁻¹ ^ p-1 • S⁻¹ ≈ S • S⁻¹
    aux00 = begin
      S⁻¹ ^ p-1 • S⁻¹ ≈⟨ word-comm p-1 1 refl ⟩
      S⁻¹ • S⁻¹ ^ p-1 ≈⟨ refl ⟩
      S⁻¹ ^ p ≈⟨ lemma-^^ S p-1 p ⟩
      S ^ (p-1 Nat.* p) ≡⟨ Eq.cong (S ^_) (NP.*-comm p-1 p) ⟩
      S ^ (p Nat.* p-1) ≈⟨ sym (lemma-^^ S p p-1) ⟩
      (S ^ p) ^ p-1 ≈⟨ lemma-^-cong (S ^ p) ε p-1 (axiom order-S) ⟩
      ε ^ p-1 ≈⟨ lemma-ε^k=ε (₁₊ p-2) ⟩
      ε ≈⟨ sym (axiom order-S) ⟩
      S • S⁻¹ ∎

  aux-Z⁻¹⁻¹ : 
    Z⁻¹ ^ p-1 ≈ Z
  aux-Z⁻¹⁻¹ = lemma-right-cancel {h = Z⁻¹} aux00
    where
    open Basis-Change _ ((₁₊ n) QRel,_===_) grouplike
    open Group-Lemmas _ ((₁₊ n) QRel,_===_) grouplike renaming (_⁻¹ to _⁻¹′)
    aux00 : Z⁻¹ ^ p-1 • Z⁻¹ ≈ Z • Z⁻¹
    aux00 = begin
      Z⁻¹ ^ p-1 • Z⁻¹ ≈⟨ word-comm p-1 1 refl ⟩
      Z⁻¹ • Z⁻¹ ^ p-1 ≈⟨ refl ⟩
      Z⁻¹ ^ p ≈⟨ lemma-^^ Z p-1 p ⟩
      Z ^ (p-1 Nat.* p) ≡⟨ Eq.cong (Z ^_) (NP.*-comm p-1 p) ⟩
      Z ^ (p Nat.* p-1) ≈⟨ sym (lemma-^^ Z p p-1) ⟩
      (Z ^ p) ^ p-1 ≈⟨ lemma-^-cong (Z ^ p) ε p-1 (lemma-order-Z) ⟩
      ε ^ p-1 ≈⟨ lemma-ε^k=ε (₁₊ p-2) ⟩
      ε ≈⟨ sym (lemma-order-Z) ⟩
      Z • Z⁻¹ ∎



  aux-X⁻¹⁻¹ : 
    X⁻¹ ^ p-1 ≈ X
  aux-X⁻¹⁻¹ = lemma-right-cancel {h = X⁻¹} aux00
    where
    open Basis-Change _ ((₁₊ n) QRel,_===_) grouplike
    open Group-Lemmas _ ((₁₊ n) QRel,_===_) grouplike renaming (_⁻¹ to _⁻¹′)
    aux00 : X⁻¹ ^ p-1 • X⁻¹ ≈ X • X⁻¹
    aux00 = begin
      X⁻¹ ^ p-1 • X⁻¹ ≈⟨ word-comm p-1 1 refl ⟩
      X⁻¹ • X⁻¹ ^ p-1 ≈⟨ refl ⟩
      X⁻¹ ^ p ≈⟨ lemma-^^ X p-1 p ⟩
      X ^ (p-1 Nat.* p) ≡⟨ Eq.cong (X ^_) (NP.*-comm p-1 p) ⟩
      X ^ (p Nat.* p-1) ≈⟨ sym (lemma-^^ X p p-1) ⟩
      (X ^ p) ^ p-1 ≈⟨ lemma-^-cong (X ^ p) ε p-1 (lemma-order-X) ⟩
      ε ^ p-1 ≈⟨ lemma-ε^k=ε (₁₊ p-2) ⟩
      ε ≈⟨ sym (lemma-order-X) ⟩
      X • X⁻¹ ∎



  conj-H-X : H • X ≈ Z • H
  conj-H-X = begin
    H • X ≈⟨ by-assoc auto ⟩
    Z • H ∎

  conj-H-X^k : ∀ k -> H • X ^ k ≈ Z ^ k • H
  conj-H-X^k k@0 = by-assoc auto
  conj-H-X^k k@1 = conj-H-X
  conj-H-X^k k@(₁₊ k'@(₁₊ k'')) = begin
    H • X ^ k ≈⟨ sym assoc ⟩
    (H • X) • X ^ k' ≈⟨ (cleft conj-H-X) ⟩
    (Z • H) • X ^ k' ≈⟨ assoc ⟩
    Z • H • X ^ k' ≈⟨ (cright conj-H-X^k k') ⟩
    Z • Z ^ k' • H ≈⟨ sym assoc ⟩
    Z ^ k • H ∎


  lemma-HH-Z : HH • Z ≈ Z^ (- ₁) • HH
  lemma-HH-Z = begin
    HH • H • H • S • H • H • S⁻¹ ≈⟨ special-assoc (□ ^ 2 • □ ^ 6) (□ • □ • □ ^ 5 • □) auto ⟩
    H • H • (H • H • S • H • H) • S⁻¹ ≈⟨ (cright cright sym (word-comm p-1 1 (lemma-comm-SHHS^kHH 1))) ⟩
    H • H • S⁻¹ • (H • H • S • H • H) ≈⟨ special-assoc (□ ^ 8) (□ ^ 6 • □ ^ 2) auto ⟩
    (H • H • S⁻¹ • H • H • S) • H • H ≈⟨ (cleft (cright cright cong (refl' (Eq.cong (S ^_) (Eq.sym lemma-toℕ-1ₚ))) (cright cright sym aux-S⁻¹⁻¹))) ⟩
    (H • H • S ^ (toℕ (- 1ₚ)) • H • H • S⁻¹ ^ p-1) • HH ≈⟨ (cleft cright cright cright cright cright refl' (Eq.cong (S⁻¹ ^_) (Eq.sym lemma-toℕ-1ₚ))) ⟩
    (H • H • S ^ (toℕ (- 1ₚ)) • H • H • S⁻¹ ^ (toℕ (- 1ₚ))) • HH ≈⟨ (cleft sym (lemma-Z^k-ℕ (toℕ (- 1ₚ)))) ⟩
    Z^ (- ₁) • HH ∎


  lemma-HH-X : HH • X ≈ X^ (- ₁) • HH
  lemma-HH-X = bbc H ε claim
    where
    open Basis-Change _ ((₁₊ n) QRel,_===_) grouplike
    claim : H • (HH • X) • ε ≈ H • (X^ (- ₁) • HH) • ε
    claim = begin
      H • (HH • X) • ε ≈⟨ cong refl right-unit ⟩
      H • (HH • X) ≈⟨ special-assoc (□ • □ ^ 2 • □) (□ ^ 2 • □ ^ 2) auto ⟩
      HH • H • X ≈⟨ (cright conj-H-X) ⟩
      HH • Z • H ≈⟨ sym assoc ⟩
      (HH • Z) • H ≈⟨ (cleft lemma-HH-Z) ⟩
      (Z^ (- ₁) • HH) • H ≈⟨ special-assoc (□ ^ 3 • □) (□ ^ 2 • □ ^ 2) auto ⟩
      (Z^ (- ₁) • H) • HH ≈⟨ (cleft sym (conj-H-X^k (toℕ (- ₁)))) ⟩
      (H • X^ (- ₁)) • HH ≈⟨ assoc ⟩
      H • (X^ (- ₁) • HH) ≈⟨ sym (cong refl right-unit) ⟩
      H • (X^ (- ₁) • HH) • ε ∎

  conj-H-Z : H • Z ≈ X^ (- ₁) • H
  conj-H-Z = bbc (H ^ 3) H claim 
    where
    open Basis-Change _ ((₁₊ n) QRel,_===_) grouplike
    claim : H ^ 3 • (H • Z) • H ≈ H ^ 3 • (X^ (- ₁) • H) • H
    claim = begin
      H ^ 3 • (H • Z) • H ≈⟨ by-assoc auto ⟩
      (H ^ 4) • Z • H ≈⟨ trans (cleft lemma-order-H) left-unit ⟩
      Z • H ≈⟨ sym conj-H-X ⟩
      H • X ≈⟨ cleft (sym (trans (cright lemma-order-H) right-unit)) ⟩
      H ^ 5 • X ≈⟨ special-assoc (□ ^ 5 • □) (□ ^ 3 • □ ^ 2 • □) auto ⟩
      H ^ 3 • HH • X ≈⟨ (cright lemma-HH-X) ⟩
      H ^ 3 • X^ (- ₁) • H • H ≈⟨ special-assoc (□ ^ 4) (□ • □ ^ 2 • □) auto ⟩
      H ^ 3 • (X^ (- ₁) • H) • H ∎


  lemma-SHSH : S • H • S • H ≈ H ^ 3 • S⁻¹
  lemma-SHSH = bbc ε (S • H) claim
    where
    open Basis-Change _ ((₁₊ n) QRel,_===_) grouplike
    open Group-Lemmas _ _ (grouplike {₁₊ n}) renaming (_⁻¹ to _⁻¹ʷ)
    
    claim : ε • (S • H • S • H) • S • H ≈ ε • (H ^ 3 • S⁻¹) • S • H
    claim = begin
      ε • (S • H • S • H) • S • H ≈⟨ left-unit ⟩
      (S • H • S • H) • S • H ≈⟨ special-assoc (□ ^ 4 • □ ^ 2) ((□ ^ 2) ^ 3) auto ⟩
      (S • H) ^ 3 ≈⟨ axiom order-SH ⟩
      ε ≈⟨ sym lemma-left-inverse ⟩
      (H ^ 3 • S⁻¹) • S • H ≈⟨ sym left-unit ⟩
      ε • (H ^ 3 • S⁻¹) • S • H ∎


  lemma-HSHSH : H • S • H • S • H ≈ S⁻¹
  lemma-HSHSH = bbc S ε claim
    where
    open Basis-Change _ ((₁₊ n) QRel,_===_) grouplike
    open Group-Lemmas _ _ (grouplike {₁₊ n}) renaming (_⁻¹ to _⁻¹ʷ)
    
    claim : S • (H • S • H • S • H) • ε ≈ S • S⁻¹ • ε
    claim = begin
      S • (H • S • H • S • H) • ε ≈⟨ by-assoc auto ⟩
      (S • H) ^ 3 ≈⟨ axiom order-SH ⟩
      ε ≈⟨ sym (axiom order-S) ⟩
      S • S⁻¹ ≈⟨ sym (cong refl right-unit) ⟩
      S • S⁻¹ • ε ∎

  lemma-HSH : H • S • H ≈ S⁻¹ • H ^ 3 • S⁻¹
  lemma-HSH = bbc S ε claim
    where
    open Basis-Change _ ((₁₊ n) QRel,_===_) grouplike
    open Group-Lemmas _ _ (grouplike {₁₊ n}) renaming (_⁻¹ to _⁻¹ʷ)
    claim : S • (H • S • H) • ε ≈ S • (S⁻¹ • H ^ 3 • S⁻¹) • ε
    claim = begin
      S • (H • S • H) • ε ≈⟨ cong refl right-unit ⟩
      S • (H • S • H) ≈⟨ lemma-SHSH ⟩
      H ^ 3 • S⁻¹ ≈⟨ sym left-unit ⟩
      ε • H ^ 3 • S⁻¹ ≈⟨ (cleft sym (axiom order-S)) ⟩
      (S • S⁻¹) • H ^ 3 • S⁻¹ ≈⟨ assoc ⟩
      S • (S⁻¹ • H ^ 3 • S⁻¹) ≈⟨ sym (cong refl right-unit) ⟩
      S • (S⁻¹ • H ^ 3 • S⁻¹) • ε ∎
  
  lemma-SX : S • X ≈ X • Z • S
  lemma-SX = begin
    S • H • S • H • H • S⁻¹ • H ≈⟨ special-assoc (□ ^ 7) (□ ^ 4 • □ ^ 3) auto ⟩
    (S • H • S • H) • H • S⁻¹ • H ≈⟨ (cleft lemma-SHSH) ⟩
    (H ^ 3 • S⁻¹) • H • S⁻¹ • H ≈⟨ (cright cleft (sym (trans (by-assoc auto) (trans (cleft lemma-order-H) left-unit)))) ⟩
    (H ^ 3 • S⁻¹) • H ^ 5 • S⁻¹ • H ≈⟨ sym (special-assoc (□ ^ 5 • □ • □ ^ 3 • □ ^ 2) ((□ ^ 3 • □ )• □ ^ 5 • □ ^ 2) auto) ⟩
    (H • H • H • S⁻¹ • H) • (H • H ^ 3 • S⁻¹ • H) ≈⟨ (cleft (cright sym left-unit)) ⟩
    (H • ε • H • H • S⁻¹ • H) • (H • H ^ 3 • S⁻¹ • H) ≈⟨ (cleft cright cleft sym (axiom order-S)) ⟩
    (H • (S • S⁻¹) • H • H • S⁻¹ • H) • (H • H ^ 3 • S⁻¹ • H) ≈⟨ special-assoc ((□ • □ ^ 2 • □ ^ 4) • □ ^ 4) (□ ^ 2 • □ ^ 6 • □ ^ 3) auto ⟩
    (H • S) • (S⁻¹ • H • H • S⁻¹ • H • H) • H ^ 3 • S⁻¹ • H ≈⟨ (cright cleft word-comm p-1 1 (lemma-comm-SHHS^kHH p-1)) ⟩
    (H • S) • ((H • H • S⁻¹ • H • H) • S⁻¹) • H ^ 3 • S⁻¹ • H ≈⟨ special-assoc (□ ^ 2 • (□ ^ 5 • □) • □ ^ 3) (□ ^ 6 • □ • □ ^ 3 • □) auto ⟩
    (H • S • H • H • S⁻¹ • H) • H • (S⁻¹ • H ^ 3 • S⁻¹) • H ≈⟨ (cright cright cleft sym lemma-HSH) ⟩
    (H • S • H • H • S⁻¹ • H) • H • (H • S • H) • H ≈⟨ special-assoc (□ ^ 6 • □ • □ ^ 3 • □) (□ ^ 6 • □ ^ 5) auto ⟩

    (H • S • H • H • S⁻¹ • H) • (H • H • S • H • H) ≈⟨ (cright sym right-unit) ⟩
    (H • S • H • H • S⁻¹ • H) • (H • H • S • H • H) • ε ≈⟨ (cright cright sym (axiom order-S)) ⟩
    (H • S • H • H • S⁻¹ • H) • (H • H • S • H • H) • S • S⁻¹ ≈⟨ (cright cright word-comm 1 p-1 refl) ⟩
    (H • S • H • H • S⁻¹ • H) • (H • H • S • H • H) • S⁻¹ • S ≈⟨ (cright special-assoc (□ ^ 5 • □ ^ 2) (□ ^ 6 • □) auto) ⟩
    (H • S • H • H • S⁻¹ • H) • (H • H • S • H • H • S⁻¹) • S ∎
    where

  conj-S-X : S • X ≈ (X • Z) • S
  conj-S-X = begin
    S • X ≈⟨ lemma-SX ⟩
    X • Z • S ≈⟨ sym assoc ⟩
    (X • Z) • S ∎

  conj-S-X^k : ∀ k -> S • X ^ k ≈ (X • Z) ^ k • S
  conj-S-X^k k = lemma-Induction conj-S-X k

  conj-S^l-X : ∀ l -> S ^ l • X ≈ X • Z ^ l • S ^ l
  conj-S^l-X l = begin
    S ^ l • X ≈⟨ lemma-Inductionˡ lemma-SX l ⟩
    X • (Z • S) ^ l ≈⟨ (cright lemma-^-• Z S l lemma-comm-Z-S) ⟩
    X • Z ^ l • S ^ l ∎  

  conj-S^l-X' : ∀ l -> S ^ l • X ≈ (X • Z ^ l) • S ^ l
  conj-S^l-X' l = begin
    S ^ l • X ≈⟨ conj-S^l-X l ⟩
    X • Z ^ l • S ^ l ≈⟨ sym assoc ⟩
    (X • Z ^ l) • S ^ l ∎
