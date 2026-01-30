{-# OPTIONS --safe #-}
{-# OPTIONS --termination-depth=20 #-}

open import Level using (0ℓ)

open import Relation.Binary using (Rel)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Binary.Morphism.Definitions using (Homomorphic₂)
open import Relation.Binary.PropositionalEquality using (_≡_ ; inspect ; setoid ; module ≡-Reasoning ; _≢_) renaming ([_] to [_]')
import Relation.Binary.Reasoning.Setoid as SR
import Relation.Binary.PropositionalEquality as Eq
open import Relation.Nullary.Decidable using (yes ; no)


open import Function using (_∘_ ; id)
open import Function.Definitions using (Injective)

open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂ ; map₁ ; ∃)
open import Data.Product.Relation.Binary.Pointwise.NonDependent as PW using (≡×≡⇒≡ ; Pointwise ; ≡⇒≡×≡)
open import Data.Nat hiding (_^_ ; _+_ ; _*_ ; _%_ ; _/_)
open import Data.Nat.DivMod
open import Agda.Builtin.Nat using ()
import Data.Nat as Nat
open import Data.Fin hiding (_+_ ; _-_)
open import Data.Bool
open import Data.List hiding ([_])


open import Data.Maybe
open import Data.Sum using (_⊎_ ; inj₁ ; inj₂ ; [_,_])
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
open import Presentation.Tactics

open import Presentation.Construct.Base hiding (_*_)
import Presentation.Construct.Properties.SemiDirectProduct2 as SDP2
import Presentation.Construct.Properties.DirectProduct as DP
import Presentation.Groups.Cyclic as Cyclic


open import Data.Fin.Properties as FP using (suc-injective ; toℕ-inject₁ ; toℕ-fromℕ)
import Data.Nat.Properties as NP
open import Presentation.GroupLike
open import Data.Nat.Primality
open import Data.Nat.Coprimality hiding (sym)
open import Data.Nat.GCD
open Bézout
open import Data.Empty
open import Algebra.Properties.Group
open import Zp.ModularArithmetic
open import Zp.Fermats-little-theorem

module N.Symplectic-Alternative
  (p-2 : ℕ)
  (p-prime : Prime (suc (suc p-2)))
  (let open PrimeModulus' p-2 p-prime)
  (g*@(g , g≠0) : ℤ* ₚ)
  (g-gen : ∀ ((x , _) : ℤ* ₚ) -> ∃ \ (k : ℤ ₚ-₁) -> x ≡ g ^′ toℕ k )
  where


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

open Primitive-Root-Modp' g* g-gen

module Symplectic-Alternative where

import N.Symplectic-Simplified p-2 p-prime as NSim
open import N.Symplectic p-2 p-prime using (module Symplectic)
open Symplectic hiding (_QRel,_===_)

module Alternative-Relations where

  
  M₋₁ : ∀ {n} -> Word (Gen (₁₊ n))
  M₋₁ = M -'₁

  Mg :  ∀ {n} -> Word (Gen (₁₊ n))
  Mg = M g′

  Mg^ : ℤ ₚ ->  ∀ {n} -> Word (Gen (₁₊ n))
  Mg^ k = Mg ^ toℕ k


  infix 4 _QRel,_===_
  data _QRel,_===_ : (n : ℕ) → WRel (Gen n) where
  
    order-S :           ∀ {n} → (₁₊ n) QRel,  S ^ p === ε
    order-H :           ∀ {n} → (₁₊ n) QRel,  H ^ 2 === M₋₁
    M-power : ∀ {n} (k : ℤ ₚ) → (₁₊ n) QRel,  Mg^ k === M (g^ k)
    semi-MS :           ∀ {n} → (₁₊ n) QRel,  Mg • S === S^ (g * g) • Mg


    order-CZ :          ∀ {n} → (₂₊ n) QRel,  CZ ^ p === ε
    order-Ex :          ∀ {n} → (₂₊ n) QRel,  Ex ^ 2 === ε

    comm-CZ-S↑ :        ∀ {n} → (₂₊ n) QRel,  CZ • S ↑ === S ↑ • CZ
    semi-M↑-CZ :        ∀ {n} → (₂₊ n) QRel,  Mg ↑ • CZ === CZ^ g • Mg ↑
    comm-Ex-CZ :        ∀ {n} → (₂₊ n) QRel,  Ex • CZ === CZ • Ex
    semi-Ex-S :         ∀ {n} → (₂₊ n) QRel,  Ex • S ↑ === S • Ex
    semi-Ex-H :         ∀ {n} → (₂₊ n) QRel,  Ex • H ↑ === H • Ex

    semi-S-CX :         ∀ {n} → (₂₊ n) QRel,  CX • S === S ↓ • S ↑ • CZ^ (- ₁) • CX
    semi-CZ-CX :        ∀ {n} → (₂₊ n) QRel,  CX • CZ === CZ • S^ (- ₁ + - ₁) • CX

    comm-CZ↑-CZ :       ∀ {n} → (₃₊ n) QRel,  CZ ↑ • CZ === CZ • CZ ↑
    yang-baxter :       ∀ {n} → (₃₊ n) QRel,  Ex ↑ • Ex ↓ • Ex ↑ === Ex ↓ • Ex ↑ • Ex ↓
    
    semi-Ex-Ex↑-CZ :    ∀ {n} → (₃₊ n) QRel,  Ex • Ex ↑ • CZ === CZ ↑ • Ex • Ex ↑
    semi-CX↑-CZ :       ∀ {n} → (₃₊ n) QRel,  CZ • CX ↑ === CX ↑ • CZ02 • CZ

    comm-H :         ∀ {n}{x} → (₂₊ n) QRel,  [ x ↥ ]ʷ • H === H • [ x ↥ ]ʷ
    comm-S :         ∀ {n}{x} → (₂₊ n) QRel,  [ x ↥ ]ʷ • S === S • [ x ↥ ]ʷ
    comm-CZ :        ∀ {n}{x} → (₃₊ n) QRel,  [ x ↥ ↥ ]ʷ • CZ === CZ • [ x ↥ ↥ ]ʷ
    
    cong↑ :         ∀ {n w v} →      n QRel,  w === v →
                                -------------------------       
                                (₁₊ n) QRel,  w ↑ === v ↑



module Lemmas-Alt where

  open Alternative-Relations
  
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


  lemma-^-↑ : ∀ {n} (w : Word (Gen n)) k → w ↑ ^ k ≡ (w ^ k) ↑
  lemma-^-↑ w ₀ = auto
  lemma-^-↑ w ₁ = auto
  lemma-^-↑ w (₂₊ k) = begin
    (w ↑) • (w ↑) ^ ₁₊ k ≡⟨ Eq.cong ((w ↑) •_) (lemma-^-↑ w (suc k)) ⟩
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

  lemma-M↓ : ∀ {n} x -> let open PB ((₂₊ n) QRel,_===_) renaming (_≈_ to _≈↓_) using () in
    M x ↓ ≈↓ M x
  lemma-M↓ {n} x' = begin
    (S^ x • H • S^ x⁻¹ • H • S^ x • H) ↓ ≈⟨ cong (refl' (lemma-↓^ (toℕ x) S)) (cright cong (refl' (lemma-↓^ (toℕ x⁻¹) S)) (cright (cleft refl' (lemma-↓^ (toℕ x) S)))) ⟩
    M x' ∎
    where
    open PB ((₂₊ n) QRel,_===_) renaming (_≈_ to _≈↓_)
    open PP ((₂₊ n) QRel,_===_)
    open SR word-setoid
    x = x' .proj₁
    x⁻¹ = ((x' ⁻¹) .proj₁ )
    
  lemma-M↑↓ : ∀ {n} x -> let open PB ((₃₊ n) QRel,_===_) renaming (_≈_ to _≈↓_) using () in
    M x ↑ ↓ ≈↓ M x ↑
  lemma-M↑↓ {n} x' = begin
    ((M x' ↑) ↓) ≡⟨ lemma-↑↓ (M x') ⟩
    ((M x' ↓) ↑) ≈⟨ lemma-cong↑ _ _ (lemma-M↓ x') ⟩
    (M x' ↑) ∎
    where
    open PB ((₃₊ n) QRel,_===_) renaming (_≈_ to _≈↓_)
    open PP ((₃₊ n) QRel,_===_)
    open SR word-setoid



  lemma-M↓↓ : ∀ {n} x -> let open PB ((₃₊ n) QRel,_===_) renaming (_≈_ to _≈↓_) using () in
    M x ↓ ↓ ≈↓ M x ↓
  lemma-M↓↓ {n} x' = begin
    (S^ x • H • S^ x⁻¹ • H • S^ x • H) ↓ ↓ ≡⟨ auto ⟩
    (S^ x ↓ • H • S^ x⁻¹ ↓ • H • S^ x ↓ • H) ↓ ≡⟨ Eq.cong₂ (\ xx yy -> (xx • H • yy • H • S^ x ↓ • H) ↓) (lemma-↓^ (toℕ x) S) (lemma-↓^ (toℕ x⁻¹) S) ⟩
    (S^ x • H • S^ x⁻¹ • H • S^ x ↓ • H) ↓ ≡⟨ Eq.cong (\ xx -> (S^ x • H • S^ x⁻¹ • H • xx • H) ↓) (lemma-↓^ (toℕ x) S) ⟩
    (S^ x • H • S^ x⁻¹ • H • S^ x • H) ↓ ≡⟨ auto ⟩
    M x' ↓ ∎
    where
    open PB ((₃₊ n) QRel,_===_) renaming (_≈_ to _≈↓_)
    open PP ((₃₊ n) QRel,_===_)
    open SR word-setoid
    x = x' .proj₁
    x⁻¹ = ((x' ⁻¹) .proj₁ )


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


module Lemmas1 (n : ℕ) where


  open Alternative-Relations

  open PB ((₁₊ n) QRel,_===_) hiding (_===_)
  open PP ((₁₊ n) QRel,_===_)
  open Pattern-Assoc
  open import Data.Nat.DivMod
  open import Data.Fin.Properties


  aux-M≡M : ∀ y y' -> y .proj₁ ≡ y' .proj₁ -> M {n = n} y ≡ M y'
  aux-M≡M y y' eq = begin
    M y ≡⟨ auto ⟩
    S^ x • H • S^ x⁻¹ • H • S^ x • H ≡⟨ Eq.cong₂ (\ xx yy -> S^ xx • H • S^ yy • H • S^ x • H) eq aux-eq ⟩
    S^ x' • H • S^ x'⁻¹ • H • S^ x • H ≡⟨ Eq.cong (\ xx -> S^ x' • H • S^ x'⁻¹ • H • S^ xx • H) eq ⟩
    S^ x' • H • S^ x'⁻¹ • H • S^ x' • H ≡⟨ auto ⟩
    M y' ∎
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

  lemma-M1 : M₁ ≈ ε
  lemma-M1 = begin
    M₁ ≡⟨ aux-M≡M ((₁ , λ ())) (g^ ₀) auto ⟩
    M (g^ ₀) ≈⟨ sym (axiom (M-power ₀)) ⟩
    Mg^ ₀ ≈⟨ refl ⟩
    ε ∎
    where
    open SR word-setoid

  lemma-order-SH : (S • H) ^ 3 ≈ ε
  lemma-order-SH = begin
    (S • H) ^ 3 ≈⟨ by-assoc auto ⟩
    S • H • S • H • S • H ≈⟨ (cright (cright cong aux-S refl)) ⟩
    S^ x • H • S^ x⁻¹ • H • S^ x • H ≈⟨ refl ⟩
    M₁ ≈⟨ lemma-M1 ⟩
    ε ∎
    where
    open SR word-setoid
    x' : ℤ* ₚ
    x' = (₁ , λ ())
    x = x' .proj₁
    x⁻¹ = ((x' ⁻¹) .proj₁ )
    aux-S : S ≈ S^ x⁻¹
    aux-S = begin
      S ≈⟨ refl ⟩
      S^ ₁ ≡⟨ Eq.cong S^ (Eq.sym aux₁⁻¹') ⟩
      S^ x⁻¹ ∎


  lemma-S⁻¹ : S⁻¹ ≈ S^ ₚ₋₁
  lemma-S⁻¹ = begin
    S⁻¹ ≈⟨ refl ⟩
    S ^ p-1 ≡⟨ Eq.cong (S ^_) (Eq.sym lemma-toℕ-ₚ₋₁) ⟩
    S ^ toℕ ₚ₋₁ ≈⟨ refl ⟩
    S^ ₚ₋₁ ∎
    where
    open SR word-setoid




  lemma-MgS^k : ∀ k ->  let g⁻¹ = (g′ ⁻¹) .proj₁ in let -g⁻¹ = - g⁻¹ in
    Mg • S ^ k ≈ S ^ (k Nat.* toℕ (g * g)) • Mg
  lemma-MgS^k k@0 = trans right-unit (sym left-unit)
  lemma-MgS^k k@1 = begin  
    Mg • S ^ k ≈⟨ refl ⟩
    Mg • S ≈⟨ axiom semi-MS ⟩
    S^ (g * g) • Mg ≈⟨ refl ⟩
    S ^ toℕ (g * g) • Mg ≈⟨ (cleft refl' (Eq.cong (S ^_) (Eq.sym ( NP.*-identityˡ (toℕ (g * g)))))) ⟩
    S ^ (k Nat.* toℕ (g * g)) • Mg ∎
    where
    open SR word-setoid
  lemma-MgS^k k@(₂₊ k') = begin  
    Mg • S ^ k ≈⟨ refl ⟩
    Mg • S • S ^ ₁₊ k' ≈⟨ sym assoc ⟩
    (Mg • S) • S ^ ₁₊ k' ≈⟨ (cleft lemma-MgS^k 1 ) ⟩
    (S ^ (1 Nat.* toℕ (g * g)) • Mg) • S ^ ₁₊ k' ≈⟨ assoc ⟩
    S ^ (1 Nat.* toℕ (g * g)) • Mg • S ^ ₁₊ k' ≈⟨ (cright lemma-MgS^k (₁₊ k')) ⟩
    S ^ (1 Nat.* toℕ (g * g)) • S ^ (₁₊ k' Nat.* toℕ (g * g)) • Mg ≈⟨ sym assoc ⟩
    (S ^ (1 Nat.* toℕ (g * g)) • S ^ (₁₊ k' Nat.* toℕ (g * g))) • Mg ≈⟨ (cleft sym (lemma-^-+ S ((1 Nat.* toℕ (g * g))) ((₁₊ k' Nat.* toℕ (g * g))))) ⟩
    (S ^ ((1 Nat.* toℕ (g * g)) Nat.+ (₁₊ k' Nat.* toℕ (g * g)))) • Mg ≈⟨ (cleft refl' (Eq.cong (S ^_) (Eq.sym (NP.*-distribʳ-+ (toℕ (g * g)) ₁ (₁₊ k'))))) ⟩
    S ^ ((1 Nat.+ ₁₊ k') Nat.* toℕ (g * g) ) • Mg ≈⟨ refl ⟩
    S ^ (k Nat.* toℕ (g * g)) • Mg ∎
    where
    open SR word-setoid

  lemma-S^k-% : ∀ k -> S ^ k ≈ S ^ (k % p)
  lemma-S^k-% k = begin
    S ^ k ≡⟨ Eq.cong (S ^_) (m≡m%n+[m/n]*n k p) ⟩
    S ^ (k Nat.% p Nat.+ k Nat./ p Nat.* p) ≈⟨ lemma-^-+ S (k Nat.% p) (k Nat./ p Nat.* p) ⟩
    S ^ (k Nat.% p) • S ^ (k Nat./ p Nat.* p) ≈⟨ (cright refl' (Eq.cong (S ^_) (NP.*-comm (k Nat./ p) p))) ⟩
    S ^ (k Nat.% p) • S ^ (p Nat.* (k Nat./ p)) ≈⟨ sym (cright lemma-^^ S p (k Nat./ p)) ⟩
    S ^ (k Nat.% p) • (S ^ p) ^ (k Nat./ p) ≈⟨ (cright lemma-^-cong (S ^ p) ε (k Nat./ p) (axiom order-S)) ⟩
    S ^ (k Nat.% p) • (ε) ^ (k Nat./ p) ≈⟨ (cright lemma-ε^k=ε (k Nat./ p)) ⟩
    S ^ (k Nat.% p) • ε ≈⟨ right-unit ⟩
    S ^ (k % p) ∎
    where
    open SR word-setoid


  lemma-MgS^k' : ∀ k -> let x⁻¹ = (g′ ⁻¹) .proj₁ in let -x⁻¹ = - x⁻¹ in
    Mg • S^ k ≈ S^ (k * (g * g)) • Mg
  lemma-MgS^k' k = begin 
    Mg • S^ k ≈⟨ refl ⟩
    Mg • S ^ toℕ k ≈⟨ lemma-MgS^k (toℕ k) ⟩
    S ^ (toℕ k Nat.* toℕ (g * g)) • Mg ≈⟨ (cleft lemma-S^k-% (toℕ k Nat.* toℕ (g * g))) ⟩
    S ^ ((toℕ k Nat.* toℕ (g * g)) % p) • Mg ≈⟨ (cleft refl' (Eq.cong (S ^_) (lemma-toℕ-% k (g * g)))) ⟩
    S ^ toℕ (k * (g * g)) • Mg ≈⟨ refl ⟩
    S^ (k * (g * g)) • Mg ∎
    where
    open SR word-setoid
    x⁻¹ = (g′ ⁻¹) .proj₁
    -x⁻¹ = - x⁻¹

  lemma-Mg^kS : ∀ k -> Mg ^ k • S ≈ S^ ((g * g) ^′ k) • Mg ^ k
  lemma-Mg^kS k@0 = trans left-unit (sym right-unit)
  lemma-Mg^kS k@1 = begin
    Mg ^ k • S ≈⟨ axiom semi-MS ⟩
    S^ ((g * g)) • Mg ^ k ≈⟨ (cleft refl' (Eq.cong S^ (Eq.sym (lemma-x^′1=x (fromℕ< _))))) ⟩
    S^ ((g * g) ^′ k) • Mg ^ k ∎
    where
    open SR word-setoid
  lemma-Mg^kS k@(₂₊ n) = begin
    (Mg • Mg ^ ₁₊ n) • S ≈⟨ assoc ⟩
    Mg • Mg ^ ₁₊ n • S ≈⟨ (cright lemma-Mg^kS (₁₊ n)) ⟩
    Mg • S^ ((g * g) ^′ (₁₊ n)) • Mg ^ (₁₊ n) ≈⟨ sym assoc ⟩
    (Mg • S^ ((g * g) ^′ (₁₊ n))) • Mg ^ (₁₊ n) ≈⟨ (cleft lemma-MgS^k' ((g * g) ^′ (₁₊ n))) ⟩
    (S^ (((g * g) ^′ (₁₊ n)) * (g * g)) • Mg) • Mg ^ (₁₊ n) ≈⟨ refl' (Eq.cong (\ xx -> (S^ xx • Mg) • Mg ^ (₁₊ n)) (*-comm ((g * g) ^′ (₁₊ n)) (g * g))) ⟩
    (S^ ((g * g) * ((g * g) ^′ (₁₊ n))) • Mg) • Mg ^ (₁₊ n) ≈⟨ assoc ⟩
    S^ ((g * g) ^′ k) • Mg • Mg ^ ₁₊ n ∎
    where
    open SR word-setoid


  lemma-semi-MS : ∀ x -> let x' = x .proj₁ in let k = g-gen x .proj₁ in M x • S ≈ S^ ((x' * x')) • M x
  lemma-semi-MS x = begin
    M x • S ≈⟨ (cleft refl' (aux-M≡M x (g^ k) (eqk))) ⟩
    M (g^ k) • S ≈⟨ cong (sym (axiom (M-power (k)))) refl ⟩
    Mg^ k • S ≈⟨ lemma-Mg^kS (toℕ k) ⟩
    S^ ((g * g) ^′ toℕ k) • Mg^ k ≈⟨ (cright axiom (M-power (k))) ⟩
    S^ ((g * g) ^′ toℕ k) • M (g^ k) ≈⟨ (cleft refl' (Eq.cong S^ (*-^′-distribʳ g g (toℕ k)))) ⟩
    S^ ((g ^′ toℕ k) * (g ^′ toℕ k)) • M (g^ k) ≈⟨ sym (cleft refl' (Eq.cong₂ (\ xx yy -> S^ (xx * yy)) (eqk) (eqk))) ⟩
    S^ (x' * x') • M (g^ k) ≈⟨ (cright refl' (aux-M≡M (g^ k) x (Eq.sym (eqk)))) ⟩
    S^ (x' * x') • M x ∎
    where
    open SR word-setoid
    x' = x .proj₁
    k = inject₁ (g-gen x .proj₁)
    eqk : x .proj₁ ≡ (g^ k) .proj₁
    eqk = Eq.sym (lemma-log-inject x)



  open import Data.Fin.Properties
  
  lemma-Mg^p-1=ε : Mg ^ p-1 ≈ ε
  lemma-Mg^p-1=ε = begin
    Mg ^ p-1 ≡⟨ Eq.cong (Mg ^_) (Eq.sym (toℕ-fromℕ< (NP.n<1+n p-1))) ⟩
    Mg^ (fromℕ< (NP.n<1+n p-1)) ≈⟨ axiom (M-power (₁₊ (fromℕ< _))) ⟩
    M (g^ p-1') ≡⟨ aux-M≡M (g^ p-1') ((g ^′ p-1 , lemma-g^′k≠0 p-1)) (Eq.cong (g ^′_) (toℕ-fromℕ< (NP.n<1+n p-1))) ⟩
    M (g ^′ p-1 , lemma-g^′k≠0 p-1) ≡⟨ aux-M≡M ((g ^′ p-1 , lemma-g^′k≠0 p-1)) (1ₚ , λ ()) Zp.Fermats-little-theorem' ⟩
    M (1ₚ , λ ()) ≈⟨ sym (axiom (M-power ₀)) ⟩
    ε ∎
    where
    open SR word-setoid
    p-1' = fromℕ< (NP.n<1+n p-1)

  aux-Mg^[kp-1] : ∀ k -> Mg ^ (k Nat.* p-1) ≈ ε
  aux-Mg^[kp-1] k = begin
    Mg ^ (k Nat.* p-1) ≈⟨ refl' (Eq.cong (Mg ^_) (NP.*-comm k p-1)) ⟩
    Mg ^ (p-1 Nat.* k) ≈⟨ sym (lemma-^^ Mg p-1 k) ⟩
    (Mg ^ p-1) ^ k ≈⟨ lemma-^-cong (Mg ^ p-1) ε k lemma-Mg^p-1=ε ⟩
    ε ^ k ≈⟨ lemma-ε^k=ε k ⟩
    ε ∎
    where
    open SR word-setoid

  lemma-M-mul : ∀ x y -> M x • M y ≈ M (x *' y)
  lemma-M-mul x y = begin
    M x • M y ≈⟨ cong (refl' (aux-M≡M x (g^ k) eqk)) (refl' (aux-M≡M y (g^ l) eql)) ⟩
    M (g^ k) • M (g^ l) ≈⟨ cong (sym (axiom (M-power k))) (sym (axiom (M-power l))) ⟩
    Mg ^ toℕ k • Mg ^ toℕ l ≈⟨ sym (lemma-^-+ Mg (toℕ k) (toℕ l)) ⟩
    Mg ^ [k+l] ≡⟨ Eq.cong (Mg ^_) (m≡m%n+[m/n]*n [k+l] p-1) ⟩
    Mg ^ ([k+l]%p-1 Nat.+ [k+l]/p-1 Nat.* p-1) ≈⟨ lemma-^-+ Mg [k+l]%p-1 (([k+l]/p-1 Nat.* p-1)) ⟩
    Mg ^ [k+l]%p-1 • Mg ^ ([k+l]/p-1 Nat.* p-1) ≈⟨ (cright trans refl (aux-Mg^[kp-1] [k+l]/p-1)) ⟩
    Mg ^ [k+l]%p-1 • ε ≈⟨ right-unit ⟩
    Mg ^ [k+l]%p-1 ≡⟨ Eq.cong (Mg ^_) (Eq.sym (toℕ-fromℕ< (m%n<n [k+l] p-1))) ⟩
    Mg ^ toℕ ( (fromℕ< (m%n<n [k+l] p-1))) ≡⟨ Eq.cong (Mg ^_) (Eq.sym (toℕ-inject₁ ((fromℕ< (m%n<n [k+l] p-1))))) ⟩
    Mg ^ toℕ (inject₁ (fromℕ< (m%n<n [k+l] p-1))) ≈⟨ refl ⟩
    Mg^ (inject₁ (fromℕ< (m%n<n [k+l] p-1))) ≈⟨ axiom (M-power (inject₁ (fromℕ< (m%n<n [k+l] p-1)))) ⟩
    M (g^ (inject₁ (fromℕ< (m%n<n [k+l] p-1)))) ≡⟨ aux-M≡M (g^ (inject₁ (fromℕ< (m%n<n [k+l] p-1)))) (g^′ [k+l]) aux-2 ⟩
    M (g^′ [k+l]) ≡⟨ aux-M≡M (g^′ [k+l]) (g^′ toℕ k *' g^′ toℕ l) aux-1 ⟩
    M (g^′ toℕ k *' g^′ toℕ l) ≡⟨ aux-M≡M (g^′ toℕ k *' g^′ toℕ l) (x *' y) aux-0 ⟩
    M (x *' y) ∎
    where
    k = inject₁ (g-gen x .proj₁)
    l = inject₁ (g-gen y .proj₁)
    eqk : x .proj₁ ≡ (g^ k) .proj₁
    eqk = Eq.sym (lemma-log-inject x)
    eql : y .proj₁ ≡ (g^ l) .proj₁
    eql = Eq.sym (lemma-log-inject y)

    [k+l] = toℕ k Nat.+ toℕ l
    [k+l]%p-1 = [k+l] Nat.% p-1
    [k+l]/p-1 = [k+l] Nat./ p-1

    aux-0 : ((g^′ toℕ k) *' (g^′ toℕ l)) .proj₁ ≡ (x *' y) .proj₁
    aux-0 = begin
      ((g^′ toℕ k) *' (g^′ toℕ l)) .proj₁ ≡⟨ auto ⟩
      (g^′ toℕ k) .proj₁ * (g^′ toℕ l) .proj₁ ≡⟨ Eq.cong₂ (\ xx yy -> (xx * yy) ) (lemma-log-inject x) (lemma-log-inject y) ⟩
      x .proj₁ * y .proj₁ ≡⟨ auto ⟩
      (x *' y) .proj₁ ∎
      where
      open ≡-Reasoning

    aux-1 : (g^′ [k+l]) .proj₁ ≡ ((g^′ toℕ k) *' (g^′ toℕ l)) .proj₁
    aux-1 = begin
      (g^′ [k+l]) .proj₁ ≡⟨ auto ⟩
      (g ^′ [k+l]) ≡⟨ Eq.sym (+-^′-distribʳ g (toℕ k) (toℕ l)) ⟩
      ((g ^′ toℕ k) * (g ^′ toℕ l)) ≡⟨ auto ⟩
      ((g^′ toℕ k) *' (g^′ toℕ l)) .proj₁ ∎
      where
      open ≡-Reasoning

    aux-2 : g ^′ toℕ (inject₁ (fromℕ< (m%n<n [k+l] p-1))) ≡ g ^′ (toℕ k Nat.+ toℕ l)
    aux-2 = begin
      g ^′ toℕ (inject₁ (fromℕ< (m%n<n [k+l] p-1))) ≡⟨ Eq.cong (g ^′_) (toℕ-inject₁ ((fromℕ< (m%n<n [k+l] p-1)))) ⟩
      g ^′ toℕ ( (fromℕ< (m%n<n [k+l] p-1))) ≡⟨ Eq.cong (g ^′_) (toℕ-fromℕ< ((m%n<n [k+l] p-1))) ⟩
      g ^′ [k+l]%p-1 ≡⟨ Eq.sym (aux-g^′-% [k+l]) ⟩
      g ^′ (toℕ k Nat.+ toℕ l) ∎
      where
      open ≡-Reasoning

    open SR word-setoid


  lemma-M₋₁^2 : M₋₁ ^ 2 ≈ ε
  lemma-M₋₁^2 = begin
    M₋₁ ^ 2 ≈⟨ lemma-M-mul -'₁ -'₁ ⟩
    M (-'₁ *' -'₁) ≡⟨ aux-M≡M (-'₁ *' -'₁) (₁ , (λ ())) aux-0 ⟩
    M₁ ≈⟨ sym (sym lemma-M1) ⟩
    ε ∎
    where
    open import Algebra.Properties.Ring (+-*-ring p-2)
    
    aux-0 : (-'₁ *' -'₁) .proj₁ ≡ ₁
    aux-0 = begin
      (- ₁ * - ₁) ≡⟨ -1*x≈-x (- ₁) ⟩
      (- - ₁) ≡⟨ -‿involutive ₁ ⟩
      ₁ ∎
      where
      open ≡-Reasoning
    open SR word-setoid

  lemma-order-H : H ^ 4 ≈ ε
  lemma-order-H = begin
    H ^ 4 ≈⟨ sym assoc ⟩
    HH ^ 2 ≈⟨ cong (axiom order-H) (axiom order-H) ⟩
    M₋₁ ^ 2 ≈⟨ lemma-M₋₁^2 ⟩
    ε ∎
    where
    open SR word-setoid


module Symplectic-Alt-GroupLike where

  private
    variable
      n : ℕ
    
  open Alternative-Relations
  open Lemmas-Alt


  grouplike : Grouplike (n QRel,_===_)
  grouplike {₁₊ n} (H-gen) = (H ) ^ 3 , claim
    where
    open PB ((₁₊ n) QRel,_===_)
    open PP ((₁₊ n) QRel,_===_)
    open SR word-setoid
    open Lemmas1 n
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


module Lemmas1b (n : ℕ) where


  open Alternative-Relations

  open PB ((₁₊ n) QRel,_===_) hiding (_===_)
  open PP ((₁₊ n) QRel,_===_)
  open Pattern-Assoc
  open Symplectic-Alt-GroupLike
  open import Data.Nat.DivMod
  open import Data.Fin.Properties

  lemma-[H⁻¹S⁻¹]^3 : (H⁻¹ • S⁻¹) ^ 3 ≈ ε
  lemma-[H⁻¹S⁻¹]^3 = begin
    (H⁻¹ • S⁻¹) ^ 3 ≈⟨ _≈_.sym assoc ⟩
    (H⁻¹ • S⁻¹) WB.^' 3 ≈⟨ lemma-cong-inv (lemma-order-SH) ⟩
    winv ε ≈⟨ refl ⟩
    ε ∎
    where
    open Lemmas1 n
    open Group-Lemmas _ _ grouplike renaming (_⁻¹ to winv)
    open SR word-setoid

  lemma-[S⁻¹H⁻¹]^3 : (S⁻¹ • H⁻¹) ^ 3 ≈ ε
  lemma-[S⁻¹H⁻¹]^3 = begin
    (S⁻¹ • H⁻¹) ^ 3 ≈⟨ sym (trans (cright lemma-left-inverse) right-unit) ⟩
    (S⁻¹ • H⁻¹) ^ 3 • (S⁻¹ • S) ≈⟨ special-assoc ((□ • □) ^ 3 • □ • □) (□ • (□ • □) ^ 3 • □) auto ⟩
    S⁻¹ • (H⁻¹ • S⁻¹) ^ 3 • S ≈⟨ cright cleft lemma-[H⁻¹S⁻¹]^3 ⟩
    S⁻¹ • ε • S ≈⟨ by-assoc auto ⟩
    S⁻¹ • S ≈⟨ lemma-left-inverse ⟩
    ε ∎
    where
    open Group-Lemmas _ _ grouplike renaming (_⁻¹ to winv)
    open SR word-setoid
    open Pattern-Assoc

  derived-5 : ∀ x k -> (nz : x ≢ ₀) -> let x⁻¹ = ((x , nz) ⁻¹) .proj₁ in let -x⁻¹ = - x⁻¹ in

    M (x , nz) • S ^ k ≈ S ^ (k Nat.* toℕ (x * x)) • M (x , nz)
  derived-5 x k@0 nz = trans right-unit (sym left-unit)
  derived-5 x k@1 nz = begin  
    M (x , nz) • S ^ k ≈⟨ refl ⟩
    M (x , nz) • S ≈⟨ lemma-semi-MS (x , nz) ⟩
    S^ (x * x) • M (x , nz) ≈⟨ refl ⟩
    S ^ toℕ (x * x) • M (x , nz) ≈⟨ (cleft refl' (Eq.cong (S ^_) (Eq.sym ( NP.*-identityˡ (toℕ (x * x)))))) ⟩
    S ^ (k Nat.* toℕ (x * x)) • M (x , nz) ∎
    where
    open SR word-setoid
    open Lemmas1 n
  derived-5 x k@(₂₊ k') nz = begin  
    M (x , nz) • S ^ k ≈⟨ refl ⟩
    M (x , nz) • S • S ^ ₁₊ k' ≈⟨ sym assoc ⟩
    (M (x , nz) • S) • S ^ ₁₊ k' ≈⟨ (cleft derived-5 x 1 nz) ⟩
    (S ^ (1 Nat.* toℕ (x * x)) • M (x , nz)) • S ^ ₁₊ k' ≈⟨ assoc ⟩
    S ^ (1 Nat.* toℕ (x * x)) • M (x , nz) • S ^ ₁₊ k' ≈⟨ (cright derived-5 x (₁₊ k') nz) ⟩
    S ^ (1 Nat.* toℕ (x * x)) • S ^ (₁₊ k' Nat.* toℕ (x * x)) • M (x , nz) ≈⟨ sym assoc ⟩
    (S ^ (1 Nat.* toℕ (x * x)) • S ^ (₁₊ k' Nat.* toℕ (x * x))) • M (x , nz) ≈⟨ (cleft sym (lemma-^-+ S ((1 Nat.* toℕ (x * x))) ((₁₊ k' Nat.* toℕ (x * x))))) ⟩
    (S ^ ((1 Nat.* toℕ (x * x)) Nat.+ (₁₊ k' Nat.* toℕ (x * x)))) • M (x , nz) ≈⟨ (cleft refl' (Eq.cong (S ^_) (Eq.sym (NP.*-distribʳ-+ (toℕ (x * x)) ₁ (₁₊ k'))))) ⟩
    S ^ ((1 Nat.+ ₁₊ k') Nat.* toℕ (x * x) ) • M (x , nz) ≈⟨ refl ⟩
    S ^ (k Nat.* toℕ (x * x)) • M (x , nz) ∎
    where
    open SR word-setoid


  lemma-MS^k : ∀ x k -> (nz : x ≢ ₀) -> let x⁻¹ = ((x , nz) ⁻¹) .proj₁ in let -x⁻¹ = - x⁻¹ in
    M (x , nz) • S^ k ≈ S^ (k * (x * x)) • M (x , nz)
  lemma-MS^k x k nz = begin 
    M (x , nz) • S^ k ≈⟨ refl ⟩
    M (x , nz) • S ^ toℕ k ≈⟨ derived-5 x (toℕ k) nz ⟩
    S ^ (toℕ k Nat.* toℕ (x * x)) • M (x , nz) ≈⟨ (cleft lemma-S^k-% (toℕ k Nat.* toℕ (x * x))) ⟩
    S ^ ((toℕ k Nat.* toℕ (x * x)) % p) • M (x , nz) ≈⟨ (cleft refl' (Eq.cong (S ^_) (lemma-toℕ-% k (x * x)))) ⟩
    S ^ toℕ (k * (x * x)) • M (x , nz) ≈⟨ refl ⟩
    S^ (k * (x * x)) • M (x , nz) ∎
    where
    open Lemmas1 n    
    open SR word-setoid
    x⁻¹ = ((x , nz) ⁻¹) .proj₁
    -x⁻¹ = - x⁻¹


  lemma-comm-HHS : H • H • S ≈ S • H • H
  lemma-comm-HHS = begin
    H • H • S ≈⟨ sym assoc ⟩
    HH • S ≈⟨ (cleft axiom order-H) ⟩
    M₋₁ • S ≈⟨ lemma-semi-MS -'₁ ⟩
    S^ (- ₁ * - ₁) • M₋₁ ≈⟨ (cleft refl' (Eq.cong S^ aux-0)) ⟩
    S^ ₁ • M₋₁ ≈⟨ refl ⟩
    S • M₋₁ ≈⟨ (cright sym (axiom order-H)) ⟩
    S • H • H ∎
    where
    open Lemmas1 n    
    open import Algebra.Properties.Ring (+-*-ring p-2)

    aux-0 : (-'₁ *' -'₁) .proj₁ ≡ ₁
    aux-0 = begin
      (- ₁ * - ₁) ≡⟨ -1*x≈-x (- ₁) ⟩
      (- - ₁) ≡⟨ -‿involutive ₁ ⟩
      ₁ ∎
      where
      open ≡-Reasoning
    
    open SR word-setoid


module Lemmas-Dual where

  private
    variable
      n : ℕ
    
  open Alternative-Relations
  open Lemmas-Alt

  open Symplectic-Alt-GroupLike

  lemma-semi-Ex-S↓ :  let open PB ((₂₊ n) QRel,_===_) in
    Ex • S ↓ ≈ S ↑ • Ex
  lemma-semi-Ex-S↓ {n} = bbc Ex Ex claim
    where
    open PB ((₂₊ n) QRel,_===_)
    open PP ((₂₊ n) QRel,_===_)
    open SR word-setoid
    open Basis-Change _ ((₂₊ n) QRel,_===_) grouplike
    claim : Ex • (Ex • S ↓) • Ex ≈ Ex • (S ↑ • Ex) • Ex
    claim = begin
      Ex • (Ex • S ↓) • Ex ≈⟨ by-assoc auto ⟩
      (Ex • Ex) • S ↓ • Ex ≈⟨ (cleft axiom order-Ex) ⟩
      ε • S ↓ • Ex ≈⟨ left-unit ⟩
      S ↓ • Ex ≈⟨ sym (axiom semi-Ex-S) ⟩
      Ex • S ↑ ≈⟨ cong refl (sym right-unit) ⟩
      Ex • S ↑ • ε ≈⟨ (cright cright sym (axiom order-Ex)) ⟩
      Ex • S ↑ • Ex • Ex ≈⟨ (cright sym assoc) ⟩
      Ex • (S ↑ • Ex) • Ex ∎


  lemma-semi-Ex-H↓ :  let open PB ((₂₊ n) QRel,_===_) in
    Ex • H ↓ ≈ H ↑ • Ex
  lemma-semi-Ex-H↓ {n} = bbc Ex Ex claim
    where
    open PB ((₂₊ n) QRel,_===_)
    open PP ((₂₊ n) QRel,_===_)
    open SR word-setoid
    open Basis-Change _ ((₂₊ n) QRel,_===_) grouplike
    claim : Ex • (Ex • H ↓) • Ex ≈ Ex • (H ↑ • Ex) • Ex
    claim = begin
      Ex • (Ex • H ↓) • Ex ≈⟨ by-assoc auto ⟩
      (Ex • Ex) • H ↓ • Ex ≈⟨ (cleft axiom order-Ex) ⟩
      ε • H ↓ • Ex ≈⟨ left-unit ⟩
      H ↓ • Ex ≈⟨ sym (axiom semi-Ex-H) ⟩
      Ex • H ↑ ≈⟨ cong refl (sym right-unit) ⟩
      Ex • H ↑ • ε ≈⟨ (cright cright sym (axiom order-Ex)) ⟩
      Ex • H ↑ • Ex • Ex ≈⟨ (cright sym assoc) ⟩
      Ex • (H ↑ • Ex) • Ex ∎

  lemma-comm-CZ-S↓ : let open PB ((₂₊ n) QRel,_===_) in
    CZ • S ↓ ≈ S ↓ • CZ
  lemma-comm-CZ-S↓ {n} = bbc Ex ε claim
    where
    open PB ((₂₊ n) QRel,_===_)
    open PP ((₂₊ n) QRel,_===_)
    open SR word-setoid
    open Basis-Change _ ((₂₊ n) QRel,_===_) grouplike
    
    claim : Ex • (CZ • S ↓) • ε ≈ Ex • (S ↓ • CZ) • ε
    claim = begin
      Ex • (CZ • S ↓) • ε ≈⟨ cong refl right-unit ⟩
      Ex • (CZ • S ↓) ≈⟨ sym assoc ⟩
      (Ex • CZ) • S ↓ ≈⟨ (cleft axiom comm-Ex-CZ) ⟩
      (CZ • Ex) • S ↓ ≈⟨ assoc ⟩
      CZ • Ex • S ↓ ≈⟨ (cright lemma-semi-Ex-S↓) ⟩
      CZ • S ↑ • Ex ≈⟨ sym assoc ⟩
      (CZ • S ↑) • Ex ≈⟨ cong (axiom comm-CZ-S↑) refl ⟩
      (S ↑ • CZ) • Ex ≈⟨ assoc ⟩
      S ↑ • CZ • Ex ≈⟨ cong refl (sym (axiom comm-Ex-CZ)) ⟩
      S ↑ • Ex • CZ ≈⟨ sym assoc ⟩
      (S ↑ • Ex) • CZ ≈⟨ (cleft sym lemma-semi-Ex-S↓) ⟩
      (Ex • S ↓) • CZ ≈⟨ assoc ⟩
      Ex • (S ↓ • CZ) ≈⟨ sym (cong refl right-unit) ⟩
      Ex • (S ↓ • CZ) • ε ∎


  aux-↑ : ∀ (w : Word (Gen n)) k -> w ↑ ^ k ≡ (w ^ k) ↑
  aux-↑ w k@0 = auto
  aux-↑ w k@1 = auto
  aux-↑ w k@(₂₊ k') = begin
    w ↑ ^ k ≡⟨ auto ⟩
    w ↑ • w ↑ ^ (₁₊ k') ≡⟨ (Eq.cong (w ↑ •_)  (aux-↑ w (₁₊ k'))) ⟩
    w ↑ • (w ^ (₁₊ k')) ↑ ≡⟨ auto ⟩
    (w ^ k) ↑ ∎
    where
    open ≡-Reasoning


  lemma-Ex-Sᵏ : ∀ k → let open PB ((₂₊ n) QRel,_===_) in 
    
    Ex • S ^ k ≈ S ↑ ^ k • Ex
    
  lemma-Ex-Sᵏ {n} ₀ = trans right-unit (sym left-unit)
    where
    open PB ((₂₊ n) QRel,_===_)
  lemma-Ex-Sᵏ {n} ₁ = sym (sym lemma-semi-Ex-S↓)
    where
    open PB ((₂₊ n) QRel,_===_)
  lemma-Ex-Sᵏ {n} (₂₊ k) = begin
    Ex • S • S ^ ₁₊ k ≈⟨ sym assoc ⟩
    (Ex • S) • S ^ ₁₊ k ≈⟨ cong (sym (sym lemma-semi-Ex-S↓)) refl ⟩
    (S ↑ • Ex) • S ^ ₁₊ k ≈⟨ assoc ⟩
    S ↑ • Ex • S ^ ₁₊ k ≈⟨ cong refl (lemma-Ex-Sᵏ (₁₊ k)) ⟩
    S ↑ • S ↑ ^ ₁₊ k • Ex ≈⟨ sym assoc ⟩
    ((S ↑) • (S ↑) ^ ₁₊ k) • Ex ∎
    where
    open PB ((₂₊ n) QRel,_===_)
    open PP ((₂₊ n) QRel,_===_)
    open SR word-setoid

  lemma-Ex-S^ᵏ : ∀ k → let open PB ((₂₊ n) QRel,_===_) in 

    Ex • S^ k ≈ S^ k ↑ • Ex

  lemma-Ex-S^ᵏ {n} k = begin
    Ex • S^ k ≈⟨ lemma-Ex-Sᵏ (toℕ k) ⟩
    S ↑ ^ toℕ k • Ex ≈⟨ (cleft refl' (aux-↑ S (toℕ k))) ⟩
    S^ k ↑ • Ex ∎
    where
    open PB ((₂₊ n) QRel,_===_)
    open PP ((₂₊ n) QRel,_===_)
    open SR word-setoid



  lemma-Ex-M : let open PB ((₂₊ n) QRel,_===_) in ∀ m -> Ex • M m ≈ M m ↑ • Ex
  lemma-Ex-M {n} m@x' = begin
    Ex • M m ≈⟨ refl ⟩
    Ex • S^ x • H • S^ x⁻¹ • H • S^ x • H ≈⟨ sym assoc ⟩
    (Ex • S^ x) • H • S^ x⁻¹ • H • S^ x • H ≈⟨ cleft lemma-Ex-S^ᵏ (m .proj₁) ⟩
    (S^ x ↑ • Ex) • H • S^ x⁻¹ • H • S^ x • H ≈⟨ special-assoc (□ ^ 2 • □ ^ 2) (□ • □ ^ 2 • □) auto ⟩
    S^ x ↑ • (Ex • H) • S^ x⁻¹ • H • S^ x • H ≈⟨ cright cleft sym (sym lemma-semi-Ex-H↓) ⟩
    S^ x ↑ • (H ↑ • Ex) • S^ x⁻¹ • H • S^ x • H ≈⟨ cright special-assoc (□ ^ 2 • □ ^ 2) (□ • □ ^ 2 • □) auto ⟩
    S^ x ↑ • H ↑ • (Ex • S^ x⁻¹) • H • S^ x • H ≈⟨ cright cright cleft lemma-Ex-S^ᵏ ((m ⁻¹) .proj₁) ⟩
    S^ x ↑ • H ↑ • (S^ x⁻¹ ↑ • Ex) • H • S^ x • H ≈⟨ cright cright special-assoc (□ ^ 2 • □ ^ 2) (□ • □ ^ 2 • □) auto ⟩
    S^ x ↑ • H ↑ • S^ x⁻¹ ↑ • (Ex • H) • S^ x • H ≈⟨ cright cright cright cleft sym (sym lemma-semi-Ex-H↓) ⟩
    S^ x ↑ • H ↑ • S^ x⁻¹ ↑ • (H ↑ • Ex) • S^ x • H ≈⟨ cright cright cright special-assoc (□ ^ 2 • □ ^ 2) (□ • □ ^ 2 • □) auto  ⟩
    S^ x ↑ • H ↑ • S^ x⁻¹ ↑ • H ↑ • (Ex • S^ x) • H ≈⟨ cright cright cright cright cleft lemma-Ex-S^ᵏ ((m) .proj₁) ⟩
    S^ x ↑ • H ↑ • S^ x⁻¹ ↑ • H ↑ • (S^ x ↑ • Ex) • H ≈⟨  cright cright cright cright assoc ⟩
    S^ x ↑ • H ↑ • S^ x⁻¹ ↑ • H ↑ • S^ x ↑ • Ex • H ≈⟨  cright cright cright cright cright sym (sym lemma-semi-Ex-H↓) ⟩
    S^ x ↑ • H ↑ • S^ x⁻¹ ↑ • H ↑ • S^ x ↑ • H ↑ • Ex ≈⟨ special-assoc (□ ^ 7) (□ ^ 6 • □) auto ⟩
    M m ↑ • Ex ∎
    where
    x = x' .proj₁
    x⁻¹ = ((x' ⁻¹) .proj₁ )
    open PB ((₂₊ n) QRel,_===_)
    open PP ((₂₊ n) QRel,_===_)
    open SR word-setoid
    open Pattern-Assoc
    open Basis-Change _ ((₂₊ n) QRel,_===_) grouplike


  lemma-semi-Mg↓-CZ :  let open PB ((₂₊ n) QRel,_===_) in
    Mg ↓ • CZ ≈ CZ^ g • Mg ↓
  lemma-semi-Mg↓-CZ {n} = bbc Ex ε (sym claim)
    where
    open PB ((₂₊ n) QRel,_===_)
    open PP ((₂₊ n) QRel,_===_)
    open SR word-setoid
    open Basis-Change _ ((₂₊ n) QRel,_===_) grouplike
    claim : Ex • (CZ^ g • Mg ↓) • ε ≈ Ex • (Mg ↓ • CZ) • ε
    claim = begin
      Ex • (CZ^ g • Mg ↓) • ε ≈⟨ cong refl right-unit ⟩
      Ex • (CZ^ g • Mg ↓) ≈⟨ sym assoc ⟩
      (Ex • CZ^ g) • Mg ↓ ≈⟨ (cleft word-comm 1 (toℕ g) (axiom comm-Ex-CZ)) ⟩
      (CZ^ g • Ex) • Mg ↓ ≈⟨ assoc ⟩
      CZ^ g • Ex • Mg ↓ ≈⟨ (cright lemma-Ex-M g*) ⟩
      CZ^ g • Mg ↑ • Ex ≈⟨ sym assoc ⟩
      (CZ^ g • Mg ↑) • Ex ≈⟨ cong (sym (axiom semi-M↑-CZ)) refl ⟩
      (Mg ↑ • CZ) • Ex ≈⟨ assoc ⟩
      Mg ↑ • CZ • Ex ≈⟨ cong refl (sym (axiom comm-Ex-CZ)) ⟩
      Mg ↑ • Ex • CZ ≈⟨ sym assoc ⟩
      (Mg ↑ • Ex) • CZ ≈⟨ (cleft sym (lemma-Ex-M g*)) ⟩
      (Ex • Mg ↓) • CZ ≈⟨ assoc ⟩
      Ex • (Mg ↓ • CZ) ≈⟨ sym (cong refl right-unit) ⟩
      Ex • (Mg ↓ • CZ) • ε ∎





-- ----------------------------------------------------------------------
-- * Data required for applying word tactics to Symplectic generators

module CommData-Alt where
  private
    variable
      n : ℕ

  open Alternative-Relations
  open Lemmas-Alt
  open Lemmas-Dual
  
  -- Commutativity.
  commute : (x y : Gen (₂₊ n)) → let open PB ((₂₊ n) QRel,_===_) in Maybe (([ x ]ʷ • [ y ]ʷ) ≈ ([ y ]ʷ • [ x ]ʷ))
  commute {n} H-gen (y ↥) = just (PB.sym (PB.axiom comm-H))
  commute {n} (x ↥) H-gen = just (PB.axiom comm-H)
  commute {n} S-gen (y ↥) = just (PB.sym (PB.axiom comm-S))
  commute {n} (x ↥) S-gen = just (PB.axiom comm-S)
  commute {n} S-gen CZ-gen = just (PB.sym lemma-comm-CZ-S↓)
  commute {n} CZ-gen S-gen = just lemma-comm-CZ-S↓
  commute {n} (S-gen ↥) CZ-gen = just (PB.sym (PB.axiom comm-CZ-S↑))
  commute {n} CZ-gen (S-gen ↥) = just (PB.axiom comm-CZ-S↑)
  
  commute {n@(suc n')} CZ-gen (CZ-gen ↥) = just (PB.sym (PB.axiom comm-CZ↑-CZ))
  commute {n} (CZ-gen ↥) CZ-gen = just (PB.axiom comm-CZ↑-CZ)
  
  commute {n@(suc n')} CZ-gen ((y ↥) ↥) = just (PB.sym (PB.axiom comm-CZ))
  commute {n@(suc n')} ((x ↥) ↥) CZ-gen = just (PB.axiom comm-CZ)
  
  commute {n@(suc n')} (x ↥) (y ↥) with commute x y
  ... | nothing = nothing
  ... | just eq = just (lemma-cong↑ ([ x ]ʷ • [ y ]ʷ) ([ y ]ʷ • [ x ]ʷ) eq)

  commute {n} _ _ = nothing


  -- We number the generators for the purpose of ordering them.
  ord : Gen (₁₊ n) → ℕ
  ord {n}(S-gen) = 0
  ord {n} (H-gen) = 1
  ord {suc n} (CZ-gen) = 2
  ord {suc n} (g ↥) = 3 Nat.+ ord g


  -- Ordering of generators.
  les : Gen (₂₊ n) → Gen (₂₊ n) → Bool
  les x y with ord x Nat.<? ord y
  les x y | yes _ = true
  les x y | no _ = false

module Commuting-Symplectic-Alt (n : ℕ) where
  open Alternative-Relations
  open CommData-Alt
  open Commuting (((₂₊ n) QRel,_===_) ) commute les public


module Rewriting-Alt where

  open Rewriting
  open Alternative-Relations
  open Lemmas-Dual
  open Lemmas-Alt
  private
    variable
      n : ℕ

  
  
  step-sym0 : let open PB ((₁₊ n) QRel,_===_) hiding (_===_) in Step-Function (Gen (₁₊ n))  ((₁₊ n) QRel,_===_)

  -- Order of generators.
  step-sym0 {n} ((H-gen) ∷ (H-gen) ∷ (H-gen) ∷ (H-gen) ∷ xs) = just (xs , at-head (lemma-order-H))
    where
    open Lemmas1 n
  step-sym0 {₁₊ n} ((H-gen ↥) ∷ (H-gen ↥) ∷ (H-gen ↥) ∷ (H-gen ↥) ∷ xs) = just (xs , at-head (lemma-cong↑ _ _ lemma-order-H))
    where
    open Lemmas1 n
    open Lemmas-Alt
  step-sym0 {₂₊ n} ((H-gen ↥ ↥) ∷ (H-gen ↥ ↥) ∷ (H-gen ↥ ↥) ∷ (H-gen ↥ ↥) ∷ xs) = just (xs , at-head (lemma-cong↑ _ _ (lemma-cong↑ _ _ lemma-order-H)))
    where
    open Lemmas1 n
    open Lemmas-Alt

  step-sym0 {n} ((S-gen) ∷ (H-gen) ∷ (S-gen) ∷ (H-gen) ∷ (S-gen) ∷ (H-gen) ∷ xs) = just (xs , at-head (lemma-order-SH))
    where
    open Lemmas1 n
  step-sym0 {₁₊ n} ((S-gen ↥) ∷ (H-gen ↥) ∷ (S-gen ↥) ∷ (H-gen ↥) ∷ (S-gen ↥) ∷ (H-gen ↥) ∷ xs) = just (xs , at-head (lemma-cong↑ _ _ lemma-order-SH))
    where
    open Lemmas1 n
    open Lemmas-Alt
  step-sym0 {₂₊ n} ((S-gen ↥ ↥) ∷ (H-gen ↥ ↥) ∷ (S-gen ↥ ↥) ∷ (H-gen ↥ ↥) ∷ (S-gen ↥ ↥) ∷ (H-gen ↥ ↥) ∷ xs) = just (xs , at-head (lemma-cong↑ _ _ (lemma-cong↑ _ _ lemma-order-SH)))
    where
    open Lemmas1 n
    open Lemmas-Alt

  -- Commuting of generators.
  step-sym0 ((S-gen) ∷ (CZ-gen) ∷ xs) = just ((CZ-gen) ∷ (S-gen) ∷ xs , at-head (PB.sym (lemma-comm-CZ-S↓)))
  step-sym0 ((S-gen ↥) ∷ (CZ-gen) ∷ xs) = just ((CZ-gen) ∷ (S-gen ↥) ∷ xs , at-head (PB.sym (PB.axiom comm-CZ-S↑)))
  step-sym0 ((S-gen ↥) ∷ (CZ-gen ↥) ∷ xs) = just ((CZ-gen ↥) ∷ (S-gen ↥) ∷ xs , at-head (PB.sym (lemma-cong↑ _ _  lemma-comm-CZ-S↓)))
  step-sym0 ((S-gen ↥ ↥) ∷ (CZ-gen ↥) ∷ xs) = just ((CZ-gen ↥) ∷ (S-gen ↥ ↥) ∷ xs , at-head (PB.sym (PB.axiom (cong↑ comm-CZ-S↑))))

  step-sym0 ((H-gen ↥ ↥) ∷ (CZ-gen) ∷ xs) = just ((CZ-gen) ∷ (H-gen ↥ ↥) ∷ xs , at-head (PB.axiom comm-CZ))
  step-sym0 ((S-gen ↥ ↥) ∷ (CZ-gen) ∷ xs) = just ((CZ-gen) ∷ (S-gen ↥ ↥) ∷ xs , at-head (PB.axiom comm-CZ))

  step-sym0 ((S-gen ↥) ∷ (S-gen) ∷ xs) = just ((S-gen) ∷ (S-gen ↥) ∷ xs , at-head ((PB.axiom comm-S)))
  step-sym0 ((S-gen ↥ ↥) ∷ (S-gen ↥) ∷ xs) = just ((S-gen ↥) ∷ (S-gen ↥ ↥) ∷ xs , at-head ((PB.axiom (cong↑ comm-S))))
  step-sym0 ((S-gen ↥ ↥) ∷ (S-gen) ∷ xs) = just ((S-gen) ∷ (S-gen ↥ ↥) ∷ xs , at-head (PB.axiom comm-S))
  step-sym0 ((S-gen ↥) ∷ (H-gen) ∷ xs) = just ((H-gen) ∷ (S-gen ↥) ∷ xs , at-head ((PB.axiom comm-H)))
  step-sym0 ((S-gen ↥ ↥) ∷ (H-gen ↥) ∷ xs) = just ((H-gen ↥) ∷ (S-gen ↥ ↥) ∷ xs , at-head ((PB.axiom (cong↑ comm-H))))
  step-sym0 ((S-gen ↥ ↥) ∷ (H-gen) ∷ xs) = just ((H-gen) ∷ (S-gen ↥ ↥) ∷ xs , at-head (PB.axiom comm-H))
  step-sym0 ((H-gen ↥) ∷ (H-gen) ∷ xs) = just ((H-gen) ∷ (H-gen ↥) ∷ xs , at-head ((PB.axiom comm-H)))
  step-sym0 ((H-gen ↥) ∷ (S-gen) ∷ xs) = just ((S-gen) ∷ (H-gen ↥) ∷ xs , at-head ((PB.axiom comm-S)))
  step-sym0 ((H-gen ↥ ↥) ∷ (H-gen ↥) ∷ xs) = just ((H-gen ↥) ∷ (H-gen ↥ ↥) ∷ xs , at-head ((PB.axiom (cong↑ comm-H))))
  step-sym0 ((H-gen ↥ ↥) ∷ (H-gen) ∷ xs) = just ((H-gen) ∷ (H-gen ↥ ↥) ∷ xs , at-head (PB.axiom comm-H))
  step-sym0 ((H-gen ↥ ↥) ∷ (S-gen ↥) ∷ xs) = just ((S-gen ↥) ∷ (H-gen ↥ ↥) ∷ xs , at-head ((PB.axiom (cong↑ comm-S))))
  step-sym0 ((H-gen ↥ ↥) ∷ (S-gen) ∷ xs) = just ((S-gen) ∷ (H-gen ↥ ↥) ∷ xs , at-head (PB.axiom comm-S))

  step-sym0 ((CZ-gen ↥ ↥) ∷ (H-gen ↥) ∷ xs) = just ((H-gen ↥) ∷ (CZ-gen ↥ ↥) ∷ xs , at-head ((PB.axiom (cong↑ comm-H))))
  step-sym0 ((CZ-gen ↥ ↥) ∷ (H-gen) ∷ xs) = just ((H-gen) ∷ (CZ-gen ↥ ↥) ∷ xs , at-head (PB.axiom comm-H))
  step-sym0 ((CZ-gen ↥ ↥) ∷ (S-gen ↥) ∷ xs) = just ((S-gen ↥) ∷ (CZ-gen ↥ ↥) ∷ xs , at-head ((PB.axiom (cong↑ comm-S))))
  step-sym0 ((CZ-gen ↥ ↥) ∷ (S-gen) ∷ xs) = just ((S-gen) ∷ (CZ-gen ↥ ↥) ∷ xs , at-head (PB.axiom comm-S))

  step-sym0 ((CZ-gen ↥ ↥) ∷ (CZ-gen) ∷ xs) = just ((CZ-gen) ∷ (CZ-gen ↥ ↥) ∷ xs , at-head ((PB.axiom comm-CZ)))
  step-sym0 ((CZ-gen ↥) ∷ (CZ-gen) ∷ xs) = just ((CZ-gen) ∷ (CZ-gen ↥) ∷ xs , at-head ((PB.axiom comm-CZ↑-CZ)))

  step-sym0 {n} ((S-gen) ∷ (H-gen) ∷ (H-gen) ∷ xs) = just ((H-gen) ∷ (H-gen) ∷ (S-gen) ∷ xs , at-head (PB.sym (lemma-comm-HHS)))
    where
    open Lemmas1b n
    open Lemmas-Alt
  step-sym0 {₁₊ n} ((S-gen ↥) ∷ (H-gen ↥) ∷ (H-gen ↥) ∷ xs) = just ((H-gen ↥) ∷ (H-gen ↥) ∷ (S-gen ↥) ∷ xs , at-head (PB.sym (lemma-cong↑ _ _ lemma-comm-HHS)))
    where
    open Lemmas1b n
    open Lemmas-Alt
  step-sym0 {₂₊ n} ((S-gen ↥ ↥) ∷ (H-gen ↥ ↥) ∷ (H-gen ↥ ↥) ∷ xs) = just ((H-gen ↥ ↥) ∷ (H-gen ↥ ↥) ∷ (S-gen ↥ ↥) ∷ xs , at-head (PB.sym (lemma-cong↑ _ _ (lemma-cong↑ _ _ lemma-comm-HHS))))
    where
    open Lemmas1b n
    open Lemmas-Alt

  -- Catch-all
  step-sym0 _ = nothing

module Alt-Rewriting (n : ℕ) where
  open Rewriting
  open Rewriting-Alt
  open Rewriting.Step (step-cong (step-sym0 {n})) renaming (general-rewrite to rewrite-sim) public



module Lemmas2 (n : ℕ) where

  open Alternative-Relations
  open Symplectic-Alt-GroupLike
  open Lemmas-Alt
  open Lemmas-Dual

  open PB ((₂₊ n) QRel,_===_) hiding (_===_)
  open PP ((₂₊ n) QRel,_===_)
  open Pattern-Assoc
  open import Data.Nat.DivMod
  open import Data.Fin.Properties
  module LL0 = Lemmas1 n
  module LLb0 = Lemmas1b n
  open Lemmas1 (₁₊ n)
  open Lemmas1b (₁₊ n)


  lemma-CZ^k-% : ∀ k -> CZ ^ k ≈ CZ ^ (k % p)
  lemma-CZ^k-% k = begin
    CZ ^ k ≡⟨ Eq.cong (CZ ^_) (m≡m%n+[m/n]*n k p) ⟩
    CZ ^ (k Nat.% p Nat.+ k Nat./ p Nat.* p) ≈⟨ lemma-^-+ CZ (k Nat.% p) (k Nat./ p Nat.* p) ⟩
    CZ ^ (k Nat.% p) • CZ ^ (k Nat./ p Nat.* p) ≈⟨ (cright refl' (Eq.cong (CZ ^_) (NP.*-comm (k Nat./ p) p))) ⟩
    CZ ^ (k Nat.% p) • CZ ^ (p Nat.* (k Nat./ p)) ≈⟨ sym (cright lemma-^^ CZ p (k Nat./ p)) ⟩
    CZ ^ (k Nat.% p) • (CZ ^ p) ^ (k Nat./ p) ≈⟨ (cright lemma-^-cong (CZ ^ p) ε (k Nat./ p) (axiom order-CZ)) ⟩
    CZ ^ (k Nat.% p) • (ε) ^ (k Nat./ p) ≈⟨ (cright lemma-ε^k=ε (k Nat./ p)) ⟩
    CZ ^ (k Nat.% p) • ε ≈⟨ right-unit ⟩
    CZ ^ (k % p) ∎
    where
    open SR word-setoid



  lemma-Mg↓CZ^k : ∀ k ->  let g⁻¹ = (g′ ⁻¹) .proj₁ in let -g⁻¹ = - g⁻¹ in
    Mg • CZ ^ k ≈ CZ ^ (k Nat.* toℕ g) • Mg
  lemma-Mg↓CZ^k k@0 = trans right-unit (sym left-unit)
  lemma-Mg↓CZ^k k@1 = begin  
    Mg • CZ ^ k ≈⟨ refl ⟩
    Mg • CZ ≈⟨ lemma-semi-Mg↓-CZ ⟩
    CZ^ g • Mg ≈⟨ refl ⟩
    CZ ^ toℕ g • Mg ≈⟨ (cleft refl' (Eq.cong (CZ ^_) (Eq.sym ( NP.*-identityˡ (toℕ g))))) ⟩
    CZ ^ (k Nat.* toℕ g) • Mg ∎
    where
    open SR word-setoid
  lemma-Mg↓CZ^k k@(₂₊ k') = begin  
    Mg • CZ ^ k ≈⟨ refl ⟩
    Mg • CZ • CZ ^ ₁₊ k' ≈⟨ sym assoc ⟩
    (Mg • CZ) • CZ ^ ₁₊ k' ≈⟨ (cleft lemma-Mg↓CZ^k 1 ) ⟩
    (CZ ^ (1 Nat.* toℕ g) • Mg) • CZ ^ ₁₊ k' ≈⟨ assoc ⟩
    CZ ^ (1 Nat.* toℕ g) • Mg • CZ ^ ₁₊ k' ≈⟨ (cright lemma-Mg↓CZ^k (₁₊ k')) ⟩
    CZ ^ (1 Nat.* toℕ g) • CZ ^ (₁₊ k' Nat.* toℕ g) • Mg ≈⟨ sym assoc ⟩
    (CZ ^ (1 Nat.* toℕ g) • CZ ^ (₁₊ k' Nat.* toℕ g)) • Mg ≈⟨ (cleft sym (lemma-^-+ CZ ((1 Nat.* toℕ g)) ((₁₊ k' Nat.* toℕ g)))) ⟩
    (CZ ^ ((1 Nat.* toℕ g) Nat.+ (₁₊ k' Nat.* toℕ g))) • Mg ≈⟨ (cleft refl' (Eq.cong (CZ ^_) (Eq.sym (NP.*-distribʳ-+ (toℕ g) ₁ (₁₊ k'))))) ⟩
    CZ ^ ((1 Nat.+ ₁₊ k') Nat.* toℕ g ) • Mg ≈⟨ refl ⟩
    CZ ^ (k Nat.* toℕ g) • Mg ∎
    where
    open SR word-setoid

  lemma-Mg↓CZ^k' : ∀ k -> let x⁻¹ = (g′ ⁻¹) .proj₁ in let -x⁻¹ = - x⁻¹ in
    Mg • CZ^ k ≈ CZ^ (k * g) • Mg
  lemma-Mg↓CZ^k' k = begin 
    Mg • CZ^ k ≈⟨ refl ⟩
    Mg • CZ ^ toℕ k ≈⟨ lemma-Mg↓CZ^k (toℕ k) ⟩
    CZ ^ (toℕ k Nat.* toℕ g) • Mg ≈⟨ (cleft lemma-CZ^k-% (toℕ k Nat.* toℕ g)) ⟩
    CZ ^ ((toℕ k Nat.* toℕ g) % p) • Mg ≈⟨ (cleft refl' (Eq.cong (CZ ^_) (lemma-toℕ-% k g))) ⟩
    CZ ^ toℕ (k * g) • Mg ≈⟨ refl ⟩
    CZ^ (k * g) • Mg ∎
    where
    open SR word-setoid
    x⁻¹ = (g′ ⁻¹) .proj₁
    -x⁻¹ = - x⁻¹

  lemma-Mg^kCZ : ∀ k -> Mg ^ k • CZ ≈ CZ^ (g ^′ k) • Mg ^ k
  lemma-Mg^kCZ k@0 = trans left-unit (sym right-unit)
  lemma-Mg^kCZ k@1 = begin
    Mg ^ k • CZ ≈⟨ lemma-semi-Mg↓-CZ ⟩
    CZ^ (g) • Mg ^ k ≈⟨ (cleft refl' (Eq.cong CZ^ (Eq.sym (lemma-x^′1=x g)))) ⟩
    CZ^ (g ^′ k) • Mg ^ k ∎
    where
    open SR word-setoid
  lemma-Mg^kCZ k@(₂₊ n) = begin
    (Mg • Mg ^ ₁₊ n) • CZ ≈⟨ assoc ⟩
    Mg • Mg ^ ₁₊ n • CZ ≈⟨ (cright lemma-Mg^kCZ (₁₊ n)) ⟩
    Mg • CZ^ (g ^′ (₁₊ n)) • Mg ^ (₁₊ n) ≈⟨ sym assoc ⟩
    (Mg • CZ^ (g ^′ (₁₊ n))) • Mg ^ (₁₊ n) ≈⟨ (cleft lemma-Mg↓CZ^k' (g ^′ (₁₊ n))) ⟩
    (CZ^ ((g ^′ (₁₊ n)) * g) • Mg) • Mg ^ (₁₊ n) ≈⟨ refl' (Eq.cong (\ xx -> (CZ^ xx • Mg) • Mg ^ (₁₊ n)) (*-comm (g ^′ (₁₊ n)) g)) ⟩
    (CZ^ (g * (g ^′ (₁₊ n))) • Mg) • Mg ^ (₁₊ n) ≈⟨ assoc ⟩
    CZ^ (g ^′ k) • Mg • Mg ^ ₁₊ n ∎
    where
    open SR word-setoid



  lemma-semi-M↓-CZ : ∀ x -> let x' = x .proj₁ in let k = g-gen x .proj₁ in M x • CZ ≈ CZ^ x' • M x
  lemma-semi-M↓-CZ x = begin
    M x • CZ ≈⟨ (cleft refl' (aux-M≡M x (g^ k) (eqk))) ⟩
    M (g^ k) • CZ ≈⟨ cong (sym (axiom (M-power (k)))) refl ⟩
    Mg^ k • CZ ≈⟨ lemma-Mg^kCZ (toℕ k) ⟩
    CZ^ (g ^′ toℕ k) • Mg^ k ≈⟨ (cright axiom (M-power (k))) ⟩
    CZ^ (g ^′ toℕ k) • M (g^ k) ≈⟨ (cleft refl' (Eq.cong CZ^ (Eq.sym eqk))) ⟩
    CZ^ (x') • M (g^ k) ≈⟨ (cright refl' (aux-M≡M (g^ k) x (Eq.sym (eqk)))) ⟩
    CZ^ (x') • M x ∎
    where
    open SR word-setoid
    x' = x .proj₁
    k = inject₁ (g-gen x .proj₁)
    eqk : x .proj₁ ≡ (g^ k) .proj₁
    eqk = Eq.sym (lemma-log-inject x)






  lemma-Mg↑CZ^k : ∀ k ->  let g⁻¹ = (g′ ⁻¹) .proj₁ in let -g⁻¹ = - g⁻¹ in
    Mg ↑ • CZ ^ k ≈ CZ ^ (k Nat.* toℕ g) • Mg ↑
  lemma-Mg↑CZ^k k@0 = trans right-unit (sym left-unit)
  lemma-Mg↑CZ^k k@1 = begin  
    Mg ↑ • CZ ^ k ≈⟨ refl ⟩
    Mg ↑ • CZ ≈⟨ axiom semi-M↑-CZ ⟩
    CZ^ g • Mg ↑ ≈⟨ refl ⟩
    CZ ^ toℕ g • Mg ↑ ≈⟨ (cleft refl' (Eq.cong (CZ ^_) (Eq.sym ( NP.*-identityˡ (toℕ g))))) ⟩
    CZ ^ (k Nat.* toℕ g) • Mg ↑ ∎
    where
    open SR word-setoid
  lemma-Mg↑CZ^k k@(₂₊ k') = begin  
    Mg ↑ • CZ ^ k ≈⟨ refl ⟩
    Mg ↑ • CZ • CZ ^ ₁₊ k' ≈⟨ sym assoc ⟩
    (Mg ↑ • CZ) • CZ ^ ₁₊ k' ≈⟨ (cleft lemma-Mg↑CZ^k 1 ) ⟩
    (CZ ^ (1 Nat.* toℕ g) • Mg ↑) • CZ ^ ₁₊ k' ≈⟨ assoc ⟩
    CZ ^ (1 Nat.* toℕ g) • Mg ↑ • CZ ^ ₁₊ k' ≈⟨ (cright lemma-Mg↑CZ^k (₁₊ k')) ⟩
    CZ ^ (1 Nat.* toℕ g) • CZ ^ (₁₊ k' Nat.* toℕ g) • Mg ↑ ≈⟨ sym assoc ⟩
    (CZ ^ (1 Nat.* toℕ g) • CZ ^ (₁₊ k' Nat.* toℕ g)) • Mg ↑ ≈⟨ (cleft sym (lemma-^-+ CZ ((1 Nat.* toℕ g)) ((₁₊ k' Nat.* toℕ g)))) ⟩
    (CZ ^ ((1 Nat.* toℕ g) Nat.+ (₁₊ k' Nat.* toℕ g))) • Mg ↑ ≈⟨ (cleft refl' (Eq.cong (CZ ^_) (Eq.sym (NP.*-distribʳ-+ (toℕ g) ₁ (₁₊ k'))))) ⟩
    CZ ^ ((1 Nat.+ ₁₊ k') Nat.* toℕ g ) • Mg ↑ ≈⟨ refl ⟩
    CZ ^ (k Nat.* toℕ g) • Mg ↑ ∎
    where
    open SR word-setoid

  lemma-Mg↑CZ^k' : ∀ k -> let x⁻¹ = (g′ ⁻¹) .proj₁ in let -x⁻¹ = - x⁻¹ in
    Mg ↑ • CZ^ k ≈ CZ^ (k * g) • Mg ↑
  lemma-Mg↑CZ^k' k = begin 
    Mg ↑ • CZ^ k ≈⟨ refl ⟩
    Mg ↑ • CZ ^ toℕ k ≈⟨ lemma-Mg↑CZ^k (toℕ k) ⟩
    CZ ^ (toℕ k Nat.* toℕ g) • Mg ↑ ≈⟨ (cleft lemma-CZ^k-% (toℕ k Nat.* toℕ g)) ⟩
    CZ ^ ((toℕ k Nat.* toℕ g) % p) • Mg ↑ ≈⟨ (cleft refl' (Eq.cong (CZ ^_) (lemma-toℕ-% k g))) ⟩
    CZ ^ toℕ (k * g) • Mg ↑ ≈⟨ refl ⟩
    CZ^ (k * g) • Mg ↑ ∎
    where
    open SR word-setoid
    x⁻¹ = (g′ ⁻¹) .proj₁
    -x⁻¹ = - x⁻¹

  lemma-Mg^k↑CZ : ∀ k -> Mg ↑ ^ k • CZ ≈ CZ^ (g ^′ k) • Mg ↑ ^ k
  lemma-Mg^k↑CZ k@0 = trans left-unit (sym right-unit)
  lemma-Mg^k↑CZ k@1 = begin
    Mg ↑ ^ k • CZ ≈⟨ axiom semi-M↑-CZ ⟩
    CZ^ (g) • Mg ↑ ^ k ≈⟨ (cleft refl' (Eq.cong CZ^ (Eq.sym (lemma-x^′1=x g)))) ⟩
    CZ^ (g ^′ k) • Mg ↑ ^ k ∎
    where
    open SR word-setoid
  lemma-Mg^k↑CZ k@(₂₊ n) = begin
    (Mg ↑ • Mg ↑ ^ ₁₊ n) • CZ ≈⟨ assoc ⟩
    Mg ↑ • Mg ↑ ^ ₁₊ n • CZ ≈⟨ (cright lemma-Mg^k↑CZ (₁₊ n)) ⟩
    Mg ↑ • CZ^ (g ^′ (₁₊ n)) • Mg ↑ ^ (₁₊ n) ≈⟨ sym assoc ⟩
    (Mg ↑ • CZ^ (g ^′ (₁₊ n))) • Mg ↑ ^ (₁₊ n) ≈⟨ (cleft lemma-Mg↑CZ^k' (g ^′ (₁₊ n))) ⟩
    (CZ^ ((g ^′ (₁₊ n)) * g) • Mg ↑) • Mg ↑ ^ (₁₊ n) ≈⟨ refl' (Eq.cong (\ xx -> (CZ^ xx • Mg ↑) • Mg ↑ ^ (₁₊ n)) (*-comm (g ^′ (₁₊ n)) g)) ⟩
    (CZ^ (g * (g ^′ (₁₊ n))) • Mg ↑) • Mg ↑ ^ (₁₊ n) ≈⟨ assoc ⟩
    CZ^ (g ^′ k) • Mg ↑ • Mg ↑ ^ ₁₊ n ∎
    where
    open SR word-setoid



  lemma-semi-M↑-CZ : ∀ x -> let x' = x .proj₁ in let k = g-gen x .proj₁ in M x ↑ • CZ ≈ CZ^ x' • M x ↑ 
  lemma-semi-M↑-CZ x = begin
    M x ↑ • CZ ≈⟨ (cleft (lemma-cong↑ _ _ ((aux-MM (x .proj₂) (((g^ k) .proj₂))  ( (eqk)))))) ⟩
    M (g^ k) ↑ • CZ ≈⟨ cong (sym (axiom (cong↑ (M-power (k))))) refl ⟩
    (Mg ^ toℕ k) ↑ • CZ ≈⟨ (cleft refl' (lemma-↑^ (toℕ k) Mg)) ⟩
    Mg ↑ ^ toℕ k • CZ ≈⟨ lemma-Mg^k↑CZ (toℕ k) ⟩
    CZ^ (g ^′ toℕ k) • Mg ↑ ^ toℕ k ≈⟨ (cright sym (refl' (lemma-↑^ (toℕ k) Mg))) ⟩
    CZ^ (g ^′ toℕ k) • (Mg ^ toℕ k) ↑ ≈⟨ (cright axiom (cong↑ (M-power (k)))) ⟩
    CZ^ (g ^′ toℕ k) • M (g^ k) ↑ ≈⟨ (cleft refl' (Eq.cong CZ^ (Eq.sym eqk))) ⟩
    CZ^ (x') • M (g^ k) ↑ ≈⟨ (cright (lemma-cong↑ _ _ ((aux-MM (((g^ k) .proj₂)) (x .proj₂) (Eq.sym (eqk)))))) ⟩
    CZ^ (x') • M x ↑ ∎
    where
    open Lemmas-Alt
    open SR word-setoid
    x' = x .proj₁
    k = inject₁ (g-gen x .proj₁)
    eqk : x .proj₁ ≡ (g^ k) .proj₁
    eqk = Eq.sym (lemma-log-inject x)



module Lemmas0b (n : ℕ) where

  open Alternative-Relations
  open Symplectic-Alt-GroupLike

  open PB ((₁₊ n) QRel,_===_) hiding (_===_)
  open PP ((₁₊ n) QRel,_===_)
  open Pattern-Assoc
  open import Data.Nat.DivMod
  open import Data.Fin.Properties
  open Lemmas1 n
  open Lemmas1b n


  lemma-S^k+l : ∀ k l -> S^ k • S^ l ≈ S^ (k + l)
  lemma-S^k+l k l = begin
    S^ k • S^ l ≈⟨ refl ⟩
    S ^ toℕ k • S ^ toℕ l ≈⟨ sym (lemma-^-+ S (toℕ k) (toℕ l)) ⟩
    S ^ (toℕ k Nat.+ toℕ l) ≡⟨ Eq.cong (S ^_) (m≡m%n+[m/n]*n k+l p) ⟩
    S ^ (k+l Nat.% p Nat.+ (k+l Nat./ p) Nat.* p) ≈⟨ lemma-^-+ S (k+l Nat.% p) (((k+l Nat./ p) Nat.* p)) ⟩
    S ^ (k+l Nat.% p) • S ^ ((k+l Nat./ p) Nat.* p) ≈⟨ cong (refl' (Eq.cong (S ^_) (Eq.sym (toℕ-fromℕ< (m%n<n k+l p))))) (refl' (Eq.cong (S ^_) (NP.*-comm ((k+l Nat./ p)) p))) ⟩
    S ^ toℕ (fromℕ< (m%n<n k+l p)) • S ^ (p Nat.* (k+l Nat./ p) ) ≈⟨ cong (sym (refl)) (sym (lemma-^^ S p (k+l Nat./ p))) ⟩
    S^ (k + l) • (S ^ p) ^ (k+l Nat./ p) ≈⟨ cright (lemma-^-cong (S ^ p) ε (k+l Nat./ p) (axiom order-S)) ⟩
    S^ (k + l) • ε ^ (k+l Nat./ p) ≈⟨ cright lemma-ε^k=ε (k+l Nat./ p) ⟩
    S^ (k + l) • ε ≈⟨ right-unit ⟩
    S^ (k + l) ∎
    where
    k+l = toℕ k Nat.+ toℕ l
    open SR word-setoid


  lemma-S^k-k : ∀ k -> S^ k • S^ (- k) ≈ ε
  lemma-S^k-k k = begin
    S^ k • S^ (- k) ≈⟨ lemma-S^k+l k (- k) ⟩
    S^ (k + - k) ≡⟨ Eq.cong S^ (+-inverseʳ k) ⟩
    S^ ₀ ≈⟨ refl ⟩
    ε ∎
    where
    open SR word-setoid
    k-k = toℕ k Nat.+ toℕ (- k)

  lemma-S^-k+k : ∀ k -> S^ (- k) • S^ k ≈ ε
  lemma-S^-k+k k = begin
    S^ (- k) • S^ k ≈⟨ refl ⟩
    S ^ toℕ (- k) • S ^ toℕ k ≈⟨ word-comm (toℕ (- k)) (toℕ ( k)) refl ⟩
    S ^ toℕ k • S ^ toℕ (- k) ≈⟨ refl ⟩
    S^ k • S^ (- k) ≈⟨ lemma-S^k-k k ⟩
    ε ∎
    where
    open SR word-setoid

  open Eq using (_≢_)



  lemma-HH-M-1 : let -'₁ = -' ((₁ , λ ())) in HH ≈ M -'₁
  lemma-HH-M-1 = begin
    HH ≈⟨ trans (sym right-unit) (cright sym lemma-[S⁻¹H⁻¹]^3) ⟩
    HH • (S⁻¹ • H⁻¹) ^ 3 ≈⟨ (cright lemma-^-cong (S⁻¹ • H⁻¹) (S⁻¹ • H • HH) 3 refl) ⟩
    HH • (S⁻¹ • H • HH) ^ 3 ≈⟨ refl ⟩
    HH • (S⁻¹ • H • HH) • (S⁻¹ • H • HH) • (S⁻¹ • H • HH) ≈⟨ (cright cong (cright sym assoc) (special-assoc (□ ^ 3 • □ ^ 3) (□ ^ 2 • □ ^ 2 • □ ^ 2) auto)) ⟩
    HH • (S⁻¹ • HH • H) • (S⁻¹ • H) • (HH • S⁻¹) • H • HH ≈⟨ (cright cong (sym assoc) (cright cleft word-comm 1 p-1 (trans assoc (lemma-comm-HHS)))) ⟩
    HH • ((S⁻¹ • HH) • H) • (S⁻¹ • H) • (S⁻¹ • HH) • H • HH ≈⟨ (cright cong (cleft word-comm p-1 1 (sym (trans assoc (lemma-comm-HHS)))) (cright assoc)) ⟩
    HH • ((HH • S⁻¹) • H) • (S⁻¹ • H) • S⁻¹ • HH • H • HH ≈⟨ (cright cright cright cright rewrite-sim 100 auto) ⟩
    HH • ((HH • S⁻¹) • H) • (S⁻¹ • H) • S⁻¹ • H ≈⟨ special-assoc (□ • (□ ^ 2 • □) • □) (□ ^ 2 • □ ^ 2 • □) auto ⟩
    (HH • HH) • (S⁻¹ • H) • (S⁻¹ • H) • S⁻¹ • H ≈⟨ (cleft rewrite-sim 100 auto) ⟩
    ε • (S⁻¹ • H) • (S⁻¹ • H) • S⁻¹ • H ≈⟨ left-unit ⟩
    (S⁻¹ • H) • (S⁻¹ • H) • S⁻¹ • H ≈⟨ special-assoc ((□ ^ 2) ^ 3) (□ ^ 6) auto ⟩
    S⁻¹ • H • S⁻¹ • H • S⁻¹ • H ≈⟨ cong lemma-S⁻¹ (cright cong lemma-S⁻¹ (cright cong lemma-S⁻¹ refl)) ⟩
    S^ ₚ₋₁ • H • S^ ₚ₋₁ • H • S^ ₚ₋₁ • H ≡⟨ Eq.cong (\ xx -> S^ ₚ₋₁ • H • S^ ₚ₋₁ • H • S^ xx • H) p-1=-1ₚ ⟩
    S^ ₚ₋₁ • H • S^ ₚ₋₁ • H • S^ -₁ • H ≡⟨ Eq.cong₂ (\ xx yy -> S^ xx • H • S^ yy • H • S^ -₁ • H) (p-1=-1ₚ) p-1=-1ₚ ⟩
    S^ -₁ • H • S^ -₁ • H • S^ -₁ • H ≡⟨ Eq.cong (\ xx -> S^ -₁ • H • S^ xx • H • S^ -₁ • H) (Eq.sym aux-₁⁻¹) ⟩
    S^ -₁ • H • S^ -₁⁻¹ • H • S^ -₁ • H ≈⟨ refl ⟩
    S^ x • H • S^ x⁻¹ • H • S^ x • H ≡⟨ Eq.refl ⟩
    M x' ∎
    where
    open Alt-Rewriting n


    x' = -'₁
    -₁ = -'₁ .proj₁
    -₁⁻¹ = (-'₁ ⁻¹) .proj₁
    x = x' .proj₁
    x⁻¹ = (x' ⁻¹) .proj₁
    open SR word-setoid



  derived-D : ∀ x -> (nz : x ≢ ₀) -> let x⁻¹ = ((x , nz) ⁻¹) .proj₁ in let -x⁻¹ = - x⁻¹ in
    H • S^ x • H ≈ H • S^ x • H • S^ x⁻¹ • H • H ^ 3 • S^ -x⁻¹
  derived-D  x nz = begin
    H • S^ x • H ≈⟨ (cright cright sym right-unit) ⟩
    H • S^ x • H • ε ≈⟨ cright cright cright sym (lemma-S^k-k x⁻¹) ⟩
    H • S^ x • H • S^ x⁻¹ • S^ -x⁻¹ ≈⟨ cright cright cright cright sym left-unit ⟩
    H • S^ x • H • S^ x⁻¹ • ε • S^ -x⁻¹ ≈⟨ cright cright cright cright sym (cong (lemma-order-H) refl) ⟩
    H • S^ x • H • S^ x⁻¹ • H ^ 4 • S^ -x⁻¹ ≈⟨ (cright cright cright cright special-assoc (□ ^ 4 • □) (□ • □ ^ 3 • □) auto) ⟩
    H • S^ x • H • S^ x⁻¹ • H • H ^ 3 • S^ -x⁻¹ ∎
    where
    x⁻¹ = ((x , nz) ⁻¹) .proj₁
    -x⁻¹ = - x⁻¹ 
    open SR word-setoid



  lemma-MS^k' : ∀ x k -> (nz : x ≢ ₀) -> let x⁻¹ = ((x , nz) ⁻¹) .proj₁ in let -x⁻¹ = - x⁻¹ in
    M (x , nz) • S^ (k * (x⁻¹ * x⁻¹)) ≈ S^ k • M (x , nz)
  lemma-MS^k' x k nz = begin 
    M (x , nz) • S^ (k * (x⁻¹ * x⁻¹)) ≈⟨ lemma-MS^k x (k * (x⁻¹ * x⁻¹)) nz ⟩
    S^ (k * (x⁻¹ * x⁻¹) * (x * x)) • M (x , nz) ≈⟨ (cleft refl' (Eq.cong S^ (Eq.trans (*-assoc k (x⁻¹ * x⁻¹)  (x * x)) (Eq.cong (k *_) (aux-xxxx (x , nz)))))) ⟩
    S^ (k * ₁) • M (x , nz) ≈⟨ (cleft refl' (Eq.cong S^ (*-identityʳ k))) ⟩
    S^ k • M (x , nz) ∎
    where
    open SR word-setoid
    x⁻¹ = ((x , nz) ⁻¹) .proj₁
    -x⁻¹ = - x⁻¹


  lemma-S^ab : ∀ (a b : ℤ ₚ) -> S ^ toℕ (a * b) ≈ S ^ (toℕ a Nat.* toℕ b)
  lemma-S^ab a b = begin
    S ^ toℕ (a * b) ≡⟨ auto ⟩
    S ^ toℕ (fromℕ< (m%n<n (toℕ a Nat.* toℕ b) p)) ≡⟨ Eq.cong (S ^_) (toℕ-fromℕ< (m%n<n (toℕ a Nat.* toℕ b) p)) ⟩
    S ^ ((toℕ a Nat.* toℕ b) % p) ≈⟨ sym right-unit ⟩
    S ^ (ab Nat.% p) • ε ≈⟨ (cright sym (lemma-ε^k=ε (ab Nat./ p))) ⟩
    S ^ (ab Nat.% p) • (ε) ^ (ab Nat./ p) ≈⟨ (cright sym (lemma-^-cong (S ^ p) ε (ab Nat./ p) (axiom order-S))) ⟩
    S ^ (ab Nat.% p) • (S ^ p) ^ (ab Nat./ p) ≈⟨ (cright lemma-^^ S p (ab Nat./ p)) ⟩
    S ^ (ab Nat.% p) • S ^ (p Nat.* (ab Nat./ p)) ≈⟨ (cright refl' (Eq.cong (S ^_) (NP.*-comm p (ab Nat./ p)))) ⟩
    S ^ (ab Nat.% p) • S ^ (ab Nat./ p Nat.* p) ≈⟨ sym (lemma-^-+ S (ab Nat.% p) (ab Nat./ p Nat.* p)) ⟩
    S ^ (ab Nat.% p Nat.+ ab Nat./ p Nat.* p) ≡⟨ Eq.cong (S ^_) (Eq.sym (m≡m%n+[m/n]*n ab p)) ⟩
    S ^ (toℕ a Nat.* toℕ b) ∎
    where
    ab = toℕ a Nat.* toℕ b
    open SR word-setoid


  derived-7 : ∀ x y -> (nz : x ≢ ₀) -> (nzy : y ≢ ₀) -> let -'₁ = -' ((₁ , λ ())) in let x⁻¹ = ((x , nz) ⁻¹) .proj₁ in let -x⁻¹ = - x⁻¹ in let -y/x' = (((y , nzy) *' ((x , nz) ⁻¹)) *' -'₁) in let -y/x = -y/x' .proj₁ in
  
    M (y , nzy) • H • S^ x • H ≈ S^ (-x⁻¹ * (y * y)) • M -y/x' • (H • S^ -x⁻¹)
    
  derived-7 x y nzx nzy = begin
    M (y , nzy) • H • S^ x • H ≈⟨ (cright derived-D x nzx) ⟩
    M (y , nzy) • H • S^ x • H • S^ x⁻¹ • H • H ^ 3 • S^ -x⁻¹ ≈⟨ (cright special-assoc (□ • □ • □ • □ • □ • □ • □) (□ ^ 5 • □ • □) auto) ⟩
    M (y , nzy) • (H • S^ x • H • S^ x⁻¹ • H) • H ^ 3 • S^ -x⁻¹ ≈⟨ (cright cleft sym left-unit) ⟩
    M (y , nzy) • (ε • H • S^ x • H • S^ x⁻¹ • H) • H ^ 3 • S^ -x⁻¹ ≈⟨ (cright cleft cleft sym (lemma-S^-k+k x⁻¹)) ⟩
    M (y , nzy) • ((S^ -x⁻¹ • S^ x⁻¹) • H • S^ x • H • S^ x⁻¹ • H) • H ^ 3 • S^ -x⁻¹ ≈⟨ special-assoc (□ • (□ ^ 2 • □ ^ 5) • □) (□ ^ 2 • □ ^ 6 • □) auto ⟩
    (M (y , nzy) • S^ -x⁻¹) • (S^ x⁻¹ • H • S^ x • H • S^ x⁻¹ • H) • H ^ 3 • S^ -x⁻¹ ≈⟨ refl ⟩
    (M (y , nzy) • S ^ toℕ -x⁻¹) • (S^ x⁻¹ • H • S^ x • H • S^ x⁻¹ • H) • H ^ 3 • S^ -x⁻¹ ≈⟨ (cleft derived-5 y (toℕ -x⁻¹) nzy) ⟩
    (S ^ (toℕ -x⁻¹ Nat.* toℕ (y * y)) • M (y , nzy)) • (S^ x⁻¹ • H • S^ x • H • S^ x⁻¹ • H) • H ^ 3 • S^ -x⁻¹ ≈⟨ special-assoc (□ ^ 2 • □ ^ 2) (□ • □ ^ 2 • □) auto ⟩
    S ^ (toℕ -x⁻¹ Nat.* toℕ (y * y)) • (M (y , nzy) • (S^ x⁻¹ • H • S^ x • H • S^ x⁻¹ • H)) • H ^ 3 • S^ -x⁻¹ ≈⟨ (cright cleft (cright (cright cright cleft refl' (Eq.cong S^ (Eq.sym (inv-involutive ((x , nz)))))))) ⟩
    S ^ (toℕ -x⁻¹ Nat.* toℕ (y * y)) • (M (y , nzy) • M ((x , nz) ⁻¹)) • H ^ 3 • S^ -x⁻¹ ≈⟨ (cright cleft (lemma-M-mul (y , nzy) ((x , nz) ⁻¹))) ⟩
    S ^ (toℕ -x⁻¹ Nat.* toℕ (y * y)) • M ((y , nzy) *' ((x , nz) ⁻¹)) • H ^ 3 • S^ -x⁻¹ ≈⟨ (cright special-assoc (□ • □ ^ 3 • □) (□ ^ 3 • □ ^ 2) auto) ⟩
    S ^ (toℕ -x⁻¹ Nat.* toℕ (y * y)) • (M ((y , nzy) *' ((x , nz) ⁻¹)) • HH) • H • S^ -x⁻¹ ≈⟨ (cright cleft (cright lemma-HH-M-1)) ⟩
    S ^ (toℕ -x⁻¹ Nat.* toℕ (y * y)) • (M ((y , nzy) *' ((x , nz) ⁻¹)) • M -'₁) • H • S^ -x⁻¹ ≈⟨ (cright cleft (lemma-M-mul (((y , nzy) *' ((x , nz) ⁻¹))) -'₁)) ⟩
    S ^ (toℕ -x⁻¹ Nat.* toℕ (y * y)) • (M (((y , nzy) *' ((x , nz) ⁻¹)) *' -'₁) ) • H • S^ -x⁻¹ ≈⟨ (cleft sym (lemma-S^ab -x⁻¹ (y * y))) ⟩
    S ^ toℕ (-x⁻¹ * (y * y)) • M -y/x' • (H • S^ -x⁻¹) ≈⟨ refl ⟩
    S^ (-x⁻¹ * (y * y)) • M -y/x' • (H • S^ -x⁻¹) ∎
    where
    open SR word-setoid
    nz = nzx
    x⁻¹ = ((x , nz) ⁻¹) .proj₁
    x⁻¹⁻¹ = (((x , nz) ⁻¹) ⁻¹) .proj₁
    -x⁻¹ = - x⁻¹
    -y/x' = (((y , nzy) *' ((x , nz) ⁻¹)) *' -'₁)
    -y/x = -y/x' .proj₁

  aux-MM : ∀ {x y : ℤ ₚ} (nzx : x ≢ ₀) (nzy : y ≢ ₀) -> x ≡ y -> M (x , nzx) ≈ M (y , nzy)
  aux-MM {x} {y} nz1 nz2 eq rewrite eq = refl


  aux-M-mul : ∀ m -> M m • M (m ⁻¹) ≈ ε
  aux-M-mul m = begin
    M m • M (m ⁻¹) ≈⟨ (lemma-M-mul m ( m ⁻¹)) ⟩
    M (m *' m ⁻¹) ≈⟨ aux-MM ((m *' m ⁻¹) .proj₂) (λ ()) (lemma-⁻¹ʳ (m ^1) {{nztoℕ {y = m ^1} {neq0 = m .proj₂}}}) ⟩
    M₁ ≈⟨ lemma-M1 ⟩
    ε ∎
    where
    open SR word-setoid

  aux-M-mulˡ : ∀ m -> M (m ⁻¹) • M m ≈ ε
  aux-M-mulˡ m = begin
    M (m ⁻¹) • M m ≈⟨ (lemma-M-mul ( m ⁻¹) m) ⟩
    M (m ⁻¹ *' m) ≈⟨ aux-MM ((m ⁻¹ *' m) .proj₂) (λ ()) (lemma-⁻¹ˡ (m ^1) {{nztoℕ {y = m ^1} {neq0 = m .proj₂}}}) ⟩
    M₁ ≈⟨ lemma-M1 ⟩
    ε ∎
    where
    open SR word-setoid



  semi-HM : ∀ (x : ℤ* ₚ) -> H • M x ≈ M (x ⁻¹) • H
  semi-HM x' = begin
    H • (S^ x • H • S^ x⁻¹ • H • S^ x • H) ≈⟨ special-assoc (□ • □ ^ 6) (□ ^ 3 • □ ^ 4) auto ⟩
    (H • S^ x • H) • S^ x⁻¹ • H • S^ x • H ≈⟨ (trans (sym left-unit) (cong (sym lemma-M1) refl)) ⟩
    M₁ • (H • S^ x • H) • S^ x⁻¹ • H • S^ x • H ≈⟨ sym assoc ⟩
    (M₁ • (H • S^ x • H)) • S^ x⁻¹ • H • S^ x • H ≈⟨ (cleft derived-7 x ₁ (x' .proj₂) λ ()) ⟩
    (S^ (-x⁻¹ * (₁ * ₁)) • M (((₁ , λ ()) *' x' ⁻¹) *' -'₁) • H • S^ -x⁻¹) • S^ x⁻¹ • H • S^ x • H ≈⟨ cleft (cright (cleft aux-MM ((((₁ , λ ()) *' x' ⁻¹) *' -'₁) .proj₂) ((-' (x' ⁻¹)) .proj₂) aux-a1)) ⟩
    (S^ (-x⁻¹ * ₁) • M (-' (x' ⁻¹)) • H • S^ -x⁻¹) • S^ x⁻¹ • H • S^ x • H ≈⟨ special-assoc (□ ^ 4 • □ ^ 4) (□ • □ ^ 4 • □ ^ 3) auto ⟩
    S^ (-x⁻¹ * ₁) • (M (-' (x' ⁻¹)) • H • S^ -x⁻¹ • S^ x⁻¹) • H • S^ x • H ≈⟨ cong (refl' (Eq.cong S^ (*-identityʳ -x⁻¹))) (cleft cright (cright lemma-S^-k+k x⁻¹)) ⟩
    S^ -x⁻¹ • (M (-' (x' ⁻¹)) • H • ε) • H • S^ x • H ≈⟨ (cright cleft (cright right-unit)) ⟩
    S^ -x⁻¹ • (M (-' (x' ⁻¹)) • H) • H • S^ x • H ≈⟨ (cright special-assoc (□ ^ 2 • □ ^ 3) (□ ^ 3 • □ ^ 2) auto) ⟩
    S^ -x⁻¹ • (M (-' (x' ⁻¹)) • H • H) • S^ x • H ≈⟨ (cright cleft cright lemma-HH-M-1) ⟩
    S^ -x⁻¹ • (M (-' (x' ⁻¹)) • M -'₁) • S^ x • H ≈⟨ (cright cleft (lemma-M-mul (-' (x' ⁻¹)) -'₁)) ⟩
    S^ -x⁻¹ • M (-' (x' ⁻¹) *' -'₁) • S^ x • H ≈⟨ (cright cleft aux-MM ((-' (x' ⁻¹) *' -'₁) .proj₂) ((x' ⁻¹) .proj₂) aux-a2) ⟩
    S^ -x⁻¹ • M (x' ⁻¹) • S^ x • H ≈⟨ sym (cong refl assoc) ⟩
    S^ -x⁻¹ • (M (x' ⁻¹) • S^ x) • H ≈⟨ (cright cleft lemma-MS^k x⁻¹ x ((x' ⁻¹) .proj₂)) ⟩
    S^ -x⁻¹ • (S^ (x * (x⁻¹ * x⁻¹)) • M (x' ⁻¹)) • H ≈⟨ (cright cleft (cleft refl' (Eq.cong S^ aux-a3))) ⟩
    S^ -x⁻¹ • (S^ x⁻¹ • M (x' ⁻¹)) • H ≈⟨ special-assoc (□ • □ ^ 2 • □) (□ ^ 2 • □ ^ 2) auto ⟩
    (S^ -x⁻¹ • S^ x⁻¹) • M (x' ⁻¹) • H ≈⟨ (cleft lemma-S^-k+k x⁻¹) ⟩
    ε • M (x' ⁻¹) • H ≈⟨ left-unit ⟩
    M (x' ⁻¹) • H ∎
    where
    x = x' .proj₁
    x⁻¹ = ((x' ⁻¹) .proj₁ )
    open Pattern-Assoc
    -x = - x
    -x⁻¹ = - x⁻¹
    aux-a1 : ₁ * x⁻¹ * (-'₁ .proj₁) ≡ -x⁻¹
    aux-a1 = begin
      ₁ * x⁻¹ * (-'₁ .proj₁) ≡⟨ Eq.cong (\ xx -> xx * (-'₁ .proj₁)) (*-identityˡ x⁻¹) ⟩
      x⁻¹ * (-'₁ .proj₁) ≡⟨ Eq.cong (x⁻¹ *_) (Eq.sym p-1=-1ₚ) ⟩
      x⁻¹ * ₋₁ ≡⟨ *-comm x⁻¹ ₋₁ ⟩
      ₋₁ * x⁻¹ ≡⟨ auto ⟩
      -x⁻¹ ∎
      where open ≡-Reasoning

    aux-a2 : -x⁻¹ * - ₁ ≡ x⁻¹
    aux-a2 = begin
      -x⁻¹ * - ₁ ≡⟨ *-comm -x⁻¹ (- ₁) ⟩
      - ₁ * -x⁻¹ ≡⟨ -1*x≈-x -x⁻¹ ⟩
      - -x⁻¹ ≡⟨ -‿involutive x⁻¹ ⟩
      x⁻¹ ∎
      where
      open ≡-Reasoning
      open import Algebra.Properties.Ring (+-*-ring p-2)


    aux-a3 : x * (x⁻¹ * x⁻¹) ≡ x⁻¹
    aux-a3 = begin
      x * (x⁻¹ * x⁻¹) ≡⟨ Eq.sym (*-assoc x x⁻¹ x⁻¹) ⟩
      x * x⁻¹ * x⁻¹ ≡⟨ Eq.cong (_* x⁻¹) (lemma-⁻¹ʳ x {{nztoℕ {y = x} {neq0 = x' .proj₂}}}) ⟩
      ₁ * x⁻¹ ≡⟨ *-identityˡ x⁻¹ ⟩
      x⁻¹ ∎
      where open ≡-Reasoning

    open SR word-setoid

  aux-comm-MM' : ∀ m m' -> M m • M m' ≈ M m' • M m
  aux-comm-MM' m m' = begin
    M m • M m' ≈⟨ (lemma-M-mul m m') ⟩
    M (m *' m') ≈⟨ aux-MM ((m *' m') .proj₂) ((m' *' m) .proj₂) (*-comm (m .proj₁) (m' .proj₁)) ⟩
    M (m' *' m) ≈⟨ sym ((lemma-M-mul m' m)) ⟩
    M m' • M m ∎
    where
    open SR word-setoid
    
  aux-comm-HHM : ∀ m -> HH • M m ≈ M m • HH
  aux-comm-HHM m = begin
    HH • M m ≈⟨ (cleft lemma-HH-M-1) ⟩
    M -'₁ • M m ≈⟨ aux-comm-MM' -'₁ m ⟩
    M m • M -'₁ ≈⟨ (cright sym lemma-HH-M-1) ⟩
    M m • HH ∎
    where
    open SR word-setoid

  lemma-S^kM : ∀ x k -> (nz : x ≢ ₀) ->
    let
    x⁻¹ = ((x , nz) ⁻¹) .proj₁
    -x⁻¹ = - x⁻¹
    x⁻² = x⁻¹ * x⁻¹
    in
    S^ k • M (x , nz) ≈ M (x , nz) • S^ (k * x⁻²)
  lemma-S^kM x k nz = bbc (M ((x , nz) ⁻¹)) (M ((x , nz) ⁻¹)) aux
    where
    open Basis-Change _ ((₁₊ n) QRel,_===_) grouplike
    open SR word-setoid
    x⁻¹ = ((x , nz) ⁻¹) .proj₁
    -x⁻¹ = - x⁻¹
    x⁻² = x⁻¹ * x⁻¹
    aux : M ((x , nz) ⁻¹) • (S^ k • M (x , nz)) • M ((x , nz) ⁻¹) ≈ M ((x , nz) ⁻¹) • (M (x , nz) • S^ (k * x⁻²)) • M ((x , nz) ⁻¹)
    aux = begin
      M ((x , nz) ⁻¹) • (S^ k • M (x , nz)) • M ((x , nz) ⁻¹) ≈⟨ cong refl assoc ⟩
      M ((x , nz) ⁻¹) • S^ k • M (x , nz) • M ((x , nz) ⁻¹) ≈⟨ sym assoc ⟩
      (M ((x , nz) ⁻¹) • S^ k) • M (x , nz) • M ((x , nz) ⁻¹) ≈⟨ (cleft lemma-MS^k x⁻¹ k (((x , nz) ⁻¹) .proj₂)) ⟩
      (S^ (k * x⁻²) • M ((x , nz) ⁻¹)) • M (x , nz) • M ((x , nz) ⁻¹) ≈⟨ assoc ⟩
      S^ (k * x⁻²) • M ((x , nz) ⁻¹) • M (x , nz) • M ((x , nz) ⁻¹) ≈⟨ (cright sym assoc) ⟩
      S^ (k * x⁻²) • (M ((x , nz) ⁻¹) • M (x , nz)) • M ((x , nz) ⁻¹) ≈⟨  (cright cleft (aux-M-mulˡ (x , nz))) ⟩
      S^ (k * x⁻²) • ε • M ((x , nz) ⁻¹) ≈⟨ cong refl left-unit ⟩
      S^ (k * x⁻²) • M ((x , nz) ⁻¹) ≈⟨ sym left-unit ⟩
      ε • S^ (k * x⁻²) • M ((x , nz) ⁻¹) ≈⟨ (cleft sym ((aux-M-mulˡ (x , nz)))) ⟩
      (M ((x , nz) ⁻¹) • M (x , nz)) • S^ (k * x⁻²) • M ((x , nz) ⁻¹) ≈⟨ assoc ⟩
      M ((x , nz) ⁻¹) • M (x , nz) • S^ (k * x⁻²) • M ((x , nz) ⁻¹) ≈⟨ sym (cong refl assoc) ⟩
      M ((x , nz) ⁻¹) • (M (x , nz) • S^ (k * x⁻²)) • M ((x , nz) ⁻¹) ∎


  aux-H³M : ∀ m* -> H ^ 3 • M m* ≈ M (m* ⁻¹) • H ^ 3
  aux-H³M m*  = begin
    H ^ 3 • M m* ≈⟨ special-assoc (□ ^ 3 • □) (□ ^ 2 • □ ^ 2 ) auto ⟩
    H ^ 2 • H • M m* ≈⟨ cright semi-HM m* ⟩
    H ^ 2 • M (m* ⁻¹) • H ≈⟨ sym assoc ⟩
    (H ^ 2 • M (m* ⁻¹)) • H ≈⟨ cleft aux-comm-HHM (m* ⁻¹) ⟩
    (M (m* ⁻¹) • H ^ 2) • H ≈⟨ trans assoc (cong refl assoc) ⟩
    M (m* ⁻¹) • H ^ 3 ∎
    where
    open SR word-setoid

  aux-H³M' : ∀ m'* -> H ^ 3 • M (m'* ⁻¹) ≈ M m'* • H ^ 3
  aux-H³M' m'* = begin
    H ^ 3 • M (m'* ⁻¹) ≈⟨ aux-H³M (m'* ⁻¹) ⟩
    M (m'* ⁻¹ ⁻¹) • H ^ 3 ≈⟨ cleft aux-MM ((m'* ⁻¹ ⁻¹).proj₂) (m'* .proj₂) (inv-involutive m'* ) ⟩
    M (m'*) • H ^ 3 ∎
    where
    open SR word-setoid

module Missing-Sim where

  private
    variable
      n : ℕ
    
  open Alternative-Relations
  open Lemmas-Alt

  open Symplectic-Alt-GroupLike

  lemma-selinger-c10 :  let open PB ((₂₊ n) QRel,_===_) in
    CZ • H ↑ • CZ ≈ S⁻¹ ↑ • H ↑ • S⁻¹ ↑ • CZ • H ↑ • S⁻¹ ↑ • S⁻¹ ↓
  lemma-selinger-c10 {n} = bbc {!!} {!!} {!!}
    where
    open PB ((₂₊ n) QRel,_===_)
    open PP ((₂₊ n) QRel,_===_)
    open SR word-setoid
    open Basis-Change _ ((₂₊ n) QRel,_===_) grouplike


  lemma-selinger-c11 :  let open PB ((₂₊ n) QRel,_===_) in
    CZ • H ↓ • CZ ≈ S⁻¹ ↓ • H ↓ • S⁻¹ ↓ • CZ • H ↓ • S⁻¹ ↓ • S⁻¹ ↑
  lemma-selinger-c11 {n} = bbc (S ↓ • S ↑ • HH) (H) {!!}
    where
    open PB ((₂₊ n) QRel,_===_)
    open PP ((₂₊ n) QRel,_===_)
    open SR word-setoid
    open Basis-Change _ ((₂₊ n) QRel,_===_) grouplike
    claim : (S ↓ • S ↑ • HH) • (CZ • H ↓ • CZ) • H ≈ (S ↓ • S ↑ • HH) • (S⁻¹ ↓ • H ↓ • S⁻¹ ↓ • CZ • H ↓ • S⁻¹ ↓ • S⁻¹ ↑) • H
    claim = begin
      (S ↓ • S ↑ • HH) • (CZ • H ↓ • CZ) • H ≈⟨ {!!} ⟩
      (S ↓ • S ↑) • (HH • CZ) • H ↓ • CZ • H ≈⟨ {!!} ⟩
      (S ↓ • S ↑) • (CZ^ (- ₁) • HH) • H ↓ • CZ • H ≈⟨ {!!} ⟩
      (S ↓ • S ↑) • CZ^ (- ₁) • CX ≈⟨ trans assoc (sym (axiom semi-S-CX)) ⟩
      CX • S ≈⟨ {!!} ⟩
      (H ^ 3 • CZ • H) • S ≈⟨ {!!} ⟩
      (H ^ 3 • CZ • H) • (H ^ 3 • S⁻¹ ↓ • H ^ 3 • S⁻¹ ↓ • H ^ 3) ≈⟨ {!!} ⟩
      (H ^ 3 • CZ) • (S⁻¹ ↓ • H ↓ • S⁻¹ ↓ • H) ≈⟨ {!!} ⟩
      (S ↑ • HH) • (H ↓ • S⁻¹ ↓ • CZ • H ↓ • S⁻¹ ↓ • S⁻¹ ↑) • H ≈⟨ {!!} ⟩
      
      (S ↓ • S ↑ • HH) • (S⁻¹ ↓ • H ↓ • S⁻¹ ↓ • CZ • H ↓ • S⁻¹ ↓ • S⁻¹ ↑) • H ∎


  lemma-selinger-c13 : let open PB ((₃₊ n) QRel,_===_) in
    ⊤⊥ ↑ • CZ ↓ • ⊥⊤ ↑ ≈ ⊥⊤ ↓ • CZ ↑ • ⊤⊥ ↓
  lemma-selinger-c13 {n} = ?
    where
    open PB ((₃₊ n) QRel,_===_)
    open PP ((₃₊ n) QRel,_===_)
    open SR word-setoid
    open Basis-Change _ ((₃₊ n) QRel,_===_) grouplike


{-

module Lemmas where

  open Symplectic-Alternative

  -- open Symplectic-Rewriting-HH p-2 p-prime
  -- open Symplectic-Powers p-2 p-prime

  open PB _===_ hiding (_===_)
  open PP _===_
  open Pattern-Assoc
  open import Data.Fin.Properties

  lemma-S^k+l : ∀ k l -> S^ k • S^ l ≈ S^ (k + l)
  lemma-S^k+l k l = begin
    S^ k • S^ l ≈⟨ refl ⟩
    S ^ toℕ k • S ^ toℕ l ≈⟨ sym (lemma-^-+ S (toℕ k) (toℕ l)) ⟩
    S ^ (toℕ k Nat.+ toℕ l) ≡⟨ Eq.cong (S ^_) (m≡m%n+[m/n]*n k+l p) ⟩
    S ^ (k+l Nat.% p Nat.+ (k+l Nat./ p) Nat.* p) ≈⟨ lemma-^-+ S (k+l Nat.% p) (((k+l Nat./ p) Nat.* p)) ⟩
    S ^ (k+l Nat.% p) • S ^ ((k+l Nat./ p) Nat.* p) ≈⟨ cong (refl' (Eq.cong (S ^_) (Eq.sym (toℕ-fromℕ< (m%n<n k+l p))))) (refl' (Eq.cong (S ^_) (NP.*-comm ((k+l Nat./ p)) p))) ⟩
    S ^ toℕ (fromℕ< (m%n<n k+l p)) • S ^ (p Nat.* (k+l Nat./ p) ) ≈⟨ cong (sym (refl)) (sym (lemma-^^ S p (k+l Nat./ p))) ⟩
    S^ (k + l) • (S ^ p) ^ (k+l Nat./ p) ≈⟨ cright (lemma-^-cong (S ^ p) ε (k+l Nat./ p) (axiom order-S)) ⟩
    S^ (k + l) • ε ^ (k+l Nat./ p) ≈⟨ cright lemma-ε^k=ε (k+l Nat./ p) ⟩
    S^ (k + l) • ε ≈⟨ right-unit ⟩
    S^ (k + l) ∎
    where
    k+l = toℕ k Nat.+ toℕ l
    open SR word-setoid


  lemma-S^k-k : ∀ k -> S^ k • S^ (- k) ≈ ε
  lemma-S^k-k k = begin
    S^ k • S^ (- k) ≈⟨ lemma-S^k+l k (- k) ⟩
    S^ (k + - k) ≡⟨ Eq.cong S^ (+-inverseʳ k) ⟩
    S^ ₀ ≈⟨ (refl) ⟩
    ε ∎
    where
    open SR word-setoid
    k-k = toℕ k Nat.+ toℕ (- k)

  lemma-S^-k+k : ∀ k -> S^ (- k) • S^ k ≈ ε
  lemma-S^-k+k k = begin
    S^ (- k) • S^ k ≈⟨ refl ⟩
    S ^ toℕ (- k) • S ^ toℕ k ≈⟨ word-comm (toℕ (- k)) (toℕ ( k)) refl ⟩
    S ^ toℕ k • S ^ toℕ (- k) ≈⟨ refl ⟩
    S^ k • S^ (- k) ≈⟨ lemma-S^k-k k ⟩
    ε ∎
    where
    open SR word-setoid

  open Eq using (_≢_)



  derived-D : ∀ x -> (nz : x ≢ ₀) -> let x⁻¹ = ((x , nz) ⁻¹) .proj₁ in let -x⁻¹ = - x⁻¹ in
    H • S^ x • H ≈ H • S^ x • H • S^ x⁻¹ • H • H ^ 3 • S^ -x⁻¹
  derived-D  x nz = begin
    H • S^ x • H ≈⟨ (cright cright sym right-unit) ⟩
    H • S^ x • H • ε ≈⟨ cright cright cright sym (lemma-S^k-k x⁻¹) ⟩
    H • S^ x • H • S^ x⁻¹ • S^ -x⁻¹ ≈⟨ cright cright cright cright sym left-unit ⟩
    H • S^ x • H • S^ x⁻¹ • ε • S^ -x⁻¹ ≈⟨ cright cright cright cright sym (cong (lemma-order-H) refl) ⟩
    H • S^ x • H • S^ x⁻¹ • H ^ 4 • S^ -x⁻¹ ≈⟨ (cright cright cright cright special-assoc (□ ^ 4 • □) (□ • □ ^ 3 • □) auto) ⟩
    H • S^ x • H • S^ x⁻¹ • H • H ^ 3 • S^ -x⁻¹ ∎
    where
    x⁻¹ = ((x , nz) ⁻¹) .proj₁
    -x⁻¹ = - x⁻¹ 
    open SR word-setoid



  lemma-S^ab : ∀ (a b : ℤ ₚ) -> S ^ toℕ (a * b) ≈ S ^ (toℕ a Nat.* toℕ b)
  lemma-S^ab a b = begin
    S ^ toℕ (a * b) ≡⟨ auto ⟩
    S ^ toℕ (fromℕ< (m%n<n (toℕ a Nat.* toℕ b) p)) ≡⟨ Eq.cong (S ^_) (toℕ-fromℕ< (m%n<n (toℕ a Nat.* toℕ b) p)) ⟩
    S ^ ((toℕ a Nat.* toℕ b) % p) ≈⟨ sym right-unit ⟩
    S ^ (ab Nat.% p) • ε ≈⟨ (cright sym (lemma-ε^k=ε (ab Nat./ p))) ⟩
    S ^ (ab Nat.% p) • (ε) ^ (ab Nat./ p) ≈⟨ (cright sym (lemma-^-cong (S ^ p) ε (ab Nat./ p) (axiom order-S))) ⟩
    S ^ (ab Nat.% p) • (S ^ p) ^ (ab Nat./ p) ≈⟨ (cright lemma-^^ S p (ab Nat./ p)) ⟩
    S ^ (ab Nat.% p) • S ^ (p Nat.* (ab Nat./ p)) ≈⟨ (cright refl' (Eq.cong (S ^_) (NP.*-comm p (ab Nat./ p)))) ⟩
    S ^ (ab Nat.% p) • S ^ (ab Nat./ p Nat.* p) ≈⟨ sym (lemma-^-+ S (ab Nat.% p) (ab Nat./ p Nat.* p)) ⟩
    S ^ (ab Nat.% p Nat.+ ab Nat./ p Nat.* p) ≡⟨ Eq.cong (S ^_) (Eq.sym (m≡m%n+[m/n]*n ab p)) ⟩
    S ^ (toℕ a Nat.* toℕ b) ∎
    where
    ab = toℕ a Nat.* toℕ b
    open SR word-setoid


  derived-7 : ∀ x y -> (nz : x ≢ ₀) -> (nzy : y ≢ ₀) -> let -'₁ = -' ((₁ , λ ())) in let x⁻¹ = ((x , nz) ⁻¹) .proj₁ in let -x⁻¹ = - x⁻¹ in let -y/x' = (((y , nzy) *' ((x , nz) ⁻¹)) *' -'₁) in let -y/x = -y/x' .proj₁ in
  
    M (y , nzy) • H • S^ x • H ≈ S^ (-x⁻¹ * (y * y)) • M -y/x' • (H • S^ -x⁻¹)
    
  derived-7 x y nzx nzy = begin
    M (y , nzy) • H • S^ x • H ≈⟨ (cright derived-D x nzx) ⟩
    M (y , nzy) • H • S^ x • H • S^ x⁻¹ • H • H ^ 3 • S^ -x⁻¹ ≈⟨ (cright special-assoc (□ • □ • □ • □ • □ • □ • □) (□ ^ 5 • □ • □) auto) ⟩
    M (y , nzy) • (H • S^ x • H • S^ x⁻¹ • H) • H ^ 3 • S^ -x⁻¹ ≈⟨ (cright cleft sym left-unit) ⟩
    M (y , nzy) • (ε • H • S^ x • H • S^ x⁻¹ • H) • H ^ 3 • S^ -x⁻¹ ≈⟨ (cright cleft cleft sym (lemma-S^-k+k x⁻¹)) ⟩
    M (y , nzy) • ((S^ -x⁻¹ • S^ x⁻¹) • H • S^ x • H • S^ x⁻¹ • H) • H ^ 3 • S^ -x⁻¹ ≈⟨ special-assoc (□ • (□ ^ 2 • □ ^ 5) • □) (□ ^ 2 • □ ^ 6 • □) auto ⟩
    (M (y , nzy) • S^ -x⁻¹) • (S^ x⁻¹ • H • S^ x • H • S^ x⁻¹ • H) • H ^ 3 • S^ -x⁻¹ ≈⟨ (cleft (cright  (refl))) ⟩
    (M (y , nzy) • S ^ toℕ -x⁻¹) • (S^ x⁻¹ • H • S^ x • H • S^ x⁻¹ • H) • H ^ 3 • S^ -x⁻¹ ≈⟨ (cleft derived-5 y (toℕ -x⁻¹) nzy) ⟩
    (S ^ (toℕ -x⁻¹ Nat.* toℕ (y * y)) • M (y , nzy)) • (S^ x⁻¹ • H • S^ x • H • S^ x⁻¹ • H) • H ^ 3 • S^ -x⁻¹ ≈⟨ special-assoc (□ ^ 2 • □ ^ 2) (□ • □ ^ 2 • □) auto ⟩
    S ^ (toℕ -x⁻¹ Nat.* toℕ (y * y)) • (M (y , nzy) • (S^ x⁻¹ • H • S^ x • H • S^ x⁻¹ • H)) • H ^ 3 • S^ -x⁻¹ ≈⟨ (cright cleft (cright (cright cright cleft refl' (Eq.cong S^ (Eq.sym (inv-involutive ((x , nz)))))))) ⟩
    S ^ (toℕ -x⁻¹ Nat.* toℕ (y * y)) • (M (y , nzy) • M ((x , nz) ⁻¹)) • H ^ 3 • S^ -x⁻¹ ≈⟨ (cright cleft  (lemma-M-mul (y , nzy) ((x , nz) ⁻¹))) ⟩
    S ^ (toℕ -x⁻¹ Nat.* toℕ (y * y)) • M ((y , nzy) *' ((x , nz) ⁻¹)) • H ^ 3 • S^ -x⁻¹ ≈⟨ (cright special-assoc (□ • □ ^ 3 • □) (□ ^ 3 • □ ^ 2) auto) ⟩
    S ^ (toℕ -x⁻¹ Nat.* toℕ (y * y)) • (M ((y , nzy) *' ((x , nz) ⁻¹)) • HH) • H • S^ -x⁻¹ ≈⟨ (cright cleft (cright (lemma-order-H))) ⟩
    S ^ (toℕ -x⁻¹ Nat.* toℕ (y * y)) • (M ((y , nzy) *' ((x , nz) ⁻¹)) • M -'₁) • H • S^ -x⁻¹ ≈⟨ (cright cleft (lemma-M-mul (((y , nzy) *' ((x , nz) ⁻¹))) -'₁)) ⟩
    S ^ (toℕ -x⁻¹ Nat.* toℕ (y * y)) • (M (((y , nzy) *' ((x , nz) ⁻¹)) *' -'₁) ) • H • S^ -x⁻¹ ≈⟨ (cleft sym (lemma-S^ab -x⁻¹ (y * y))) ⟩
    S ^ toℕ (-x⁻¹ * (y * y)) • M -y/x' • (H • S^ -x⁻¹) ≈⟨  refl ⟩
    S^ (-x⁻¹ * (y * y)) • M -y/x' • (H • S^ -x⁻¹) ∎
    where
    open SR word-setoid
    nz = nzx
    x⁻¹ = ((x , nz) ⁻¹) .proj₁
    x⁻¹⁻¹ = (((x , nz) ⁻¹) ⁻¹) .proj₁
    -x⁻¹ = - x⁻¹
    -y/x' = (((y , nzy) *' ((x , nz) ⁻¹)) *' -'₁)
    -y/x = -y/x' .proj₁

  aux-M≡M : ∀ {x y : ℤ ₚ} (nzx : x ≢ ₀) (nzy : y ≢ ₀) -> x ≡ y -> M (x , nzx) ≈ M (y , nzy)
  aux-M≡M {x} {y} nz1 nz2 eq rewrite eq = refl


  semi-HM : ∀ (x : ℤ* ₚ) -> H • M x ≈ M (x ⁻¹) • H
  semi-HM x' = begin
    H • (S^ x • H • S^ x⁻¹ • H • S^ x • H) ≈⟨ special-assoc (□ • □ ^ 6) (□ ^ 3 • □ ^ 4) auto ⟩
    (H • S^ x • H) • S^ x⁻¹ • H • S^ x • H ≈⟨ (trans (sym left-unit) (cong (sym (sym lemma-M1)) refl)) ⟩
    M₁ • (H • S^ x • H) • S^ x⁻¹ • H • S^ x • H ≈⟨ sym assoc ⟩
    (M₁ • (H • S^ x • H)) • S^ x⁻¹ • H • S^ x • H ≈⟨ (cleft derived-7 x ₁ (x' .proj₂) λ ()) ⟩
    (S^ (-x⁻¹ * (₁ * ₁)) • M (((₁ , λ ()) *' x' ⁻¹) *' -'₁) • H • S^ -x⁻¹) • S^ x⁻¹ • H • S^ x • H ≈⟨ cleft (cright (cleft aux-M≡M ((((₁ , λ ()) *' x' ⁻¹) *' -'₁) .proj₂) ((-' (x' ⁻¹)) .proj₂) aux-a1)) ⟩
    (S^ (-x⁻¹ * ₁) • M (-' (x' ⁻¹)) • H • S^ -x⁻¹) • S^ x⁻¹ • H • S^ x • H ≈⟨ special-assoc (□ ^ 4 • □ ^ 4) (□ • □ ^ 4 • □ ^ 3) auto ⟩
    S^ (-x⁻¹ * ₁) • (M (-' (x' ⁻¹)) • H • S^ -x⁻¹ • S^ x⁻¹) • H • S^ x • H ≈⟨ cong (refl' (Eq.cong S^ (*-identityʳ -x⁻¹))) (cleft cright (cright lemma-S^-k+k x⁻¹)) ⟩
    S^ -x⁻¹ • (M (-' (x' ⁻¹)) • H • ε) • H • S^ x • H ≈⟨ (cright cleft (cright right-unit)) ⟩
    S^ -x⁻¹ • (M (-' (x' ⁻¹)) • H) • H • S^ x • H ≈⟨ (cright special-assoc (□ ^ 2 • □ ^ 3) (□ ^ 3 • □ ^ 2) auto) ⟩
    S^ -x⁻¹ • (M (-' (x' ⁻¹)) • H • H) • S^ x • H ≈⟨ (cright cleft cright (lemma-order-H)) ⟩
    S^ -x⁻¹ • (M (-' (x' ⁻¹)) • M -'₁) • S^ x • H ≈⟨ (cright cleft  (lemma-M-mul (-' (x' ⁻¹)) -'₁)) ⟩
    S^ -x⁻¹ • M (-' (x' ⁻¹) *' -'₁) • S^ x • H ≈⟨ (cright cleft aux-M≡M ((-' (x' ⁻¹) *' -'₁) .proj₂) ((x' ⁻¹) .proj₂) aux-a2) ⟩
    S^ -x⁻¹ • M (x' ⁻¹) • S^ x • H ≈⟨ sym (cong refl assoc) ⟩
    S^ -x⁻¹ • (M (x' ⁻¹) • S^ x) • H ≈⟨ (cright cleft lemma-MS^k x⁻¹ x ((x' ⁻¹) .proj₂)) ⟩
    S^ -x⁻¹ • (S^ (x * (x⁻¹ * x⁻¹)) • M (x' ⁻¹)) • H ≈⟨ (cright cleft (cleft refl' (Eq.cong S^ aux-a3))) ⟩
    S^ -x⁻¹ • (S^ x⁻¹ • M (x' ⁻¹)) • H ≈⟨  special-assoc (□ • □ ^ 2 • □) (□ ^ 2 • □ ^ 2) auto ⟩
    (S^ -x⁻¹ • S^ x⁻¹) • M (x' ⁻¹) • H ≈⟨ (cleft lemma-S^-k+k x⁻¹) ⟩
    ε • M (x' ⁻¹) • H ≈⟨ left-unit ⟩
    M (x' ⁻¹) • H ∎
    where
    x = x' .proj₁
    x⁻¹ = ((x' ⁻¹) .proj₁ )

    -x = - x
    -x⁻¹ = - x⁻¹
    aux-a1 : ₁ * x⁻¹ * (-'₁ .proj₁) ≡ -x⁻¹
    aux-a1 = begin
      ₁ * x⁻¹ * (-'₁ .proj₁) ≡⟨ Eq.cong (\ xx -> xx * (-'₁ .proj₁)) (*-identityˡ x⁻¹) ⟩
      x⁻¹ * (-'₁ .proj₁) ≡⟨ Eq.cong (x⁻¹ *_) (Eq.sym p-1=-1ₚ) ⟩
      x⁻¹ * ₋₁ ≡⟨ *-comm x⁻¹ ₋₁ ⟩
      ₋₁ * x⁻¹ ≡⟨ auto ⟩
      -x⁻¹ ∎
      where open ≡-Reasoning

    aux-a2 : -x⁻¹ * - ₁ ≡ x⁻¹
    aux-a2 = begin
      -x⁻¹ * - ₁ ≡⟨ *-comm -x⁻¹ (- ₁) ⟩
      - ₁ * -x⁻¹ ≡⟨ -1*x≈-x -x⁻¹ ⟩
      - -x⁻¹ ≡⟨ -‿involutive x⁻¹ ⟩
      x⁻¹ ∎
      where
      open ≡-Reasoning
      open import Algebra.Properties.Ring (+-*-ring p-2)


    aux-a3 : x * (x⁻¹ * x⁻¹) ≡ x⁻¹
    aux-a3 = begin
      x * (x⁻¹ * x⁻¹) ≡⟨ Eq.sym (*-assoc x x⁻¹ x⁻¹) ⟩
      x * x⁻¹ * x⁻¹ ≡⟨ Eq.cong (_* x⁻¹) (lemma-⁻¹ʳ x {{nztoℕ {y = x} {neq0 = x' .proj₂}}}) ⟩
      ₁ * x⁻¹ ≡⟨ *-identityˡ x⁻¹ ⟩
      x⁻¹ ∎
      where open ≡-Reasoning

    open SR word-setoid

  -- Just to collect all derived rules.
  module Derived where
  
    -- semi-HM : ∀ (x : ℤ* ₚ) -> H • M x ≈ M (x ⁻¹) • H
    -- M (y , nzy) • H • S^ x • H ≈ S^ (-x⁻¹ * (y * y)) • M -y/x' • (H • S^ -x⁻¹)
    -- M (x , nz) • S^ k ≈ S^ (k * (x * x)) • M (x , nz)
    -- lemma-M-mul : ∀ x y -> M x • M y ≈ M (x *' y)
    -- M x • S ≈ S^ ((x' * x')) • M x
    -- Mg ^ p-1 ≈ ε
    -- lemma-Mg^kS : ∀ k -> Mg ^ k • S ≈ S^ ((g * g) ^′ k) • Mg ^ k
    -- Mg • S^ k ≈ S^ (k * (g * g)) • Mg
    -- lemma-S^k-% : ∀ k -> S ^ k ≈ S ^ (k % p)
    -- HH ≈ M -'₁
    -- S⁻¹ ≈ S^ ₚ₋₁
    -- ε ≈ M (₁ , λ ())
    -- (H⁻¹ • S⁻¹) ^ 3 ≈ ε
    -- (S⁻¹ • H⁻¹) ^ 3 ≈ ε
-}


module Iso where

  private
    variable
      n : ℕ

  module Sim  = NSim.Simplified-Relations
  module Alt  = Alternative-Relations
  open Symplectic renaming (Gen to Gen₁ ; _QRel,_===_ to _QRel,_===₁_) using ()
  Gen₂ = Gen₁
  open Alt renaming (_QRel,_===_ to _QRel,_===₂_) using ()
  open NSim.Symplectic-Sim-GroupLike renaming (grouplike to grouplike₁) using ()
  open Symplectic-Alt-GroupLike renaming (grouplike to grouplike₂) using ()
  open Lemmas-Dual


  f-well-defined : let open PB (n QRel,_===₂_) renaming (_≈_ to _≈₂_) in
    ∀ {w v} -> n QRel, w ===₁ v -> id w ≈₂ id v
  f-well-defined {n} order-S = PB.axiom Alt.order-S
  f-well-defined {₁₊ n} order-H = lemma-order-H
    where
    open Lemmas1 n
  f-well-defined {₁₊ n} order-SH = lemma-order-SH
    where
    open Lemmas1 n
  f-well-defined {₁₊ n} comm-HHS = lemma-comm-HHS
    where
    open Lemmas1b n
  f-well-defined {₁₊ n} (M-mul x y) = lemma-M-mul x y
    where
    open Lemmas1 n
  f-well-defined {₁₊ n} (semi-MS x) = lemma-semi-MS x
    where
    open Lemmas1 n
  f-well-defined {₂₊ n} (semi-M↑CZ x) = lemma-semi-M↑-CZ x
    where
    open Lemmas2 n
  f-well-defined {₂₊ n} (semi-M↓CZ x) = lemma-semi-M↓-CZ x
    where
    open Lemmas2 n
  f-well-defined {n} order-CZ = PB.axiom Alt.order-CZ
  f-well-defined {n} comm-CZ-S↓ = lemma-comm-CZ-S↓
  f-well-defined {n} comm-CZ-S↑ = PB.axiom Alt.comm-CZ-S↑
  f-well-defined {n} selinger-c10 = {!!}
  f-well-defined {n} selinger-c11 = {!!}
  f-well-defined {n} selinger-c12 = PB.axiom Alt.comm-CZ↑-CZ
  f-well-defined {n} selinger-c13 = {!!}
  f-well-defined {n} selinger-c14 = {!!}
  f-well-defined {n} selinger-c15 = {!!}
  f-well-defined {n} comm-H = PB.axiom Alt.comm-H
  f-well-defined {n} comm-S = PB.axiom Alt.comm-S
  f-well-defined {n} comm-CZ = PB.axiom Alt.comm-CZ
  f-well-defined {n} (cong↑ eq) = lemma-cong↑ _ _ (f-well-defined eq)
    where
    open Lemmas-Alt

{-  
  g-well-defined : let open PB (n QRel,_===₁_) renaming (_≈_ to _≈₁_) in
    ∀ {u t} -> n QRel, u ===₂ t -> id u ≈₁ id t
  g-well-defined Alt.order-S = PB.axiom _QRel,_===₁_.order-S
  g-well-defined {₁₊ n} Alt.order-H = lemma-HH-M-1
    where
    open Lemmas0 n
  g-well-defined {₁₊ n} (Alt.M-power k) = begin
    (Mg^ k) ≡⟨ auto ⟩
    Mg ^ toℕ k ≈⟨ lemma-^-cong (Mg) (M g′) (toℕ k) (refl) ⟩
    M g′ ^ toℕ k ≈⟨ lemma-M-power g′ (toℕ k) ⟩
    M (g^ k) ≈⟨ refl ⟩
    (M (g^ k)) ∎
    where
    open PB ((₁₊ n) QRel,_===₁_)
    open PP ((₁₊ n) QRel,_===₁_)
    open SR word-setoid
    open Lemmas0 n
    open Alt

    
  g-well-defined {₁₊ n} Alt.semi-MS = PB.axiom (_QRel,_===₁_.semi-MS ((g , g≠0)))
  g-well-defined Alt.semi-M↑-CZ = PB.axiom (_QRel,_===₁_.semi-M↑-CZ ((g , g≠0)))
  g-well-defined Alt.semi-M↓CZ = PB.axiom (_QRel,_===₁_.semi-M↓CZ ((g , g≠0)))
  g-well-defined Alt.order-CZ = PB.axiom _QRel,_===₁_.order-CZ
  g-well-defined Alt.comm-CZ-S↓ = PB.axiom _QRel,_===₁_.comm-CZ-S↓
  g-well-defined Alt.comm-CZ-S↑ = PB.axiom _QRel,_===₁_.comm-CZ-S↑
  g-well-defined Alt.selinger-c10 = PB.axiom _QRel,_===₁_.selinger-c10
  g-well-defined Alt.selinger-c11 = PB.axiom _QRel,_===₁_.selinger-c11
  g-well-defined Alt.comm-CZ↑-CZ = PB.axiom _QRel,_===₁_.comm-CZ↑-CZ
  g-well-defined Alt.selinger-c13 = PB.axiom _QRel,_===₁_.selinger-c13
  g-well-defined Alt.selinger-c14 = PB.axiom _QRel,_===₁_.selinger-c14
  g-well-defined Alt.selinger-c15 = PB.axiom _QRel,_===₁_.selinger-c15
  g-well-defined Alt.comm-H = PB.axiom _QRel,_===₁_.comm-H
  g-well-defined Alt.comm-S = PB.axiom _QRel,_===₁_.comm-S
  g-well-defined Alt.comm-CZ = PB.axiom _QRel,_===₁_.comm-CZ
  g-well-defined (Alt.cong↑ eq) = lemma-cong↑ _ _ (g-well-defined eq)
    where
    open Lemmas-Sim


  open import Algebra.Bundles using (Group)
  open import Algebra.Morphism.Structures using (module GroupMorphisms)

  open GroupMorphisms


  Theorem-Sim-iso-Alt : ∀ {n} ->
    let
    module G1 = Group-Lemmas (Gen₁ n) (n QRel,_===₁_) grouplike₁
    module G2 = Group-Lemmas (Gen₂ n) (n QRel,_===₂_) grouplike₂
    in
    IsGroupIsomorphism (Group.rawGroup G1.•-ε-group) (Group.rawGroup G2.•-ε-group) id
  Theorem-Sim-iso-Alt {n}  = StarGroupIsomorphism.isGroupIsomorphism f-well-defined g-well-defined
    where
    open import Presentation.MorphismId (n QRel,_===₁_) (n QRel,_===₂_)
    open GroupMorphs (grouplike₁ {n}) (grouplike₂ {n})



  Theorem-Sim-iso-Alt' : ∀ {n} ->
    let
    module G1 = Group-Lemmas (Gen₁ n) (n QRel,_===₁_) grouplike₁
    module G2 = Group-Lemmas (Gen₂ n) (n QRel,_===₂_) grouplike₂
    in
    IsGroupIsomorphism (Group.rawGroup G2.•-ε-group) (Group.rawGroup G1.•-ε-group)  id
  Theorem-Sim-iso-Alt' {n} = StarGroupIsomorphism.isGroupIsomorphism g-well-defined f-well-defined
    where
    open import Presentation.MorphismId  (n QRel,_===₂_) (n QRel,_===₁_)
    open GroupMorphs (grouplike₂ {n}) (grouplike₁ {n}) 

-}

