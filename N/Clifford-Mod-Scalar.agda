{-# OPTIONS --safe #-}
{-# OPTIONS --prop #-}
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

module N.Clifford-Mod-Scalar
  (p-3 : ℕ)
  (let p-2 = suc p-3)
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

module Symplectic-Simplified where

open import N.Symplectic p-2 p-prime as NSym
open Symplectic hiding (_QRel,_===_ ; M ; M₁)

module Clifford-Relations where

  Z : ∀ {n} -> Word (Gen (₁₊ n))
  Z = H • H • S • H • H • S⁻¹
  
  X : ∀ {n} -> Word (Gen (₁₊ n))
  X = H • S • H • H • S⁻¹ • H

  Z⁻¹ : ∀ {n} -> Word (Gen (₁₊ n))
  Z⁻¹ = Z ^ p-1

  X⁻¹ : ∀ {n} -> Word (Gen (₁₊ n))
  X⁻¹ = X ^ p-1

  1/2 = ((₂ , λ ()) ⁻¹) .proj₁

  Z^ : ℤ ₚ ->  ∀ {n} -> Word (Gen (₁₊ n))
  Z^ k = Z ^ toℕ k

  X^ : ℤ ₚ ->  ∀ {n} -> Word (Gen (₁₊ n))
  X^ k = X ^ toℕ k

  𝑠 : ∀ {n} -> Word (Gen (₁₊ n))
  𝑠 = S • Z^ 1/2
  𝑠^ : ∀ {n} ->  ℤ ₚ ->  Word (Gen (₁₊ n))
  𝑠^ k = 𝑠 ^ toℕ k


  M : ∀ {n} -> ℤ* ₚ -> Word (Gen (₁₊ n))
  M x' = 𝑠^ x • H • 𝑠^ x⁻¹ • H • 𝑠^ x • H
    where
    x = x' .proj₁
    x⁻¹ = ((x' ⁻¹) .proj₁ )

  M₋₁ : ∀ {n} -> Word (Gen (₁₊ n))
  M₋₁ = M -'₁

  M₁ : ∀ {n} -> Word (Gen (₁₊ n))
  M₁ = M (₁ , λ ())

  Mg :  ∀ {n} -> Word (Gen (₁₊ n))
  Mg = M g′

  Mg^ : ℤ ₚ ->  ∀ {n} -> Word (Gen (₁₊ n))
  Mg^ k = Mg ^ toℕ k




  infix 4 _QRel,_===_
  data _QRel,_===_ : (n : ℕ) → WRel (Gen n) where
  
    order-S :           ∀ {n} → (₁₊ n) QRel,  S ^ p === ε
    order-H :           ∀ {n} → (₁₊ n) QRel,  H ^ 2 === M₋₁
    M-power : ∀ {n} (k : ℤ ₚ) → (₁₊ n) QRel,  Mg^ k === M (g^ k)
    semi-M𝑠 :           ∀ {n} → (₁₊ n) QRel,  Mg • 𝑠 === 𝑠^ (g * g) • Mg
    order-SH :          ∀ {n} → (₁₊ n) QRel,  (S • H) ^ 3 === ε
    comm-HHSHHS :       ∀ {n} → (₁₊ n) QRel,  H • H • S • H • H • S === S • H • H • S • H • H

    semi-M↑CZ :         ∀ {n} → (₂₊ n) QRel,  Mg ↑ • CZ === CZ^ g • Mg ↑
    semi-M↓CZ :         ∀ {n} → (₂₊ n) QRel,  Mg ↓ • CZ === CZ^ g • Mg ↓

    order-CZ :          ∀ {n} → (₂₊ n) QRel,  CZ ^ p === ε

    comm-CZ-S↓ :        ∀ {n} → (₂₊ n) QRel,  CZ • S ↓ === S ↓ • CZ
    comm-CZ-S↑ :        ∀ {n} → (₂₊ n) QRel,  CZ • S ↑ === S ↑ • CZ

    selinger-c10 :      ∀ {n} → (₂₊ n) QRel,  CZ • H ↑ • CZ === 𝑠 ↑ ^ p-1 • H ↑ • 𝑠 ↑ ^ p-1 • CZ • H ↑ • 𝑠 ↑ ^ p-1 • 𝑠 ↓ ^ p-1
    selinger-c11 :      ∀ {n} → (₂₊ n) QRel,  CZ • H ↓ • CZ === 𝑠 ↓ ^ p-1 • H ↓ • 𝑠 ↓ ^ p-1 • CZ • H ↓ • 𝑠 ↓ ^ p-1 • 𝑠 ↑ ^ p-1

    selinger-c12 :      ∀ {n} → (₃₊ n) QRel,  CZ ↑ • CZ === CZ • CZ ↑
    selinger-c13 :      ∀ {n} → (₃₊ n) QRel,  ⊤⊥ ↑ • CZ ↓ • ⊥⊤ ↑ === ⊥⊤ ↓ • CZ ↑ • ⊤⊥ ↓
    
    selinger-c14 :      ∀ {n} → (₃₊ n) QRel,  (⊤⊥ ↑ • CZ ↓) ^ 3 === ε
    selinger-c15 :      ∀ {n} → (₃₊ n) QRel,  (⊥⊤ ↓ • CZ ↑) ^ 3 === ε

    comm-H :         ∀ {n}{x} → (₂₊ n) QRel,  [ x ↥ ]ʷ • H === H • [ x ↥ ]ʷ
    comm-S :         ∀ {n}{x} → (₂₊ n) QRel,  [ x ↥ ]ʷ • S === S • [ x ↥ ]ʷ
    comm-CZ :        ∀ {n}{x} → (₃₊ n) QRel,  [ x ↥ ↥ ]ʷ • CZ === CZ • [ x ↥ ↥ ]ʷ
    
    cong↑ :         ∀ {n w v} →      n QRel,  w === v →
                                -------------------------       
                                (₁₊ n) QRel,  w ↑ === v ↑


module Lemmas-Clifford where

  open Clifford-Relations
  
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


module Lemmas1 (n : ℕ) where


  open Clifford-Relations

  open PB ((₁₊ n) QRel,_===_) hiding (_===_)
  open PP ((₁₊ n) QRel,_===_)
  open Pattern-Assoc
  open import Data.Nat.DivMod
  open import Data.Fin.Properties


  aux-M≡M : ∀ y y' -> y .proj₁ ≡ y' .proj₁ -> M {n = n} y ≡ M y'
  aux-M≡M y y' eq = begin
    M y ≡⟨ auto ⟩
    𝑠^ x • H • 𝑠^ x⁻¹ • H • 𝑠^ x • H ≡⟨ Eq.cong₂ (\ xx yy -> 𝑠^ xx • H • 𝑠^ yy • H • 𝑠^ x • H) eq aux-eq ⟩
    𝑠^ x' • H • 𝑠^ x'⁻¹ • H • 𝑠^ x • H ≡⟨ Eq.cong (\ xx -> 𝑠^ x' • H • 𝑠^ x'⁻¹ • H • 𝑠^ xx • H) eq ⟩
    𝑠^ x' • H • 𝑠^ x'⁻¹ • H • 𝑠^ x' • H ≡⟨ auto ⟩
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


  lemma-M1 : M (₁ , λ ()) ≈ ε
  lemma-M1 = begin
    M (₁ , λ ()) ≡⟨ aux-M≡M ((₁ , λ ())) (g^ ₀) auto ⟩
    M (g^ ₀) ≈⟨ sym (axiom (M-power ₀)) ⟩
    Mg^ ₀ ≈⟨ refl ⟩
    ε ∎
    where
    open SR word-setoid




  lemma-S⁻¹ : S⁻¹ ≈ S^ ₚ₋₁
  lemma-S⁻¹ = begin
    S⁻¹ ≈⟨ refl ⟩
    S ^ p-1 ≡⟨ Eq.cong (S ^_) (Eq.sym lemma-toℕ-ₚ₋₁) ⟩
    S ^ toℕ ₚ₋₁ ≈⟨ refl ⟩
    S^ ₚ₋₁ ∎
    where
    open SR word-setoid



  lemma-Mg𝑠^k : ∀ k ->  let g⁻¹ = (g′ ⁻¹) .proj₁ in let -g⁻¹ = - g⁻¹ in
    Mg • 𝑠 ^ k ≈ 𝑠 ^ (k Nat.* toℕ (g * g)) • Mg
  lemma-Mg𝑠^k k@0 = trans right-unit (sym left-unit)
  lemma-Mg𝑠^k k@1 = begin  
    Mg • 𝑠 ^ k ≈⟨ refl ⟩
    Mg • 𝑠 ≈⟨ axiom semi-M𝑠 ⟩
    𝑠^ (g * g) • Mg ≈⟨ refl ⟩
    𝑠 ^ toℕ (g * g) • Mg ≈⟨ (cleft refl' (Eq.cong (𝑠 ^_) (Eq.sym ( NP.*-identityˡ (toℕ (g * g)))))) ⟩
    𝑠 ^ (k Nat.* toℕ (g * g)) • Mg ∎
    where
    open SR word-setoid
  lemma-Mg𝑠^k k@(₂₊ k') = begin  
    Mg • 𝑠 ^ k ≈⟨ refl ⟩
    Mg • 𝑠 • 𝑠 ^ ₁₊ k' ≈⟨ sym assoc ⟩
    (Mg • 𝑠) • 𝑠 ^ ₁₊ k' ≈⟨ (cleft lemma-Mg𝑠^k 1 ) ⟩
    (𝑠 ^ (1 Nat.* toℕ (g * g)) • Mg) • 𝑠 ^ ₁₊ k' ≈⟨ assoc ⟩
    𝑠 ^ (1 Nat.* toℕ (g * g)) • Mg • 𝑠 ^ ₁₊ k' ≈⟨ (cright lemma-Mg𝑠^k (₁₊ k')) ⟩
    𝑠 ^ (1 Nat.* toℕ (g * g)) • 𝑠 ^ (₁₊ k' Nat.* toℕ (g * g)) • Mg ≈⟨ sym assoc ⟩
    (𝑠 ^ (1 Nat.* toℕ (g * g)) • 𝑠 ^ (₁₊ k' Nat.* toℕ (g * g))) • Mg ≈⟨ (cleft sym (lemma-^-+ 𝑠 ((1 Nat.* toℕ (g * g))) ((₁₊ k' Nat.* toℕ (g * g))))) ⟩
    (𝑠 ^ ((1 Nat.* toℕ (g * g)) Nat.+ (₁₊ k' Nat.* toℕ (g * g)))) • Mg ≈⟨ (cleft refl' (Eq.cong (𝑠 ^_) (Eq.sym (NP.*-distribʳ-+ (toℕ (g * g)) ₁ (₁₊ k'))))) ⟩
    𝑠 ^ ((1 Nat.+ ₁₊ k') Nat.* toℕ (g * g) ) • Mg ≈⟨ refl ⟩
    𝑠 ^ (k Nat.* toℕ (g * g)) • Mg ∎
    where
    open SR word-setoid


  open import Data.Fin.Properties
  
  lemma-Mg^p-1=ε : Mg ^ p-1 ≈ ε
  lemma-Mg^p-1=ε = begin
    Mg ^ p-1 ≡⟨ Eq.cong (Mg ^_) (Eq.sym (toℕ-fromℕ< (NP.n<1+n p-1))) ⟩
    Mg^ (fromℕ< (NP.n<1+n p-1)) ≈⟨ axiom (M-power (₂₊ (fromℕ< _))) ⟩
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

  lemma-comm-SHHS^kHH : ∀ k  -> S • H • H • S ^ k • H • H ≈ (H • H • S ^ k • H • H) • S
  lemma-comm-SHHS^kHH k@0 = begin
    S • H • H • ε • H • H ≈⟨ by-assoc auto ⟩
    S • H • H • H • H ≈⟨ (cright lemma-order-H) ⟩
    S • ε ≈⟨ trans right-unit (sym left-unit) ⟩
    ε • S ≈⟨ (cleft sym lemma-order-H) ⟩
    (H • H • H • H) • S ≈⟨ by-assoc auto ⟩
    (H • H • ε • H • H) • S ∎
    where
    open SR word-setoid
    open Pattern-Assoc
  lemma-comm-SHHS^kHH k@1 = sym (by-assoc-and (axiom comm-HHSHHS) auto auto)
  lemma-comm-SHHS^kHH k@(₁₊ k'@(₁₊ k'')) = begin
    S • H • H • S ^ k • H • H ≈⟨ refl ⟩
    S • H • H • (S • S ^ k') • H • H ≈⟨ (cright cright cright cleft cright sym left-unit) ⟩
    S • H • H • (S • ε • S ^ k') • H • H ≈⟨ (cright cright cright cleft cright cleft sym lemma-order-H) ⟩
    S • H • H • (S • (H • H • H • H) • S ^ k') • H • H ≈⟨ special-assoc (□ • □ • □ • (□ • □ ^ 4 • □) • □ ^ 2 ) (□ ^ 6 • □ ^ 5 ) auto ⟩
    (S • H • H • S • H • H) • H • H • S ^ k' • H • H ≈⟨ (cleft sym (axiom comm-HHSHHS)) ⟩
    (H • H • S • H • H • S) • H • H • S ^ k' • H • H ≈⟨ special-assoc (□ ^ 6 • □ ^ 5) (□ ^ 5 • □ ^ 6) auto ⟩
    (H • H • S • H • H) • S • H • H • S ^ k' • H • H ≈⟨ (cright lemma-comm-SHHS^kHH k') ⟩
    (H • H • S • H • H) • (H • H • S ^ k' • H • H) • S ≈⟨ special-assoc (□ ^ 5 • □ ^ 5 • □) (□ ^ 7 • □ ^ 4) auto ⟩
    (H • H • S • H • H • H • H) • S ^ k' • H • H • S ≈⟨ (cleft (cright cright trans (cright lemma-order-H) right-unit)) ⟩
    (H • H • S) • S ^ k' • H • H • S ≈⟨ special-assoc (□ ^ 3 • □ ^ 4) (□ • □ • □ ^ 2 • □ ^ 3) auto ⟩
    H • H • (S • S ^ k') • H • H • S ≈⟨ special-assoc (□ ^ 6) (□ ^ 5 • □) auto ⟩
    (H • H • S ^ k • H • H) • S ∎
    where
    open SR word-setoid
    open Pattern-Assoc


  lemma-Z^k-ℕ : ∀ k -> Z ^ k ≈ H • H • S ^ k • H • H • S⁻¹ ^ k
  lemma-Z^k-ℕ k@0 = sym (by-assoc-and ((lemma-order-H)) auto auto)
  lemma-Z^k-ℕ k@1 = refl
  lemma-Z^k-ℕ k@(₁₊ k'@(₁₊ k'')) = begin
    Z • Z ^ k' ≈⟨ (cright lemma-Z^k-ℕ k') ⟩
    Z • H • H • S ^ k' • H • H • S⁻¹ ^ k' ≈⟨ refl ⟩
    (H • H • S • H • H • S⁻¹) • H • H • S ^ k' • H • H • S⁻¹ ^ k' ≈⟨ special-assoc (□ ^ 6 • □ ^ 6) (□ ^ 5 • □ ^ 6 • □) auto ⟩
    (H • H • S • H • H) • (S⁻¹ • H • H • S ^ k' • H • H) • S⁻¹ ^ k' ≈⟨ (cright cleft word-comm p-1 1 (lemma-comm-SHHS^kHH k')) ⟩
    (H • H • S • H • H) • ((H • H • S ^ k' • H • H) • S⁻¹) • S⁻¹ ^ k' ≈⟨ special-assoc (□ ^ 5 • (□ ^ 5 • □) • □) (□ ^ 7 • □ ^ 3 • □ ^ 2) auto ⟩
    (H • H • S • H • H • H • H) • (S ^ k' • H • H) • S⁻¹ • S⁻¹ ^ k' ≈⟨ (cleft (cright cright trans (cright lemma-order-H) right-unit)) ⟩
    (H • H • S) • (S ^ k' • H • H) • S⁻¹ ^ ₁₊ k' ≈⟨ special-assoc (□ ^ 3 • □ ^ 3 • □) (□ ^ 2 • □ ^ 2 • □ ^ 3) auto ⟩
    (H • H) • (S • S ^ k') • H • H • S⁻¹ ^ ₁₊ k' ≈⟨ refl ⟩
    (H • H) • S ^ ₁₊ k' • H • H • S⁻¹ ^ ₁₊ k' ≈⟨ assoc ⟩
    H • H • S ^ k • H • H • S⁻¹ ^ k ∎
    where
    open SR word-setoid
    open Pattern-Assoc


  lemma-X^k-ℕ : ∀ k -> X ^ k ≈ H • S ^ k • H • H • S⁻¹ ^ k • H
  lemma-X^k-ℕ k@0 = sym (by-assoc-and lemma-order-H auto auto)
  lemma-X^k-ℕ k@1 = refl
  lemma-X^k-ℕ k@(₁₊ k'@(₁₊ k'')) = begin
    X • X ^ k' ≈⟨ (cright lemma-X^k-ℕ k') ⟩
    X • H • S ^ k' • H • H • S⁻¹ ^ k' • H ≈⟨ refl ⟩
    (H • S • H • H • S⁻¹ • H) • H • S ^ k' • H • H • S⁻¹ ^ k' • H ≈⟨ special-assoc (□ ^ 6 • □ ^ 6) (□ ^ 4 • □ ^ 6 • □ ^ 2) auto ⟩
    (H • S • H • H) • (S⁻¹ • H • H • S ^ k' • H • H) • S⁻¹ ^ k' • H ≈⟨ (cright cleft word-comm p-1 1 (lemma-comm-SHHS^kHH k')) ⟩
    (H • S • H • H) • ((H • H • S ^ k' • H • H) • S⁻¹) • S⁻¹ ^ k' • H ≈⟨ special-assoc (□ ^ 4 • (□ ^ 5 • □) • □ ^ 2) (□ ^ 6 • □ ^ 3 • □ ^ 2 • □) auto ⟩
    (H • S • H • H • H • H) • (S ^ k' • H • H) • (S⁻¹ • S⁻¹ ^ k') • H ≈⟨ (cleft (cright trans (cright lemma-order-H) right-unit)) ⟩
    (H • S) • (S ^ k' • H • H) • S⁻¹ ^ k • H ≈⟨ special-assoc (□ ^ 2 • □ ^ 3 • □ ^ 2) (□ • □ ^ 2 • □ ^ 4) auto ⟩
    H • (S • S ^ k') • H • H • S⁻¹ ^ k • H ≈⟨ refl ⟩
    H • S ^ k • H • H • S⁻¹ ^ k • H ∎
    where
    open SR word-setoid
    open Pattern-Assoc


  lemma-order-w^k : ∀ (w : Word (Gen (₁₊ n))) o k -> w ^ o ≈ ε -> (w ^ k) ^ o ≈ ε
  lemma-order-w^k w o k eq = begin
    (w ^ k) ^ o ≈⟨ lemma-^^' w k o ⟩
    (w ^ o) ^ k ≈⟨ lemma-^-cong (w ^ o) ε k eq ⟩
    ε ^ k ≈⟨ lemma-ε^k=ε k ⟩
    ε ∎
    where
    open SR word-setoid
    open Pattern-Assoc


  lemma-order-Z : Z ^ p ≈ ε
  lemma-order-Z = begin
    Z ^ p ≈⟨ lemma-Z^k-ℕ p ⟩
    H • H • S ^ p • H • H • S⁻¹ ^ p ≈⟨ (cright cright cong (axiom order-S) (cright cright lemma-order-w^k S p p-1 (axiom order-S))) ⟩
    H • H • ε • H • H • ε ≈⟨ by-assoc auto ⟩
    H • H • H • H ≈⟨ lemma-order-H ⟩
    ε ∎
    where
    open SR word-setoid
    open Pattern-Assoc


  lemma-order-X : X ^ p ≈ ε
  lemma-order-X = begin
    X ^ p ≈⟨ lemma-X^k-ℕ p ⟩
    H • S ^ p • H • H • S⁻¹ ^ p • H ≈⟨ (cright  cong (axiom order-S) (cright cright cleft lemma-order-w^k S p p-1 (axiom order-S))) ⟩
    H • ε • H • H • ε • H ≈⟨ by-assoc auto ⟩
    H • H • H • H ≈⟨ lemma-order-H ⟩
    ε ∎
    where
    open SR word-setoid
    open Pattern-Assoc


  lemma-comm-Z-S : Z • S ≈ S • Z
  lemma-comm-Z-S = begin
    (H • H • S • H • H • S⁻¹) • S ≈⟨ special-assoc (□ ^ 6 • □) (□ ^ 5 • □ ^ 2 ) auto ⟩
    (H • H • S • H • H) • S⁻¹ • S ≈⟨ (cright word-comm p-1 1 refl) ⟩
    (H • H • S • H • H) • S • S⁻¹ ≈⟨ sym (special-assoc (□ ^ 6 • □) (□ ^ 5 • □ ^ 2 ) auto) ⟩
    (H • H • S • H • H • S) • S⁻¹ ≈⟨ (cleft axiom comm-HHSHHS) ⟩
    (S • H • H • S • H • H) • S⁻¹ ≈⟨ special-assoc (□ ^ 6 • □) (□ • □ ^ 6) auto ⟩
    S • (H • H • S • H • H • S⁻¹) ≈⟨ refl ⟩
    S • Z ∎
    where
    open SR word-setoid
    open Pattern-Assoc
  
  lemma-order-𝑠 : 𝑠 ^ p ≈ ε
  lemma-order-𝑠 = begin
    (S • Z^ 1/2) ^ p ≈⟨ lemma-^-cong (S • Z^ 1/2) (Z^ 1/2 • S) p (word-comm 1 (toℕ 1/2) (sym lemma-comm-Z-S)) ⟩
    (Z^ 1/2 • S) ^ p ≈⟨ lemma-^-• (Z^ 1/2) S p (word-comm (toℕ 1/2) 1 lemma-comm-Z-S) ⟩
    Z^ 1/2 ^ p • S ^ p ≈⟨ (cright axiom order-S) ⟩
    Z^ 1/2 ^ p • ε ≈⟨ right-unit ⟩
    Z^ 1/2 ^ p ≈⟨ lemma-order-w^k Z p (toℕ 1/2) lemma-order-Z ⟩
    ε ∎
    where
    open SR word-setoid
    
  lemma-𝑠^k-% : ∀ k -> 𝑠 ^ k ≈ 𝑠 ^ (k % p)
  lemma-𝑠^k-% k = begin
    𝑠 ^ k ≡⟨ Eq.cong (𝑠 ^_) (m≡m%n+[m/n]*n k p) ⟩
    𝑠 ^ (k Nat.% p Nat.+ k Nat./ p Nat.* p) ≈⟨ lemma-^-+ 𝑠 (k Nat.% p) (k Nat./ p Nat.* p) ⟩
    𝑠 ^ (k Nat.% p) • 𝑠 ^ (k Nat./ p Nat.* p) ≈⟨ (cright refl' (Eq.cong (𝑠 ^_) (NP.*-comm (k Nat./ p) p))) ⟩
    𝑠 ^ (k Nat.% p) • 𝑠 ^ (p Nat.* (k Nat./ p)) ≈⟨ sym (cright lemma-^^ 𝑠 p (k Nat./ p)) ⟩
    𝑠 ^ (k Nat.% p) • (𝑠 ^ p) ^ (k Nat./ p) ≈⟨ (cright lemma-^-cong (𝑠 ^ p) ε (k Nat./ p) (lemma-order-𝑠)) ⟩
    𝑠 ^ (k Nat.% p) • (ε) ^ (k Nat./ p) ≈⟨ (cright lemma-ε^k=ε (k Nat./ p)) ⟩
    𝑠 ^ (k Nat.% p) • ε ≈⟨ right-unit ⟩
    𝑠 ^ (k % p) ∎
    where
    open SR word-setoid






  lemma-Mg𝑠^k' : ∀ k -> let x⁻¹ = (g′ ⁻¹) .proj₁ in let -x⁻¹ = - x⁻¹ in
    Mg • 𝑠^ k ≈ 𝑠^ (k * (g * g)) • Mg
  lemma-Mg𝑠^k' k = begin 
    Mg • 𝑠^ k ≈⟨ refl ⟩
    Mg • 𝑠 ^ toℕ k ≈⟨ lemma-Mg𝑠^k (toℕ k) ⟩
    𝑠 ^ (toℕ k Nat.* toℕ (g * g)) • Mg ≈⟨ (cleft lemma-𝑠^k-% (toℕ k Nat.* toℕ (g * g))) ⟩
    𝑠 ^ ((toℕ k Nat.* toℕ (g * g)) % p) • Mg ≈⟨ (cleft refl' (Eq.cong (𝑠 ^_) (lemma-toℕ-% k (g * g)))) ⟩
    𝑠 ^ toℕ (k * (g * g)) • Mg ≈⟨ refl ⟩
    𝑠^ (k * (g * g)) • Mg ∎
    where
    open SR word-setoid
    x⁻¹ = (g′ ⁻¹) .proj₁
    -x⁻¹ = - x⁻¹

  lemma-Mg^k𝑠 : ∀ k -> Mg ^ k • 𝑠 ≈ 𝑠^ ((g * g) ^′ k) • Mg ^ k
  lemma-Mg^k𝑠 k@0 = trans left-unit (sym right-unit)
  lemma-Mg^k𝑠 k@1 = begin
    Mg ^ k • 𝑠 ≈⟨ axiom semi-M𝑠 ⟩
    𝑠^ ((g * g)) • Mg ^ k ≈⟨ (cleft refl' ( Eq.cong 𝑠^ (Eq.sym (lemma-x^′1=x (fromℕ< _))))) ⟩ -- 
    𝑠^ ((g * g) ^′ k) • Mg ^ k ∎
    where
    open SR word-setoid
  lemma-Mg^k𝑠 k@(₂₊ n) = begin
    (Mg • Mg ^ ₁₊ n) • 𝑠 ≈⟨ assoc ⟩
    Mg • Mg ^ ₁₊ n • 𝑠 ≈⟨ (cright lemma-Mg^k𝑠 (₁₊ n)) ⟩
    Mg • 𝑠^ ((g * g) ^′ (₁₊ n)) • Mg ^ (₁₊ n) ≈⟨ sym assoc ⟩
    (Mg • 𝑠^ ((g * g) ^′ (₁₊ n))) • Mg ^ (₁₊ n) ≈⟨ (cleft lemma-Mg𝑠^k' ((g * g) ^′ (₁₊ n))) ⟩
    (𝑠^ (((g * g) ^′ (₁₊ n)) * (g * g)) • Mg) • Mg ^ (₁₊ n) ≈⟨ refl' (Eq.cong (\ xx -> (𝑠^ xx • Mg) • Mg ^ (₁₊ n)) (*-comm ((g * g) ^′ (₁₊ n)) (g * g))) ⟩
    (𝑠^ ((g * g) * ((g * g) ^′ (₁₊ n))) • Mg) • Mg ^ (₁₊ n) ≈⟨ assoc ⟩
    𝑠^ ((g * g) ^′ k) • Mg • Mg ^ ₁₊ n ∎
    where
    open SR word-setoid


  lemma-semi-M𝑠 : ∀ x -> let x' = x .proj₁ in let k = g-gen x .proj₁ in M x • 𝑠 ≈ 𝑠^ ((x' * x')) • M x
  lemma-semi-M𝑠 x = begin
    M x • 𝑠 ≈⟨ (cleft refl' (aux-M≡M x (g^ k) (eqk))) ⟩
    M (g^ k) • 𝑠 ≈⟨ cong (sym (axiom (M-power (k)))) refl ⟩
    Mg^ k • 𝑠 ≈⟨ lemma-Mg^k𝑠 (toℕ k) ⟩
    𝑠^ ((g * g) ^′ toℕ k) • Mg^ k ≈⟨ (cright axiom (M-power (k))) ⟩
    𝑠^ ((g * g) ^′ toℕ k) • M (g^ k) ≈⟨ (cleft refl' (Eq.cong 𝑠^ (*-^′-distribʳ g g (toℕ k)))) ⟩
    𝑠^ ((g ^′ toℕ k) * (g ^′ toℕ k)) • M (g^ k) ≈⟨ sym (cleft refl' (Eq.cong₂ (\ xx yy -> 𝑠^ (xx * yy)) (eqk) (eqk))) ⟩
    𝑠^ (x' * x') • M (g^ k) ≈⟨ (cright refl' (aux-M≡M (g^ k) x (Eq.sym (eqk)))) ⟩
    𝑠^ (x' * x') • M x ∎
    where
    open SR word-setoid
    x' = x .proj₁
    k = inject₁ (g-gen x .proj₁)
    eqk : x .proj₁ ≡ (g^ k) .proj₁
    eqk = Eq.sym (lemma-log-inject x)



module Clifford-GroupLike where

  private
    variable
      n : ℕ
    
  open Clifford-Relations
  open Lemmas-Clifford


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



-- ----------------------------------------------------------------------
-- * Data required for applying word tactics to Symplectic generators

module CommData-Sim where
  variable
    n : ℕ

  open Clifford-Relations
  open Lemmas-Clifford
  
  
  -- Commutativity.
  commute : (x y : Gen (₂₊ n)) → let open PB ((₂₊ n) QRel,_===_) in Maybe (([ x ]ʷ • [ y ]ʷ) ≈ ([ y ]ʷ • [ x ]ʷ))
  commute {n} H-gen (y ↥) = just (PB.sym (PB.axiom comm-H))
  commute {n} (x ↥) H-gen = just (PB.axiom comm-H)
  commute {n} S-gen (y ↥) = just (PB.sym (PB.axiom comm-S))
  commute {n} (x ↥) S-gen = just (PB.axiom comm-S)
  commute {n} S-gen CZ-gen = just (PB.sym (PB.axiom comm-CZ-S↓))
  commute {n} CZ-gen S-gen = just (PB.axiom comm-CZ-S↓)
  commute {n} (S-gen ↥) CZ-gen = just (PB.sym (PB.axiom comm-CZ-S↑))
  commute {n} CZ-gen (S-gen ↥) = just (PB.axiom comm-CZ-S↑)
  
  commute {n@(suc n')} CZ-gen (CZ-gen ↥) = just (PB.sym (PB.axiom selinger-c12))
  commute {n} (CZ-gen ↥) CZ-gen = just (PB.axiom selinger-c12)
  
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

module Commuting-Symplectic-Sim (n : ℕ) where
  open Clifford-Relations
  open CommData-Sim hiding (n)
  open Commuting (((₂₊ n) QRel,_===_) ) commute les public


module Rewriting-Sim where

  open Rewriting
  open Clifford-Relations
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
    open Lemmas-Clifford
  step-sym0 {₂₊ n} ((H-gen ↥ ↥) ∷ (H-gen ↥ ↥) ∷ (H-gen ↥ ↥) ∷ (H-gen ↥ ↥) ∷ xs) = just (xs , at-head (lemma-cong↑ _ _ (lemma-cong↑ _ _ lemma-order-H)))
    where
    open Lemmas1 n
    open Lemmas-Clifford

  step-sym0 {n} ((S-gen) ∷ (H-gen) ∷ (S-gen) ∷ (H-gen) ∷ (S-gen) ∷ (H-gen) ∷ xs) = just (xs , at-head (PB.axiom order-SH))
    where
    open Lemmas1 n
  step-sym0 {₁₊ n} ((S-gen ↥) ∷ (H-gen ↥) ∷ (S-gen ↥) ∷ (H-gen ↥) ∷ (S-gen ↥) ∷ (H-gen ↥) ∷ xs) = just (xs , at-head (lemma-cong↑ _ _ (PB.axiom order-SH)))
    where
    open Lemmas1 n
    open Lemmas-Clifford
  step-sym0 {₂₊ n} ((S-gen ↥ ↥) ∷ (H-gen ↥ ↥) ∷ (S-gen ↥ ↥) ∷ (H-gen ↥ ↥) ∷ (S-gen ↥ ↥) ∷ (H-gen ↥ ↥) ∷ xs) = just (xs , at-head (lemma-cong↑ _ _ (lemma-cong↑ _ _ (PB.axiom order-SH))))
    where
    open Lemmas1 n
    open Lemmas-Clifford

  -- Commuting of generators.
  step-sym0 ((S-gen) ∷ (CZ-gen) ∷ xs) = just ((CZ-gen) ∷ (S-gen) ∷ xs , at-head (PB.sym (PB.axiom comm-CZ-S↓)))
  step-sym0 ((S-gen ↥) ∷ (CZ-gen) ∷ xs) = just ((CZ-gen) ∷ (S-gen ↥) ∷ xs , at-head (PB.sym (PB.axiom comm-CZ-S↑)))
  step-sym0 ((S-gen ↥) ∷ (CZ-gen ↥) ∷ xs) = just ((CZ-gen ↥) ∷ (S-gen ↥) ∷ xs , at-head (PB.sym (PB.axiom (cong↑ comm-CZ-S↓))))
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
  step-sym0 ((CZ-gen ↥) ∷ (CZ-gen) ∷ xs) = just ((CZ-gen) ∷ (CZ-gen ↥) ∷ xs , at-head ((PB.axiom selinger-c12)))

  step-sym0 {n} ((S-gen) ∷ (H-gen) ∷ (H-gen) ∷ (S-gen) ∷ (H-gen) ∷ (H-gen) ∷ xs) = just ((H-gen) ∷ (H-gen) ∷ (S-gen) ∷ (H-gen) ∷ (H-gen) ∷ (S-gen) ∷ xs , at-head (PB.sym (PB.axiom comm-HHSHHS)))
  step-sym0 {n} ((S-gen ↥) ∷ (H-gen ↥) ∷ (H-gen ↥) ∷ (S-gen ↥) ∷ (H-gen ↥) ∷ (H-gen ↥) ∷ xs) = just ((H-gen ↥) ∷ (H-gen ↥) ∷ (S-gen ↥) ∷ (H-gen ↥) ∷ (H-gen ↥) ∷ (S-gen ↥) ∷ xs , at-head (PB.sym (PB.axiom (cong↑  comm-HHSHHS))))
  step-sym0 {n} ((S-gen ↥ ↥) ∷ (H-gen ↥ ↥) ∷ (H-gen ↥ ↥) ∷ (S-gen ↥ ↥) ∷ (H-gen ↥ ↥) ∷ (H-gen ↥ ↥) ∷ xs) = just ((H-gen ↥ ↥) ∷ (H-gen ↥ ↥) ∷ (S-gen ↥ ↥) ∷ (H-gen ↥ ↥) ∷ (H-gen ↥ ↥) ∷ (S-gen ↥ ↥) ∷ xs , at-head (PB.sym (PB.axiom (cong↑ (cong↑ comm-HHSHHS)))))


  -- Catch-all
  step-sym0 _ = nothing

module Sim-Rewriting (n : ℕ) where
  open Rewriting
  open Rewriting-Sim hiding (n)
  open Rewriting.Step (step-cong (step-sym0 {n})) renaming (general-rewrite to rewrite-sim) public



module Lemmas1b (n : ℕ) where


  open Clifford-Relations
  open Lemmas-Clifford
  open Lemmas1 n

  open PB ((₁₊ n) QRel,_===_) hiding (_===_)
  open PP ((₁₊ n) QRel,_===_)
  open SR word-setoid
  open Pattern-Assoc
  open Clifford-GroupLike
  open import Data.Nat.DivMod
  open import Data.Fin.Properties


  aux-S⁻¹⁻¹ : 
    S⁻¹ ^ p-1 ≈ S
  aux-S⁻¹⁻¹ = lemma-right-cancel {h = S⁻¹} aux00
    where
    open Sym0-Rewriting n
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
    open Sym0-Rewriting n
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
    open Sym0-Rewriting n
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
    (H ^ 3 • S⁻¹) • H • S⁻¹ • H ≈⟨ (cright cleft rewrite-sim 100  auto) ⟩
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
    open Sim-Rewriting n

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

  conj-S^l-X^k : ∀ l k -> S ^ l • X ^ k ≈ X ^ k • (Z ^ l • S ^ l) ^ k
  conj-S^l-X^k l k = begin
    S ^ l • X ^ k ≈⟨ lemma-Induction (conj-S^l-X' l) k ⟩
    (X • Z ^ l) ^ k • S ^ l ≈⟨ {!!} ⟩
    (X • Z ^ l) ^ k • S ^ l ≈⟨ {!!} ⟩
    X ^ k • (Z ^ l • S ^ l) ^ k ∎  

  aux-X⁻¹ : X⁻¹ ≈ H • S⁻¹ • H • H • S • H
  aux-X⁻¹ = begin
    X⁻¹ ≈⟨ lemma-X^k-ℕ p-1 ⟩
    H • S⁻¹ • H • H • S⁻¹ ^ p-1 • H ≈⟨ (cright cright cright cright cleft aux-S⁻¹⁻¹) ⟩
    H • S⁻¹ • H • H • S • H ∎
    where
    open Sim-Rewriting n


  aux-Z⁻¹ : Z⁻¹ ≈ H • H • S ^ p-1 • H • H • S
  aux-Z⁻¹ = begin
    Z⁻¹ ≈⟨ lemma-Z^k-ℕ p-1 ⟩
    H • H • S ^ p-1 • H • H • S⁻¹ ^ p-1 ≈⟨ (cright cright cright cright cright aux-S⁻¹⁻¹) ⟩
    H • H • S ^ p-1 • H • H • S ∎
    where
    open Sim-Rewriting n

  lemma-order-S⁻¹H' : (S⁻¹ • H) ^ 3 ≈ HH
  lemma-order-S⁻¹H' = begin
    (S⁻¹ • H) ^ 3 ≈⟨ {!!} ⟩





    S ^ p-1 • H • (S ^ p-1 • X ^ (toℕ 1/2 Nat.* p-1) ) • Z^ 1/2 ^ p-1 • H • (S ^ p-1 • Z^ 1/2  ^ p-1) • H ≈⟨ {!!} ⟩
    S ^ p-1 • H • (X ^ (toℕ 1/2 Nat.* p-1) • S ^ p-1) • Z^ 1/2 ^ p-1 • H • (S ^ p-1 • Z^ 1/2  ^ p-1) • H ≈⟨ (cright cright cleft cleft sym (lemma-^^ X (toℕ 1/2) p-1)) ⟩
    S ^ p-1 • H • (X^ 1/2 ^ p-1 • S ^ p-1) • Z^ 1/2 ^ p-1 • H • (S ^ p-1 • Z^ 1/2  ^ p-1) • H ≈⟨ (cright special-assoc (□ • □ ^ 2 • □ • □) (□ ^ 2 • □ ^ 2 • □) auto) ⟩

    S ^ p-1 • (H • X^ 1/2 ^ p-1) • (S ^ p-1 • Z^ 1/2 ^ p-1) • H • (S ^ p-1 • Z^ 1/2  ^ p-1) • H ≈⟨ (cright cleft lemma-Induction (lemma-Induction conj-H-X (toℕ 1/2)) p-1) ⟩
    S ^ p-1 • (Z^ 1/2 ^ p-1 • H) • (S ^ p-1 • Z^ 1/2 ^ p-1) • H • (S ^ p-1 • Z^ 1/2  ^ p-1) • H ≈⟨ special-assoc (□ • □ ^ 2 • □) (□ ^ 2 • □ • □) auto ⟩
    (S ^ p-1 • Z^ 1/2 ^ p-1) • H • (S ^ p-1 • Z^ 1/2 ^ p-1) • H • (S ^ p-1 • Z^ 1/2  ^ p-1) • H ≈⟨ cong (sym (lemma-^-• S (Z^ 1/2) (p-1) (word-comm 1 (toℕ 1/2) (sym lemma-comm-Z-S)))) (cright cong ((sym (lemma-^-• S (Z^ 1/2) (p-1) (word-comm 1 (toℕ 1/2) (sym lemma-comm-Z-S))))) (cright cleft (sym (lemma-^-• S (Z^ 1/2) (p-1) (word-comm 1 (toℕ 1/2) (sym lemma-comm-Z-S)))))) ⟩
    (S • Z^ 1/2) ^ p-1 • H • (S • Z^ 1/2) ^ p-1 • H • (S • Z^ 1/2) ^ p-1 • H ≈⟨ refl ⟩
    (S • Z^ 1/2) ^ p-1 • H • (S • Z^ 1/2) ^ p-1 • H • (S • Z^ 1/2) ^ p-1 • H ≈⟨ refl ⟩
    𝑠 ^ p-1 • H • 𝑠 ^ p-1 • H • 𝑠 ^ p-1 • H ≈⟨ cong (refl' (Eq.cong (𝑠 ^_) (Eq.sym lemma-toℕ-1ₚ))) (cright cong ((refl' (Eq.cong (𝑠 ^_) (Eq.sym (Eq.trans (Eq.cong toℕ aux-₁⁻¹ ) lemma-toℕ-1ₚ))))) (cright cleft (refl' (Eq.cong (𝑠 ^_) (Eq.sym lemma-toℕ-1ₚ))))) ⟩
    𝑠^ x • H • 𝑠^ x⁻¹ • H • 𝑠^ x • H ≈⟨ refl ⟩
    M -'₁ ≈⟨ sym (axiom order-H) ⟩
    HH ∎
    where
    x' = -'₁
    x = x' .proj₁
    x⁻¹ = ((x' ⁻¹) .proj₁ )
    
  lemma-order-S⁻¹H  : (S⁻¹ • H) ^ 6 ≈ ε
  lemma-order-S⁻¹H  = begin
    (S⁻¹ • H) ^ 6 ≈⟨ {!!} ⟩
    S⁻¹ • H • S⁻¹ • H • S⁻¹ • H • S⁻¹ • H • S⁻¹ • H • S⁻¹ • H ≈⟨ {!!} ⟩
    (S • S ^ p-3 • S) • H • (S • S ^ p-3 • S) • H • (S • S ^ p-3 • S) • H • (S • S ^ p-3 • S) • H • (S • S ^ p-3 • S) • H • (S • S ^ p-3 • S) • H ≈⟨ {!!} ⟩
    (S • S ^ p-3) • (S • H • S) • S ^ p-3 • (S • H • S) • S ^ p-3 • (S • H • S) • S ^ p-3 • (S • H • S) • S ^ p-3 • (S • H • S) • S ^ p-3 • S • H ≈⟨ {!!} ⟩
    (S • S ^ p-3) • (H ^ 3 • S ^ p-1 • H ^ 3) • S ^ p-3 • (H ^ 3 • S ^ p-1 • H ^ 3) • S ^ p-3 • (H ^ 3 • S ^ p-1 • H ^ 3) • S ^ p-3 • (H ^ 3 • S ^ p-1 • H ^ 3) • S ^ p-3 • (H ^ 3 • S ^ p-1 • H ^ 3)   • S ^ p-3 • S • H ≈⟨ {!!} ⟩
    ε ∎
    where
    open Sim-Rewriting n

  aux-XZX⁻¹Z⁻¹ : X • Z • X⁻¹ • Z⁻¹ ≈ ε
  aux-XZX⁻¹Z⁻¹ = begin
    (H • S • H • H • S⁻¹ • H) • (H • H • S • H • H • S⁻¹) • (H • S • H • H • S⁻¹ • H) ^ p-1 • (H • H • S • H • H • S⁻¹) ^ p-1 ≈⟨ (cright cright cong aux-X⁻¹ aux-Z⁻¹) ⟩
    (H • S • H • H • S⁻¹ • H) • (H • H • S • H • H • S⁻¹) • (H • S⁻¹ • H • H • S • H) • (H • H • S⁻¹ • H • H • S) ≈⟨ {!!} ⟩
    (H • S • H • H • S⁻¹ • H) • (H • H • S • H • H • S⁻¹) • (H • S⁻¹ • H • H • S • H) • (S • H • H • S⁻¹ • H • H) ≈⟨ {!!} ⟩
    (H • S • H • H • S⁻¹ • H) • (H • H • S • H • H • S⁻¹) • (H • S⁻¹ • H) • (H • S • H • S • H) • H • S⁻¹ • H • H ≈⟨ {!!} ⟩
    (H • S • H • H • S⁻¹ • H) • (H • H • S • H • H • S⁻¹) • (H • S⁻¹ • H) • (S⁻¹) • H • S⁻¹ • H • H ≈⟨ {!!} ⟩
    ε ∎
    where
    open Sim-Rewriting n

  aux-XZ : X • Z ≈ H ^ 3 • S⁻¹ • H • S⁻¹ • H • S⁻¹
  aux-XZ = sym (begin
    H ^ 3 • S⁻¹ • H • S⁻¹ • H • S⁻¹ ≈⟨ sym assoc ⟩
    (H ^ 3 • S⁻¹) • H • S⁻¹ • H • S⁻¹ ≈⟨ (cright cleft rewrite-sim 100  auto) ⟩
    (H ^ 3 • S⁻¹) • H ^ 5 • S⁻¹ • H • S⁻¹ ≈⟨ sym (special-assoc (□ ^ 5 • □ • □ ^ 3 • □ ^ 2) ((□ ^ 3 • □ )• □ ^ 5 • □ ^ 2) auto) ⟩
    (H • H • H • S⁻¹ • H) • (H • H ^ 3 • S⁻¹ • H • S⁻¹) ≈⟨ (cleft (cright sym left-unit)) ⟩
    (H • ε • H • H • S⁻¹ • H) • (H • H ^ 3 • S⁻¹ • H • S⁻¹) ≈⟨ (cleft cright cleft sym (axiom order-S)) ⟩
    (H • (S • S⁻¹) • H • H • S⁻¹ • H) • (H • H ^ 3 • S⁻¹ • H • S⁻¹) ≈⟨ special-assoc ((□ • □ ^ 2 • □ ^ 4) • □ ^ 4) (□ ^ 2 • □ ^ 6 • □ ^ 3) auto ⟩
    (H • S) • (S⁻¹ • H • H • S⁻¹ • H • H) • H ^ 3 • S⁻¹ • H • S⁻¹ ≈⟨ (cright cleft word-comm p-1 1 (lemma-comm-SHHS^kHH p-1)) ⟩
    (H • S) • ((H • H • S⁻¹ • H • H) • S⁻¹) • H ^ 3 • S⁻¹ • H • S⁻¹ ≈⟨ special-assoc (□ ^ 2 • (□ ^ 5 • □) • □ ^ 3) (□ ^ 6 • □ • □ ^ 3 • □) auto ⟩
    (H • S • H • H • S⁻¹ • H) • H • (S⁻¹ • H ^ 3 • S⁻¹) • H • S⁻¹ ≈⟨ (cright cright cleft sym lemma-HSH) ⟩
    (H • S • H • H • S⁻¹ • H) • H • (H • S • H) • H • S⁻¹ ≈⟨ special-assoc (□ ^ 6 • □ • □ ^ 3 • □ ^ 2) (□ ^ 6 • □ ^ 6) auto ⟩
    X • Z ∎)
    where
    open Sim-Rewriting n

  lemma-comm-XZ : X • Z ≈ Z • X
  lemma-comm-XZ = begin
    (H • S • H • H • S⁻¹ • H) • H • H • S • H • H • S⁻¹ ≈⟨ aux-XZ ⟩
    H ^ 3 • S⁻¹ • H • S⁻¹ • H • S⁻¹ ≈⟨ {!!} ⟩
    (H • H • S • H • H • S⁻¹) • (H • S • H • H • S⁻¹ • H) ≈⟨ {!!} ⟩

    Z • X ∎
    where
    open Sim-Rewriting n

  lemma-XS : X • S ≈ (S • Z ^ p-1) • X
  lemma-XS = begin
    X • S ≈⟨ bbc ε Z claim ⟩
    S • X • Z ^ p-1 ≈⟨ {!!} ⟩
    (S • Z ^ p-1) • X ∎
    where
    open Basis-Change _ ((₁₊ n) QRel,_===_) grouplike
    claim : ε • (X • S) • Z ≈ ε • (S • X • Z ^ p-1) • Z
    claim = begin
      ε • (X • S) • Z ≈⟨ left-unit ⟩
      (X • S) • Z ≈⟨ assoc ⟩
      X • S • Z ≈⟨ (cright sym lemma-comm-Z-S) ⟩
      X • Z • S ≈⟨ sym lemma-SX ⟩
      (S • X) ≈⟨ sym right-unit ⟩
      (S • X) • ε ≈⟨ (cright sym lemma-order-Z) ⟩
      (S • X) • Z • Z ^ p-1 ≈⟨ (cright word-comm 1 p-1 refl) ⟩
      (S • X) • Z ^ p-1 • Z ≈⟨ special-assoc (□ ^ 2 • □ ^ 2) (□ ^ 3 • □) auto ⟩
      (S • X • Z ^ p-1) • Z ≈⟨ sym left-unit ⟩
      ε • (S • X • Z ^ p-1) • Z ∎
  

  lemma-order-Z^kSH : ∀ k -> (S • Z^ k • H) ^ 3 ≈ ε
  lemma-order-Z^kSH k = begin
    (S • Z^ k • H) ^ 3 ≈⟨ refl ⟩
    (S • Z^ k • H) • (S • Z^ k • H) • (S • Z^ k • H) ≈⟨ (cleft cright sym (conj-H-X^k (toℕ k))) ⟩
    (S • H • X^ k) • (S • Z^ k • H) • (S • Z^ k • H) ≈⟨ special-assoc (□ ^ 3 • □ ^ 3 • □ ^ 3) (□ ^ 2 • □ ^ 2 • □ ^ 2 • □ ^ 3) auto ⟩
    (S • H) • (X^ k • S) • (Z^ k • H) • (S • Z^ k • H) ≈⟨ {!!} ⟩
    (S • H) • (S • X^ k • Z^ k) • (Z^ k • H) • (S • Z^ k • H) ≈⟨ {!!} ⟩

    ε ∎


  lemma-order-SH : (S • H) ^ 3 ≈ ε
  lemma-order-SH = begin
    (S • H) ^ 3 ≈⟨ by-assoc auto ⟩
    S • H • S • H • S • H ≈⟨ (cright (cright cong {!!} refl)) ⟩
    S^ x • H • S^ x⁻¹ • H • S^ x • H ≈⟨ {!!} ⟩
    M₁ ≈⟨ lemma-M1 ⟩
    ε ∎
    where
  
    x' : ℤ* ₚ
    x' = (₁ , λ ())
    x = x' .proj₁
    x⁻¹ = ((x' ⁻¹) .proj₁ )
    -- aux-S : S ≈ S^ x⁻¹
    -- aux-S = begin
    --   S ≈⟨ refl ⟩
    --   S^ ₁ ≡⟨ Eq.cong S^ (Eq.sym aux₁⁻¹') ⟩
    --   S^ x⁻¹ ∎

{-
{-





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
    M (x , nz) • S ≈⟨ lemma-semi-M𝑠 (x , nz) ⟩
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
    M₋₁ • S ≈⟨ lemma-semi-M𝑠 -'₁ ⟩
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






module Lemmas2 (n : ℕ) where

  open Clifford-Relations
  open Clifford-GroupLike

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
    Mg • CZ ≈⟨ axiom semi-M↓CZ ⟩
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
    Mg ^ k • CZ ≈⟨ axiom semi-M↓CZ ⟩
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



  lemma-semi-M↓CZ : ∀ x -> let x' = x .proj₁ in let k = g-gen x .proj₁ in M x • CZ ≈ CZ^ x' • M x
  lemma-semi-M↓CZ x = begin
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
    Mg ↑ • CZ ≈⟨ axiom semi-M↑CZ ⟩
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
    Mg ↑ ^ k • CZ ≈⟨ axiom semi-M↑CZ ⟩
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



  lemma-semi-M↑CZ : ∀ x -> let x' = x .proj₁ in let k = g-gen x .proj₁ in M x ↑ • CZ ≈ CZ^ x' • M x ↑ 
  lemma-semi-M↑CZ x = begin
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
    open Lemmas-Clifford
    open SR word-setoid
    x' = x .proj₁
    k = inject₁ (g-gen x .proj₁)
    eqk : x .proj₁ ≡ (g^ k) .proj₁
    eqk = Eq.sym (lemma-log-inject x)



module Lemmas0b (n : ℕ) where

  open Clifford-Relations
  open Clifford-GroupLike

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
    open Sim-Rewriting n


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


{-
module Clifford-Lemmas1 (n : ℕ) where
  open Clifford-Relations
  open Clifford-GroupLike

  open PB ((₁₊ n) QRel,_===_) hiding (_===_)
  open PP ((₁₊ n) QRel,_===_)
  open Pattern-Assoc
  open import Data.Nat.DivMod
  open import Data.Fin.Properties
  open Lemmas1 n
  open Lemmas1b n
  open SR word-setoid
  
  lemma-order-HH : HH ^ 2 ≈ ε
  lemma-order-HH = begin
    (H ^ 2) ^ 2 ≈⟨ assoc ⟩
    (H ^ 4) ≈⟨ axiom {!!} ⟩
    ε ∎


  lemma-order-Z : Z ^ 2 • Z ≈ ε
  lemma-order-Z = begin
    Z ^ 2 • Z ≈⟨ by-assoc auto ⟩
    (H • H • S • H • H • S) • (S • H • H • S • H • H) • S ^ 2 • (H • H • S • H • H • S) • S ≈⟨ cong (_≈_.axiom comm-HHSHHS) (_≈_.cong (_≈_.sym (_≈_.axiom comm-HHSHHS)) _≈_.refl) ⟩
    (S • H • H • S • H • H) • (H • H • S • H • H • S) • S ^ 2 • (H • H • S • H • H • S) • S ≈⟨ by-assoc auto ⟩
    (S • H • H • S) • H ^ 4 • (S • H • H) • S ^ 3 • (H • H • S • H • H • S) • S ≈⟨ cong _≈_.refl (cong (_≈_.axiom order-H) (_≈_.cong _≈_.refl (_≈_.cong (_≈_.axiom order-S) _≈_.refl))) ⟩
    (S • H • H • S) • ε • (S • H • H) • ε • (H • H • S • H • H • S) • S ≈⟨ by-assoc auto ⟩
    (S • H • H • S • S) • H ^ 4 • S • H • H • S • S ≈⟨ _≈_.cong _≈_.refl (_≈_.cong (_≈_.axiom order-H) _≈_.refl) ⟩
    (S • H • H • S • S) • ε • S • H • H • S • S ≈⟨ by-assoc auto ⟩
    (S • H • H) • S ^ 3 • H • H • S • S ≈⟨ _≈_.cong _≈_.refl (_≈_.cong (_≈_.axiom order-S) _≈_.refl) ⟩
    (S • H • H) • ε • H • H • S • S ≈⟨ by-assoc auto ⟩
    S • H ^ 4 • S • S ≈⟨ _≈_.cong _≈_.refl (_≈_.cong (_≈_.axiom order-H) _≈_.refl) ⟩
    S • ε • S • S ≈⟨ _≈_.trans (_≈_.cong _≈_.refl _≈_.left-unit) (_≈_.axiom order-S) ⟩
    ε ∎

  lemma-order-X : X ^ 2 • X ≈ ε
  lemma-order-X = begin
    X ^ 2 • X ≈⟨ by-assoc auto ⟩
    (H • S • HH • S) • (S • H • H • S • H • H) • S ^ 2 • H • H • S • H • H • SS • H ≈⟨ cong refl (_≈_.cong (_≈_.sym (_≈_.axiom comm-HHSHHS)) _≈_.refl) ⟩
    (H • S • HH • S) • (H • H • S • H • H • S) • S ^ 2 • H • H • S • H • H • SS • H ≈⟨ by-assoc auto ⟩
    (H • S • HH • S • H • H • S • H • H) • S ^ 3 • H • H • S • H • H • SS • H ≈⟨ _≈_.cong _≈_.refl (_≈_.cong (_≈_.axiom order-S) _≈_.refl) ⟩
    (H • S • HH • S • H • H • S • H • H) • ε • H • H • S • H • H • SS • H ≈⟨ by-assoc auto ⟩
    (H • S • HH • S • H • H • S) • H ^ 4 • S • H • H • SS • H ≈⟨ _≈_.cong _≈_.refl (_≈_.cong (_≈_.axiom order-H) _≈_.refl) ⟩
    (H • S • HH • S • H • H • S) • ε • S • H • H • SS • H ≈⟨ by-assoc auto ⟩
    H • (S • H • H • S • H • H) • S ^ 2 • H • H • SS • H ≈⟨ cong refl (_≈_.cong (_≈_.sym (_≈_.axiom comm-HHSHHS)) _≈_.refl) ⟩
    H • (H • H • S • H • H • S) • S ^ 2 • H • H • SS • H ≈⟨ by-assoc auto ⟩
    (H • H • H • S • H • H) • S ^ 3 • H • H • SS • H ≈⟨ _≈_.cong _≈_.refl (_≈_.cong (_≈_.axiom order-S) _≈_.refl) ⟩
    (H • H • H • S • H • H) • ε • H • H • SS • H ≈⟨ by-assoc auto ⟩
    (H • H • H • S) • H ^ 4 • SS • H ≈⟨ _≈_.cong _≈_.refl (_≈_.cong (_≈_.axiom order-H) _≈_.refl) ⟩
    (H • H • H • S) • ε • SS • H ≈⟨ by-assoc auto ⟩
    (H • H • H) • S ^ 3 • H ≈⟨ _≈_.cong _≈_.refl (_≈_.cong (_≈_.axiom order-S) _≈_.refl) ⟩
    (H • H • H) • ε • H ≈⟨ by-assoc auto ⟩
    H • H • H • H ≈⟨ _≈_.axiom order-H ⟩
    ε ∎

  lemma-comm-Z-S : Z • S ≈ S • Z
  lemma-comm-Z-S = begin
    Z • S ≈⟨ by-assoc auto ⟩
    (H • H • S • H • H • S) • S • S ≈⟨ _≈_.cong (_≈_.axiom comm-HHSHHS) _≈_.refl ⟩
    (S • H • H • S • H • H) • S • S ≈⟨ by-assoc auto ⟩
    S • Z ∎

  lemma-SH^2 : (S • H) ^ 2 ≈ H ^ 3 • S ^ 2
  lemma-SH^2 = begin
    (S • H) ^ 2 ≈⟨ by-assoc auto ⟩
    (S • H • S • H) • ε ≈⟨ _≈_.sym (_≈_.cong _≈_.refl (_≈_.axiom order-S)) ⟩
    (S • H • S • H) • S ^ 3 ≈⟨ by-assoc auto ⟩
    (S • H • S • H • S) • ε • S ^ 2 ≈⟨ cong refl (_≈_.sym (_≈_.cong (_≈_.axiom order-H) _≈_.refl)) ⟩
    (S • H • S • H • S) • H ^ 4 • S ^ 2 ≈⟨ by-assoc auto ⟩
    (S • H) ^ 3 • H ^ 3 • S ^ 2 ≈⟨ cong (_≈_.axiom order-SH) refl ⟩
    ε • H ^ 3 • S ^ 2 ≈⟨ left-unit ⟩
    H ^ 3 • S ^ 2 ∎

  lemma-comm-HHSSHHS : H • H • S • S • H • H • S ≈ S • H • H • S • S • H • H
  lemma-comm-HHSSHHS = begin
    H • H • S • S • H • H • S ≈⟨ by-assoc Eq.refl ⟩
    (H • H • S) • S • H • H • S ≈⟨ cong refl (trans (sym left-unit) (sym (cong (axiom order-H) refl))) ⟩
    (H • H • S) • H ^ 4 • S • H • H • S ≈⟨ by-assoc Eq.refl ⟩
    (H • H • S • H  • H) • (H • H • S • H • H • S) ≈⟨ cong refl (axiom comm-HHSHHS) ⟩
    (H • H • S • H  • H) • S • (H • H • S • H • H) ≈⟨ by-assoc Eq.refl ⟩
    (H • H • S • H  • H • S) • (H • H • S • H • H) ≈⟨ cong (axiom comm-HHSHHS) refl ⟩
    (S • (H • H • S • H • H)) • (H • H • S • H • H) ≈⟨ by-assoc Eq.refl ⟩
    (S • H • H • S) • H ^ 4 • S • H • H ≈⟨ cong refl (cong (axiom order-H) refl) ⟩
    (S • H • H • S) • ε • S • H • H ≈⟨ by-assoc Eq.refl ⟩
    S • H • H • S • S • H • H ∎

  lemma-conj-HH-Z : HH • Z ≈ (Z • Z) • HH
  lemma-conj-HH-Z = begin
    HH • HH • S • HH • SS ≈⟨ by-assoc auto ⟩
    H ^ 4 • S • HH • SS ≈⟨ _≈_.trans (_≈_.cong (_≈_.axiom order-H) _≈_.refl) _≈_.left-unit ⟩
    S • HH • SS ≈⟨ by-assoc auto ⟩
    (ε • ε) • (S • H • H • S • S) • ε ≈⟨ cong (_≈_.sym (_≈_.cong (_≈_.axiom order-H) (_≈_.axiom order-S))) (_≈_.sym (_≈_.cong _≈_.refl (_≈_.axiom order-H))) ⟩
    (H ^ 4 • S ^ 3) • (S • H • H • S • S) • H ^ 4 ≈⟨ by-assoc auto ⟩
    (H ^ 4 • S ^ 3) • (S • H • H • S • S • H • H) • HH ≈⟨ cong refl (cong (_≈_.sym lemma-comm-HHSSHHS) refl) ⟩
    (H ^ 4 • S ^ 3) • (H • H • S • S • H • H • S) • HH ≈⟨ by-assoc auto ⟩
    (H ^ 4 • S • S) • (S • H • H • S • S • H • H) • S • HH ≈⟨ cong refl (cong (_≈_.sym lemma-comm-HHSSHHS) refl) ⟩
    (H ^ 4 • S • S) • (H • H • S • S • H • H • S) • S • HH ≈⟨ by-assoc auto ⟩
    HH • (H • H • S • S • H • H • S) • S • HH • SS • HH ≈⟨ cong refl (cong lemma-comm-HHSSHHS refl) ⟩
    HH • (S • H • H • S • S • H • H) • S • HH • SS • HH ≈⟨ by-assoc auto ⟩
    (Z • Z) • HH ∎


  lemma-def-XX : X • X ≈ (H • S • S • H) • (H • S • H)
  lemma-def-XX = begin
    X • X ≈⟨ by-assoc auto ⟩
    (H • S) • (H • H • S • S • H • H • S) • H • H • S • S • H ≈⟨ cong refl (cong lemma-comm-HHSSHHS refl) ⟩
    (H • S) • (S • H • H • S • S • H • H) • H • H • S • S • H ≈⟨ by-assoc Eq.refl ⟩
    (H • S • S • H • H • S • S) • H ^ 4 • S • S • H ≈⟨ general-powers 100 auto ⟩
    (H • S • S • H) • (H • S • H) ∎

  lemma-def-ZZ : Z • Z ≈ (HH • S • S • HH) • S
  lemma-def-ZZ = begin
    (HH • S • HH • SS) • (HH • S • HH • SS) ≈⟨ by-assoc auto ⟩
    (HH • S • HH • S) • (S • H • H • S • H • H) • SS ≈⟨ cong refl (sym (cong (axiom comm-HHSHHS) refl)) ⟩
    (HH • S • HH • S) • (H • H • S • H • H • S) • SS ≈⟨ by-assoc auto ⟩
    (HH • S • HH) • (S • H • H • S • H • H) • S ^ 3 ≈⟨ cong refl (cong (sym (axiom comm-HHSHHS)) (axiom order-S)) ⟩
    (HH • S • HH) • (H • H • S • H • H • S) • ε ≈⟨ general-powers 100 auto ⟩
    (HH • S • S • HH) • S ∎

  lemma-conj-HH-X : HH • X ≈ (X • X) • HH
  lemma-conj-HH-X = begin
    HH • X ≈⟨ general-powers 100 auto ⟩
    H • (H • H • S • H • H • S) • S • H ≈⟨ cong refl (cong (axiom comm-HHSHHS) refl) ⟩
    H • (S • H • H • S • H • H) • S • H ≈⟨ by-assoc auto ⟩
    (H • S) • (H • H • S • H • H • S) • H ≈⟨ cong refl (cong (axiom comm-HHSHHS) refl) ⟩
    (H • S) • (S • H • H • S • H • H) • H ≈⟨ by-assoc auto ⟩
    ((H • S • S • H) • (H • S • H)) • HH ≈⟨ cong (sym lemma-def-XX) refl ⟩
    (X • X) • HH ∎
    
  lemma-conj-HH-S : HH • S ≈ (S • Z) • HH
  lemma-conj-HH-S = begin
    HH • S ≈⟨ general-powers 100 auto ⟩
    (S • HH) • (H • H • S • S • H • H • S) ≈⟨ cong refl lemma-comm-HHSSHHS ⟩
    (S • HH) • (S • H • H • S • S • H • H) ≈⟨ by-assoc auto ⟩
    (S • HH • S • HH • SS) • HH ∎

  lemma-SHS : S • H • S ≈ H ^ 3 • S ^ 2 • H ^ 3
  lemma-SHS = begin
    S • H • S ≈⟨ general-powers 100 auto ⟩
    (S • H) ^ 3 • H ^ 3 • S ^ 2 • H ^ 3 ≈⟨ cong (axiom order-SH) refl ⟩
    ε • H ^ 3 • S ^ 2 • H ^ 3 ≈⟨ left-unit ⟩
    H ^ 3 • S ^ 2 • H ^ 3 ∎

  lemma-SHSH : S • H • S • H ≈ H ^ 3 • S ^ 2
  lemma-SHSH = begin
    S • H • S • H ≈⟨ general-powers 100 auto ⟩
    (S • H) ^ 3 • H ^ 3 • S ^ 2 ≈⟨ trans (cong (axiom order-SH) refl) left-unit ⟩
    H ^ 3 • S ^ 2 ∎

  lemma-HSH : H • S • H ≈ S ^ 2 • H ^ 3 • S ^ 2
  lemma-HSH = begin
    H • S • H ≈⟨ general-powers 100 auto ⟩
    S ^ 2 • (S • H) ^ 3 • H ^ 3 • S ^ 2 ≈⟨ cong refl (trans (cong (axiom order-SH) refl) left-unit) ⟩
    S ^ 2 • H ^ 3 • S ^ 2 ≈⟨ general-powers 100 auto ⟩
    S ^ 2 • H ^ 3 • S ^ 2 ∎

  lemma-HSHS : H • S • H • S ≈ S ^ 2 • H ^ 3
  lemma-HSHS = begin
    H • S • H • S ≈⟨ general-powers 100 auto ⟩
    S ^ 2 • (S • H) ^ 3 • H ^ 3 ≈⟨ cong refl (trans (cong (axiom order-SH) refl) left-unit) ⟩
    S ^ 2 • H ^ 3 ≈⟨ general-powers 100 auto ⟩
    S ^ 2 • H ^ 3 ∎

  lemma-SHSHS : S • H • S • H • S ≈ H ^ 3
  lemma-SHSHS = begin
    S • H • S • H • S ≈⟨ general-powers 100 auto ⟩
    (S • H) ^ 3 • H ^ 3 ≈⟨ trans (cong (axiom order-SH) refl) left-unit ⟩
    H ^ 3 ∎

  lemma-HSHSH : H • S • H • S • H ≈ S ^ 2
  lemma-HSHSH = begin
    H • S • H • S • H ≈⟨ general-powers 100 auto ⟩
    S ^ 2 • (S • H) ^ 3 ≈⟨ cong refl (axiom order-SH) ⟩
    S ^ 2 • ε ≈⟨ general-powers 100 auto ⟩
    S ^ 2 ∎

  lemma-SSH^6 : (S • S • H) ^ 6 ≈ ε
  lemma-SSH^6 = begin
    (S • S • H) ^ 6 ≈⟨ by-assoc auto ⟩
    S • (S • H • S) • (S • H • S) • (S • H • S) • (S • H • S) • (S • H • S) • S • H ≈⟨ cong refl (cong lemma-SHS (cong lemma-SHS (cong lemma-SHS (cong lemma-SHS (cong lemma-SHS refl))))) ⟩
    S • (H ^ 3 • S ^ 2 • H ^ 3) • (H ^ 3 • S ^ 2 • H ^ 3) • (H ^ 3 • S ^ 2 • H ^ 3) • (H ^ 3 • S ^ 2 • H ^ 3) • (H ^ 3 • S ^ 2 • H ^ 3) • S • H ≈⟨ general-powers 1000 auto ⟩
    S • H • (H • H • S • S • H • H • S) • (S • H • H • S • S • H • H) • S • S • H • H • S • S • H ^ 3 • S • H ≈⟨ cong refl (cong refl (cong lemma-comm-HHSSHHS (cong (sym lemma-comm-HHSSHHS) refl))) ⟩
    S • H • (S • H • H • S • S • H • H) • (H • H • S • S • H • H • S) • S • S • H • H • S • S • H ^ 3 • S • H ≈⟨ general-powers 1000 auto ⟩
    (S • H) ^ 3 ≈⟨ axiom order-SH ⟩
    ε ∎

  lemma-SSH^3 : (S • S • H) ^ 3 ≈ (H ^ 3 • S) ^ 3
  lemma-SSH^3 = begin
    (S • S • H) ^ 3 ≈⟨ general-powers 100 auto ⟩
    (S • S • H) ^ 6 • (H ^ 3 • S) ^ 3 ≈⟨ cong lemma-SSH^6 refl ⟩
    ε • (H ^ 3 • S) ^ 3 ≈⟨ left-unit ⟩
    (H ^ 3 • S) ^ 3 ∎


  lemma-XZXXZZ : X • Z • X ^ 2 • Z ^ 2 ≈ ε
  lemma-XZXXZZ = begin
    X • Z • X ^ 2 • Z ^ 2 ≈⟨ cong refl (cong refl (cong lemma-def-XX lemma-def-ZZ)) ⟩
    (H • S • HH • SS • H) • (HH • S • HH • SS) • ((H • S • S • H) • (H • S • H)) • (HH • S • S • HH) • S ≈⟨ by-assoc auto ⟩
    (H • S • HH • SS • H • HH • S • HH • SS • H • S • S • H • H • S • H) • (H • H • S • S • H • H • S) ≈⟨ cong refl lemma-comm-HHSSHHS ⟩
    (H • S • HH • SS • H • HH • S • HH • SS • H • S • S • H • H • S • H) • (S • H • H • S • S • H • H) ≈⟨ by-assoc auto ⟩
    (H • S • HH • SS • H • HH • S • HH • SS • H • S • S • H) • (H • S • H • S • H) • H • S • S • H • H ≈⟨ cong refl (cong lemma-HSHSH refl) ⟩
    (H • S • HH • SS • H • HH • S • HH • SS • H • S • S • H) • (S • S) • H • S • S • H • H ≈⟨ general-powers 100 auto ⟩
    (H • S • HH • SS • H • HH • S • HH • SS • H) • (S • S • H) ^ 3 • H ≈⟨ cong refl (cong lemma-SSH^3 refl) ⟩
    (H • S • HH • SS • H • HH • S • HH • SS • H) • (H ^ 3 • S) ^ 3 • H ≈⟨ general-powers 100 auto ⟩
    (H • S • HH • SS • H • HH • S • H • S) • (H ^ 3 • S) • H ≈⟨ by-assoc auto ⟩
    (H • S • HH • SS • H • HH) • (S • H • S • H) • H ^ 2 • S • H ≈⟨ cong refl (cong lemma-SHSH refl) ⟩
    (H • S • HH • SS • H • HH) • (H ^ 3 • S ^ 2) • H ^ 2 • S • H ≈⟨ general-powers 1000 auto ⟩
    H • (S • H • H • S • S • H • H) • S ^ 2 • H ^ 2 • S • H ≈⟨ cong refl (sym (cong lemma-comm-HHSSHHS refl)) ⟩
    H • (H • H • S • S • H • H • S) • S ^ 2 • H ^ 2 • S • H ≈⟨  general-powers 1000 auto ⟩
    ε ∎

  lemma-conj-X-S : X • S ≈ (S • Z • Z) • X
  lemma-conj-X-S = begin
    X • S ≈⟨ by-assoc auto ⟩
    H • (S • H • H • S • S • H • S) ≈⟨ general-powers 100 auto ⟩
    H • (S • H • H • S • S • H • H) • (H ^ 3 • S) ≈⟨ cong refl (sym (cong lemma-comm-HHSSHHS refl)) ⟩
    H • (H • H • S • S • H • H • S) • (H ^ 3 • S) ≈⟨ general-powers 100 auto ⟩
    (H ^ 3 • S ^ 2) • H ^ 2 • S • (H ^ 3 • S) ≈⟨ (sym (cong lemma-SHSH refl)) ⟩
    (S • H • S • H) • H ^ 2 • S • (H ^ 3 • S) ≈⟨ general-powers 100 auto ⟩
    (S • H • H) • (H ^ 3 • S) ^ 3 ≈⟨ cong refl (sym lemma-SSH^3) ⟩
    (S • H • H) • (S • S • H) ^ 3 ≈⟨ by-assoc auto ⟩
    S • H • H • S • S • H • S • S • H • S • S • H ≈⟨ by-assoc auto ⟩
    ε • S • H • H • S • S • H • S ^ 2 • H • SS • H ≈⟨ (sym (cong (axiom order-H) refl)) ⟩
    H ^ 4 • S • H • H • S • S • H • S ^ 2 • H • SS • H ≈⟨ by-assoc auto ⟩
    (H • H) • (H • H • S • H • H • S) • S • H • S ^ 2 • H • SS • H ≈⟨ cong refl (_≈_.cong (_≈_.axiom comm-HHSHHS) _≈_.refl) ⟩
    (H • H) • (S • H • H • S • H • H) • S • H • S ^ 2 • H • SS • H ≈⟨ by-assoc auto ⟩
    (H • H • S) • (H • H • S • H • H • S) • H • S ^ 2 • H • SS • H ≈⟨ cong refl (_≈_.cong (_≈_.axiom comm-HHSHHS) _≈_.refl) ⟩
    (H • H • S) • (S • H • H • S • H • H) • H • S ^ 2 • H • SS • H ≈⟨ by-assoc auto ⟩
    (H • H • SS • HH • S) • (H ^ 3 • S ^ 2) • H • SS • H ≈⟨ general-powers 100 auto ⟩
    (H • H • SS • HH • S) • (H ^ 3 • S ^ 2) • H • SS • H ≈⟨ cong refl (sym (cong lemma-SH^2 refl)) ⟩
    (H • H • SS • HH • S) • ((S • H) ^ 2) • H • SS • H ≈⟨ by-assoc auto ⟩
    (H • H • S) • ε • S • HH • SS • H • S • HH • SS • H ≈⟨ cong refl (_≈_.sym (_≈_.cong (_≈_.axiom order-H) _≈_.refl)) ⟩
    (H • H • S) • H ^ 4 • S • HH • SS • H • S • HH • SS • H ≈⟨ by-assoc auto ⟩
    (H • H • S • H • H) • ε • HH • S • HH • SS • H • S • HH • SS • H ≈⟨ cong refl (_≈_.sym (_≈_.cong (_≈_.axiom order-S) _≈_.refl)) ⟩
    (H • H • S • H • H) • S ^ 3 • HH • S • HH • SS • H • S • HH • SS • H ≈⟨ by-assoc auto ⟩
    (H • H • S • H • H • S) • SS • HH • S • HH • SS • H • S • HH • SS • H ≈⟨ (_≈_.cong (_≈_.axiom comm-HHSHHS) _≈_.refl) ⟩
    (S • H • H • S • H • H) • SS • HH • S • HH • SS • H • S • HH • SS • H ≈⟨ by-assoc auto ⟩
    S • HH • S • HH • SS • HH • S • HH • SS • H • S • HH • SS • H ≈⟨ by-assoc auto ⟩
    (S • Z • Z) • X ∎

  lemma-conj-X-Z : X • Z ≈ (Z) • X
  lemma-conj-X-Z = begin
    X • Z ≈⟨ by-assoc auto ⟩
    X • Z • ε ≈⟨ cong refl (sym (cong refl lemma-order-X)) ⟩
    X • Z • X ^ 2 • X ≈⟨ by-assoc auto ⟩
    (X • Z • X ^ 2) • ε • X ≈⟨ cong refl (cong (sym lemma-order-Z) refl) ⟩
    (X • Z • X ^ 2) • (Z ^ 2 • Z) • X ≈⟨ by-assoc auto ⟩
    ((X • Z • X ^ 2 • Z ^ 2) • Z) • X ≈⟨  cong (trans (cong lemma-XZXXZZ refl) left-unit) refl ⟩
    Z • X ∎

  lemma-X^3 : X ^ 3 ≈ ε
  lemma-X^3 = begin
    X ^ 3 ≈⟨ sym assoc ⟩
    X ^ 2 • X ≈⟨ lemma-order-X ⟩
    ε ∎

  lemma-HX : H • X ≈ Z • H
  lemma-HX = begin
    H • X ≈⟨ by-assoc auto ⟩
    Z • H ∎

  lemma-HSSH : (H • S • S) • H ≈ (S • Z • X • X) • H • S
  lemma-HSSH = begin
    (H • S • S) • H ≈⟨ general-powers 100 auto ⟩
    (H) • (S ^ 2) • H ≈⟨ cong refl (sym (cong lemma-HSHSH refl)) ⟩
    (H) • (H • S • H • S • H) • H ≈⟨ general-powers 100 auto ⟩
    (S • H • H) • (H • H • S • S • H • H • S) • H • S • H • H ≈⟨ cong refl (cong lemma-comm-HHSSHHS refl ) ⟩
    (S • H • H) • (S • H • H • S • S • H • H) • H • S • H • H ≈⟨ general-powers 100 auto ⟩
    (S) • (H • X) • H • H • S • H • H ≈⟨ cong refl (cong lemma-HX refl) ⟩
    (S) • (Z • H) • H • H • S • H • H ≈⟨ general-powers 100 auto ⟩
    (S • Z • H • S • S) • (S • H • H • S • H • H) ≈⟨ cong refl (sym (axiom comm-HHSHHS)) ⟩
    (S • Z • H • S • S) • (H • H • S • H • H • S) ≈⟨ general-powers 100 auto ⟩
    (S • Z) • ((H • S • S • H) • (H • S • H)) • H • S ≈⟨ cong refl (cong (sym lemma-def-XX) refl) ⟩
    (S • Z) • (X • X) • H • S ≈⟨ by-assoc auto ⟩
    (S • Z • X • X) • H • S ∎


  lemma-ZZS^3 : (Z ^ 2 • S) ^ 2 • Z ^ 2 • S ≈ ε
  lemma-ZZS^3 = begin
    (Z ^ 2 • S) ^ 2 • Z ^ 2 • S ≈⟨ by-assoc auto ⟩
    Z • (Z • S) • Z ^ 2 • S • Z ^ 2 • S ≈⟨ cong refl (cong lemma-comm-Z-S refl) ⟩
    Z • (S • Z) • Z ^ 2 • S • Z ^ 2 • S ≈⟨ by-assoc auto ⟩
    (Z • S) • (Z ^ 2 • Z) • S • Z ^ 2 • S ≈⟨ cong refl (cong lemma-order-Z refl) ⟩
    (Z • S) • ε • S • Z ^ 2 • S ≈⟨ by-assoc auto ⟩
    (Z • S • S • Z) • (Z • S) ≈⟨ cong refl lemma-comm-Z-S ⟩
    (Z • S • S • Z) • (S • Z) ≈⟨ by-assoc auto ⟩
    (Z • S • S) • (Z • S) • Z ≈⟨ cong refl (cong lemma-comm-Z-S refl) ⟩
    (Z • S • S) • (S • Z) • Z ≈⟨ by-assoc auto ⟩
    Z • S ^ 3 • Z • Z ≈⟨ cong refl (cong (axiom order-S) refl) ⟩
    Z • ε • Z • Z ≈⟨ by-assoc auto ⟩
    Z ^ 2 • Z ≈⟨ lemma-order-Z ⟩
    ε ∎



{-
module Iso where

  private
    variable
      n : ℕ

  module Sym  = NSym.Symplectic
  module Sim  = Clifford-Relations
  open Sym renaming (Gen to Gen₁ ; _QRel,_===_ to _QRel,_===₁_) using ()
  Gen₂ = Gen₁
  open Sim renaming (_QRel,_===_ to _QRel,_===₂_) using ()
  open Symplectic-GroupLike renaming (grouplike to grouplike₁) using ()
  open Clifford-GroupLike renaming (grouplike to grouplike₂) using ()


  f-well-defined : let open PB (n QRel,_===₂_) renaming (_≈_ to _≈₂_) in
    ∀ {w v} -> n QRel, w ===₁ v -> id w ≈₂ id v
  f-well-defined {n} order-S = PB.axiom Sim.order-S
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
  f-well-defined {₁₊ n} (semi-M𝑠 x) = lemma-semi-M𝑠 x
    where
    open Lemmas1 n
  f-well-defined {₂₊ n} (semi-M↑CZ x) = lemma-semi-M↑CZ x
    where
    open Lemmas2 n
  f-well-defined {₂₊ n} (semi-M↓CZ x) = lemma-semi-M↓CZ x
    where
    open Lemmas2 n
  f-well-defined {n} order-CZ = PB.axiom Sim.order-CZ
  f-well-defined {n} comm-CZ-S↓ = PB.axiom Sim.comm-CZ-S↓
  f-well-defined {n} comm-CZ-S↑ = PB.axiom Sim.comm-CZ-S↑
  f-well-defined {n} selinger-c10 = PB.axiom Sim.selinger-c10
  f-well-defined {n} selinger-c11 = PB.axiom Sim.selinger-c11
  f-well-defined {n} selinger-c12 = PB.axiom Sim.selinger-c12
  f-well-defined {n} selinger-c13 = PB.axiom Sim.selinger-c13
  f-well-defined {n} selinger-c14 = PB.axiom Sim.selinger-c14
  f-well-defined {n} selinger-c15 = PB.axiom Sim.selinger-c15
  f-well-defined {n} comm-H = PB.axiom Sim.comm-H
  f-well-defined {n} comm-S = PB.axiom Sim.comm-S
  f-well-defined {n} comm-CZ = PB.axiom Sim.comm-CZ
  f-well-defined {n} (cong↑ eq) = lemma-cong↑ _ _ (f-well-defined eq)
    where
    open Lemmas-Clifford
  
  g-well-defined : let open PB (n QRel,_===₁_) renaming (_≈_ to _≈₁_) in
    ∀ {u t} -> n QRel, u ===₂ t -> id u ≈₁ id t
  g-well-defined Sim.order-S = PB.axiom _QRel,_===₁_.order-S
  g-well-defined {₁₊ n} Sim.order-H = lemma-HH-M-1
    where
    open Lemmas0 n
  g-well-defined {₁₊ n} (Sim.M-power k) = begin
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
    open Sim

    
  g-well-defined {₁₊ n} Sim.semi-M𝑠 = PB.axiom (_QRel,_===₁_.semi-M𝑠 ((g , g≠0)))
  g-well-defined Sim.semi-M↑CZ = PB.axiom (_QRel,_===₁_.semi-M↑CZ ((g , g≠0)))
  g-well-defined Sim.semi-M↓CZ = PB.axiom (_QRel,_===₁_.semi-M↓CZ ((g , g≠0)))
  g-well-defined Sim.order-CZ = PB.axiom _QRel,_===₁_.order-CZ
  g-well-defined Sim.comm-CZ-S↓ = PB.axiom _QRel,_===₁_.comm-CZ-S↓
  g-well-defined Sim.comm-CZ-S↑ = PB.axiom _QRel,_===₁_.comm-CZ-S↑
  g-well-defined Sim.selinger-c10 = PB.axiom _QRel,_===₁_.selinger-c10
  g-well-defined Sim.selinger-c11 = PB.axiom _QRel,_===₁_.selinger-c11
  g-well-defined Sim.selinger-c12 = PB.axiom _QRel,_===₁_.selinger-c12
  g-well-defined Sim.selinger-c13 = PB.axiom _QRel,_===₁_.selinger-c13
  g-well-defined Sim.selinger-c14 = PB.axiom _QRel,_===₁_.selinger-c14
  g-well-defined Sim.selinger-c15 = PB.axiom _QRel,_===₁_.selinger-c15
  g-well-defined Sim.comm-H = PB.axiom _QRel,_===₁_.comm-H
  g-well-defined Sim.comm-S = PB.axiom _QRel,_===₁_.comm-S
  g-well-defined Sim.comm-CZ = PB.axiom _QRel,_===₁_.comm-CZ
  g-well-defined (Sim.cong↑ eq) = lemma-cong↑ _ _ (g-well-defined eq)
    where
    open Lemmas-Sym


  open import Algebra.Bundles using (Group)
  open import Algebra.Morphism.Structures using (module GroupMorphisms)

  open GroupMorphisms


  Theorem-Sym-iso-Sim : ∀ {n} ->
    let
    module G1 = Group-Lemmas (Gen₁ n) (n QRel,_===₁_) grouplike₁
    module G2 = Group-Lemmas (Gen₂ n) (n QRel,_===₂_) grouplike₂
    in
    IsGroupIsomorphism (Group.rawGroup G1.•-ε-group) (Group.rawGroup G2.•-ε-group) id
  Theorem-Sym-iso-Sim {n}  = StarGroupIsomorphism.isGroupIsomorphism f-well-defined g-well-defined
    where
    open import Presentation.MorphismId (n QRel,_===₁_) (n QRel,_===₂_)
    open GroupMorphs (grouplike₁ {n}) (grouplike₂ {n})



  Theorem-Sym-iso-Sim' : ∀ {n} ->
    let
    module G1 = Group-Lemmas (Gen₁ n) (n QRel,_===₁_) grouplike₁
    module G2 = Group-Lemmas (Gen₂ n) (n QRel,_===₂_) grouplike₂
    in
    IsGroupIsomorphism (Group.rawGroup G2.•-ε-group) (Group.rawGroup G1.•-ε-group)  id
  Theorem-Sym-iso-Sim' {n} = StarGroupIsomorphism.isGroupIsomorphism g-well-defined f-well-defined
    where
    open import Presentation.MorphismId  (n QRel,_===₂_) (n QRel,_===₁_)
    open GroupMorphs (grouplike₂ {n}) (grouplike₁ {n}) 

-}
-}

-}
-}


