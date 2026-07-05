-- {-# OPTIONS --allow-unsolved-metas #-}
{-# OPTIONS --safe #-}
-- {-# OPTIONS --prop #-}
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
open import Notations
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

module N.Clifford.Clifford-Mod-Scalar.Part1
  (p-3 : ℕ)
  (let p-2 = ₁₊ p-3)
  (p-prime : Prime (suc (₁₊ p-2)))
  (let open PrimeModulus' p-2 p-prime)
  (g*@(g , g≠0) : ℤ* ₚ)
  (g-gen : ∀ ((x , _) : ℤ* ₚ) -> ∃ \ (k : ℤ ₚ-₁) -> x ≡ g ^′ toℕ k )
  where


pattern auto = Eq.refl
pattern ₀ = zero
pattern ₁ = ₁₊ ₀
pattern ₂ = ₁₊ ₁
pattern ₃ = ₁₊ ₂
pattern ₄ = ₁₊ ₃


open Primitive-Root-Modp' g* g-gen

module Symplectic-Simplified where

open import N.Symplectic p-2 p-prime as NSym
open Symplectic hiding (_QRel,_===_ ; M ; M₁) public

1/2 = ((₂ , λ ()) ⁻¹) .proj₁

-1/2 = - ((₂ , λ ()) ⁻¹) .proj₁


module Clifford-Relations where

  Z : ∀ {n} -> Word (Gen (₁₊ n))
  Z = H • H • S • H • H • S⁻¹
  
  X : ∀ {n} -> Word (Gen (₁₊ n))
  X = H • S • H • H • S⁻¹ • H

  Z⁻¹ : ∀ {n} -> Word (Gen (₁₊ n))
  Z⁻¹ = Z ^ p-1

  X⁻¹ : ∀ {n} -> Word (Gen (₁₊ n))
  X⁻¹ = X ^ p-1


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
    comm-X-Z :          ∀ {n} → (₁₊ n) QRel,  X • Z === Z • X

    semi-M↑CZ :         ∀ {n} → (₂₊ n) QRel,  Mg ↑ • CZ === CZ^ g • Mg ↑
    semi-M↓CZ :         ∀ {n} → (₂₊ n) QRel,  Mg ↓ • CZ === CZ^ g • Mg ↓

    rel-X↑-CZ :         ∀ {n} → (₂₊ n) QRel,  CZ • X ↑ === X ↑ • Z ↓ • CZ
    rel-X↓-CZ :         ∀ {n} → (₂₊ n) QRel,  CZ • X ↓ === X ↓ • Z ↑ • CZ

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


