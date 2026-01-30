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
open import Data.Fin.Properties as FP using (suc-injective ; toℕ-inject₁ ; toℕ-fromℕ)
import Data.Nat.Properties as NP
open import Presentation.GroupLike
open import Presentation.Tactics hiding ([_])
open import Data.Nat.Primality



module N.Symplectic-Derived (p-2 : ℕ) (p-prime : Prime (2+ p-2))  where

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

module Symplectic-Derived-Gen where

  
  data Gen : ℕ → Set where
    H-gen : ∀ {n} → ℤ ₄ -> Gen (₁₊ n)
    S-gen : ∀ {n} → ℤ ₚ -> Gen (₁₊ n)
    CZ-gen : ∀ {n} → ℤ ₚ -> Gen (₂₊ n)
    -- lift a generator from Gen n to Gen (₁₊ n). E.g., in a two
    -- qupit circut H-gen = H 0, and H-gen ↥ = H 1.
    _↥ : ∀ {n} → Gen n → Gen (suc n)

  [_⇑] : ∀ {n} → Word (Gen n) → Word (Gen (suc n))
  [_⇑] {n} = ([_]ʷ ∘ _↥) WB.*

  [_⇑]' : ∀ {n} → Word (Gen n) → Word (Gen (suc n))
  [_⇑]' {n} = wmap _↥

  _↑ : ∀ {n} → Word (Gen n) → Word (Gen (suc n))
  _↑ = wmap _↥

  _↓-gen : ∀ {n} → Gen n → Gen (suc n)
  _↓-gen {zero} ()
  _↓-gen {₁₊ n} (H-gen k) = (H-gen k)
  _↓-gen {₁₊ n} (S-gen k) = S-gen k
  _↓-gen {₁₊ .(₁₊ _)} (CZ-gen k) = CZ-gen k
  _↓-gen {₁₊ n} (g ↥) = (g ↓-gen) ↥

  -- _↓ : ∀ {n} → Word (Gen n) → Word (Gen (suc n))
  -- _↓ {n} = wmap _↓-gen

  _↓ : ∀ {n} → Word (Gen n) → Word (Gen ( n))
  _↓ {n} x = x


  lemma-[⇑]=[⇑]' : ∀ {n} (w : Word (Gen n)) → [ w ⇑] ≡ [ w ⇑]'
  lemma-[⇑]=[⇑]' {n} [ x ]ʷ = Eq.refl
  lemma-[⇑]=[⇑]' {n} ε = Eq.refl
  lemma-[⇑]=[⇑]' {n} (w • w₁) = Eq.cong₂ _•_ (lemma-[⇑]=[⇑]' w) (lemma-[⇑]=[⇑]' w₁)

  S : ∀ {n} → Word (Gen (₁₊ n))
  S = [ S-gen ₁ ]ʷ

  S⁻¹ : ∀ {n} → Word (Gen (₁₊ n))
  S⁻¹ = S ^ p-1
  
  H : ∀ {n} → Word (Gen (₁₊ n))
  H = [ H-gen ₁ ]ʷ

  H⁻¹ : ∀ {n} → Word (Gen (₁₊ n))
  H⁻¹ = H ^ 3

  HH : ∀ {n} → Word (Gen (₁₊ n))
  HH = H ^ 2

  SH : ∀ {n} → Word (Gen (₁₊ n))
  SH = S • H

  CZ : ∀ {n} → Word (Gen (₂₊ n))
  CZ = [ CZ-gen ₁ ]ʷ

  CZ⁻¹ : ∀ {n} → Word (Gen (₂₊ n))
  CZ⁻¹ = CZ ^ p-1
  
  CX : ∀ {n} → Word (Gen (₂₊ n))
  CX = H ↓ ^ 3 • CZ • H ↓ 

  XC : ∀ {n} → Word (Gen (₂₊ n))
  XC = H ↑ ^ 3 • CZ • H ↑ 

  CX' : ∀ {n} → Word (Gen (₂₊ n))
  CX' = H ↓ • CZ • H ↓ ^ 3

  XC' : ∀ {n} → Word (Gen (₂₊ n))
  XC' = H ↑ • CZ • H ↑ ^ 3

  Ex : ∀ {n} → Word (Gen (₂₊ n))
  Ex = CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑

  ₕ|ₕ : ∀ {n} → Word (Gen (₂₊ n))
  ₕ|ₕ = H ↓ • CZ • H ↓

  ʰ|ʰ : ∀ {n} → Word (Gen (₂₊ n))
  ʰ|ʰ = H ↑ • CZ • H ↑

  ⊥⊤ : ∀ {n} → Word (Gen (₂₊ n))
  ⊥⊤ = ₕ|ₕ • ʰ|ʰ

  ⊤⊥ : ∀ {n} → Word (Gen (₂₊ n))
  ⊤⊥ = ʰ|ʰ • ₕ|ₕ

  H^ : ∀ {n} → ℤ ₄ -> Word (Gen (₁₊ n))
  H^ k = [ H-gen k ]ʷ

  S^ : ∀ {n} → ℤ ₚ -> Word (Gen (₁₊ n))
  S^ k = [ S-gen k ]ʷ

  CZ^ : ∀ {n} → ℤ ₚ -> Word (Gen (₂₊ n))
  CZ^ k = [ CZ-gen k ]ʷ

  M : ∀ {n} -> ℤ* ₚ -> Word (Gen (₁₊ n))
  M x' = S^ x • H • S^ x⁻¹ • H • S^ x • H
    where
    x = x' .proj₁
    x⁻¹ = ((x' ⁻¹) .proj₁ )

  M₁ : ∀ {n} -> Word (Gen (₁₊ n))
  M₁ = M (₁ , λ ())

  infixr 9 _^2
  _^2 : ℤ* ₚ -> ℤ ₚ
  _^2 x' = let x = x' .proj₁ in x * x 

  infixr 9 _^1
  _^1 : ℤ* ₚ -> ℤ ₚ
  _^1 x' = let x = x' .proj₁ in x

  infix 4 _QRel,_===_
  data _QRel,_===_ : (n : ℕ) → WRel (Gen n) where
  
    order-S :      ∀ {n} → (₁₊ n) QRel,  S ^ p === ε
    order-H :      ∀ {n} → (₁₊ n) QRel,  H ^ 4 === ε
    order-SH :     ∀ {n} → (₁₊ n) QRel,  (S • H) ^ 3 === ε
    comm-HHS :     ∀ {n} → (₁₊ n) QRel,  H • H • S === S • H • H

    M-mul :    ∀ {n} x y → (₁₊ n) QRel,  M x • M y === M (x *' y)
    semi-MS :    ∀ {n} x → (₁₊ n) QRel,  M x • S === S^ (x ^2) • M x
    semi-M↑CZ :  ∀ {n} x → (₂₊ n) QRel,  M x ↑ • CZ === CZ^ (x ^1) • M x ↑
    semi-M↓CZ :  ∀ {n} x → (₂₊ n) QRel,  M x ↓ • CZ === CZ^ (x ^1) • M x ↓

    order-CZ :     ∀ {n} → (₂₊ n) QRel,  CZ ^ p === ε

    comm-CZ-S↓ :   ∀ {n} → (₂₊ n) QRel,  CZ • S ↓ === S ↓ • CZ
    comm-CZ-S↑ :   ∀ {n} → (₂₊ n) QRel,  CZ • S ↑ === S ↑ • CZ

    selinger-c10 : ∀ {n} → (₂₊ n) QRel,  CZ • H ↑ • CZ === S⁻¹ ↑ • H ↑ • S⁻¹ ↑ • CZ • H ↑ • S⁻¹ ↑ • S⁻¹ ↓
    selinger-c11 : ∀ {n} → (₂₊ n) QRel,  CZ • H ↓ • CZ === S⁻¹ ↓ • H ↓ • S⁻¹ ↓ • CZ • H ↓ • S⁻¹ ↓ • S⁻¹ ↑

    selinger-c12 : ∀ {n} → (₃₊ n) QRel,  CZ ↑ • CZ === CZ • CZ ↑
    selinger-c13 : ∀ {n} → (₃₊ n) QRel,  ⊤⊥ ↑ • CZ ↓ • ⊥⊤ ↑ === ⊥⊤ ↓ • CZ ↑ • ⊤⊥ ↓
    
    selinger-c14 : ∀ {n} → (₃₊ n) QRel,  (⊤⊥ ↑ • CZ ↓) ^ 3 === ε
    selinger-c15 : ∀ {n} → (₃₊ n) QRel,  (⊥⊤ ↓ • CZ ↑) ^ 3 === ε

    comm-H :    ∀ {n}{g} → (₂₊ n) QRel,  [ g ↥ ]ʷ • H === H • [ g ↥ ]ʷ
    comm-S :    ∀ {n}{g} → (₂₊ n) QRel,  [ g ↥ ]ʷ • S === S • [ g ↥ ]ʷ
    comm-CZ :   ∀ {n}{g} → (₃₊ n) QRel,  [ g ↥ ↥ ]ʷ • CZ === CZ • [ g ↥ ↥ ]ʷ

    derived-S :  ∀ {n} k → (₁₊ n) QRel,  S^ k === S ^ toℕ k
    derived-H :  ∀ {n} k → (₁₊ n) QRel,  H^ k === H ^ toℕ k
    derived-CZ : ∀ {n} k → (₂₊ n) QRel,  CZ^ k === CZ ^ toℕ k

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

  lemma-cong↓-S^ : ∀ {n} k -> let open PB ((₂₊ n) QRel,_===_) renaming (_≈_ to _≈↓_) using () in
    (S ^ k) ↓ ≈↓ S ^ k
  lemma-cong↓-S^ {n} ₀ = PB.refl
  lemma-cong↓-S^ {n} ₁ = PB.refl
  lemma-cong↓-S^ {n} (₂₊ k) = PB.cong PB.refl (lemma-cong↓-S^ {n} (₁₊ k))


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

{-
  lemma-cong↓ : ∀ {n} w v →
    let open PB (n QRel,_===_) using (_≈_) in
    let open PB ((suc n) QRel,_===_) renaming (_≈_ to _≈↓_) using () in
    w ≈ v → w ↓ ≈↓ v ↓
  lemma-cong↓ {n} w v PB.refl = PB.refl
  lemma-cong↓ {n} w v (PB.sym eq) = PB.sym (lemma-cong↓ v w eq)
  lemma-cong↓ {n} w v (PB.trans eq eq₁) = PB.trans (lemma-cong↓ _ _ eq) (lemma-cong↓ _ _ eq₁)
  lemma-cong↓ {n} w v (PB.cong eq eq₁) = PB.cong (lemma-cong↓ _ _ eq) (lemma-cong↓ _ _ eq₁)
  lemma-cong↓ {n} w v PB.assoc = PB.assoc
  lemma-cong↓ {n} w v PB.left-unit = PB.left-unit
  lemma-cong↓ {n} w v PB.right-unit = PB.right-unit
  lemma-cong↓ {n} w v (PB.axiom order-S) = begin
    ((S • S ^ ₁₊ p-2) ↓) ≈⟨ cong refl (lemma-cong↓-S^ (₁₊ p-2)) ⟩
    ((S • S ^ ₁₊ p-2)) ≈⟨ axiom order-S ⟩
    (ε ↓) ∎
    where
    open PB ((suc n) QRel,_===_) renaming (_≈_ to _≈↓_)
    open PP ((suc n) QRel,_===_)
    open SR word-setoid
  lemma-cong↓ {n} w v (PB.axiom order-H) = PB.axiom order-H
  lemma-cong↓ {n} w v (PB.axiom order-SH) = PB.axiom order-SH
  lemma-cong↓ {n} w v (PB.axiom comm-HHS) = PB.axiom comm-HHS
  lemma-cong↓ {n} w v (PB.axiom (M-mul x y)) = PB.axiom (M-mul x y)
  lemma-cong↓ {n} w v (PB.axiom (semi-MS x)) = PB.axiom (semi-MS x)
  lemma-cong↓ {n} w v (PB.axiom (semi-M↑CZ x)) = PB.axiom (semi-M↑CZ x)
  lemma-cong↓ {n} w v (PB.axiom (semi-M↓CZ x)) = PB.axiom (semi-M↓CZ x)
  lemma-cong↓ {n} w v (PB.axiom order-CZ) = begin
    ((CZ • CZ ^ ₁₊ p-2) ↓) ≈⟨ cong refl (lemma-cong↓-CZ^ (₁₊ p-2)) ⟩
    ((CZ • CZ ^ ₁₊ p-2)) ≈⟨ axiom order-CZ ⟩
    (ε ↓) ∎
    where
    open PB ((suc n) QRel,_===_) renaming (_≈_ to _≈↓_)
    open PP ((suc n) QRel,_===_)
    open SR word-setoid
  lemma-cong↓ {n} w v (PB.axiom comm-CZ-S↓) = PB.axiom comm-CZ-S↓
  lemma-cong↓ {n} w v (PB.axiom comm-CZ-S↑) = PB.axiom comm-CZ-S↑
  lemma-cong↓ {n} w v (PB.axiom selinger-c10) = begin
    ((CZ • (H ↑) • CZ) ↓) ≈⟨ refl ⟩
    ((CZ • (H ↑) • CZ) ) ≈⟨ axiom selinger-c10 ⟩
    ((S⁻¹ ↑) • (H ↑) • (S⁻¹ ↑) • CZ • (H ↑) • (S⁻¹ ↑) • (S⁻¹ ↓)) ≈⟨ sym (cong (lemma-cong↓-S^↑ (₁₊ p-2)) (cright cong (lemma-cong↓-S^↑ (₁₊ p-2)) (cright (cright cong (lemma-cong↓-S^↑ (₁₊ p-2)) (lemma-cong↓-S^↓ (₁₊ p-2)))))) ⟩
    ((S⁻¹ ↑ ↓) • (H ↑) • (S⁻¹ ↑ ↓) • CZ • (H ↑) • (S⁻¹ ↑ ↓) • (S⁻¹ ↓ ↓)) ≈⟨ refl ⟩
    ((S⁻¹ ↑ ↓) • (H ↑ ↓) • (S⁻¹ ↑ ↓) • CZ ↓ • (H ↑ ↓) • (S⁻¹ ↑ ↓) • (S⁻¹ ↓ ↓)) ≈⟨ refl ⟩
    (((S⁻¹ ↑) • (H ↑) • (S⁻¹ ↑) • CZ • (H ↑) • (S⁻¹ ↑) • (S⁻¹ ↓)) ↓) ∎
    where
    open PB ((suc n) QRel,_===_) renaming (_≈_ to _≈↓_)
    open PP ((suc n) QRel,_===_)
    open SR word-setoid
  lemma-cong↓ {n} w v (PB.axiom selinger-c11) = begin
    ((CZ • (H ↓) • CZ) ↓) ≈⟨ refl ⟩
    ((CZ • (H ↓) • CZ) ) ≈⟨ axiom selinger-c11 ⟩
    ((S⁻¹ ↓) • (H ↓) • (S⁻¹ ↓) • CZ • (H ↓) • (S⁻¹ ↓) • (S⁻¹ ↑)) ≈⟨ sym (cong (lemma-cong↓-S^↓ (₁₊ p-2)) (cright cong (lemma-cong↓-S^↓ (₁₊ p-2)) (cright (cright cong (lemma-cong↓-S^↓ (₁₊ p-2)) (lemma-cong↓-S^↑ (₁₊ p-2)))))) ⟩
    ((S⁻¹ ↓ ↓) • (H ↓) • (S⁻¹ ↓ ↓) • CZ • (H ↓) • (S⁻¹ ↓ ↓) • (S⁻¹ ↑ ↓)) ≈⟨ refl ⟩
    (((S⁻¹ ↓) • (H ↓) • (S⁻¹ ↓) • CZ • (H ↓) • (S⁻¹ ↓) • (S⁻¹ ↑)) ↓) ∎
    where
    open PB ((suc n) QRel,_===_) renaming (_≈_ to _≈↓_)
    open PP ((suc n) QRel,_===_)
    open SR word-setoid
  lemma-cong↓ {n} w v (PB.axiom selinger-c12) = PB.axiom selinger-c12
  lemma-cong↓ {n} w v (PB.axiom selinger-c13) = PB.axiom selinger-c13
  lemma-cong↓ {n} w v (PB.axiom selinger-c14) = PB.axiom selinger-c14
  lemma-cong↓ {n} w v (PB.axiom selinger-c15) = PB.axiom selinger-c15
  lemma-cong↓ {n} w v (PB.axiom comm-H) = PB.axiom comm-H
  lemma-cong↓ {n} w v (PB.axiom comm-S) = PB.axiom comm-S
  lemma-cong↓ {n} w v (PB.axiom comm-CZ) = PB.axiom comm-CZ
  lemma-cong↓ {n} w v (PB.axiom (derived-S k)) = begin
    ([ S-gen k ]ʷ ↓) ≈⟨ refl ⟩
    ([ S-gen k ]ʷ) ≈⟨ axiom (derived-S k) ⟩
    ((S ^ toℕ k)) ≈⟨ sym (lemma-cong↓-S^ (toℕ k)) ⟩
    ((S ^ toℕ k) ↓) ∎
    where
    open PB ((suc n) QRel,_===_) renaming (_≈_ to _≈↓_)
    open PP ((suc n) QRel,_===_)
    open SR word-setoid
  lemma-cong↓ {n} w v (PB.axiom (derived-H k)) = begin
    ([ H-gen k ]ʷ ↓) ≈⟨ refl ⟩
    ([ H-gen k ]ʷ) ≈⟨ axiom (derived-H k) ⟩
    ((H ^ toℕ k)) ≈⟨ sym (lemma-cong↓-H^ (toℕ k)) ⟩
    ((H ^ toℕ k) ↓) ∎
    where
    open PB ((suc n) QRel,_===_) renaming (_≈_ to _≈↓_)
    open PP ((suc n) QRel,_===_)
    open SR word-setoid
  lemma-cong↓ {n} w v (PB.axiom (derived-CZ k)) =  begin
    ([ CZ-gen k ]ʷ ↓) ≈⟨ refl ⟩
    ([ CZ-gen k ]ʷ) ≈⟨ axiom (derived-CZ k) ⟩
    ((CZ ^ toℕ k)) ≈⟨ sym (lemma-cong↓-CZ^ (toℕ k)) ⟩
    ((CZ ^ toℕ k) ↓) ∎
    where
    open PB ((suc n) QRel,_===_) renaming (_≈_ to _≈↓_)
    open PP ((suc n) QRel,_===_)
    open SR word-setoid
  lemma-cong↓ {n} w v (PB.axiom (cong↑ {w = w₁} {v = v₁} x)) = begin
    ((w₁ ↑) ↓) ≡⟨  lemma-↑↓ w₁ ⟩
    ((w₁ ↓) ↑) ≈⟨ lemma-cong↑ _ _ (lemma-cong↓ _ _ (PB.axiom x)) ⟩
    ((v₁ ↓) ↑) ≡⟨ Eq.sym (lemma-↑↓ v₁) ⟩
    ((v₁ ↑) ↓) ∎
    where
    open PB ((suc n) QRel,_===_) renaming (_≈_ to _≈↓_)
    open PP ((suc n) QRel,_===_)
    open SR word-setoid
-}

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

  -- lemma-comm-H↑-M : ∀ {n} m → let open PB ((₂₊ n) QRel,_===_) in
    
  --   H ↑ • M m ≈ M m • H ↑

  -- lemma-comm-H↑-M {n} m = begin    
  --   H ↑ • M m ≈⟨ {!!} ⟩
  --   M m • H ↑ ∎
  --   where
  --   open PB ((₂₊ n) QRel,_===_)
  --   open PP ((₂₊ n) QRel,_===_)
  --   open SR word-setoid


module Symplectic-Derived-GroupLike where
  private
    variable
      n : ℕ

  open Symplectic-Derived-Gen
  
  grouplike : Grouplike (n QRel,_===_)
  grouplike {₁₊ n} (H-gen k) = (H ^ toℕ k) ^ 3 , claim
    where
    open PB ((₁₊ n) QRel,_===_)
    open PP ((₁₊ n) QRel,_===_)
    open SR word-setoid
    claim : (H ^ toℕ k) ^ 3 • H^ k ≈ ε
    claim = begin
      (H ^ toℕ k) ^ 3 • H^ k ≈⟨ (cright axiom (derived-H k)) ⟩
      (H ^ toℕ k) ^ 3 • H ^ toℕ k ≈⟨ sym (lemma-^-+ (H ^ toℕ k) 3 1) ⟩
      (H ^ toℕ k) ^ 4 ≈⟨ lemma-^^' H (toℕ k) 4 ⟩
      (H ^ 4) ^ toℕ k ≈⟨ lemma-^-cong (H ^ 4) ε (toℕ k) (axiom order-H) ⟩
      (ε) ^ toℕ k ≈⟨ lemma-ε^k=ε (toℕ k) ⟩
      ε ∎

  grouplike {₁₊ n} (S-gen k) = (S ^ toℕ k) ^ p-1 ,  claim
    where
    open PB ((₁₊ n) QRel,_===_)
    open PP ((₁₊ n) QRel,_===_)
    open SR word-setoid
    claim : (S ^ toℕ k) ^ p-1 • S^ k ≈ ε
    claim = begin
      (S ^ toℕ k) ^ p-1 • S^ k ≈⟨ (cright axiom (derived-S k)) ⟩
      (S ^ toℕ k) ^ p-1 • S ^ toℕ k ≈⟨ sym (lemma-^-+ (S ^ toℕ k) p-1 1) ⟩
      (S ^ toℕ k) ^ (p-1 Nat.+ 1) ≈⟨ lemma-^^' S (toℕ k) (p-1 Nat.+ 1) ⟩
      (S ^ (p-1 Nat.+ 1)) ^ toℕ k ≈⟨ lemma-^-cong (S ^ (p-1 Nat.+ 1)) (S ^ p) (toℕ k) (refl' (Eq.cong (S ^_) (NP.+-comm p-1 1))) ⟩
      (S ^ p) ^ toℕ k ≈⟨ lemma-^-cong (S ^ p) ε (toℕ k) (axiom order-S) ⟩
      (ε) ^ toℕ k ≈⟨ lemma-ε^k=ε (toℕ k) ⟩
      ε ∎

  grouplike {₂₊ n} (CZ-gen k) = (CZ ^ toℕ k) ^ p-1 ,  claim
    where
    open PB ((₂₊ n) QRel,_===_)
    open PP ((₂₊ n) QRel,_===_)
    open SR word-setoid
    claim : (CZ ^ toℕ k) ^ p-1 • CZ^ k ≈ ε
    claim = begin
      (CZ ^ toℕ k) ^ p-1 • CZ^ k ≈⟨ (cright axiom (derived-CZ k)) ⟩
      (CZ ^ toℕ k) ^ p-1 • CZ ^ toℕ k ≈⟨ sym (lemma-^-+ (CZ ^ toℕ k) p-1 1) ⟩
      (CZ ^ toℕ k) ^ (p-1 Nat.+ 1) ≈⟨ lemma-^^' CZ (toℕ k) (p-1 Nat.+ 1) ⟩
      (CZ ^ (p-1 Nat.+ 1)) ^ toℕ k ≈⟨ lemma-^-cong (CZ ^ (p-1 Nat.+ 1)) (CZ ^ p) (toℕ k) (refl' (Eq.cong (CZ ^_) (NP.+-comm p-1 1))) ⟩
      (CZ ^ p) ^ toℕ k ≈⟨ lemma-^-cong (CZ ^ p) ε (toℕ k) (axiom order-CZ) ⟩
      (ε) ^ toℕ k ≈⟨ lemma-ε^k=ε (toℕ k) ⟩
      ε ∎

  grouplike {₂₊ n} (g ↥) with grouplike g
  ... | ig , prf = (ig ↑) , lemma-cong↑ (ig • [ g ]ʷ) ε prf
    where
    open PB ((₂₊ n) QRel,_===_)
    open PP ((₂₊ n) QRel,_===_)


  import Data.Nat.Literals as NL
  open import Agda.Builtin.FromNat
  open import Data.Unit.Base using (⊤)
  open import Data.Fin.Literals
  import Data.Nat.Literals as NL


  instance
    Numℕ' : Number ℕ
    Numℕ' = NL.number 

  instance
    NumFin' : Number (Fin p)
    NumFin' = number p


{-
  A : Set
  A = Σ[ ab ∈ (Fin 3 × Fin 3) ] (ab ≢ (0 , 0))

  F : Set
  F = Fin 3 × Fin 3

  G : Set
  G = Fin 2 × Fin 3

  B : Set
  B = Fin 3 × Fin 3

  D : Set
  D = Fin 3 × Fin 3

  E : Set
  E = Fin 3
  E' = E

  L' : (j : ℕ) → Set
  L' j = Vec B j × A

  jL = Σ[ j ∈ ℕ ] L' j
  
  L : (n : ℕ) → Set
  L n = Σ[ (j , l) ∈ jL ]  j ≤ n

  M : ℕ → Set
  M n = E × Vec D n

  LM : (n : ℕ) → Set
  LM n = L n × M n

  jLM = Σ[ j ∈ ℕ ] (LM j)

  [_]ᵃ : ∀ {n} → A → Word (Gen (₁₊ n))
  [_]ᵃ {n} ((₀ , ₀) , prf) with prf auto
  ... | ()
  [_]ᵃ {n} ((₀ , ₁) , prf) = ε
  [_]ᵃ {n} ((₀ , ₂) , prf) = [ (- ₂ , ₀) , (λ ()) ]ᵃ • H
--  [_]ᵃ {n} ((₂ , ₀) , prf) = H ^ 3
  [_]ᵃ {n} ((₁ , b) , prf) = H • S ^ -b
    where
    -b = toℕ (- b)
  [_]ᵃ {n} ((a''@(₂₊ a') , b'') , prf) = H • S ^ -a • H • S ^ -a⁻¹[b+1]
    where
    -a⁻¹[b+1]' = - a'' ⁻¹ * (₁ + b'')
    -a⁻¹[b+1] = toℕ -a⁻¹[b+1]'
    -a = toℕ (- a'')

  [_]ᵇ : ∀ {n} → B → Word (Gen (₂₊ n))
  [_]ᵇ {n} (₀ , ₀) = Ex
  [_]ᵇ {n} (₀ , ₁) = H ↑ ^ 3 • CZ • H ↑ • Ex
  [_]ᵇ {n} (a@₀ , b@(₂)) = [ ₀ , ₁ ]ᵇ • [ (a , b) , (λ ()) ]ᵃ ↑
  [_]ᵇ {n} (a@(suc a') , b) = [ ₀ , ₁ ]ᵇ • [ (a , b) , (λ ()) ]ᵃ ↑


{- Sarah's B box
  [_]ᵇ : ∀ {n} → B → Word (Gen (₂₊ n))
  [_]ᵇ {n} (₀ , ₀) = Ex • CZ
  [_]ᵇ {n} (₀ , ₁) = H ↑ ^ 3 • CZ • H ↑ • CZ • CZ • Ex
  [_]ᵇ {n} (a@₀ , b@(₂)) = [ ₀ , ₁ ]ᵇ • CZ • [ (a , b) , (λ ()) ]ᵃ ↑
  [_]ᵇ {n} (a@(suc a') , b) = [ ₀ , ₁ ]ᵇ • CZ • CZ • [ (a , b) , (λ ()) ]ᵃ ↑
-}


  -- F sends XᵃZᵇ to Zᵃ if a ≠ 0, otherwise F is identity.
  [_]ᶠ : ∀ {n} → F → Word (Gen (₁₊ n))
  [_]ᶠ {n} (₀ , _) = ε
--  [_]ᶠ {n} (x@(₁₊ _) , ₀) = H
  [_]ᶠ {n} (x@(₁₊ _) , y) = H • S ^ k
    where
    k = toℕ (- y * x ⁻¹)

  -- G sends X¹⁺ᵃZᵇ to X.
  [_]ᵍ : ∀ {n} → G → Word (Gen (₁₊ n))
  [_]ᵍ {n} (a , b) = (H ^ 2) ^ h • S ^ k
    where
    h = toℕ a
    k = toℕ (- b * (₁₊ a) ⁻¹)

  -- NOTE: [ G ]ᵍ × [ F ]ᶠ ≈ Sp(1,3)

  [_]ᵈ : ∀ {n} → D → Word (Gen (₂₊ n))
  [_]ᵈ {n} (₀ , y) = CZ ^ y' • Ex
    where
    y' = toℕ (- y)
  [_]ᵈ {n} a@(x@(₁₊ _) , y) = [ ₀ , x ]ᵈ • [ a ]ᶠ


{- last used.
  [_]ᵈ : ∀ {n} → D → Word (Gen (₂₊ n))
  [_]ᵈ {n} (₀ , ₀) = Ex
  [_]ᵈ {n} a@(_ , ₁₊ _) = CZ ^ 2 • Ex • [ a , (λ ()) ]ᵃ
  [_]ᵈ {n} a@(₁₊ _ , _) = CZ ^ 2 • Ex • [ a , (λ ()) ]ᵃ 
-}

{- Another choice of dbox
  [_]ᵈ : ∀ {n} → D → Word (Gen (₂₊ n))
  [_]ᵈ {n} (₀ , ₀) = Ex
  [_]ᵈ {n} (₀ , ₂) = CZ • Ex
  [_]ᵈ {n} a@(₀ , ₁) = [ ₀ , ₂ ]ᵈ • H ^ 2 • [ a , (λ ()) ]ᵃ
  [_]ᵈ {n} a@(₁₊ _ , _) = [ ₀ , ₂ ]ᵈ • H ^ 2 • [ a , (λ ()) ]ᵃ 
-}

  [_]ᵉ : ∀ {n} → E → Word (Gen (₁₊ n))
  [_]ᵉ {n} b = S ^ toℕ b

  [_]ᵉ' : ∀ {n} → E' → Word (Gen (₂₊ n))
  [_]ᵉ' {n} b = CZ ^ toℕ b

  [_]ᵛᵇ : ∀ {n} → Vec B n → Word (Gen (₁₊ n))
  [_]ᵛᵇ {₀} [] = ε
  [_]ᵛᵇ {suc n} (x ∷ v) = [ v ]ᵛᵇ ↑ • [ x ]ᵇ

  [_]ᵛᵈ : ∀ {n} → Vec D n → Word (Gen (₁₊ n))
  [_]ᵛᵈ {₀} [] = ε
  [_]ᵛᵈ {suc n} (x ∷ v) = [ x ]ᵈ • [ v ]ᵛᵈ ↑

  [_]ᵐ : ∀ {n} → M n → Word (Gen (₁₊ n))
  [_]ᵐ {n} (e , ds) = [ e ]ᵉ • [ ds ]ᵛᵈ

  abox : ∀ {j n} → j ≤ n → A → Word (Gen (₁₊ n))
  abox {₀} {₀} z≤n a = [ a ]ᵃ
  abox {₀} {₁₊ n} z≤n a = abox {₀} {n} z≤n a ↑
  abox {₁₊ j} {₁₊ n} (s≤s j≤n) a = abox {j} {n} (j≤n) a ↓

  bbox : ∀ {j n} → j ≤ n → B → Word (Gen (₂₊ n))
  bbox {₀} {₀} z≤n b = [ b ]ᵇ
  bbox {₀} {₁₊ n} z≤n b = bbox {₀} {n} z≤n b ↑
  bbox {₁₊ j} {₁₊ n} (s≤s j≤n) b = bbox {j} {n} (j≤n) b ↓

  lemma-[]ᵇ : ∀ {n} b → ([_]ᵇ {n} b ↓) ≡ [ b ]ᵇ
  lemma-[]ᵇ {n} (₀ , ₀) = auto
  lemma-[]ᵇ {n} (₀ , ₁) = auto
  lemma-[]ᵇ {n} (₀ , ₂) = auto
  lemma-[]ᵇ {n} (₁ , ₀) = auto
  lemma-[]ᵇ {n} (₁ , ₁) = auto
  lemma-[]ᵇ {n} (₁ , ₂) = auto
  lemma-[]ᵇ {n} (₂ , ₀) = auto
  lemma-[]ᵇ {n} (₂ , ₁) = auto
  lemma-[]ᵇ {n} (₂ , ₂) = auto


  lemma-bbox : ∀ {n} b → (bbox (NP.≤-reflexive {n} auto) b ↓) ≡ [ b ]ᵇ
  lemma-bbox {₀} (₀ , ₀) = auto
  lemma-bbox {₀} (₀ , ₁) = auto
  lemma-bbox {₀} (₀ , ₂) = auto
  lemma-bbox {₀} (₁ , ₀) = auto
  lemma-bbox {₀} (₁ , ₁) = auto
  lemma-bbox {₀} (₁ , ₂) = auto
  lemma-bbox {₀} (₂ , ₀) = auto
  lemma-bbox {₀} (₂ , ₁) = auto
  lemma-bbox {₀} (₂ , ₂) = auto
  lemma-bbox {₁₊ n} b = begin
    ((bbox (NP.≤-reflexive auto) b ↓) ↓) ≡⟨ Eq.cong _↓ (lemma-bbox b) ⟩
    ([ b ]ᵇ ↓) ≡⟨ lemma-[]ᵇ b ⟩
    [ b ]ᵇ ∎
    where open ≡-Reasoning


  bboxes : ∀ {j n} → j ≤ n → Vec B j → Word (Gen (₁₊ n))
  bboxes {₀} {n} j≤n [] = ε
  bboxes {₁₊ j} {₁₊ n} (s≤s j≤n) (b ∷ v) = bboxes j≤n v ↑ • bbox j≤n b

  lemma-bboxes : ∀ {n} (vb : Vec B n) → bboxes (NP.≤-reflexive auto) vb ≡ [ vb ]ᵛᵇ
  lemma-bboxes {₀} [] = auto
  lemma-bboxes {₁} (b ∷ []) = auto
  lemma-bboxes {₂₊ n} (b ∷ vb) = Eq.cong₂ _•_ (Eq.cong _↑ (lemma-bboxes vb)) (lemma-bbox b) 

  [_]ˡ' : ∀ {j} → L' j → Word (Gen (₁₊ j))
  [_]ˡ' {j} (bs , a) = [ bs ]ᵛᵇ • [ a ]ᵃ

  [_]ˡ : ∀ {n} → L n → Word (Gen (₁₊ n))
  [_]ˡ {n} ((j , bs , a) , j≤n) = bboxes j≤n bs • abox j≤n a

  [_] : ∀ {n} → LM n → Word (Gen (₁₊ n))
  [_] {n} (l , m) = [ m ]ᵐ • [ l ]ˡ

-}


{-
  sform1-antisym' : ∀ (p q : Pauli1) -> sform1 p q ≡ - sform1 q p
  sform1-antisym' p@(a , b) q@(c , d) = begin
    sform1 (a , b) (c , d) ≡⟨ solve p-2 {!4!} {!!} {!!} ⟩
    (- a) * d + c * b ≡⟨ {!\ a b c d -> (solve p-2 4 ? ?)!} ⟩
    - ((- c) * b + a * d) ≡⟨ solve p-2 {!4!} {!!} {!!} ⟩
    - sform1 (c , d) (a , b) ∎
    where
    open ≡-Reasoning
    aux2 : ∀ a b c d e -> - e * ((a) * d + c * b) ≡ - e * (c * b + (a) * d)
    aux2 = solve p-2 5 (\ a b c d e -> (⊝ e) ⊗ ((a) ⊗ d ⊕ c ⊗ b) , (⊝ e) ⊗ (c ⊗ b ⊕ (a) ⊗ d)) λ {x} {x = x₁} {x = x₂} {x = x₃} {x = x₄} → Eq.refl

    aux3 : ∀ a b -> a * b ≡ b * a
    aux3 = solve p-2 2 (\ a b -> a ⊗ b , b ⊗ a) λ {x} {x = x₁} → Eq.refl

-}

  module Two-Qupit-Completeness where

{-
    aux1 : ∀ (p : Pauli 1) -> sform pIₙ p ≡ 0
    aux1 p = {!!}

    Theorem-NF :
    
      ∀ (p q : Pauli 1) ->
      sform p q ≡ 1 ->
      -------------------------------
      ∃ \ nf -> act ⟦ nf ⟧ p ≡ pZ₀ ×
                act ⟦ nf ⟧ q ≡ pX₀
      
    Theorem-NF p@((₀ , ₀) ∷ []) q@(q1 ∷ []) eq with 0ₚ≢1ₚ (Eq.trans (Eq.sym (aux1 q)) eq)
    ... | ()
    Theorem-NF p@((₀ , ₁₊ b) ∷ []) q@((₀ , ₀) ∷ []) eq = {!!}
    Theorem-NF p@((₀ , ₁₊ b) ∷ []) q@((₀ , ₁₊ d) ∷ []) eq = {!!}
    Theorem-NF p@((₀ , ₁₊ b) ∷ []) q@((₁₊ c , ₀) ∷ []) eq = {!!}
    Theorem-NF p@((₀ , ₁₊ b) ∷ []) q@((₁₊ c , ₁₊ d) ∷ []) eq = {!!}
    Theorem-NF p@((₁₊ a , ₀) ∷ []) q@((₀ , ₀) ∷ []) eq = {!!}
    Theorem-NF p@((₁₊ a , ₀) ∷ []) q@((₀ , ₁₊ d) ∷ []) eq = {!!}
    Theorem-NF p@((₁₊ a , ₀) ∷ []) q@((₁₊ c , ₀) ∷ []) eq = {!!}
    Theorem-NF p@((₁₊ a , ₀) ∷ []) q@((₁₊ c , ₁₊ d) ∷ []) eq = {!!}
    Theorem-NF p@((₁₊ a , ₁₊ b) ∷ []) q@((₀ , ₀) ∷ []) eq = {!!}
    Theorem-NF p@((₁₊ a , ₁₊ b) ∷ []) q@((₀ , ₁₊ d) ∷ []) eq = {!!}
    Theorem-NF p@((₁₊ a , ₁₊ b) ∷ []) q@((₁₊ c , ₀) ∷ []) eq = {!!}
    Theorem-NF p@((₁₊ a , ₁₊ b) ∷ []) q@((₁₊ c , ₁₊ d) ∷ []) eq = {!!}
  -}

{-
  prop-abox : ∀ {n} (p : Pauli1) (p≢I : p ≢ pI) (ps : Pauli n) → 
    act [ p , p≢I ]ᵃ (p ∷ ps) ≡ (₀ , ₁) ∷ ps
  prop-abox (₀ , ₀) p≢I ps with p≢I auto
  ... | ()
  prop-abox (₀ , ₁) p≢I ps = auto
  prop-abox (₀ , ₂) p≢I ps = auto
  prop-abox (₁ , ₀) p≢I ps = auto
  prop-abox (₁ , ₁) p≢I ps = auto
  prop-abox (₁ , ₂) p≢I ps = auto
  prop-abox (₂ , ₀) p≢I ps = auto
  prop-abox (₂ , ₁) p≢I ps = auto
  prop-abox (₂ , ₂) p≢I ps = auto

  neqeq : ∀ x → x ≢ pI ⊎ x ≡ pI
  neqeq (₀ , ₀) = inj₂ auto
  neqeq (₀ , ₁) = inj₁ (λ ())
  neqeq (₀ , ₂) = inj₁ (λ ())
  neqeq (₁ , ₀) = inj₁ (λ ())
  neqeq (₁ , ₁) = inj₁ (λ ())
  neqeq (₁ , ₂) = inj₁ (λ ())
  neqeq (₂ , ₀) = inj₁ (λ ())
  neqeq (₂ , ₁) = inj₁ (λ ())
  neqeq (₂ , ₂) = inj₁ (λ ())



  prop-abox-↓ : ∀ {n} (p : Pauli1) (p≢I : p ≢ pI) (ps : Pauli (₁₊ n)) → 
    act ([ p , p≢I ]ᵃ ↓) (p ∷ ps) ≡ (₀ , ₁) ∷ ps
  prop-abox-↓ (₀ , ₀) p≢I ps with p≢I auto
  ... | ()
  prop-abox-↓ (₀ , ₁) p≢I ps = auto
  prop-abox-↓ (₀ , ₂) p≢I ps = auto
  prop-abox-↓ (₁ , ₀) p≢I ps = auto
  prop-abox-↓ (₁ , ₁) p≢I ps = auto
  prop-abox-↓ (₁ , ₂) p≢I ps = auto
  prop-abox-↓ (₂ , ₀) p≢I ps = auto
  prop-abox-↓ (₂ , ₁) p≢I ps = auto
  prop-abox-↓ (₂ , ₂) p≢I ps = auto

  lemma-[]ᵃ : ∀ {n} a → ([_]ᵃ {n} a ↓) ≡ [ a ]ᵃ
  lemma-[]ᵃ ((₀ , ₀) , p≢I) with p≢I auto
  ... | ()
  lemma-[]ᵃ ((₀ , ₁) , p≢I) = auto
  lemma-[]ᵃ ((₀ , ₂) , p≢I) = auto
  lemma-[]ᵃ ((₁ , ₀) , p≢I) = auto
  lemma-[]ᵃ ((₁ , ₁) , p≢I) = auto
  lemma-[]ᵃ ((₁ , ₂) , p≢I) = auto
  lemma-[]ᵃ ((₂ , ₀) , p≢I) = auto
  lemma-[]ᵃ ((₂ , ₁) , p≢I) = auto
  lemma-[]ᵃ ((₂ , ₂) , p≢I) = auto


  lemma-abox-a : ∀ {n} a → (abox (NP.≤-reflexive {n} auto) a) ≡ [ a ]ᵃ
  lemma-abox-a {₀} ((₀ , ₀) , p≢I) with p≢I auto
  ... | ()
  lemma-abox-a {₀} ((₀ , ₁) , p≢I) = auto
  lemma-abox-a {₀} ((₀ , ₂) , p≢I) = auto
  lemma-abox-a {₀} ((₁ , ₀) , p≢I) = auto
  lemma-abox-a {₀} ((₁ , ₁) , p≢I) = auto
  lemma-abox-a {₀} ((₁ , ₂) , p≢I) = auto
  lemma-abox-a {₀} ((₂ , ₀) , p≢I) = auto
  lemma-abox-a {₀} ((₂ , ₁) , p≢I) = auto
  lemma-abox-a {₀} ((₂ , ₂) , p≢I) = auto
  lemma-abox-a {₁₊ n} a = begin
    (abox (NP.≤-reflexive auto) a ↓) ≡⟨ Eq.cong _↓ (lemma-abox-a a) ⟩
    ( [ a ]ᵃ ↓) ≡⟨ lemma-[]ᵃ a ⟩
    [ a ]ᵃ ∎
    where open ≡-Reasoning

{-
  prop-abox-↓↓ : ∀ {j n} (p : Pauli1) (p≢I : p ≢ pI) (le : j ≤ n) (ps : Pauli n) → 
    act (abox le (p , p≢I)) (p ∷ ps) ≡ (₀ , ₁) ∷ ps
  prop-abox-↓↓ (₀ , ₀) p≢I le ps with p≢I auto
  ... | ()
  prop-abox-↓↓ (₀ , ₁) p≢I le ps = {!!}
  prop-abox-↓↓ (₀ , ₂) p≢I le ps = {!!}
  prop-abox-↓↓ (₁ , ₀) p≢I le ps = {!!}
  prop-abox-↓↓ (₁ , ₁) p≢I le ps = {!!}
  prop-abox-↓↓ (₁ , ₂) p≢I le ps = {!!}
  prop-abox-↓↓ (₂ , ₀) p≢I le ps = {!!}
  prop-abox-↓↓ (₂ , ₁) p≢I le ps = {!!}
  prop-abox-↓↓ (₂ , ₂) p≢I le ps = {!!}
-}

  prop-bbox : ∀ {n} (p : Pauli1) (ps : Pauli n) → act [ p ]ᵇ (pZ ∷ p ∷ ps) ≡ pI ∷ pZ ∷ ps
  prop-bbox (₀ , ₀) ps = auto
  prop-bbox (₀ , ₁) ps = auto
  prop-bbox (₀ , ₂) ps = auto
  prop-bbox (₁ , ₀) ps = auto
  prop-bbox (₁ , ₁) ps = auto
  prop-bbox (₁ , ₂) ps = auto
  prop-bbox (₂ , ₀) ps = auto
  prop-bbox (₂ , ₁) ps = auto
  prop-bbox (₂ , ₂) ps = auto

  prop-dbox : ∀ {n} (p : Pauli1) (ps : Pauli n) → act [ p ]ᵈ (p ∷ pX ∷ ps) ≡ pX ∷ pI ∷ ps
  prop-dbox (₀ , ₀) ps = auto
  prop-dbox (₀ , ₁) ps = auto
  prop-dbox (₀ , ₂) ps = auto
  prop-dbox (₁ , ₀) ps = auto
  prop-dbox (₁ , ₁) ps = auto
  prop-dbox (₁ , ₂) ps = auto
  prop-dbox (₂ , ₀) ps = auto
  prop-dbox (₂ , ₁) ps = auto
  prop-dbox (₂ , ₂) ps = auto


  prop-dbox-XZᵇ : ∀ {n} (p : Pauli1) (ᵇ : ℤ ₚ) (ps : Pauli n) → act [ p ]ᵈ (p ∷ pXZ ᵇ ∷ ps) ≡ pXZ ᵇ ∷ pI ∷ ps
  prop-dbox-XZᵇ (₀ , ₀) ₀ ps = auto
  prop-dbox-XZᵇ (₀ , ₀) ₁ ps = auto
  prop-dbox-XZᵇ (₀ , ₀) ₂ ps = auto
  prop-dbox-XZᵇ (₀ , ₁) ₀ ps = auto
  prop-dbox-XZᵇ (₀ , ₁) ₁ ps = auto
  prop-dbox-XZᵇ (₀ , ₁) ₂ ps = auto
  prop-dbox-XZᵇ (₀ , ₂) ₀ ps = auto
  prop-dbox-XZᵇ (₀ , ₂) ₁ ps = auto
  prop-dbox-XZᵇ (₀ , ₂) ₂ ps = auto
  prop-dbox-XZᵇ (₁ , ₀) ₀ ps = auto
  prop-dbox-XZᵇ (₁ , ₀) ₁ ps = auto
  prop-dbox-XZᵇ (₁ , ₀) ₂ ps = auto
  prop-dbox-XZᵇ (₁ , ₁) ₀ ps = auto
  prop-dbox-XZᵇ (₁ , ₁) ₁ ps = auto
  prop-dbox-XZᵇ (₁ , ₁) ₂ ps = auto
  prop-dbox-XZᵇ (₁ , ₂) ₀ ps = auto
  prop-dbox-XZᵇ (₁ , ₂) ₁ ps = auto
  prop-dbox-XZᵇ (₁ , ₂) ₂ ps = auto
  prop-dbox-XZᵇ (₂ , ₀) ₀ ps = auto
  prop-dbox-XZᵇ (₂ , ₀) ₁ ps = auto
  prop-dbox-XZᵇ (₂ , ₀) ₂ ps = auto
  prop-dbox-XZᵇ (₂ , ₁) ₀ ps = auto
  prop-dbox-XZᵇ (₂ , ₁) ₁ ps = auto
  prop-dbox-XZᵇ (₂ , ₁) ₂ ps = auto
  prop-dbox-XZᵇ (₂ , ₂) ₀ ps = auto
  prop-dbox-XZᵇ (₂ , ₂) ₁ ps = auto
  prop-dbox-XZᵇ (₂ , ₂) ₂ ps = auto


  prop-ebox : ∀ {n} (b : ℤ ₚ) (p : Pauli n) → 
    act [ - b ]ᵉ ((₁ , b) ∷ p) ≡ (₁ , ₀) ∷ p
  prop-ebox {n} ₀ p = auto
  prop-ebox {n} ₁ p = auto
  prop-ebox {n} ₂ p = auto

  prop-ebox-dual : ∀ {n} (b : ℤ ₚ) → 
    act ([_]ᵉ {n} b) pZ₀ ≡ pZ₀
  prop-ebox-dual {₀} ₀ = auto
  prop-ebox-dual {₀} ₁ = auto
  prop-ebox-dual {₀} ₂ = auto
  prop-ebox-dual {₁₊ n} ₀ = auto
  prop-ebox-dual {₁₊ n} ₁ = auto
  prop-ebox-dual {₁₊ n} ₂ = auto

  prop-dbox-Z : ∀ {n} (p : Pauli1) (ps : Pauli n) → act [ p ]ᵈ (pI ∷ pZ ∷ ps) ≡ pZ ∷ pI ∷ ps
  prop-dbox-Z (₀ , ₀) ps = auto
  prop-dbox-Z (₀ , ₁) ps = auto
  prop-dbox-Z (₀ , ₂) ps = auto
  prop-dbox-Z (₁ , ₀) ps = auto
  prop-dbox-Z (₁ , ₁) ps = auto
  prop-dbox-Z (₁ , ₂) ps = auto
  prop-dbox-Z (₂ , ₀) ps = auto
  prop-dbox-Z (₂ , ₁) ps = auto
  prop-dbox-Z (₂ , ₂) ps = auto



{-
  prop-bbox-X : ∀ {n} (p : Pauli1) (ps : Pauli n) → ∃ \ q → (act [ p ]ᵇ (pX ∷ p ∷ ps)) ≡ q ∷ pX ∷ ps
  prop-bbox-X (₀ , ₀) p = (₀ , ₀) , auto
  prop-bbox-X (₀ , ₁) p = (₀ , ₁ + 2F * pX .proj₂) , auto
  prop-bbox-X (₀ , ₂) p = (2F *
                            (2F * (2F * ₂ + (2F * ₂ + ₀)) +
                             (2F * (2F * ₂ + (2F * ₂ + ₀)) + 2F * ₂))
                            , 2F * (2F * ₂ + (2F * ₂ + ₀)) + 2F * pX .proj₂)
                           , auto
  prop-bbox-X (₁ , ₀) p = (2F * (2F * (2F * (₁ + ₀)) + 2F * ₁) ,
                            2F * (2F * (₁ + ₀)) + 2F * pX .proj₂)
                           , auto
  prop-bbox-X (₁ , ₁) p = (2F *
                            (2F *
                             (2F * (2F * (2F * ₁) + (2F * (2F * ₁) + 2F * ₁)) +
                              (2F * (2F * (2F * ₁) + (2F * (2F * ₁) + 2F * ₁)) + 2F * (2F * ₁)))
                             + 2F * (2F * (2F * ₁) + (2F * (2F * ₁) + 2F * ₁)))
                            ,
                            2F *
                            (2F * (2F * (2F * ₁) + (2F * (2F * ₁) + 2F * ₁)) +
                             (2F * (2F * (2F * ₁) + (2F * (2F * ₁) + 2F * ₁)) + 2F * (2F * ₁)))
                            + 2F * pX .proj₂)
                           , auto
  prop-bbox-X (₁ , ₂) p = (2F * (2F * (2F * (2F * ₂) + (2F * (2F * ₂) + 2F * ₁))) ,
                            2F *
                            (2F * (2F * (2F * ₂) + (2F * (2F * ₂) + 2F * ₁)) +
                             (2F * (2F * (2F * ₂) + (2F * (2F * ₂) + 2F * ₁)) + 2F * (2F * ₂)))
                            + 2F * pX .proj₂)
                           , auto
  prop-bbox-X (₂ , ₀) p = (2F *
                            (2F * (2F * (₂ + (₂ + ₀))) + (2F * (2F * (₂ + (₂ + ₀))) + 2F * ₂))
                            , 2F * (2F * (₂ + (₂ + ₀))) + 2F * pX .proj₂)
                           , auto
  prop-bbox-X (₂ , ₁) p = (2F *
                            (2F * (2F * (2F * (2F * ₁) + 2F * ₂) + 2F * (2F * ₁)) +
                             (2F * (2F * (2F * (2F * ₁) + 2F * ₂) + 2F * (2F * ₁)) +
                              2F * (2F * (2F * ₁) + 2F * ₂)))
                            ,
                            2F * (2F * (2F * (2F * ₁) + 2F * ₂) + 2F * (2F * ₁)) +
                            2F * pX .proj₂)
                           , auto
  prop-bbox-X (₂ , ₂) p = (2F * (2F * (2F * (2F * ₂) + 2F * ₂)) ,
                            2F * (2F * (2F * (2F * ₂) + 2F * ₂) + 2F * (2F * ₂)) +
                            2F * pX .proj₂)
                           , auto
-}

  prop-dbox-I : ∀ {n} (p : Pauli1) (ps : Pauli n) → act [ p ]ᵈ (pI ∷ pI ∷ ps) ≡ pI ∷ pI ∷ ps
  prop-dbox-I (₀ , ₀) ps = auto
  prop-dbox-I (₀ , ₁) ps = auto
  prop-dbox-I (₀ , ₂) ps = auto
  prop-dbox-I (₁ , ₀) ps = auto
  prop-dbox-I (₁ , ₁) ps = auto
  prop-dbox-I (₁ , ₂) ps = auto
  prop-dbox-I (₂ , ₀) ps = auto
  prop-dbox-I (₂ , ₁) ps = auto
  prop-dbox-I (₂ , ₂) ps = auto


  prop-dboxes : ∀ {n} (vd : Vec D n) → act [ vd ]ᵛᵈ (pZₙ) ≡ pZ₀
  prop-dboxes {₀} [] = auto
  prop-dboxes {₁} (x ∷ []) = prop-dbox-Z x pIₙ
  prop-dboxes {₂₊ n} vd@(x ∷ ds) = begin
    act [ vd ]ᵛᵈ (pI ∷ pI ∷ pZₙ) ≡⟨ auto ⟩
    act [ x ]ᵈ  (act ([ ds ]ᵛᵈ ↑) (pI ∷ pI ∷ pZₙ)) ≡⟨ Eq.cong (act [ x ]ᵈ) (lemma-act-↑ [ ds ]ᵛᵈ pI (pI ∷ pZₙ)) ⟩
    act [ x ]ᵈ  (pI ∷ act [ ds ]ᵛᵈ (pI ∷ pZₙ)) ≡⟨ Eq.cong (\ □ → act [ x ]ᵈ  (pI ∷ □)) (prop-dboxes ds) ⟩
    act [ x ]ᵈ  (pI ∷ (pZ ∷ pIₙ)) ≡⟨ prop-dbox-Z x pIₙ ⟩
    pZ ∷ (₀ , ₀) ∷ (₀ , ₀) ∷ pIₙ ∎
    where open ≡-Reasoning

  last-∷ : ∀ {n}{A : Set}{a : A} {as : Vec A (₁₊ n)} → last (a ∷ as) ≡ last as
  last-∷ {₀} {A} {a} {x ∷ []} = auto
  last-∷ {₁₊ n} {A} {a} {x ∷ x₁ ∷ as} rewrite last-∷ {n} {A} {a} {x₁ ∷ as} = ih
    where
    ih = last-∷ {n} {A} {a} {x₁ ∷ as}

  prop-∃-dboxes : ∀ {n} (ps : Pauli (₁₊ n)) (eqX : last ps ≡ pX) → ∃ \ vd → act [ vd ]ᵛᵈ ps ≡ pX₀
  prop-∃-dboxes {₀} (x ∷ []) eqX rewrite eqX = [] , auto
  prop-∃-dboxes {₁} (x ∷ y ∷ []) eqX rewrite eqX = x ∷ [] , prop-dbox x []
  prop-∃-dboxes {₂₊ n} (x ∷ y ∷ ps) eqX = x ∷ proj₁ ih , (begin
    act [ x ]ᵈ (act ([ proj₁ ih ]ᵛᵈ ↑) (x ∷ y ∷ ps)) ≡⟨ Eq.cong (act [ x ]ᵈ) (lemma-act-↑ [ proj₁ ih ]ᵛᵈ x (y ∷ ps)) ⟩
    act [ x ]ᵈ (x ∷ act ([ proj₁ ih ]ᵛᵈ) (y ∷ ps)) ≡⟨ Eq.cong (\ □ → act [ x ]ᵈ (x ∷ □)) (proj₂ ih) ⟩
    act [ x ]ᵈ (x ∷ pX₀) ≡⟨ prop-dbox x pIₙ ⟩
    pX ∷ (₀ , ₀) ∷ (₀ , ₀) ∷ pIₙ ∎)
    where
    open ≡-Reasoning
    ih : ∃ \ vd → act [ vd ]ᵛᵈ (y ∷ ps) ≡ pX₀
    ih = prop-∃-dboxes {₁₊ n} (y ∷ ps) (Eq.trans (Eq.sym (last-∷ {a = x} {as = y ∷ ps})) eqX)


  prop-∃-dboxes-XZ : ∀ {n} {ᵉ} (ps : Pauli (₁₊ n)) (eqX : last ps ≡ (₁ , ᵉ)) → ∃ \ vd → act [ vd ]ᵛᵈ ps ≡ pX₀Z₀ ᵉ
  prop-∃-dboxes-XZ {₀} {ᵉ} (x ∷ []) eqX rewrite eqX = [] , auto
  prop-∃-dboxes-XZ {₁} {ᵉ} (x ∷ y ∷ []) eqX rewrite eqX = x ∷ [] , prop-dbox-XZᵇ x ᵉ []
  prop-∃-dboxes-XZ {₂₊ n} {ᵉ} (x ∷ y ∷ ps) eqX = x ∷ proj₁ ih , (begin
    act [ x ]ᵈ (act ([ proj₁ ih ]ᵛᵈ ↑) (x ∷ y ∷ ps)) ≡⟨ Eq.cong (act [ x ]ᵈ) (lemma-act-↑ [ proj₁ ih ]ᵛᵈ x (y ∷ ps)) ⟩
    act [ x ]ᵈ (x ∷ act ([ proj₁ ih ]ᵛᵈ) (y ∷ ps)) ≡⟨ Eq.cong (\ □ → act [ x ]ᵈ (x ∷ □)) (proj₂ ih) ⟩
    act [ x ]ᵈ (x ∷ pX₀Z₀ ᵉ) ≡⟨ prop-dbox-XZᵇ x ᵉ pIₙ ⟩
    pX₀Z₀ ᵉ ∎)
    where
    open ≡-Reasoning
    ih : ∃ \ vd → act [ vd ]ᵛᵈ (y ∷ ps) ≡ pX₀Z₀ ᵉ
    ih = prop-∃-dboxes-XZ {₁₊ n} {ᵉ} (y ∷ ps) (Eq.trans (Eq.sym (last-∷ {a = x} {as = y ∷ ps})) eqX)


  prop-∃-bboxes : ∀ {n} (ps : Pauli (₁₊ n)) (eqZ : head ps ≡ pZ) → ∃ \ vb → act [ vb ]ᵛᵇ ps ≡ pZₙ
  prop-∃-bboxes {₀} (x ∷ []) eqZ rewrite eqZ = [] , auto
  prop-∃-bboxes {₁} (x ∷ y ∷ []) eqZ rewrite eqZ = (y ∷ []) , (prop-bbox y [])
  prop-∃-bboxes {₂₊ n} (x ∷ y ∷ z ∷ ps) eqZ rewrite eqZ = y ∷ proj₁ ih , (begin
    act ([ proj₁ ih ]ᵛᵇ ↑) (act [ y ]ᵇ (pZ ∷ y ∷ z ∷ ps)) ≡⟨ Eq.cong (act ([ proj₁ ih ]ᵛᵇ ↑)) (prop-bbox y (z ∷ ps)) ⟩
    act ([ proj₁ ih ]ᵛᵇ ↑) (pI ∷ pZ ∷ z ∷ ps) ≡⟨ lemma-act-↑ [ proj₁ ih ]ᵛᵇ pI (pZ ∷ z ∷ ps) ⟩
    pI ∷ act ([ proj₁ ih ]ᵛᵇ) (pZ ∷ z ∷ ps) ≡⟨ Eq.cong (pI ∷_) (proj₂ ih) ⟩
    pI ∷ pI ∷ pZₙ ∎)
    where
    open ≡-Reasoning
    ih : ∃ \ vd → act [ vd ]ᵛᵇ (pZ ∷ z ∷ ps) ≡ pZₙ
    ih = prop-∃-bboxes (pZ ∷ z ∷ ps) auto

  prop-∃-M : ∀ {n} {e} (ps : Pauli (₁₊ n)) (eqX : last ps ≡ (₁ , e)) → ∃ \ m → act [ m ]ᵐ ps ≡ pX₀
  prop-∃-M {0} {e} (x ∷ []) eqX rewrite eqX = (- e , []) , prop-ebox e []
  prop-∃-M {n@(suc m)} {e} ps eqX = (- e , proj₁ vdp) , (begin
    act [ - e ]ᵉ (act [ proj₁ vdp ]ᵛᵈ ps) ≡⟨ Eq.cong (act [ - e ]ᵉ) (proj₂ vdp) ⟩
    act [ - e ]ᵉ (pX₀Z₀ e) ≡⟨ prop-ebox e pIₙ ⟩
    pX₀ ∎)
    where
    open ≡-Reasoning
    vdp = prop-∃-dboxes-XZ {n} {e} ps eqX

  lemma-init-last : ∀ {n} {A : Set} (vs : Vec A (₁₊ n)) → vs ≡ init vs ∷ʳ last vs
  lemma-init-last (x ∷ []) = auto
  lemma-init-last (x ∷ x₁ ∷ vs) = Eq.cong (x ∷_) (lemma-init-last (x₁ ∷ vs))

  lemma-<⇒≤ : ∀ {j n} (le : j < (₁₊ n)) → NP.<⇒≤ (s≤s le) ≡ s≤s (NP.<⇒≤ le)
  lemma-<⇒≤ (s≤s z≤n) = auto
  lemma-<⇒≤ (s≤s (s≤s le)) = auto

  lemma-sspred : ∀ {j n} (le : j < (₁₊ n)) → s≤s (NP.≤-pred le) ≡ le
  lemma-sspred (s≤s z≤n) = auto
  lemma-sspred (s≤s (s≤s le)) = auto

  lemma-abox : ∀ {n j} p (ps : Pauli (₁₊ n)) (le : j < (₁₊ n)) a (neq : a ≢ pI) →
    act (abox (NP.<⇒≤ le) (a , neq)) (p ∷ ps) ≡ p ∷ act (abox (NP.≤-pred le) (a , neq)) ps
  lemma-abox {₀} {₀} p (x ∷ []) (s≤s z≤n) a neq = lemma-act-↑ ([ a , neq ]ᵃ) p (x ∷ [])
  lemma-abox {₁₊ n} {₀} p (x ∷ x₁ ∷ ps) (s≤s z≤n) a neq = lemma-act-↑ (abox z≤n (a , neq) ↑) p (x ∷ x₁ ∷ ps)
  lemma-abox {₁₊ n} {₁₊ j} p (x ∷ ps) (s≤s le) a neq = begin
    act (abox (NP.<⇒≤ (s≤s le)) (a , neq)) (p ∷ x ∷ ps) ≡⟨ Eq.cong (\ □ → act (abox □ (a , neq)) (p ∷ x ∷ ps)) ( lemma-<⇒≤ le) ⟩
    act (abox (s≤s (NP.<⇒≤ le)) (a , neq)) (p ∷ x ∷ ps) ≡⟨ auto ⟩
    act (abox (NP.<⇒≤ le) (a , neq) ↓) (p ∷ x ∷ ps) ≡⟨ Eq.cong (\ □ → act (abox (NP.<⇒≤ le) (a , neq) ↓) (p ∷ x ∷ □)) (lemma-init-last ps) ⟩
    act (abox (NP.<⇒≤ le) (a , neq) ↓) (p ∷ x ∷ (init ps ∷ʳ last ps)) ≡⟨ auto ⟩
    act (abox (NP.<⇒≤ le) (a , neq) ↓) ((p ∷ x ∷ init ps) ∷ʳ last ps) ≡⟨ lemma-act-↓ (abox (NP.<⇒≤ le) (a , neq)) (last ps) (p ∷ x ∷ init ps) ⟩
    act (abox (NP.<⇒≤ le) (a , neq)) (p ∷ x ∷ init ps) ∷ʳ last ps ≡⟨ Eq.cong (_∷ʳ last ps) (lemma-abox p (x ∷ init ps) le a neq) ⟩
    (p ∷ act (abox (NP.≤-pred le) (a , neq)) (x ∷ init ps)) ∷ʳ last ps ≡⟨ auto ⟩
    p ∷ (act (abox (NP.≤-pred le) (a , neq)) (x ∷ init ps) ∷ʳ last ps) ≡⟨ Eq.cong (p ∷_) (Eq.sym (lemma-act-↓ (abox (NP.≤-pred le) (a , neq)) (last ps) (x ∷ init ps))) ⟩
    p ∷ (act (abox (NP.≤-pred le) (a , neq) ↓) ((x ∷ init ps) ∷ʳ last ps)) ≡⟨ auto ⟩
    p ∷ (act (abox (NP.≤-pred le) (a , neq) ↓) (x ∷ (init ps ∷ʳ last ps))) ≡⟨ Eq.cong (\ □ → p ∷ (act (abox (NP.≤-pred le) (a , neq) ↓) (x ∷ □))) (Eq.sym (lemma-init-last ps)) ⟩
    p ∷ (act (abox (NP.≤-pred le) (a , neq) ↓) (x ∷ ps)) ≡⟨ Eq.sym auto ⟩
    p ∷ act (abox (s≤s (NP.≤-pred le)) (a , neq)) (x ∷ ps) ≡⟨ Eq.cong (\ □ → p ∷ act (abox □ (a , neq)) (x ∷ ps)) (lemma-sspred le) ⟩
    p ∷ act (abox le (a , neq)) (x ∷ ps) ∎
    where
    open ≡-Reasoning

  lemma-bbox2 : ∀ {n j} p (ps : Pauli (₂₊ n)) (le : j < (₁₊ n)) b →
    act (bbox (NP.<⇒≤ le) (b)) (p ∷ ps) ≡ p ∷ act (bbox (NP.≤-pred le) (b)) ps
  lemma-bbox2 {₀} {₀} p (x ∷ x₁ ∷ []) (s≤s z≤n) b = lemma-act-↑ [ b ]ᵇ p (x ∷ x₁ ∷ [])
  lemma-bbox2 {₁₊ n} {₀} p (x ∷ ps) (s≤s z≤n) b = lemma-act-↑ (bbox z≤n b ↑) p (x ∷ ps)
  lemma-bbox2 {₁₊ n} {₁₊ j} p (x ∷ ps) (s≤s le) b = begin
    act (bbox (NP.<⇒≤ (s≤s le)) (b)) (p ∷ x ∷ ps) ≡⟨ Eq.cong (\ □ → act (bbox □ (b)) (p ∷ x ∷ ps)) ( lemma-<⇒≤ le) ⟩
    act (bbox (s≤s (NP.<⇒≤ le)) (b)) (p ∷ x ∷ ps) ≡⟨ auto ⟩
    act (bbox (NP.<⇒≤ le) (b) ↓) (p ∷ x ∷ ps) ≡⟨ Eq.cong (\ □ → act (bbox (NP.<⇒≤ le) (b) ↓) (p ∷ x ∷ □)) (lemma-init-last ps) ⟩
    act (bbox (NP.<⇒≤ le) (b) ↓) (p ∷ x ∷ (init ps ∷ʳ last ps)) ≡⟨ auto ⟩
    act (bbox (NP.<⇒≤ le) (b) ↓) ((p ∷ x ∷ init ps) ∷ʳ last ps) ≡⟨ lemma-act-↓ (bbox (NP.<⇒≤ le) (b)) (last ps) (p ∷ x ∷ init ps) ⟩
    act (bbox (NP.<⇒≤ le) (b)) (p ∷ x ∷ init ps) ∷ʳ last ps ≡⟨ Eq.cong (_∷ʳ last ps) (lemma-bbox2 p (x ∷ init ps) le b) ⟩
    (p ∷ act (bbox (NP.≤-pred le) (b)) (x ∷ init ps)) ∷ʳ last ps ≡⟨ auto ⟩
    p ∷ (act (bbox (NP.≤-pred le) (b)) (x ∷ init ps) ∷ʳ last ps) ≡⟨ Eq.cong (p ∷_) (Eq.sym (lemma-act-↓ (bbox (NP.≤-pred le) (b)) (last ps) (x ∷ init ps))) ⟩
    p ∷ (act (bbox (NP.≤-pred le) (b) ↓) ((x ∷ init ps) ∷ʳ last ps)) ≡⟨ auto ⟩
    p ∷ (act (bbox (NP.≤-pred le) (b) ↓) (x ∷ (init ps ∷ʳ last ps))) ≡⟨ Eq.cong (\ □ → p ∷ (act (bbox (NP.≤-pred le) (b) ↓) (x ∷ □))) (Eq.sym (lemma-init-last ps)) ⟩
    p ∷ (act (bbox (NP.≤-pred le) (b) ↓) (x ∷ ps)) ≡⟨ Eq.sym auto ⟩
    p ∷ act (bbox (s≤s (NP.≤-pred le)) (b)) (x ∷ ps) ≡⟨ Eq.cong (\ □ → p ∷ act (bbox □ (b)) (x ∷ ps)) (lemma-sspred le) ⟩
    p ∷ act (bbox le (b)) (x ∷ ps) ∎
    where
    open ≡-Reasoning

  lemma-↑↓ : ∀ {n} (w : Word (Gen n)) → w ↑ ↓ ≡ w ↓ ↑
  lemma-↑↓ [ x ]ʷ = auto
  lemma-↑↓ ε = auto
  lemma-↑↓ (w • w₁) = Eq.cong₂ _•_ (lemma-↑↓ w) (lemma-↑↓ w₁)

  lemma-bbox2a : ∀ {n j} (le : j < (₁₊ n)) b →
    bbox (NP.<⇒≤ le) b ≡ bbox (≤-pred le) b ↑
  lemma-bbox2a {₀} {₀} (s≤s z≤n) b = auto
  lemma-bbox2a {₁₊ n} {₀} (s≤s z≤n) b = auto
  lemma-bbox2a {₁₊ n} {₁₊ j} (s≤s (s≤s le)) b = begin
    (bbox (NP.<⇒≤ (s≤s le)) b ↓) ≡⟨ Eq.cong _↓ ih ⟩
    ((bbox le b ↑) ↓) ≡⟨ lemma-↑↓ (bbox le b) ⟩
    ((bbox le b ↓) ↑) ∎
    where
    open ≡-Reasoning
    ih = lemma-bbox2a (s≤s le) b

  lemma-bboxes2a : ∀ {n j} (le : j < (₁₊ n)) vb →
    bboxes (NP.<⇒≤ le) vb ≡ (bboxes (≤-pred le) vb ↑)
  lemma-bboxes2a {₀} {₀} (s≤s z≤n) [] = auto
  lemma-bboxes2a {₁₊ n} {₀} (s≤s le) [] = auto
  lemma-bboxes2a {₁₊ n} {₁₊ j} (s≤s le@(s≤s le')) (x ∷ vb) = begin
    bboxes (NP.<⇒≤ (s≤s le)) (x ∷ vb) ≡⟨ auto ⟩
    bboxes (s≤s (NP.<⇒≤ le)) (x ∷ vb) ≡⟨ auto ⟩
    bboxes (NP.<⇒≤ (le)) (vb) ↑ • bbox (NP.<⇒≤ (le)) x ≡⟨ Eq.cong (bboxes (NP.<⇒≤ (le)) (vb) ↑ •_) (lemma-bbox2a (s≤s le') x) ⟩
    bboxes (NP.<⇒≤ (le)) (vb) ↑ • bbox (≤-pred le) x ↑ ≡⟨ auto ⟩
    (bboxes (NP.<⇒≤ le) (vb) • bbox (≤-pred le) x) ↑ ≡⟨ Eq.cong ( \ □ → (□ • bbox (≤-pred le) x) ↑) ih ⟩
    (bboxes (≤-pred le) vb ↑ • bbox (≤-pred le) x) ↑ ≡⟨ auto ⟩
    (bboxes (s≤s (≤-pred le)) (x ∷ vb) ↑) ≡⟨ auto ⟩
    (bboxes (≤-pred (s≤s le)) (x ∷ vb) ↑) ∎
    where
    open ≡-Reasoning
    ih = lemma-bboxes2a le vb

  lemma-bboxes2 : ∀ {n j} p (ps : Pauli (₁₊ n)) (le : j < (₁₊ n)) vb →
    act (bboxes (NP.<⇒≤ le) vb) (p ∷ ps) ≡ p ∷ act (bboxes (NP.≤-pred le) vb) ps
  lemma-bboxes2 {₀} {₀} p (x ∷ []) (s≤s z≤n) [] = auto
  lemma-bboxes2 {₁₊ n} {₀} p (x ∷ ps) (s≤s z≤n) [] = auto
  lemma-bboxes2 {₁₊ n} {₁₊ j} p (x ∷ ps) (s≤s le@(s≤s le')) (b ∷ vb) = begin
    act (bboxes (NP.<⇒≤ (s≤s le)) (b ∷ vb)) (p ∷ x ∷ ps) ≡⟨ auto ⟩
    act (bboxes (s≤s (NP.<⇒≤ le)) (b ∷ vb)) (p ∷ x ∷ ps) ≡⟨ auto ⟩
    act (bboxes (NP.<⇒≤ (le)) vb ↑ • bbox (NP.<⇒≤ le) b) (p ∷ x ∷ ps) ≡⟨ auto ⟩
    act (bboxes (NP.<⇒≤ (le)) vb ↑) (act (bbox (NP.<⇒≤ le) b) (p ∷ x ∷ ps)) ≡⟨ Eq.cong (act (bboxes (NP.<⇒≤ (le)) vb ↑)) (lemma-bbox2 p (x ∷ ps) le b) ⟩
    act (bboxes (NP.<⇒≤ (le)) vb ↑) (p ∷ act (bbox (NP.≤-pred le) b) (x ∷ ps)) ≡⟨ lemma-act-↑ (bboxes (NP.<⇒≤ (le)) vb) p (act (bbox (≤-pred le) b) (x ∷ ps)) ⟩
    p ∷ act (bboxes (NP.<⇒≤ (le)) vb) (act (bbox (NP.≤-pred le) b) (x ∷ ps)) ≡⟨ auto ⟩
    p ∷ act (bboxes (NP.<⇒≤ (le)) vb) (act (bbox (NP.≤-pred le) b) (x ∷ ps)) ≡⟨ Eq.cong (\ □ → p ∷ act (□) (act (bbox (NP.≤-pred le) b) (x ∷ ps))) (lemma-bboxes2a (s≤s le') vb) ⟩
    p ∷ act (bboxes ((≤-pred le)) (vb) ↑) (act (bbox ((≤-pred le)) b) (x ∷ ps))  ≡⟨ auto ⟩
    p ∷ act (bboxes ((≤-pred le)) (vb) ↑ • bbox ((≤-pred le)) b) (x ∷ ps)  ≡⟨ auto ⟩
    p ∷ act (bboxes (s≤s (≤-pred le)) (b ∷ vb)) (x ∷ ps)  ≡⟨ auto ⟩
    p ∷ act (bboxes (≤-pred (s≤s le)) (b ∷ vb)) (x ∷ ps) ∎
    where
    open ≡-Reasoning
    ih = lemma-bboxes2 p ps le vb

  prop-∃-L' : ∀ {n} (ps : Pauli n) (p : Pauli1) (p≢I : p ≢ pI) → ∃ \ l → act [ l ]ˡ (p ∷ ps) ≡ pZₙ
  prop-∃-L' {0} [] p neq = ((0 , [] , p , neq) , z≤n) , prop-abox p neq []
  prop-∃-L' {n@(suc n')} ps@(q ∷ qs) p neq =
    let le = NP.≤-reflexive auto in
    let (vb , prf) = prop-∃-bboxes (pZ ∷ q ∷ qs) auto in
    ((n , vb , p , neq), le) , (begin
      act (bboxes le vb) (act (abox le (p , neq)) (p ∷ ps)) ≡⟨ auto ⟩
      act (bboxes le vb) (act (abox le (p , neq)) (p ∷ q ∷ qs)) ≡⟨ Eq.cong (\ □ → act (bboxes le vb) (act (□) (p ∷ q ∷ qs))) (lemma-abox-a (p , neq)) ⟩ --(prop-abox-↓↓ p neq le (q ∷ qs))
      act (bboxes le vb) (act ([(p , neq)]ᵃ) (p ∷ q ∷ qs)) ≡⟨ Eq.cong (act (bboxes le vb)) (prop-abox p neq (q ∷ qs)) ⟩
      act (bboxes le vb) (pZ ∷ q ∷ qs) ≡⟨ Eq.cong (\ □ → act □ (pZ ∷ q ∷ qs)) (lemma-bboxes vb) ⟩
      act ([ vb ]ᵛᵇ) (pZ ∷ q ∷ qs) ≡⟨ prf ⟩
      pZₙ ∎)
    where
    open ≡-Reasoning

{-
  lemma-act-bbox : ∀ {j n} (j<n : j < n) p ps → act (bbox j<n pI) (p ∷ ps) ≡ p ∷ ps
  lemma-act-bbox {₀} {₁₊ n} (s≤s j≤n) p ps = {!!}
  lemma-act-bbox {₁₊ j} {₀} () p ps
  lemma-act-bbox {₁₊ j} {₁₊ n} (s≤s j<n) p ps = {!!}
  lemma-act-bbox {j} {n} (j<n) p ps = begin
    act (bbox j<n pI) (p ∷ ps) ≡⟨ {!!} ⟩
    p ∷ ps ∎
    where
    open ≡-Reasoning

  lemma-bboxes-< : ∀ {j n} (j<n : j < ₁₊ n) (vb : Vec B j) p ps →
    act (bboxes (NP.≤-pred j<n) vb) (p ∷ ps) ≡ {!!} -- p ∷ act (bboxes (j<n) vb) ps
  lemma-bboxes-< {j} {n} (s≤s j<n) vb p ps = begin
    act (bboxes (j<n) (vb)) (p ∷ ps) ≡⟨ Eq.refl ⟩
    {!!} ∎
    where
    open ≡-Reasoning
-}

  prop-∃-L : ∀ {n} (ps : Pauli (₁₊ n)) (≢I : ps ≢ pIₙ {₁₊ n}) → ∃ \ l → act [ l ]ˡ ps ≡ pZₙ
  prop-∃-L {₀} (x ∷ []) ≢I = ((₀ , [] , x , neq) , z≤n) , prop-abox x neq []
    where
    neq : x ≢ pI
    neq eq = ≢I (Eq.cong (_∷ []) eq)
  prop-∃-L {₁} ps@(x ∷ y ∷ []) ≢I = [ c1 , c2 ]′ (neqeq x)
    where
    open ≡-Reasoning
    c1 : x ≢ pI → ∃ \ l → act [ l ]ˡ ps ≡ pZₙ
    c1 neq = ((₁ , (y ∷ []), x , neq) , s≤s z≤n) , (begin
      act [ y ]ᵇ (act ([ x , neq ]ᵃ ↓) (x ∷ y ∷ [])) ≡⟨ Eq.cong (act [ y ]ᵇ) (prop-abox-↓ x neq (y ∷ [])) ⟩
      act [ y ]ᵇ (pZ ∷ y ∷ []) ≡⟨ prop-bbox y [] ⟩
      pI ∷ pZ ∷ [] ∎)

    c2 : x ≡ pI → ∃ \ l → act [ l ]ˡ ps ≡ pZₙ
    c2 eq rewrite eq = ((₀ , ([]), y , neq) , z≤n) , (begin
      act ([ y , neq ]ᵃ ↑) (pI ∷ y ∷ []) ≡⟨ lemma-act-↑ [ y , neq ]ᵃ pI (y ∷ []) ⟩
      pI ∷ act ([ y , neq ]ᵃ) (y ∷ []) ≡⟨ Eq.cong (pI ∷_) (prop-abox y neq []) ⟩
      pI ∷ pZ ∷ [] ∎)
      where
      neq : y ≢ pI
      neq eq2 rewrite eq | eq2 = ≢I auto

  prop-∃-L {₂₊ n} ps@(x ∷ y ∷ ps') ≢I = [ c1 , c2 ]′ (neqeq x)
    where
    open ≡-Reasoning
    c1 : x ≢ pI → ∃ \ l → act [ l ]ˡ ps ≡ pZₙ
    c1 neq = prop-∃-L' (y ∷ ps') x neq
    
    c2 : x ≡ pI → ∃ \ l → act [ l ]ˡ ps ≡ pZₙ
    c2 eq rewrite eq =
      let ((j , qs , a , neq) , le) , prf = ih in
      let le' = s≤s le in
      let le'' = NP.<⇒≤ le' in
        ((j , qs , a , neq) , le'') , (begin
           act (bboxes le'' qs) (act (abox le'' (a , neq)) ((₀ , ₀) ∷ y ∷ ps')) ≡⟨ Eq.cong (act (bboxes le'' qs)) (lemma-abox pI (y ∷ ps') le' a neq) ⟩
           act (bboxes le'' qs) ((₀ , ₀) ∷ act (abox (≤-pred le') (a , neq)) (y ∷ ps')) ≡⟨ lemma-bboxes2 pI (act (abox (≤-pred le') (a , neq)) (y ∷ ps')) (le') qs ⟩
           (₀ , ₀) ∷ act (bboxes (≤-pred le') qs) (act (abox (≤-pred le') (a , neq)) (y ∷ ps')) ≡⟨ auto ⟩
           (₀ , ₀) ∷ act (bboxes le qs) (act (abox le (a , neq)) (y ∷ ps')) ≡⟨ Eq.cong (pI ∷_) prf ⟩
           (₀ , ₀) ∷ (₀ , ₀) ∷ pZₙ ∎)
      where
      neq : y ∷ ps' ≢ pIₙ
      neq eq2 rewrite eq | eq2 = ≢I auto
      
      ih = prop-∃-L {₁₊ n} (y ∷ ps') neq







  -- open import Data.Product.Relation.Binary.Pointwise.NonDependent as PW
  -- open import Tactic.RingSolver

  lemma-sform-aux-s : ∀ a b c d → sform1 (a , b) (c , d) ≡ sform1 (a , a + b) (c , c + d)
  lemma-sform-aux-s a b c d = begin
    (- a) * d + c * b ≡⟨ lemma-sform-aux-s' a b c d  ⟩
    (- a) * (c + d) + c * (a + b) ∎
    where
    open ≡-Reasoning

  lemma-sform-aux : ∀ a b c d → sform1  (a , b) (c , d) ≡ sform1 (2F * b , a) (2F * d , c)
  lemma-sform-aux a b c d = lemma-sform-aux-h a b c d

  lemma-sform-aux-cz :  ∀ x y z w → sform1 (x .proj₁ , x .proj₂ + y .proj₁)
      (z .proj₁ , z .proj₂ + w .proj₁)
      +
      sform1 (y .proj₁ , x .proj₁ + y .proj₂)
       (w .proj₁ , z .proj₁ + w .proj₂)
      ≡ sform1 x z + sform1 y w
  lemma-sform-aux-cz x y z w = Eq.sym (lemma-sform-aux-cz' (x .proj₁) (x .proj₂) (z .proj₁) (z .proj₂) (y .proj₁) (y .proj₂) (w .proj₁) (w .proj₂))

  lemma-sform-fix-gen : ∀ {n} g ps qs → sform {n} (act1 g ps) (act1 g qs) ≡ sform ps qs
  lemma-sform-fix-gen {n} H-gen (x ∷ ps) (x₁ ∷ qs) = Eq.cong₂ _+_ (Eq.sym (lemma-sform-aux (proj₁ x) (proj₂ x) (proj₁ x₁) (proj₂ x₁))) Eq.refl
  lemma-sform-fix-gen {n} S-gen (x ∷ ps) (x₁ ∷ qs) = Eq.cong₂ _+_ (Eq.sym (lemma-sform-aux-s (proj₁ x) (proj₂ x) (proj₁ x₁) (proj₂ x₁))) Eq.refl
  lemma-sform-fix-gen {n} CZ-gen (x ∷ x₂ ∷ ps) (x₁ ∷ x₃ ∷ qs) = begin
    sform1 (x .proj₁ , x .proj₂ + x₂ .proj₁) (x₁ .proj₁ , x₁ .proj₂ + x₃ .proj₁) + (sform1 (x₂ .proj₁ , x .proj₁ + x₂ .proj₂) (x₃ .proj₁ , x₁ .proj₁ + x₃ .proj₂) + sform ps qs) ≡⟨ Eq.sym (+-assoc (sform1 (x .proj₁ , x .proj₂ + x₂ .proj₁) (x₁ .proj₁ , x₁ .proj₂ + x₃ .proj₁) )  (sform1 (x₂ .proj₁ , x .proj₁ + x₂ .proj₂) (x₃ .proj₁ , x₁ .proj₁ + x₃ .proj₂))  (sform ps qs)) ⟩
    (sform1 (x .proj₁ , x .proj₂ + x₂ .proj₁) (x₁ .proj₁ , x₁ .proj₂ + x₃ .proj₁) + sform1 (x₂ .proj₁ , x .proj₁ + x₂ .proj₂) (x₃ .proj₁ , x₁ .proj₁ + x₃ .proj₂)) + sform ps qs ≡⟨ Eq.cong₂ _+_ (lemma-sform-aux-cz x x₂ x₁ x₃) auto ⟩
    (sform1 x x₁ + sform1 x₂ x₃) + sform ps qs ≡⟨ +-assoc (sform1 x x₁) (sform1 x₂ x₃)  (sform ps qs) ⟩
    sform1 x x₁ + (sform1 x₂ x₃ + sform ps qs) ∎
    where open ≡-Reasoning
    
  lemma-sform-fix-gen {n} (g ↥) (x ∷ ps) (x₁ ∷ qs) = Eq.cong₂ _+_ (Eq.refl {x = sform1 x x₁})  (lemma-sform-fix-gen g ps qs)

  lemma-sform-fix : ∀ {n} w ps qs → sform {n} (act w ps) (act w qs) ≡ sform ps qs
  lemma-sform-fix {n} [ x ]ʷ ps qs = lemma-sform-fix-gen x ps qs
  lemma-sform-fix {n} ε ps qs = auto
  lemma-sform-fix {n} (w • w₁) ps qs = begin
    sform (act w (act w₁ ps)) (act w (act w₁ qs)) ≡⟨ lemma-sform-fix w (act w₁ ps) (act w₁ qs) ⟩
    sform ((act w₁ ps)) ((act w₁ qs)) ≡⟨ lemma-sform-fix w₁ ps qs ⟩
    sform ps qs ∎
    where open ≡-Reasoning


  lemma-sform1-pI' : ∀ x → sform1 pI x ≡ 0F
  lemma-sform1-pI' x = begin
    sform1 pI x ≡⟨ lemma-sform1-pI (x .proj₁) (x .proj₂) ⟩
    0F ∎
    where
    open ≡-Reasoning

  lemma-sform1-pIʳ : ∀ x → sform1 x pI ≡ 0F
  lemma-sform1-pIʳ x = begin
    sform1 x pI ≡⟨ lemma-sform1-pIʳ' (x .proj₁) (x .proj₂) ⟩
    0F ∎
    where
    open ≡-Reasoning

  lemma-eq0 : ∀ {n} (ps : Pauli ( n)) → sform pIₙ ps ≡ 0F
  lemma-eq0 {₀} ([]) = auto
  lemma-eq0 {₁₊ n} (x ∷ ps) = Eq.cong₂ _+_ eq0 (lemma-eq0 ps)
    where
    open ≡-Reasoning
    eq0 : sform1 pI x ≡ 0F
    eq0 = begin
      sform1 pI x ≡⟨ lemma-sform1-pI (x .proj₁) (x .proj₂) ⟩
      0F ∎


  lemma-neqI : ∀ {n} (ps qs : Pauli (₁₊ n)) (eq1 : sform ps qs ≡ ₁) → ps ≢ pIₙ
  lemma-neqI ps qs eq1 eq rewrite eq = 1neq0 (Eq.trans (Eq.sym eq1) (lemma-eq0 qs))
    where
    1neq0 : ₁ ≢ 0F
    1neq0 ()

  lemma-na1 : ∀ p → sform1 pZ p ≡ ₁ → proj₁ p ≡ ₁
  lemma-na1 p eq = [ (\ h → ⊥-elim (c0 h)) , (\ h → [ (λ z → z) , (\ h → ⊥-elim (c2 h)) ]′ h )]′ (lemma-enum (proj₁ p))
    where
    c0 : proj₁ p ≡ 0F → ⊥
    c0 eq2 = 0F≠₁ (Eq.trans (Eq.sym aux1) eq)
      where
      0F≠₁ : 0F ≡ ₁ → ⊥
      0F≠₁ ()
      aux1 : sform1 pZ p ≡ 0F
      aux1 rewrite eq2 = auto
    c2 : proj₁ p ≡ 2F → ⊥
    c2 eq2 = 2F≠₁ (Eq.trans (Eq.sym aux1) eq)
      where
      2F≠₁ : 2F ≡ ₁ → ⊥
      2F≠₁ ()
      aux1 : sform1 pZ p ≡ 2F
      aux1 rewrite eq2 = auto

  lemma-₁-trivial : ∀ (p : Pauli1) → proj₁ p ≡ ₁ → ∃ \ e → p ≡ (₁ , e)
  lemma-₁-trivial (a , ₀) eq rewrite eq = ₀ , auto
  lemma-₁-trivial (a , ₁) eq rewrite eq = ₁ , auto
  lemma-₁-trivial (a , ₂) eq rewrite eq = ₂ , auto


  lemma-sform-pzn : ∀ {n} (qs : Pauli (₁₊ n)) (eq1 : sform pZₙ qs ≡ ₁) →
    ∃ \ e → last qs ≡ (₁ , e)
  lemma-sform-pzn (x ∷ []) eq1 = lemma-₁-trivial x aux
    where
    aux0 : sform1 pZ x ≡ ₁
    aux0 = Eq.trans (Eq.sym (+-identityʳ (sform1 pZ x))) eq1
    
    aux : proj₁ (last (x ∷ [])) ≡ ₁
    aux = lemma-na1 x aux0
  lemma-sform-pzn (x ∷ y ∷ qs) eq1 = (proj₁ ih) , (proj₂ ih)
    where
    open ≡-Reasoning
    ihh : sform pZₙ (y ∷ qs) ≡ ₁
    ihh = begin
      sform pZₙ (y ∷ qs) ≡⟨ Eq.sym (+-identityˡ (sform pZₙ (y ∷ qs))) ⟩
      0F + sform pZₙ (y ∷ qs) ≡⟨ Eq.cong (\ □ → □ + sform pZₙ (y ∷ qs)) (Eq.sym (lemma-sform1-pI' x)) ⟩
      sform1 pI x + sform pZₙ (y ∷ qs) ≡⟨ auto ⟩
      sform pZₙ (x ∷ y ∷ qs) ≡⟨ eq1 ⟩
      ₁ ∎

    ih = lemma-sform-pzn (y ∷ qs) ihh

  lemma-lbox : ∀ {n} (ps qs : Pauli (₁₊ n)) (eq1 : sform ps qs ≡ ₁) →
    let (l , pzn) = prop-∃-L ps (lemma-neqI ps qs eq1) in
    ∃ \ e → last (act [ l ]ˡ qs) ≡ (₁ , e)
  lemma-lbox {n} ps qs eq1 = (proj₁ la) , proj₂ la
    where
    open ≡-Reasoning
    lp = prop-∃-L ps (lemma-neqI ps qs eq1)
    pn = lemma-sform-fix [ proj₁ lp ]ˡ ps qs
    ps' = act [ proj₁ lp ]ˡ ps
    qs' = act [ proj₁ lp ]ˡ qs
    eq1' : sform pZₙ qs' ≡ ₁
    eq1' = begin
      sform pZₙ qs' ≡⟨ Eq.cong (\ □ → sform □ qs') (Eq.sym (proj₂ lp)) ⟩
      sform ps' qs' ≡⟨ pn ⟩
      sform ps qs ≡⟨ eq1 ⟩
      ₁ ∎

    la = lemma-sform-pzn qs' eq1'
    em = prop-∃-M qs' (proj₂ la)


  lemma-lbox' : ∀ {n} (ps qs : Pauli (₁₊ n)) (eq1 : sform ps qs ≡ ₁) →
    ∃ \ l → 
    ∃ \ e → last (act [ l ]ˡ qs) ≡ (₁ , e) × (act [ l ]ˡ ps) ≡ pZₙ
  lemma-lbox' {n} ps qs eq1 = proj₁ lp , (proj₁ la) , proj₂ la , proj₂ lp
    where
    open ≡-Reasoning
    lp = prop-∃-L ps (lemma-neqI ps qs eq1)
    pn = lemma-sform-fix [ proj₁ lp ]ˡ ps qs
    ps' = act [ proj₁ lp ]ˡ ps
    qs' = act [ proj₁ lp ]ˡ qs
    eq1' : sform pZₙ qs' ≡ ₁
    eq1' = begin
      sform pZₙ qs' ≡⟨ Eq.cong (\ □ → sform □ qs') (Eq.sym (proj₂ lp)) ⟩
      sform ps' qs' ≡⟨ pn ⟩
      sform ps qs ≡⟨ eq1 ⟩
      ₁ ∎

    la = lemma-sform-pzn qs' eq1'

  prop-∃-LM : ∀ {n} (ps qs : Pauli (₁₊ n)) (eq1 : sform ps qs ≡ ₁) →
    ∃ \ lm → act [ lm ] ps ≡ pZ₀ × act [ lm ] qs ≡ pX₀
  prop-∃-LM {n} ps qs eq1 = (l , m) , claim , claim2
    where
    open ≡-Reasoning
    
    lp = lemma-lbox' ps qs eq1
    l = proj₁ lp
    qs' = act [ l ]ˡ qs
    mp = prop-∃-M qs' (lp .proj₂ .proj₂ .proj₁)
    m = proj₁ mp
    claim : act [ (l , m) ] ps ≡ pZ₀
    claim = begin
      act [ (l , m) ] ps ≡⟨ auto ⟩
      act [ m ]ᵐ (act [ l ]ˡ ps) ≡⟨ Eq.cong (\ □ →  act [ m ]ᵐ □ ) ((lp .proj₂ .proj₂ .proj₂)) ⟩
      act [ m ]ᵐ pZₙ ≡⟨ auto ⟩
      act [ m .proj₁ ]ᵉ (act [ m .proj₂ ]ᵛᵈ pZₙ) ≡⟨ Eq.cong (\ □ → act [ m .proj₁ ]ᵉ □) (prop-dboxes (m .proj₂)) ⟩
      act [ m .proj₁ ]ᵉ (pZ₀) ≡⟨ prop-ebox-dual (m .proj₁) ⟩
      pZ₀ ∎

    claim2 : act [ (l , m) ] qs ≡ pX₀
    claim2 = begin
      act [ (l , m) ] qs ≡⟨ auto ⟩
      act [ m ]ᵐ (act [ l ]ˡ qs) ≡⟨ auto ⟩
      act [ m ]ᵐ qs' ≡⟨ proj₂ mp ⟩
      pX₀ ∎


-}


module Lemmas00 where

  variable
    n : ℕ

  -- open Lemmas hiding (n)
  -- open Lemmas2 hiding (n)
  -- open Lemmas3 hiding (n)

  open import Zp.ModularArithmetic
  open Rewriting

  -- lemma-semi-CZ-HH↓ : let open PB ((₂₊ n) QRel,_===_) in

  --   CZ • H ↓ ^ 2 ≈ H ↓ ^ 2 • CZ^ ₋₁
    
  -- lemma-semi-CZ-HH↓ = {!!}
    


module Symplectic-Powers0 where

  -- This module provides a rewrite system for reducing powers of
  -- Symplectic operators (for example, S⁴ → I). It also commutes
  -- generators on different qubits (for example, H1 H0 → H0 H1).
  -- Finally, it moves scalars to the end of the word. While this is
  -- not yet a very powerful rewrite system, it is a useful
  -- bootstrapping step.
  variable
    n : ℕ

  open Symplectic-Derived-Gen
  open Rewriting


  -- ----------------------------------------------------------------------
  -- * Lemmas

  -- The following lemmas are needed to justify the rewrite steps.

  -- ----------------------------------------------------------------------
  -- * Rewrite rules for monoidal structure and order of generators

  step-order : let open PB ((₁₊ n) QRel,_===_) hiding (_===_) in Step-Function (Gen (₁₊ n))  ((₁₊ n) QRel,_===_)

  -- Order of generators.
  -- step-order (((S-gen ₁)) ∷ ((S-gen ₁)) ∷ ((S-gen ₁)) ∷ xs) = just (xs , at-head (PB.axiom order-S))
  -- step-order (((S-gen ₁) ↥) ∷ ((S-gen ₁) ↥) ∷ ((S-gen ₁) ↥) ∷ xs) = just (xs , at-head (PB.axiom (cong↑ order-S)))
  -- step-order (((S-gen ₁) ↥ ↥) ∷ ((S-gen ₁) ↥ ↥) ∷ ((S-gen ₁) ↥ ↥) ∷ xs) = just (xs , at-head (PB.axiom (cong↑ (cong↑ order-S))))
  step-order (((H-gen ₁)) ∷ ((H-gen ₁)) ∷ ((H-gen ₁)) ∷ ((H-gen ₁)) ∷ xs) = just (xs , at-head (PB.axiom order-H))
  step-order (((H-gen ₁) ↥) ∷ ((H-gen ₁) ↥) ∷ ((H-gen ₁) ↥) ∷ ((H-gen ₁) ↥) ∷ xs) = just (xs , at-head (PB.axiom (cong↑ order-H)))
  step-order (((H-gen ₁) ↥ ↥) ∷ ((H-gen ₁) ↥ ↥) ∷ ((H-gen ₁) ↥ ↥) ∷ ((H-gen ₁) ↥ ↥) ∷ xs) = just (xs , at-head (PB.axiom (cong↑ (cong↑ order-H))))
  -- step-order ((CZ-gen) ∷ (CZ-gen) ∷ (CZ-gen) ∷ xs) = just (xs , at-head (PB.axiom order-CZ))
  -- step-order ((CZ-gen ↥) ∷ (CZ-gen ↥) ∷ (CZ-gen ↥) ∷ xs) = just (xs , at-head (PB.axiom (cong↑ order-CZ)))

  step-order (((S-gen ₁)) ∷ ((H-gen ₁)) ∷ ((S-gen ₁)) ∷ ((H-gen ₁)) ∷ ((S-gen ₁)) ∷ ((H-gen ₁)) ∷ xs) = just (xs , at-head (PB.axiom order-SH))
  step-order (((S-gen ₁) ↥) ∷ ((H-gen ₁) ↥) ∷ ((S-gen ₁) ↥) ∷ ((H-gen ₁) ↥) ∷ ((S-gen ₁) ↥) ∷ ((H-gen ₁) ↥) ∷ xs) = just (xs , at-head (PB.axiom (cong↑ order-SH)))
  step-order (((S-gen ₁) ↥ ↥) ∷ ((H-gen ₁) ↥ ↥) ∷ ((S-gen ₁) ↥ ↥) ∷ ((H-gen ₁) ↥ ↥) ∷ ((S-gen ₁) ↥ ↥) ∷ ((H-gen ₁) ↥ ↥) ∷ xs) = just (xs , at-head (PB.axiom (cong↑ (cong↑ order-SH))))

--  step-order (CZ-gen ∷ (H-gen ₁) ∷ (H-gen ₁) ↥ ∷ CZ-gen ∷ (H-gen ₁) ∷ (H-gen ₁) ↥ ∷ CZ-gen ∷ (H-gen ₁) ∷ (H-gen ₁) ↥ ∷ CZ-gen ∷ (H-gen ₁) ∷ (H-gen ₁) ↥ ∷ CZ-gen ∷ (H-gen ₁) ∷ (H-gen ₁) ↥ ∷ CZ-gen ∷ (H-gen ₁) ∷ (H-gen ₁) ↥ ∷ xs) = just (xs , at-head (PB.axiom lemma-order-Ex))
--  step-order (CZ-gen ↥ ∷ (H-gen ₁) ↥ ∷ (H-gen ₁) ↥ ↥ ∷ CZ-gen ↥ ∷ (H-gen ₁) ↥ ∷ (H-gen ₁) ↥ ↥ ∷ CZ-gen ↥ ∷ (H-gen ₁) ↥ ∷ (H-gen ₁) ↥ ↥ ∷ CZ-gen ↥ ∷ (H-gen ₁) ↥ ∷ (H-gen ₁) ↥ ↥ ∷ CZ-gen ↥ ∷ (H-gen ₁) ↥ ∷ (H-gen ₁) ↥ ↥ ∷ CZ-gen ↥ ∷ (H-gen ₁) ↥ ∷ (H-gen ₁) ↥ ↥ ∷ xs) = just (xs , at-head (PB.axiom (cong↑ order-Ex)))
  

  -- Commuting of generators.

  -- Catch-all
  step-order _ = nothing

  -- From this rewrite relation, we extract a tactic 'general-powers'.
module Powers0-Symplectic (n : ℕ) where

  open Rewriting
  open Symplectic-Powers0 hiding (n)
  open Rewriting.Step (step-cong (step-order {n})) renaming (general-rewrite to general-powers0) public

module Lemmas0 (n : ℕ) where

  open Symplectic-Derived-Gen
  open Symplectic-Derived-GroupLike
  open import Zp.ModularArithmetic

  open PB ((₁₊ n) QRel,_===_) hiding (_===_)
  open PP ((₁₊ n) QRel,_===_)
  open Pattern-Assoc
  open import Data.Nat.DivMod
  open import Data.Fin.Properties


  lemma-S^k+l : ∀ k l -> S^ k • S^ l ≈ S^ (k + l)
  lemma-S^k+l k l = begin
    S^ k • S^ l ≈⟨ cong (axiom (derived-S k)) (axiom (derived-S l)) ⟩
    S ^ toℕ k • S ^ toℕ l ≈⟨ sym (lemma-^-+ S (toℕ k) (toℕ l)) ⟩
    S ^ (toℕ k Nat.+ toℕ l) ≡⟨ Eq.cong (S ^_) (m≡m%n+[m/n]*n k+l p) ⟩
    S ^ (k+l Nat.% p Nat.+ (k+l Nat./ p) Nat.* p) ≈⟨ lemma-^-+ S (k+l Nat.% p) (((k+l Nat./ p) Nat.* p)) ⟩
    S ^ (k+l Nat.% p) • S ^ ((k+l Nat./ p) Nat.* p) ≈⟨ cong (refl' (Eq.cong (S ^_) (Eq.sym (toℕ-fromℕ< (m%n<n k+l p))))) (refl' (Eq.cong (S ^_) (NP.*-comm ((k+l Nat./ p)) p))) ⟩
    S ^ toℕ (fromℕ< (m%n<n k+l p)) • S ^ (p Nat.* (k+l Nat./ p) ) ≈⟨ cong (sym (axiom (derived-S (k + l)))) (sym (lemma-^^ S p (k+l Nat./ p))) ⟩
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
    S^ ₀ ≈⟨ axiom (derived-S ₀) ⟩
    ε ∎
    where
    open SR word-setoid
    k-k = toℕ k Nat.+ toℕ (- k)

  lemma-S^-k+k : ∀ k -> S^ (- k) • S^ k ≈ ε
  lemma-S^-k+k k = begin
    S^ (- k) • S^ k ≈⟨ cong (axiom (derived-S (- k))) (axiom (derived-S k)) ⟩
    S ^ toℕ (- k) • S ^ toℕ k ≈⟨ word-comm (toℕ (- k)) (toℕ ( k)) refl ⟩
    S ^ toℕ k • S ^ toℕ (- k) ≈⟨ cong (sym (axiom (derived-S k))) (sym (axiom (derived-S (- k)))) ⟩
    S^ k • S^ (- k) ≈⟨ lemma-S^k-k k ⟩
    ε ∎
    where
    open SR word-setoid

  open Eq using (_≢_)

  ₁⁻¹ = ((₁ , λ ()) ⁻¹) .proj₁

  
  lemma-M1 : ε ≈ M (₁ , λ ())
  lemma-M1 = begin
    ε ≈⟨ _≈_.sym (axiom order-SH) ⟩
    (S • H) ^ 3 ≈⟨ by-assoc auto ⟩
    S • H • S • H • S • H ≡⟨ auto ⟩
    S^ ₁ • H • S^ ₁ • H • S^ ₁ • H ≡⟨ Eq.cong (\ xx -> S^ ₁ • H • S^ xx • H • S^ ₁ • H) (Eq.sym inv-₁) ⟩
    S^ ₁ • H • S^ ₁⁻¹ • H • S^ ₁ • H ≈⟨ refl ⟩
    M (₁ , λ ()) ∎
    where
    open SR word-setoid


  lemma-[H⁻¹S⁻¹]^3 : (H⁻¹ • S⁻¹) ^ 3 ≈ ε
  lemma-[H⁻¹S⁻¹]^3 = begin
    (H⁻¹ • S⁻¹) ^ 3 ≈⟨ _≈_.sym assoc ⟩
    (H⁻¹ • S⁻¹) WB.^' 3 ≈⟨ lemma-cong-inv (axiom order-SH) ⟩
    winv ε ≈⟨ refl ⟩
    ε ∎
    where
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

  lemma-S⁻¹ : S⁻¹ ≈ S^ ₚ₋₁
  lemma-S⁻¹ = begin
    S⁻¹ ≈⟨ refl ⟩
    S ^ p-1 ≡⟨ Eq.cong (S ^_) (Eq.sym lemma-toℕ-ₚ₋₁) ⟩
    S ^ toℕ ₚ₋₁ ≈⟨ sym (axiom (derived-S ₚ₋₁)) ⟩
    S^ ₚ₋₁ ∎
    where
    open SR word-setoid

  lemma-HH-M-1 : let -'₁ = -' ((₁ , λ ())) in HH ≈ M -'₁
  lemma-HH-M-1 = begin
    HH ≈⟨ trans (sym right-unit) (cright sym lemma-[S⁻¹H⁻¹]^3) ⟩
    HH • (S⁻¹ • H⁻¹) ^ 3 ≈⟨ (cright lemma-^-cong (S⁻¹ • H⁻¹) (S⁻¹ • H • HH) 3 refl) ⟩
    HH • (S⁻¹ • H • HH) ^ 3 ≈⟨ refl ⟩
    HH • (S⁻¹ • H • HH) • (S⁻¹ • H • HH) • (S⁻¹ • H • HH) ≈⟨ (cright cong (cright sym assoc) (special-assoc (□ ^ 3 • □ ^ 3) (□ ^ 2 • □ ^ 2 • □ ^ 2) auto)) ⟩
    HH • (S⁻¹ • HH • H) • (S⁻¹ • H) • (HH • S⁻¹) • H • HH ≈⟨ (cright cong (sym assoc) (cright cleft word-comm 1 p-1 (trans assoc (axiom comm-HHS)))) ⟩
    HH • ((S⁻¹ • HH) • H) • (S⁻¹ • H) • (S⁻¹ • HH) • H • HH ≈⟨ (cright cong (cleft word-comm p-1 1 (sym (trans assoc (axiom comm-HHS)))) (cright assoc)) ⟩
    HH • ((HH • S⁻¹) • H) • (S⁻¹ • H) • S⁻¹ • HH • H • HH ≈⟨ (cright cright cright cright general-powers0 100 auto) ⟩
    HH • ((HH • S⁻¹) • H) • (S⁻¹ • H) • S⁻¹ • H ≈⟨ special-assoc (□ • (□ ^ 2 • □) • □) (□ ^ 2 • □ ^ 2 • □) auto ⟩
    (HH • HH) • (S⁻¹ • H) • (S⁻¹ • H) • S⁻¹ • H ≈⟨ (cleft general-powers0 100 auto) ⟩
    ε • (S⁻¹ • H) • (S⁻¹ • H) • S⁻¹ • H ≈⟨ left-unit ⟩
    (S⁻¹ • H) • (S⁻¹ • H) • S⁻¹ • H ≈⟨ special-assoc ((□ ^ 2) ^ 3) (□ ^ 6) auto ⟩
    S⁻¹ • H • S⁻¹ • H • S⁻¹ • H ≈⟨ cong lemma-S⁻¹ (cright cong lemma-S⁻¹ (cright (cleft lemma-S⁻¹))) ⟩
    S^ ₚ₋₁ • H • S^ ₚ₋₁ • H • S^ ₚ₋₁ • H ≡⟨ Eq.cong (\ xx -> S^ ₚ₋₁ • H • S^ ₚ₋₁ • H • S^ xx • H) p-1=-1ₚ ⟩
    S^ ₚ₋₁ • H • S^ ₚ₋₁ • H • S^ -₁ • H ≡⟨ Eq.cong₂ (\ xx yy -> S^ xx • H • S^ yy • H • S^ -₁ • H) (p-1=-1ₚ) p-1=-1ₚ ⟩
    S^ -₁ • H • S^ -₁ • H • S^ -₁ • H ≡⟨ Eq.cong (\ xx -> S^ -₁ • H • S^ xx • H • S^ -₁ • H) (Eq.sym aux-₁⁻¹) ⟩
    S^ -₁ • H • S^ -₁⁻¹ • H • S^ -₁ • H ≈⟨ refl ⟩
    S^ x • H • S^ x⁻¹ • H • S^ x • H ≡⟨ Eq.refl ⟩
    M x' ∎
    where
    open Powers0-Symplectic n

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
    H • S^ x • H • S^ x⁻¹ • ε • S^ -x⁻¹ ≈⟨ cright cright cright cright sym (cong (axiom order-H) refl) ⟩
    H • S^ x • H • S^ x⁻¹ • H ^ 4 • S^ -x⁻¹ ≈⟨ (cright cright cright cright special-assoc (□ ^ 4 • □) (□ • □ ^ 3 • □) auto) ⟩
    H • S^ x • H • S^ x⁻¹ • H • H ^ 3 • S^ -x⁻¹ ∎
    where
    x⁻¹ = ((x , nz) ⁻¹) .proj₁
    -x⁻¹ = - x⁻¹ 
    open SR word-setoid

  derived-5 : ∀ x k -> (nz : x ≢ ₀) -> let x⁻¹ = ((x , nz) ⁻¹) .proj₁ in let -x⁻¹ = - x⁻¹ in
    M (x , nz) • S ^ k ≈ S ^ (k Nat.* toℕ (x * x)) • M (x , nz)
  derived-5 x k@0 nz = trans right-unit (sym left-unit)
  derived-5 x k@1 nz = begin  
    M (x , nz) • S ^ k ≈⟨ refl ⟩
    M (x , nz) • S ≈⟨ axiom (semi-MS (x , nz)) ⟩
    S^ (x * x) • M (x , nz) ≈⟨ cong (axiom (derived-S (x * x))) refl ⟩
    S ^ toℕ (x * x) • M (x , nz) ≈⟨ (cleft refl' (Eq.cong (S ^_) (Eq.sym ( NP.*-identityˡ (toℕ (x * x)))))) ⟩
    S ^ (k Nat.* toℕ (x * x)) • M (x , nz) ∎
    where
    open SR word-setoid
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

  lemma-MS^k : ∀ x k -> (nz : x ≢ ₀) -> let x⁻¹ = ((x , nz) ⁻¹) .proj₁ in let -x⁻¹ = - x⁻¹ in
    M (x , nz) • S^ k ≈ S^ (k * (x * x)) • M (x , nz)
  lemma-MS^k x k nz = begin 
    M (x , nz) • S^ k ≈⟨ cong refl (axiom (derived-S k)) ⟩
    M (x , nz) • S ^ toℕ k ≈⟨ derived-5 x (toℕ k) nz ⟩
    S ^ (toℕ k Nat.* toℕ (x * x)) • M (x , nz) ≈⟨ (cleft lemma-S^k-% (toℕ k Nat.* toℕ (x * x))) ⟩
    S ^ ((toℕ k Nat.* toℕ (x * x)) % p) • M (x , nz) ≈⟨ (cleft refl' (Eq.cong (S ^_) (lemma-toℕ-% k (x * x)))) ⟩
    S ^ toℕ (k * (x * x)) • M (x , nz) ≈⟨ cong (sym (axiom (derived-S (k * (x * x))))) refl ⟩
    S^ (k * (x * x)) • M (x , nz) ∎
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
    (M (y , nzy) • S^ -x⁻¹) • (S^ x⁻¹ • H • S^ x • H • S^ x⁻¹ • H) • H ^ 3 • S^ -x⁻¹ ≈⟨ (cleft (cright axiom (derived-S -x⁻¹))) ⟩
    (M (y , nzy) • S ^ toℕ -x⁻¹) • (S^ x⁻¹ • H • S^ x • H • S^ x⁻¹ • H) • H ^ 3 • S^ -x⁻¹ ≈⟨ (cleft derived-5 y (toℕ -x⁻¹) nzy) ⟩
    (S ^ (toℕ -x⁻¹ Nat.* toℕ (y * y)) • M (y , nzy)) • (S^ x⁻¹ • H • S^ x • H • S^ x⁻¹ • H) • H ^ 3 • S^ -x⁻¹ ≈⟨ special-assoc (□ ^ 2 • □ ^ 2) (□ • □ ^ 2 • □) auto ⟩
    S ^ (toℕ -x⁻¹ Nat.* toℕ (y * y)) • (M (y , nzy) • (S^ x⁻¹ • H • S^ x • H • S^ x⁻¹ • H)) • H ^ 3 • S^ -x⁻¹ ≈⟨ (cright cleft (cright (cright cright cleft refl' (Eq.cong S^ (Eq.sym (inv-involutive ((x , nz)))))))) ⟩
    S ^ (toℕ -x⁻¹ Nat.* toℕ (y * y)) • (M (y , nzy) • M ((x , nz) ⁻¹)) • H ^ 3 • S^ -x⁻¹ ≈⟨ (cright cleft axiom (M-mul (y , nzy) ((x , nz) ⁻¹))) ⟩
    S ^ (toℕ -x⁻¹ Nat.* toℕ (y * y)) • M ((y , nzy) *' ((x , nz) ⁻¹)) • H ^ 3 • S^ -x⁻¹ ≈⟨ (cright special-assoc (□ • □ ^ 3 • □) (□ ^ 3 • □ ^ 2) auto) ⟩
    S ^ (toℕ -x⁻¹ Nat.* toℕ (y * y)) • (M ((y , nzy) *' ((x , nz) ⁻¹)) • HH) • H • S^ -x⁻¹ ≈⟨ (cright cleft (cright lemma-HH-M-1)) ⟩
    S ^ (toℕ -x⁻¹ Nat.* toℕ (y * y)) • (M ((y , nzy) *' ((x , nz) ⁻¹)) • M -'₁) • H • S^ -x⁻¹ ≈⟨ (cright cleft axiom (M-mul (((y , nzy) *' ((x , nz) ⁻¹))) -'₁)) ⟩
    S ^ (toℕ -x⁻¹ Nat.* toℕ (y * y)) • (M (((y , nzy) *' ((x , nz) ⁻¹)) *' -'₁) ) • H • S^ -x⁻¹ ≈⟨ (cleft sym (lemma-S^ab -x⁻¹ (y * y))) ⟩
    S ^ toℕ (-x⁻¹ * (y * y)) • M -y/x' • (H • S^ -x⁻¹) ≈⟨ cong (sym (axiom (derived-S (-x⁻¹ * (y * y))))) refl ⟩
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


  semi-HM : ∀ (x : ℤ* ₚ) -> H • M x ≈ M (x ⁻¹) • H
  semi-HM x' = begin
    H • (S^ x • H • S^ x⁻¹ • H • S^ x • H) ≈⟨ by-assoc auto ⟩
    (H • S^ x • H) • S^ x⁻¹ • H • S^ x • H ≈⟨ (trans (sym left-unit) (cong lemma-M1 refl)) ⟩
    M₁ • (H • S^ x • H) • S^ x⁻¹ • H • S^ x • H ≈⟨ sym assoc ⟩
    (M₁ • (H • S^ x • H)) • S^ x⁻¹ • H • S^ x • H ≈⟨ (cleft derived-7 x ₁ (x' .proj₂) λ ()) ⟩
    (S^ (-x⁻¹ * (₁ * ₁)) • M (((₁ , λ ()) *' x' ⁻¹) *' -'₁) • H • S^ -x⁻¹) • S^ x⁻¹ • H • S^ x • H ≈⟨ cleft (cright (cleft aux-MM ((((₁ , λ ()) *' x' ⁻¹) *' -'₁) .proj₂) ((-' (x' ⁻¹)) .proj₂) aux-a1)) ⟩
    (S^ (-x⁻¹ * ₁) • M (-' (x' ⁻¹)) • H • S^ -x⁻¹) • S^ x⁻¹ • H • S^ x • H ≈⟨ special-assoc (□ ^ 4 • □ ^ 4) (□ • □ ^ 4 • □ ^ 3) auto ⟩
    S^ (-x⁻¹ * ₁) • (M (-' (x' ⁻¹)) • H • S^ -x⁻¹ • S^ x⁻¹) • H • S^ x • H ≈⟨ cong (refl' (Eq.cong S^ (*-identityʳ -x⁻¹))) (cleft cright (cright lemma-S^-k+k x⁻¹)) ⟩
    S^ -x⁻¹ • (M (-' (x' ⁻¹)) • H • ε) • H • S^ x • H ≈⟨ (cright cleft (cright right-unit)) ⟩
    S^ -x⁻¹ • (M (-' (x' ⁻¹)) • H) • H • S^ x • H ≈⟨ (cright by-assoc auto) ⟩
    S^ -x⁻¹ • (M (-' (x' ⁻¹)) • H • H) • S^ x • H ≈⟨ (cright cleft cright lemma-HH-M-1) ⟩
    S^ -x⁻¹ • (M (-' (x' ⁻¹)) • M -'₁) • S^ x • H ≈⟨ (cright cleft axiom (M-mul (-' (x' ⁻¹)) -'₁)) ⟩
    S^ -x⁻¹ • M (-' (x' ⁻¹) *' -'₁) • S^ x • H ≈⟨ (cright cleft aux-MM ((-' (x' ⁻¹) *' -'₁) .proj₂) ((x' ⁻¹) .proj₂) aux-a2) ⟩
    S^ -x⁻¹ • M (x' ⁻¹) • S^ x • H ≈⟨ sym (cong refl assoc) ⟩
    S^ -x⁻¹ • (M (x' ⁻¹) • S^ x) • H ≈⟨ (cright cleft lemma-MS^k x⁻¹ x ((x' ⁻¹) .proj₂)) ⟩
    S^ -x⁻¹ • (S^ (x * (x⁻¹ * x⁻¹)) • M (x' ⁻¹)) • H ≈⟨ (cright cleft (cleft refl' (Eq.cong S^ aux-a3))) ⟩
    S^ -x⁻¹ • (S^ x⁻¹ • M (x' ⁻¹)) • H ≈⟨ by-assoc auto ⟩
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


module Lemmas-1 (n : ℕ) where

  open Symplectic-Derived-Gen
  open Symplectic-Derived-GroupLike
  open import Zp.ModularArithmetic

  open PB ((₂₊ n) QRel,_===_) hiding (_===_)
  open PP ((₂₊ n) QRel,_===_)
  open Pattern-Assoc
  open import Data.Nat.DivMod
  open import Data.Fin.Properties


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
