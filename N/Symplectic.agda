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
open import Presentation.Tactics hiding ([_])
open import Data.Nat.Primality



module N.Symplectic (p-2 : ℕ) (p-prime : Prime (2+ p-2))  where

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


module Symplectic where

  
  -- p-1 : ℕ
  -- p-1 = ₁₊ p-2
  -- p : ℕ
  -- p = ₁₊ p-1
  -- ₚ = p
  
  data Gen : ℕ → Set where
    H-gen : ∀ {n} → Gen (₁₊ n)
    S-gen : ∀ {n} → Gen (₁₊ n)
    CZ-gen : ∀ {n} → Gen (₂₊ n)
--    EX-gen : ∀ {n} → Gen (₂₊ n)
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
  _↓-gen {₁₊ n} H-gen = H-gen
  _↓-gen {₁₊ n} S-gen = S-gen
  _↓-gen {₁₊ .(₁₊ _)} CZ-gen = CZ-gen
--  _↓-gen {₁₊ .(₁₊ _)} EX-gen = EX-gen
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
  S = [ S-gen ]ʷ

  S⁻¹ : ∀ {n} → Word (Gen (₁₊ n))
  S⁻¹ = S ^ p-1

  H : ∀ {n} → Word (Gen (₁₊ n))
  H = [ H-gen ]ʷ

  HH : ∀ {n} → Word (Gen (₁₊ n))
  HH = H ^ 2

  H⁻¹ : ∀ {n} → Word (Gen (₁₊ n))
  H⁻¹ = H ^ 3

  CZ : ∀ {n} → Word (Gen (₂₊ n))
  CZ = [ CZ-gen ]ʷ

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

  -- EX : ∀ {n} → Word (Gen (₂₊ n))
  -- EX = [ EX-gen ]ʷ

  ₕ|ₕ : ∀ {n} → Word (Gen (₂₊ n))
  ₕ|ₕ = H ↓ • CZ • H ↓

  ʰ|ʰ : ∀ {n} → Word (Gen (₂₊ n))
  ʰ|ʰ = H ↑ • CZ • H ↑

  ⊥⊤ : ∀ {n} → Word (Gen (₂₊ n))
  ⊥⊤ = ₕ|ₕ • ʰ|ʰ

  ⊤⊥ : ∀ {n} → Word (Gen (₂₊ n))
  ⊤⊥ = ʰ|ʰ • ₕ|ₕ

  H^ : ∀ {n} → ℤ ₄ -> Word (Gen (₁₊ n))
  H^ k = H ^ toℕ k

  S^ : ∀ {n} → ℤ ₚ -> Word (Gen (₁₊ n))
  S^ k = S ^ toℕ k

  CZ^ : ∀ {n} → ℤ ₚ -> Word (Gen (₂₊ n))
  CZ^ k = CZ ^ toℕ k
  
  CX^ : ∀ {n} → ℤ ₚ -> Word (Gen (₂₊ n))
  CX^ k = CX ^ toℕ k

  M : ∀ {n} -> ℤ* ₚ -> Word (Gen (₁₊ n))
  M x' = S^ x • H • S^ x⁻¹ • H • S^ x • H
    where
    x = x' .proj₁
    x⁻¹ = ((x' ⁻¹) .proj₁ )

  M₁ : ∀ {n} -> Word (Gen (₁₊ n))
  M₁ = M ₁ₚ

  CX⁻¹ : ∀ {n} → Word (Gen (₂₊ n))
  CX⁻¹ = H ^ 3 • CZ^ (- ₁) • H

  XC⁻¹ : ∀ {n} → Word (Gen (₂₊ n))
  XC⁻¹ = H ↑ ^ 3 • CZ^ (- ₁) • H ↑


  CZ02 : ∀ {n} → Word (Gen (₃₊ n))
  CZ02 = Ex • CZ ↑ • Ex

  CZ02' : ∀ {n} → Word (Gen (₃₊ n))
  CZ02' = Ex ↑ • CZ • Ex ↑

  CZ02⁻¹ : ∀ {n} → Word (Gen (₃₊ n))
  CZ02⁻¹ = Ex • CZ⁻¹ ↑ • Ex

  CZ02k : ∀ {n} k → Word (Gen (₃₊ n))
  CZ02k k = Ex • CZ ↑ ^ k • Ex

  CZ02'k : ∀ {n} k → Word (Gen (₃₊ n))
  CZ02'k k = Ex ↑ • CZ ^ k • Ex ↑

  CZ02⁻ᵏ : ∀ {n} k → Word (Gen (₃₊ n))
  CZ02⁻ᵏ k = Ex • CZ⁻¹ ↑ ^ k • Ex

  CZ02'⁻ᵏ : ∀ {n} k → Word (Gen (₃₊ n))
  CZ02'⁻ᵏ k = Ex ↑ • CZ⁻¹ ^ k • Ex ↑

  CZ02'⁻¹ : ∀ {n} -> Word (Gen (₃₊ n))
  CZ02'⁻¹ = Ex ↑ • CZ⁻¹ • Ex ↑

  XC02 : ∀ {n} → Word (Gen (₃₊ n))
  XC02 = H ↑ ↑ ^ 3 • CZ02 • H ↑ ↑

  CZ02^ : ∀ {n} (k : ℤ ₚ) → Word (Gen (₃₊ n))
  CZ02^ k = Ex • CZ^ k ↑ • Ex

  CZ02'^ : ∀ {n} (k : ℤ ₚ) → Word (Gen (₃₊ n))
  CZ02'^ k = CZ02 ^ toℕ k

  CX'^ : ∀ {n} → ℤ ₚ -> Word (Gen (₂₊ n))
  CX'^ k = H ^ 3 • CZ^ k • H

  XC^ : ∀ {n} → ℤ ₚ -> Word (Gen (₂₊ n))
  XC^ k = XC ^ toℕ k

  XC'^ : ∀ {n} → ℤ ₚ -> Word (Gen (₂₊ n))
  XC'^ k = H ↑ ^ 3 • CZ^ k • H ↑

  XC02^ : ∀ {n} → ℤ ₚ -> Word (Gen (₃₊ n))
  XC02^ k = H ↑ ↑ ^ 3 • CZ02^ k • H ↑ ↑

  CX02^ : ∀ {n} → ℤ ₚ -> Word (Gen (₃₊ n))
  CX02^ k = H ^ 3 • CZ02^ k • H

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

    -- def-EX :       ∀ {n} → (₂₊ n) QRel,  EX === Ex
    -- order-EX :     ∀ {n} → (₂₊ n) QRel,  EX ^ 2 === ε
    -- comm-EX :   ∀ {n}{g} → (₃₊ n) QRel,  [ g ↥ ↥ ]ʷ • EX === EX • [ g ↥ ↥ ]ʷ

    comm-H :    ∀ {n}{g} → (₂₊ n) QRel,  [ g ↥ ]ʷ • H === H • [ g ↥ ]ʷ
    comm-S :    ∀ {n}{g} → (₂₊ n) QRel,  [ g ↥ ]ʷ • S === S • [ g ↥ ]ʷ
    comm-CZ :   ∀ {n}{g} → (₃₊ n) QRel,  [ g ↥ ↥ ]ʷ • CZ === CZ • [ g ↥ ↥ ]ʷ

    cong↑ : ∀ {n w v} → n QRel,  w === v → (₁₊ n) QRel,  w ↑ === v ↑

module Lemmas-Sym where
  open Symplectic
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


  import Data.Nat.Literals as NL
  open import Agda.Builtin.FromNat
  open import Data.Unit.Base using (⊤)
  open import Data.Fin.Literals
  import Data.Nat.Literals as NL


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
  lemma-cong↓ {n} w v (PB.axiom (M-mul x y)) = begin
    ((M x • M y) ↓) ≈⟨ refl ⟩
    M x ↓ • M y ↓ ≈⟨ cong (lemma-M↓ x) (lemma-M↓ y) ⟩
    M x • M y  ≈⟨ axiom (M-mul x y) ⟩
    M (x *' y)  ≈⟨ sym (lemma-M↓ (x *' y)) ⟩
    (M (x *' y) ↓) ∎
    where
    open PB ((suc n) QRel,_===_) renaming (_≈_ to _≈↓_)
    open PP ((suc n) QRel,_===_)
    open SR word-setoid
  lemma-cong↓ {n} w v (PB.axiom (semi-MS x)) = begin
    ((M x • S) ↓) ≈⟨ (cleft lemma-M↓ x) ⟩
    M x • S ≈⟨ axiom (semi-MS x) ⟩
    S^ (x ^2) • M x ≈⟨ sym (cong (lemma-cong↓-S^ (toℕ (fromℕ< _))) (lemma-M↓ x)) ⟩
    ((S^ (x ^2) • M x) ↓) ∎
    where
    open PB ((suc n) QRel,_===_) renaming (_≈_ to _≈↓_)
    open PP ((suc n) QRel,_===_)
    open SR word-setoid
  lemma-cong↓ {n} w v (PB.axiom (semi-M↑CZ x)) = begin
    (((M x ↑) • CZ) ↓) ≈⟨ cong (lemma-M↑↓ x) refl ⟩
    M x ↑ • CZ ≈⟨ axiom (semi-M↑CZ x) ⟩
    CZ^ (x ^1) • M x ↑ ≈⟨ cong (sym (lemma-cong↓-CZ^ (toℕ (x .proj₁)))) (sym (lemma-M↑↓ x)) ⟩
    ((CZ^ (x ^1) • (M x ↑)) ↓) ∎
    where
    open PB ((suc n) QRel,_===_) renaming (_≈_ to _≈↓_)
    open PP ((suc n) QRel,_===_)
    open SR word-setoid
  lemma-cong↓ {n} w v (PB.axiom (semi-M↓CZ x)) =  begin
    (((M x ↓) • CZ) ↓) ≈⟨ cong (lemma-M↓↓ x) refl ⟩
    M x ↓ • CZ ≈⟨ axiom (semi-M↓CZ x) ⟩
    CZ^ (x ^1) • M x ↓ ≈⟨ cong (sym (lemma-cong↓-CZ^ (toℕ (x .proj₁)))) (sym (lemma-M↓↓ x)) ⟩
    ((CZ^ (x ^1) • (M x ↓)) ↓) ∎
    where
    open PB ((suc n) QRel,_===_) renaming (_≈_ to _≈↓_)
    open PP ((suc n) QRel,_===_)
    open SR word-setoid
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

  instance
    Numℕ' : Number ℕ
    Numℕ' = NL.number 

  instance
    NumFin' : Number (Fin p)
    NumFin' = number p

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


module Symplectic-GroupLike where

  private
    variable
      n : ℕ
    
  open Symplectic
  open Lemmas-Sym

  grouplike : Grouplike (n QRel,_===_)
  grouplike {₁₊ n} (H-gen) = (H ) ^ 3 , claim
    where
    open PB ((₁₊ n) QRel,_===_)
    open PP ((₁₊ n) QRel,_===_)
    open SR word-setoid
    claim : (H ) ^ 3 • H ≈ ε
    claim = begin
      (H) ^ 3 • H ≈⟨ by-assoc auto ⟩
      (H) ^ 4 ≈⟨ axiom order-H ⟩
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

  -- grouplike {₂₊ n} (EX-gen) = EX ,  claim
  --   where
  --   open PB ((₂₊ n) QRel,_===_)
  --   open PP ((₂₊ n) QRel,_===_)
  --   open SR word-setoid
  --   claim : (EX) • EX ≈ ε
  --   claim = axiom order-EX

  grouplike {₂₊ n} (g ↥) with grouplike g
  ... | ig , prf = (ig ↑) , lemma-cong↑ (ig • [ g ]ʷ) ε prf
    where
    open PB ((₂₊ n) QRel,_===_)
    open PP ((₂₊ n) QRel,_===_)


{-
module Symplectic-Derived-Gen where

  -- p-1 : ℕ
  -- p-1 = ₁₊ p-2
  -- p : ℕ
  -- p = ₁₊ p-1
  -- ₚ = p
  
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

  _↓ : ∀ {n} → Word (Gen n) → Word (Gen (suc n))
  _↓ {n} = wmap _↓-gen


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

    -- semi-CZ-HH↓ :  ∀ {n} → (₂₊ n) QRel,  CZ • H ↓ ^ 2 === H ↓ ^ 2 • CZ ^ 2
    -- semi-CZ-HH↑ :  ∀ {n} → (₂₊ n) QRel,  CZ • H ↑ ^ 2 === H ↑ ^ 2 • CZ ^ 2

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
  
  grouplike : Grouplike ((₁₊ n) QRel,_===_)
  grouplike {n} (H-gen k) = (H ^ toℕ k) ^ 3 , claim
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

  grouplike {n} (S-gen k) = (S ^ toℕ k) ^ p-1 ,  claim
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

  grouplike {₁₊ n} (CZ-gen k) = (CZ ^ toℕ k) ^ p-1 ,  claim
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

  grouplike {₁₊ n} (g ↥) with grouplike g
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

module Action where

  open Symplectic-Derived-Gen

  Pauli1 = ℤ ₚ × ℤ ₚ

  Pauli : ℕ → Set
  Pauli n = Vec Pauli1 n

  act1 : ∀ {n} → Gen n → Pauli n → Pauli n
  act1 {₁₊ n} (H-gen ₀) ((a , b) ∷ ps) = ((a , b) ∷ ps)
  act1 {₁₊ n} (H-gen ₁) ((a , b) ∷ ps) = ((- b , a) ∷ ps)
  act1 {₁₊ n} (H-gen ₂) ((a , b) ∷ ps) = ((- a , - b) ∷ ps)
  act1 {₁₊ n} (H-gen ₃) ((a , b) ∷ ps) = ((b , - a) ∷ ps)
  act1 {₁₊ n} (S-gen k) ((a , b) ∷ ps) = ((a , b + a * k) ∷ ps)
  act1 {₂₊ n} (CZ-gen k) ((a , b) ∷ (a' , b') ∷ ps) = (a , b + a' * k) ∷ (a' , b' + a * k) ∷ ps
  act1 {₁₊ n} (g ↥) (p ∷ ps) = p ∷ act1 {n} g ps

  act : ∀ {n} → Word (Gen n) → Pauli n → Pauli n
  act {n} = word-act act1
  -- act {n} ε p = p
  -- act {n} (w • w₁) p = act w (act w₁ p)

  lemma-act-↑ : ∀ {n} (w : Word (Gen n)) → (p : Pauli1 ) (q : Pauli n) → act (w ↑) (p ∷ q) ≡ p ∷ act w q
  lemma-act-↑ {n} [ x ]ʷ p q = auto
  lemma-act-↑ {n} ε p q = auto
  lemma-act-↑ {n} (w • v) p q = begin
    act ((w • v) ↑) (p ∷ q) ≡⟨ auto ⟩
    act (w ↑) (act (v ↑) (p ∷ q)) ≡⟨ Eq.cong (act (w ↑)) (lemma-act-↑ v p q) ⟩
    act (w ↑) (p ∷ act v q) ≡⟨ lemma-act-↑ w p (act v q) ⟩
    p ∷ act w (act v q) ≡⟨ auto ⟩
    p ∷ act (w • v) q ∎
    where open ≡-Reasoning

  cong₃ : ∀ {A B C D : Set}(f : A → B → C → D) {x y u v a b} → x ≡ y → u ≡ v → a ≡ b → f x u a  ≡ f y v b
  cong₃ f Eq.refl Eq.refl Eq.refl = Eq.refl


  lemma-act-↓-gen : ∀ {n} (gen : Gen n) → (p : Pauli1 ) (ps : Pauli n) → act1 (gen ↓-gen) (ps ∷ʳ p) ≡ (act1 gen ps) ∷ʳ p
  lemma-act-↓-gen {₁} (H-gen ₀) p (x ∷ []) = auto
  lemma-act-↓-gen {₁} (H-gen ₁) p (x ∷ []) = auto
  lemma-act-↓-gen {₁} (H-gen ₂) p (x ∷ []) = auto
  lemma-act-↓-gen {₁} (H-gen ₃) p (x ∷ []) = auto
  lemma-act-↓-gen {₁} (S-gen k) p (x ∷ []) = auto
  lemma-act-↓-gen {₂₊ n} (H-gen ₀) p (x ∷ x₁ ∷ ps) = auto
  lemma-act-↓-gen {₂₊ n} (H-gen ₁) p (x ∷ x₁ ∷ ps) = auto
  lemma-act-↓-gen {₂₊ n} (H-gen ₂) p (x ∷ x₁ ∷ ps) = auto
  lemma-act-↓-gen {₂₊ n} (H-gen ₃) p (x ∷ x₁ ∷ ps) = auto
  lemma-act-↓-gen {₂₊ n} (S-gen k) p (x ∷ x₁ ∷ ps) = auto
  lemma-act-↓-gen {₂₊ n} (CZ-gen k) p (x ∷ x₁ ∷ ps) = auto
  lemma-act-↓-gen {₂₊ n} (gen ↥) p (x ∷ x₁ ∷ ps) rewrite lemma-act-↓-gen {₁₊ n} gen p (x₁ ∷ ps) = Eq.cong (x ∷_) auto

  lemma-act-↓ : ∀ {n} (w : Word (Gen n)) → (p : Pauli1 ) (ps : Pauli n) → act (w ↓) (ps ∷ʳ p) ≡ (act w ps) ∷ʳ p
  lemma-act-↓ {₁₊ n} [ x ]ʷ p (x₁ ∷ ps) = lemma-act-↓-gen x p (x₁ ∷ ps)
  lemma-act-↓ {n} ε p ps = auto
  lemma-act-↓ {n} (w • w₁) p ps rewrite lemma-act-↓ w₁ p ps | lemma-act-↓ w p (act w₁ ps) = auto


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
  pX₀ {₁} = pX ∷ []
  pX₀ {₁₊ n} = pX ∷ pIₙ

  pZ₀ : ∀ {n} → Pauli n
  pZ₀ {₀} = []
  pZ₀ {₁} = pZ ∷ []
  pZ₀ {₁₊ n} = pZ ∷ pIₙ

  pX₀Z₀ : ∀ {n} (e : ℤ ₚ) → Pauli n
  pX₀Z₀ {₀} e = []
  pX₀Z₀ {₁} e = (₁ , e) ∷ []
  pX₀Z₀ {₁₊ n} e = (₁ , e) ∷ pIₙ

  pXₙZₙ : ∀ {n} (e : ℤ ₚ) → Pauli n
  pXₙZₙ {₀} e = []
  pXₙZₙ {₁} e = (₁ , e) ∷ []
  pXₙZₙ {₁₊ n} e = pI ∷ pXₙZₙ e

  pXZ : ∀ (e : ℤ ₚ) → Pauli1
  pXZ e = (₁ , e)

  sform1 : Pauli1 → Pauli1 → ℤ ₚ
  sform1 (a , b) (c , d) = (- a) * d + c * b

  sform : ∀ {n} → Pauli n → Pauli n → ℤ ₚ
  sform {₀} [] [] = ₀
  sform {₁₊ n} (x ∷ ps) (y ∷ qs) = sform1 x y + sform ps qs

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
    open import Data.Integer.Tactic.RingSolver
    open ≡-Reasoning

  sform-antisym1 : ∀ (p q : Pauli 1) -> sform p q ≡ - sform q p
  sform-antisym1 p@((a , b) ∷ []) q@((c , d) ∷ []) = begin
    sform1 (a , b) (c , d) + ₀ ≡⟨ +-identityʳ (sform1 (a , b) (c , d)) ⟩
    sform1 (a , b) (c , d) ≡⟨ sform1-antisym (a , b) (c , d) ⟩
    - sform1 (c , d) (a , b) ≡⟨ Eq.cong -_ (Eq.sym (+-identityʳ (sform1 (c , d) (a , b)))) ⟩
    - (sform1 (c , d) (a , b) + ₀) ∎
    where
    open import Data.Integer.Tactic.RingSolver
    open ≡-Reasoning

  0≢1 : 0 ≢ 1
  0≢1 ()

  0≢1+n : ∀ n -> 0 ≢ ₁₊ n
  0≢1+n n ()

-}

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


-}

-- ----------------------------------------------------------------------
-- * Data required for applying word tactics to Symplectic generators

module CommData where
  variable
    n : ℕ

  open Symplectic
  open Lemmas-Sym
  
  
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
--  ord {suc n} (EX-gen) = 3
  ord {suc n} (g ↥) = 4 Nat.+ ord g


  -- Ordering of generators.
  les : Gen (₂₊ n) → Gen (₂₊ n) → Bool
  les x y with ord x Nat.<? ord y
  les x y | yes _ = true
  les x y | no _ = false

module Commuting-Symplectic (n : ℕ) where
  open Symplectic
  open CommData hiding (n)
  open Commuting (((₂₊ n) QRel,_===_) ) commute les public

module Lemmas00 where

  variable
    n : ℕ

  -- open Lemmas hiding (n)
  -- open Lemmas2 hiding (n)
  -- open Lemmas3 hiding (n)
  open Symplectic
  open import Zp.ModularArithmetic
  open Rewriting

  -- lemma-semi-CZ-HH↓ : let open PB ((₂₊ n) QRel,_===_) in

  --   CZ • H ↓ ^ 2 ≈ H ↓ ^ 2 • CZ^ ₋₁
    
  -- lemma-semi-CZ-HH↓ = {!!}
    


module Rewriting-Sym0 where

  -- This module provides a complete rewrite system for 1-qubit
  -- Swap operators. It is specialized toward relations on qubit 0
  -- (but can also be applied to qubit 1 via duality).
  variable
    n : ℕ

  open Symplectic
  open Rewriting
  
  
  step-sym0 : let open PB ((₁₊ n) QRel,_===_) hiding (_===_) in Step-Function (Gen (₁₊ n))  ((₁₊ n) QRel,_===_)

  -- Order of generators.
  -- step-sym0 ((S-gen) ∷ (S-gen) ∷ (S-gen) ∷ xs) = just (xs , at-head (PB.axiom order-S))
  -- step-sym0 ((S-gen ↥) ∷ (S-gen ↥) ∷ (S-gen ↥) ∷ xs) = just (xs , at-head (PB.axiom (cong↑ order-S)))
  -- step-sym0 ((S-gen ↥ ↥) ∷ (S-gen ↥ ↥) ∷ (S-gen ↥ ↥) ∷ xs) = just (xs , at-head (PB.axiom (cong↑ (cong↑ order-S))))
  step-sym0 ((H-gen) ∷ (H-gen) ∷ (H-gen) ∷ (H-gen) ∷ xs) = just (xs , at-head (PB.axiom order-H))
  step-sym0 ((H-gen ↥) ∷ (H-gen ↥) ∷ (H-gen ↥) ∷ (H-gen ↥) ∷ xs) = just (xs , at-head (PB.axiom (cong↑ order-H)))
  step-sym0 ((H-gen ↥ ↥) ∷ (H-gen ↥ ↥) ∷ (H-gen ↥ ↥) ∷ (H-gen ↥ ↥) ∷ xs) = just (xs , at-head (PB.axiom (cong↑ (cong↑ order-H))))
  -- step-sym0 ((CZ-gen) ∷ (CZ-gen) ∷ (CZ-gen) ∷ xs) = just (xs , at-head (PB.axiom order-CZ))
  -- step-sym0 ((CZ-gen ↥) ∷ (CZ-gen ↥) ∷ (CZ-gen ↥) ∷ xs) = just (xs , at-head (PB.axiom (cong↑ order-CZ)))

  step-sym0 ((S-gen) ∷ (H-gen) ∷ (S-gen) ∷ (H-gen) ∷ (S-gen) ∷ (H-gen) ∷ xs) = just (xs , at-head (PB.axiom order-SH))
  step-sym0 ((S-gen ↥) ∷ (H-gen ↥) ∷ (S-gen ↥) ∷ (H-gen ↥) ∷ (S-gen ↥) ∷ (H-gen ↥) ∷ xs) = just (xs , at-head (PB.axiom (cong↑ order-SH)))
  step-sym0 ((S-gen ↥ ↥) ∷ (H-gen ↥ ↥) ∷ (S-gen ↥ ↥) ∷ (H-gen ↥ ↥) ∷ (S-gen ↥ ↥) ∷ (H-gen ↥ ↥) ∷ xs) = just (xs , at-head (PB.axiom (cong↑ (cong↑ order-SH))))

--  step-sym0 (CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ xs) = just (xs , at-head (PB.axiom order-Ex))
--  step-sym0 (CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ xs) = just (xs , at-head (PB.axiom (cong↑ order-Ex)))

  -- Commuting of generators.
  step-sym0 ((S-gen) ∷ (CZ-gen) ∷ xs) = just ((CZ-gen) ∷ (S-gen) ∷ xs , at-head (PB.sym (PB.axiom comm-CZ-S↓)))
  step-sym0 ((S-gen ↥) ∷ (CZ-gen) ∷ xs) = just ((CZ-gen) ∷ (S-gen ↥) ∷ xs , at-head (PB.sym (PB.axiom comm-CZ-S↑)))
  step-sym0 ((S-gen ↥) ∷ (CZ-gen ↥) ∷ xs) = just ((CZ-gen ↥) ∷ (S-gen ↥) ∷ xs , at-head (PB.sym (PB.axiom (cong↑ comm-CZ-S↓))))
  step-sym0 ((S-gen ↥ ↥) ∷ (CZ-gen ↥) ∷ xs) = just ((CZ-gen ↥) ∷ (S-gen ↥ ↥) ∷ xs , at-head (PB.sym (PB.axiom (cong↑ comm-CZ-S↑))))

  step-sym0 ((H-gen ↥ ↥) ∷ (CZ-gen) ∷ xs) = just ((CZ-gen) ∷ (H-gen ↥ ↥) ∷ xs , at-head (PB.axiom comm-CZ))
  step-sym0 ((S-gen ↥ ↥) ∷ (CZ-gen) ∷ xs) = just ((CZ-gen) ∷ (S-gen ↥ ↥) ∷ xs , at-head (PB.axiom comm-CZ))

  -- step-sym0 ((EX-gen ↥ ↥) ∷ (CZ-gen) ∷ xs) = just ((CZ-gen) ∷ (EX-gen ↥ ↥) ∷ xs , at-head (PB.axiom comm-CZ))
  -- step-sym0 ((EX-gen ↥) ∷ (H-gen) ∷ xs) = just ((H-gen) ∷ (EX-gen ↥) ∷ xs , at-head (PB.axiom comm-H))
  -- step-sym0 ((EX-gen ↥) ∷ (S-gen) ∷ xs) = just ((S-gen) ∷ (EX-gen ↥) ∷ xs , at-head (PB.axiom comm-S))
  -- step-sym0 ((EX-gen ↥ ↥) ∷ (H-gen) ∷ xs) = just ((H-gen) ∷ (EX-gen ↥ ↥) ∷ xs , at-head (PB.axiom comm-H))
  -- step-sym0 ((EX-gen ↥ ↥) ∷ (S-gen) ∷ xs) = just ((S-gen) ∷ (EX-gen ↥ ↥) ∷ xs , at-head (PB.axiom comm-S))
  -- step-sym0 ((EX-gen ↥ ↥) ∷ (S-gen ↥) ∷ xs) = just ((S-gen ↥) ∷ (EX-gen ↥ ↥) ∷ xs , at-head ((PB.axiom (cong↑ comm-S))))
  -- step-sym0 ((EX-gen ↥ ↥) ∷ (H-gen ↥) ∷ xs) = just ((H-gen ↥) ∷ (EX-gen ↥ ↥) ∷ xs , at-head ((PB.axiom (cong↑ comm-H))))
  -- step-sym0 ((EX-gen ↥ ↥ ↥) ∷ (CZ-gen ↥) ∷ xs) = just ((CZ-gen ↥) ∷ (EX-gen ↥ ↥ ↥) ∷ xs , at-head ((PB.axiom (cong↑ comm-CZ))))
  -- step-sym0 ((H-gen ↥ ↥) ∷ (EX-gen) ∷ xs) = just ((EX-gen) ∷ (H-gen ↥ ↥) ∷ xs , at-head (PB.axiom comm-EX))
  -- step-sym0 ((S-gen ↥ ↥) ∷ (EX-gen) ∷ xs) = just ((EX-gen) ∷ (S-gen ↥ ↥) ∷ xs , at-head (PB.axiom comm-EX))
  -- step-sym0 ((CZ-gen ↥ ↥) ∷ (EX-gen) ∷ xs) = just ((EX-gen) ∷ (CZ-gen ↥ ↥) ∷ xs , at-head (PB.axiom comm-EX))

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

  step-sym0 ((S-gen) ∷ (H-gen) ∷ (H-gen) ∷ xs) = just ((H-gen) ∷ (H-gen) ∷ (S-gen) ∷ xs , at-head (PB.sym (PB.axiom comm-HHS)))
  step-sym0 ((S-gen ↥) ∷ (H-gen ↥) ∷ (H-gen ↥) ∷ xs) = just ((H-gen ↥) ∷ (H-gen ↥) ∷ (S-gen ↥) ∷ xs , at-head (PB.sym (PB.axiom (cong↑ comm-HHS))))
  step-sym0 ((S-gen ↥ ↥) ∷ (H-gen ↥ ↥) ∷ (H-gen ↥ ↥) ∷ xs) = just ((H-gen ↥ ↥) ∷ (H-gen ↥ ↥) ∷ (S-gen ↥ ↥) ∷ xs , at-head (PB.sym (PB.axiom (cong↑ (cong↑ comm-HHS)))))

  -- Others.
--  step-sym0 ((CZ-gen) ∷ (H-gen) ∷ (H-gen) ∷ xs) = just ((H-gen) ∷ (H-gen) ∷ (CZ-gen) ∷ (CZ-gen) ∷ xs , at-head (PB.axiom semi-CZ-HH↓))
--  step-sym0 ((CZ-gen) ∷ (H-gen ↥) ∷ (H-gen ↥) ∷ xs) = just ((H-gen ↥) ∷ (H-gen ↥) ∷ (CZ-gen) ∷ (CZ-gen) ∷ xs , at-head (PB.axiom semi-CZ-HH↑))

  -- step-sym0 ((CZ-gen) ∷ (H-gen) ∷ (CZ-gen) ∷ xs) = just ((S-gen) ∷ (S-gen) ∷ H-gen ∷ (S-gen) ∷ (S-gen) ∷ CZ-gen ∷ H-gen ∷ S-gen ∷ S-gen ∷ S-gen ↥ ∷ S-gen ↥ ∷ xs , at-head (PB.axiom selinger-c11 ))
  -- step-sym0 ((CZ-gen ↥) ∷ (H-gen ↥) ∷ (CZ-gen ↥) ∷ xs) = just ((S-gen ↥) ∷ (S-gen ↥) ∷ H-gen ↥ ∷ (S-gen ↥) ∷ (S-gen ↥) ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ S-gen ↥ ∷ S-gen ↥ ∷ S-gen ↥ ↥ ∷ S-gen ↥ ↥ ∷ xs , at-head (PB.axiom (cong↑ selinger-c11 )))
  -- step-sym0 ((CZ-gen) ∷ (H-gen ↥) ∷ (CZ-gen) ∷ xs) = just ((S-gen ↥) ∷ (S-gen ↥) ∷ H-gen ↥ ∷ (S-gen ↥) ∷ (S-gen ↥) ∷ CZ-gen ∷ H-gen ↥ ∷ S-gen ↥ ∷ S-gen ↥ ∷ S-gen ∷ S-gen ∷ xs , at-head (PB.axiom selinger-c10 ))
  -- step-sym0 ((CZ-gen ↥) ∷ (H-gen ↥ ↥) ∷ (CZ-gen ↥) ∷ xs) = just ((S-gen ↥ ↥) ∷ (S-gen ↥ ↥) ∷ H-gen ↥ ↥ ∷ (S-gen ↥ ↥) ∷ (S-gen ↥ ↥) ∷ CZ-gen ↥ ∷ H-gen ↥ ↥ ∷ S-gen ↥ ↥ ∷ S-gen ↥ ↥ ∷ S-gen ↥ ∷ S-gen ↥ ∷ xs , at-head (PB.axiom (cong↑ selinger-c10 )))

  -- Catch-all
  step-sym0 _ = nothing

module Sym0-Rewriting (n : ℕ) where
  open Symplectic
  open Rewriting
  open Rewriting-Sym0 hiding (n)
  open Rewriting.Step (step-cong (step-sym0 {n})) renaming (general-rewrite to rewrite-sym0) public



module Lemmas0 (n : ℕ) where

  open Symplectic
--  open Symplectic-GroupLike
  open import Zp.ModularArithmetic

  open PB ((₁₊ n) QRel,_===_) hiding (_===_)
  open PP ((₁₊ n) QRel,_===_)
  open Pattern-Assoc
  open import Data.Nat.DivMod
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
    (H⁻¹ • S⁻¹) ^ 3 ≈⟨ sym left-unit ⟩
    ε • (H⁻¹ • S⁻¹) ^ 3 ≈⟨ (cleft rewrite-sym0 100 auto) ⟩
    (S • H) ^ 3 • (H⁻¹ • S⁻¹) ^ 3 ≈⟨ rewrite-sym0 100 auto ⟩
    ((S • H • S • H • S) • (H • H⁻¹)) • S⁻¹ • (H⁻¹ • S⁻¹) • (H⁻¹ • S⁻¹) ≈⟨ ( cleft trans (cright axiom order-H) (by-assoc auto)) ⟩
    ((S • H • S • H) • S) • S⁻¹ • (H⁻¹ • S⁻¹) • (H⁻¹ • S⁻¹) ≈⟨ by-assoc auto ⟩
    (S • H • S • H) • (S • S⁻¹) • (H⁻¹ • S⁻¹) • (H⁻¹ • S⁻¹) ≈⟨ (cright cleft axiom order-S) ⟩
    (S • H • S • H) • ε • (H⁻¹ • S⁻¹) • (H⁻¹ • S⁻¹) ≈⟨ by-assoc auto ⟩
    (S • H • S • H • H⁻¹) • S⁻¹ • (H⁻¹ • S⁻¹) ≈⟨ (cleft cright cright cright axiom order-H) ⟩
    (S • H • S • ε) • S⁻¹ • (H⁻¹ • S⁻¹) ≈⟨ by-assoc auto ⟩
    (S • H • S • S⁻¹) • (H⁻¹ • S⁻¹) ≈⟨ (cleft cright cright axiom order-S) ⟩
    (S • H • ε) • (H⁻¹ • S⁻¹) ≈⟨ by-assoc auto ⟩
    (S • H • H⁻¹) • S⁻¹ ≈⟨ (cleft cright axiom order-H) ⟩
    (S • ε) • S⁻¹ ≈⟨ by-assoc auto ⟩
    S • S⁻¹ ≈⟨ axiom order-S ⟩
    ε ∎
    where
    open SR word-setoid
    open Sym0-Rewriting n


  lemma-[S⁻¹H⁻¹]^3 : (S⁻¹ • H⁻¹) ^ 3 ≈ ε
  lemma-[S⁻¹H⁻¹]^3 = begin
    (S⁻¹ • H⁻¹) ^ 3 ≈⟨ sym (trans (cright trans (word-comm p-1 1 refl) (axiom order-S)) right-unit) ⟩
    (S⁻¹ • H⁻¹) ^ 3 • (S⁻¹ • S) ≈⟨ special-assoc ((□ • □) ^ 3 • □ • □) (□ • (□ • □) ^ 3 • □) auto ⟩
    S⁻¹ • (H⁻¹ • S⁻¹) ^ 3 • S ≈⟨ cright cleft lemma-[H⁻¹S⁻¹]^3 ⟩
    S⁻¹ • ε • S ≈⟨ by-assoc auto ⟩
    S⁻¹ • S ≈⟨ word-comm p-1 1 refl ⟩
    S • S⁻¹ ≈⟨ axiom order-S ⟩
    ε ∎
    where
--    open Group-Lemmas _ _ grouplike renaming (_⁻¹ to winv)
    open SR word-setoid

  lemma-S⁻¹ : S⁻¹ ≈ S^ ₚ₋₁
  lemma-S⁻¹ = begin
    S⁻¹ ≈⟨ refl ⟩
    S ^ p-1 ≡⟨ Eq.cong (S ^_) (Eq.sym lemma-toℕ-ₚ₋₁) ⟩
    S ^ toℕ ₚ₋₁ ≡⟨ Eq.refl ⟩
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
    HH • ((HH • S⁻¹) • H) • (S⁻¹ • H) • S⁻¹ • HH • H • HH ≈⟨ (cright cright cright cright rewrite-sym0 100 auto) ⟩
    HH • ((HH • S⁻¹) • H) • (S⁻¹ • H) • S⁻¹ • H ≈⟨ special-assoc (□ • (□ ^ 2 • □) • □) (□ ^ 2 • □ ^ 2 • □) auto ⟩
    (HH • HH) • (S⁻¹ • H) • (S⁻¹ • H) • S⁻¹ • H ≈⟨ (cleft rewrite-sym0 100 auto) ⟩
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
    open Sym0-Rewriting n


    x' = -'₁
    -₁ = -'₁ .proj₁
    -₁⁻¹ = (-'₁ ⁻¹) .proj₁
    x = x' .proj₁
    x⁻¹ = (x' ⁻¹) .proj₁
    open SR word-setoid


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


  lemma-M-power : ∀ (x : ℤ* ₚ) k -> let x' = x .proj₁ in  M x ^ k ≈ M (x ^' k)
  lemma-M-power x k@0 = lemma-M1 
  lemma-M-power x k@1 = begin
    M x ^ 1 ≡⟨ aux-M≡M x (x ^' 1) (Eq.sym (lemma-x^′1=x (x .proj₁))) ⟩
    M (x ^' 1) ∎
    where
    open SR word-setoid
  lemma-M-power x k@(₂₊ k') = begin
    M x • M x ^ ₁₊ k' ≈⟨ (cright lemma-M-power x (₁₊ k')) ⟩
    M x • M (x ^' ₁₊ k') ≈⟨ axiom (M-mul x (x ^' ₁₊ k')) ⟩
    M (x *' (x ^' ₁₊ k')) ≡⟨ aux-M≡M (x *' (x ^' ₁₊ k')) (x ^' ₂₊ k') auto ⟩
    M (x ^' ₂₊ k') ∎
    where
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
    S^ (x * x) • M (x , nz) ≈⟨ refl ⟩
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
    M (x , nz) • S^ k ≈⟨ refl ⟩
    M (x , nz) • S ^ toℕ k ≈⟨ derived-5 x (toℕ k) nz ⟩
    S ^ (toℕ k Nat.* toℕ (x * x)) • M (x , nz) ≈⟨ (cleft lemma-S^k-% (toℕ k Nat.* toℕ (x * x))) ⟩
    S ^ ((toℕ k Nat.* toℕ (x * x)) % p) • M (x , nz) ≈⟨ (cleft refl' (Eq.cong (S ^_) (lemma-toℕ-% k (x * x)))) ⟩
    S ^ toℕ (k * (x * x)) • M (x , nz) ≈⟨ refl ⟩
    S^ (k * (x * x)) • M (x , nz) ∎
    where
    open SR word-setoid
    x⁻¹ = ((x , nz) ⁻¹) .proj₁
    -x⁻¹ = - x⁻¹

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
    S ^ (toℕ -x⁻¹ Nat.* toℕ (y * y)) • (M (y , nzy) • M ((x , nz) ⁻¹)) • H ^ 3 • S^ -x⁻¹ ≈⟨ (cright cleft axiom (M-mul (y , nzy) ((x , nz) ⁻¹))) ⟩
    S ^ (toℕ -x⁻¹ Nat.* toℕ (y * y)) • M ((y , nzy) *' ((x , nz) ⁻¹)) • H ^ 3 • S^ -x⁻¹ ≈⟨ (cright special-assoc (□ • □ ^ 3 • □) (□ ^ 3 • □ ^ 2) auto) ⟩
    S ^ (toℕ -x⁻¹ Nat.* toℕ (y * y)) • (M ((y , nzy) *' ((x , nz) ⁻¹)) • HH) • H • S^ -x⁻¹ ≈⟨ (cright cleft (cright lemma-HH-M-1)) ⟩
    S ^ (toℕ -x⁻¹ Nat.* toℕ (y * y)) • (M ((y , nzy) *' ((x , nz) ⁻¹)) • M -'₁) • H • S^ -x⁻¹ ≈⟨ (cright cleft axiom (M-mul (((y , nzy) *' ((x , nz) ⁻¹))) -'₁)) ⟩
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
    M m • M (m ⁻¹) ≈⟨ axiom (M-mul m ( m ⁻¹)) ⟩
    M (m *' m ⁻¹) ≈⟨ aux-MM ((m *' m ⁻¹) .proj₂) (λ ()) (lemma-⁻¹ʳ (m ^1) {{nztoℕ {y = m ^1} {neq0 = m .proj₂}}}) ⟩
    M₁ ≈⟨ sym lemma-M1 ⟩
    ε ∎
    where
    open SR word-setoid

  aux-M-mulˡ : ∀ m -> M (m ⁻¹) • M m ≈ ε
  aux-M-mulˡ m = begin
    M (m ⁻¹) • M m ≈⟨ axiom (M-mul ( m ⁻¹) m) ⟩
    M (m ⁻¹ *' m) ≈⟨ aux-MM ((m ⁻¹ *' m) .proj₂) (λ ()) (lemma-⁻¹ˡ (m ^1) {{nztoℕ {y = m ^1} {neq0 = m .proj₂}}}) ⟩
    M₁ ≈⟨ sym lemma-M1 ⟩
    ε ∎
    where
    open SR word-setoid



  semi-HM : ∀ (x : ℤ* ₚ) -> H • M x ≈ M (x ⁻¹) • H
  semi-HM x' = begin
    H • (S^ x • H • S^ x⁻¹ • H • S^ x • H) ≈⟨ special-assoc (□ • □ ^ 6) (□ ^ 3 • □ ^ 4) auto ⟩
    (H • S^ x • H) • S^ x⁻¹ • H • S^ x • H ≈⟨ (trans (sym left-unit) (cong lemma-M1 refl)) ⟩
    M₁ • (H • S^ x • H) • S^ x⁻¹ • H • S^ x • H ≈⟨ sym assoc ⟩
    (M₁ • (H • S^ x • H)) • S^ x⁻¹ • H • S^ x • H ≈⟨ (cleft derived-7 x ₁ (x' .proj₂) λ ()) ⟩
    (S^ (-x⁻¹ * (₁ * ₁)) • M (((₁ , λ ()) *' x' ⁻¹) *' -'₁) • H • S^ -x⁻¹) • S^ x⁻¹ • H • S^ x • H ≈⟨ cleft (cright (cleft aux-MM ((((₁ , λ ()) *' x' ⁻¹) *' -'₁) .proj₂) ((-' (x' ⁻¹)) .proj₂) aux-a1)) ⟩
    (S^ (-x⁻¹ * ₁) • M (-' (x' ⁻¹)) • H • S^ -x⁻¹) • S^ x⁻¹ • H • S^ x • H ≈⟨ special-assoc (□ ^ 4 • □ ^ 4) (□ • □ ^ 4 • □ ^ 3) auto ⟩
    S^ (-x⁻¹ * ₁) • (M (-' (x' ⁻¹)) • H • S^ -x⁻¹ • S^ x⁻¹) • H • S^ x • H ≈⟨ cong (refl' (Eq.cong S^ (*-identityʳ -x⁻¹))) (cleft cright (cright lemma-S^-k+k x⁻¹)) ⟩
    S^ -x⁻¹ • (M (-' (x' ⁻¹)) • H • ε) • H • S^ x • H ≈⟨ (cright cleft (cright right-unit)) ⟩
    S^ -x⁻¹ • (M (-' (x' ⁻¹)) • H) • H • S^ x • H ≈⟨ (cright special-assoc (□ ^ 2 • □ ^ 3) (□ ^ 3 • □ ^ 2) auto) ⟩
    S^ -x⁻¹ • (M (-' (x' ⁻¹)) • H • H) • S^ x • H ≈⟨ (cright cleft cright lemma-HH-M-1) ⟩
    S^ -x⁻¹ • (M (-' (x' ⁻¹)) • M -'₁) • S^ x • H ≈⟨ (cright cleft axiom (M-mul (-' (x' ⁻¹)) -'₁)) ⟩
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
    M m • M m' ≈⟨ axiom (M-mul m m') ⟩
    M (m *' m') ≈⟨ aux-MM ((m *' m') .proj₂) ((m' *' m) .proj₂) (*-comm (m .proj₁) (m' .proj₁)) ⟩
    M (m' *' m) ≈⟨ sym (axiom (M-mul m' m)) ⟩
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
  lemma-S^kM x k nz = begin
    S^ k • M (x , nz) ≈⟨ sym (trans left-unit (cong refl right-unit)) ⟩
    ε • S^ k • M (x , nz) • ε ≈⟨ cong (sym (aux-M-mul (x , nz))) (cright cright sym (aux-M-mulˡ (x , nz))) ⟩
    (M ((x , nz)) • M ((x , nz) ⁻¹) ) • S^ k • M (x , nz) • (M ((x , nz) ⁻¹) • M ((x , nz)))  ≈⟨ special-assoc (□ ^ 2 • □ • □ • □ ^ 2) (□ • (□ • □ ^ 2 • □) • □) auto ⟩
    M ((x , nz)) • (M ((x , nz) ⁻¹)  • (S^ k • M (x , nz)) • M ((x , nz) ⁻¹)) • M ((x , nz))  ≈⟨ (cright cleft aux) ⟩
    M ((x , nz)) • (M ((x , nz) ⁻¹) • (M (x , nz) • S^ (k * x⁻²)) • M ((x , nz) ⁻¹)) • M ((x , nz))  ≈⟨ sym (special-assoc (□ ^ 2 • □ ^ 2 • □ ^ 2) (□ • (□ • □ ^ 2 • □) • □) auto) ⟩
    (M ((x , nz)) • M ((x , nz) ⁻¹)) • (M (x , nz) • S^ (k * x⁻²)) • (M ((x , nz) ⁻¹) • M ((x , nz)))  ≈⟨ cong (aux-M-mul (x , nz)) (cright aux-M-mulˡ (x , nz)) ⟩
    ε • (M (x , nz) • S^ (k * x⁻²)) • ε  ≈⟨ trans left-unit right-unit ⟩
    M (x , nz) • S^ (k * x⁻²) ∎
    where
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
  open Symplectic
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
    (H⁻¹ • S⁻¹) ^' 3 ≈⟨ lemma-cong-inv (axiom order-SH) ⟩
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


-}    

{-
  lemma-S↓HCZH : let open PB ((₂₊ n) QRel,_===_) in
    S • H • CZ • H ≈ H • CZ • H • CZ • S ↑ • S
  lemma-S↓HCZH {n} = sym (begin
    H • CZ • H • CZ • S ↑ • S ≈⟨ by-assoc auto ⟩
    H • (CZ • H • CZ) • S ↑ • S ≈⟨ (cright (cleft axiom {!!})) ⟩
    H • (S ↓ ^ 2 • H ↓ • S ↓ ^ 2 • CZ • H ↓ • S ↓ ^ 2 • S ↑ ^ 2) • S ↑ • S ≈⟨ general-powers0 100 {!!} ⟩
    (H • S ↓ ^ 2 • H ↓) • S ↓ ^ 2 • CZ • H ↓ ≈⟨ (cleft {!!}) ⟩
    (S • H • S) • S ↓ ^ 2 • CZ • H ↓ ≈⟨ general-powers0 100 {!!} ⟩
    S • H • CZ • H ∎)
    where
    open PB ((₂₊ n) QRel,_===_)
    open PP ((₂₊ n) QRel,_===_)
    open SR word-setoid
    open Powers0-Symplectic (suc n)
    open Commuting-Symplectic (n)


  lemma-comm-Ex-S↑↑ : let open PB ((₃₊ n) QRel,_===_) in
    Ex • S ↑ ↑ ≈ S ↑ ↑ • Ex
  lemma-comm-Ex-S↑↑ {n} = general-comm auto
    where
    open PB ((₂₊ n) QRel,_===_)
    open PP ((₂₊ n) QRel,_===_)
    open SR word-setoid
    open Powers0-Symplectic (suc n)
    open Commuting-Symplectic (suc n)

  lemma-comm-Ex↑-S : let open PB ((₃₊ n) QRel,_===_) in
    Ex ↑ • S ≈ S • Ex ↑
  lemma-comm-Ex↑-S {n} = general-comm auto
    where
    open PB ((₂₊ n) QRel,_===_)
    open PP ((₂₊ n) QRel,_===_)
    open SR word-setoid
    open Powers0-Symplectic (suc n)
    open Commuting-Symplectic (suc n)

  lemma-comm-Ex-H↑↑ : let open PB ((₃₊ n) QRel,_===_) in
    Ex • H ↑ ↑ ≈ H ↑ ↑ • Ex
  lemma-comm-Ex-H↑↑ {n} = general-comm auto
    where
    open PB ((₂₊ n) QRel,_===_)
    open PP ((₂₊ n) QRel,_===_)
    open Commuting-Symplectic (suc n)

  lemma-comm-Ex↑-H : let open PB ((₃₊ n) QRel,_===_) in
    Ex ↑ • H ≈ H • Ex ↑
  lemma-comm-Ex↑-H {n} = general-comm auto
    where
    open PB ((₂₊ n) QRel,_===_)
    open PP ((₂₊ n) QRel,_===_)
    open Commuting-Symplectic (suc n)




  lemma-S↑H↑CZ↑H : let open PB ((₂₊ n) QRel,_===_) in
    S ↑ • H ↑ • CZ • H ↑ ≈ H ↑ • CZ • H ↑ • CZ • S ↓ • S ↑
  lemma-S↑H↑CZ↑H {n} = sym (begin
    H ↑ • CZ • H ↑ • CZ • S ↓ • S ↑ ≈⟨ by-assoc auto ⟩
    H ↑ • (CZ • H ↑ • CZ) • S ↓ • S ↑ ≈⟨ (cright ( cleft axiom selinger-c10 )) ⟩
    H ↑ • (S ↑ ^ 2 • H ↑ • S ↑ ^ 2 • CZ • H ↑ • S ↑ ^ 2 • S ↓ ^ 2) • S ↓ • S ↑ ≈⟨ general-powers0 100 auto ⟩
    (H ↑ • S ↑ ^ 2 • H ↑) • S ↑ ^ 2 • CZ • H ↑ ≈⟨ (cleft lemma-cong↑ _ _ lemma-HSSH) ⟩
    (S ↑ • H ↑ • S ↑) • S ↑ ^ 2 • CZ • H ↑ ≈⟨ general-powers0 100 auto ⟩
    S ↑ • H ↑ • CZ • H ↑ ∎)
    where
    open PB ((₂₊ n) QRel,_===_)
    open PP ((₂₊ n) QRel,_===_)
    open SR word-setoid
    open Powers0-Symplectic (suc n)
    open Commuting-Symplectic (n)


  lemma-S↑²H↑CZ↑H : let open PB ((₂₊ n) QRel,_===_) in
    S ↑ ^ 2 • H ↑ • CZ • H ↑ ≈ H ↑ • CZ • H ↑ • CZ ^ 2 • S ↓ ^ 2 • S ↑ ^ 2
  lemma-S↑²H↑CZ↑H {n@(₀)} = begin
    S ↑ ^ 2 • H ↑ • CZ • H ↑ ≈⟨ assoc ⟩
    S ↑ • S ↑ • H ↑ • CZ • H ↑ ≈⟨ (cright lemma-S↑H↑CZ↑H) ⟩
    S ↑ • H ↑ • CZ • H ↑ • CZ • S ↓ • S ↑ ≈⟨ by-assoc auto ⟩
    (S ↑ • H ↑ • CZ • H ↑) • CZ • S ↓ • S ↑ ≈⟨ (cleft lemma-S↑H↑CZ↑H) ⟩
    (H ↑ • CZ • H ↑ • CZ • S ↓ • S ↑) • CZ • S ↓ • S ↑ ≈⟨ by-assoc auto ⟩
    (H ↑ • CZ • H ↑) • CZ • S  • S ↑ • CZ • S  • S ↑ ≈⟨ ( general-comm auto) ⟩
    H ↑ • CZ • H ↑ • CZ ^ 2 • S ↓ ^ 2 • S ↑ ^ 2 ∎
    where
    open PB ((₂₊ n) QRel,_===_)
    open PP ((₂₊ n) QRel,_===_)
    open SR word-setoid
    open Powers0-Symplectic (suc n)
    open Commuting-Symplectic (n)
  lemma-S↑²H↑CZ↑H {n@(suc n')} = begin
    S ↑ ^ 2 • H ↑ • CZ • H ↑ ≈⟨ assoc ⟩
    S ↑ • S ↑ • H ↑ • CZ • H ↑ ≈⟨ (cright lemma-S↑H↑CZ↑H) ⟩
    S ↑ • H ↑ • CZ • H ↑ • CZ • S ↓ • S ↑ ≈⟨ by-assoc auto ⟩
    (S ↑ • H ↑ • CZ • H ↑) • CZ • S ↓ • S ↑ ≈⟨ (cleft lemma-S↑H↑CZ↑H) ⟩
    (H ↑ • CZ • H ↑ • CZ • S ↓ • S ↑) • CZ • S ↓ • S ↑ ≈⟨ by-assoc auto ⟩
    (H ↑ • CZ • H ↑) • CZ • S  • S ↑ • CZ • S  • S ↑ ≈⟨ ( general-comm auto) ⟩
    H ↑ • CZ • H ↑ • CZ ^ 2 • S ↓ ^ 2 • S ↑ ^ 2 ∎
    where
    open PB ((₂₊ n) QRel,_===_)
    open PP ((₂₊ n) QRel,_===_)
    open SR word-setoid
    open Powers0-Symplectic (suc n)
    open Commuting-Symplectic (n)



  lemma-H↑CZ↑HS↑ : let open PB ((₂₊ n) QRel,_===_) in
    S ↑ • S ↓ • CZ • H ↑ • CZ • H ↑ ≈ H ↑ • CZ • H ↑ • S ↑
  lemma-H↑CZ↑HS↑ {n} = begin
    S ↑ • S ↓ • CZ • H ↑ • CZ • H ↑ ≈⟨ general-comm auto ⟩
    S ↑ • (CZ • H ↑ • CZ) • H ↑ • S ↓ ≈⟨ (cright (cleft axiom selinger-c10)) ⟩
    S ↑ • (S ↑ ^ 2 • H ↑ • S ↑ ^ 2 • CZ • H ↑ • S ↑ ^ 2 • S ↓ ^ 2) • H ↑ • S ↓ ≈⟨ rewrite-sym0 100 auto ⟩
    (H ↑ • CZ • S ↑ ^ 2) • (H ↑ • S ↑ ^ 2 • H ↑) ≈⟨ (cright lemma-cong↑ _ _ lemma-HSSH) ⟩
    (H ↑ • CZ • S ↑ ^ 2) • (S • H • S) ↑ ≈⟨ general-powers0 100 auto ⟩
    H ↑ • CZ • H ↑ • S ↑ ∎
    where
    open PB ((₂₊ n) QRel,_===_)
    open PP ((₂₊ n) QRel,_===_)
    open SR word-setoid
    open Powers0-Symplectic (suc n)
    open Sym0-Rewriting (suc n)    
    open Commuting-Symplectic (n)

  lemma-H↑CZ↑HS↑S↑ : let open PB ((₂₊ n) QRel,_===_) in
    S ↑ ^ 2 • S ↓ ^ 2 • CZ ^ 2 • H ↑ • CZ • H ↑ ≈ H ↑ • CZ • H ↑ • S ↑ ^ 2
  lemma-H↑CZ↑HS↑S↑ {n} = begin
    S ↑ ^ 2 • S ↓ ^ 2 • CZ ^ 2 • H ↑ • CZ • H ↑ ≈⟨ rewrite-sym0 100 auto ⟩
    (S ↑ • S ↓ • CZ) • (S ↑ • S ↓ • CZ • H ↑ • CZ • H ↑) ≈⟨ ( cright lemma-H↑CZ↑HS↑) ⟩
    (S ↑ • S ↓ • CZ) • (H ↑ • CZ • H ↑ • S ↑) ≈⟨ by-assoc auto ⟩
    (S ↑ • S ↓ • CZ • H ↑ • CZ • H ↑) • S ↑ ≈⟨ (cleft lemma-H↑CZ↑HS↑) ⟩
    (H ↑ • CZ • H ↑ • S ↑) • S ↑ ≈⟨ by-assoc auto ⟩
    H ↑ • CZ • H ↑ • S ↑ ^ 2 ∎
    where
    open PB ((₂₊ n) QRel,_===_)
    open PP ((₂₊ n) QRel,_===_)
    open SR word-setoid
    open Powers0-Symplectic (suc n)
    open Commuting-Symplectic (n)
    open Sym0-Rewriting (suc n)    

  lemma-S↓H↓CZ↓H : let open PB ((₂₊ n) QRel,_===_) in
    S • H • CZ • H ≈ H • CZ • H • CZ • S ↑ • S
  lemma-S↓H↓CZ↓H {n} = sym (begin
    H • CZ • H • CZ • S ↑ • S ≈⟨ by-assoc auto ⟩
    H • (CZ • H • CZ) • S ↑ • S ≈⟨ (cright (cleft axiom selinger-c11)) ⟩
    H • (S ↓ ^ 2 • H ↓ • S ↓ ^ 2 • CZ • H ↓ • S ↓ ^ 2 • S ↑ ^ 2) • S ↑ • S ≈⟨ general-powers0 100 auto ⟩
    (H • S ↓ ^ 2 • H ↓) • S ↓ ^ 2 • CZ • H ↓ ≈⟨ (cleft lemma-HSSH) ⟩
    (S • H • S) • S ↓ ^ 2 • CZ • H ↓ ≈⟨ general-powers0 100 auto ⟩
    S • H • CZ • H ∎)
    where
    open PB ((₂₊ n) QRel,_===_)
    open PP ((₂₊ n) QRel,_===_)
    open SR word-setoid
    open Powers0-Symplectic (suc n)
    open Commuting-Symplectic (n)

  lemma-S↓²H↓CZ↓H : let open PB ((₂₊ n) QRel,_===_) in
    S ↓ ^ 2 • H ↓ • CZ • H ↓ ≈ H ↓ • CZ • H ↓ • CZ ^ 2 • S ↑ ^ 2 • S ↓ ^ 2
  lemma-S↓²H↓CZ↓H {n@(₀)} = begin
    S ↓ ^ 2 • H ↓ • CZ • H ↓ ≈⟨ assoc ⟩
    S ↓ • S ↓ • H ↓ • CZ • H ↓ ≈⟨ (cright lemma-S↓H↓CZ↓H) ⟩
    S ↓ • H ↓ • CZ • H ↓ • CZ • S ↑ • S ↓ ≈⟨ by-assoc auto ⟩
    (S ↓ • H ↓ • CZ • H ↓) • CZ • S ↑ • S ↓ ≈⟨ (cleft lemma-S↓H↓CZ↓H) ⟩
    (H ↓ • CZ • H ↓ • CZ • S ↑ • S) • CZ • S ↑ • S ↓ ≈⟨ by-assoc auto ⟩
    (H ↓ • CZ • H ↓) • CZ • S ↑  • S ↓ • CZ • S ↑ • S ↓ ≈⟨ ( general-comm auto) ⟩
    H ↓ • CZ • H ↓ • CZ ^ 2 • S ↑ ^ 2 • S ↓ ^ 2 ∎
    where
    open PB ((₂₊ n) QRel,_===_)
    open PP ((₂₊ n) QRel,_===_)
    open SR word-setoid
    open Powers0-Symplectic (suc n)
    open Commuting-Symplectic (n)
  lemma-S↓²H↓CZ↓H {n@(suc _)} = begin
    S ↓ ^ 2 • H ↓ • CZ • H ↓ ≈⟨ assoc ⟩
    S ↓ • S ↓ • H ↓ • CZ • H ↓ ≈⟨ (cright lemma-S↓H↓CZ↓H) ⟩
    S ↓ • H ↓ • CZ • H ↓ • CZ • S ↑ • S ↓ ≈⟨ by-assoc auto ⟩
    (S ↓ • H ↓ • CZ • H ↓) • CZ • S ↑ • S ↓ ≈⟨ (cleft lemma-S↓H↓CZ↓H) ⟩
    (H ↓ • CZ • H ↓ • CZ • S ↑ • S) • CZ • S ↑ • S ↓ ≈⟨ by-assoc auto ⟩
    (H ↓ • CZ • H ↓) • CZ • S ↑  • S ↓ • CZ • S ↑ • S ↓ ≈⟨ ( general-comm auto) ⟩
    H ↓ • CZ • H ↓ • CZ ^ 2 • S ↑ ^ 2 • S ↓ ^ 2 ∎
    where
    open PB ((₂₊ n) QRel,_===_)
    open PP ((₂₊ n) QRel,_===_)
    open SR word-setoid
    open Powers0-Symplectic (suc n)
    open Commuting-Symplectic (n)


  lemma-comm-S-Ex' : let open PB ((₂₊ n) QRel,_===_) in
    S • H • CZ • H • H ↑ • CZ • H ↑ ≈ H • CZ • H • H ↑ • CZ • H ↑ • S ↑
  lemma-comm-S-Ex' {n}  = begin
    S • H • CZ • H • H ↑ • CZ • H ↑ ≈⟨ by-assoc auto ⟩
    (S • H • CZ • H) • H ↑ • CZ • H ↑ ≈⟨ (cleft lemma-S↓H↓CZ↓H) ⟩
    (H • CZ • H • CZ • S ↑ • S) • H ↑ • CZ • H ↑ ≈⟨ rewrite-sym0 1000 auto ⟩
    (H • CZ • H • CZ • S ↑ • H ↑) • S ↓ • CZ • H ↑ ≈⟨ (cright rewrite-sym0 1000 auto) ⟩
    (H • CZ • H • CZ • S ↑ • H ↑) • CZ • H ↑ • S ↓ ≈⟨ by-assoc auto ⟩
    (H • CZ • H • CZ) • (S ↑ • H ↑ • CZ • H ↑) • S ↓ ≈⟨ (cright (cleft lemma-S↑H↑CZ↑H)) ⟩
    (H • CZ • H • CZ) • (H ↑ • CZ • H ↑ • CZ • S ↓ • S ↑) • S ↓ ≈⟨ by-assoc auto ⟩
    (H • CZ • H) • (CZ • H ↑ • CZ) • H ↑ • CZ • S ↓ • S ↑ • S ↓ ≈⟨ (cright (cleft axiom selinger-c10)) ⟩
    (H • CZ • H) • (S ↑ ^ 2 • H ↑ • S ↑ ^ 2 • CZ • H ↑ • S ↑ ^ 2 • S ↓ ^ 2) • H ↑ • CZ • S ↓ • S ↑ • S ↓ ≈⟨ (cright general-comm auto) ⟩
    (H • CZ • H) • (S ↑ ^ 2 • H ↑ • S ↑ ^ 2 • CZ • H ↑ • S ↑ ^ 2) • H ↑ • CZ • S ↓ ^ 4 • S ↑ ≈⟨ (cright general-powers0 100 auto) ⟩
    (H • CZ • H) • (S ↑ ^ 2 • H ↑ • S ↑ ^ 2 • CZ) • (H ↑ • S ↑ ^ 2 • H ↑) • CZ • S ↓ • S ↑ ≈⟨ (cright (cright (cleft lemma-cong↑ _ _ lemma-HSSH))) ⟩
    (H • CZ • H) • (S ↑ ^ 2 • H ↑ • S ↑ ^ 2 • CZ) • (S • H • S) ↑ • CZ • S ↓ • S ↑ ≈⟨ (cright rewrite-sym0 1000 auto ) ⟩
    (H • CZ • H) • (S ↑ ^ 2 • H ↑ • CZ • H ↑) • S ↑ ^ 2 • CZ • S ↓ ≈⟨ (cright (cleft lemma-S↑²H↑CZ↑H)) ⟩
    (H • CZ • H) • (H ↑ • CZ • H ↑ • CZ ^ 2 • S ↓ ^ 2 • S ↑ ^ 2) • S ↑ ^ 2 • CZ • S ↓ ≈⟨ general-powers0 100 auto ⟩
    (H • CZ • H) • (H ↑ • CZ • H ↑ • CZ ^ 2 • S ↓ ^ 2 • S ↑) • CZ • S ↓ ≈⟨ general-comm auto ⟩
    (H • CZ • H) • (H ↑ • CZ • H ↑ • CZ ^ 3 • S ↓ ^ 3 • S ↑) ≈⟨ general-powers0 100 auto ⟩
    H • CZ • H • H ↑ • CZ • H ↑ • S ↑ ∎
    where
    open PB ((₂₊ n) QRel,_===_)
    open PP ((₂₊ n) QRel,_===_)
    open SR word-setoid
    open Powers0-Symplectic (suc n)
    open Commuting-Symplectic (n)
    open Sym0-Rewriting (suc n)    


  lemma-comm-S↑-Ex' : let open PB ((₂₊ n) QRel,_===_) in
    S ↑ • H ↑ • CZ • H ↑ • H ↓ • CZ • H ↓ ≈ H ↑ • CZ • H ↑ • H ↓ • CZ • H ↓ • S ↓
  lemma-comm-S↑-Ex' {n}  = begin
    S ↑ • H ↑ • CZ • H ↑ • H ↓ • CZ • H ↓ ≈⟨ by-assoc auto ⟩
    (S ↑ • H ↑ • CZ • H ↑) • H ↓ • CZ • H ↓ ≈⟨ (cleft lemma-S↑H↑CZ↑H) ⟩
    (H ↑ • CZ • H ↑ • CZ • S ↓ • S ↑) • H ↓ • CZ • H ↓ ≈⟨ rewrite-sym0 1000 auto ⟩
    (H ↑ • CZ • H ↑ • CZ • S ↓ • H ↓) • S ↑ • CZ • H ↓ ≈⟨ (cright rewrite-sym0 1000 auto) ⟩
    (H ↑ • CZ • H ↑ • CZ • S ↓ • H ↓) • CZ • H ↓ • S ↑ ≈⟨ by-assoc auto ⟩
    (H ↑ • CZ • H ↑ • CZ) • (S ↓ • H ↓ • CZ • H ↓) • S ↑ ≈⟨ (cright (cleft lemma-S↓H↓CZ↓H)) ⟩
    (H ↑ • CZ • H ↑ • CZ) • (H ↓ • CZ • H ↓ • CZ • S ↑ • S ↓) • S ↑ ≈⟨ by-assoc auto ⟩
    (H ↑ • CZ • H ↑) • (CZ • H ↓ • CZ) • H ↓ • CZ • S ↑ • S ↓ • S ↑ ≈⟨ (cright (cleft axiom selinger-c11)) ⟩
    (H ↑ • CZ • H ↑) • (S ↓ ^ 2 • H ↓ • S ↓ ^ 2 • CZ • H ↓ • S ↓ ^ 2 • S ↑ ^ 2) • H ↓ • CZ • S ↑ • S ↓ • S ↑ ≈⟨ (cright rewrite-sym0 1000 auto) ⟩
    (H ↑ • CZ • H ↑) • (S ↓ ^ 2 • H ↓ • S ↓ ^ 2 • CZ • H ↓ • S ↓ ^ 2) • H ↓ • CZ • S ↑ ^ 4 • S ↓ ≈⟨ (cright general-powers0 100 auto) ⟩
    (H ↑ • CZ • H ↑) • (S ↓ ^ 2 • H ↓ • S ↓ ^ 2 • CZ) • (H ↓ • S ↓ ^ 2 • H ↓) • CZ • S ↑ • S ↓ ≈⟨ ((cright (cright (cleft lemma-HSSH)))) ⟩
    (H ↑ • CZ • H ↑) • (S ↓ ^ 2 • H ↓ • S ↓ ^ 2 • CZ) • (S • H • S) • CZ • S ↑ • S ↓ ≈⟨ (cright rewrite-sym0 1000 auto) ⟩
    (H ↑ • CZ • H ↑) • (S ↓ ^ 2 • H ↓ • CZ • H ↓) • S ↓ ^ 2 • CZ • S ↑ ≈⟨ (cright cleft lemma-S↓²H↓CZ↓H) ⟩
    (H ↑ • CZ • H ↑) • (H ↓ • CZ • H ↓ • CZ ^ 2 • S ↑ ^ 2 • S ↓ ^ 2) • S ↓ ^ 2 • CZ • S ↑ ≈⟨ general-powers0 100 auto ⟩
    (H ↑ • CZ • H ↑) • (H ↓ • CZ • H ↓ • CZ ^ 2 • S ↑ ^ 2 • S ↓) • CZ • S ↑ ≈⟨ (cright rewrite-sym0 1000 auto) ⟩
    (H ↑ • CZ • H ↑) • (H ↓ • CZ • H ↓ • CZ ^ 3 • S ↑ ^ 3 • S ↓) ≈⟨ general-powers0 100 auto ⟩
    H ↑ • CZ • H ↑ • H ↓ • CZ • H ↓ • S ↓ ∎
    where
    open PB ((₂₊ n) QRel,_===_)
    open PP ((₂₊ n) QRel,_===_)
    open SR word-setoid
    open Powers0-Symplectic (suc n)
    open Commuting-Symplectic (n)
    open Sym0-Rewriting (suc n)    




  lemma-comm-Ex-S : let open PB ((₂₊ n) QRel,_===_) in
    S ↑ • Ex ≈ Ex • S
  lemma-comm-Ex-S {n}  = begin
    S ↑ • CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑ ≈⟨ general-comm auto ⟩
    (S ↑ • CZ • H • H ↑) • CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑ ≈⟨ (rewrite-sym0 1000 auto) ⟩
    (CZ • H) • (S ↑ • H ↑ • CZ • H ↑ • H ↓ • CZ • H ↓) • H ↑ ≈⟨ (cright (cleft lemma-comm-S↑-Ex')) ⟩
    (CZ • H) • (H ↑ • CZ • H ↑ • H ↓ • CZ • H ↓ • S ↓) • H ↑ ≈⟨ general-comm auto ⟩
    Ex • S ∎
    where
    open PB ((₂₊ n) QRel,_===_)
    open PP ((₂₊ n) QRel,_===_)
    open SR word-setoid
    open Powers0-Symplectic (suc n)
    open Commuting-Symplectic (n)
    open Sym0-Rewriting (suc n)    


  lemma-SHSHS : let open PB ((₁₊ n) QRel,_===_) in

    S • H • S • H • S ≈ H ^ 3

  lemma-SHSHS  {n} = begin
    S • H • S • H • S ≈⟨ sym right-unit ⟩
    (S • H • S • H • S) • ε ≈⟨ sym (cong refl (axiom order-H)) ⟩
    (S • H • S • H • S) • H ^ 4 ≈⟨ by-assoc auto ⟩
    (S • H) ^ 3 • H ^ 3 ≈⟨ cong (axiom order-SH) refl ⟩
    ε • H ^ 3 ≈⟨ left-unit ⟩
    H ^ 3 ∎
    where
    open PB ((₁₊ n) QRel,_===_)
    open PP ((₁₊ n) QRel,_===_)
    open SR word-setoid
    open Powers0-Symplectic n


  lemma-CZHCZCZ : let open PB ((₂₊ n) QRel,_===_) in
    CZ • H ↑ • CZ • CZ ≈ S • S ↑ • H ↑ ^ 3 • CZ • S ↑ • H ↑ • S ↑
  lemma-CZHCZCZ {n@(₀)} = begin
    CZ • H ↑ • CZ • CZ ≈⟨ sym (trans assoc (cong refl assoc)) ⟩
    (CZ • H ↑ • CZ) • CZ ≈⟨ cong (axiom selinger-c10) refl ⟩
    (S ↑ ^ 2 • H ↑ • S ↑ ^ 2 • CZ • H ↑ • S ↑ ^ 2 • S ↓ ^ 2) • CZ ≈⟨ general-comm auto ⟩
    (S ↑ ^ 2 • H ↑ • S ↑ ^ 2) • (CZ • H ↑ • CZ) • S ↑ ^ 2 • S ↓ ^ 2 ≈⟨ (cright (cleft axiom selinger-c10)) ⟩
    (S ↑ ^ 2 • H ↑ • S ↑ ^ 2) • (S ↑ ^ 2 • H ↑ • S ↑ ^ 2 • CZ • H ↑ • S ↑ ^ 2 • S ↓ ^ 2) • S ↑ ^ 2 • S ↓ ^ 2 ≈⟨ rewrite-sym0 100 auto ⟩
    (S ↑ ^ 2 • H ↑ • S ↑ ^ 2) • (S ↑ ^ 2 • H ↑ • S ↑ ^ 2 • CZ • H ↑ • S ↑ • S ↓)  ≈⟨ rewrite-sym0 100 auto ⟩
    (S ↑ ^ 2 • H ↑ • S ↑ • H ↑ • S ↑ ^ 2 • CZ • H ↑ • S ↑ • S ↓)  ≈⟨ general-powers0 100 auto ⟩
    S ↑ • (S ↑ • H ↑ • S ↑ • H ↑ • S ↑) • S ↑ • CZ • H ↑ • S ↑ • S ↓  ≈⟨ (cright (cleft lemma-cong↑ _ _ lemma-SHSHS)) ⟩
    S ↑ • (H ↑ ^ 3) • S ↑ • CZ • H ↑ • S ↑ • S ↓  ≈⟨ general-comm auto ⟩
    S • S ↑ • H ↑ ^ 3 • CZ • S ↑ • H ↑ • S ↑ ∎
    where
    open PB ((₂₊ n) QRel,_===_)
    open PP ((₂₊ n) QRel,_===_)
    open SR word-setoid
    open Powers0-Symplectic (suc n)
    open Commuting-Symplectic (n)
    open Sym0-Rewriting (suc n)
  lemma-CZHCZCZ {n@(suc _)} = begin
    CZ • H ↑ • CZ • CZ ≈⟨ sym (trans assoc (cong refl assoc)) ⟩
    (CZ • H ↑ • CZ) • CZ ≈⟨ cong (axiom selinger-c10) refl ⟩
    (S ↑ ^ 2 • H ↑ • S ↑ ^ 2 • CZ • H ↑ • S ↑ ^ 2 • S ↓ ^ 2) • CZ ≈⟨ general-comm auto ⟩
    (S ↑ ^ 2 • H ↑ • S ↑ ^ 2) • (CZ • H ↑ • CZ) • S ↑ ^ 2 • S ↓ ^ 2 ≈⟨ (cright (cleft axiom selinger-c10)) ⟩
    (S ↑ ^ 2 • H ↑ • S ↑ ^ 2) • (S ↑ ^ 2 • H ↑ • S ↑ ^ 2 • CZ • H ↑ • S ↑ ^ 2 • S ↓ ^ 2) • S ↑ ^ 2 • S ↓ ^ 2 ≈⟨ rewrite-sym0 100 auto ⟩
    (S ↑ ^ 2 • H ↑ • S ↑ ^ 2) • (S ↑ ^ 2 • H ↑ • S ↑ ^ 2 • CZ • H ↑ • S ↑ • S ↓)  ≈⟨ rewrite-sym0 100 auto ⟩
    (S ↑ ^ 2 • H ↑ • S ↑ • H ↑ • S ↑ ^ 2 • CZ • H ↑ • S ↑ • S ↓)  ≈⟨ general-powers0 100 auto ⟩
    S ↑ • (S ↑ • H ↑ • S ↑ • H ↑ • S ↑) • S ↑ • CZ • H ↑ • S ↑ • S ↓  ≈⟨ (cright (cleft lemma-cong↑ _ _ lemma-SHSHS)) ⟩
    S ↑ • (H ↑ ^ 3) • S ↑ • CZ • H ↑ • S ↑ • S ↓  ≈⟨ general-comm auto ⟩
    S • S ↑ • H ↑ ^ 3 • CZ • S ↑ • H ↑ • S ↑ ∎
    where
    open PB ((₂₊ n) QRel,_===_)
    open PP ((₂₊ n) QRel,_===_)
    open SR word-setoid
    open Powers0-Symplectic (suc n)
    open Commuting-Symplectic (n)
    open Sym0-Rewriting (suc n)



  lemma-CZCZH↓CZ : let open PB ((₂₊ n) QRel,_===_) in
    CZ • CZ • H • CZ ≈ S • H • CZ • S • (H ^ 3) • S • S ↑
  lemma-CZCZH↓CZ {n@(₀)} = begin
    CZ • CZ • H  • CZ ≈⟨ cong refl (axiom selinger-c11) ⟩
    CZ • (S  ^ 2 • H  • S  ^ 2 • CZ • H  • S  ^ 2 • S ↑ ^ 2) ≈⟨ general-comm auto ⟩
    S  ^ 2 • (CZ • H • CZ) • S  ^ 2 • H  • S  ^ 2 • S ↑ ^ 2 ≈⟨ (cright (cleft axiom selinger-c11)) ⟩
    S  ^ 2 • (S  ^ 2 • H  • S  ^ 2 • CZ • H  • S  ^ 2 • S ↑ ^ 2) • S  ^ 2 • H • S  ^ 2 • S ↑ ^ 2 ≈⟨ general-comm auto ⟩
    S  ^ 4 • H  • S  ^ 2 • CZ • H  • S ^ 4 • S ↑ ^ 4 • H • S  ^ 2 ≈⟨ general-powers0 100 auto ⟩
    S  • H  • S  ^ 2 • CZ • H  • S • S ↑ • H • S  ^ 2 ≈⟨ general-comm auto ⟩
    (S • H • CZ • S) • (S • H • S • H • S) • S • S ↑ ≈⟨ (cright (cleft lemma-SHSHS)) ⟩
    (S • H • CZ • S) • (H ^ 3) • S • S ↑ ≈⟨ by-assoc auto ⟩
    S • H • CZ • S • (H ^ 3) • S • S ↑ ∎
    where
    open PB ((₂₊ n) QRel,_===_)
    open PP ((₂₊ n) QRel,_===_)
    open SR word-setoid
    open Powers0-Symplectic (suc n)
    open Commuting-Symplectic (n)
    open Sym0-Rewriting (suc n)
  lemma-CZCZH↓CZ {n@(suc _)} = begin
    CZ • CZ • H  • CZ ≈⟨ cong refl (axiom selinger-c11) ⟩
    CZ • (S  ^ 2 • H  • S  ^ 2 • CZ • H  • S  ^ 2 • S ↑ ^ 2) ≈⟨ general-comm auto ⟩
    S  ^ 2 • (CZ • H • CZ) • S  ^ 2 • H  • S  ^ 2 • S ↑ ^ 2 ≈⟨ (cright (cleft axiom selinger-c11)) ⟩
    S  ^ 2 • (S  ^ 2 • H  • S  ^ 2 • CZ • H  • S  ^ 2 • S ↑ ^ 2) • S  ^ 2 • H • S  ^ 2 • S ↑ ^ 2 ≈⟨ general-comm auto ⟩
    S  ^ 4 • H  • S  ^ 2 • CZ • H  • S ^ 4 • S ↑ ^ 4 • H • S  ^ 2 ≈⟨ general-powers0 100 auto ⟩
    S  • H  • S  ^ 2 • CZ • H  • S • S ↑ • H • S  ^ 2 ≈⟨ general-comm auto ⟩
    (S • H • CZ • S) • (S • H • S • H • S) • S • S ↑ ≈⟨ (cright (cleft lemma-SHSHS)) ⟩
    (S • H • CZ • S) • (H ^ 3) • S • S ↑ ≈⟨ by-assoc auto ⟩
    S • H • CZ • S • (H ^ 3) • S • S ↑ ∎
    where
    open PB ((₂₊ n) QRel,_===_)
    open PP ((₂₊ n) QRel,_===_)
    open SR word-setoid
    open Powers0-Symplectic (suc n)
    open Commuting-Symplectic (n)
    open Sym0-Rewriting (suc n)
  

  lemma-CZH↓CZCZ : let open PB ((₂₊ n) QRel,_===_) in
    CZ • H • CZ • CZ ≈ S ↑ • S  • H  ^ 3 • CZ • S  • H  • S 
  lemma-CZH↓CZCZ {n@(₀)} = begin
    CZ • H  • CZ • CZ ≈⟨ sym (trans assoc (cong refl assoc)) ⟩
    (CZ • H  • CZ) • CZ ≈⟨ cong (axiom selinger-c11) refl ⟩
    (S  ^ 2 • H  • S  ^ 2 • CZ • H  • S  ^ 2 • S ↑ ^ 2) • CZ ≈⟨ general-comm auto ⟩
    (S  ^ 2 • H  • S  ^ 2) • (CZ • H • CZ) • S  ^ 2 • S ↑ ^ 2 ≈⟨ (cright (cleft axiom selinger-c11)) ⟩
    (S  ^ 2 • H  • S  ^ 2) • (S  ^ 2 • H • S  ^ 2 • CZ • H  • S  ^ 2 • S ↑ ^ 2) • S  ^ 2 • S ↑ ^ 2 ≈⟨ rewrite-sym0 100 auto ⟩
    (S  ^ 2 • H  • S  ^ 2) • (S  ^ 2 • H  • S  ^ 2 • CZ • H  • S  • S ↑ )  ≈⟨ rewrite-sym0 100 auto ⟩
    (S  ^ 2 • H  • S  • H  • S  ^ 2 • CZ • H  • S  • S ↑ )  ≈⟨ general-comm auto ⟩
    S  • (S  • H  • S  • H  • S ) • S  • CZ • H  • S  • S ↑  ≈⟨ (cright cleft (lemma-SHSHS)) ⟩
    S  • (H  ^ 3) • S  • CZ • H  • S  • S ↑  ≈⟨ general-comm auto ⟩
    S ↑ • S  • H  ^ 3 • CZ • S  • H  • S  ∎
    where
    open PB ((₂₊ n) QRel,_===_)
    open PP ((₂₊ n) QRel,_===_)
    open SR word-setoid
    open Powers0-Symplectic (suc n)
    open Commuting-Symplectic (n)
    open Sym0-Rewriting (suc n)
  lemma-CZH↓CZCZ {n@(suc _)} = begin
    CZ • H  • CZ • CZ ≈⟨ sym (trans assoc (cong refl assoc)) ⟩
    (CZ • H  • CZ) • CZ ≈⟨ cong (axiom selinger-c11) refl ⟩
    (S  ^ 2 • H  • S  ^ 2 • CZ • H  • S  ^ 2 • S ↑ ^ 2) • CZ ≈⟨ general-comm auto ⟩
    (S  ^ 2 • H  • S  ^ 2) • (CZ • H • CZ) • S  ^ 2 • S ↑ ^ 2 ≈⟨ (cright (cleft axiom selinger-c11)) ⟩
    (S  ^ 2 • H  • S  ^ 2) • (S  ^ 2 • H • S  ^ 2 • CZ • H  • S  ^ 2 • S ↑ ^ 2) • S  ^ 2 • S ↑ ^ 2 ≈⟨ rewrite-sym0 100 auto ⟩
    (S  ^ 2 • H  • S  ^ 2) • (S  ^ 2 • H  • S  ^ 2 • CZ • H  • S  • S ↑ )  ≈⟨ rewrite-sym0 100 auto ⟩
    (S  ^ 2 • H  • S  • H  • S  ^ 2 • CZ • H  • S  • S ↑ )  ≈⟨ general-comm auto ⟩
    S  • (S  • H  • S  • H  • S ) • S  • CZ • H  • S  • S ↑  ≈⟨ (cright cleft (lemma-SHSHS)) ⟩
    S  • (H  ^ 3) • S  • CZ • H  • S  • S ↑  ≈⟨ general-comm auto ⟩
    S ↑ • S  • H  ^ 3 • CZ • S  • H  • S  ∎
    where
    open PB ((₂₊ n) QRel,_===_)
    open PP ((₂₊ n) QRel,_===_)
    open SR word-setoid
    open Powers0-Symplectic (suc n)
    open Commuting-Symplectic (n)
    open Sym0-Rewriting (suc n)

  lemma-SHSH' : let open PB ((₁₊ n) QRel,_===_) in

    S • H • S • H ≈ H ^ 3 • S ^ 2

  lemma-SHSH' {n} = begin
    S • H • S • H ≈⟨ (cright lemma-HSH) ⟩
    S • (S • S) • H ^ 3 • S • S ≈⟨ general-powers0 100 auto ⟩
    H ^ 3 • S ^ 2 ∎
    where
    open PB ((₁₊ n) QRel,_===_)
    open PP ((₁₊ n) QRel,_===_)
    open SR word-setoid
    open Powers0-Symplectic n


  lemma-SSHSSH : let open PB ((₁₊ n) QRel,_===_) in

    S ^ 2 • H • S ^ 2 • H ≈ H • S

  lemma-SSHSSH {n} = begin
    S ^ 2 • H • S ^ 2 • H ≈⟨ (cright lemma-HSSH) ⟩
    S ^ 2 • S • H • S ≈⟨ general-powers0 100 auto ⟩
    H • S ∎
    where
    open PB ((₁₊ n) QRel,_===_)
    open PP ((₁₊ n) QRel,_===_)
    open SR word-setoid
    open Powers0-Symplectic n

  lemma-SHS : let open PB ((₁₊ n) QRel,_===_) in

    S • H • S ≈ H ^ 3 • S ^ 2 • H ^ 3

  lemma-SHS {n} = begin
    S • H • S ≈⟨ general-powers0 100 auto ⟩
    (S • H • S • H) • H ^ 3 ≈⟨ (cleft lemma-SHSH') ⟩
    (H ^ 3 • S ^ 2) • H ^ 3 ≈⟨ assoc ⟩
    H ^ 3 • S ^ 2 • H ^ 3 ∎
    where
    open PB ((₁₊ n) QRel,_===_)
    open PP ((₁₊ n) QRel,_===_)
    open SR word-setoid
    open Powers0-Symplectic n


  lemma-HSHSH : let open PB ((₁₊ n) QRel,_===_) in

    H • S • H • S • H ≈ S ^ 2

  lemma-HSHSH {n} = begin
    H • S • H • S • H ≈⟨ (cright lemma-SHSH') ⟩
    H • H ^ 3 • S ^ 2 ≈⟨ general-powers0 100 auto ⟩
    S ^ 2 ∎
    where
    open PB ((₁₊ n) QRel,_===_)
    open PP ((₁₊ n) QRel,_===_)
    open SR word-setoid
    open Powers0-Symplectic n

  lemma-HSHS : let open PB ((₁₊ n) QRel,_===_) in

    H • S • H • S ≈ (S • S) • H ^ 3

  lemma-HSHS {n} = begin
    H • S • H • S ≈⟨ by-assoc auto ⟩
    (H • S • H) • S ≈⟨ (cleft lemma-HSH) ⟩
    ((S • S) • H ^ 3 • S • S) • S ≈⟨ general-powers0 100 auto ⟩
    (S • S) • H ^ 3 ∎
    where
    open PB ((₁₊ n) QRel,_===_)
    open PP ((₁₊ n) QRel,_===_)
    open SR word-setoid
    open Powers0-Symplectic n


  -- eqn 17 in Peter's clifford supplement.
  lemma-eqn17 : let open PB ((₂₊ n) QRel,_===_) in
    H ↑ • CZ • S ↑ ^ 2 • H ↑ • H • CZ ≈ CZ • S ↑ • H ↑ • H • CZ • S ^ 2 • H • S ^ 2
  lemma-eqn17 {n@₀} = begin
        H ↑ • CZ • S ↑ ^ 2 • H ↑ • H • CZ ≈⟨ general-powers0 100 auto ⟩
        (H ↑ • CZ • S ↑ ^ 2 • H ↑ • CZ) • CZ • CZ • H • CZ ≈⟨ rewrite-sym0 100 auto ⟩
        (H ↑ • S ↑ ^ 2) • (CZ • H ↑ • CZ • CZ) • CZ • H • CZ ≈⟨ (cright (cleft lemma-CZHCZCZ)) ⟩
        (H ↑ • S ↑ ^ 2) • (S • S ↑ • H ↑ ^ 3 • CZ • S ↑ • H ↑ • S ↑) • CZ • H • CZ ≈⟨ general-comm auto ⟩
        (H ↑ • S ↑ ^ 3 • H ↑ ^ 3) • CZ • S ↑ • H ↑ • S ↑ • S • CZ • H • CZ ≈⟨ general-powers0 100 auto ⟩
        (CZ • S ↑ • H ↑ • S ↑ • S) • CZ • H • CZ ≈⟨ cong refl (axiom selinger-c11) ⟩
        (CZ • S ↑ • H ↑ • S ↑ • S) • S ↓ ^ 2 • H ↓ • S ↓ ^ 2 • CZ • H ↓ • S ↓ ^ 2 • S ↑ ^ 2 ≈⟨ general-powers0 100 auto ⟩
        (CZ • S ↑ • H ↑ • S ↑) • H ↓ • S ↓ ^ 2 • CZ • H ↓ • S ↓ ^ 2 • S ↑ ^ 2 ≈⟨ general-comm auto ⟩
        (CZ • S ↑ • H ↑) • H ↓ • S ↓ ^ 2 • CZ • H ↓ • S ↓ ^ 2 • S ↑ ^ 3 ≈⟨ general-powers0 100 auto ⟩
        (CZ • S ↑ • H ↑) • H ↓ • S ↓ ^ 2 • CZ • H ↓ • S ↓ ^ 2 ≈⟨ general-comm auto ⟩
        CZ • S ↑ • H ↑ • H • CZ • S ^ 2 • H • S ^ 2 ∎
    where
    open PB ((₂₊ n) QRel,_===_)
    open PP ((₂₊ n) QRel,_===_)
    open SR word-setoid
    open Powers0-Symplectic (suc n)
    open Commuting-Symplectic (n)
    open Sym0-Rewriting (suc n)

  lemma-eqn17 {n@(suc _)} = begin
        H ↑ • CZ • S ↑ ^ 2 • H ↑ • H • CZ ≈⟨ general-powers0 100 auto ⟩
        (H ↑ • CZ • S ↑ ^ 2 • H ↑ • CZ) • CZ • CZ • H • CZ ≈⟨ rewrite-sym0 100 auto ⟩
        (H ↑ • S ↑ ^ 2) • (CZ • H ↑ • CZ • CZ) • CZ • H • CZ ≈⟨ (cright (cleft lemma-CZHCZCZ)) ⟩
        (H ↑ • S ↑ ^ 2) • (S • S ↑ • H ↑ ^ 3 • CZ • S ↑ • H ↑ • S ↑) • CZ • H • CZ ≈⟨ general-comm auto ⟩
        (H ↑ • S ↑ ^ 3 • H ↑ ^ 3) • CZ • S ↑ • H ↑ • S ↑ • S • CZ • H • CZ ≈⟨ general-powers0 100 auto ⟩
        (CZ • S ↑ • H ↑ • S ↑ • S) • CZ • H • CZ ≈⟨ cong refl (axiom selinger-c11) ⟩
        (CZ • S ↑ • H ↑ • S ↑ • S) • S ↓ ^ 2 • H ↓ • S ↓ ^ 2 • CZ • H ↓ • S ↓ ^ 2 • S ↑ ^ 2 ≈⟨ general-powers0 100 auto ⟩
        (CZ • S ↑ • H ↑ • S ↑) • H ↓ • S ↓ ^ 2 • CZ • H ↓ • S ↓ ^ 2 • S ↑ ^ 2 ≈⟨ general-comm auto ⟩
        (CZ • S ↑ • H ↑) • H ↓ • S ↓ ^ 2 • CZ • H ↓ • S ↓ ^ 2 • S ↑ ^ 3 ≈⟨ general-powers0 100 auto ⟩
        (CZ • S ↑ • H ↑) • H ↓ • S ↓ ^ 2 • CZ • H ↓ • S ↓ ^ 2 ≈⟨ general-comm auto ⟩
        CZ • S ↑ • H ↑ • H • CZ • S ^ 2 • H • S ^ 2 ∎
    where
    open PB ((₂₊ n) QRel,_===_)
    open PP ((₂₊ n) QRel,_===_)
    open SR word-setoid
    open Powers0-Symplectic (suc n)
    open Commuting-Symplectic (n)
    open Sym0-Rewriting (suc n)

  -- eqn 17 in Peter's clifford supplement.
  lemma-eqn17↓ : let open PB ((₂₊ n) QRel,_===_) in
    H  • CZ • S  ^ 2 • H  • H ↑ • CZ ≈ CZ • S  • H  • H ↑ • CZ • S ↑ ^ 2 • H ↑ • S ↑ ^ 2
  lemma-eqn17↓ {n@₀} = begin
        H  • CZ • S  ^ 2 • H • H ↑ • CZ ≈⟨ general-powers0 100 auto ⟩
        (H  • CZ • S  ^ 2 • H  • CZ) • CZ • CZ • H ↑ • CZ ≈⟨ rewrite-sym0 100 auto ⟩
        (H  • S  ^ 2) • (CZ • H • CZ • CZ) • CZ • H ↑ • CZ ≈⟨ (cright (cleft lemma-CZH↓CZCZ)) ⟩
        (H  • S  ^ 2) • (S ↑ • S  • H  ^ 3 • CZ • S • H  • S) • CZ • H ↑ • CZ ≈⟨ general-comm auto ⟩
        (H  • S  ^ 3 • H  ^ 3) • CZ • S  • H  • S • S ↑ • CZ • H ↑ • CZ ≈⟨ general-powers0 100 auto ⟩
        (CZ • S  • H  • S  • S ↑) • CZ • H ↑ • CZ ≈⟨ cong refl (axiom selinger-c10) ⟩
        (CZ • S  • H  • S  • S ↑) • S ↑ ^ 2 • H ↑ • S ↑ ^ 2 • CZ • H ↑ • S ↑ ^ 2 • S ↓ ^ 2 ≈⟨ general-powers0 100 auto ⟩
        (CZ • S  • H  • S ) • H ↑ • S ↑ ^ 2 • CZ • H ↑ • S ↑ ^ 2 • S ↓ ^ 2 ≈⟨ general-comm auto ⟩
        (CZ • S  • H ) • H ↑ • S ↑ ^ 2 • CZ • H ↑ • S ↑ ^ 2 • S  ^ 3 ≈⟨ general-powers0 100 auto ⟩
        (CZ • S  • H ) • H ↑ • S ↑ ^ 2 • CZ • H ↑ • S ↑ ^ 2 ≈⟨ general-comm auto ⟩
        CZ • S  • H  • H ↑ • CZ • S ↑ ^ 2 • H ↑ • S ↑ ^ 2 ∎
    where
    open PB ((₂₊ n) QRel,_===_)
    open PP ((₂₊ n) QRel,_===_)
    open SR word-setoid
    open Powers0-Symplectic (suc n)
    open Commuting-Symplectic (n)
    open Sym0-Rewriting (suc n)
  lemma-eqn17↓ {n@(suc _)} = begin
        H  • CZ • S  ^ 2 • H • H ↑ • CZ ≈⟨ general-powers0 100 auto ⟩
        (H  • CZ • S  ^ 2 • H  • CZ) • CZ • CZ • H ↑ • CZ ≈⟨ rewrite-sym0 100 auto ⟩
        (H  • S  ^ 2) • (CZ • H • CZ • CZ) • CZ • H ↑ • CZ ≈⟨ (cright (cleft lemma-CZH↓CZCZ)) ⟩
        (H  • S  ^ 2) • (S ↑ • S  • H  ^ 3 • CZ • S • H  • S) • CZ • H ↑ • CZ ≈⟨ general-comm auto ⟩
        (H  • S  ^ 3 • H  ^ 3) • CZ • S  • H  • S • S ↑ • CZ • H ↑ • CZ ≈⟨ general-powers0 100 auto ⟩
        (CZ • S  • H  • S  • S ↑) • CZ • H ↑ • CZ ≈⟨ cong refl (axiom selinger-c10) ⟩
        (CZ • S  • H  • S  • S ↑) • S ↑ ^ 2 • H ↑ • S ↑ ^ 2 • CZ • H ↑ • S ↑ ^ 2 • S ↓ ^ 2 ≈⟨ general-powers0 100 auto ⟩
        (CZ • S  • H  • S ) • H ↑ • S ↑ ^ 2 • CZ • H ↑ • S ↑ ^ 2 • S ↓ ^ 2 ≈⟨ general-comm auto ⟩
        (CZ • S  • H ) • H ↑ • S ↑ ^ 2 • CZ • H ↑ • S ↑ ^ 2 • S  ^ 3 ≈⟨ general-powers0 100 auto ⟩
        (CZ • S  • H ) • H ↑ • S ↑ ^ 2 • CZ • H ↑ • S ↑ ^ 2 ≈⟨ general-comm auto ⟩
        CZ • S  • H  • H ↑ • CZ • S ↑ ^ 2 • H ↑ • S ↑ ^ 2 ∎
    where
    open PB ((₂₊ n) QRel,_===_)
    open PP ((₂₊ n) QRel,_===_)
    open SR word-setoid
    open Powers0-Symplectic (suc n)
    open Commuting-Symplectic (n)
    open Sym0-Rewriting (suc n)


  -- eqn 16 in Peter's clifford supplement.
  lemma-eqn16 : let open PB ((₂₊ n) QRel,_===_) in
    S • H • CZ • H • H ↑ • CZ ≈ H • CZ • H • H ↑ • CZ • S ↑ ^ 2 • H ↑ • S ↑ ^ 2
  lemma-eqn16 {n@₀} = begin
    S • H • CZ • H • H ↑ • CZ ≈⟨ general-powers0 100 auto ⟩
    S • H • (CZ • H • CZ • CZ) • CZ • H ↑ • CZ ≈⟨ (cright (cright (cleft lemma-CZH↓CZCZ))) ⟩
    S • H • (S ↑ • S  • H  ^ 3 • CZ • S  • H  • S) • CZ • H ↑ • CZ ≈⟨ by-assoc auto ⟩
    (S • H • S ↑ • S  • H  ^ 3 • CZ • S  • H  • S) • (CZ • H ↑ • CZ) ≈⟨ (cright (axiom selinger-c10)) ⟩
    (S • H • S ↑ • S  • H  ^ 3 • CZ • S  • H  • S) • (S ↑ ^ 2 • H ↑ • S ↑ ^ 2 • CZ • H ↑ • S ↑ ^ 2 • S ↓ ^ 2) ≈⟨ general-comm auto ⟩
    (S • H • S • H  ^ 3 • CZ • S • H) • (S ↑ ^ 3 • H ↑ • S ↑ ^ 2 • CZ • H ↑ • S ↑ ^ 2 • S ↓ ^ 3) ≈⟨ general-powers0 100 auto ⟩
    (S • H • S • H  ^ 3 • CZ • S • H ) • (H ↑ • S ↑ ^ 2 • CZ • H ↑ • S ↑ ^ 2) ≈⟨ by-assoc auto ⟩
    (S • H • S • H) • H ^ 2 • CZ • S • H  • (H ↑ • S ↑ ^ 2 • CZ • H ↑ • S ↑ ^ 2) ≈⟨ (cleft lemma-SHSH') ⟩
    (H ^ 3 • S ^ 2) • H ^ 2 • CZ • S • H  • (H ↑ • S ↑ ^ 2 • CZ • H ↑ • S ↑ ^ 2) ≈⟨ rewrite-sym0 100 auto ⟩
    H • CZ • H • (H ↑ • S ↑ ^ 2 • CZ • H ↑ • S ↑ ^ 2) ≈⟨ general-comm auto ⟩
    H • CZ • H • H ↑ • CZ • S ↑ ^ 2 • H ↑ • S ↑ ^ 2 ∎
    where
    open PB ((₂₊ n) QRel,_===_)
    open PP ((₂₊ n) QRel,_===_)
    open SR word-setoid
    open Powers0-Symplectic (suc n)
    open Commuting-Symplectic (n)
    open Sym0-Rewriting (suc n)

  lemma-eqn16 {n@(suc _)} = begin
    S • H • CZ • H • H ↑ • CZ ≈⟨ general-powers0 100 auto ⟩
    S • H • (CZ • H • CZ • CZ) • CZ • H ↑ • CZ ≈⟨ (cright (cright (cleft lemma-CZH↓CZCZ))) ⟩
    S • H • (S ↑ • S  • H  ^ 3 • CZ • S  • H  • S) • CZ • H ↑ • CZ ≈⟨ by-assoc auto ⟩
    (S • H • S ↑ • S  • H  ^ 3 • CZ • S  • H  • S) • (CZ • H ↑ • CZ) ≈⟨ (cright (axiom selinger-c10)) ⟩
    (S • H • S ↑ • S  • H  ^ 3 • CZ • S  • H  • S) • (S ↑ ^ 2 • H ↑ • S ↑ ^ 2 • CZ • H ↑ • S ↑ ^ 2 • S ↓ ^ 2) ≈⟨ general-comm auto ⟩
    (S • H • S • H  ^ 3 • CZ • S • H) • (S ↑ ^ 3 • H ↑ • S ↑ ^ 2 • CZ • H ↑ • S ↑ ^ 2 • S ↓ ^ 3) ≈⟨ general-powers0 100 auto ⟩
    (S • H • S • H  ^ 3 • CZ • S • H ) • (H ↑ • S ↑ ^ 2 • CZ • H ↑ • S ↑ ^ 2) ≈⟨ by-assoc auto ⟩
    (S • H • S • H) • H ^ 2 • CZ • S • H  • (H ↑ • S ↑ ^ 2 • CZ • H ↑ • S ↑ ^ 2) ≈⟨ (cleft lemma-SHSH') ⟩
    (H ^ 3 • S ^ 2) • H ^ 2 • CZ • S • H  • (H ↑ • S ↑ ^ 2 • CZ • H ↑ • S ↑ ^ 2) ≈⟨ rewrite-sym0 100 auto ⟩
    H • CZ • H • (H ↑ • S ↑ ^ 2 • CZ • H ↑ • S ↑ ^ 2) ≈⟨ general-comm auto ⟩
    H • CZ • H • H ↑ • CZ • S ↑ ^ 2 • H ↑ • S ↑ ^ 2 ∎
    where
    open PB ((₂₊ n) QRel,_===_)
    open PP ((₂₊ n) QRel,_===_)
    open SR word-setoid
    open Powers0-Symplectic (suc n)
    open Commuting-Symplectic (n)
    open Sym0-Rewriting (suc n)

  lemma-eqn16↑ : let open PB ((₂₊ n) QRel,_===_) in
    S ↑ • H ↑ • CZ • H ↑ • H • CZ ≈ H ↑ • CZ • H ↑ • H • CZ • S ^ 2 • H • S ^ 2
  lemma-eqn16↑ {n@₀} = begin
    S ↑ • H ↑ • CZ • H ↑ • H • CZ ≈⟨ general-powers0 100 auto ⟩
    S ↑ • H ↑ • (CZ • H ↑ • CZ • CZ) • CZ • H • CZ ≈⟨ (cright (cright (cleft lemma-CZHCZCZ))) ⟩
    S ↑ • H ↑ • (S • S ↑  • H ↑  ^ 3 • CZ • S ↑  • H ↑  • S ↑) • CZ • H • CZ ≈⟨ by-assoc auto ⟩
    (S ↑ • H ↑ • S • S ↑  • H ↑  ^ 3 • CZ • S ↑  • H ↑  • S ↑) • (CZ • H • CZ) ≈⟨ (cright (axiom selinger-c11)) ⟩
    (S ↑ • H ↑ • S • S ↑  • H ↑  ^ 3 • CZ • S ↑  • H ↑  • S ↑) • (S ↓ ^ 2 • H ↓ • S ↓ ^ 2 • CZ • H ↓ • S ↓ ^ 2 • S ↑ ^ 2) ≈⟨ general-comm auto ⟩
    (S ↑ • H ↑ • S ↑ • H ↑  ^ 3 • CZ • S ↑ • H ↑) • (S ^ 3 • H • S ^ 2 • CZ • H • S ^ 2 • S ↑  ^ 3) ≈⟨ general-powers0 100 auto ⟩
    (S ↑ • H ↑ • S ↑ • H ↑  ^ 3 • CZ • S ↑ • H ↑ ) • (H • S ^ 2 • CZ • H • S ^ 2) ≈⟨ by-assoc auto ⟩
    (S ↑ • H ↑ • S ↑ • H ↑) • H ↑ ^ 2 • CZ • S ↑ • H ↑  • (H • S ^ 2 • CZ • H • S ^ 2) ≈⟨ (cleft lemma-cong↑ _ _ lemma-SHSH') ⟩
    (H ↑ ^ 3 • S ↑ ^ 2) • H ↑ ^ 2 • CZ • S ↑ • H ↑  • (H • S ^ 2 • CZ • H • S ^ 2) ≈⟨ rewrite-sym0 100 auto ⟩
    H ↑ • CZ • H ↑ • (H • S ^ 2 • CZ • H • S ^ 2) ≈⟨ general-comm auto ⟩
    H ↑ • CZ • H ↑ • H • CZ • S ^ 2 • H • S ^ 2 ∎
    where
    open PB ((₂₊ n) QRel,_===_)
    open PP ((₂₊ n) QRel,_===_)
    open SR word-setoid
    open Powers0-Symplectic (suc n)
    open Commuting-Symplectic (n)
    open Sym0-Rewriting (suc n)

  lemma-eqn16↑ {n@(suc _)} = begin
    S ↑ • H ↑ • CZ • H ↑ • H • CZ ≈⟨ general-powers0 100 auto ⟩
    S ↑ • H ↑ • (CZ • H ↑ • CZ • CZ) • CZ • H • CZ ≈⟨ (cright (cright (cleft lemma-CZHCZCZ))) ⟩
    S ↑ • H ↑ • (S • S ↑  • H ↑  ^ 3 • CZ • S ↑  • H ↑  • S ↑) • CZ • H • CZ ≈⟨ by-assoc auto ⟩
    (S ↑ • H ↑ • S • S ↑  • H ↑  ^ 3 • CZ • S ↑  • H ↑  • S ↑) • (CZ • H • CZ) ≈⟨ (cright (axiom selinger-c11)) ⟩
    (S ↑ • H ↑ • S • S ↑  • H ↑  ^ 3 • CZ • S ↑  • H ↑  • S ↑) • (S ↓ ^ 2 • H ↓ • S ↓ ^ 2 • CZ • H ↓ • S ↓ ^ 2 • S ↑ ^ 2) ≈⟨ general-comm auto ⟩
    (S ↑ • H ↑ • S ↑ • H ↑  ^ 3 • CZ • S ↑ • H ↑) • (S ^ 3 • H • S ^ 2 • CZ • H • S ^ 2 • S ↑  ^ 3) ≈⟨ general-powers0 100 auto ⟩
    (S ↑ • H ↑ • S ↑ • H ↑  ^ 3 • CZ • S ↑ • H ↑ ) • (H • S ^ 2 • CZ • H • S ^ 2) ≈⟨ by-assoc auto ⟩
    (S ↑ • H ↑ • S ↑ • H ↑) • H ↑ ^ 2 • CZ • S ↑ • H ↑  • (H • S ^ 2 • CZ • H • S ^ 2) ≈⟨ (cleft lemma-cong↑ _ _ lemma-SHSH') ⟩
    (H ↑ ^ 3 • S ↑ ^ 2) • H ↑ ^ 2 • CZ • S ↑ • H ↑  • (H • S ^ 2 • CZ • H • S ^ 2) ≈⟨ rewrite-sym0 100 auto ⟩
    H ↑ • CZ • H ↑ • (H • S ^ 2 • CZ • H • S ^ 2) ≈⟨ general-comm auto ⟩
    H ↑ • CZ • H ↑ • H • CZ • S ^ 2 • H • S ^ 2 ∎
    where
    open PB ((₂₊ n) QRel,_===_)
    open PP ((₂₊ n) QRel,_===_)
    open SR word-setoid
    open Powers0-Symplectic (suc n)
    open Commuting-Symplectic (n)
    open Sym0-Rewriting (suc n)


  -- eqn 18 in Peter's clifford supplement.
  lemma-comm-Ex-H' : let open PB ((₂₊ n) QRel,_===_) in
    H ↓ • CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑ • CZ ≈ (CZ • H ↑ • H • CZ • H • H ↑ • CZ) • H ↑
  lemma-comm-Ex-H' {n@₀}  = begin
    H ↓ • CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑ • CZ ≈⟨ general-powers0 100 auto ⟩
    (H • CZ • H ↓ • H ↑) • (CZ • H ↓ • CZ • CZ) • CZ • H ↑ • CZ ≈⟨ (cright (cleft lemma-CZH↓CZCZ)) ⟩
    (H • CZ • H ↓ • H ↑) • (S ↑ • S • H  ^ 3 • CZ • S  • H  • S) • CZ • H ↑ • CZ ≈⟨ (cright rewrite-sym0 1000 auto) ⟩
    (H • CZ • H ↓ • H ↑) • S ↑ • (S • H • S) • H ^ 2 • CZ  • H  • S • CZ • H ↑ • CZ ≈⟨ rewrite-sym0 1000 auto ⟩
    (H • CZ • H ↑) • S ↑ • (H • S • H • S • H) • H • CZ  • H  • S • CZ • H ↑ • CZ ≈⟨ (cright (cright (cleft lemma-HSHSH))) ⟩
    (H • CZ • H ↑) • S ↑ • (S ^ 2) • H • CZ  • H  • S • CZ • H ↑ • CZ ≈⟨ ((cright rewrite-sym0 1000 auto)) ⟩
    (H • CZ • H ↑) • (S ^ 2) • H • CZ • S ↑ • H  • S • CZ • H ↑ • CZ ≈⟨ by-assoc auto ⟩
    (H • CZ • H ↑ • S ^ 2 • H • CZ) • S ↑ • H  • S • CZ • H ↑ • CZ ≈⟨ general-comm auto ⟩
    (H • CZ • S ^ 2 • H • H ↑ • CZ) • S ↑ • H  • S • CZ • H ↑ • CZ ≈⟨ (cleft lemma-eqn17↓) ⟩
    (CZ • S • H  • H ↑ • CZ • S ↑ ^ 2 • H ↑ • S ↑ ^ 2) • S ↑ • H  • S • CZ • H ↑ • CZ ≈⟨ general-powers0 100 auto ⟩
    CZ • S • H  • H ↑ • CZ • S ↑ ^ 2 • H ↑ • H  • S • CZ • H ↑ • CZ ≈⟨ general-comm auto ⟩
    (CZ • H ↑ • S ↑ ^ 2) • (S • H • CZ • H • H ↑ • CZ) • S • H ↑ • CZ ≈⟨ (cright (cleft lemma-eqn16)) ⟩
    (CZ • H ↑ • S ↑ ^ 2) • (H • CZ • H • H ↑ • CZ • S ↑ ^ 2 • H ↑ • S ↑ ^ 2) • S • H ↑ • CZ ≈⟨ general-comm auto ⟩
    (CZ • H ↑ • H • CZ) • (H • S ↑ ^ 2 • H ↑ • CZ) • (S ↑ ^ 2 • H ↑ • S ↑ ^ 2 • H ↑) • S • CZ ≈⟨ (cright (cright (cleft lemma-cong↑ _ _ lemma-SSHSSH))) ⟩
    (CZ • H ↑ • H • CZ) • (H • S ↑ ^ 2 • H ↑ • CZ) • (H ↑ • S ↑) • S • CZ ≈⟨ general-comm auto ⟩
    (CZ • H ↑ • H • CZ • H) • (S ↑ ^ 2 • H ↑ • CZ • H ↑) • S ↑ • S • CZ ≈⟨ (cright (cleft lemma-S↑²H↑CZ↑H)) ⟩
    (CZ • H ↑ • H • CZ • H) • (H ↑ • CZ • H ↑ • CZ ^ 2 • S ↓ ^ 2 • S ↑ ^ 2) • S ↑ • S • CZ ≈⟨ general-powers0 100 auto ⟩
    (CZ • H ↑ • H • CZ • H • H ↑ • CZ) • H ↑ ∎
    where
    open PB ((₂₊ n) QRel,_===_)
    open PP ((₂₊ n) QRel,_===_)
    open SR word-setoid
    open Powers0-Symplectic (suc n)
    open Commuting-Symplectic (n)
    open Sym0-Rewriting (suc n)
  lemma-comm-Ex-H' {n@(suc _)}  = begin
    H ↓ • CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑ • CZ ≈⟨ general-powers0 100 auto ⟩
    (H • CZ • H ↓ • H ↑) • (CZ • H ↓ • CZ • CZ) • CZ • H ↑ • CZ ≈⟨ (cright (cleft lemma-CZH↓CZCZ)) ⟩
    (H • CZ • H ↓ • H ↑) • (S ↑ • S • H  ^ 3 • CZ • S  • H  • S) • CZ • H ↑ • CZ ≈⟨ (cright rewrite-sym0 1000 auto) ⟩
    (H • CZ • H ↓ • H ↑) • S ↑ • (S • H • S) • H ^ 2 • CZ  • H  • S • CZ • H ↑ • CZ ≈⟨ rewrite-sym0 1000 auto ⟩
    (H • CZ • H ↑) • S ↑ • (H • S • H • S • H) • H • CZ  • H  • S • CZ • H ↑ • CZ ≈⟨ (cright (cright (cleft lemma-HSHSH))) ⟩
    (H • CZ • H ↑) • S ↑ • (S ^ 2) • H • CZ  • H  • S • CZ • H ↑ • CZ ≈⟨ ((cright rewrite-sym0 1000 auto)) ⟩
    (H • CZ • H ↑) • (S ^ 2) • H • CZ • S ↑ • H  • S • CZ • H ↑ • CZ ≈⟨ by-assoc auto ⟩
    (H • CZ • H ↑ • S ^ 2 • H • CZ) • S ↑ • H  • S • CZ • H ↑ • CZ ≈⟨ general-comm auto ⟩
    (H • CZ • S ^ 2 • H • H ↑ • CZ) • S ↑ • H  • S • CZ • H ↑ • CZ ≈⟨ (cleft lemma-eqn17↓) ⟩
    (CZ • S • H  • H ↑ • CZ • S ↑ ^ 2 • H ↑ • S ↑ ^ 2) • S ↑ • H  • S • CZ • H ↑ • CZ ≈⟨ general-powers0 100 auto ⟩
    CZ • S • H  • H ↑ • CZ • S ↑ ^ 2 • H ↑ • H  • S • CZ • H ↑ • CZ ≈⟨ general-comm auto ⟩
    (CZ • H ↑ • S ↑ ^ 2) • (S • H • CZ • H • H ↑ • CZ) • S • H ↑ • CZ ≈⟨ (cright (cleft lemma-eqn16)) ⟩
    (CZ • H ↑ • S ↑ ^ 2) • (H • CZ • H • H ↑ • CZ • S ↑ ^ 2 • H ↑ • S ↑ ^ 2) • S • H ↑ • CZ ≈⟨ general-comm auto ⟩
    (CZ • H ↑ • H • CZ) • (H • S ↑ ^ 2 • H ↑ • CZ) • (S ↑ ^ 2 • H ↑ • S ↑ ^ 2 • H ↑) • S • CZ ≈⟨ (cright (cright (cleft lemma-cong↑ _ _ lemma-SSHSSH))) ⟩
    (CZ • H ↑ • H • CZ) • (H • S ↑ ^ 2 • H ↑ • CZ) • (H ↑ • S ↑) • S • CZ ≈⟨ general-comm auto ⟩
    (CZ • H ↑ • H • CZ • H) • (S ↑ ^ 2 • H ↑ • CZ • H ↑) • S ↑ • S • CZ ≈⟨ (cright (cleft lemma-S↑²H↑CZ↑H)) ⟩
    (CZ • H ↑ • H • CZ • H) • (H ↑ • CZ • H ↑ • CZ ^ 2 • S ↓ ^ 2 • S ↑ ^ 2) • S ↑ • S • CZ ≈⟨ general-powers0 100 auto ⟩
    (CZ • H ↑ • H • CZ • H • H ↑ • CZ) • H ↑ ∎
    where
    open PB ((₂₊ n) QRel,_===_)
    open PP ((₂₊ n) QRel,_===_)
    open SR word-setoid
    open Powers0-Symplectic (suc n)
    open Commuting-Symplectic (n)
    open Sym0-Rewriting (suc n)


  lemma-comm-Ex-H↑' : let open PB ((₂₊ n) QRel,_===_) in
    H ↑  • CZ • H ↑  • H • CZ • H ↑  • H • CZ ≈ (CZ • H • H ↑ • CZ • H ↑ • H • CZ) • H
  lemma-comm-Ex-H↑' {n@₀}  = begin
    H ↑  • CZ • H ↑  • H • CZ • H ↑  • H • CZ ≈⟨ general-powers0 100 auto ⟩
    (H ↑ • CZ • H ↑  • H) • (CZ • H ↑ • CZ • CZ) • CZ • H • CZ ≈⟨ (cright (cleft lemma-CZHCZCZ)) ⟩
    (H ↑ • CZ • H ↑  • H) • (S • S ↑ • H ↑ ^ 3 • CZ • S ↑ • H ↑ • S ↑) • CZ • H • CZ ≈⟨ (cright rewrite-sym0 1000 auto) ⟩
    (H ↑ • CZ • H ↑  • H) • S • (S ↑ • H ↑ • S ↑) • H ↑ ^ 2 • CZ  • H ↑  • S ↑ • CZ • H • CZ ≈⟨ rewrite-sym0 1000 auto ⟩
    (H ↑ • CZ • H) • S • (H ↑ • S ↑ • H ↑ • S ↑ • H ↑) • H ↑ • CZ  • H ↑  • S ↑ • CZ • H • CZ ≈⟨ (cright (cright (cleft lemma-cong↑ _ _ lemma-HSHSH ))) ⟩
    (H ↑ • CZ • H) • S • (S ↑ ^ 2) • H ↑ • CZ  • H ↑  • S ↑ • CZ • H • CZ ≈⟨ ((cright general-comm auto)) ⟩
    (H ↑ • CZ • H) • (S ↑ ^ 2) • H ↑ • CZ • S • H ↑  • S ↑ • CZ • H • CZ ≈⟨ by-assoc auto ⟩
    (H ↑ • CZ • H • S ↑ ^ 2 • H ↑ • CZ) • S • H ↑  • S ↑ • CZ • H • CZ ≈⟨ general-comm auto ⟩
    (H ↑ • CZ • S ↑ ^ 2 • H ↑ • H • CZ) • S • H ↑  • S ↑ • CZ • H • CZ ≈⟨ (cleft lemma-eqn17) ⟩
    (CZ • S ↑ • H ↑  • H • CZ • S ^ 2 • H • S ^ 2) • S • H ↑  • S ↑ • CZ • H • CZ ≈⟨ general-powers0 100 auto ⟩
    CZ • S ↑ • H ↑  • H • CZ • S ^ 2 • H • H ↑  • S ↑ • CZ • H • CZ ≈⟨ general-comm auto ⟩
    (CZ • H • S ^ 2) • (S ↑ • H ↑ • CZ • H ↑ • H • CZ) • S ↑ • H • CZ ≈⟨ (cright (cleft lemma-eqn16↑)) ⟩
    (CZ • H • S ^ 2) • (H ↑ • CZ • H ↑ • H • CZ • S ^ 2 • H • S ^ 2) • S ↑ • H • CZ ≈⟨ general-comm auto ⟩
    (CZ • H • H ↑ • CZ) • (H ↑ • S ^ 2 • H • CZ) • (S ^ 2 • H • S ^ 2 • H) • S ↑ • CZ ≈⟨ (cright (cright (cleft  lemma-SSHSSH ))) ⟩
    (CZ • H • H ↑ • CZ) • (H ↑ • S ^ 2 • H • CZ) • (H • S) • S ↑ • CZ ≈⟨ general-comm auto ⟩
    (CZ • H • H ↑ • CZ • H ↑) • (S ^ 2 • H • CZ • H) • S • S ↑ • CZ ≈⟨ (cright (cleft lemma-S↓²H↓CZ↓H)) ⟩
    (CZ • H • H ↑ • CZ • H ↑) • (H • CZ • H • CZ ^ 2 • S ↑  ^ 2 • S ^ 2) • S • S ↑ • CZ ≈⟨ general-powers0 100 auto ⟩
    (CZ • H • H ↑ • CZ • H ↑ • H • CZ) • H ∎
    where
    open PB ((₂₊ n) QRel,_===_)
    open PP ((₂₊ n) QRel,_===_)
    open SR word-setoid
    open Powers0-Symplectic (suc n)
    open Commuting-Symplectic (n)
    open Sym0-Rewriting (suc n)

  lemma-comm-Ex-H↑' {n@(suc _)}  = begin
    H ↑  • CZ • H ↑  • H • CZ • H ↑  • H • CZ ≈⟨ general-powers0 100 auto ⟩
    (H ↑ • CZ • H ↑  • H) • (CZ • H ↑ • CZ • CZ) • CZ • H • CZ ≈⟨ (cright (cleft lemma-CZHCZCZ)) ⟩
    (H ↑ • CZ • H ↑  • H) • (S • S ↑ • H ↑ ^ 3 • CZ • S ↑ • H ↑ • S ↑) • CZ • H • CZ ≈⟨ (cright rewrite-sym0 1000 auto) ⟩
    (H ↑ • CZ • H ↑  • H) • S • (S ↑ • H ↑ • S ↑) • H ↑ ^ 2 • CZ  • H ↑  • S ↑ • CZ • H • CZ ≈⟨ rewrite-sym0 1000 auto ⟩
    (H ↑ • CZ • H) • S • (H ↑ • S ↑ • H ↑ • S ↑ • H ↑) • H ↑ • CZ  • H ↑  • S ↑ • CZ • H • CZ ≈⟨ (cright (cright (cleft lemma-cong↑ _ _ lemma-HSHSH ))) ⟩
    (H ↑ • CZ • H) • S • (S ↑ ^ 2) • H ↑ • CZ  • H ↑  • S ↑ • CZ • H • CZ ≈⟨ ((cright general-comm auto)) ⟩
    (H ↑ • CZ • H) • (S ↑ ^ 2) • H ↑ • CZ • S • H ↑  • S ↑ • CZ • H • CZ ≈⟨ by-assoc auto ⟩
    (H ↑ • CZ • H • S ↑ ^ 2 • H ↑ • CZ) • S • H ↑  • S ↑ • CZ • H • CZ ≈⟨ general-comm auto ⟩
    (H ↑ • CZ • S ↑ ^ 2 • H ↑ • H • CZ) • S • H ↑  • S ↑ • CZ • H • CZ ≈⟨ (cleft lemma-eqn17) ⟩
    (CZ • S ↑ • H ↑  • H • CZ • S ^ 2 • H • S ^ 2) • S • H ↑  • S ↑ • CZ • H • CZ ≈⟨ general-powers0 100 auto ⟩
    CZ • S ↑ • H ↑  • H • CZ • S ^ 2 • H • H ↑  • S ↑ • CZ • H • CZ ≈⟨ general-comm auto ⟩
    (CZ • H • S ^ 2) • (S ↑ • H ↑ • CZ • H ↑ • H • CZ) • S ↑ • H • CZ ≈⟨ (cright (cleft lemma-eqn16↑)) ⟩
    (CZ • H • S ^ 2) • (H ↑ • CZ • H ↑ • H • CZ • S ^ 2 • H • S ^ 2) • S ↑ • H • CZ ≈⟨ general-comm auto ⟩
    (CZ • H • H ↑ • CZ) • (H ↑ • S ^ 2 • H • CZ) • (S ^ 2 • H • S ^ 2 • H) • S ↑ • CZ ≈⟨ (cright (cright (cleft  lemma-SSHSSH ))) ⟩
    (CZ • H • H ↑ • CZ) • (H ↑ • S ^ 2 • H • CZ) • (H • S) • S ↑ • CZ ≈⟨ general-comm auto ⟩
    (CZ • H • H ↑ • CZ • H ↑) • (S ^ 2 • H • CZ • H) • S • S ↑ • CZ ≈⟨ (cright (cleft lemma-S↓²H↓CZ↓H)) ⟩
    (CZ • H • H ↑ • CZ • H ↑) • (H • CZ • H • CZ ^ 2 • S ↑  ^ 2 • S ^ 2) • S • S ↑ • CZ ≈⟨ general-powers0 100 auto ⟩
    (CZ • H • H ↑ • CZ • H ↑ • H • CZ) • H ∎
    where
    open PB ((₂₊ n) QRel,_===_)
    open PP ((₂₊ n) QRel,_===_)
    open SR word-setoid
    open Powers0-Symplectic (suc n)
    open Commuting-Symplectic (n)
    open Sym0-Rewriting (suc n)


  lemma-comm-Ex-H : let open PB ((₂₊ n) QRel,_===_) in
    H ↑ • Ex ≈ Ex • H
  lemma-comm-Ex-H {n@₀}  = begin
    H ↑ • CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑ ≈⟨ general-comm auto ⟩
    (H ↑  • CZ • H ↑  • H • CZ • H ↑  • H • CZ) • H ↓ • H ↑ ≈⟨ (cleft lemma-comm-Ex-H↑') ⟩
    ((CZ • H • H ↑ • CZ • H ↑ • H • CZ) • H) • H ↓ • H ↑ ≈⟨ general-comm auto ⟩
    Ex • H ∎
    where
    open PB ((₂₊ n) QRel,_===_)
    open PP ((₂₊ n) QRel,_===_)
    open SR word-setoid
    open Powers0-Symplectic (suc n)
    open Commuting-Symplectic (n)
    open Sym0-Rewriting (suc n)

  lemma-comm-Ex-H {n@(suc _)}  = begin
    H ↑ • CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑ ≈⟨ general-comm auto ⟩
    (H ↑  • CZ • H ↑  • H • CZ • H ↑  • H • CZ) • H ↓ • H ↑ ≈⟨ (cleft lemma-comm-Ex-H↑') ⟩
    ((CZ • H • H ↑ • CZ • H ↑ • H • CZ) • H) • H ↓ • H ↑ ≈⟨ general-comm auto ⟩
    Ex • H ∎
    where
    open PB ((₂₊ n) QRel,_===_)
    open PP ((₂₊ n) QRel,_===_)
    open SR word-setoid
    open Powers0-Symplectic (suc n)
    open Commuting-Symplectic (n)
    open Sym0-Rewriting (suc n)




  lemma-comm-Ex-CZ' : let open PB ((₂₊ n) QRel,_===_) in
    CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑ ≈ (H ↓ • H ↑ • CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑) • CZ
  lemma-comm-Ex-CZ' {n@₀} = begin
    CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑ ≈⟨ general-comm auto ⟩
    ((CZ • H • H ↑ • CZ • H ↑ • H • CZ) • H) • H ↑ ≈⟨ (cleft sym lemma-comm-Ex-H↑') ⟩
    (H ↑  • CZ • H ↑  • H • CZ • H ↑  • H • CZ) • H ↑ ≈⟨ general-comm auto ⟩
    H ↑  • (CZ • H ↑ • H • CZ • H • H ↑ • CZ) • H ↑ ≈⟨ (cright sym lemma-comm-Ex-H') ⟩
    H ↑  • H ↓ • CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑ • CZ ≈⟨ general-comm auto ⟩
    (H ↓ • H ↑ • CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑) • CZ ∎
    where
    open PB ((₂₊ n) QRel,_===_)
    open PP ((₂₊ n) QRel,_===_)
    open SR word-setoid
    open Powers0-Symplectic (suc n)
    open Commuting-Symplectic (n)
    open Sym0-Rewriting (suc n)
  lemma-comm-Ex-CZ' {n@(suc _)} = begin
    CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑ ≈⟨ general-comm auto ⟩
    ((CZ • H • H ↑ • CZ • H ↑ • H • CZ) • H) • H ↑ ≈⟨ (cleft sym lemma-comm-Ex-H↑') ⟩
    (H ↑  • CZ • H ↑  • H • CZ • H ↑  • H • CZ) • H ↑ ≈⟨ general-comm auto ⟩
    H ↑  • (CZ • H ↑ • H • CZ • H • H ↑ • CZ) • H ↑ ≈⟨ (cright sym lemma-comm-Ex-H') ⟩
    H ↑  • H ↓ • CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑ • CZ ≈⟨ general-comm auto ⟩
    (H ↓ • H ↑ • CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑) • CZ ∎
    where
    open PB ((₂₊ n) QRel,_===_)
    open PP ((₂₊ n) QRel,_===_)
    open SR word-setoid
    open Powers0-Symplectic (suc n)
    open Commuting-Symplectic (n)
    open Sym0-Rewriting (suc n)

  lemma-comm-Ex-CZ : let open PB ((₂₊ n) QRel,_===_) in
    CZ • Ex ≈ Ex • CZ
  lemma-comm-Ex-CZ {n@₀} = begin
    CZ • Ex ≈⟨ refl ⟩
    CZ • CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑ ≈⟨ (cright lemma-comm-Ex-CZ') ⟩
    CZ • (H ↓ • H ↑ • CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑) • CZ ≈⟨ sym assoc ⟩
    Ex • CZ ∎
    where
    open PB ((₂₊ n) QRel,_===_)
    open PP ((₂₊ n) QRel,_===_)
    open SR word-setoid
    open Powers0-Symplectic (suc n)
    open Commuting-Symplectic (n)
    open Sym0-Rewriting (suc n)

  lemma-comm-Ex-CZ {n@(suc _)} = begin
    CZ • Ex ≈⟨ refl ⟩
    CZ • CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑ ≈⟨ (cright lemma-comm-Ex-CZ') ⟩
    CZ • (H ↓ • H ↑ • CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑) • CZ ≈⟨ sym assoc ⟩
    Ex • CZ ∎
    where
    open PB ((₂₊ n) QRel,_===_)
    open PP ((₂₊ n) QRel,_===_)
    open SR word-setoid
    open Powers0-Symplectic (suc n)
    open Commuting-Symplectic (n)
    open Sym0-Rewriting (suc n)


  lemma-order-Ex : let open PB ((₂₊ n) QRel,_===_) in
    Ex ^ 2 ≈ ε
  lemma-order-Ex {n@₀} = begin
    Ex ^ 2 ≈⟨ refl ⟩
    (CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑) • (CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑) ≈⟨ (cright lemma-comm-Ex-CZ') ⟩
    (CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑) • ((H ↓ • H ↑ • CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑) • CZ) ≈⟨ general-comm auto ⟩
    ((CZ • H • H ↑ • CZ • H ↑ • H • CZ) • H) • H ↑ ^ 2 • (H ↓ • CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑ • CZ) ≈⟨ cong (sym lemma-comm-Ex-H↑') (cong refl lemma-comm-Ex-H') ⟩
    (H ↑  • CZ • H ↑  • H • CZ • H ↑  • H • CZ) • H ↑ ^ 2 • ((CZ • H ↑ • H • CZ • H • H ↑ • CZ) • H ↑) ≈⟨ general-comm auto ⟩
    (H ↑  • CZ • H ↑  • H • CZ • H ↑  • H) • (CZ • H ↑ ^ 2) • ((CZ • H ↑ • H • CZ • H • H ↑ • CZ) • H ↑) ≈⟨ (cright (cleft axiom semi-CZ-HH↑)) ⟩
    (H ↑  • CZ • H ↑  • H • CZ • H ↑  • H) • (H ↑ ^ 2 • CZ ^ 2) • ((CZ • H ↑ • H • CZ • H • H ↑ • CZ) • H ↑) ≈⟨ general-powers0 100 auto ⟩
    (H ↑  • CZ • H ↑  • H • CZ • H ↑  • H) • (H ↑ ^ 2 • H ↑ • H • CZ • H • H ↑ • CZ • H ↑) ≈⟨ general-comm auto ⟩
    (H ↑  • CZ • H ↑  • H • CZ • H ↑ ^ 4) • (H ^ 2 • CZ) • H • H ↑ • CZ • H ↑ ≈⟨ (cright (cleft rewrite-sym0 100 auto)) ⟩
    (H ↑  • CZ • H ↑  • H • CZ • H ↑ ^ 4) • (CZ ^ 2 • H ^ 2) • H • H ↑ • CZ • H ↑ ≈⟨ general-powers0 100 auto ⟩
    (H ↑  • CZ) • (H ↑ ^ 2 • CZ) • H ↑ ≈⟨ (cright (cleft rewrite-sym0 100 auto)) ⟩
    (H ↑  • CZ) • (CZ ^ 2 • H ↑ ^ 2) • H ↑ ≈⟨ general-powers0 100 auto ⟩
    ε ∎
    where
    open PB ((₂₊ n) QRel,_===_)
    open PP ((₂₊ n) QRel,_===_)
    open SR word-setoid
    open Powers0-Symplectic (suc n)
    open Commuting-Symplectic (n)
    open Sym0-Rewriting (suc n)

  lemma-order-Ex {n@(suc _)} = begin
    Ex ^ 2 ≈⟨ refl ⟩
    (CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑) • (CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑) ≈⟨ (cright lemma-comm-Ex-CZ') ⟩
    (CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑) • ((H ↓ • H ↑ • CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑) • CZ) ≈⟨ general-comm auto ⟩
    ((CZ • H • H ↑ • CZ • H ↑ • H • CZ) • H) • H ↑ ^ 2 • (H ↓ • CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑ • CZ) ≈⟨ cong (sym lemma-comm-Ex-H↑') (cong refl lemma-comm-Ex-H') ⟩
    (H ↑  • CZ • H ↑  • H • CZ • H ↑  • H • CZ) • H ↑ ^ 2 • ((CZ • H ↑ • H • CZ • H • H ↑ • CZ) • H ↑) ≈⟨ general-comm auto ⟩
    (H ↑  • CZ • H ↑  • H • CZ • H ↑  • H) • (CZ • H ↑ ^ 2) • ((CZ • H ↑ • H • CZ • H • H ↑ • CZ) • H ↑) ≈⟨ (cright (cleft axiom semi-CZ-HH↑)) ⟩
    (H ↑  • CZ • H ↑  • H • CZ • H ↑  • H) • (H ↑ ^ 2 • CZ ^ 2) • ((CZ • H ↑ • H • CZ • H • H ↑ • CZ) • H ↑) ≈⟨ general-powers0 100 auto ⟩
    (H ↑  • CZ • H ↑  • H • CZ • H ↑  • H) • (H ↑ ^ 2 • H ↑ • H • CZ • H • H ↑ • CZ • H ↑) ≈⟨ general-comm auto ⟩
    (H ↑  • CZ • H ↑  • H • CZ • H ↑ ^ 4) • (H ^ 2 • CZ) • H • H ↑ • CZ • H ↑ ≈⟨ (cright (cleft rewrite-sym0 100 auto)) ⟩
    (H ↑  • CZ • H ↑  • H • CZ • H ↑ ^ 4) • (CZ ^ 2 • H ^ 2) • H • H ↑ • CZ • H ↑ ≈⟨ general-powers0 100 auto ⟩
    (H ↑  • CZ) • (H ↑ ^ 2 • CZ) • H ↑ ≈⟨ (cright (cleft rewrite-sym0 100 auto)) ⟩
    (H ↑  • CZ) • (CZ ^ 2 • H ↑ ^ 2) • H ↑ ≈⟨ general-powers0 100 auto ⟩
    ε ∎
    where
    open PB ((₂₊ n) QRel,_===_)
    open PP ((₂₊ n) QRel,_===_)
    open SR word-setoid
    open Powers0-Symplectic (suc n)
    open Commuting-Symplectic (n)
    open Sym0-Rewriting (suc n)


  lemma-order-ₕ|ₕ : let open PB ((₂₊ n) QRel,_===_) in
    ₕ|ₕ ^ 2 ≈ ε
  lemma-order-ₕ|ₕ {n} = begin
    ₕ|ₕ ^ 2 ≈⟨ rewrite-sym0 100 auto ⟩
    ε ∎
    where
    open PB ((₂₊ n) QRel,_===_)
    open PP ((₂₊ n) QRel,_===_)
    open SR word-setoid
    open Powers0-Symplectic (suc n)
    open Commuting-Symplectic (n)
    open Sym0-Rewriting (suc n)

  lemma-order-ʰ|ʰ : let open PB ((₂₊ n) QRel,_===_) in
    ʰ|ʰ ^ 2 ≈ ε
  lemma-order-ʰ|ʰ {n} = begin
    ʰ|ʰ ^ 2 ≈⟨ rewrite-sym0 100 auto ⟩
    ε ∎
    where
    open PB ((₂₊ n) QRel,_===_)
    open PP ((₂₊ n) QRel,_===_)
    open SR word-setoid
    open Powers0-Symplectic (suc n)
    open Commuting-Symplectic (n)
    open Sym0-Rewriting (suc n)


  lemma-Ex-Ex↑-CZ'a : let open PB ((₃₊ n) QRel,_===_) in
    Ex ↑ • CZ • Ex ↑ ≈ ⊤⊥ ↑ • CZ ↓ • ⊥⊤ ↑
  lemma-Ex-Ex↑-CZ'a {n@₀} = begin
    (CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑) ↑ • CZ • (CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑) ↑ ≈⟨ (cright (cright lemma-cong↑ _ _ lemma-comm-Ex-CZ')) ⟩
    (CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑) ↑ • CZ • ((H ↓ • H ↑ • CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑) • CZ) ↑ ≈⟨ general-comm auto ⟩
    (((CZ • H • H ↑ • CZ • H ↑ • H • CZ) • H) • H ↑) ↑ • CZ • (H ↑ • (H ↓ • CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑ • CZ)) ↑ ≈⟨ cong (cleft (sym (lemma-cong↑ _ _ lemma-comm-Ex-H↑'))) (cright (cright lemma-cong↑ _ _ lemma-comm-Ex-H')) ⟩
    ((H ↑  • CZ • H ↑  • H • CZ • H ↑ • H • CZ) • H ↑) ↑ • CZ • (H ↑ • ((CZ • H ↑ • H • CZ • H • H ↑ • CZ) • H ↑)) ↑ ≈⟨ general-comm auto ⟩
    (H ↑  • CZ • H ↑  • H • CZ • H ↑ • H) ↑ • (CZ ↑ • H ↑ ↑ ^ 2) • CZ  • (((CZ • H ↑ • H • CZ • H • H ↑ • CZ) • H ↑)) ↑ ≈⟨ (cright (cleft axiom (cong↑ semi-CZ-HH↑))) ⟩
    (H ↑  • CZ • H ↑  • H • CZ • H ↑ • H) ↑ • (H ↑ ↑ ^ 2 • CZ ↑ ^ 2) • CZ  • (((CZ • H ↑ • H • CZ • H • H ↑ • CZ) • H ↑)) ↑ ≈⟨ general-comm auto ⟩
    (H ↑  • CZ • H ↑  • H • CZ • H ↑ • H) ↑ • (H ↑ ↑ ^ 2 • CZ ↑ ^ 3) • CZ  • ((( H ↑ • H • CZ • H • H ↑ • CZ) • H ↑)) ↑ ≈⟨ general-powers0 100 auto ⟩
    (H ↑  • CZ • H ↑  • H • CZ • H ↑ • H) ↑ • (H ↑ ↑ ^ 2) • CZ  • ((( H ↑ • H • CZ • H • H ↑ • CZ) • H ↑)) ↑ ≈⟨ general-comm auto ⟩
    (H ↑  • CZ • H ↑  • H • CZ • H) ↑ • (H ↑ ↑ ^ 4) • CZ  • (((H • CZ • H • H ↑ • CZ) • H ↑)) ↑ ≈⟨ general-powers0 100 auto ⟩
    (H ↑  • CZ • H ↑  • H • CZ • H) ↑ • CZ  • (((H • CZ • H • H ↑ • CZ) • H ↑)) ↑ ≈⟨ by-assoc auto ⟩
    ⊤⊥ ↑ • CZ ↓ • ⊥⊤ ↑ ∎
    where
    open PB ((₃₊ n) QRel,_===_)
    open PP ((₃₊ n) QRel,_===_)
    open SR word-setoid
    open Powers0-Symplectic (₂₊ n)
    open Commuting-Symplectic (suc n)
  lemma-Ex-Ex↑-CZ'a {n@(suc _)} = begin
    (CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑) ↑ • CZ • (CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑) ↑ ≈⟨ (cright (cright lemma-cong↑ _ _ lemma-comm-Ex-CZ')) ⟩
    (CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑) ↑ • CZ • ((H ↓ • H ↑ • CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑) • CZ) ↑ ≈⟨ general-comm auto ⟩
    (((CZ • H • H ↑ • CZ • H ↑ • H • CZ) • H) • H ↑) ↑ • CZ • (H ↑ • (H ↓ • CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑ • CZ)) ↑ ≈⟨ cong (cleft (sym (lemma-cong↑ _ _ lemma-comm-Ex-H↑'))) (cright (cright lemma-cong↑ _ _ lemma-comm-Ex-H')) ⟩
    ((H ↑  • CZ • H ↑  • H • CZ • H ↑ • H • CZ) • H ↑) ↑ • CZ • (H ↑ • ((CZ • H ↑ • H • CZ • H • H ↑ • CZ) • H ↑)) ↑ ≈⟨ general-comm auto ⟩
    (H ↑  • CZ • H ↑  • H • CZ • H ↑ • H) ↑ • (CZ ↑ • H ↑ ↑ ^ 2) • CZ  • (((CZ • H ↑ • H • CZ • H • H ↑ • CZ) • H ↑)) ↑ ≈⟨ (cright (cleft axiom (cong↑ semi-CZ-HH↑))) ⟩
    (H ↑  • CZ • H ↑  • H • CZ • H ↑ • H) ↑ • (H ↑ ↑ ^ 2 • CZ ↑ ^ 2) • CZ  • (((CZ • H ↑ • H • CZ • H • H ↑ • CZ) • H ↑)) ↑ ≈⟨ general-comm auto ⟩
    (H ↑  • CZ • H ↑  • H • CZ • H ↑ • H) ↑ • (H ↑ ↑ ^ 2 • CZ ↑ ^ 3) • CZ  • ((( H ↑ • H • CZ • H • H ↑ • CZ) • H ↑)) ↑ ≈⟨ general-powers0 100 auto ⟩
    (H ↑  • CZ • H ↑  • H • CZ • H ↑ • H) ↑ • (H ↑ ↑ ^ 2) • CZ  • ((( H ↑ • H • CZ • H • H ↑ • CZ) • H ↑)) ↑ ≈⟨ general-comm auto ⟩
    (H ↑  • CZ • H ↑  • H • CZ • H) ↑ • (H ↑ ↑ ^ 4) • CZ  • (((H • CZ • H • H ↑ • CZ) • H ↑)) ↑ ≈⟨ general-powers0 100 auto ⟩
    (H ↑  • CZ • H ↑  • H • CZ • H) ↑ • CZ  • (((H • CZ • H • H ↑ • CZ) • H ↑)) ↑ ≈⟨ by-assoc auto ⟩
    ⊤⊥ ↑ • CZ ↓ • ⊥⊤ ↑ ∎
    where
    open PB ((₃₊ n) QRel,_===_)
    open PP ((₃₊ n) QRel,_===_)
    open SR word-setoid
    open Powers0-Symplectic (₂₊ n)
    open Commuting-Symplectic (suc n)
    


  lemma-Ex-Ex↑-CZ'b : let open PB ((₃₊ n) QRel,_===_) in
    Ex • CZ ↑ • Ex ≈ ⊥⊤ ↓ • CZ ↑ • ⊤⊥ ↓
  lemma-Ex-Ex↑-CZ'b {n} = begin
    Ex • CZ ↑ • Ex ≈⟨ refl ⟩
    (CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑) • CZ ↑ • (CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑) ≈⟨ (cright (cright lemma-comm-Ex-CZ')) ⟩
    (CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑) • CZ ↑  • ((H ↓ • H ↑ • CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑) • CZ) ≈⟨ general-comm auto ⟩
    (((CZ • H ↑ • H • CZ • H • H ↑ • CZ) • H ↑) • H) • CZ ↑ • (H • (H ↑  • CZ • H ↑  • H • CZ • H ↑  • H • CZ)) ≈⟨ cong (cleft sym lemma-comm-Ex-H') (cright (cright lemma-comm-Ex-H↑')) ⟩
    ((H ↓ • CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑ • CZ) • H) • CZ ↑ • (H • ((CZ • H • H ↑ • CZ • H ↑ • H • CZ) • H)) ≈⟨ general-comm auto ⟩
    (H ↓ • CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑) • (CZ • H ^ 2) • CZ ↑ • (((CZ • H • H ↑ • CZ • H ↑ • H • CZ) • H)) ≈⟨ (cright (cleft axiom semi-CZ-HH↓)) ⟩
    (H ↓ • CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑) • (H ^ 2 • CZ ^ 2) • CZ ↑ • (((CZ • H • H ↑ • CZ • H ↑ • H • CZ) • H)) ≈⟨ general-comm auto ⟩
    (H ↓ • CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑) • (H ^ 2 • CZ ^ 3) • CZ ↑ • (((H • H ↑ • CZ • H ↑ • H • CZ) • H)) ≈⟨ general-powers0 100 auto ⟩
    (H ↓ • CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑) • (H ^ 2) • CZ ↑ • (((H • H ↑ • CZ • H ↑ • H • CZ) • H)) ≈⟨ general-comm auto ⟩
    (H ↓ • CZ • H ↓ • H ↑ • CZ • H ↑) • (H ^ 4) • CZ ↑ • (((H ↑ • CZ • H ↑ • H • CZ) • H)) ≈⟨ general-powers0 100 auto ⟩
    ⊥⊤ ↓ • CZ ↑ • ⊤⊥ ↓ ∎
    where
    open PB ((₃₊ n) QRel,_===_)
    open PP ((₃₊ n) QRel,_===_)
    open SR word-setoid
    open Powers0-Symplectic (₂₊ n)
    open Commuting-Symplectic (suc n)



  lemma-CZ02-alt : let open PB ((₃₊ n) QRel,_===_) in
    Ex ↑ • CZ • Ex ↑ ≈ Ex • CZ ↑ • Ex
  lemma-CZ02-alt {n} = begin
    Ex ↑ • CZ • Ex ↑ ≈⟨ lemma-Ex-Ex↑-CZ'a ⟩
    ⊤⊥ ↑ • CZ ↓ • ⊥⊤ ↑ ≈⟨ axiom selinger-c13 ⟩
    ⊥⊤ ↓ • CZ ↑ • ⊤⊥ ↓ ≈⟨ sym lemma-Ex-Ex↑-CZ'b ⟩
    Ex • CZ ↑ • Ex ∎
    where
    open PB ((₃₊ n) QRel,_===_)
    open PP ((₃₊ n) QRel,_===_)
    open SR word-setoid
    open Powers0-Symplectic (₂₊ n)
    open Commuting-Symplectic (suc n)



module Symplectic-Powers where

  -- This module provides a rewrite system for reducing powers of
  -- Symplectic operators (for example, S⁴ → I). It also commutes
  -- generators on different qubits (for example, H1 H0 → H0 H1).
  -- Finally, it moves scalars to the end of the word. While this is
  -- not yet a very powerful rewrite system, it is a useful
  -- bootstrapping step.
  variable
    n : ℕ

  open Symplectic
  open Rewriting
  open Lemmas0 hiding (n)
  
  -- ----------------------------------------------------------------------
  -- * Lemmas

  -- The following lemmas are needed to justify the rewrite steps.

  -- ----------------------------------------------------------------------
  -- * Rewrite rules for monoidal structure and order of generators

  step-order : let open PB ((₁₊ n) QRel,_===_) hiding (_===_) in Step-Function (Gen (₁₊ n))  ((₁₊ n) QRel,_===_)

  -- Order of generators.
  step-order ((S-gen) ∷ (S-gen) ∷ (S-gen) ∷ xs) = just (xs , at-head (PB.axiom order-S))
  step-order ((S-gen ↥) ∷ (S-gen ↥) ∷ (S-gen ↥) ∷ xs) = just (xs , at-head (PB.axiom (cong↑ order-S)))
  step-order ((S-gen ↥ ↥) ∷ (S-gen ↥ ↥) ∷ (S-gen ↥ ↥) ∷ xs) = just (xs , at-head (PB.axiom (cong↑ (cong↑ order-S))))
  step-order ((H-gen) ∷ (H-gen) ∷ (H-gen) ∷ (H-gen) ∷ xs) = just (xs , at-head (PB.axiom order-H))
  step-order ((H-gen ↥) ∷ (H-gen ↥) ∷ (H-gen ↥) ∷ (H-gen ↥) ∷ xs) = just (xs , at-head (PB.axiom (cong↑ order-H)))
  step-order ((H-gen ↥ ↥) ∷ (H-gen ↥ ↥) ∷ (H-gen ↥ ↥) ∷ (H-gen ↥ ↥) ∷ xs) = just (xs , at-head (PB.axiom (cong↑ (cong↑ order-H))))
  step-order ((CZ-gen) ∷ (CZ-gen) ∷ (CZ-gen) ∷ xs) = just (xs , at-head (PB.axiom order-CZ))
  step-order ((CZ-gen ↥) ∷ (CZ-gen ↥) ∷ (CZ-gen ↥) ∷ xs) = just (xs , at-head (PB.axiom (cong↑ order-CZ)))

  step-order ((S-gen) ∷ (H-gen) ∷ (S-gen) ∷ (H-gen) ∷ (S-gen) ∷ (H-gen) ∷ xs) = just (xs , at-head (PB.axiom order-SH))
  step-order ((S-gen ↥) ∷ (H-gen ↥) ∷ (S-gen ↥) ∷ (H-gen ↥) ∷ (S-gen ↥) ∷ (H-gen ↥) ∷ xs) = just (xs , at-head (PB.axiom (cong↑ order-SH)))
  step-order ((S-gen ↥ ↥) ∷ (H-gen ↥ ↥) ∷ (S-gen ↥ ↥) ∷ (H-gen ↥ ↥) ∷ (S-gen ↥ ↥) ∷ (H-gen ↥ ↥) ∷ xs) = just (xs , at-head (PB.axiom (cong↑ (cong↑ order-SH))))

  step-order (CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ xs) = just (xs , at-head ( lemma-order-Ex))
  step-order (CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ xs) = just (xs , at-head ( (lemma-cong↑ _ _ lemma-order-Ex)))
  

  step-order ((H-gen) ∷ (CZ-gen) ∷ (H-gen) ∷ (H-gen) ∷ (CZ-gen) ∷ H-gen ∷ xs) = just (xs , at-head lemma-order-ₕ|ₕ)
  step-order ((H-gen ↥) ∷ (CZ-gen ↥) ∷ (H-gen ↥) ∷ (H-gen ↥) ∷ (CZ-gen ↥) ∷ H-gen ↥ ∷ xs) = just (xs , at-head (lemma-cong↑ _ _ lemma-order-ₕ|ₕ))

  step-order ((H-gen ↥) ∷ (CZ-gen) ∷ (H-gen ↥) ∷ (H-gen ↥) ∷ (CZ-gen) ∷ H-gen ↥ ∷ xs) = just (xs , at-head lemma-order-ʰ|ʰ)
  step-order ((H-gen ↥ ↥) ∷ (CZ-gen ↥) ∷ (H-gen ↥ ↥) ∷ (H-gen ↥ ↥) ∷ (CZ-gen ↥) ∷ H-gen ↥ ↥ ∷ xs) = just (xs , at-head (lemma-cong↑ _ _ lemma-order-ʰ|ʰ))

  -- Commuting of generators.

  -- Catch-all
  step-order _ = nothing

  -- From this rewrite relation, we extract a tactic 'general-powers'.
module Powers-Symplectic (n : ℕ) where
  open Symplectic
  open Rewriting
  open Symplectic-Powers hiding (n)
  open Rewriting.Step (step-cong (step-order {n})) renaming (general-rewrite to general-powers) public

-- ----------------------------------------------------------------------
-- * Lemmas

module Lemmas where
  open Lemmas0 hiding (n)
  variable
    n : ℕ

  open Symplectic
  open import Zp.ModularArithmetic


  lemma-Ex-Ex↑-CZ : let open PB ((₃₊ n) QRel,_===_) in
    Ex • Ex ↑ • CZ ≈ CZ ↑ • Ex • Ex ↑
  lemma-Ex-Ex↑-CZ {n} = begin
    Ex • Ex ↑ • CZ ≈⟨ general-powers 100 auto ⟩
    Ex • (Ex ↑ • CZ • Ex ↑) • Ex ↑ ≈⟨ cong refl (cong lemma-CZ02-alt refl) ⟩
    Ex • (Ex • CZ ↑ • Ex) • Ex ↑ ≈⟨ general-powers 100 auto ⟩
    CZ ↑ • Ex • Ex ↑ ∎
    where
    open PB ((₃₊ n) QRel,_===_)
    open PP ((₃₊ n) QRel,_===_)
    open SR word-setoid
    open Powers-Symplectic (₂₊ n)

  lemma-Ex-S : let open PB ((₂₊ n) QRel,_===_) in 
    
    Ex • S ≈ S ↑ • Ex
    
  lemma-Ex-S = PB.sym (lemma-comm-Ex-S)


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





  lemma-Ex-H : let open PB ((₂₊ n) QRel,_===_) in 
    
    Ex • H ≈ H ↑ • Ex
    
  lemma-Ex-H = PB.sym (lemma-comm-Ex-H)

  lemma-Ex-Hᵏ : ∀ k → let open PB ((₂₊ n) QRel,_===_) in 
    
    Ex • H ^ k ≈ H ↑ ^ k • Ex
    
  lemma-Ex-Hᵏ {n} ₀ = trans right-unit (sym left-unit)
    where
    open PB ((₂₊ n) QRel,_===_)
  lemma-Ex-Hᵏ {n} ₁ = lemma-Ex-H
  lemma-Ex-Hᵏ {n} (₂₊ k) = begin
    Ex • H • H ^ ₁₊ k ≈⟨ sym assoc ⟩
    (Ex • H) • H ^ ₁₊ k ≈⟨ cong lemma-Ex-H refl ⟩
    (H ↑ • Ex) • H ^ ₁₊ k ≈⟨ assoc ⟩
    H ↑ • Ex • H ^ ₁₊ k ≈⟨ cong refl (lemma-Ex-Hᵏ (₁₊ k)) ⟩
    H ↑ • H ↑ ^ ₁₊ k • Ex ≈⟨ sym assoc ⟩
    ((H ↑) • (H ↑) ^ ₁₊ k) • Ex ∎
    where
    open PB ((₂₊ n) QRel,_===_)
    open PP ((₂₊ n) QRel,_===_)
    open SR word-setoid

  lemma-Ex-Sᵏ : ∀ k → let open PB ((₂₊ n) QRel,_===_) in 
    
    Ex • S ^ k ≈ S ↑ ^ k • Ex
    
  lemma-Ex-Sᵏ {n} ₀ = trans right-unit (sym left-unit)
    where
    open PB ((₂₊ n) QRel,_===_)
  lemma-Ex-Sᵏ {n} ₁ = lemma-Ex-S
  lemma-Ex-Sᵏ {n} (₂₊ k) = begin
    Ex • S • S ^ ₁₊ k ≈⟨ sym assoc ⟩
    (Ex • S) • S ^ ₁₊ k ≈⟨ cong lemma-Ex-S refl ⟩
    (S ↑ • Ex) • S ^ ₁₊ k ≈⟨ assoc ⟩
    S ↑ • Ex • S ^ ₁₊ k ≈⟨ cong refl (lemma-Ex-Sᵏ (₁₊ k)) ⟩
    S ↑ • S ↑ ^ ₁₊ k • Ex ≈⟨ sym assoc ⟩
    ((S ↑) • (S ↑) ^ ₁₊ k) • Ex ∎
    where
    open PB ((₂₊ n) QRel,_===_)
    open PP ((₂₊ n) QRel,_===_)
    open SR word-setoid


  lemma-comm-H↑-Sᵏ : ∀ {n} k →
    let open PB ((₂₊ n) QRel,_===_) in
    
    H ↑ • S ^ k ≈ S ^ k • H ↑
    
  lemma-comm-H↑-Sᵏ {n} ₀ = trans right-unit (sym left-unit)
    where
    open PB ((₂₊ n) QRel,_===_)
    open PP ((₂₊ n) QRel,_===_)
    open SR word-setoid
  lemma-comm-H↑-Sᵏ {n} (₁) = axiom comm-S
    where
    open PB ((₂₊ n) QRel,_===_)
    open PP ((₂₊ n) QRel,_===_)
    open SR word-setoid
  lemma-comm-H↑-Sᵏ {n} (₂₊ k) = begin
    (H ↑) • S ^ ₂₊ k ≈⟨ refl ⟩
    (H ↑) • S • S ^ ₁₊ k ≈⟨ sym assoc ⟩
    (H ↑ • S) • S ^ ₁₊ k ≈⟨ cong (axiom comm-S) refl ⟩
    (S • H ↑) • S ^ ₁₊ k ≈⟨ assoc ⟩
    S • H ↑ • S ^ ₁₊ k ≈⟨ cong refl (lemma-comm-H↑-Sᵏ (₁₊ k)) ⟩
    S • S ^ ₁₊ k • H ↑ ≈⟨ sym assoc ⟩
    S ^ ₂₊ k • (H ↑) ∎
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


  lemma-comm-CZ-w↑↑ : ∀ {n} w → let open PB ((₂₊ n) QRel,_===_) in
    
    CZ • w ↑ ↑ ≈ w ↑ ↑ • CZ
    
  lemma-comm-CZ-w↑↑ {n} [ H-gen ]ʷ = PB.sym (PB.axiom comm-CZ)
  lemma-comm-CZ-w↑↑ {n} [ S-gen ]ʷ = PB.sym (PB.axiom comm-CZ)
  lemma-comm-CZ-w↑↑ {n} [ CZ-gen ]ʷ = PB.sym (PB.axiom comm-CZ)
  lemma-comm-CZ-w↑↑ {n} [ x ↥ ]ʷ = PB.sym (PB.axiom comm-CZ)
  lemma-comm-CZ-w↑↑ {n} ε = PB.trans PB.right-unit (PB.sym PB.left-unit)
  lemma-comm-CZ-w↑↑ {n} (w • v) = begin
    CZ • (((w • v) ↑) ↑) ≈⟨ refl ⟩
    CZ • w ↑ ↑ • v ↑ ↑ ≈⟨ sym assoc ⟩
    (CZ • w ↑ ↑) • v ↑ ↑ ≈⟨ cong (lemma-comm-CZ-w↑↑ w) refl ⟩
    (w ↑ ↑ • CZ) • v ↑ ↑ ≈⟨ assoc ⟩
    w ↑ ↑ • CZ • v ↑ ↑ ≈⟨ cong refl (lemma-comm-CZ-w↑↑ v) ⟩
    w ↑ ↑ • v ↑ ↑ • CZ ≈⟨ sym assoc ⟩
    (((w • v) ↑) ↑) • CZ ∎
    where
    open PB ((₂₊ n) QRel,_===_)
    open PP ((₂₊ n) QRel,_===_)
    open SR word-setoid



  lemma-comm-S-w↑↑ : ∀ {n} w → let open PB ((₂₊ n) QRel,_===_) in
    
    S • w ↑ ↑ ≈ w ↑ ↑ • S
    
  lemma-comm-S-w↑↑ {n} [ H-gen ]ʷ = PB.sym (PB.axiom comm-S)
  lemma-comm-S-w↑↑ {n} [ S-gen ]ʷ = PB.sym (PB.axiom comm-S)
  lemma-comm-S-w↑↑ {n} [ CZ-gen ]ʷ = PB.sym (PB.axiom comm-S)
  lemma-comm-S-w↑↑ {n} [ x ↥ ]ʷ = PB.sym (PB.axiom comm-S)
  lemma-comm-S-w↑↑ {n} ε = PB.trans PB.right-unit (PB.sym PB.left-unit)
  lemma-comm-S-w↑↑ {n} (w • v) = begin
    S • (((w • v) ↑) ↑) ≈⟨ refl ⟩
    S • w ↑ ↑ • v ↑ ↑ ≈⟨ sym assoc ⟩
    (S • w ↑ ↑) • v ↑ ↑ ≈⟨ cong (lemma-comm-S-w↑↑ w) refl ⟩
    (w ↑ ↑ • S) • v ↑ ↑ ≈⟨ assoc ⟩
    w ↑ ↑ • S • v ↑ ↑ ≈⟨ cong refl (lemma-comm-S-w↑↑ v) ⟩
    w ↑ ↑ • v ↑ ↑ • S ≈⟨ sym assoc ⟩
    (((w • v) ↑) ↑) • S ∎
    where
    open PB ((₂₊ n) QRel,_===_)
    open PP ((₂₊ n) QRel,_===_)
    open SR word-setoid


  lemma-comm-H-w↑↑ : ∀ {n} w → let open PB ((₂₊ n) QRel,_===_) in
    
    H • w ↑ ↑ ≈ w ↑ ↑ • H
    
  lemma-comm-H-w↑↑ {n} [ H-gen ]ʷ = PB.sym (PB.axiom comm-H)
  lemma-comm-H-w↑↑ {n} [ S-gen ]ʷ = PB.sym (PB.axiom comm-H)
  lemma-comm-H-w↑↑ {n} [ CZ-gen ]ʷ = PB.sym (PB.axiom comm-H)
  lemma-comm-H-w↑↑ {n} [ x ↥ ]ʷ = PB.sym (PB.axiom comm-H)
  lemma-comm-H-w↑↑ {n} ε = PB.trans PB.right-unit (PB.sym PB.left-unit)
  lemma-comm-H-w↑↑ {n} (w • v) = begin
    H • (((w • v) ↑) ↑) ≈⟨ refl ⟩
    H • w ↑ ↑ • v ↑ ↑ ≈⟨ sym assoc ⟩
    (H • w ↑ ↑) • v ↑ ↑ ≈⟨ cong (lemma-comm-H-w↑↑ w) refl ⟩
    (w ↑ ↑ • H) • v ↑ ↑ ≈⟨ assoc ⟩
    w ↑ ↑ • H • v ↑ ↑ ≈⟨ cong refl (lemma-comm-H-w↑↑ v) ⟩
    w ↑ ↑ • v ↑ ↑ • H ≈⟨ sym assoc ⟩
    (((w • v) ↑) ↑) • H ∎
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


  lemma-comm-CZᵏ-w↑↑ : ∀ {n} k w → let open PB ((₂₊ n) QRel,_===_) in
    
    CZ ^ k • w ↑ ↑ ≈ w ↑ ↑ • CZ ^ k
    
  lemma-comm-CZᵏ-w↑↑ {n} ₀ w = trans left-unit (sym right-unit)
    where
    open PB ((₂₊ n) QRel,_===_)
  lemma-comm-CZᵏ-w↑↑ {n} ₁ w = lemma-comm-CZ-w↑↑ w
    where
    open PB ((₂₊ n) QRel,_===_)
  lemma-comm-CZᵏ-w↑↑ {n} (₂₊ k) w = begin
    (CZ • CZ ^ ₁₊ k) • (w ↑ ↑) ≈⟨ assoc ⟩
    CZ • CZ ^ ₁₊ k • (w ↑ ↑) ≈⟨ cong refl (lemma-comm-CZᵏ-w↑↑ (₁₊ k) w) ⟩
    CZ • (w ↑ ↑) • CZ ^ ₁₊ k ≈⟨ sym assoc ⟩
    (CZ • w ↑ ↑) • CZ ^ ₁₊ k ≈⟨ cong (lemma-comm-CZ-w↑↑ w) refl ⟩
    (w ↑ ↑ • CZ) • CZ ^ ₁₊ k ≈⟨ assoc ⟩
    (w ↑ ↑) • CZ • CZ ^ ₁₊ k ∎
    where
    open PB ((₂₊ n) QRel,_===_)
    open PP ((₂₊ n) QRel,_===_)
    open SR word-setoid

  lemma-comm-Sᵏ-w↑↑ : ∀ {n} k w → let open PB ((₂₊ n) QRel,_===_) in
    
    S ^ k • w ↑ ↑ ≈ w ↑ ↑ • S ^ k
    
  lemma-comm-Sᵏ-w↑↑ {n} ₀ w = trans left-unit (sym right-unit)
    where
    open PB ((₂₊ n) QRel,_===_)
  lemma-comm-Sᵏ-w↑↑ {n} ₁ w = lemma-comm-S-w↑↑ w
    where
    open PB ((₂₊ n) QRel,_===_)
  lemma-comm-Sᵏ-w↑↑ {n} (₂₊ k) w = begin
    (S • S ^ ₁₊ k) • (w ↑ ↑) ≈⟨ assoc ⟩
    S • S ^ ₁₊ k • (w ↑ ↑) ≈⟨ cong refl (lemma-comm-Sᵏ-w↑↑ (₁₊ k) w) ⟩
    S • (w ↑ ↑) • S ^ ₁₊ k ≈⟨ sym assoc ⟩
    (S • w ↑ ↑) • S ^ ₁₊ k ≈⟨ cong (lemma-comm-S-w↑↑ w) refl ⟩
    (w ↑ ↑ • S) • S ^ ₁₊ k ≈⟨ assoc ⟩
    (w ↑ ↑) • S • S ^ ₁₊ k ∎
    where
    open PB ((₂₊ n) QRel,_===_)
    open PP ((₂₊ n) QRel,_===_)
    open SR word-setoid

  lemma-comm-Hᵏ-w↑↑ : ∀ {n} k w → let open PB ((₂₊ n) QRel,_===_) in
    
    H ^ k • w ↑ ↑ ≈ w ↑ ↑ • H ^ k
    
  lemma-comm-Hᵏ-w↑↑ {n} ₀ w = trans left-unit (sym right-unit)
    where
    open PB ((₂₊ n) QRel,_===_)
  lemma-comm-Hᵏ-w↑↑ {n} ₁ w = lemma-comm-H-w↑↑ w
    where
    open PB ((₂₊ n) QRel,_===_)
  lemma-comm-Hᵏ-w↑↑ {n} (₂₊ k) w = begin
    (H • H ^ ₁₊ k) • (w ↑ ↑) ≈⟨ assoc ⟩
    H • H ^ ₁₊ k • (w ↑ ↑) ≈⟨ cong refl (lemma-comm-Hᵏ-w↑↑ (₁₊ k) w) ⟩
    H • (w ↑ ↑) • H ^ ₁₊ k ≈⟨ sym assoc ⟩
    (H • w ↑ ↑) • H ^ ₁₊ k ≈⟨ cong (lemma-comm-H-w↑↑ w) refl ⟩
    (w ↑ ↑ • H) • H ^ ₁₊ k ≈⟨ assoc ⟩
    (w ↑ ↑) • H • H ^ ₁₊ k ∎
    where
    open PB ((₂₊ n) QRel,_===_)
    open PP ((₂₊ n) QRel,_===_)
    open SR word-setoid


  lemma-CZᵏ-H↑² : ∀ k → let open PB ((₂₊ n) QRel,_===_) in
    
    CZ ^ toℕ k • H ↑ ^ 2 ≈ H ↑ ^ 2 • CZ ^ toℕ (- k)
    
  lemma-CZᵏ-H↑² {n} ₀ = trans left-unit (sym right-unit)
    where open PB ((₂₊ n) QRel,_===_)
  lemma-CZᵏ-H↑² {n} ₁ = axiom semi-CZ-HH↑
    where open PB ((₂₊ n) QRel,_===_)
  lemma-CZᵏ-H↑² {n} ₂ = begin
    CZ ^ 2 • H ↑ ^ 2 ≈⟨ by-assoc auto ⟩
    CZ • (CZ • H ↑ ^ 2) ≈⟨ cong refl (axiom semi-CZ-HH↑) ⟩
    CZ • (H ↑ ^ 2 • CZ ^ 2) ≈⟨ sym assoc ⟩
    (CZ • H ↑ ^ 2) • CZ ^ 2 ≈⟨ cong (axiom semi-CZ-HH↑) refl ⟩
    (H ↑ ^ 2 • CZ ^ 2) • CZ ^ 2 ≈⟨ by-assoc auto  ⟩
    (H ↑ ^ 2 • CZ) • CZ ^ 3 ≈⟨ cong refl (axiom order-CZ) ⟩
    (H ↑ ^ 2 • CZ) • ε ≈⟨ right-unit ⟩
    ((H ↑) • (H ↑)) • CZ ∎
    where
    open PB ((₂₊ n) QRel,_===_)
    open PP ((₂₊ n) QRel,_===_)
    open SR word-setoid

  aux-e+0 : ∀ e → e + ₀ ≡ e
  aux-e+0 ₀ = auto
  aux-e+0 ₁ = auto
  aux-e+0 ₂ = auto

  lemma-^-↑ : ∀ (w : Word (Gen n)) k → w ↑ ^ k ≡ (w ^ k) ↑
  lemma-^-↑ w ₀ = auto
  lemma-^-↑ w ₁ = auto
  lemma-^-↑ w (₂₊ k) = begin
    (w ↑) • (w ↑) ^ ₁₊ k ≡⟨ Eq.cong ((w ↑) •_) (lemma-^-↑ w (suc k)) ⟩
    (w ↑) • (w ^ ₁₊ k) ↑ ≡⟨ auto ⟩
    ((w • w ^ ₁₊ k) ↑) ∎
    where open ≡-Reasoning


  lemma-Ex-HᵏSˡ : let open PB ((₂₊ n) QRel,_===_) in ∀ k l →
    
    Ex • (H ^ k • S ^ l) ≈ (H ^ k • S ^ l) ↑ • Ex
    
  lemma-Ex-HᵏSˡ {n} k l = begin
    Ex • H ^ k • S ^ l ≈⟨ sym assoc ⟩
    (Ex • H ^ k) • S ^ l ≈⟨ cong (lemma-Ex-Hᵏ k) refl ⟩
    (H ↑ ^ k • Ex) • S ^ l ≈⟨ assoc ⟩
    H ↑ ^ k • Ex • S ^ l ≈⟨ cong refl (lemma-Ex-Sᵏ l) ⟩
    H ↑ ^ k • S ↑ ^ l • Ex ≈⟨ sym assoc ⟩
    (H ↑ ^ k • S ↑ ^ l) • Ex ≈⟨ cong (cong (refl' (lemma-^-↑ H k)) (refl' (lemma-^-↑ S l))) refl ⟩
    ((H ^ k) ↑ • (S ^ l) ↑) • Ex ≈⟨ cong refl refl ⟩
    ((H ) ^ k • (S ) ^ l) ↑ • Ex ∎
    where
    open PB ((₂₊ n) QRel,_===_)
    open PP ((₂₊ n) QRel,_===_)
    open SR word-setoid


-- ----------------------------------------------------------------------
-- * Lemmas

module Lemmas2 where
  open Lemmas0 hiding (n)

  variable
    n : ℕ

  open Symplectic
  open import Zp.ModularArithmetic


  lemma-Ex-H↑ : let open PB ((₂₊ n) QRel,_===_) in

    Ex • H ↑ ≈ H • Ex

  lemma-Ex-H↑ {n} = begin
    Ex • (H ↑) ≈⟨ sym right-unit ⟩
    (Ex • (H ↑)) • ε ≈⟨ (cright sym lemma-order-Ex) ⟩
    (Ex • (H ↑)) • Ex ^ 2 ≈⟨ by-assoc auto ⟩
    Ex • (H ↑ • Ex) • Ex ≈⟨ cong refl (cong (lemma-comm-Ex-H) refl) ⟩
    Ex • (Ex • H) • Ex ≈⟨ by-assoc auto ⟩
    (Ex • Ex) • H • Ex ≈⟨ cong lemma-order-Ex refl ⟩
    ε • H • Ex ≈⟨ left-unit ⟩
    H • Ex ∎
    where
    open PB ((₂₊ n) QRel,_===_)
    open PP ((₂₊ n) QRel,_===_)
    open SR word-setoid
    open Powers-Symplectic (₁₊ n)

  lemma-Ex-S↑ : let open PB ((₂₊ n) QRel,_===_) in

    Ex • S ↑ ≈ S • Ex

  lemma-Ex-S↑ {n} = begin
    Ex • (S ↑) ≈⟨ sym right-unit ⟩
    (Ex • (S ↑)) • ε ≈⟨ (cright sym lemma-order-Ex) ⟩
    (Ex • (S ↑)) • Ex ^ 2 ≈⟨ by-assoc auto ⟩
    Ex • (S ↑ • Ex) • Ex ≈⟨ cong refl (cong (lemma-comm-Ex-S) refl) ⟩
    Ex • (Ex • S) • Ex ≈⟨ by-assoc auto ⟩
    (Ex • Ex) • S • Ex ≈⟨ cong lemma-order-Ex refl ⟩
    ε • S • Ex ≈⟨ left-unit ⟩
    S • Ex ∎
    where
    open PB ((₂₊ n) QRel,_===_)
    open PP ((₂₊ n) QRel,_===_)
    open SR word-setoid
    open Powers-Symplectic (₁₊ n)



  lemma-CZᵏ-S↑ : let open PB ((₂₊ n) QRel,_===_) in ∀  k →

    CZ ^ k • S ↑ ≈ S ↑ • CZ ^ k
    
  lemma-CZᵏ-S↑ {n} ₀ = PB.trans PB.left-unit (PB.sym PB.right-unit)
  lemma-CZᵏ-S↑ {n} ₁ = PB.axiom comm-CZ-S↑
  lemma-CZᵏ-S↑ {n} (₂₊ k) = begin
    (CZ • CZ ^ ₁₊ k) • (S ↑) ≈⟨ assoc ⟩
    CZ • CZ ^ ₁₊ k • (S ↑) ≈⟨ cong refl (lemma-CZᵏ-S↑ (₁₊ k)) ⟩
    CZ • (S ↑) • CZ ^ ₁₊ k ≈⟨ sym assoc ⟩
    (CZ • S ↑) • CZ ^ ₁₊ k ≈⟨ cong (axiom comm-CZ-S↑) refl ⟩
    (S ↑ • CZ) • CZ ^ ₁₊ k ≈⟨ assoc ⟩
    (S ↑) • CZ • CZ ^ ₁₊ k ∎
    where
    open PB ((₂₊ n) QRel,_===_)
    open PP ((₂₊ n) QRel,_===_)
    open SR word-setoid
    open Powers-Symplectic (₁₊ n)

  lemma-CZᵏ-S↑² : let open PB ((₂₊ n) QRel,_===_) in ∀  k →

    CZ ^ k • S ↑ ^ 2 ≈ S ↑ ^ 2 • CZ ^ k
    
  lemma-CZᵏ-S↑² {n} k = begin
    CZ ^ k • (S ↑) • (S ↑) ≈⟨ sym assoc ⟩
    (CZ ^ k • S ↑) • (S ↑) ≈⟨ cong (lemma-CZᵏ-S↑ k) refl ⟩
    (S ↑ • CZ ^ k) • (S ↑) ≈⟨ assoc ⟩
    S ↑ • CZ ^ k • (S ↑) ≈⟨ cong refl (lemma-CZᵏ-S↑ k) ⟩
    S ↑ • (S ↑) • CZ ^ k ≈⟨ sym assoc ⟩
    ((S ↑) • (S ↑)) • CZ ^ k ∎
    where
    open PB ((₂₊ n) QRel,_===_)
    open PP ((₂₊ n) QRel,_===_)
    open SR word-setoid
    open Powers-Symplectic (₁₊ n)

  lemma-CZᵏ-Ex : let open PB ((₂₊ n) QRel,_===_) in ∀  k →

    CZ ^ k • Ex ≈ Ex • CZ ^ k
    
  lemma-CZᵏ-Ex {n} ₀ = PB.trans PB.left-unit (PB.sym PB.right-unit)
  lemma-CZᵏ-Ex {n} ₁ = lemma-comm-Ex-CZ
  lemma-CZᵏ-Ex {n} (₂₊ k) = begin
    (CZ • CZ ^ ₁₊ k) • (Ex) ≈⟨ assoc ⟩
    CZ • CZ ^ ₁₊ k • (Ex) ≈⟨ cong refl (lemma-CZᵏ-Ex (₁₊ k)) ⟩
    CZ • (Ex) • CZ ^ ₁₊ k ≈⟨ sym assoc ⟩
    (CZ • Ex) • CZ ^ ₁₊ k ≈⟨ cong (lemma-comm-Ex-CZ) refl ⟩
    (Ex • CZ) • CZ ^ ₁₊ k ≈⟨ assoc ⟩
    (Ex) • CZ • CZ ^ ₁₊ k ∎
    where
    open PB ((₂₊ n) QRel,_===_)
    open PP ((₂₊ n) QRel,_===_)
    open SR word-setoid
    open Powers-Symplectic (₁₊ n)


  lemma-CZᵏ-CZ↑ : let open PB ((₃₊ n) QRel,_===_) in ∀  k →

    CZ ^ k • CZ ↑ ≈ CZ ↑ • CZ ^ k
    
  lemma-CZᵏ-CZ↑ {n} ₀ = PB.trans PB.left-unit (PB.sym PB.right-unit)
  lemma-CZᵏ-CZ↑ {n} ₁ = PB.sym (PB.axiom selinger-c12)
  lemma-CZᵏ-CZ↑ {n} (₂₊ k) = begin
    (CZ • CZ ^ ₁₊ k) • (CZ ↑) ≈⟨ assoc ⟩
    CZ • CZ ^ ₁₊ k • (CZ ↑) ≈⟨ cong refl (lemma-CZᵏ-CZ↑ (₁₊ k)) ⟩
    CZ • (CZ ↑) • CZ ^ ₁₊ k ≈⟨ sym assoc ⟩
    (CZ • CZ ↑) • CZ ^ ₁₊ k ≈⟨ sym (cong (axiom selinger-c12) refl) ⟩
    (CZ ↑ • CZ) • CZ ^ ₁₊ k ≈⟨ assoc ⟩
    (CZ ↑) • CZ • CZ ^ ₁₊ k ∎
    where
    open PB ((₃₊ n) QRel,_===_)
    open PP ((₃₊ n) QRel,_===_)
    open SR word-setoid
    open Powers-Symplectic (₂₊ n)


  lemma-CZᵏ↑-CZ : let open PB ((₃₊ n) QRel,_===_) in ∀  k →

    (CZ ^ k) ↑ • CZ ≈ CZ • (CZ ^ k) ↑
    
  lemma-CZᵏ↑-CZ {n} ₀ = PB.trans PB.left-unit (PB.sym PB.right-unit)
  lemma-CZᵏ↑-CZ {n} ₁ = PB.axiom selinger-c12
  lemma-CZᵏ↑-CZ {n} (₂₊ k) = begin
    (CZ • CZ ^ ₁₊ k) ↑ • (CZ) ≈⟨ assoc ⟩
    CZ ↑ • (CZ ^ ₁₊ k) ↑ • (CZ) ≈⟨ cong refl (lemma-CZᵏ↑-CZ (₁₊ k)) ⟩
    CZ ↑ • (CZ) • (CZ ^ ₁₊ k) ↑ ≈⟨ sym assoc ⟩
    (CZ ↑ • CZ) • (CZ ^ ₁₊ k) ↑ ≈⟨ cong (axiom selinger-c12) refl ⟩
    (CZ • CZ ↑) • (CZ ^ ₁₊ k) ↑ ≈⟨ assoc ⟩
    (CZ) • (CZ • CZ ^ ₁₊ k) ↑ ∎
    where
    open PB ((₃₊ n) QRel,_===_)
    open PP ((₃₊ n) QRel,_===_)
    open SR word-setoid
    open Powers-Symplectic (₂₊ n)


  lemma-CZᵏ-HH↑ : let open PB ((₂₊ n) QRel,_===_) in ∀  k →

    CZ ^ toℕ k • H ↑ ^ 2 ≈ H ↑ ^ 2 • CZ ^ toℕ (- k)
    
  lemma-CZᵏ-HH↑ {n} ₀ = PB.trans PB.left-unit (PB.sym PB.right-unit)
  lemma-CZᵏ-HH↑ {n} ₁ = PB.axiom semi-CZ-HH↑
  lemma-CZᵏ-HH↑ {n} ₂ = begin
    (CZ • CZ) • (H ↑) • (H ↑) ≈⟨ assoc ⟩
    CZ • CZ • (H ↑) • (H ↑) ≈⟨ cong refl (trans (axiom semi-CZ-HH↑) assoc) ⟩
    CZ • (H ↑) • (H ↑) • CZ ^ 2 ≈⟨ by-assoc auto ⟩
    (CZ • (H ↑) • (H ↑)) • CZ ^ 2 ≈⟨ cong (trans (axiom semi-CZ-HH↑) assoc) refl ⟩
    ((H ↑) • (H ↑) • CZ ^ 2) • CZ ^ 2 ≈⟨ general-powers 100 auto ⟩
    ((H ↑) • (H ↑)) • CZ ∎
    where
    open PB ((₂₊ n) QRel,_===_)
    open PP ((₂₊ n) QRel,_===_)
    open SR word-setoid
    open Powers-Symplectic (₁₊ n)

  open Lemmas hiding (n)
  
  lemma-Ex-HᵏSˡ' : let open PB ((₂₊ n) QRel,_===_) in ∀ k l →
    
    Ex • (H ^ k • S ^ l) ↑ ≈ (H ^ k • S ^ l) • Ex
    
  lemma-Ex-HᵏSˡ' {n} k l = begin
    Ex • ((H ^ k • S ^ l) ↑) ≈⟨ cong refl (sym right-unit) ⟩
    Ex • (H ^ k • S ^ l) ↑ • ε ≈⟨ cong refl (cong refl (general-powers 100 auto)) ⟩
    Ex • (H ^ k • S ^ l) ↑ • Ex • Ex ≈⟨ sym (cong refl assoc) ⟩
    Ex • ((H ^ k • S ^ l) ↑ • Ex) • Ex ≈⟨ cong refl (cong (sym (lemma-Ex-HᵏSˡ k l)) refl) ⟩
    Ex • (Ex • (H ^ k • S ^ l)) • Ex ≈⟨ cong refl assoc ⟩
    Ex • Ex • (H ^ k • S ^ l) • Ex ≈⟨ sym assoc ⟩
    (Ex • Ex) • (H ^ k • S ^ l) • Ex ≈⟨ cong (general-powers 100 auto) refl ⟩
    ε • (H ^ k • S ^ l) • Ex ≈⟨ left-unit ⟩
    (H ^ k • S ^ l) • Ex ∎
    where
    open PB ((₂₊ n) QRel,_===_)
    open PP ((₂₊ n) QRel,_===_)
    open SR word-setoid
    open Powers-Symplectic (₁₊ n)

  lemma-Ex-Sᵏ↑ : ∀ k → let open PB ((₂₊ n) QRel,_===_) in 
    
    Ex • (S ^ k) ↑ ≈ (S ^ k) • Ex
    
  lemma-Ex-Sᵏ↑ {n} k = begin
    Ex • ((S ^ k) ↑) ≈⟨ cong refl (sym right-unit) ⟩
    Ex • (S ^ k) ↑ • ε ≈⟨ cong refl (cong refl (general-powers 100 auto)) ⟩
    Ex • (S ^ k) ↑ • Ex • Ex ≈⟨ sym (cong refl assoc) ⟩
    Ex • ((S ^ k) ↑ • Ex) • Ex ≈⟨ (cright (cleft (cleft sym (refl' (lemma-^-↑ S k))))) ⟩
    Ex • ((S ↑ ^ k) • Ex) • Ex ≈⟨ cong refl (cong (sym (lemma-Ex-Sᵏ k)) refl) ⟩
    Ex • (Ex • (S ^ k)) • Ex ≈⟨ cong refl assoc ⟩
    Ex • Ex • (S ^ k) • Ex ≈⟨ sym assoc ⟩
    (Ex • Ex) • (S ^ k) • Ex ≈⟨ cong (general-powers 100 auto) refl ⟩
    ε • (S ^ k) • Ex ≈⟨ left-unit ⟩
    (S ^ k) • Ex ∎
    where
    open PB ((₂₊ n) QRel,_===_)
    open PP ((₂₊ n) QRel,_===_)
    open SR word-setoid
    open Powers-Symplectic (₁₊ n)


  lemma-Ex-S↑ᵏ : ∀ k → let open PB ((₂₊ n) QRel,_===_) in 
    
    Ex • (S ↑ ^ k) ≈ (S ^ k) • Ex
    
  lemma-Ex-S↑ᵏ {n} k = begin
    Ex • (S ↑ ^ k) ≈⟨ refl' (Eq.cong (\ xx -> Ex • xx) (lemma-^-↑ S k)) ⟩
    Ex • (S ^ k) ↑ ≈⟨ lemma-Ex-Sᵏ↑ k ⟩
    (S ^ k) • Ex ∎
    where
    open PB ((₂₊ n) QRel,_===_)
    open PP ((₂₊ n) QRel,_===_)
    open SR word-setoid
    open Powers-Symplectic (₁₊ n)




module Symplectic-Rewriting where

  -- This module provides a complete rewrite system for 1-qubit
  -- Symplectic operators. It is specialized toward relations on qubit 0
  -- (but can also be applied to qubit 1 via duality).
  variable
    n : ℕ

  open Symplectic
  open Rewriting
  open Lemmas0 hiding (n)
  open Lemmas2 hiding (n)
  
  -- ----------------------------------------------------------------------
  -- * Rewrite rules for 1-qubit Symplectic relations
  
  step-symplectic : let open PB ((₁₊ n) QRel,_===_) hiding (_===_) in Step-Function (Gen (₁₊ n))  ((₁₊ n) QRel,_===_)

  -- Order of generators.
  step-symplectic ((S-gen) ∷ (S-gen) ∷ (S-gen) ∷ xs) = just (xs , at-head (PB.axiom order-S))
  step-symplectic ((S-gen ↥) ∷ (S-gen ↥) ∷ (S-gen ↥) ∷ xs) = just (xs , at-head (PB.axiom (cong↑ order-S)))
  step-symplectic ((S-gen ↥ ↥) ∷ (S-gen ↥ ↥) ∷ (S-gen ↥ ↥) ∷ xs) = just (xs , at-head (PB.axiom (cong↑ (cong↑ order-S))))
  step-symplectic ((H-gen) ∷ (H-gen) ∷ (H-gen) ∷ (H-gen) ∷ xs) = just (xs , at-head (PB.axiom order-H))
  step-symplectic ((H-gen ↥) ∷ (H-gen ↥) ∷ (H-gen ↥) ∷ (H-gen ↥) ∷ xs) = just (xs , at-head (PB.axiom (cong↑ order-H)))
  step-symplectic ((H-gen ↥ ↥) ∷ (H-gen ↥ ↥) ∷ (H-gen ↥ ↥) ∷ (H-gen ↥ ↥) ∷ xs) = just (xs , at-head (PB.axiom (cong↑ (cong↑ order-H))))
  step-symplectic ((CZ-gen) ∷ (CZ-gen) ∷ (CZ-gen) ∷ xs) = just (xs , at-head (PB.axiom order-CZ))
  step-symplectic ((CZ-gen ↥) ∷ (CZ-gen ↥) ∷ (CZ-gen ↥) ∷ xs) = just (xs , at-head (PB.axiom (cong↑ order-CZ)))

  step-symplectic ((S-gen) ∷ (H-gen) ∷ (S-gen) ∷ (H-gen) ∷ (S-gen) ∷ (H-gen) ∷ xs) = just (xs , at-head (PB.axiom order-SH))
  step-symplectic ((S-gen ↥) ∷ (H-gen ↥) ∷ (S-gen ↥) ∷ (H-gen ↥) ∷ (S-gen ↥) ∷ (H-gen ↥) ∷ xs) = just (xs , at-head (PB.axiom (cong↑ order-SH)))
  step-symplectic ((S-gen ↥ ↥) ∷ (H-gen ↥ ↥) ∷ (S-gen ↥ ↥) ∷ (H-gen ↥ ↥) ∷ (S-gen ↥ ↥) ∷ (H-gen ↥ ↥) ∷ xs) = just (xs , at-head (PB.axiom (cong↑ (cong↑ order-SH))))

  step-symplectic (CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ xs) = just (xs , at-head (lemma-order-Ex))
  step-symplectic (CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ xs) = just (xs , at-head ( (lemma-cong↑ _ _ lemma-order-Ex)))

  -- Commuting of generators.
  step-symplectic ((S-gen) ∷ (CZ-gen) ∷ xs) = just ((CZ-gen) ∷ (S-gen) ∷ xs , at-head (PB.sym (PB.axiom comm-CZ-S↓)))
  step-symplectic ((S-gen ↥) ∷ (CZ-gen) ∷ xs) = just ((CZ-gen) ∷ (S-gen ↥) ∷ xs , at-head (PB.sym (PB.axiom comm-CZ-S↑)))
  step-symplectic ((S-gen ↥) ∷ (CZ-gen ↥) ∷ xs) = just ((CZ-gen ↥) ∷ (S-gen ↥) ∷ xs , at-head (PB.sym (PB.axiom (cong↑ comm-CZ-S↓))))
  step-symplectic ((S-gen ↥ ↥) ∷ (CZ-gen ↥) ∷ xs) = just ((CZ-gen ↥) ∷ (S-gen ↥ ↥) ∷ xs , at-head (PB.sym (PB.axiom (cong↑ comm-CZ-S↑))))

  step-symplectic ((H-gen ↥ ↥) ∷ (CZ-gen) ∷ xs) = just ((CZ-gen) ∷ (H-gen ↥ ↥) ∷ xs , at-head (PB.axiom comm-CZ))
  step-symplectic ((S-gen ↥ ↥) ∷ (CZ-gen) ∷ xs) = just ((CZ-gen) ∷ (S-gen ↥ ↥) ∷ xs , at-head (PB.axiom comm-CZ))

  step-symplectic ((S-gen ↥) ∷ (S-gen) ∷ xs) = just ((S-gen) ∷ (S-gen ↥) ∷ xs , at-head ((PB.axiom comm-S)))
  step-symplectic ((S-gen ↥ ↥) ∷ (S-gen ↥) ∷ xs) = just ((S-gen ↥) ∷ (S-gen ↥ ↥) ∷ xs , at-head ((PB.axiom (cong↑ comm-S))))
  step-symplectic ((S-gen ↥ ↥) ∷ (S-gen) ∷ xs) = just ((S-gen) ∷ (S-gen ↥ ↥) ∷ xs , at-head (PB.axiom comm-S))
  step-symplectic ((S-gen ↥) ∷ (H-gen) ∷ xs) = just ((H-gen) ∷ (S-gen ↥) ∷ xs , at-head ((PB.axiom comm-H)))
  step-symplectic ((S-gen ↥ ↥) ∷ (H-gen ↥) ∷ xs) = just ((H-gen ↥) ∷ (S-gen ↥ ↥) ∷ xs , at-head ((PB.axiom (cong↑ comm-H))))
  step-symplectic ((S-gen ↥ ↥) ∷ (H-gen) ∷ xs) = just ((H-gen) ∷ (S-gen ↥ ↥) ∷ xs , at-head (PB.axiom comm-H))
  step-symplectic ((H-gen ↥) ∷ (H-gen) ∷ xs) = just ((H-gen) ∷ (H-gen ↥) ∷ xs , at-head ((PB.axiom comm-H)))
  step-symplectic ((H-gen ↥) ∷ (S-gen) ∷ xs) = just ((S-gen) ∷ (H-gen ↥) ∷ xs , at-head ((PB.axiom comm-S)))
  step-symplectic ((H-gen ↥ ↥) ∷ (H-gen ↥) ∷ xs) = just ((H-gen ↥) ∷ (H-gen ↥ ↥) ∷ xs , at-head ((PB.axiom (cong↑ comm-H))))
  step-symplectic ((H-gen ↥ ↥) ∷ (H-gen) ∷ xs) = just ((H-gen) ∷ (H-gen ↥ ↥) ∷ xs , at-head (PB.axiom comm-H))
  step-symplectic ((H-gen ↥ ↥) ∷ (S-gen ↥) ∷ xs) = just ((S-gen ↥) ∷ (H-gen ↥ ↥) ∷ xs , at-head ((PB.axiom (cong↑ comm-S))))
  step-symplectic ((H-gen ↥ ↥) ∷ (S-gen) ∷ xs) = just ((S-gen) ∷ (H-gen ↥ ↥) ∷ xs , at-head (PB.axiom comm-S))

  step-symplectic ((CZ-gen ↥ ↥) ∷ (H-gen ↥) ∷ xs) = just ((H-gen ↥) ∷ (CZ-gen ↥ ↥) ∷ xs , at-head ((PB.axiom (cong↑ comm-H))))
  step-symplectic ((CZ-gen ↥ ↥) ∷ (H-gen) ∷ xs) = just ((H-gen) ∷ (CZ-gen ↥ ↥) ∷ xs , at-head (PB.axiom comm-H))
  step-symplectic ((CZ-gen ↥ ↥) ∷ (S-gen ↥) ∷ xs) = just ((S-gen ↥) ∷ (CZ-gen ↥ ↥) ∷ xs , at-head ((PB.axiom (cong↑ comm-S))))
  step-symplectic ((CZ-gen ↥ ↥) ∷ (S-gen) ∷ xs) = just ((S-gen) ∷ (CZ-gen ↥ ↥) ∷ xs , at-head (PB.axiom comm-S))

  step-symplectic ((CZ-gen ↥ ↥) ∷ (CZ-gen) ∷ xs) = just ((CZ-gen) ∷ (CZ-gen ↥ ↥) ∷ xs , at-head ((PB.axiom comm-CZ)))
  step-symplectic ((CZ-gen ↥) ∷ (CZ-gen) ∷ xs) = just ((CZ-gen) ∷ (CZ-gen ↥) ∷ xs , at-head ((PB.axiom selinger-c12)))

  step-symplectic ((S-gen) ∷ (H-gen) ∷ (H-gen) ∷ xs) = just ((H-gen) ∷ (H-gen) ∷ (S-gen) ∷ xs , at-head (PB.sym (PB.axiom comm-HHS)))
  step-symplectic ((S-gen ↥) ∷ (H-gen ↥) ∷ (H-gen ↥) ∷ xs) = just ((H-gen ↥) ∷ (H-gen ↥) ∷ (S-gen ↥) ∷ xs , at-head (PB.sym (PB.axiom (cong↑ comm-HHS))))
  step-symplectic ((S-gen ↥ ↥) ∷ (H-gen ↥ ↥) ∷ (H-gen ↥ ↥) ∷ xs) = just ((H-gen ↥ ↥) ∷ (H-gen ↥ ↥) ∷ (S-gen ↥ ↥) ∷ xs , at-head (PB.sym (PB.axiom (cong↑ (cong↑ comm-HHS)))))

  -- Others.
  step-symplectic ((CZ-gen) ∷ (H-gen) ∷ (H-gen) ∷ xs) = just ((H-gen) ∷ (H-gen) ∷ (CZ-gen) ∷ (CZ-gen) ∷ xs , at-head (PB.axiom semi-CZ-HH↓))
  step-symplectic ((CZ-gen) ∷ (H-gen ↥) ∷ (H-gen ↥) ∷ xs) = just ((H-gen ↥) ∷ (H-gen ↥) ∷ (CZ-gen) ∷ (CZ-gen) ∷ xs , at-head (PB.axiom semi-CZ-HH↑))

  step-symplectic ((CZ-gen) ∷ (H-gen) ∷ (CZ-gen) ∷ xs) = just ((S-gen) ∷ (S-gen) ∷ H-gen ∷ (S-gen) ∷ (S-gen) ∷ CZ-gen ∷ H-gen ∷ S-gen ∷ S-gen ∷ S-gen ↥ ∷ S-gen ↥ ∷ xs , at-head (PB.axiom selinger-c11 ))
  step-symplectic ((CZ-gen ↥) ∷ (H-gen ↥) ∷ (CZ-gen ↥) ∷ xs) = just ((S-gen ↥) ∷ (S-gen ↥) ∷ H-gen ↥ ∷ (S-gen ↥) ∷ (S-gen ↥) ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ S-gen ↥ ∷ S-gen ↥ ∷ S-gen ↥ ↥ ∷ S-gen ↥ ↥ ∷ xs , at-head (PB.axiom (cong↑ selinger-c11 )))
  step-symplectic ((CZ-gen) ∷ (H-gen ↥) ∷ (CZ-gen) ∷ xs) = just ((S-gen ↥) ∷ (S-gen ↥) ∷ H-gen ↥ ∷ (S-gen ↥) ∷ (S-gen ↥) ∷ CZ-gen ∷ H-gen ↥ ∷ S-gen ↥ ∷ S-gen ↥ ∷ S-gen ∷ S-gen ∷ xs , at-head (PB.axiom selinger-c10 ))
  step-symplectic ((CZ-gen ↥) ∷ (H-gen ↥ ↥) ∷ (CZ-gen ↥) ∷ xs) = just ((S-gen ↥ ↥) ∷ (S-gen ↥ ↥) ∷ H-gen ↥ ↥ ∷ (S-gen ↥ ↥) ∷ (S-gen ↥ ↥) ∷ CZ-gen ↥ ∷ H-gen ↥ ↥ ∷ S-gen ↥ ↥ ∷ S-gen ↥ ↥ ∷ S-gen ↥ ∷ S-gen ↥ ∷ xs , at-head (PB.axiom (cong↑ selinger-c10 )))

  step-symplectic (CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ xs) = just (CZ-gen ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ xs , at-head (PB.sym (lemma-comm-Ex-CZ)))
  step-symplectic (CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ xs) = just (CZ-gen ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ xs , at-head (PB.sym ( (lemma-cong↑ _ _ lemma-comm-Ex-CZ))))

  step-symplectic (CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ H-gen ∷ xs) = just (H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ xs , at-head (PB.sym (lemma-comm-Ex-H)))
  step-symplectic (CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ H-gen ↥ ∷ xs) = just (H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ xs , at-head (PB.sym ( (lemma-cong↑ _ _ lemma-comm-Ex-H))))

  step-symplectic (CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ S-gen ∷ xs) = just (S-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ xs , at-head (PB.sym (lemma-comm-Ex-S)))
  step-symplectic (CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ S-gen ↥ ∷ xs) = just (S-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ xs , at-head (PB.sym ( (lemma-cong↑ _ _ lemma-comm-Ex-S))))

  step-symplectic {suc n} (CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ S-gen ↥ ∷ xs) = just (S-gen ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ xs , at-head (((lemma-Ex-S↑ {n}))))
  step-symplectic (CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ S-gen ↥ ↥ ∷ xs) = just (S-gen ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ xs , at-head (lemma-cong↑ _ _ lemma-Ex-S↑))

  step-symplectic {suc n} (CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ H-gen ↥ ∷ xs) = just (H-gen ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ xs , at-head (((lemma-Ex-H↑ {n}))))
  step-symplectic (CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ H-gen ↥ ↥ ∷ xs) = just (H-gen ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ xs , at-head (lemma-cong↑ _ _ lemma-Ex-H↑))



  -- Catch-all
  step-symplectic _ = nothing

module Rewriting-Symplectic (n : ℕ) where
  open Symplectic
  open Rewriting
  open Symplectic-Rewriting hiding (n)
  open Rewriting.Step (step-cong (step-symplectic {n})) renaming (general-rewrite to rewrite-sym) public


module Swap-Rewriting where

  -- This module provides a complete rewrite system for 1-qubit
  -- Swap operators. It is specialized toward relations on qubit 0
  -- (but can also be applied to qubit 1 via duality).
  variable
    n : ℕ

  open Symplectic
  open Rewriting
  open Lemmas0 hiding (n)
  open Lemmas2 hiding (n)
  
  -- ----------------------------------------------------------------------
  -- * Rewrite rules for 1-qubit Swap relations
  
  step-swap : let open PB ((₁₊ n) QRel,_===_) hiding (_===_) in Step-Function (Gen (₁₊ n))  ((₁₊ n) QRel,_===_)

  -- Order of generators.
  step-swap ((S-gen) ∷ (S-gen) ∷ (S-gen) ∷ xs) = just (xs , at-head (PB.axiom order-S))
  step-swap ((S-gen ↥) ∷ (S-gen ↥) ∷ (S-gen ↥) ∷ xs) = just (xs , at-head (PB.axiom (cong↑ order-S)))
  step-swap ((S-gen ↥ ↥) ∷ (S-gen ↥ ↥) ∷ (S-gen ↥ ↥) ∷ xs) = just (xs , at-head (PB.axiom (cong↑ (cong↑ order-S))))
  step-swap ((H-gen) ∷ (H-gen) ∷ (H-gen) ∷ (H-gen) ∷ xs) = just (xs , at-head (PB.axiom order-H))
  step-swap ((H-gen ↥) ∷ (H-gen ↥) ∷ (H-gen ↥) ∷ (H-gen ↥) ∷ xs) = just (xs , at-head (PB.axiom (cong↑ order-H)))
  step-swap ((H-gen ↥ ↥) ∷ (H-gen ↥ ↥) ∷ (H-gen ↥ ↥) ∷ (H-gen ↥ ↥) ∷ xs) = just (xs , at-head (PB.axiom (cong↑ (cong↑ order-H))))
  step-swap ((CZ-gen) ∷ (CZ-gen) ∷ (CZ-gen) ∷ xs) = just (xs , at-head (PB.axiom order-CZ))
  step-swap ((CZ-gen ↥) ∷ (CZ-gen ↥) ∷ (CZ-gen ↥) ∷ xs) = just (xs , at-head (PB.axiom (cong↑ order-CZ)))

  step-swap ((S-gen) ∷ (H-gen) ∷ (S-gen) ∷ (H-gen) ∷ (S-gen) ∷ (H-gen) ∷ xs) = just (xs , at-head (PB.axiom order-SH))
  step-swap ((S-gen ↥) ∷ (H-gen ↥) ∷ (S-gen ↥) ∷ (H-gen ↥) ∷ (S-gen ↥) ∷ (H-gen ↥) ∷ xs) = just (xs , at-head (PB.axiom (cong↑ order-SH)))
  step-swap ((S-gen ↥ ↥) ∷ (H-gen ↥ ↥) ∷ (S-gen ↥ ↥) ∷ (H-gen ↥ ↥) ∷ (S-gen ↥ ↥) ∷ (H-gen ↥ ↥) ∷ xs) = just (xs , at-head (PB.axiom (cong↑ (cong↑ order-SH))))

  step-swap (CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ xs) = just (xs , at-head (lemma-order-Ex))
  step-swap (CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ xs) = just (xs , at-head ( (lemma-cong↑ _ _ lemma-order-Ex)))


  -- Commuting of generators.
  -- step-swap ((S-gen) ∷ (CZ-gen) ∷ xs) = just ((CZ-gen) ∷ (S-gen) ∷ xs , at-head (PB.sym (PB.axiom comm-CZ-S↓)))
  -- step-swap ((S-gen ↥) ∷ (CZ-gen) ∷ xs) = just ((CZ-gen) ∷ (S-gen ↥) ∷ xs , at-head (PB.sym (PB.axiom comm-CZ-S↑)))
  -- step-swap ((S-gen ↥) ∷ (CZ-gen ↥) ∷ xs) = just ((CZ-gen ↥) ∷ (S-gen ↥) ∷ xs , at-head (PB.sym (PB.axiom (cong↑ comm-CZ-S↓))))
  -- step-swap ((S-gen ↥ ↥) ∷ (CZ-gen ↥) ∷ xs) = just ((CZ-gen ↥) ∷ (S-gen ↥ ↥) ∷ xs , at-head (PB.sym (PB.axiom (cong↑ comm-CZ-S↑))))

  -- step-swap ((H-gen ↥ ↥) ∷ (CZ-gen) ∷ xs) = just ((CZ-gen) ∷ (H-gen ↥ ↥) ∷ xs , at-head (PB.axiom comm-CZ))
  -- step-swap ((S-gen ↥ ↥) ∷ (CZ-gen) ∷ xs) = just ((CZ-gen) ∷ (S-gen ↥ ↥) ∷ xs , at-head (PB.axiom comm-CZ))

  -- step-swap ((S-gen ↥) ∷ (S-gen) ∷ xs) = just ((S-gen) ∷ (S-gen ↥) ∷ xs , at-head ((PB.axiom comm-S)))
  -- step-swap ((S-gen ↥ ↥) ∷ (S-gen ↥) ∷ xs) = just ((S-gen ↥) ∷ (S-gen ↥ ↥) ∷ xs , at-head ((PB.axiom (cong↑ comm-S))))
  -- step-swap ((S-gen ↥ ↥) ∷ (S-gen) ∷ xs) = just ((S-gen) ∷ (S-gen ↥ ↥) ∷ xs , at-head (PB.axiom comm-S))
  -- step-swap ((S-gen ↥) ∷ (H-gen) ∷ xs) = just ((H-gen) ∷ (S-gen ↥) ∷ xs , at-head ((PB.axiom comm-H)))
  -- step-swap ((S-gen ↥ ↥) ∷ (H-gen ↥) ∷ xs) = just ((H-gen ↥) ∷ (S-gen ↥ ↥) ∷ xs , at-head ((PB.axiom (cong↑ comm-H))))
  -- step-swap ((S-gen ↥ ↥) ∷ (H-gen) ∷ xs) = just ((H-gen) ∷ (S-gen ↥ ↥) ∷ xs , at-head (PB.axiom comm-H))
  -- step-swap ((H-gen ↥) ∷ (H-gen) ∷ xs) = just ((H-gen) ∷ (H-gen ↥) ∷ xs , at-head ((PB.axiom comm-H)))
  -- step-swap ((H-gen ↥) ∷ (S-gen) ∷ xs) = just ((S-gen) ∷ (H-gen ↥) ∷ xs , at-head ((PB.axiom comm-S)))
  -- step-swap ((H-gen ↥ ↥) ∷ (H-gen ↥) ∷ xs) = just ((H-gen ↥) ∷ (H-gen ↥ ↥) ∷ xs , at-head ((PB.axiom (cong↑ comm-H))))
  -- step-swap ((H-gen ↥ ↥) ∷ (H-gen) ∷ xs) = just ((H-gen) ∷ (H-gen ↥ ↥) ∷ xs , at-head (PB.axiom comm-H))
  -- step-swap ((H-gen ↥ ↥) ∷ (S-gen ↥) ∷ xs) = just ((S-gen ↥) ∷ (H-gen ↥ ↥) ∷ xs , at-head ((PB.axiom (cong↑ comm-S))))
  -- step-swap ((H-gen ↥ ↥) ∷ (S-gen) ∷ xs) = just ((S-gen) ∷ (H-gen ↥ ↥) ∷ xs , at-head (PB.axiom comm-S))

  -- step-swap ((CZ-gen ↥ ↥) ∷ (H-gen ↥) ∷ xs) = just ((H-gen ↥) ∷ (CZ-gen ↥ ↥) ∷ xs , at-head ((PB.axiom (cong↑ comm-H))))
  -- step-swap ((CZ-gen ↥ ↥) ∷ (H-gen) ∷ xs) = just ((H-gen) ∷ (CZ-gen ↥ ↥) ∷ xs , at-head (PB.axiom comm-H))
  -- step-swap ((CZ-gen ↥ ↥) ∷ (S-gen ↥) ∷ xs) = just ((S-gen ↥) ∷ (CZ-gen ↥ ↥) ∷ xs , at-head ((PB.axiom (cong↑ comm-S))))
  -- step-swap ((CZ-gen ↥ ↥) ∷ (S-gen) ∷ xs) = just ((S-gen) ∷ (CZ-gen ↥ ↥) ∷ xs , at-head (PB.axiom comm-S))

  -- step-swap ((CZ-gen ↥ ↥) ∷ (CZ-gen) ∷ xs) = just ((CZ-gen) ∷ (CZ-gen ↥ ↥) ∷ xs , at-head ((PB.axiom comm-CZ)))
  -- step-swap ((CZ-gen ↥) ∷ (CZ-gen) ∷ xs) = just ((CZ-gen) ∷ (CZ-gen ↥) ∷ xs , at-head ((PB.axiom selinger-c12)))

  -- step-swap ((S-gen) ∷ (H-gen) ∷ (H-gen) ∷ xs) = just ((H-gen) ∷ (H-gen) ∷ (S-gen) ∷ xs , at-head (PB.sym (PB.axiom comm-HHS)))
  -- step-swap ((S-gen ↥) ∷ (H-gen ↥) ∷ (H-gen ↥) ∷ xs) = just ((H-gen ↥) ∷ (H-gen ↥) ∷ (S-gen ↥) ∷ xs , at-head (PB.sym (PB.axiom (cong↑ comm-HHS))))
  -- step-swap ((S-gen ↥ ↥) ∷ (H-gen ↥ ↥) ∷ (H-gen ↥ ↥) ∷ xs) = just ((H-gen ↥ ↥) ∷ (H-gen ↥ ↥) ∷ (S-gen ↥ ↥) ∷ xs , at-head (PB.sym (PB.axiom (cong↑ (cong↑ comm-HHS)))))

  -- Others.
  -- step-swap ((CZ-gen) ∷ (H-gen) ∷ (H-gen) ∷ xs) = just ((H-gen) ∷ (H-gen) ∷ (CZ-gen) ∷ (CZ-gen) ∷ xs , at-head (PB.axiom semi-CZ-HH↓))
  -- step-swap ((CZ-gen) ∷ (H-gen ↥) ∷ (H-gen ↥) ∷ xs) = just ((H-gen ↥) ∷ (H-gen ↥) ∷ (CZ-gen) ∷ (CZ-gen) ∷ xs , at-head (PB.axiom semi-CZ-HH↑))

  -- step-swap ((CZ-gen) ∷ (H-gen) ∷ (CZ-gen) ∷ xs) = just ((S-gen) ∷ (S-gen) ∷ H-gen ∷ (S-gen) ∷ (S-gen) ∷ CZ-gen ∷ H-gen ∷ S-gen ∷ S-gen ∷ S-gen ↥ ∷ S-gen ↥ ∷ xs , at-head (PB.axiom selinger-c11 ))
  -- step-swap ((CZ-gen ↥) ∷ (H-gen ↥) ∷ (CZ-gen ↥) ∷ xs) = just ((S-gen ↥) ∷ (S-gen ↥) ∷ H-gen ↥ ∷ (S-gen ↥) ∷ (S-gen ↥) ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ S-gen ↥ ∷ S-gen ↥ ∷ S-gen ↥ ↥ ∷ S-gen ↥ ↥ ∷ xs , at-head (PB.axiom (cong↑ selinger-c11 )))
  -- step-swap ((CZ-gen) ∷ (H-gen ↥) ∷ (CZ-gen) ∷ xs) = just ((S-gen ↥) ∷ (S-gen ↥) ∷ H-gen ↥ ∷ (S-gen ↥) ∷ (S-gen ↥) ∷ CZ-gen ∷ H-gen ↥ ∷ S-gen ↥ ∷ S-gen ↥ ∷ S-gen ∷ S-gen ∷ xs , at-head (PB.axiom selinger-c10 ))
  -- step-swap ((CZ-gen ↥) ∷ (H-gen ↥ ↥) ∷ (CZ-gen ↥) ∷ xs) = just ((S-gen ↥ ↥) ∷ (S-gen ↥ ↥) ∷ H-gen ↥ ↥ ∷ (S-gen ↥ ↥) ∷ (S-gen ↥ ↥) ∷ CZ-gen ↥ ∷ H-gen ↥ ↥ ∷ S-gen ↥ ↥ ∷ S-gen ↥ ↥ ∷ S-gen ↥ ∷ S-gen ↥ ∷ xs , at-head (PB.axiom (cong↑ selinger-c10 )))


  step-swap (CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ xs) = just (CZ-gen ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ xs , at-head (PB.sym (lemma-comm-Ex-CZ)))
  step-swap (CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ xs) = just (CZ-gen ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ xs , at-head (PB.sym ( (lemma-cong↑ _ _ lemma-comm-Ex-CZ))))

  step-swap (CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ H-gen ∷ xs) = just (H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ xs , at-head (PB.sym (lemma-comm-Ex-H)))
  step-swap (CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ H-gen ↥ ∷ xs) = just (H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ xs , at-head (PB.sym ( (lemma-cong↑ _ _ lemma-comm-Ex-H))))

  step-swap (CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ S-gen ∷ xs) = just (S-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ xs , at-head (PB.sym (lemma-comm-Ex-S)))
  step-swap (CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ S-gen ↥ ∷ xs) = just (S-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ xs , at-head (PB.sym ( (lemma-cong↑ _ _ lemma-comm-Ex-S))))

  step-swap {suc n} (CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ S-gen ↥ ∷ xs) = just (S-gen ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ xs , at-head (((lemma-Ex-S↑ {n}))))
  step-swap (CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ S-gen ↥ ↥ ∷ xs) = just (S-gen ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ xs , at-head (lemma-cong↑ _ _ lemma-Ex-S↑))

  step-swap {suc n} (CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ H-gen ↥ ∷ xs) = just (H-gen ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ xs , at-head (((lemma-Ex-H↑ {n}))))
  step-swap (CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ H-gen ↥ ↥ ∷ xs) = just (H-gen ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ xs , at-head (lemma-cong↑ _ _ lemma-Ex-H↑))


  -- Trivial commutations.
  step-swap (CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ S-gen ↥ ↥ ∷ xs) = just (S-gen ↥ ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ xs , at-head ( (lemma-comm-Ex-S↑↑)))
  step-swap (CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ S-gen ∷ xs) = just (S-gen ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ xs , at-head ( ( (lemma-comm-Ex↑-S))))
  step-swap (CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ xs) = just (H-gen ↥ ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ xs , at-head ( (lemma-comm-Ex-H↑↑)))
  step-swap (CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ H-gen ∷ xs) = just (H-gen ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ xs , at-head ( ( (lemma-comm-Ex↑-H))))

  -- Catch-all
  step-swap _ = nothing


module Rewriting-Swap (n : ℕ) where
  open Symplectic
  open Rewriting
  open Swap-Rewriting hiding (n)
  open Rewriting.Step (step-cong (step-swap {n})) renaming (general-rewrite to rewrite-swap) public



module Swap0-Rewriting where

  -- This module provides a complete rewrite system for 1-qubit
  -- Swap0 operators. It is specialized toward relations on qubit 0
  -- (but can also be applied to qubit 1 via duality).
  variable
    n : ℕ

  open Symplectic
  open Rewriting
  open Lemmas0 hiding (n)
--  open Lemmas2 hiding (n)
  
  -- ----------------------------------------------------------------------
  -- * Rewrite rules for 1-qubit Swap0 relations
  
  step-swap0 : let open PB ((₁₊ n) QRel,_===_) hiding (_===_) in Step-Function (Gen (₁₊ n))  ((₁₊ n) QRel,_===_)

  step-swap0 (CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ xs) = just (xs , at-head (lemma-order-Ex))
  step-swap0 (CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ xs) = just (xs , at-head ( (lemma-cong↑ _ _ lemma-order-Ex)))


  step-swap0 (CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ xs) = just (CZ-gen ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ xs , at-head (PB.sym (lemma-comm-Ex-CZ)))
  step-swap0 (CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ xs) = just (CZ-gen ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ xs , at-head (PB.sym ( (lemma-cong↑ _ _ lemma-comm-Ex-CZ))))

  step-swap0 (CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ H-gen ∷ xs) = just (H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ xs , at-head (PB.sym (lemma-comm-Ex-H)))
  step-swap0 (CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ H-gen ↥ ∷ xs) = just (H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ xs , at-head (PB.sym ( (lemma-cong↑ _ _ lemma-comm-Ex-H))))

  step-swap0 (CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ S-gen ∷ xs) = just (S-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ xs , at-head (PB.sym (lemma-comm-Ex-S)))
  step-swap0 (CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ S-gen ↥ ∷ xs) = just (S-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ xs , at-head (PB.sym ( (lemma-cong↑ _ _ lemma-comm-Ex-S))))

  step-swap0 {suc n} (CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ S-gen ↥ ∷ xs) = just (S-gen ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ xs , at-head (((lemma-Ex-S↑ {n}))))
  step-swap0 (CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ S-gen ↥ ↥ ∷ xs) = just (S-gen ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ xs , at-head (lemma-cong↑ _ _ lemma-Ex-S↑))

  step-swap0 {suc n} (CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ H-gen ↥ ∷ xs) = just (H-gen ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ xs , at-head (((lemma-Ex-H↑ {n}))))
  step-swap0 (CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ H-gen ↥ ↥ ∷ xs) = just (H-gen ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ xs , at-head (lemma-cong↑ _ _ lemma-Ex-H↑))


  -- Trivial commutations.
  step-swap0 (CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ S-gen ↥ ↥ ∷ xs) = just (S-gen ↥ ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ xs , at-head ( (lemma-comm-Ex-S↑↑)))
  step-swap0 (CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ S-gen ∷ xs) = just (S-gen ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ xs , at-head ( ( (lemma-comm-Ex↑-S))))
  step-swap0 (CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ xs) = just (H-gen ↥ ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ xs , at-head ( (lemma-comm-Ex-H↑↑)))
  step-swap0 (CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ H-gen ∷ xs) = just (H-gen ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ xs , at-head ( ( (lemma-comm-Ex↑-H))))

  -- Catch-all
  step-swap0 _ = nothing


module Rewriting-Swap0 (n : ℕ) where
  open Symplectic
  open Rewriting
  open Swap0-Rewriting hiding (n)
  open Rewriting.Step (step-cong (step-swap0 {n})) renaming (general-rewrite to rewrite-swap0) public
-}

module Lemmas3 where
  variable
    n : ℕ

  open Symplectic
  open import Zp.ModularArithmetic
--  open Rewriting-Symplectic
  open Rewriting


  lemma-comm-Ex-w↑↑ : ∀ {n} w → let open PB ((₂₊ n) QRel,_===_) in
    
    Ex • w ↑ ↑ ≈ w ↑ ↑ • Ex
    
  lemma-comm-Ex-w↑↑ {n} [ H-gen ]ʷ = general-comm auto
    where
    open Commuting-Symplectic n
    
  -- lemma-comm-Ex-w↑↑ {n} [ EX-gen ]ʷ = general-comm auto
  --   where
  --   open Commuting-Symplectic n
    
  lemma-comm-Ex-w↑↑ {n} [ S-gen ]ʷ = general-comm auto
    where
    open Commuting-Symplectic n
  lemma-comm-Ex-w↑↑ {n} [ CZ-gen ]ʷ = general-comm auto
    where
    open Commuting-Symplectic n
  lemma-comm-Ex-w↑↑ {n} [ x ↥ ]ʷ = begin
    (CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑) • (([ x ↥ ]ʷ ↑) ↑) ≈⟨ by-assoc auto ⟩
    (CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑ • CZ • H ↓) • H ↑ • [ x ↥ ]ʷ ↑ ↑ ≈⟨ cong refl (sym (axiom (cong↑ comm-H))) ⟩
    (CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑ • CZ • H ↓) • [ x ↥ ]ʷ ↑ ↑ • H ↑ ≈⟨ by-assoc auto ⟩
    ((CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑ • CZ) • H ↓ • [ x ↥ ]ʷ ↑ ↑) • H ↑ ≈⟨ cong (cong refl (sym (axiom comm-H))) refl ⟩
    ((CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑ • CZ) • [ x ↥ ]ʷ ↑ ↑ • H ↓) • H ↑ ≈⟨ by-assoc auto ⟩
    ((CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑) • CZ • [ x ↥ ]ʷ ↑ ↑) • (H ↓ • H ↑) ≈⟨ cong (cong refl (sym (axiom comm-CZ))) refl ⟩
    ((CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑) • [ x ↥ ]ʷ ↑ ↑ • CZ) • (H ↓ • H ↑) ≈⟨ by-assoc auto ⟩
    ((CZ • H ↓ • H ↑ • CZ • H ↓) • H ↑ • [ x ↥ ]ʷ ↑ ↑) • (CZ • H ↓ • H ↑) ≈⟨ cong (cong refl (sym (axiom (cong↑ comm-H)))) refl ⟩
    ((CZ • H ↓ • H ↑ • CZ • H ↓) • [ x ↥ ]ʷ ↑ ↑ • H ↑) • (CZ • H ↓ • H ↑) ≈⟨ by-assoc auto ⟩
    ((CZ • H ↓ • H ↑ • CZ) • H ↓ • [ x ↥ ]ʷ ↑ ↑) • (H ↑ • CZ • H ↓ • H ↑) ≈⟨ cong (cong refl (sym (axiom comm-H))) refl ⟩
    ((CZ • H ↓ • H ↑ • CZ) • [ x ↥ ]ʷ ↑ ↑ • H ↓) • (H ↑ • CZ • H ↓ • H ↑) ≈⟨ by-assoc auto ⟩
    ((CZ • H ↓ • H ↑) • CZ • [ x ↥ ]ʷ ↑ ↑) • (H ↓ • H ↑ • CZ • H ↓ • H ↑) ≈⟨ cong (cong refl (sym (axiom comm-CZ))) refl ⟩
    ((CZ • H ↓ • H ↑) • [ x ↥ ]ʷ ↑ ↑ • CZ) • (H ↓ • H ↑ • CZ • H ↓ • H ↑) ≈⟨ by-assoc auto ⟩
    ((CZ • H ↓) • H ↑ • [ x ↥ ]ʷ ↑ ↑) • (CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑) ≈⟨ cong (cong refl (sym (axiom (cong↑ comm-H)))) refl ⟩
    ((CZ • H ↓) • [ x ↥ ]ʷ ↑ ↑ • H ↑) • (CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑) ≈⟨ by-assoc auto ⟩
    (CZ • H ↓ • [ x ↥ ]ʷ ↑ ↑) • (H ↑ • CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑) ≈⟨ cong (cong refl (sym (axiom comm-H))) refl ⟩
    (CZ • [ x ↥ ]ʷ ↑ ↑ • H ↓) • (H ↑ • CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑) ≈⟨ by-assoc auto ⟩
    (CZ • [ x ↥ ]ʷ ↑ ↑) • (H ↓ • H ↑ • CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑) ≈⟨ cong ( (sym (axiom comm-CZ))) refl ⟩
    ([ x ↥ ]ʷ ↑ ↑ • CZ) • (H ↓ • H ↑ • CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑) ≈⟨ by-assoc auto ⟩
    [ x ↥ ]ʷ ↑ ↑ • (CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑) ≈⟨ refl ⟩
    (([ x ↥ ]ʷ ↑) ↑) • Ex ∎
    where
    open PB ((₂₊ n) QRel,_===_)
    open PP ((₂₊ n) QRel,_===_)
    open SR word-setoid
  lemma-comm-Ex-w↑↑ {n} ε = PB.trans PB.right-unit (PB.sym PB.left-unit)
  lemma-comm-Ex-w↑↑ {n} (w • v) = begin
    Ex • (((w • v) ↑) ↑) ≈⟨ refl ⟩
    Ex • w ↑ ↑ • v ↑ ↑ ≈⟨ sym assoc ⟩
    (Ex • w ↑ ↑) • v ↑ ↑ ≈⟨ cong (lemma-comm-Ex-w↑↑ w) refl ⟩
    (w ↑ ↑ • Ex) • v ↑ ↑ ≈⟨ assoc ⟩
    w ↑ ↑ • Ex • v ↑ ↑ ≈⟨ cong refl (lemma-comm-Ex-w↑↑ v) ⟩
    w ↑ ↑ • v ↑ ↑ • Ex ≈⟨ sym assoc ⟩
    (((w • v) ↑) ↑) • Ex ∎
    where
    open PB ((₂₊ n) QRel,_===_)
    open PP ((₂₊ n) QRel,_===_)
    open SR word-setoid








-- ----------------------------------------------------------------------
-- * Duality

module Duality where

  open Symplectic
  open Commuting-Symplectic
  open Rewriting
  open Symplectic

  private
    variable
      n : ℕ

  -- Here, we provide a proof principle for duality (an equation is
  -- provable iff its dual is provable).


  -- Each generator has a dual, obtained by swapping the two qubits.
  dual-gen : Gen 2 -> Gen 2
  dual-gen H-gen = H-gen ↥
  dual-gen S-gen = S-gen ↥
  dual-gen CZ-gen = CZ-gen
--  dual-gen EX-gen = EX-gen
  dual-gen (H-gen ↥) = H-gen
  dual-gen (S-gen ↥) = S-gen
  

  -- Compute the dual of a word.
  dual : Word (Gen 2) -> Word (Gen 2)
  dual [ x ]ʷ = [ (dual-gen x) ]ʷ
  dual ε = ε
  dual (w • u) = dual w • dual u

  -- Lemma: duality is an involution.
  lemma-double-dual : ∀ w -> w ≡ dual (dual w)
  lemma-double-dual ([ H-gen ]ʷ) = Eq.refl
  lemma-double-dual ([ H-gen ↥ ]ʷ) = Eq.refl
  lemma-double-dual ([ S-gen ]ʷ) = Eq.refl
  lemma-double-dual ([ S-gen ↥ ]ʷ) = Eq.refl
  lemma-double-dual ([ CZ-gen ]ʷ) = Eq.refl
--  lemma-double-dual ([ EX-gen ]ʷ) = Eq.refl
  lemma-double-dual ε = Eq.refl
  lemma-double-dual (w • v) = Eq.cong₂ _•_ (lemma-double-dual w) (lemma-double-dual v)


  aux-dual : ∀ w k -> dual (w ^ k) ≡ dual w ^ k
  aux-dual w k@0 = auto
  aux-dual w k@1 = auto
  aux-dual w k@(₂₊ k') = begin
    dual (w ^ k) ≡⟨ auto ⟩
    dual w • dual (w ^ ₁₊ k') ≡⟨ (Eq.cong (dual w •_) (aux-dual w (₁₊ k'))) ⟩
    dual w • dual w ^ ₁₊ k' ≡⟨ auto ⟩
    dual w ^ k ∎
    where
    open ≡-Reasoning

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

  aux-dual-S⁻¹↑ : dual (S⁻¹ ↑) ≡ S⁻¹
  aux-dual-S⁻¹↑ = begin
    dual (S⁻¹ ↑) ≡⟨ Eq.cong dual (Eq.sym (aux-↑ S p-1)) ⟩
    dual (S ↑ ^ p-1) ≡⟨ aux-dual (S ↑) p-1 ⟩
    S⁻¹ ∎
    where
    open ≡-Reasoning

  aux-dual-S^k↑ : ∀ k -> dual ((S ^ k) ↑) ≡ S ^ k
  aux-dual-S^k↑ k = begin
    dual ((S ^ k) ↑) ≡⟨ Eq.cong dual (Eq.sym (aux-↑ S k)) ⟩
    dual (S ↑ ^ k) ≡⟨ aux-dual (S ↑) k ⟩
    S ^ k ∎
    where
    open ≡-Reasoning

  aux-dual-S⁻¹ : dual (S⁻¹ ↓) ≡ (S⁻¹ ↑)
  aux-dual-S⁻¹ = begin
    dual (S⁻¹ ↓) ≡⟨ aux-dual S p-1 ⟩
    S ↑ ^ p-1 ≡⟨ aux-↑ S p-1 ⟩
    (S⁻¹ ↑) ∎
    where
    open ≡-Reasoning

  aux-dual-S^k : ∀ k -> dual ((S ^ k) ↓) ≡ (S ^ k) ↑
  aux-dual-S^k k = begin
    dual ((S ^ k) ↓) ≡⟨ aux-dual S k ⟩
    S ↑ ^ k ≡⟨ aux-↑ S k ⟩
    (S ^ k) ↑ ∎
    where
    open ≡-Reasoning


  aux-dual-CZ^k : ∀ k -> dual ((CZ ^ k)) ≡ (CZ ^ k)
  aux-dual-CZ^k k = begin
    dual ((CZ ^ k)) ≡⟨ aux-dual CZ k ⟩
    CZ ^ k ≡⟨ auto ⟩
    (CZ ^ k) ∎
    where
    open ≡-Reasoning


  aux-dual-Mx : ∀ x -> dual (M x) ≡ M x ↑
  aux-dual-Mx x' = begin
    dual (S^ x • H • S^ x⁻¹ • H • S^ x • H) ≡⟨ Eq.cong₂ (\ xx yy -> xx • H ↑ • yy • dual(H • S^ x • H)) (aux-dual-S^k (toℕ x)) (aux-dual-S^k (toℕ x⁻¹)) ⟩
    S^ x ↑ • H ↑ • S^ x⁻¹ ↑ • dual (H • S^ x • H) ≡⟨ Eq.cong (\ xx -> S^ x ↑ • H ↑ • S^ x⁻¹ ↑ • (H ↑ • xx • H ↑)) (aux-dual-S^k (toℕ x)) ⟩
    M x' ↑ ∎
    where
    open ≡-Reasoning
    x = x' .proj₁
    x⁻¹ = ((x' ⁻¹) .proj₁ )


  aux-dual-Mx↑ : ∀ x -> dual (M x ↑) ≡ M x
  aux-dual-Mx↑ x' = begin
    dual (S^ x ↑ • H ↑ • S^ x⁻¹ ↑ • H ↑ • S^ x ↑ • H ↑) ≡⟨ Eq.cong₂ (\ xx yy -> xx • H • yy • dual(H ↑ • S^ x ↑ • H ↑)) (aux-dual-S^k↑ (toℕ x)) (aux-dual-S^k↑ (toℕ x⁻¹)) ⟩
    S^ x • H • S^ x⁻¹ • dual (H ↑ • S^ x ↑ • H ↑) ≡⟨ Eq.cong (\ xx -> S^ x • H • S^ x⁻¹ • (H • xx • H)) (aux-dual-S^k↑ (toℕ x)) ⟩
    M x' ∎
    where
    open ≡-Reasoning
    x = x' .proj₁
    x⁻¹ = ((x' ⁻¹) .proj₁ )

  -- Dualize a proof. Duality is useful early on. However, we will not
  -- prove the duals of axioms rel-A, rel-B, and rel-C until much
  -- later. Therefore, we work only with Clifford relations for the
  -- time being.
  open PB (2 QRel,_===_)
  open PP (2 QRel,_===_)
  open SR word-setoid




  lemma-dual : ∀ {w u} -> w === u -> dual w ≈ dual u
  -- lemma-dual def-EX = begin
  --   EX ≈⟨ axiom def-EX ⟩
  --   Ex ≈⟨ general-comm 0 auto ⟩
  --   dual Ex ∎
  -- lemma-dual order-EX = axiom order-EX
  lemma-dual order-S = begin
    [ S-gen ↥ ]ʷ • dual (S ^ ₁₊ p-2) ≈⟨ (cright (refl' (aux-dual S p-1))) ⟩
    [ S-gen ↥ ]ʷ • dual S ^ ₁₊ p-2 ≈⟨ refl ⟩
    [ S-gen ↥ ]ʷ • (S ↑) ^ ₁₊ p-2 ≈⟨ (cright (refl' (aux-↑ S p-1))) ⟩
    (S ^ p) ↑ ≈⟨ axiom (cong↑ order-S) ⟩
    ε ∎
  lemma-dual order-H = axiom (cong↑ order-H)
  lemma-dual order-SH = axiom (cong↑ order-SH)
  lemma-dual comm-HHS = axiom (cong↑ comm-HHS)
  lemma-dual (M-mul x y) = begin
    dual (M x • M y) ≈⟨ cong (refl' (aux-dual-Mx x)) (refl' (aux-dual-Mx y)) ⟩
    (M x • M y) ↑ ≈⟨ axiom (cong↑ (M-mul x y)) ⟩
    M (x *' y) ↑ ≈⟨ refl' ((Eq.sym  (aux-dual-Mx (x *' y)))) ⟩
    dual (M (x *' y)) ∎
  lemma-dual (semi-MS x) = begin
    dual (M x • S) ≈⟨ (cleft refl' (aux-dual-Mx x)) ⟩
    (M x • S) ↑ ≈⟨ axiom (cong↑ (semi-MS x)) ⟩
    (S^ (x ^2) • M x) ↑ ≈⟨ cong (refl' (Eq.sym (aux-dual-S^k (toℕ (fromℕ< _))))) (refl' (Eq.sym (aux-dual-Mx x))) ⟩
    dual (S^ (x ^2) • M x) ∎
  lemma-dual (semi-M↑CZ x) = begin
    dual (M x ↑ • CZ) ≈⟨ (cleft refl' (aux-dual-Mx↑ x)) ⟩
    (M x • CZ) ≈⟨ axiom (semi-M↓CZ x) ⟩
    (CZ^ (x ^1) • M x) ≈⟨ cong (refl' (Eq.sym (aux-dual-CZ^k (toℕ (x .proj₁))))) (sym (refl' (aux-dual-Mx↑ x))) ⟩
    dual (CZ^ (x ^1) • M x ↑) ∎
  lemma-dual (semi-M↓CZ x) = begin
    dual (M x • CZ) ≈⟨ (cleft refl' (aux-dual-Mx x)) ⟩
    (M x ↑ • CZ) ≈⟨ axiom (semi-M↑CZ x) ⟩
    (CZ^ (x ^1) • M x ↑) ≈⟨ cong (refl' (Eq.sym (aux-dual-CZ^k (toℕ (x .proj₁))))) (sym (refl' (aux-dual-Mx x))) ⟩
    dual (CZ^ (x ^1) • M x) ∎
  lemma-dual order-CZ =  begin
    [ CZ-gen ]ʷ • dual (CZ ^ ₁₊ p-2) ≈⟨ (cright (refl' (aux-dual CZ p-1))) ⟩
    [ CZ-gen ]ʷ • dual CZ ^ ₁₊ p-2 ≈⟨ refl ⟩
    (CZ ^ p) ≈⟨ axiom (order-CZ) ⟩
    ε ∎
  lemma-dual comm-CZ-S↓ = axiom comm-CZ-S↑
  lemma-dual comm-CZ-S↑ = axiom comm-CZ-S↓
  lemma-dual selinger-c10 = begin
    dual (CZ • H ↑ • CZ) ≈⟨ refl ⟩
    (CZ • H • CZ) ≈⟨ axiom selinger-c11 ⟩
    S⁻¹ ↓ • H ↓ • S⁻¹ ↓ • CZ • H ↓ • S⁻¹ ↓ • S⁻¹ ↑ ≈⟨ sym (cong (refl' aux-dual-S⁻¹↑) (cright cong (refl' aux-dual-S⁻¹↑) (cright (cright cong (refl' aux-dual-S⁻¹↑) (refl' aux-dual-S⁻¹))))) ⟩
    dual (S⁻¹ ↑ • H ↑ • S⁻¹ ↑ • CZ • H ↑ • S⁻¹ ↑ • S⁻¹ ↓) ∎
  lemma-dual selinger-c11 = begin
    dual (CZ • H ↓ • CZ) ≈⟨ refl ⟩
    (CZ • H ↑ • CZ) ≈⟨ axiom selinger-c10 ⟩
    S⁻¹ ↑ • H ↑ • S⁻¹ ↑ • CZ • H ↑ • S⁻¹ ↑ • S⁻¹ ≈⟨ sym (cong (refl' aux-dual-S⁻¹) (cright cong (refl' aux-dual-S⁻¹) (cright (cright cong (refl' aux-dual-S⁻¹) (refl' aux-dual-S⁻¹↑))))) ⟩
    dual (S⁻¹ • H • S⁻¹ • CZ • H • S⁻¹ • S⁻¹ ↑) ∎
  lemma-dual (comm-H {g = S-gen}) = sym (axiom comm-S)
  lemma-dual (comm-H {g = H-gen}) = sym (axiom comm-H)
  lemma-dual (comm-S {g = S-gen}) = sym (axiom comm-S)
  lemma-dual (comm-S {g = H-gen}) = sym (axiom comm-H)
  lemma-dual (cong↑ order-S) = begin
     S • dual ((S ^ p-1) ↑) ≈⟨ (cright refl' (Eq.cong dual (Eq.sym (aux-↑ S p-1)))) ⟩
     S • dual ((S ↑ ^ p-1)) ≈⟨ (cright refl' ( aux-dual (S ↑) p-1)) ⟩
     S • dual (S ↑) ^ p-1 ≈⟨ axiom order-S ⟩
     ε ∎
  lemma-dual (cong↑ order-H) = axiom order-H
  lemma-dual (cong↑ order-SH) = axiom order-SH
  lemma-dual (cong↑ comm-HHS) = axiom comm-HHS
  lemma-dual (cong↑ (M-mul x y)) = begin
    dual ((M x • M y) ↑) ≈⟨ cong (refl' (aux-dual-Mx↑ x)) (refl' (aux-dual-Mx↑ y)) ⟩
    M x • M y ≈⟨ axiom (M-mul x y) ⟩
    M (x *' y) ≈⟨ sym (refl' (aux-dual-Mx↑ (x *' y))) ⟩
    dual (M (x *' y) ↑) ∎
  lemma-dual (cong↑ (semi-MS x)) = begin
    dual ((M x • S) ↑) ≈⟨ (cleft refl' (aux-dual-Mx↑ x)) ⟩
    M x • S ≈⟨ axiom (semi-MS x) ⟩
    S^ (x ^2) • M x ≈⟨ sym (cong (refl' (aux-dual-S^k↑ (toℕ (fromℕ< _)))) (refl' (aux-dual-Mx↑ x))) ⟩
    dual ((S^ (x ^2) • M x) ↑) ∎

  -- A proof principle for duality.
  by-duality : ∀ {w u} -> w ≈ u -> dual w ≈ dual u
  by-duality PB.refl = refl
  by-duality (PB.sym eq) = sym (by-duality eq)
  by-duality (PB.trans eq eq₁) = trans (by-duality eq) (by-duality eq₁)
  by-duality (PB.cong eq eq₁) = cong (by-duality eq) (by-duality eq₁)
  by-duality PB.assoc = assoc
  by-duality PB.left-unit = left-unit
  by-duality PB.right-unit = right-unit
  by-duality (PB.axiom x) = lemma-dual x


  -- A proof principle for duality.
  by-duality' : ∀ {w u w' u'} -> w ≈ u -> dual w ≈ w' -> dual u ≈ u' -> w' ≈ u'
  by-duality' eq eqw equ = trans (sym eqw) (trans (by-duality eq) equ)


{-
module Duality-n where

  open Symplectic
  open Commuting-Symplectic
  open Rewriting
  open Symplectic

  private
    variable
      n : ℕ

  -- Here, we provide a proof principle for duality (an equation is
  -- provable iff its dual is provable).


  -- Each generator has a dual, obtained by swapping the two qubits.
  dual-gen : Gen (₂₊ n) -> Gen (₂₊ n)
  dual-gen H-gen = H-gen ↥
  dual-gen S-gen = S-gen ↥
  dual-gen (H-gen ↥) = H-gen
  dual-gen (S-gen ↥) = S-gen
  dual-gen g = g
  
  -- Compute the dual of a word.
  dual : Word (Gen (₂₊ n)) -> Word (Gen (₂₊ n))
  dual [ x ]ʷ = [ (dual-gen x) ]ʷ
  dual ε = ε
  dual (w • u) = dual w • dual u


  -- Lemma: duality is an involution.
  lemma-double-dual : ∀ w -> w ≡ dual {n} (dual w)
  lemma-double-dual ([ H-gen ]ʷ) = Eq.refl
  lemma-double-dual ([ H-gen ↥ ]ʷ) = Eq.refl
  lemma-double-dual ([ S-gen ]ʷ) = Eq.refl
  lemma-double-dual ([ S-gen ↥ ]ʷ) = Eq.refl
  lemma-double-dual [ CZ-gen ]ʷ = auto
  lemma-double-dual [ CZ-gen ↥ ]ʷ = auto
  lemma-double-dual [ (g ↥) ↥ ]ʷ = auto
  lemma-double-dual ε = Eq.refl
  lemma-double-dual (w • v) = Eq.cong₂ _•_ (lemma-double-dual w) (lemma-double-dual v)


  aux-dual : ∀ w k -> dual {n} (w ^ k) ≡ dual w ^ k
  aux-dual w k@0 = auto
  aux-dual w k@1 = auto
  aux-dual w k@(₂₊ k') = begin
    dual (w ^ k) ≡⟨ auto ⟩
    dual w • dual (w ^ ₁₊ k') ≡⟨ (Eq.cong (dual w •_) (aux-dual w (₁₊ k'))) ⟩
    dual w • dual w ^ ₁₊ k' ≡⟨ auto ⟩
    dual w ^ k ∎
    where
    open ≡-Reasoning

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

  aux-dual-S⁻¹↑ : dual {n} (S⁻¹ ↑) ≡ S⁻¹
  aux-dual-S⁻¹↑ = begin
    dual (S⁻¹ ↑) ≡⟨ Eq.cong dual (Eq.sym (aux-↑ S p-1)) ⟩
    dual (S ↑ ^ p-1) ≡⟨ aux-dual (S ↑) p-1 ⟩
    S⁻¹ ∎
    where
    open ≡-Reasoning

  aux-dual-S^k↑ : ∀ k -> dual {n} ((S ^ k) ↑) ≡ S ^ k
  aux-dual-S^k↑ k = begin
    dual ((S ^ k) ↑) ≡⟨ Eq.cong dual (Eq.sym (aux-↑ S k)) ⟩
    dual (S ↑ ^ k) ≡⟨ aux-dual (S ↑) k ⟩
    S ^ k ∎
    where
    open ≡-Reasoning

  aux-dual-S⁻¹ : dual {n} (S⁻¹ ↓) ≡ (S⁻¹ ↑)
  aux-dual-S⁻¹ = begin
    dual (S⁻¹ ↓) ≡⟨ aux-dual S p-1 ⟩
    S ↑ ^ p-1 ≡⟨ aux-↑ S p-1 ⟩
    (S⁻¹ ↑) ∎
    where
    open ≡-Reasoning

  aux-dual-S^k : ∀ k -> dual {n} ((S ^ k) ↓) ≡ (S ^ k) ↑
  aux-dual-S^k k = begin
    dual ((S ^ k) ↓) ≡⟨ aux-dual S k ⟩
    S ↑ ^ k ≡⟨ aux-↑ S k ⟩
    (S ^ k) ↑ ∎
    where
    open ≡-Reasoning


  aux-dual-CZ^k : ∀ k -> dual {n} ((CZ ^ k)) ≡ (CZ ^ k)
  aux-dual-CZ^k k = begin
    dual ((CZ ^ k)) ≡⟨ aux-dual CZ k ⟩
    CZ ^ k ≡⟨ auto ⟩
    (CZ ^ k) ∎
    where
    open ≡-Reasoning


  aux-dual-Mx : ∀ x -> dual {n} (M x) ≡ M x ↑
  aux-dual-Mx x' = begin
    dual (S^ x • H • S^ x⁻¹ • H • S^ x • H) ≡⟨ Eq.cong₂ (\ xx yy -> xx • H ↑ • yy • dual(H • S^ x • H)) (aux-dual-S^k (toℕ x)) (aux-dual-S^k (toℕ x⁻¹)) ⟩
    S^ x ↑ • H ↑ • S^ x⁻¹ ↑ • dual (H • S^ x • H) ≡⟨ Eq.cong (\ xx -> S^ x ↑ • H ↑ • S^ x⁻¹ ↑ • (H ↑ • xx • H ↑)) (aux-dual-S^k (toℕ x)) ⟩
    M x' ↑ ∎
    where
    open ≡-Reasoning
    x = x' .proj₁
    x⁻¹ = ((x' ⁻¹) .proj₁ )

  aux-dual-Mx↑ : ∀ x -> dual {n} (M x ↑) ≡ M x
  aux-dual-Mx↑ x' = begin
    dual (S^ x ↑ • H ↑ • S^ x⁻¹ ↑ • H ↑ • S^ x ↑ • H ↑) ≡⟨ Eq.cong₂ (\ xx yy -> xx • H • yy • dual(H ↑ • S^ x ↑ • H ↑)) (aux-dual-S^k↑ (toℕ x)) (aux-dual-S^k↑ (toℕ x⁻¹)) ⟩
    S^ x • H • S^ x⁻¹ • dual (H ↑ • S^ x ↑ • H ↑) ≡⟨ Eq.cong (\ xx -> S^ x • H • S^ x⁻¹ • (H • xx • H)) (aux-dual-S^k↑ (toℕ x)) ⟩
    M x' ∎
    where
    open ≡-Reasoning
    x = x' .proj₁
    x⁻¹ = ((x' ⁻¹) .proj₁ )

  -- Dualize a proof. Duality is useful early on. However, we will not
  -- prove the duals of axioms rel-A, rel-B, and rel-C until much
  -- later. Therefore, we work only with Clifford relations for the
  -- time being.
  
  
  lemma-dual : let open PB ((₂₊ n) QRel,_===_) in ∀ {w u} -> w === u -> dual w ≈ dual u
  lemma-dual {n} order-S = begin
    [ S-gen ↥ ]ʷ • dual (S ^ ₁₊ p-2) ≈⟨ (cright (refl' (aux-dual S p-1))) ⟩
    [ S-gen ↥ ]ʷ • dual S ^ ₁₊ p-2 ≈⟨ refl ⟩
    [ S-gen ↥ ]ʷ • (S ↑) ^ ₁₊ p-2 ≈⟨ (cong refl (refl' (aux-↑ S p-1))) ⟩
    (S ^ p) ↑ ≈⟨ axiom (cong↑ order-S) ⟩
    ε ∎
    where
    open PB ((₂₊ n) QRel,_===_)
    open PP ((₂₊ n) QRel,_===_)
    open SR word-setoid
  lemma-dual {n} order-H = axiom (cong↑ order-H)
    where
    open PB ((₂₊ n) QRel,_===_)
  lemma-dual {n} order-SH = axiom (cong↑ order-SH)
    where
    open PB ((₂₊ n) QRel,_===_)
  lemma-dual {n} comm-HHS = axiom (cong↑ comm-HHS)
    where
    open PB ((₂₊ n) QRel,_===_)
  lemma-dual {n} (M-mul x y) = begin
    dual (M x • M y) ≈⟨ cong (refl' (aux-dual-Mx x)) (refl' (aux-dual-Mx y)) ⟩
    (M x • M y) ↑ ≈⟨ axiom (cong↑ (M-mul x y)) ⟩
    M (x *' y) ↑ ≈⟨ refl' ((Eq.sym  (aux-dual-Mx (x *' y)))) ⟩
    dual (M (x *' y)) ∎
    where
    open PB ((₂₊ n) QRel,_===_)
    open PP ((₂₊ n) QRel,_===_)
    open SR word-setoid
  lemma-dual {n} (semi-MS x) = begin
    dual (M x • S) ≈⟨ (cleft refl' (aux-dual-Mx x)) ⟩
    (M x • S) ↑ ≈⟨ axiom (cong↑ (semi-MS x)) ⟩
    (S^ (x ^2) • M x) ↑ ≈⟨ cong (refl' (Eq.sym (aux-dual-S^k (toℕ (fromℕ< _))))) (refl' (Eq.sym (aux-dual-Mx x))) ⟩
    dual (S^ (x ^2) • M x) ∎
    where
    open PB ((₂₊ n) QRel,_===_)
    open PP ((₂₊ n) QRel,_===_)
    open SR word-setoid
  lemma-dual {n} (semi-M↑CZ x) = begin
    dual (M x ↑ • CZ) ≈⟨ (cleft refl' (aux-dual-Mx↑ x)) ⟩
    (M x • CZ) ≈⟨ axiom (semi-M↓CZ x) ⟩
    (CZ^ (x ^1) • M x) ≈⟨ cong (refl' (Eq.sym (aux-dual-CZ^k (toℕ (x .proj₁))))) (sym (refl' (aux-dual-Mx↑ x))) ⟩
    dual (CZ^ (x ^1) • M x ↑) ∎
    where
    open PB ((₂₊ n) QRel,_===_)
    open PP ((₂₊ n) QRel,_===_)
    open SR word-setoid
  lemma-dual {n} (semi-M↓CZ x) = begin
    dual (M x • CZ) ≈⟨ (cleft refl' (aux-dual-Mx x)) ⟩
    (M x ↑ • CZ) ≈⟨ axiom (semi-M↑CZ x) ⟩
    (CZ^ (x ^1) • M x ↑) ≈⟨ cong (refl' (Eq.sym (aux-dual-CZ^k (toℕ (x .proj₁))))) (sym (refl' (aux-dual-Mx x))) ⟩
    dual (CZ^ (x ^1) • M x) ∎
    where
    open PB ((₂₊ n) QRel,_===_)
    open PP ((₂₊ n) QRel,_===_)
    open SR word-setoid
  lemma-dual {n} order-CZ =  begin
    [ CZ-gen ]ʷ • dual (CZ ^ ₁₊ p-2) ≈⟨ (cright (refl' (aux-dual CZ p-1))) ⟩
    [ CZ-gen ]ʷ • dual CZ ^ ₁₊ p-2 ≈⟨ refl ⟩
    (CZ ^ p) ≈⟨ axiom (order-CZ) ⟩
    ε ∎
    where
    open PB ((₂₊ n) QRel,_===_)
    open PP ((₂₊ n) QRel,_===_)
    open SR word-setoid
  lemma-dual {n} comm-CZ-S↓ = axiom comm-CZ-S↑
    where
    open PB ((₂₊ n) QRel,_===_)
  lemma-dual {n} comm-CZ-S↑ = axiom comm-CZ-S↓
    where
    open PB ((₂₊ n) QRel,_===_)
  lemma-dual {n} selinger-c10 = begin
    dual (CZ • H ↑ • CZ) ≈⟨ refl ⟩
    (CZ • H • CZ) ≈⟨ axiom selinger-c11 ⟩
    S⁻¹ ↓ • H ↓ • S⁻¹ ↓ • CZ • H ↓ • S⁻¹ ↓ • S⁻¹ ↑ ≈⟨ sym (cong (refl' aux-dual-S⁻¹↑) (cright cong (refl' aux-dual-S⁻¹↑) (cright (cright cong (refl' aux-dual-S⁻¹↑) (refl' aux-dual-S⁻¹))))) ⟩
    dual (S⁻¹ ↑ • H ↑ • S⁻¹ ↑ • CZ • H ↑ • S⁻¹ ↑ • S⁻¹ ↓) ∎
    where
    open PB ((₂₊ n) QRel,_===_)
    open PP ((₂₊ n) QRel,_===_)
    open SR word-setoid
  lemma-dual {n} selinger-c11 = begin
    dual (CZ • H ↓ • CZ) ≈⟨ refl ⟩
    (CZ • H ↑ • CZ) ≈⟨ axiom selinger-c10 ⟩
    S⁻¹ ↑ • H ↑ • S⁻¹ ↑ • CZ • H ↑ • S⁻¹ ↑ • S⁻¹ ≈⟨ sym (cong (refl' aux-dual-S⁻¹) (cright cong (refl' aux-dual-S⁻¹) (cright (cright cong (refl' aux-dual-S⁻¹) (refl' aux-dual-S⁻¹↑))))) ⟩
    dual (S⁻¹ • H • S⁻¹ • CZ • H • S⁻¹ • S⁻¹ ↑) ∎
    where
    open PB ((₂₊ n) QRel,_===_)
    open PP ((₂₊ n) QRel,_===_)
    open SR word-setoid
  lemma-dual {n} (comm-H {g = S-gen}) = sym (axiom comm-S)
    where
    open PB ((₂₊ n) QRel,_===_)
  lemma-dual {n} (comm-H {g = H-gen}) = sym (axiom comm-H)
    where
    open PB ((₂₊ n) QRel,_===_)
  lemma-dual {n} (comm-S {g = S-gen}) = sym (axiom comm-S)
    where
    open PB ((₂₊ n) QRel,_===_)
  lemma-dual {n} (comm-S {g = H-gen}) = sym (axiom comm-H)
    where
    open PB ((₂₊ n) QRel,_===_)
  lemma-dual {n} (cong↑ order-S) = begin
     S • dual ((S ^ p-1) ↑) ≈⟨ (cright refl' (Eq.cong dual (Eq.sym (aux-↑ S p-1)))) ⟩
     S • dual ((S ↑ ^ p-1)) ≈⟨ (cright refl' ( aux-dual (S ↑) p-1)) ⟩
     S • dual (S ↑) ^ p-1 ≈⟨ axiom order-S ⟩
     ε ∎
    where
    open PB ((₂₊ n) QRel,_===_)
    open PP ((₂₊ n) QRel,_===_)
    open SR word-setoid
  lemma-dual {n} (cong↑ order-H) = axiom order-H
    where
    open PB ((₂₊ n) QRel,_===_)
  lemma-dual {n} (cong↑ order-SH) = axiom order-SH
    where
    open PB ((₂₊ n) QRel,_===_)
  lemma-dual {n} (cong↑ comm-HHS) = axiom comm-HHS
    where
    open PB ((₂₊ n) QRel,_===_)
  lemma-dual {n} (cong↑ (M-mul x y)) = begin
    dual ((M x • M y) ↑) ≈⟨ cong (refl' (aux-dual-Mx↑ x)) (refl' (aux-dual-Mx↑ y)) ⟩
    M x • M y ≈⟨ axiom (M-mul x y) ⟩
    M (x *' y) ≈⟨ sym (refl' (aux-dual-Mx↑ (x *' y))) ⟩
    dual (M (x *' y) ↑) ∎
    where
    open PB ((₂₊ n) QRel,_===_)
    open PP ((₂₊ n) QRel,_===_)
    open SR word-setoid
  lemma-dual {n} (cong↑ (semi-MS x)) = begin
    dual ((M x • S) ↑) ≈⟨ (cleft refl' (aux-dual-Mx↑ x)) ⟩
    M x • S ≈⟨ axiom (semi-MS x) ⟩
    S^ (x ^2) • M x ≈⟨ sym (cong (refl' (aux-dual-S^k↑ (toℕ (fromℕ< _)))) (refl' (aux-dual-Mx↑ x))) ⟩
    dual ((S^ (x ^2) • M x) ↑) ∎
    where
    open PB ((₂₊ n) QRel,_===_)
    open PP ((₂₊ n) QRel,_===_)
    open SR word-setoid


  -- A proof principle for duality.
  by-duality : ∀ {w u} -> w ≈ u -> dual w ≈ dual u
  by-duality PB.refl = refl
  by-duality (PB.sym eq) = sym (by-duality eq)
  by-duality (PB.trans eq eq₁) = trans (by-duality eq) (by-duality eq₁)
  by-duality (PB.cong eq eq₁) = cong (by-duality eq) (by-duality eq₁)
  by-duality PB.assoc = assoc
  by-duality PB.left-unit = left-unit
  by-duality PB.right-unit = right-unit
  by-duality (PB.axiom x) = lemma-dual {n} x


  -- A proof principle for duality.
  by-duality' : ∀ {w u w' u'} -> w ≈ u -> dual w ≈ w' -> dual u ≈ u' -> w' ≈ u'
  by-duality' eq eqw equ = trans (sym eqw) (trans (by-duality eq) equ)
-}


