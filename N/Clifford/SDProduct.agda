{-# OPTIONS --allow-unsolved-metas #-}
-- {-# OPTIONS  --safe #-}
{-# OPTIONS --termination-depth=4 #-}
open import Level using (0ℓ)

open import Relation.Binary using (Rel)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Binary.Morphism.Definitions using (Homomorphic₂)
open import Relation.Binary.PropositionalEquality using (_≡_ ; _≢_ ; inspect ; setoid ; module ≡-Reasoning) renaming ([_] to [_]')
import Relation.Binary.Reasoning.Setoid as SR
import Relation.Binary.PropositionalEquality as Eq
open import Relation.Nullary.Decidable using (yes ; no)


open import Function using (_∘_ ; id)
open import Function.Definitions using (Injective)

open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂ ; map₁ ; ∃ ; Σ ; Σ-syntax)

open import Data.Product.Relation.Binary.Pointwise.NonDependent as PW using (≡×≡⇒≡ ; Pointwise ; ≡⇒≡×≡)
open import Data.Nat hiding (_^_ ; _*_ ; _+_)
open import Agda.Builtin.Nat using (_-_)
import Data.Nat as Nat
open import Data.Fin hiding (_+_ ; _≤_)
open import Data.Bool hiding (_≤_)
open import Data.List hiding ([_])

open import Data.Maybe
open import Data.Sum using (_⊎_ ; inj₁ ; inj₂ ; [_,_])
open import Data.Unit using (⊤ ; tt)
open import Data.Empty using (⊥ ; ⊥-elim)

open import Word.Base as WB hiding (wfoldl)
open import Word.Properties
import Presentation.Base as PB
import Presentation.Properties as PP
open PP using (NFProperty ; NFProperty')
import Presentation.CosetNF as CA
import Presentation.Reidemeister-Schreier as RS
open import Notations
module RSF = RS.Star-Injective-Full.Reidemeister-Schreier-Full

open import Presentation.Construct.Base hiding (_*_)
import Presentation.Construct.Properties.SemiDirectProduct2 as SDP2
import Presentation.Construct.Properties.DirectProduct as DP
import Presentation.Groups.Cyclic as Cyclic
open import Presentation.Tactics hiding ([_])

open import Data.Fin.Properties using (suc-injective ; toℕ-inject₁ ; toℕ-fromℕ)
import Data.Nat.Properties as NP
open import Presentation.GroupLike
import N.Symplectic as NS
open import Data.Nat.Primality

open import Zp.ModularArithmetic
open import Zp.Fermats-little-theorem

module N.Clifford.SDProduct
  (p-3 : ℕ)
  (let p-2 = ₁₊ p-3)
  (p-prime : Prime (suc (₁₊ p-2)))
  (let open PrimeModulus' p-2 p-prime)
  (g*@(g , g≠0) : ℤ* ₚ)
  (g-gen : ∀ ((x , _) : ℤ* ₚ) -> ∃ \ (k : ℤ ₚ-₁) -> x ≡ g ^′ toℕ k )
  where




pattern ₀ = zero
pattern ₁ = ₁₊ ₀
pattern ₂ = ₁₊ ₁


import N.Symplectic p-2 p-prime as NSym
import N.Symplectic-Simplified p-2 p-prime g* g-gen as NSim
module Sym = NSym.Symplectic
module Sim = NSim.Simplified-Relations
import N.XZ p-2 p-prime as XZ

module SemiDirect where

  private
    variable
      n : ℕ
      
  open import Presentation.Construct.Base

  Gen : ℕ -> Set
  Gen n = XZ.Gen n ⊎ Sym.Gen n

  pattern X-gen = inj₁ XZ.X-gen
  pattern Z-gen = inj₁ XZ.Z-gen
  pattern H-gen = inj₂ Sym.H-gen
  pattern S-gen = inj₂ Sym.S-gen
  pattern CZ-gen = inj₂ Sym.CZ-gen

  _↓ : ∀ {n} → Word (Gen n) → Word (Gen ( n))
  _↓ {n} x = x 

  _↑ : ∀ {n} → Word (Gen n) → Word (Gen (₁₊ n))
  [ inj₁ x ]ʷ ↑ = [ inj₁ (x XZ.↥) ]ʷ
  [ inj₂ y ]ʷ ↑ = [ inj₂ (y Sym.↥) ]ʷ
  ε ↑ = ε
  (w • w₁) ↑ = w ↑ • w₁ ↑

  X : ∀ {n} → Word (Gen (₁₊ n))
  X = [ X-gen ]ʷ

  Z : ∀ {n} → Word (Gen (₁₊ n))
  Z = [ Z-gen ]ʷ

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

  Z^ : ∀ {n} → ℤ ₚ -> Word (Gen (₁₊ n))
  Z^ k = Z ^ toℕ k

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


  conj : Sym.Gen n -> XZ.Gen n -> Word (XZ.Gen n)
  conj Sym.H-gen XZ.X-gen = XZ.Z
  conj Sym.H-gen XZ.Z-gen = XZ.X ^ p-1
  conj Sym.S-gen XZ.X-gen = XZ.X • XZ.Z
  conj Sym.S-gen XZ.Z-gen = XZ.Z
  conj Sym.CZ-gen XZ.X-gen = XZ.X • XZ.Z XZ.↑
  conj Sym.CZ-gen (XZ.X-gen XZ.↥) = XZ.X XZ.↑ • XZ.Z
  conj Sym.CZ-gen XZ.Z-gen = XZ.Z
  conj Sym.CZ-gen (XZ.Z-gen XZ.↥) = XZ.Z XZ.↑
  conj Sym.H-gen (xz XZ.↥) = [ xz ]ʷ XZ.↑
  conj Sym.S-gen (xz XZ.↥) = [ xz ]ʷ XZ.↑
  conj Sym.CZ-gen (xz XZ.↥ XZ.↥) = [ xz ]ʷ XZ.↑ XZ.↑
  conj (sym Sym.↥) XZ.X-gen = XZ.X
  conj (sym Sym.↥) XZ.Z-gen = XZ.Z
  conj (sym Sym.↥) (xz XZ.↥) = conj sym xz XZ.↑


  
  pattern order-X = left XZ.order-X
  pattern order-Z = left XZ.order-Z
  pattern comm-Z-X = left XZ.comm-Z-X
  
  pattern comm-Z = left XZ.comm-Z
  pattern comm-X = left XZ.comm-X


  pattern order-S = right Sim.order-S
  pattern order-H = right Sim.order-H
  pattern M-power = right Sim.M-power
  pattern semi-MS = right Sim.semi-MS

{-
  pattern semi-M↑CZ = right Sim.semi-M↑CZ
  pattern semi-M↓CZ = right Sim.semi-M↓CZ

  pattern order-CZ = right Sim.order-CZ

  pattern comm-CZ-S↓ = right Sim.comm-CZ-S↓
  pattern comm-CZ-S↑ = right Sim.comm-CZ-S↑

  pattern selinger-c10 = right Sim.selinger-c10
  pattern selinger-c11 = right Sim.selinger-c11

  pattern selinger-c12 = right Sim.selinger-c12
  pattern selinger-c13 = right Sim.selinger-c13
  pattern selinger-c14 = right Sim.selinger-c14
  pattern selinger-c15 = right Sim.selinger-c15

  pattern comm-H = right Sim.comm-H
  pattern comm-S = right Sim.comm-S
  pattern comm-CZ = right Sim.comm-CZ
  pattern cong↑ = right Sim.cong↑


  pattern conj-H-X = mid (comm XZ.X-gen Sym.H-gen)
  pattern conj-H-Z = mid (comm XZ.Z-gen Sym.H-gen)
  pattern conj-S-X = mid (comm XZ.X-gen Sym.S-gen)
  pattern conj-S-Z = mid (comm XZ.Z-gen Sym.S-gen)

  pattern conj-CZ-X↑ = mid (comm (XZ.X-gen XZ.↥) Sym.CZ-gen)
  pattern conj-CZ-Z↑ = mid (comm (XZ.Z-gen XZ.↥) Sym.CZ-gen)
  pattern conj-CZ-X = mid (comm XZ.X-gen Sym.CZ-gen)
  pattern conj-CZ-Z = mid (comm XZ.Z-gen Sym.CZ-gen)

  pattern conj-H↑-X = mid (comm XZ.X-gen (Sym.H-gen Sym.↥))
  pattern conj-H↑-Z = mid (comm XZ.Z-gen (Sym.H-gen Sym.↥))
  pattern conj-S↑-X = mid (comm XZ.X-gen (Sym.S-gen Sym.↥))
  pattern conj-S↑-Z = mid (comm XZ.Z-gen (Sym.S-gen Sym.↥))

  pattern conj-H-X↑ = mid (comm (XZ.X-gen XZ.↥) Sym.H-gen)
  pattern conj-H-Z↑ = mid (comm (XZ.Z-gen XZ.↥) Sym.H-gen)
  pattern conj-S-X↑ = mid (comm (XZ.X-gen XZ.↥) Sym.S-gen)
  pattern conj-S-Z↑ = mid (comm (XZ.Z-gen XZ.↥) Sym.S-gen)

-}

  infix 4 _QRel,_===_
  _QRel,_===_ : (n : ℕ) → WRel (Gen n)
  _QRel,_===_ n = (XZ._QRel,_===_ n ⸲ Sim._QRel,_===_  n ⸲ Γⱼ' conj)
  

  lemma-[]ₗ-↑ : ∀ (u : Word (XZ.Gen n)) -> [ u ]ₗ ↑ ≡ [ u XZ.↑ ]ₗ
  lemma-[]ₗ-↑ {n} [ XZ.X-gen ]ʷ = auto
  lemma-[]ₗ-↑ {n} [ XZ.Z-gen ]ʷ = auto
  lemma-[]ₗ-↑ {n} [ x XZ.↥ ]ʷ = auto
  lemma-[]ₗ-↑ {n} ε = auto
  lemma-[]ₗ-↑ {n} (u • v) = Eq.cong₂ _•_ (lemma-[]ₗ-↑ u) (lemma-[]ₗ-↑ v)


  lemma-[]ᵣ-↑ : ∀ (u : Word (Sym.Gen n)) -> [ u ]ᵣ ↑ ≡ [ u Sym.↑ ]ᵣ
  lemma-[]ᵣ-↑ {n} [ Sym.H-gen ]ʷ = auto
  lemma-[]ᵣ-↑ {n} [ Sym.S-gen ]ʷ = auto
  lemma-[]ᵣ-↑ {n} [ Sym.CZ-gen ]ʷ = auto
  lemma-[]ᵣ-↑ {n} [ x Sym.↥ ]ʷ = auto
  lemma-[]ᵣ-↑ {n} ε = auto
  lemma-[]ᵣ-↑ {n} (u • v) = Eq.cong₂ _•_ (lemma-[]ᵣ-↑ u) (lemma-[]ᵣ-↑ v)


  lemma-[]ₗ^k : ∀ (u : Word (XZ.Gen n)) k -> [_]ₗ {B = Sym.Gen n} (u ^ k) ≡ [ u ]ₗ ^ k
  lemma-[]ₗ^k {n} u ₀ = auto
  lemma-[]ₗ^k {n} u ₁ = auto
  lemma-[]ₗ^k {n} u (₁₊ k'@(₁₊ k'')) = Eq.cong₂ _•_ auto (lemma-[]ₗ^k u k')

  lemma-[]ᵣ^k : ∀ (u : Word (Sym.Gen n)) k -> [_]ᵣ {A = XZ.Gen n} (u ^ k) ≡ [ u ]ᵣ ^ k
  lemma-[]ᵣ^k {n} u ₀ = auto
  lemma-[]ᵣ^k {n} u ₁ = auto
  lemma-[]ᵣ^k {n} u (₁₊ k'@(₁₊ k'')) = Eq.cong₂ _•_ auto (lemma-[]ᵣ^k u k')

  lemma-cong↑ : ∀ {n} w v →
    let
    open PB (n QRel,_===_) using (_≈_)
    open PB ((₁₊ n) QRel,_===_) renaming (_≈_ to _≈↑_) using ()
    in
    w ≈ v → w ↑ ≈↑ v ↑
  lemma-cong↑ {n} w v PB.refl = PB.refl
  lemma-cong↑ {n} w v (PB.sym eq) = PB.sym (lemma-cong↑ v w eq)
  lemma-cong↑ {n} w v (PB.trans eq eq₁) = PB.trans (lemma-cong↑ _ _ eq) (lemma-cong↑ _ _ eq₁)
  lemma-cong↑ {n} w v (PB.cong eq eq₁) = PB.cong (lemma-cong↑ _ _ eq) (lemma-cong↑ _ _ eq₁)
  lemma-cong↑ {n} w v PB.assoc = PB.assoc
  lemma-cong↑ {n} w v PB.left-unit = PB.left-unit
  lemma-cong↑ {n} w v PB.right-unit = PB.right-unit
  lemma-cong↑ {₁₊ n} w v (PB.axiom (left {u} {v₁} x)) rewrite lemma-[]ₗ-↑ u | lemma-[]ₗ-↑ v₁ = PB.axiom (left (XZ.cong↑ x))
  lemma-cong↑ {₁₊ n} w v (PB.axiom (right {u} {v₁} x)) rewrite lemma-[]ᵣ-↑ u | lemma-[]ᵣ-↑ v₁ = PB.axiom (right (Sim.cong↑ x))
  lemma-cong↑ {n} w v (PB.axiom (mid (comm XZ.X-gen Sym.H-gen))) = PB.axiom (mid (comm (XZ.X-gen XZ.↥) (Sym.Gen.H-gen Sym.↥)))
  lemma-cong↑ {n} w v (PB.axiom (mid (comm XZ.X-gen Sym.S-gen))) = PB.axiom (mid (comm (XZ.X-gen XZ.↥) (Sym.Gen.S-gen Sym.↥)))
  lemma-cong↑ {n} w v (PB.axiom (mid (comm XZ.X-gen Sym.CZ-gen))) = PB.axiom (mid (comm (XZ.X-gen XZ.↥) (Sym.Gen.CZ-gen Sym.↥)))
  lemma-cong↑ {n} w v (PB.axiom (mid (comm XZ.X-gen (b Sym.↥)))) = PB.axiom (mid (comm (XZ.X-gen XZ.↥) ((b Sym.Gen.↥) Sym.↥)))
  lemma-cong↑ {n} w v (PB.axiom (mid (comm XZ.Z-gen Sym.H-gen))) = begin
    H ↑ • Z ↑ ≈⟨ axiom (mid (comm (XZ.Z-gen XZ.↥) (Sym.H-gen Sym.↥))) ⟩
    ([ conj (Sym.H-gen) (XZ.Z-gen) XZ.↑ ]ₗ) • H ↑ ≡⟨ Eq.sym (Eq.cong (\ xx -> xx • H ↑) (lemma-[]ₗ-↑ (conj (Sym.H-gen) (XZ.Z-gen)))) ⟩
    ([ conj Sym.H-gen XZ.Z-gen ]ₗ ↑) • H ↑ ∎
    where
    open PB (n QRel,_===_) using (_≈_)
    open PB ((₁₊ n) QRel,_===_) renaming (_≈_ to _≈↑_)
    open PP ((₁₊ n) QRel,_===_)
    open SR word-setoid
    
  lemma-cong↑ {n} w v (PB.axiom (mid (comm XZ.Z-gen Sym.S-gen))) = PB.axiom (mid (comm (XZ.Z-gen XZ.↥) (Sym.Gen.S-gen Sym.↥)))
  lemma-cong↑ {n} w v (PB.axiom (mid (comm XZ.Z-gen Sym.CZ-gen))) = PB.axiom (mid (comm (XZ.Z-gen XZ.↥) (Sym.Gen.CZ-gen Sym.↥)))
  lemma-cong↑ {n} w v (PB.axiom (mid (comm XZ.Z-gen (b Sym.↥)))) = PB.axiom (mid (comm (XZ.Z-gen XZ.↥) ((b Sym.Gen.↥) Sym.↥)))
  lemma-cong↑ {n} w v (PB.axiom (mid (comm (a XZ.↥) Sym.H-gen))) = PB.axiom (mid (comm ((a XZ.↥) XZ.↥) (Sym.Gen.H-gen Sym.↥)))
  lemma-cong↑ {n} w v (PB.axiom (mid (comm (a XZ.↥) Sym.S-gen))) = PB.axiom (mid (comm ((a XZ.↥) XZ.↥) (Sym.Gen.S-gen Sym.↥)))
  lemma-cong↑ {n} w v (PB.axiom (mid (comm (XZ.X-gen XZ.↥) Sym.CZ-gen))) = PB.axiom (mid (comm ((XZ.X-gen XZ.↥) XZ.↥) (Sym.Gen.CZ-gen Sym.↥)))
  lemma-cong↑ {n} w v (PB.axiom (mid (comm (XZ.Z-gen XZ.↥) Sym.CZ-gen))) = PB.axiom (mid (comm ((XZ.Z-gen XZ.↥) XZ.↥) (Sym.Gen.CZ-gen Sym.↥)))
  lemma-cong↑ {n} w v (PB.axiom (mid (comm ((a XZ.↥) XZ.↥) Sym.CZ-gen))) = PB.axiom (mid (comm (((a XZ.↥) XZ.↥) XZ.↥) (Sym.Gen.CZ-gen Sym.↥)))
  lemma-cong↑ {₁₊ n@(₁₊ n')} w v (PB.axiom (mid (comm (a XZ.↥) (b Sym.↥)))) = begin
    [ inj₂ (b Sym.↥ Sym.↥) ]ʷ • [ inj₁ (a XZ.↥ XZ.↥) ]ʷ ≈⟨ refl ⟩
    [ inj₂ (b Sym.↥) ]ʷ ↑ • [ inj₁ (a XZ.↥) ]ʷ ↑ ≈⟨ PB.axiom (mid (comm ((a XZ.↥) XZ.↥) ((b Sym.↥) Sym.↥))) ⟩
    [ conj b a XZ.↑ XZ.↑ ]ₗ • [ inj₂ (b Sym.↥) ]ʷ ↑ ≡⟨ Eq.cong (\ xx -> xx • [ inj₂ (b Sym.↥) ]ʷ ↑) (Eq.sym (lemma-[]ₗ-↑ (conj b a XZ.↑))) ⟩
    ([ conj b a XZ.↑ ]ₗ ↑) • [ inj₂ (b Sym.↥ Sym.↥) ]ʷ ∎
    where
    open PB ((₁₊ n) QRel,_===_) using (_≈_)
    module PB1 = PB ( (₁₊ n) QRel,_===_)
    open PB ((₂₊ n) QRel,_===_) renaming (_≈_ to _≈↑_)
    open PP ((₂₊ n) QRel,_===_)
    open SR word-setoid
-- lemma-cong↑ _ _ (PB.axiom (mid (comm (a XZ.↥) (b Sym.Gen.↥))))


module Semi-GroupLike where

  open SemiDirect
  private
    variable
      n : ℕ
    
  grouplike : Grouplike (n QRel,_===_)
  grouplike {₁₊ n} (H-gen) = (H ) ^ 3 , claim
    where
    open PB ((₁₊ n) QRel,_===_)
    open PP ((₁₊ n) QRel,_===_)
    open SR word-setoid
    open LeftRightCongruence (XZ._QRel,_===_ (₁₊ n)) (Sim._QRel,_===_  (₁₊ n)) (Γⱼ' conj)
    open NSim.Lemmas1 n
    claim : (H ) ^ 3 • H ≈ ε
    claim = begin
      (H) ^ 3 • H ≈⟨ by-assoc auto ⟩
      [ Sym.H ^ 4 ]ᵣ ≈⟨ rights lemma-order-H  ⟩
      ε ∎

  grouplike {₁₊ n} (S-gen) = S ^ p-1 , claim
    where
    open PB ((₁₊ n) QRel,_===_)
    open PP ((₁₊ n) QRel,_===_)
    open SR word-setoid
    open LeftRightCongruence (XZ._QRel,_===_ (₁₊ n)) (Sim._QRel,_===_  (₁₊ n)) (Γⱼ' conj)
    open NSim.Lemmas1 n
    module RG = NSim.Symplectic-Sim-GroupLike
    claim : S ^ p-1 • S ≈ ε
    claim = begin
      S ^ p-1 • S ≡⟨ (Eq.cong ( \ xx -> xx • S) ( Eq.sym (lemma-[]ᵣ^k Sym.S p-1))) ⟩
      [ Sym.S ^ p-1 • Sym.S ]ᵣ ≈⟨ rights (RG.grouplike Sym.S-gen .proj₂)  ⟩
      ε ∎
  grouplike {₂₊ n} (CZ-gen) = CZ ^ p-1 , claim
    where
    open PB ((₂₊ n) QRel,_===_)
    open PP ((₂₊ n) QRel,_===_)
    open SR word-setoid
    open LeftRightCongruence (XZ._QRel,_===_ (₂₊ n)) (Sim._QRel,_===_  (₂₊ n)) (Γⱼ' conj)
    open NSim.Lemmas1 n
    module RG = NSim.Symplectic-Sim-GroupLike
    claim : CZ ^ p-1 • CZ ≈ ε
    claim = begin
      CZ ^ p-1 • CZ ≡⟨ (Eq.cong ( \ xx -> xx • CZ) ( Eq.sym (lemma-[]ᵣ^k Sym.CZ p-1))) ⟩
      [ Sym.CZ ^ p-1 • Sym.CZ ]ᵣ ≈⟨ rights (RG.grouplike Sym.CZ-gen .proj₂)  ⟩
      ε ∎

  grouplike {₁₊ n} (X-gen) = X ^ p-1 , claim
    where
    open PB ((₁₊ n) QRel,_===_)
    open PP ((₁₊ n) QRel,_===_)
    open SR word-setoid
    open LeftRightCongruence (XZ._QRel,_===_ (₁₊ n)) (Sim._QRel,_===_  (₁₊ n)) (Γⱼ' conj)
    open NSim.Lemmas1 n
    module LG = XZ.XZ-GroupLike
    claim : X ^ p-1 • X ≈ ε
    claim = begin
      X ^ p-1 • X ≡⟨ (Eq.cong ( \ xx -> xx • X) ( Eq.sym (lemma-[]ₗ^k XZ.X p-1))) ⟩
      [ XZ.X ^ p-1 • XZ.X ]ₗ ≈⟨ lefts (LG.grouplike XZ.X-gen .proj₂)  ⟩
      ε ∎

  grouplike {₁₊ n} (Z-gen) = Z ^ p-1 , claim
    where
    open PB ((₁₊ n) QRel,_===_)
    open PP ((₁₊ n) QRel,_===_)
    open SR word-setoid
    open LeftRightCongruence (XZ._QRel,_===_ (₁₊ n)) (Sim._QRel,_===_  (₁₊ n)) (Γⱼ' conj)
    open NSim.Lemmas1 n
    module LG = XZ.XZ-GroupLike
    claim : Z ^ p-1 • Z ≈ ε
    claim = begin
      Z ^ p-1 • Z ≡⟨ (Eq.cong ( \ xx -> xx • Z) ( Eq.sym (lemma-[]ₗ^k XZ.Z p-1))) ⟩
      [ XZ.Z ^ p-1 • XZ.Z ]ₗ ≈⟨ lefts (LG.grouplike XZ.Z-gen .proj₂)  ⟩
      ε ∎


  grouplike {₂₊ n} (inj₁ (g XZ.↥)) with XZ.XZ-GroupLike.grouplike (g XZ.↥)
  ... | ig , prf = ([ ig ]ₗ) , lefts prf
    where
    open LeftRightCongruence (XZ._QRel,_===_ (₂₊ n)) (Sim._QRel,_===_  (₂₊ n)) (Γⱼ' conj)
  grouplike {₂₊ n} (inj₂ (g Sym.↥)) with NSim.Symplectic-Sim-GroupLike.grouplike (g Sym.↥)
  ... | ig , prf = ([ ig ]ᵣ) , rights prf
    where
    open LeftRightCongruence (XZ._QRel,_===_ (₂₊ n)) (Sim._QRel,_===_  (₂₊ n)) (Γⱼ' conj)
