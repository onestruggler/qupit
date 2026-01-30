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



module N.Ex-Sym1 (p-2 : ℕ) (p-prime : Prime (2+ p-2))  where

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
open import N.Ex-Sym p-2 p-prime
open import N.Lemmas-2Qupit-Sym p-2 p-prime

open Lemmas0a
module Lemmas0a1 where

  private
    variable
      n : ℕ
      
  open Symplectic
  open Lemmas-Sym

  open Symplectic-GroupLike

  open import Data.Nat.DivMod
  open import Data.Fin.Properties


  lemma-selinger-c11 : let open PB ((₂₊ n) QRel,_===_) in 
    CZ • H • CZ ≈ S⁻¹ • H • CZ • (S⁻¹ • H • S⁻¹) • S⁻¹ ↑
  lemma-selinger-c11 {n} = begin 
    CZ • H • CZ ≈⟨ axiom selinger-c11 ⟩
    S⁻¹ • H • S⁻¹ • CZ • H • S⁻¹ • S⁻¹ ↑ ≈⟨ special-assoc (□ ^ 7) (□ ^ 2 • □ ^ 2 • □ ^ 3) auto ⟩
    (S⁻¹ • H) • (S⁻¹ • CZ) • H • S⁻¹ • S⁻¹ ↑ ≈⟨ (cright cleft word-comm p-1 1 (sym (axiom comm-CZ-S↓))) ⟩
    (S⁻¹ • H) • (CZ • S⁻¹) • H • S⁻¹ • S⁻¹ ↑ ≈⟨ special-assoc (□ ^ 2 • □ ^ 2 • □ ^ 3) (□ • □ • □ • □ ^ 3 • □) auto ⟩
    S⁻¹ • H • CZ • (S⁻¹ • H • S⁻¹) • S⁻¹ ↑ ∎
    where
    open PB ((₂₊ n) QRel,_===_)
    open PP ((₂₊ n) QRel,_===_)
    open SR word-setoid
    open Commuting-Symplectic (n)
    open Sym0-Rewriting (suc n)
    open Pattern-Assoc


  lemma-CZ^kHCZ : let open PB ((₂₊ n) QRel,_===_) in ∀ k' -> let k = suc k' in
    CZ ^ k • H • CZ ≈ (S⁻¹ ^ k) • H • CZ • (S⁻¹ • H • S⁻¹) ^ k • S⁻¹ ↑ ^ k
  lemma-CZ^kHCZ {n} k'@0 = let k = suc k' in lemma-selinger-c11
    where
    open PB ((₂₊ n) QRel,_===_)
    open PP ((₂₊ n) QRel,_===_)
    open SR word-setoid
    open Commuting-Symplectic (n)
    open Sym0-Rewriting (suc n)
    open Pattern-Assoc

  lemma-CZ^kHCZ {n} k'@(₁₊ k'') = let k = suc k' in begin
    CZ ^ k • H • CZ ≈⟨ assoc ⟩
    CZ • CZ ^ k' • H • CZ ≈⟨ (cright lemma-CZ^kHCZ k'') ⟩
    CZ • (S⁻¹ ^ k') • H • CZ • (S⁻¹ • H • S⁻¹) ^ k' • S⁻¹ ↑ ^ k' ≈⟨ sym assoc ⟩
    (CZ • S⁻¹ ^ k') • H • CZ • (S⁻¹ • H • S⁻¹) ^ k' • S⁻¹ ↑ ^ k' ≈⟨ (cleft word-comm 1 k' (word-comm 1 p-1 (axiom comm-CZ-S↓))) ⟩
    (S⁻¹ ^ k' • CZ) • H • CZ • (S⁻¹ • H • S⁻¹) ^ k' • S⁻¹ ↑ ^ k' ≈⟨ special-assoc (□ ^ 2 • □ • □ • □) (□ • □ ^ 3 • □) auto ⟩
    S⁻¹ ^ k' • (CZ • H • CZ) • (S⁻¹ • H • S⁻¹) ^ k' • S⁻¹ ↑ ^ k' ≈⟨ (cright cleft lemma-selinger-c11) ⟩
    S⁻¹ ^ k' • (S⁻¹ • H • CZ • (S⁻¹ • H • S⁻¹) • S⁻¹ ↑) • (S⁻¹ • H • S⁻¹) ^ k' • S⁻¹ ↑ ^ k' ≈⟨ special-assoc (□ • □ ^ 5 • □ ^ 2) (□ ^ 2 • □ ^ 2 • □ • □ ^ 2 • □) auto ⟩
    (S⁻¹ ^ k' • S⁻¹) • (H • CZ) • (S⁻¹ • H • S⁻¹) • (S⁻¹ ↑ • (S⁻¹ • H • S⁻¹) ^ k') • S⁻¹ ↑ ^ k' ≈⟨ cong (word-comm k' p-1 (word-comm p-1 1 refl)) (cright cright cleft word-comm 1 k' aux) ⟩
    (S⁻¹ • S⁻¹ ^ k') • (H • CZ) • (S⁻¹ • H • S⁻¹) • ((S⁻¹ • H • S⁻¹) ^ k' • S⁻¹ ↑) • S⁻¹ ↑ ^ k' ≈⟨ special-assoc ((□ ^ 2 • □ ^ 2 • □ • □ ^ 2 • □)) (□ ^ 2 • □ • □ • □ ^ 2 • □ ^ 2) auto ⟩
    S⁻¹ ^ k • H • CZ • (S⁻¹ • H • S⁻¹) ^ k • S⁻¹ ↑ ^ k ∎
    where
    open PB ((₂₊ n) QRel,_===_)
    open PP ((₂₊ n) QRel,_===_)
    open SR word-setoid
    open Commuting-Symplectic (n)
    open Sym0-Rewriting (suc n)
    open Pattern-Assoc
    aux : (S⁻¹ ↑) • (S⁻¹ • H • S⁻¹) ≈ (S⁻¹ • H • S⁻¹) • (S⁻¹ ↑)
    aux = begin
      (S⁻¹ ↑) • (S⁻¹ • H • S⁻¹) ≈⟨ sym assoc ⟩
      (S⁻¹ ↑ • S⁻¹) • H • S⁻¹ ≈⟨ (cleft sym (lemma-comm-Sᵏ-w↑ p-1 S⁻¹)) ⟩
      (S⁻¹ • S⁻¹ ↑) • H • S⁻¹ ≈⟨ special-assoc (□ ^ 2 • □ ^ 2) (□ • □ ^ 2 • □) auto ⟩
      S⁻¹ • (S⁻¹ ↑ • H) • S⁻¹ ≈⟨ (cright cleft sym (lemma-comm-H-w↑ S⁻¹)) ⟩
      S⁻¹ • (H • S⁻¹ ↑) • S⁻¹ ≈⟨ (cright assoc) ⟩
      S⁻¹ • H • S⁻¹ ↑ • S⁻¹ ≈⟨ (cright cright sym (lemma-comm-Sᵏ-w↑ p-1 S⁻¹)) ⟩
      S⁻¹ • H • S⁻¹ • S⁻¹ ↑ ≈⟨ trans (by-assoc auto) (sym assoc) ⟩
      (S⁻¹ • H • S⁻¹) • (S⁻¹ ↑) ∎

  open import Algebra.Properties.Ring (+-*-ring p-2)
  

  lemma-Euler : let open PB ((₁₊ n) QRel,_===_) in ∀ b' -> let b = b' .proj₁ in let -b⁻¹ = - ((b' ⁻¹) .proj₁) in
    H • S^ b • H ≈ (S^ -b⁻¹ • H ^ 3 • S^ (- b)) • M b'
  lemma-Euler {n} b' = begin    
    H • S^ b • H ≈⟨ sym left-unit ⟩
    S^ ₀ • H • S^ b • H ≈⟨ (cleft sym (refl' (Eq.cong S^ (+-inverseˡ b⁻¹)))) ⟩
    S^ (-b⁻¹ + b⁻¹) • H • S^ b • H ≈⟨ (cleft sym ( lemma-S^k+l -b⁻¹ b⁻¹)) ⟩
    (S^ -b⁻¹ • S^ b⁻¹) • H • S^ b • H ≈⟨ assoc ⟩
    S^ -b⁻¹ • S^ b⁻¹ • H • S^ b • H ≈⟨ sym (cong refl left-unit) ⟩
    S^ -b⁻¹ • ε • S^ b⁻¹ • H • S^ b • H ≈⟨ (cright cleft rewrite-sym0 100 auto) ⟩
    S^ -b⁻¹ • (H ^ 3 • H) • S^ b⁻¹ • H • S^ b • H ≈⟨ trans (by-assoc auto) (sym assoc) ⟩
    (S^ -b⁻¹ • H ^ 3) • H • S^ b⁻¹ • H • S^ b • H ≈⟨ sym (cong refl left-unit) ⟩
    (S^ -b⁻¹ • H ^ 3) • S^ ₀ • H • S^ b⁻¹ • H • S^ b • H ≈⟨ (cright cleft refl' (Eq.cong S^ (Eq.sym (+-inverseˡ b)))) ⟩
    (S^ -b⁻¹ • H ^ 3) • S^ (- b + b) • H • S^ b⁻¹ • H • S^ b • H ≈⟨ (cright cleft sym (lemma-S^k+l (- b) b)) ⟩
    (S^ -b⁻¹ • H ^ 3) • (S^ (- b) • S^ b) • H • S^ b⁻¹ • H • S^ b • H ≈⟨ special-assoc (□ ^ 2 • □ ^ 2 • □ ) (□ ^ 3 • □ • □) auto ⟩
    (S^ -b⁻¹ • H ^ 3 • S^ (- b)) • (S^ b • H • S^ b⁻¹ • H • S^ b • H) ≈⟨ refl ⟩
    (S^ -b⁻¹ • H ^ 3 • S^ (- b)) • M b' ∎
    where
    open PB ((₁₊ n) QRel,_===_)
    open PP ((₁₊ n) QRel,_===_)
    open SR word-setoid
    open Sym0-Rewriting n
    open Lemmas0 n

    open Pattern-Assoc
    b = b' .proj₁
    -b⁻¹ = - ((b' ⁻¹) .proj₁)
    b⁻¹ = ((b' ⁻¹) .proj₁)




  lemma-Euler' : let open PB ((₂₊ n) QRel,_===_) in ∀ b' -> let b = b' .proj₁ in let -b⁻¹ = - ((b' ⁻¹) .proj₁) in
    H ^ 3 • S^ b • H ≈ (S^ -b⁻¹ • H • S^ (- b)) • M b'
  lemma-Euler' {n} b' = begin
    H ^ 3 • S^ b • H ≈⟨ by-assoc auto ⟩
    H ^ 2 • H • S^ b • H ≈⟨ (cright lemma-Euler b') ⟩
    H ^ 2 • (S^ -b⁻¹ • H ^ 3 • S^ (- b)) • M b' ≈⟨ special-assoc (□ • □ ^ 3 • □) (□ ^ 2 • □ ^ 3) auto ⟩
    (H ^ 2 • S^ -b⁻¹) • H ^ 3 • S^ (- b) • M b' ≈⟨ (cleft word-comm 1 (toℕ -b⁻¹) (trans assoc (axiom comm-HHS))) ⟩
    (S^ -b⁻¹ • H ^ 2) • H ^ 3 • S^ (- b) • M b' ≈⟨ special-assoc (□ ^ 2 • □ ^ 3) (□ • □ ^ 2 • □ ^ 2) auto ⟩
    S^ -b⁻¹ • (H ^ 2 • H ^ 3) • S^ (- b) • M b' ≈⟨ (cright cleft rewrite-sym0 100 auto) ⟩
    S^ -b⁻¹ • H • S^ (- b) • M b' ≈⟨ trans (by-assoc auto) (sym assoc) ⟩
    (S^ -b⁻¹ • H • S^ (- b)) • M b' ∎
    where
    open PB ((₂₊ n) QRel,_===_)
    open PP ((₂₊ n) QRel,_===_)
    open SR word-setoid
    open Commuting-Symplectic (n)
    open Sym0-Rewriting (suc n)
    open Lemmas0 (₁₊ n)

    open Pattern-Assoc
    b = b' .proj₁
    -b⁻¹ = - ((b' ⁻¹) .proj₁)
    b⁻¹ = ((b' ⁻¹) .proj₁)


  lemma-Euler-v2 : let open PB ((₂₊ n) QRel,_===_) in ∀ b' -> let b = b' .proj₁ in let b⁻¹ = ((b' ⁻¹) .proj₁) in let -b⁻¹ = - b⁻¹ in
  
    H • S^ b • H ≈ (S^ -b⁻¹ • H • S^ (- b)) • M (-' b')

  lemma-Euler-v2 {n} b' = begin
    H • S^ b • H ≈⟨ (cleft rewrite-sym0 100 auto) ⟩
    (H ^ 2 • H ^ 3) • S^ b • H ≈⟨ assoc ⟩
    H ^ 2 • H ^ 3 • S^ b • H ≈⟨ (cright lemma-Euler' b') ⟩
    H ^ 2 • (S^ -b⁻¹ • H • S^ (- b)) • M b' ≈⟨ special-assoc (□ • □ ^ 3 • □) (□ ^ 2 • □ ^ 3) auto ⟩
    (H ^ 2 • S^ -b⁻¹) • H • S^ (- b) • M b' ≈⟨ (cleft word-comm 1 (toℕ -b⁻¹) (trans assoc (axiom comm-HHS))) ⟩
    (S^ -b⁻¹ • H ^ 2) • H • S^ (- b) • M b' ≈⟨ special-assoc (□ ^ 3 • □ ^ 3) (□ ^ 2 • (□ ^ 2 • □) • □) auto ⟩
    (S^ -b⁻¹ • H) • (H ^ 2 • S^ (- b)) • M b' ≈⟨ (cright cleft word-comm 1 (toℕ (- b)) (trans assoc (axiom comm-HHS))) ⟩
    (S^ -b⁻¹ • H) • (S^ (- b) • H ^ 2) • M b' ≈⟨ (cright assoc) ⟩
    (S^ -b⁻¹ • H) • S^ (- b) • H ^ 2 • M b' ≈⟨ (cright cright cleft lemma-HH-M-1) ⟩
    (S^ -b⁻¹ • H) • S^ (- b) • M -'₁ • M b' ≈⟨ (cright cright axiom (M-mul -'₁ b')) ⟩
    (S^ -b⁻¹ • H) • S^ (- b) • M (-'₁ *' b') ≈⟨ (cright cright aux-MM ((-'₁ *' b').proj₂) ((-' b') .proj₂) (-1*x≈-x b)) ⟩
    (S^ -b⁻¹ • H) • S^ (- b) • M (-' b') ≈⟨ special-assoc (□ ^ 2 • □ ^ 2) (□ ^ 3 • □) auto ⟩
    (S^ -b⁻¹ • H • S^ (- b)) • M (-' b') ∎
    where
    open PB ((₂₊ n) QRel,_===_)
    open PP ((₂₊ n) QRel,_===_)
    open SR word-setoid
    open Commuting-Symplectic (n)
    open Sym0-Rewriting (suc n)
    open Lemmas0 (₁₊ n)

    open Pattern-Assoc
    b = b' .proj₁
    -b⁻¹ = - ((b' ⁻¹) .proj₁)
    b⁻¹ = ((b' ⁻¹) .proj₁)



  semi-HM' : let open PB ((₁₊ n) QRel,_===_) in ∀ (x : ℤ* ₚ) -> H • M (x ⁻¹) ≈ M x • H
  semi-HM' {n} x@(x' , nzx) = begin
    H • M (x ⁻¹) ≈⟨ semi-HM (x ⁻¹) ⟩
    M (x ⁻¹ ⁻¹) • H ≈⟨ (cleft aux-MM ((x ⁻¹ ⁻¹) .proj₂) nzx (inv-involutive x)) ⟩
    M x • H ∎
    where
    open PB ((₁₊ n) QRel,_===_)
    open PP ((₁₊ n) QRel,_===_)
    open SR word-setoid
    open Sym0-Rewriting n
    open Lemmas0 n
    x⁻¹ = x ⁻¹

  aux-comm-HH-M : let open PB ((₁₊ n) QRel,_===_) in ∀ x ->
    H ^ 2 • M x ≈ M x • H ^ 2
  aux-comm-HH-M {n} x = begin
    (H ^ 2 • M x) ≈⟨ (cleft lemma-HH-M-1) ⟩
    (M -'₁ • M x) ≈⟨ axiom (M-mul -'₁ x) ⟩
    M (-'₁ *' x) ≈⟨ aux-MM ((-'₁ *' x) .proj₂) ((x *' -'₁) .proj₂) (*-comm (-'₁ .proj₁) (x .proj₁)) ⟩
    M (x *' -'₁) ≈⟨ sym (axiom (M-mul x -'₁)) ⟩
    M x • M -'₁ ≈⟨ (cright sym lemma-HH-M-1) ⟩
    M x • H ^ 2 ∎
    where
    open PB ((₁₊ n) QRel,_===_)
    open PP ((₁₊ n) QRel,_===_)
    open SR word-setoid
    open Sym0-Rewriting n
    open Lemmas0 n
    x⁻¹ = x ⁻¹


  semi-MH³ : let open PB ((₁₊ n) QRel,_===_) in ∀ (x : ℤ* ₚ) -> H ^ 3 • M (x ⁻¹) ≈ M x • H ^ 3
  semi-MH³ {n} x@(x' , nzx) = begin
    H ^ 3 • M (x ⁻¹) ≈⟨ by-assoc auto ⟩
    H ^ 2 • H • M (x ⁻¹) ≈⟨ (cright semi-HM' (x)) ⟩
    H ^ 2 • M (x) • H ≈⟨ sym assoc ⟩
    (H ^ 2 • M (x)) • H ≈⟨ (cleft aux-comm-HH-M (x)) ⟩
    (M (x) • H ^ 2) • H ≈⟨ assoc ⟩
    M (x) • H ^ 2 • H ≈⟨ (cright assoc) ⟩
    M x • H ^ 3 ∎
    where
    open PB ((₁₊ n) QRel,_===_)
    open PP ((₁₊ n) QRel,_===_)
    open SR word-setoid
    open Sym0-Rewriting n
    open Lemmas0 n
    x⁻¹ = x ⁻¹



  semi-H³M : let open PB ((₁₊ n) QRel,_===_) in ∀ (x : ℤ* ₚ) -> H ^ 3 • M x ≈ M (x ⁻¹) • H ^ 3
  semi-H³M {n} x@(x' , nzx) = begin
    H ^ 3 • M (x) ≈⟨ by-assoc auto ⟩
    H ^ 2 • H • M (x) ≈⟨ (cright semi-HM (x)) ⟩
    H ^ 2 • M (x ⁻¹) • H ≈⟨ sym assoc ⟩
    (H ^ 2 • M (x ⁻¹)) • H ≈⟨ (cleft aux-comm-HH-M (x ⁻¹)) ⟩
    (M (x ⁻¹) • H ^ 2) • H ≈⟨ assoc ⟩
    M (x ⁻¹) • H ^ 2 • H ≈⟨ (cright assoc) ⟩
    M (x ⁻¹) • H ^ 3 ∎
    where
    open PB ((₁₊ n) QRel,_===_)
    open PP ((₁₊ n) QRel,_===_)
    open SR word-setoid
    open Sym0-Rewriting n
    open Lemmas0 n
    x⁻¹ = x ⁻¹


  lemma-S⁻¹^k : let open PB ((₁₊ n) QRel,_===_) in ∀ k -> let k' = toℕ k in S⁻¹ ^ k' ≈ S^ (- k)
  lemma-S⁻¹^k {n} k = begin
    S⁻¹ ^ k' ≈⟨ (lemma-^^ S p-1 k') ⟩
    S ^ (p-1 Nat.* k') ≈⟨ (lemma-S^k-% (p-1 Nat.* k')) ⟩
    S ^ ((p-1 Nat.* k') Nat.% p) ≈⟨ (refl' (Eq.cong (\ xx -> S ^ ((xx Nat.* toℕ k) Nat.% p)) (Eq.sym (toℕ-fromℕ< (NP.≤-refl {p}))))) ⟩
    S ^ ((toℕ (ₚ₋₁) Nat.* k') Nat.% p) ≈⟨ (refl' (Eq.cong (\ xx -> S ^ ((toℕ xx Nat.* toℕ k) Nat.% p)) (p-1=-1ₚ))) ⟩
    S ^ ((toℕ (- 1ₚ) Nat.* toℕ k) Nat.% p) ≈⟨ (refl' (Eq.cong (S ^_) (Eq.sym (toℕ-fromℕ< (m%n<n (toℕ (- 1ₚ) Nat.* toℕ k)  p))))) ⟩
    S^ (- 1ₚ * k) ≈⟨ (refl' (Eq.cong S^ (-1*x≈-x k))) ⟩
    S^ -k ∎
    where
    open PB ((₁₊ n) QRel,_===_)
    open PP ((₁₊ n) QRel,_===_)
    open SR word-setoid
    open Sym0-Rewriting n
    open Lemmas0 n
    k' = toℕ k
    -k = - k



  aux-ww^k : ∀ w k -> let open PB ((₁₊ n) QRel,_===_) in 
    w • w ^ k ≈ w ^ (₁₊ k)
  aux-ww^k {n} w ₀ = right-unit
    where
    open PB ((₁₊ n) QRel,_===_)
  aux-ww^k {n} w (₁₊ k) = refl
    where
    open PB ((₁₊ n) QRel,_===_)


  aux-S^-^  : let open PB ((₁₊ n) QRel,_===_) in  ∀ a k -> (nza : a ≢ ₀) -> let j = toℕ a in
    S^ k ^ j ≈ S^ (k * a)
  aux-S^-^ {n} a k nza = begin
    S^ k ^ j ≈⟨ refl ⟩
    (S ^ toℕ k) ^ j ≈⟨ lemma-^^ S (toℕ k) j ⟩
    S ^ (toℕ k Nat.* j) ≈⟨ (lemma-S^k-% (toℕ k Nat.* j)) ⟩
    S ^ ((toℕ k Nat.* toℕ a) Nat.% p)  ≈⟨ refl' (Eq.cong (S ^_) (Eq.sym (toℕ-fromℕ< (m%n<n (toℕ k Nat.* toℕ a) p)))) ⟩
    S ^ toℕ (fromℕ< (m%n<n (toℕ k Nat.* toℕ a) p)) ≈⟨ refl ⟩
    S ^ toℕ (k * a) ≈⟨ refl ⟩
    S^ (k * a) ∎
    where
    j = toℕ a
    open PB ((₁₊ n) QRel,_===_)
    open PP ((₁₊ n) QRel,_===_)
    open SR word-setoid
    open Sym0-Rewriting n
    open Lemmas0 n




  lemma-Euler′ : let open PB ((₁₊ n) QRel,_===_) in ∀ b' -> let b = b' .proj₁ in let -b⁻¹ = - ((b' ⁻¹) .proj₁) in
    H • S^ b • H ≈ M (-' b' ⁻¹) • (S^ (- b) • H • S^ (-b⁻¹))
  lemma-Euler′ {n} b' = begin
    (H • S^ b • H) ≈⟨ ( lemma-Euler b') ⟩
    ((S^ -b⁻¹ • H ^ 3 • S^ -b ) • M b') ≈⟨ sym (cong refl right-unit) ⟩
    (S^ -b⁻¹ • H ^ 3 • S^ -b) • M b' • ε ≈⟨ (cright cright rewrite-sym0 100 auto) ⟩
    (S^ -b⁻¹ • H ^ 3 • S^ -b) • M b' • HH • H ^ 2 ≈⟨ (cright cright cleft lemma-HH-M-1) ⟩
    (S^ -b⁻¹ • H ^ 3 • S^ -b) • M b' • M -'₁ • H ^ 2 ≈⟨ (cright  sym assoc ) ⟩
    (S^ -b⁻¹ • H ^ 3 • S^ -b) • (M b' • M -'₁) • H ^ 2 ≈⟨ (cright cleft axiom (M-mul b' -'₁)) ⟩
    (S^ -b⁻¹ • H ^ 3 • S^ -b) • M (b' *' -'₁) • H ^ 2 ≈⟨ (cright cleft aux-MM ((b' *' -'₁) .proj₂) ((-' b') .proj₂) (Eq.trans (*-comm b (fromℕ< _)) (-1*x≈-x b))) ⟩
    (S^ -b⁻¹ • H ^ 3 • S^ -b) • M (-' b') • H ^ 2 ≈⟨ special-assoc (□ ^ 3 • □ ^ 2) (□ ^ 4 • □) auto ⟩
    (S^ -b⁻¹ • H ^ 3 • S^ -b • M (-' b')) • H ^ 2 ≈⟨ special-assoc (□ ^ 4 • □) (□ ^ 5) auto ⟩
    S^ (-b⁻¹) • H ^ 3 • S^ -b • M (-' b') • H ^ 2 ≈⟨ (cright cright (cright sym (aux-comm-HH-M (-' b')))) ⟩
    S^ (-b⁻¹) • H ^ 3 • S^ -b • H ^ 2 • M (-' b') ≈⟨ (cright cright sym assoc) ⟩
    S^ (-b⁻¹) • H ^ 3 • (S^ -b • H ^ 2) • M (-' b') ≈⟨ (cright cright cleft word-comm (toℕ -b) 1 (sym (trans assoc (axiom comm-HHS)))) ⟩
    S^ (-b⁻¹) • H ^ 3 • (H ^ 2 • S^ -b) • M (-' b') ≈⟨ (cright by-assoc auto) ⟩
    S^ (-b⁻¹) • (H ^ 3 • H ^ 2) • S^ (-b) • M (-' b') ≈⟨ (cright cleft rewrite-sym0 100 auto) ⟩
    S^ (-b⁻¹) • H • S^ (-b) • M (-' b') ≈⟨ cong (refl' (Eq.cong S^ (  (Eq.sym (*-identityˡ -b⁻¹))))) (cright cleft refl' (Eq.cong S^ ((Eq.sym (*-identityˡ -b))))) ⟩
    S^ (₁ * -b⁻¹) • H • S^ (₁ * -b) • M (-' b') ≈⟨ cong (refl' (Eq.cong S^ ( Eq.cong (_* -b⁻¹) (Eq.sym (aux--b*-b⁻¹ b'))))) (cright cleft refl' (Eq.cong S^ (Eq.cong (_* -b) (Eq.sym (aux--b⁻¹*-b b'))))) ⟩
    S^ (-b * -b⁻¹ * -b⁻¹) • H • S^ (-b⁻¹ * -b * -b) • M (-' b') ≈⟨ cong (refl' (Eq.cong S^ ( (*-assoc -b -b⁻¹ -b⁻¹)))) (cright cleft refl' (Eq.cong S^ (*-assoc -b⁻¹ -b -b))) ⟩
    S^ (-b * (-b⁻¹ * -b⁻¹)) • H • S^ (-b⁻¹ * (-b * -b)) • M (-' b') ≈⟨ (cright cright sym (lemma-MS^k -b -b⁻¹ ((-' b') .proj₂))) ⟩
    S^ (-b * (-b⁻¹ * -b⁻¹)) • H • M (-' b') • S^ (-b⁻¹) ≈⟨ (cright sym assoc) ⟩
    S^ (-b * (-b⁻¹ * -b⁻¹)) • (H • M ((-' b'))) • S^ (-b⁻¹) ≈⟨ (cright (cleft (cright aux-MM (((-' b')) .proj₂) (((-' b') ⁻¹ ⁻¹).proj₂) (Eq.sym (inv-involutive (-' b')))))) ⟩
    S^ (-b * (-b⁻¹ * -b⁻¹)) • (H • M ((-' b') ⁻¹ ⁻¹)) • S^ (-b⁻¹) ≈⟨ (cright cleft semi-HM' ((-' b') ⁻¹)) ⟩
    S^ (-b * (-b⁻¹ * -b⁻¹)) • (M ((-' b') ⁻¹) • H) • S^ (-b⁻¹) ≈⟨ (cright (cleft (cleft aux-MM (((-' b') ⁻¹) .proj₂) ((-' (b' ⁻¹)) .proj₂) (inv-neg-comm b')))) ⟩
    S^ (-b * (-b⁻¹ * -b⁻¹)) • (M (-' (b' ⁻¹)) • H) • S^ (-b⁻¹) ≈⟨ special-assoc (□ • □ ^ 2 • □) (□ ^ 2 • □ ^ 2) auto ⟩
    (S^ (-b * (-b⁻¹ * -b⁻¹)) • M (-' (b' ⁻¹))) • H • S^ (-b⁻¹) ≈⟨ (cleft sym ( lemma-MS^k ((-' (b' ⁻¹)) .proj₁) -b ((-' (b' ⁻¹)) .proj₂))) ⟩
    (M (-' (b' ⁻¹)) • S^ -b) • H • S^ (-b⁻¹) ≈⟨ assoc ⟩
    M (-' (b' ⁻¹)) • (S^ (- b) • H • S^ (-b⁻¹)) ∎
    where
    open PB ((₁₊ n) QRel,_===_)
    open PP ((₁₊ n) QRel,_===_)
    open SR word-setoid
    open Sym0-Rewriting n
    open Lemmas0 n

    open Pattern-Assoc
    b = b' .proj₁
    -b⁻¹ = - ((b' ⁻¹) .proj₁)
    b⁻¹ = ((b' ⁻¹) .proj₁)
    -b = - b
    aux : ((-' b' ⁻¹) ⁻¹) .proj₁ ≡ -b
    aux = inv-inv-neg b'



  lemma-Euler′' : let open PB ((₁₊ n) QRel,_===_) in ∀ b' -> let b = b' .proj₁ in let -b⁻¹ = - ((b' ⁻¹) .proj₁) in
    H • S^ b • H ^ 3 ≈ M (-' b' ⁻¹) • (S^ (- b) • H ^ 3 • S^ (-b⁻¹))
  lemma-Euler′' {n} b' = begin
    H • S^ b • H ^ 3 ≈⟨ special-assoc (□ ^ 4) (□ ^ 3 • □) auto ⟩
    (H • S^ b • H) • H ^ 2 ≈⟨ (cleft lemma-Euler′ b') ⟩
    (M (-' b' ⁻¹) • (S^ (- b) • H • S^ (-b⁻¹))) • H ^ 2 ≈⟨ assoc ⟩
    M (-' b' ⁻¹) • (S^ (- b) • H • S^ (-b⁻¹)) • H ^ 2 ≈⟨ (cright trans assoc (cong refl assoc)) ⟩
    M (-' b' ⁻¹) • S^ (- b) • H • S^ (-b⁻¹) • H ^ 2 ≈⟨ (cright cright cright word-comm (toℕ -b⁻¹) 1 (sym (trans assoc (axiom comm-HHS)))) ⟩
    M (-' b' ⁻¹) • S^ (- b) • H • H ^ 2 • S^ (-b⁻¹) ≈⟨ (cright sym (cong refl assoc)) ⟩
    M (-' b' ⁻¹) • (S^ (- b) • H ^ 3 • S^ (-b⁻¹)) ∎
    where
    open PB ((₁₊ n) QRel,_===_)
    open PP ((₁₊ n) QRel,_===_)
    open SR word-setoid
    open Sym0-Rewriting n
    open Lemmas0 n

    open Pattern-Assoc
    b = b' .proj₁
    -b⁻¹ = - ((b' ⁻¹) .proj₁)
    b⁻¹ = ((b' ⁻¹) .proj₁)
    -b = - b
    aux : ((-' b' ⁻¹) ⁻¹) .proj₁ ≡ -b
    aux = inv-inv-neg b'


  lemma-Euler-Mˡ : let open PB ((₁₊ n) QRel,_===_) in ∀ b' -> let b = b' .proj₁ in let -b⁻¹ = - ((b' ⁻¹) .proj₁) in let -b = - b in
    H • S^ b • H ^ 3 ≈ M (b' ⁻¹) • S^ -b • H • S^ -b⁻¹ 
  lemma-Euler-Mˡ {n} b' = begin
    H • S^ b • H ^ 3 ≈⟨ lemma-Euler′' b' ⟩
    M (-' b' ⁻¹) • (S^ (- b) • H ^ 3 • S^ (-b⁻¹)) ≈⟨ (cright special-assoc (□ • □ ^ 3 • □) (□ ^ 3 • □ ^ 2) auto) ⟩
    M (-' b' ⁻¹) • ((S^ (- b) • H ^ 2) • H • S^ (-b⁻¹)) ≈⟨ (cright cleft word-comm (toℕ (-b)) 1 (sym (trans assoc (axiom comm-HHS)))) ⟩
    M (-' b' ⁻¹) • ((H ^ 2 • S^ (- b)) • H • S^ (-b⁻¹)) ≈⟨ special-assoc (□ • ((□ ^ 2 • □) • □)) (□ ^ 3 • □ ^ 2) auto ⟩
    (M (-' b' ⁻¹) • HH) • S^ (- b) • H • S^ (-b⁻¹) ≈⟨ (cleft cright lemma-HH-M-1) ⟩
    (M (-' b' ⁻¹) • M -'₁) • S^ -b • H • S^ -b⁻¹ ≈⟨ (cleft axiom (M-mul (-' b' ⁻¹) -'₁)) ⟩
    M (-' b' ⁻¹ *' -'₁) • S^ -b • H • S^ -b⁻¹ ≈⟨ (cleft aux-MM ((-' b' ⁻¹ *' -'₁) .proj₂) ((b' ⁻¹) .proj₂) (Eq.trans (Eq.trans (Eq.sym (-‿distribʳ-* -b⁻¹ ₁)) (Eq.cong -_ (*-identityʳ -b⁻¹))) (-‿involutive (b⁻¹) ))) ⟩
    M (b' ⁻¹) • S^ -b • H • S^ -b⁻¹  ∎
    where
    open PB ((₁₊ n) QRel,_===_)
    open PP ((₁₊ n) QRel,_===_)
    open SR word-setoid
    open Sym0-Rewriting n
    open Lemmas0 n

    open Pattern-Assoc
    b = b' .proj₁
    -b⁻¹ = - ((b' ⁻¹) .proj₁)
    b⁻¹ = ((b' ⁻¹) .proj₁)
    -b = - b
    aux : ((-' b' ⁻¹) ⁻¹) .proj₁ ≡ -b
    aux = inv-inv-neg b'


  lemma-Euler-Mˡ' : let open PB ((₁₊ n) QRel,_===_) in ∀ b' -> let b = b' .proj₁ in let -b⁻¹ = - ((b' ⁻¹) .proj₁) in let -b = - b in
    H ^ 3 • S^ b • H ≈ M (b' ⁻¹) • S^ -b • H • S^ -b⁻¹ 
  lemma-Euler-Mˡ' {n} b' = begin
    H ^ 3 • S^ b • H ≈⟨ by-assoc auto ⟩
    H • (H ^ 2 • S^ b) • H ≈⟨ (cright cleft word-comm 1 (toℕ b) (trans assoc (axiom comm-HHS))) ⟩
    H • (S^ b • H ^ 2) • H ≈⟨ (cright assoc) ⟩
    H • S^ b • H ^ 2 • H ≈⟨ (cright cright assoc) ⟩
    H • S^ b • H ^ 3 ≈⟨ lemma-Euler-Mˡ b' ⟩
    M (b' ⁻¹) • S^ -b • H • S^ -b⁻¹  ∎
    where
    open PB ((₁₊ n) QRel,_===_)
    open PP ((₁₊ n) QRel,_===_)
    open SR word-setoid
    open Sym0-Rewriting n
    open Lemmas0 n

    open Pattern-Assoc
    b = b' .proj₁
    -b⁻¹ = - ((b' ⁻¹) .proj₁)
    b⁻¹ = ((b' ⁻¹) .proj₁)
    -b = - b
    aux : ((-' b' ⁻¹) ⁻¹) .proj₁ ≡ -b
    aux = inv-inv-neg b'




  aux--2k-2k' : let open PB ((₁₊ n) QRel,_===_) in ∀ k ->
    let
      -k = (p-1) Nat.* k
      -2k = -k Nat.+ -k
      k' : ℤ ₚ
      k' = fromℕ< (m%n<n k p)
      -k' = - k'
      -2k' = -k' + -k'
    in
      S^ -2k' ≈ S ^ (-2k Nat.% p)
  aux--2k-2k' {n} k = begin
    S^ -2k' ≈⟨ refl' (Eq.cong (S ^_) aux--2k-2k'') ⟩
    S ^ ((toℕ -k' Nat.% p Nat.+ toℕ -k' Nat.% p) Nat.% p) ≈⟨ sym (lemma-S^k-% (toℕ -k' Nat.% p Nat.+ toℕ -k' Nat.% p)) ⟩
    S ^ ((toℕ -k' Nat.% p Nat.+ toℕ -k' Nat.% p)) ≈⟨ lemma-^-+ S (toℕ -k' Nat.% p) (toℕ -k' Nat.% p) ⟩
    S ^ (toℕ -k' Nat.% p) • S ^ (toℕ -k' Nat.% p) ≈⟨ sym (cong (lemma-S^k-% (toℕ -k')) (lemma-S^k-% (toℕ -k'))) ⟩
    S ^ (toℕ -k') • S ^ (toℕ -k') ≈⟨ refl ⟩
    S^ -k' • S^ -k' ≈⟨ cong aux aux ⟩
    S ^ -k • S ^ -k ≈⟨ sym (lemma-^-+ S -k -k) ⟩
    S ^ (-2k ) ≈⟨ lemma-S^k-% -2k ⟩
    S ^ (-2k Nat.% p) ∎
    where

    -k = (p-1) Nat.* k
    -2k = -k Nat.+ -k
    k' : ℤ ₚ
    k' = fromℕ< (m%n<n k p)
    -k' = - k'
    -2k' = -k' + -k'
    aux--2k-2k'' : toℕ -2k' ≡ (toℕ -k' Nat.% p Nat.+ toℕ -k' Nat.% p) Nat.% p
    aux--2k-2k'' = begin
      toℕ -2k' ≡⟨ auto ⟩
      toℕ (fromℕ< (m%n<n (toℕ -k' Nat.+ toℕ -k') p)) ≡⟨ toℕ-fromℕ< (m%n<n (toℕ -k' Nat.+ toℕ -k') p) ⟩
      (toℕ -k' Nat.+ toℕ -k') Nat.% p ≡⟨ %-distribˡ-+ (toℕ -k') (toℕ -k') p ⟩
      (toℕ -k' Nat.% p Nat.+ toℕ -k' Nat.% p) Nat.% p ∎
      where
      open ≡-Reasoning

    open PB ((₁₊ n) QRel,_===_)
    open PP ((₁₊ n) QRel,_===_)
    open SR word-setoid
    open Sym0-Rewriting n
    open Lemmas0 n

    open Pattern-Assoc
    aux : S^ -k' ≈ S ^ -k
    aux = begin
      S^ -k' ≈⟨ refl' (Eq.cong S^ (Eq.sym (-1*x≈-x k'))) ⟩
      S^ (- 1ₚ * k') ≈⟨  refl ⟩
      S ^ toℕ (fromℕ< (m%n<n (toℕ (- 1ₚ) Nat.* toℕ k') p)) ≈⟨  refl' (Eq.cong (S ^_) (toℕ-fromℕ< (m%n<n (toℕ (- 1ₚ) Nat.* toℕ k') p))) ⟩
      S ^ ((toℕ (- 1ₚ) Nat.* toℕ k') Nat.% p) ≈⟨  sym (lemma-S^k-% (toℕ (- 1ₚ) Nat.* toℕ k')) ⟩
      S ^ (toℕ (- 1ₚ) Nat.* toℕ k') ≈⟨  sym (lemma-^^ S (toℕ (- 1ₚ)) (toℕ k')) ⟩
      (S ^ toℕ (- 1ₚ)) ^ toℕ k' ≈⟨  refl' (Eq.cong (\ xx -> (S ^ toℕ xx) ^ toℕ k') (Eq.sym p-1=-1ₚ)) ⟩
      (S ^ toℕ (ₚ₋₁)) ^ toℕ k' ≈⟨   refl' (Eq.cong (\ xx -> (S ^ xx) ^ toℕ k') lemma-toℕ-ₚ₋₁) ⟩
      (S ^ p-1) ^ toℕ k' ≈⟨  refl' (Eq.cong ((S ^ p-1) ^_) (toℕ-fromℕ< (m%n<n k p))) ⟩
      (S ^ p-1) ^ (k Nat.% p) ≈⟨  lemma-^^' S p-1 ((k Nat.% p)) ⟩
      (S ^ (k Nat.% p)) ^ p-1 ≈⟨  lemma-^-cong (S ^ (k Nat.% p)) (S ^ k) p-1 (sym (lemma-S^k-% k)) ⟩
      (S ^ k) ^ p-1 ≈⟨  lemma-^^' S k p-1 ⟩
      (S ^ p-1) ^ k ≈⟨  lemma-^^ S p-1 k ⟩
      S ^ -k ∎



