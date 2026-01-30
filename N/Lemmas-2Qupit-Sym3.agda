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
open import Data.Fin.Properties using (suc-injective ; toℕ-inject₁ ; toℕ-fromℕ)
import Data.Nat.Properties as NP
open import Presentation.GroupLike
open import Presentation.Tactics hiding ([_])
open import Data.Nat.Primality



module N.Lemmas-2Qupit-Sym3 (p-2 : ℕ) (p-prime : Prime (2+ p-2))  where

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
open import N.Lemmas-2Qupit-Sym p-2 p-prime
open import N.Lemmas4-Sym p-2 p-prime


open Symplectic renaming (M to ZM)
open Lemmas-Sym

open Symplectic-GroupLike


private
  variable
    n : ℕ

aux-CXᵏ : let open PB ((₂₊ n) QRel,_===_) in
  ∀ k -> CX ^ k ≈ H ^ 3 • CZ ^ k • H 
aux-CXᵏ {n} k@0 = rewrite-sym0 100 auto
  where
  open Sym0-Rewriting (₁₊ n)
aux-CXᵏ {n} k@1 = PB.refl
aux-CXᵏ {n} k@(₁₊ k'@(₁₊ k'')) = begin
  CX ^ k ≈⟨ (cright aux-CXᵏ k') ⟩
  (H ↓ ^ 3 • CZ • H ↓) • H ^ 3 • CZ ^ k' • H  ≈⟨ special-assoc (□ ^ 3 • □ ^ 3) (□ ^ 4 • □ ^ 2) auto ⟩
  (H ↓ ^ 3 • CZ • H ↓ • H ^ 3) • CZ ^ k' • H  ≈⟨ (cleft rewrite-sym0 100 auto) ⟩
  (H ↓ ^ 3 • CZ) • CZ ^ k' • H  ≈⟨ special-assoc (□ ^ 2 • □ ^ 2) (□ • □ ^ 2 • □) auto ⟩
  H ^ 3 • CZ ^ k • H ∎
  where
  open PB ((₂₊ n) QRel,_===_) hiding (_===_)
  open PP ((₂₊ n) QRel,_===_)
  open Pattern-Assoc
  open SR word-setoid
  open Sym0-Rewriting (₁₊ n)



aux-CX^k : let open PB ((₂₊ n) QRel,_===_) in
  ∀ k -> CX^ k ≈ H ^ 3 • CZ^ k • H 
aux-CX^k {n} k = aux-CXᵏ (toℕ k)


aux-XCᵏ : let open PB ((₂₊ n) QRel,_===_) in
  ∀ k -> XC ^ k ≈ H ↑ ^ 3 • CZ ^ k • H ↑
aux-XCᵏ {n} k@0 = rewrite-sym0 100 auto
  where
  open Sym0-Rewriting (₁₊ n)
aux-XCᵏ {n} k@1 = PB.refl
aux-XCᵏ {n} k@(₁₊ k'@(₁₊ k'')) = begin
  XC ^ k ≈⟨ (cright aux-XCᵏ k') ⟩
  (H ↑  ^ 3 • CZ • H ↑ ) • H ↑ ^ 3 • CZ ^ k' • H ↑  ≈⟨ special-assoc (□ ^ 3 • □ ^ 3) (□ ^ 4 • □ ^ 2) auto ⟩
  (H ↑  ^ 3 • CZ • H ↑  • H ↑ ^ 3) • CZ ^ k' • H ↑  ≈⟨ (cleft rewrite-sym0 100 auto) ⟩
  (H ↑  ^ 3 • CZ) • CZ ^ k' • H ↑  ≈⟨ special-assoc (□ ^ 2 • □ ^ 2) (□ • □ ^ 2 • □) auto ⟩
  H ↑ ^ 3 • CZ ^ k • H ↑ ∎
  where
  open PB ((₂₊ n) QRel,_===_) hiding (_===_)
  open PP ((₂₊ n) QRel,_===_)
  open Pattern-Assoc
  open SR word-setoid
  open Sym0-Rewriting (₁₊ n)

aux-XC^k : let open PB ((₂₊ n) QRel,_===_) in
  ∀ k -> XC^ k ≈ H ↑ ^ 3 • CZ^ k • H ↑ 
aux-XC^k {n} k = aux-XCᵏ (toℕ k)



lemma-semi-HH↑-CX : let open PB ((₂₊ n) QRel,_===_) in

  HH ↑ • CX ≈ CX^ (- ₁) • HH ↑

lemma-semi-HH↑-CX {n@0} = begin
  HH ↑ • CX ≈⟨ general-comm auto ⟩
  H ^ 3 • (HH ↑ • CZ) • H ≈⟨ (cright cleft  lemma-semi-HH↑-CZ^k ₁) ⟩
  H ^ 3 • (CZ^ (- ₁) • HH ↑) • H ≈⟨ special-assoc (□ • □ ^ 2 • □) (□ ^ 2 • □ ^ 2) auto ⟩
  (H ^ 3 • CZ^ (- ₁)) • HH ↑ • H ≈⟨ (cright general-comm auto) ⟩
  (H ^ 3 • CZ^ (- ₁)) • H • HH ↑ ≈⟨ special-assoc (□ ^ 2 • □ ^ 2) (□ ^ 3 • □) auto ⟩
  (H ^ 3 • CZ^ (- ₁) • H) • HH ↑ ≈⟨ (cleft sym (aux-CX^k (- ₁))) ⟩
  CX^ (- ₁) • HH ↑ ∎
  where
  open PB ((₂₊ n) QRel,_===_) hiding (_===_)
  open PP ((₂₊ n) QRel,_===_)
  open Pattern-Assoc
  open SR word-setoid
  open Lemmas0 (n)
  module L1 = Lemmas0 (₁₊ n)
  open Commuting-Symplectic n
  open Lemmas-2Q n

lemma-semi-HH↑-CX {n@(suc _)} = begin
  HH ↑ • CX ≈⟨ general-comm auto ⟩
  H ^ 3 • (HH ↑ • CZ) • H ≈⟨ (cright cleft  lemma-semi-HH↑-CZ^k ₁) ⟩
  H ^ 3 • (CZ^ (- ₁) • HH ↑) • H ≈⟨ special-assoc (□ • □ ^ 2 • □) (□ ^ 2 • □ ^ 2) auto ⟩
  (H ^ 3 • CZ^ (- ₁)) • HH ↑ • H ≈⟨ (cright general-comm auto) ⟩
  (H ^ 3 • CZ^ (- ₁)) • H • HH ↑ ≈⟨ special-assoc (□ ^ 2 • □ ^ 2) (□ ^ 3 • □) auto ⟩
  (H ^ 3 • CZ^ (- ₁) • H) • HH ↑ ≈⟨ (cleft sym (aux-CX^k (- ₁))) ⟩
  CX^ (- ₁) • HH ↑ ∎
  where
  open PB ((₂₊ n) QRel,_===_) hiding (_===_)
  open PP ((₂₊ n) QRel,_===_)
  open Pattern-Assoc
  open SR word-setoid
  open Lemmas0 (n)
  module L1 = Lemmas0 (₁₊ n)
  open Commuting-Symplectic n
  open Lemmas-2Q n


lemma-semi-HH↑-CX⁻¹ : let open PB ((₂₊ n) QRel,_===_) in
  HH ↑ • CX^ (- ₁) ≈ CX • HH ↑
lemma-semi-HH↑-CX⁻¹ {n} = bbc (HH ↑) (HH ↑) claim
  where
  open PB ((₂₊ n) QRel,_===_) hiding (_===_)
  open PP ((₂₊ n) QRel,_===_)
  open Pattern-Assoc
  open SR word-setoid
  open Lemmas0 (n)
  module L1 = Lemmas0 (₁₊ n)
  open Commuting-Symplectic n
  open Lemmas-2Q n
  open Symplectic-GroupLike
  open Basis-Change _ ((₂₊ n) QRel,_===_) grouplike
  claim : HH ↑ • (HH ↑ • CX^ (- ₁)) • HH ↑ ≈ HH ↑ • (CX • HH ↑) • HH ↑
  claim = begin
    HH ↑ • (HH ↑ • CX^ (- ₁)) • HH ↑ ≈⟨ special-assoc (□ • □ ^ 2 • □) (□ ^ 2 • □ ^ 2) auto ⟩
    (HH ↑ • HH ↑) • CX^ (- ₁) • HH ↑ ≈⟨ (cleft trans assoc (axiom (cong↑ order-H))) ⟩
    ε • CX^ (- ₁) • HH ↑ ≈⟨ left-unit ⟩
    CX^ (- ₁) • HH ↑ ≈⟨ sym lemma-semi-HH↑-CX ⟩
    (HH ↑ • CX) ≈⟨ sym right-unit ⟩
    (HH ↑ • CX) • ε ≈⟨ (cright sym (trans assoc (axiom (cong↑ order-H)))) ⟩
    (HH ↑ • CX) • HH ↑ • HH ↑ ≈⟨ sym (special-assoc (□ • □ ^ 2 • □) (□ ^ 2 • □ ^ 2) auto ) ⟩
    HH ↑ • (CX • HH ↑) • HH ↑ ∎




lemma-semi-HH↓-CX : let open PB ((₂₊ n) QRel,_===_) in

  HH ↓ • CX ≈ CX^ (- ₁) • HH ↓

lemma-semi-HH↓-CX {n@0} = begin
  HH ↓ • CX ≈⟨ general-comm auto ⟩
  H ^ 3 • (HH ↓ • CZ) • H ≈⟨ (cright cleft  lemma-semi-HH↓-CZ^k' ₁) ⟩
  H ^ 3 • (CZ^ (- ₁) • HH ↓) • H ≈⟨ special-assoc (□ • □ ^ 2 • □) (□ ^ 2 • □ ^ 2) auto ⟩
  (H ^ 3 • CZ^ (- ₁)) • HH ↓ • H ≈⟨ (cright general-comm auto) ⟩
  (H ^ 3 • CZ^ (- ₁)) • H • HH ↓ ≈⟨ special-assoc (□ ^ 2 • □ ^ 2) (□ ^ 3 • □) auto ⟩
  (H ^ 3 • CZ^ (- ₁) • H) • HH ↓ ≈⟨ (cleft sym (aux-CX^k (- ₁))) ⟩
  CX^ (- ₁) • HH ↓ ∎
  where
  open PB ((₂₊ n) QRel,_===_) hiding (_===_)
  open PP ((₂₊ n) QRel,_===_)
  open Pattern-Assoc
  open SR word-setoid
  open Lemmas0 (n)
  module L1 = Lemmas0 (₁₊ n)
  open Commuting-Symplectic n
  open Lemmas-2Q n

lemma-semi-HH↓-CX {n@(suc _)} = begin
  HH ↓ • CX ≈⟨ general-comm auto ⟩
  H ^ 3 • (HH ↓ • CZ) • H ≈⟨ (cright cleft  lemma-semi-HH↓-CZ^k' ₁) ⟩
  H ^ 3 • (CZ^ (- ₁) • HH ↓) • H ≈⟨ special-assoc (□ • □ ^ 2 • □) (□ ^ 2 • □ ^ 2) auto ⟩
  (H ^ 3 • CZ^ (- ₁)) • HH ↓ • H ≈⟨ (cright general-comm auto) ⟩
  (H ^ 3 • CZ^ (- ₁)) • H • HH ↓ ≈⟨ special-assoc (□ ^ 2 • □ ^ 2) (□ ^ 3 • □) auto ⟩
  (H ^ 3 • CZ^ (- ₁) • H) • HH ↓ ≈⟨ (cleft sym (aux-CX^k (- ₁))) ⟩
  CX^ (- ₁) • HH ↓ ∎
  where
  open PB ((₂₊ n) QRel,_===_) hiding (_===_)
  open PP ((₂₊ n) QRel,_===_)
  open Pattern-Assoc
  open SR word-setoid
  open Lemmas0 (n)
  module L1 = Lemmas0 (₁₊ n)
  open Commuting-Symplectic n
  open Lemmas-2Q n


lemma-semi-HH↓-CX⁻¹ : let open PB ((₂₊ n) QRel,_===_) in
  HH ↓ • CX^ (- ₁) ≈ CX • HH ↓
lemma-semi-HH↓-CX⁻¹ {n} = bbc (HH ↓) (HH ↓) claim
  where
  open PB ((₂₊ n) QRel,_===_) hiding (_===_)
  open PP ((₂₊ n) QRel,_===_)
  open Pattern-Assoc
  open SR word-setoid
  open Lemmas0 (n)
  module L1 = Lemmas0 (₁₊ n)
  open Commuting-Symplectic n
  open Lemmas-2Q n
  open Symplectic-GroupLike
  open Basis-Change _ ((₂₊ n) QRel,_===_) grouplike
  claim : HH ↓ • (HH ↓ • CX^ (- ₁)) • HH ↓ ≈ HH ↓ • (CX • HH ↓) • HH ↓
  claim = begin
    HH ↓ • (HH ↓ • CX^ (- ₁)) • HH ↓ ≈⟨ special-assoc (□ • □ ^ 2 • □) (□ ^ 2 • □ ^ 2) auto ⟩
    (HH ↓ • HH ↓) • CX^ (- ₁) • HH ↓ ≈⟨ (cleft trans assoc (axiom ( order-H))) ⟩
    ε • CX^ (- ₁) • HH ↓ ≈⟨ left-unit ⟩
    CX^ (- ₁) • HH ↓ ≈⟨ sym lemma-semi-HH↓-CX ⟩
    (HH ↓ • CX) ≈⟨ sym right-unit ⟩
    (HH ↓ • CX) • ε ≈⟨ (cright sym (trans assoc (axiom ( order-H)))) ⟩
    (HH ↓ • CX) • HH ↓ • HH ↓ ≈⟨ sym (special-assoc (□ • □ ^ 2 • □) (□ ^ 2 • □ ^ 2) auto ) ⟩
    HH ↓ • (CX • HH ↓) • HH ↓ ∎




lemma-semi-M↓-XC : let open PB ((₂₊ n) QRel,_===_) in

  ∀ m -> ZM m • XC ≈ XC^ (m .proj₁) • ZM m

lemma-semi-M↓-XC {n} m = begin
  ZM m • H ↑ ^ 3 • CZ • H ↑  ≈⟨ special-assoc (□ ^ 4) (□ ^ 2 • □ ^ 2) auto ⟩
  (ZM m • H ↑ ^ 3) • CZ • H ↑  ≈⟨ (cleft aux-comm-m-w↑ m (H ^ 3)) ⟩
  (H ↑ ^ 3 • ZM m) • CZ • H ↑  ≈⟨ special-assoc (□ ^ 2 • □ ^ 2) (□ • □ ^ 2 • □) auto ⟩
  H ↑ ^ 3 • (ZM m • CZ) • H ↑  ≈⟨ (cright cleft axiom (semi-M↓CZ m)) ⟩
  H ↑ ^ 3 • (CZ^ (m .proj₁) • ZM m) • H ↑  ≈⟨ sym (special-assoc (□ ^ 2 • □ ^ 2) (□ • □ ^ 2 • □) auto) ⟩
  (H ↑ ^ 3 • CZ^ (m .proj₁)) • ZM m • H ↑  ≈⟨ (cright aux-comm-m-w↑ m H) ⟩
  (H ↑ ^ 3 • CZ^ (m .proj₁)) • H ↑ • ZM m  ≈⟨ special-assoc (□ ^ 2 • □ ^ 2) (□ ^ 3 • □) auto ⟩
  (H ↑ ^ 3 • CZ^ (m .proj₁) • H ↑) • ZM m  ≈⟨ (cleft sym (aux-XC^k (m .proj₁))) ⟩
  XC^ (m .proj₁) • ZM m ∎
  where
  open PB ((₂₊ n) QRel,_===_) hiding (_===_)
  open PP ((₂₊ n) QRel,_===_)
  open Pattern-Assoc
  open SR word-setoid
  open Lemmas0 (n)
  module L1 = Lemmas0 (₁₊ n)
  open Commuting-Symplectic n
  open Lemmas-2Q n
  open Symplectic-GroupLike
  open Basis-Change _ ((₂₊ n) QRel,_===_) grouplike

--open import N.Boxes p-2 p-prime
open import N.LM-Sym p-2 p-prime
open import N.Pushing.DH p-2 p-prime
open import N.NF1-Sym p-2 p-prime
open import N.Cosets p-2 p-prime
open import Algebra.Properties.Ring (+-*-ring p-2)

A'-of-AZM : A -> ℤ* ₚ -> A
A'-of-AZM ((₀ , ₀) , nz) m = ⊥-elim (nz auto)
A'-of-AZM ((₀ , b@(₁₊ _)) , nz) m = (₀ , b') , aux-b≠0⇒ab≠0  ₀ b' nzb'
  where
  b' = ((b , λ ()) *' m ⁻¹) .proj₁
  nzb' = ((b , λ ()) *' m ⁻¹) .proj₂
  
A'-of-AZM ((a@(₁₊ _) , b) , nz) m = (a' , b') , aux-a≠0⇒ab≠0  (a') b' nza' 
  where
  a' = ((a , λ ()) *' m) .proj₁
  nza' = ((a , λ ()) *' m) .proj₂
  b' = b * (m ⁻¹) .proj₁

lemma-abox-m : ∀ x m -> let open PB ((₁₊ n) QRel,_===_) in
  let x' = A'-of-AZM x m in
  
  [ x ]ᵃ • ZM m ≈ [ x' ]ᵃ

lemma-abox-m ((₀ , ₀) , nz) m = ⊥-elim (nz auto)
lemma-abox-m {n} x@((₀ , b@(₁₊ _)) , nz) m = begin
  ⟦ (b , λ ()) ⁻¹ , ε ⟧ₘ₊ • ZM m ≈⟨ (cleft right-unit) ⟩
  ⟦ (b , λ ()) ⁻¹ ⟧ₘ • ZM m ≈⟨ axiom (M-mul ((b , λ ()) ⁻¹) m) ⟩
  ⟦ (b , λ ()) ⁻¹ *' m ⟧ₘ ≈⟨ aux-MM (((b , λ ()) ⁻¹ *' m) .proj₂) (((b , λ ()) ⁻¹ *' m ⁻¹ ⁻¹) .proj₂) (Eq.cong (b⁻¹ *_) (Eq.sym (inv-involutive m))) ⟩
  ⟦ (b , λ ()) ⁻¹ *' m ⁻¹ ⁻¹ ⟧ₘ ≈⟨ aux-MM (((b , λ ()) ⁻¹ *' m ⁻¹ ⁻¹) .proj₂) ((((b , λ ()) *' m  ⁻¹) ⁻¹) .proj₂) (Eq.sym (inv-distrib (b , λ ()) (m ⁻¹))) ⟩
  ⟦ ((b , λ ()) *' m  ⁻¹) ⁻¹  ⟧ₘ ≈⟨ sym (aux-abox-nzb (((b , λ ()) *' m  ⁻¹) .proj₁) (((b , λ ()) *' m  ⁻¹) .proj₂)) ⟩
  [ x' ]ᵃ ∎
  where
  x' = A'-of-AZM x m   
  open PB ((₁₊ n) QRel,_===_) hiding (_===_)
  open PP ((₁₊ n) QRel,_===_)
  open Pattern-Assoc
  open SR word-setoid
  open Lemmas0 n
  b⁻¹ = ((b , λ ()) ⁻¹) .proj₁

lemma-abox-m {n} x@((a@(₁₊ _), b) , nz) m = begin
  ⟦ (a , λ ()) ⁻¹ , HS^ -b/a  ⟧ₘ₊ • ZM m ≈⟨ special-assoc (□ ^ 3 • □) (□ ^ 4) auto ⟩
  ⟦ (a , λ ()) ⁻¹ ⟧ₘ • H • S^ -b/a • ZM m ≈⟨ (cright cright lemma-S^kM (m .proj₁) -b/a (m .proj₂)) ⟩
  ⟦ (a , λ ()) ⁻¹ ⟧ₘ • H • ZM m • S^ (-b/a * m⁻²) ≈⟨ (cright sym assoc) ⟩
  ⟦ (a , λ ()) ⁻¹ ⟧ₘ • (H • ZM m) • S^ (-b/a * m⁻²) ≈⟨ (cright cleft semi-HM m) ⟩
  ⟦ (a , λ ()) ⁻¹ ⟧ₘ • (ZM (m ⁻¹) • H) • S^ (-b/a * m⁻²) ≈⟨ special-assoc (□ • □ ^ 2 • □) (□ ^ 2 • □ ^ 2) auto ⟩
  (⟦ (a , λ ()) ⁻¹ ⟧ₘ • ZM (m ⁻¹)) • H • S^ (-b/a * m⁻²) ≈⟨ (cleft axiom (M-mul ((a , λ ()) ⁻¹) (m ⁻¹))) ⟩
  ⟦ (a , λ ()) ⁻¹ *' m ⁻¹ ⟧ₘ • H • S^ (-b/a * m⁻²) ≈⟨ (cleft aux-MM (((a , λ ()) ⁻¹ *' m ⁻¹) .proj₂) ((((a , λ ()) *' m) ⁻¹).proj₂) (Eq.sym (inv-distrib (a , λ ()) m))) ⟩
  ⟦ ((a , λ ()) *' m) ⁻¹ ⟧ₘ • H • S^ (-b/a * m⁻²) ≈⟨ cright cright refl' (Eq.cong S^ aux) ⟩
  ⟦ ((a , λ ()) *' m) ⁻¹ ⟧ₘ • H • S^ (-b'/[am]) ≈⟨ sym (aux-abox-nza (a * m .proj₁) ((b * m⁻¹)) ((((a , λ ()) *' m) ) .proj₂)) ⟩
  [ x' ]ᵃ ∎
  where
  x' = A'-of-AZM x m   
  open PB ((₁₊ n) QRel,_===_) hiding (_===_)
  open PP ((₁₊ n) QRel,_===_)
  open Pattern-Assoc
  open SR word-setoid
  open Lemmas0 n
  a⁻¹ = ((a , λ ()) ⁻¹) .proj₁
  -b/a = - b * a⁻¹
  [am]⁻¹ = (((a , λ ()) *' m) ⁻¹) .proj₁
  

  m⁻¹ = (m ⁻¹) .proj₁
  -m⁻¹ = - m⁻¹
  m⁻² = m⁻¹ * m⁻¹

  -b'/[am] = - (b * m⁻¹) * [am]⁻¹
  aux : -b/a * m⁻² ≡ -b'/[am]
  aux = Eq.sym (Eq.trans (Eq.cong (_* [am]⁻¹) (-‿distribˡ-* b m⁻¹)) (Eq.trans (*-assoc (- b) m⁻¹ [am]⁻¹) (Eq.trans (Eq.cong (- b *_) (*-comm m⁻¹ [am]⁻¹)) (Eq.trans (Eq.cong (- b *_) (Eq.cong (_* m⁻¹) (inv-distrib (a , λ ()) m))) (Eq.trans (Eq.cong ((- b *_)) (*-assoc a⁻¹ m⁻¹ m⁻¹)) (Eq.trans (Eq.sym (*-assoc (- b) a⁻¹ m⁻²)) auto))))))
