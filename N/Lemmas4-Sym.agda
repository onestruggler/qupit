{-# OPTIONS  --safe #-}
{-# OPTIONS  --call-by-name #-}
{-# OPTIONS --termination-depth=4 #-}
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
--open import Data.List using () hiding ([_] ; _++_ ; last ; head ; tail ; _∷ʳ_)
open import Data.Vec hiding ([_])
open import Data.Vec as V
open import Data.Fin hiding (_+_ ; _-_ ; _≤_ ; _<_)

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
open import Presentation.Tactics using ()
open import Data.Nat.Primality



module N.Lemmas4-Sym (p-2 : ℕ) (p-prime : Prime (2+ p-2))  where

private
  variable
    n : ℕ
    
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
open import N.Cosets p-2 p-prime
open import N.Symplectic p-2 p-prime
open Symplectic renaming (M to ZM)
open import N.NF1-Sym p-2 p-prime
open import N.LM-Sym p-2 p-prime

open import N.Action p-2 p-prime
open import N.Action-Lemmas p-2 p-prime
open import Algebra.Properties.Ring (+-*-ring p-2)
open import N.NF2-Sym p-2 p-prime
open LM2


open import Zp.ModularArithmetic
open import N.Lemmas-2Qupit p-2 p-prime
open import N.NF2-Sym p-2 p-prime
--open Lemmas-2Q 2

open import N.NF1 p-2 p-prime
open import N.Ex-Sym p-2 p-prime
open import N.Ex-Sym1 p-2 p-prime
open import N.Ex-Sym2 p-2 p-prime
open import N.Ex-Sym3 p-2 p-prime
open import N.Ex-Sym4 p-2 p-prime
open import N.Ex-Sym5 p-2 p-prime hiding (module L0)

open import N.Lemma-Comm-n p-2 p-prime
open import N.Completeness1-Sym p-2 p-prime renaming (module Completeness to Cp1)
open Lemmas0a
open Lemmas0a1
open Lemmas0b
open Lemmas0c
open Lemmas-Sym
open Duality

open import N.Completeness1-Sym p-2 p-prime renaming (module Completeness to CP1) using ()
open import N.Coset2-Update-Sym p-2 p-prime renaming (module Completeness to CP2) using ()


aux-comm-m-CZ↑ : let open PB ((₃₊ n) QRel,_===_) in ∀ m -> ⟦ m ⟧ₘ • CZ ↑ ≈ CZ ↑ • ⟦ m ⟧ₘ
aux-comm-m-CZ↑ {n} m = begin
  ⟦ m ⟧ₘ • CZ ↑ ≈⟨ (cleft refl) ⟩
  (S^ x • H • S^ x⁻¹ • H • S^ x • H) • CZ ↑ ≈⟨ special-assoc (□ ^ 6 • □) (□ ^ 5 • □ ^ 2) auto ⟩
  (S^ x • H • S^ x⁻¹ • H • S^ x) • H • CZ ↑ ≈⟨ (cright sym (axiom comm-H)) ⟩
  (S^ x • H • S^ x⁻¹ • H • S^ x) • CZ ↑ • H ≈⟨ special-assoc (□ ^ 5 • □ ^ 2) (□ ^ 4 • □ ^ 2 • □) auto ⟩
  (S^ x • H • S^ x⁻¹ • H) • (S^ x • CZ ↑) • H ≈⟨ (cright cleft word-comm (toℕ x) 1 (sym (axiom comm-S))) ⟩
  (S^ x • H • S^ x⁻¹ • H) • (CZ ↑ • S^ x) • H ≈⟨ special-assoc ((□ ^ 4 • □ ^ 2 • □)) (□ ^ 3 • □ ^ 2 • □ ^ 2) auto ⟩
  (S^ x • H • S^ x⁻¹) • (H • CZ ↑) • S^ x • H ≈⟨ (cright cleft sym (axiom comm-H)) ⟩
  (S^ x • H • S^ x⁻¹) • (CZ ↑ • H) • S^ x • H ≈⟨ special-assoc (□ ^ 3 • □ ^ 2 • □ ^ 2) (□ ^ 2 • □ ^ 2 • □ ^ 3) auto ⟩
  (S^ x • H) • (S^ x⁻¹ • CZ ↑) • H • S^ x • H ≈⟨ (cright cleft word-comm (toℕ x⁻¹) 1 (sym (axiom comm-S))) ⟩
  (S^ x • H) • (CZ ↑ • S^ x⁻¹) • H • S^ x • H ≈⟨ special-assoc ((□ ^ 2 • □ ^ 2 • □ ^ 3)) ((□ • □ ^ 2 • □ ^ 4)) auto ⟩
  S^ x • (H • CZ ↑) • S^ x⁻¹ • H • S^ x • H ≈⟨ (cright cleft sym (axiom comm-H)) ⟩
  S^ x • (CZ ↑ • H) • S^ x⁻¹ • H • S^ x • H ≈⟨ special-assoc ((□ • □ ^ 2 • □ ^ 4)) ((□ ^ 2 • □ ^ 5)) auto ⟩
  (S^ x • CZ ↑) • H • S^ x⁻¹ • H • S^ x • H ≈⟨ (cleft word-comm (toℕ x) 1 (sym (axiom comm-S))) ⟩
  (CZ ↑ • S^ x) • H • S^ x⁻¹ • H • S^ x • H ≈⟨ assoc ⟩
  CZ ↑ • ⟦ m ⟧ₘ ∎
  where
  x = m .proj₁
  x⁻¹ = ((m ⁻¹) .proj₁ )
  open PB ((₃₊ n) QRel,_===_)  
  open PP ((₃₊ n) QRel,_===_)
  open SR word-setoid
  open Pattern-Assoc

aux-comm-m-CZ^ : let open PB ((₃₊ n) QRel,_===_) in ∀ m k -> ⟦ m ⟧ₘ • CZ^ k ↑ ≈ CZ^ k ↑ • ⟦ m ⟧ₘ
aux-comm-m-CZ^ {n} m k = begin
  ⟦ m ⟧ₘ • CZ^ k ↑ ≈⟨ cright sym (refl' (aux-↑ CZ (toℕ k))) ⟩
  ⟦ m ⟧ₘ • CZ ↑ ^ toℕ k ≈⟨ word-comm 1 (toℕ k) (aux-comm-m-CZ↑ m) ⟩
  CZ ↑ ^ toℕ k • ⟦ m ⟧ₘ ≈⟨ cleft refl' (aux-↑ CZ (toℕ k)) ⟩
  CZ^ k ↑ • ⟦ m ⟧ₘ ∎
  where
  open PB ((₃₊ n) QRel,_===_)  
  open PP ((₃₊ n) QRel,_===_)
  open SR word-setoid

aux-comm-m-g↥↑ : let open PB ((₃₊ n) QRel,_===_) in ∀ m g -> ⟦ m ⟧ₘ • [ g ↥ ]ʷ ↑ ≈ [ g ↥ ]ʷ ↑ • ⟦ m ⟧ₘ
aux-comm-m-g↥↑ {n} m g = begin
  ⟦ m ⟧ₘ • [ g ↥ ]ʷ ↑ ≈⟨ (cleft refl) ⟩
  (S^ x • H • S^ x⁻¹ • H • S^ x • H) • [ g ↥ ]ʷ ↑ ≈⟨ special-assoc (□ ^ 6 • □) (□ ^ 5 • □ ^ 2) auto ⟩
  (S^ x • H • S^ x⁻¹ • H • S^ x) • H • [ g ↥ ]ʷ ↑ ≈⟨ (cright sym (axiom comm-H)) ⟩
  (S^ x • H • S^ x⁻¹ • H • S^ x) • [ g ↥ ]ʷ ↑ • H ≈⟨ special-assoc (□ ^ 5 • □ ^ 2) (□ ^ 4 • □ ^ 2 • □) auto ⟩
  (S^ x • H • S^ x⁻¹ • H) • (S^ x • [ g ↥ ]ʷ ↑) • H ≈⟨ (cright cleft word-comm (toℕ x) 1 (sym (axiom comm-S))) ⟩
  (S^ x • H • S^ x⁻¹ • H) • ([ g ↥ ]ʷ ↑ • S^ x) • H ≈⟨ special-assoc ((□ ^ 4 • □ ^ 2 • □)) (□ ^ 3 • □ ^ 2 • □ ^ 2) auto ⟩
  (S^ x • H • S^ x⁻¹) • (H • [ g ↥ ]ʷ ↑) • S^ x • H ≈⟨ (cright cleft sym (axiom comm-H)) ⟩
  (S^ x • H • S^ x⁻¹) • ([ g ↥ ]ʷ ↑ • H) • S^ x • H ≈⟨ special-assoc (□ ^ 3 • □ ^ 2 • □ ^ 2) (□ ^ 2 • □ ^ 2 • □ ^ 3) auto ⟩
  (S^ x • H) • (S^ x⁻¹ • [ g ↥ ]ʷ ↑) • H • S^ x • H ≈⟨ (cright cleft word-comm (toℕ x⁻¹) 1 (sym (axiom comm-S))) ⟩
  (S^ x • H) • ([ g ↥ ]ʷ ↑ • S^ x⁻¹) • H • S^ x • H ≈⟨ special-assoc ((□ ^ 2 • □ ^ 2 • □ ^ 3)) ((□ • □ ^ 2 • □ ^ 4)) auto ⟩
  S^ x • (H • [ g ↥ ]ʷ ↑) • S^ x⁻¹ • H • S^ x • H ≈⟨ (cright cleft sym (axiom comm-H)) ⟩
  S^ x • ([ g ↥ ]ʷ ↑ • H) • S^ x⁻¹ • H • S^ x • H ≈⟨ special-assoc ((□ • □ ^ 2 • □ ^ 4)) ((□ ^ 2 • □ ^ 5)) auto ⟩
  (S^ x • [ g ↥ ]ʷ ↑) • H • S^ x⁻¹ • H • S^ x • H ≈⟨ (cleft word-comm (toℕ x) 1 (sym (axiom comm-S))) ⟩
  ([ g ↥ ]ʷ ↑ • S^ x) • H • S^ x⁻¹ • H • S^ x • H ≈⟨ assoc ⟩
  [ g ↥ ]ʷ ↑ • ⟦ m ⟧ₘ ∎
  where
  x = m .proj₁
  x⁻¹ = ((m ⁻¹) .proj₁ )
  open PB ((₃₊ n) QRel,_===_)  
  open PP ((₃₊ n) QRel,_===_)
  open SR word-setoid
  open Pattern-Assoc


aux-comm-m-w↑ : let open PB ((₁₊ n) QRel,_===_) in ∀ m w -> ⟦ m ⟧ₘ • w ↑ ≈ w ↑ • ⟦ m ⟧ₘ
aux-comm-m-w↑ {₁₊ n} m [ H-gen ]ʷ = aux-comm-m-H↑ n m
aux-comm-m-w↑ {₁₊ n} m [ S-gen ]ʷ = aux-comm-m-S↑ n m
aux-comm-m-w↑ {₂₊ n} m [ CZ-gen ]ʷ = aux-comm-m-CZ↑ m
aux-comm-m-w↑ {₂₊ n} m [ x ↥ ]ʷ = aux-comm-m-g↥↑ m x
aux-comm-m-w↑ {n} m ε = PB.trans PB.right-unit (PB.sym PB.left-unit)
aux-comm-m-w↑ {n} m (w • v) = begin
  ⟦ m ⟧ₘ • w ↑ • v ↑ ≈⟨ sym assoc ⟩
  (⟦ m ⟧ₘ • w ↑) • v ↑ ≈⟨ (cleft aux-comm-m-w↑ m w) ⟩
  (w ↑ • ⟦ m ⟧ₘ) • v ↑ ≈⟨ assoc ⟩
  w ↑ • ⟦ m ⟧ₘ • v ↑ ≈⟨ (cright aux-comm-m-w↑ m v) ⟩
  w ↑ • v ↑ • ⟦ m ⟧ₘ ≈⟨ sym assoc ⟩
  (w ↑ • v ↑) • ⟦ m ⟧ₘ ∎
  where
  open PB ((₁₊ n) QRel,_===_)  
  open PP ((₁₊ n) QRel,_===_)
  open SR word-setoid


comm-abox-w↑ : let open PB ((₁₊ n) QRel,_===_) in
  ∀ a (w : Word (Gen n)) -> [ a ]ᵃ • w ↑ ≈ w ↑ • [ a ]ᵃ
comm-abox-w↑ {n} a@((₀ , ₀) , neqI) w = ⊥-elim (neqI auto)
comm-abox-w↑ {n} a@((₀ , b@(₁₊ _)) , neqI) w = begin
  ⟦ (b , λ ()) ⁻¹ , ε ⟧ₘ₊ • (w ↑) ≈⟨ (cleft right-unit) ⟩
  ⟦ (b , λ ()) ⁻¹ ⟧ₘ • (w ↑) ≈⟨ aux-comm-m-w↑ ((b , λ ()) ⁻¹) w ⟩
  w ↑ • ⟦ (b , λ ()) ⁻¹ ⟧ₘ ≈⟨ sym (cong refl right-unit) ⟩
  (w ↑) • [ (₀ , b) , neqI ]ᵃ ∎
  where
  open PB ((₁₊ n) QRel,_===_)  
  open PP ((₁₊ n) QRel,_===_)
  open SR word-setoid
comm-abox-w↑ {0} ((a@(₁₊ _) , b) , neqI) ε = PB.trans PB.right-unit (PB.sym PB.left-unit)
comm-abox-w↑ {0} d@(((₁₊ _) , b) , neqI) (w • v) = begin
  [ d ]ᵃ • w ↑ • v ↑ ≈⟨ sym assoc ⟩
  ([ d ]ᵃ • w ↑) • v ↑ ≈⟨ (cleft comm-abox-w↑ d w) ⟩
  (w ↑ • [ d ]ᵃ) • v ↑ ≈⟨ assoc ⟩
  w ↑ • [ d ]ᵃ • v ↑ ≈⟨ (cright comm-abox-w↑ d v) ⟩
  w ↑ • v ↑ • [ d ]ᵃ ≈⟨ sym assoc ⟩
  (w ↑ • v ↑) • [ d ]ᵃ ∎
  where
  open PB ((1) QRel,_===_)  
  open PP ((1) QRel,_===_)
  open SR word-setoid
comm-abox-w↑ {n@(₁₊ _)} ((a@(₁₊ _) , b) , neqI) w = begin
  ⟦ (a , λ ()) ⁻¹ , HS^ -b/a ⟧ₘ₊ • w ↑ ≈⟨ special-assoc (□ ^ 3 • □) (□ ^ 4) auto ⟩
  ⟦ (a , λ ()) ⁻¹ ⟧ₘ • H • S^ -b/a • w ↑ ≈⟨ (cright cright lemma-comm-Sᵏ-w↑ (toℕ -b/a) w) ⟩
  ⟦ (a , λ ()) ⁻¹ ⟧ₘ • H • w ↑ • S^ -b/a ≈⟨ (cright sym assoc) ⟩
  ⟦ (a , λ ()) ⁻¹ ⟧ₘ • (H • w ↑) • S^ -b/a ≈⟨ (cright cleft lemma-comm-H-w↑ w) ⟩
  ⟦ (a , λ ()) ⁻¹ ⟧ₘ • (w ↑ • H) • S^ -b/a ≈⟨ special-assoc (□ • □ ^ 2 • □) (□ ^ 2 • □ ^ 2) auto ⟩
  (⟦ (a , λ ()) ⁻¹ ⟧ₘ • w ↑) • H • S^ -b/a ≈⟨ (cleft aux-comm-m-w↑ ((a , λ ()) ⁻¹) w) ⟩
  (w ↑ • ⟦ (a , λ ()) ⁻¹ ⟧ₘ) • H • S^ -b/a ≈⟨ assoc ⟩
  w ↑ • ⟦ (a , λ ()) ⁻¹ , HS^ -b/a ⟧ₘ₊ ∎
  where
  open PB ((₁₊ n) QRel,_===_)  
  open PP ((₁₊ n) QRel,_===_)
  open SR word-setoid
  open Pattern-Assoc
  a⁻¹ = ((a , λ ()) ⁻¹) .proj₁
  -b/a = - b * a⁻¹





comm-hs-w↑ : let open PB ((₁₊ n) QRel,_===_) in
  ∀ k (w : Word (Gen n)) -> (H • S^ k) • w ↑ ≈ w ↑ • H • S^ k
comm-hs-w↑ {0} k ε = PB.trans PB.right-unit (PB.sym PB.left-unit)
comm-hs-w↑ {0} k (w • v) = begin
  (H • S^ k) • w ↑ • v ↑ ≈⟨ sym assoc ⟩
  ((H • S^ k) • w ↑) • v ↑ ≈⟨ (cleft comm-hs-w↑ k w) ⟩
  (w ↑ • (H • S^ k)) • v ↑ ≈⟨ assoc ⟩
  w ↑ • (H • S^ k) • v ↑ ≈⟨ (cright comm-hs-w↑ k v) ⟩
  w ↑ • v ↑ • (H • S^ k) ≈⟨ sym assoc ⟩
  (w ↑ • v ↑) • (H • S^ k) ∎
  where
  open PB ((1) QRel,_===_)  
  open PP ((1) QRel,_===_)
  open SR word-setoid
comm-hs-w↑ {n@(₁₊ _)} k w = begin
  (H • S^ k) • w ↑ ≈⟨ assoc ⟩
  H • S^ k • w ↑ ≈⟨ (cright lemma-comm-Sᵏ-w↑ (toℕ k) w) ⟩
  H • w ↑ • S^ k ≈⟨ ( sym assoc) ⟩
  (H • w ↑) • S^ k ≈⟨ ( cleft lemma-comm-H-w↑ w) ⟩
  (w ↑ • H) • S^ k ≈⟨ assoc ⟩
  w ↑ • H • S^ k ∎
  where
  open PB ((₁₊ n) QRel,_===_)  
  open PP ((₁₊ n) QRel,_===_)
  open SR word-setoid
  open Pattern-Assoc

comm-Ex-CZ^k-w↑↑ : let open PB ((₂₊ n) QRel,_===_) in
  ∀ k (w : Word (Gen n)) -> (Ex • CZ^ k) • w ↑ ↑ ≈ w ↑ ↑ • Ex • CZ^ k

comm-Ex-CZ^k-w↑↑ {0} l ε = PB.trans PB.right-unit (PB.sym PB.left-unit)
comm-Ex-CZ^k-w↑↑ {0} k (w • v) = begin
  (Ex • CZ^ k) • w ↑ ↑ • v ↑ ↑ ≈⟨ sym assoc ⟩
  ((Ex • CZ^ k) • w ↑ ↑) • v ↑ ↑ ≈⟨ (cleft comm-Ex-CZ^k-w↑↑ k w) ⟩
  (w ↑ ↑ • (Ex • CZ^ k)) • v ↑ ↑ ≈⟨ assoc ⟩
  w ↑ ↑ • (Ex • CZ^ k) • v ↑ ↑ ≈⟨ (cright comm-Ex-CZ^k-w↑↑ k v) ⟩
  w ↑ ↑ • v ↑ ↑ • (Ex • CZ^ k) ≈⟨ sym assoc ⟩
  (w ↑ ↑ • v ↑ ↑) • (Ex • CZ^ k) ∎
  where
  open PB ((2) QRel,_===_)  
  open PP ((2) QRel,_===_)
  open SR word-setoid


comm-Ex-CZ^k-w↑↑ {₁₊ n} k w = begin
  (Ex • CZ^ k) • w ↑ ↑ ≈⟨ assoc ⟩
  Ex • CZ^ k • w ↑ ↑ ≈⟨ cright word-comm (toℕ k) 1 (lemma-comm-CZ-w↑↑ w) ⟩
  Ex • w ↑ ↑ • CZ^ k ≈⟨ sym assoc ⟩
  (Ex • w ↑ ↑) • CZ^ k ≈⟨ cleft lemma-comm-Ex-w↑↑ w ⟩
  (w ↑ ↑ • Ex) • CZ^ k ≈⟨ assoc ⟩
  w ↑ ↑ • Ex • CZ^ k ∎
  where
  open PB ((₃₊ n) QRel,_===_)  
  open PP ((₃₊ n) QRel,_===_)
  open SR word-setoid
  open Lemmas3
  open import N.Ex-Sym3n p-2 p-prime hiding (lemma-comm-Ex-w↑↑)
  

lemma-comm-CX^k-w↑↑ : ∀ {n} k w → let open PB ((₂₊ n) QRel,_===_) in

  CX'^ k • w ↑ ↑ ≈ w ↑ ↑ • CX'^ k

lemma-comm-CX^k-w↑↑ {n} k w = begin
  CX'^ k • w ↑ ↑ ≈⟨ special-assoc (□ ^ 3 • □) (□ ^ 4) auto ⟩
  H ^ 3 • CZ^ k • H • w ↑ ↑ ≈⟨ (cright cright lemma-comm-H-w↑ (w ↑)) ⟩
  H ^ 3 • CZ^ k • w ↑ ↑ • H ≈⟨ cright sym assoc ⟩
  H ^ 3 • (CZ^ k • w ↑ ↑) • H ≈⟨ (cright cleft word-comm (toℕ k) 1 (lemma-comm-CZ-w↑↑ w)) ⟩
  H ^ 3 • (w ↑ ↑ • CZ^ k) • H ≈⟨ trans (by-assoc auto) assoc ⟩
  (H ^ 3 • w ↑ ↑) • CZ^ k • H ≈⟨ (cleft lemma-comm-Hᵏ-w↑ 3 (w ↑)) ⟩
  (w ↑ ↑ • H ^ 3) • CZ^ k • H ≈⟨ assoc ⟩
  w ↑ ↑ • CX'^ k ∎
  where
  open PB ((₂₊ n) QRel,_===_)
  open PP ((₂₊ n) QRel,_===_)
  open SR word-setoid
  open Pattern-Assoc
  open Lemmas3
  open import N.Ex-Sym3n p-2 p-prime hiding (lemma-comm-Ex-w↑↑)




comm-dbox-w↑↑' : let open PB ((₂₊ n) QRel,_===_) in
  ∀ a b (w : Word (Gen n)) -> [ a , b ]ᵈ • w ↑ ↑ ≈ w ↑ ↑ • [ a , b ]ᵈ
comm-dbox-w↑↑' {0} a b ε = PB.trans PB.right-unit (PB.sym PB.left-unit)
comm-dbox-w↑↑' {0} a b' (w • v) = let b = (a , b') in begin
  [ b ]ᵈ • w ↑ ↑ • v ↑ ↑ ≈⟨ sym assoc ⟩
  ([ b ]ᵈ • w ↑ ↑) • v ↑ ↑ ≈⟨ (cleft comm-dbox-w↑↑' a b' w) ⟩
  (w ↑ ↑ • [ b ]ᵈ) • v ↑ ↑ ≈⟨ assoc ⟩
  w ↑ ↑ • [ b ]ᵈ • v ↑ ↑ ≈⟨ (cright comm-dbox-w↑↑' a b' v) ⟩
  w ↑ ↑ • v ↑ ↑ • [ b ]ᵈ ≈⟨ sym assoc ⟩
  (w ↑ ↑ • v ↑ ↑) • [ b ]ᵈ ∎
  where
  open PB ((2) QRel,_===_)  
  open PP ((2) QRel,_===_)
  open SR word-setoid
comm-dbox-w↑↑' {₁₊ n} a@₀ b' w = let b = (₀ , b') in  begin
  [ ₀ , b' ]ᵈ • w ↑ ↑ ≈⟨ assoc ⟩
  Ex • CZ^ (- b') • w ↑ ↑ ≈⟨ cright word-comm (toℕ (- b')) 1 (lemma-comm-CZ-w↑↑ w) ⟩
  Ex • w ↑ ↑ • CZ^ (- b') ≈⟨ sym assoc ⟩
  (Ex • w ↑ ↑) • CZ^ (- b') ≈⟨ cleft lemma-comm-Ex-w↑↑ w ⟩
  (w ↑ ↑ • Ex) • CZ^ (- b') ≈⟨ assoc ⟩
  w ↑ ↑ • [ b ]ᵈ ∎
  where
  open PB ((₃₊ n) QRel,_===_)  
  open PP ((₃₊ n) QRel,_===_)
  open SR word-setoid
  open Lemmas3
  open import N.Ex-Sym3n p-2 p-prime hiding (lemma-comm-Ex-w↑↑)
  
comm-dbox-w↑↑' {₁₊ n} a@(₁₊ _) b w = let d = (a , b) in  begin
  [ a , b ]ᵈ • w ↑ ↑ ≈⟨ refl ⟩
  (Ex • CZ^ (- a) • H • S^ -b/a) • w ↑ ↑ ≈⟨ special-assoc (□ ^ 3 • □) (□ ^ 2 • □ ^ 2) auto ⟩
  (Ex • CZ^ (- a)) • (H • S^ -b/a) • w ↑ ↑ ≈⟨ (cright (comm-hs-w↑ -b/a (w ↑))) ⟩
  (Ex • CZ^ (- a)) • w ↑ ↑ • (H • S^ -b/a) ≈⟨ sym assoc ⟩
  ((Ex • CZ^ (- a)) • w ↑ ↑) • (H • S^ -b/a) ≈⟨ (cleft comm-Ex-CZ^k-w↑↑ (- a) w) ⟩
  (w ↑ ↑ • (Ex • CZ^ (- a))) • (H • S^ -b/a) ≈⟨ special-assoc (□ ^ 3 • □ ^ 2 ) (□ • □ ^ 4) auto ⟩
  w ↑ ↑ • [ d ]ᵈ ∎
  where
  open PB ((₃₊ n) QRel,_===_)  
  open PP ((₃₊ n) QRel,_===_)
  open SR word-setoid
  open Lemmas3
  open Pattern-Assoc
  m1 : ℤ ₚ
  m1 = - ₁
  a⁻¹ = ((a , λ ()) ⁻¹) .proj₁
  -b/a = - b * a⁻¹


comm-dbox-w↑↑ : let open PB ((₂₊ n) QRel,_===_) in
  ∀ b (w : Word (Gen n)) -> [ b ]ᵈ • w ↑ ↑ ≈ w ↑ ↑ • [ b ]ᵈ
comm-dbox-w↑↑ {n} d@(a , b) w = comm-dbox-w↑↑' a b w



comm-bbox-w↑↑' : let open PB ((₂₊ n) QRel,_===_) in
  ∀ a b (w : Word (Gen n)) -> [ a , b ]ᵇ • w ↑ ↑ ≈ w ↑ ↑ • [ a , b ]ᵇ
comm-bbox-w↑↑' {0} a b ε = PB.trans PB.right-unit (PB.sym PB.left-unit)
comm-bbox-w↑↑' {0} a b' (w • v) = let b = (a , b') in begin
  [ b ]ᵇ • w ↑ ↑ • v ↑ ↑ ≈⟨ sym assoc ⟩
  ([ b ]ᵇ • w ↑ ↑) • v ↑ ↑ ≈⟨ (cleft comm-bbox-w↑↑' a b' w) ⟩
  (w ↑ ↑ • [ b ]ᵇ) • v ↑ ↑ ≈⟨ assoc ⟩
  w ↑ ↑ • [ b ]ᵇ • v ↑ ↑ ≈⟨ (cright comm-bbox-w↑↑' a b' v) ⟩
  w ↑ ↑ • v ↑ ↑ • [ b ]ᵇ ≈⟨ sym assoc ⟩
  (w ↑ ↑ • v ↑ ↑) • [ b ]ᵇ ∎
  where
  open PB ((2) QRel,_===_)  
  open PP ((2) QRel,_===_)
  open SR word-setoid
comm-bbox-w↑↑' {₁₊ n} a@₀ b' w = let b = (₀ , b') in  begin
  [ ₀ , b' ]ᵇ • w ↑ ↑ ≈⟨ assoc ⟩
  Ex • CX'^ (b') • w ↑ ↑ ≈⟨ cright lemma-comm-CX^k-w↑↑ b' w ⟩
  Ex • w ↑ ↑ • CX'^ (b') ≈⟨ sym assoc ⟩
  (Ex • w ↑ ↑) • CX'^ (b') ≈⟨ cleft lemma-comm-Ex-w↑↑ w ⟩
  (w ↑ ↑ • Ex) • CX'^ (b') ≈⟨ assoc ⟩
  w ↑ ↑ • [ b ]ᵇ ∎
  where
  open PB ((₃₊ n) QRel,_===_)  
  open PP ((₃₊ n) QRel,_===_)
  open SR word-setoid
  open Lemmas3
  open import N.Ex-Sym3n p-2 p-prime hiding (lemma-comm-Ex-w↑↑)


comm-bbox-w↑↑' {₁₊ n} a@(₁₊ _) b w = let d = (a , b) in  begin
  [ a , b ]ᵇ • w ↑ ↑ ≈⟨ refl ⟩
  (Ex • CX'^ (a) • (H • S^ -b/a) ↑) • w ↑ ↑ ≈⟨ special-assoc (□ ^ 3 • □) (□ ^ 2 • □ ^ 2) auto ⟩
  (Ex • CX'^ (a)) • (H • S^ -b/a) ↑ • w ↑ ↑ ≈⟨ (cright (lemma-cong↑ _ _ (comm-hs-w↑ -b/a (w )))) ⟩
  (Ex • CX'^ (a)) • w ↑ ↑ • (H • S^ -b/a) ↑ ≈⟨ sym assoc ⟩
  ((Ex • CX'^ (a)) • w ↑ ↑) • (H • S^ -b/a) ↑ ≈⟨ (cleft assoc) ⟩
  (Ex • CX'^ (a) • w ↑ ↑) • (H • S^ -b/a) ↑ ≈⟨ (cleft (cright lemma-comm-CX^k-w↑↑ a w)) ⟩
  (Ex • w ↑ ↑ • CX'^ (a)) • (H • S^ -b/a) ↑ ≈⟨ ( special-assoc (□ ^ 3 • □) (□ ^ 2 • □ ^ 2) auto) ⟩
  (Ex • w ↑ ↑) • CX'^ a • (H • S^ -b/a) ↑ ≈⟨ (cleft lemma-comm-Ex-w↑↑ w) ⟩
  (w ↑ ↑ • Ex) • CX'^ a • (H • S^ -b/a) ↑ ≈⟨ ( special-assoc (□ ^ 2 • □ ^ 2) (□ ^ 4) auto) ⟩ 
  w ↑ ↑ • Ex • CX'^ a • (H • S^ -b/a) ↑ ≈⟨ refl ⟩
  w ↑ ↑ • [ d ]ᵇ ∎
  where
  open PB ((₃₊ n) QRel,_===_)  
  open PP ((₃₊ n) QRel,_===_)
  open SR word-setoid
  open Lemmas3
  open Pattern-Assoc
  m1 : ℤ ₚ
  m1 = - ₁
  a⁻¹ = ((a , λ ()) ⁻¹) .proj₁
  -b/a = - b * a⁻¹


comm-bbox-w↑↑ : let open PB ((₂₊ n) QRel,_===_) in
  ∀ b (w : Word (Gen n)) -> [ b ]ᵇ • w ↑ ↑ ≈ w ↑ ↑ • [ b ]ᵇ
comm-bbox-w↑↑ {n} d@(a , b) w = comm-bbox-w↑↑' a b w


{-

comm-dbox-w↑↑' : let open PB ((₂₊ n) QRel,_===_) in
  ∀ a d (w : Word (Gen n)) -> [ a , d ]ᵈ • w ↑ ↑ ≈ w ↑ ↑ • [ a , d ]ᵈ
comm-dbox-w↑↑' {0} a d ε = PB.trans PB.right-unit (PB.sym PB.left-unit)
comm-dbox-w↑↑' {0} a d' (w • v) = let d = (a , d') in begin
  [ d ]ᵈ • w ↑ ↑ • v ↑ ↑ ≈⟨ sym assoc ⟩
  ([ d ]ᵈ • w ↑ ↑) • v ↑ ↑ ≈⟨ (cleft comm-dbox-w↑↑' a d' w) ⟩
  (w ↑ ↑ • [ d ]ᵈ) • v ↑ ↑ ≈⟨ assoc ⟩
  w ↑ ↑ • [ d ]ᵈ • v ↑ ↑ ≈⟨ (cright comm-dbox-w↑↑' a d' v) ⟩
  w ↑ ↑ • v ↑ ↑ • [ d ]ᵈ ≈⟨ sym assoc ⟩
  (w ↑ ↑ • v ↑ ↑) • [ d ]ᵈ ∎
  where
  open PB ((2) QRel,_===_)  
  open PP ((2) QRel,_===_)
  open SR word-setoid
comm-dbox-w↑↑' {₁₊ n} a@₀ d'@₀ w = let d = (₀ , d') in  begin
  [ ₀ , d' ]ᵈ • w ↑ ↑ ≈⟨ refl ⟩
  (Ex ) • w ↑ ↑ ≈⟨  lemma-comm-Ex-w↑↑ w ⟩
  w ↑ ↑ • [ d ]ᵈ ∎
  where
  open PB ((₃₊ n) QRel,_===_)  
  open PP ((₃₊ n) QRel,_===_)
  open SR word-setoid
  open Lemmas3
comm-dbox-w↑↑' {₁₊ n} a@₀ d'@(₁₊ _) w = let d = (₀ , d') in  begin
  [ ₀ , d' ]ᵈ • w ↑ ↑ ≈⟨ refl ⟩
  (Ex • CZ^ (- ₁) • [ (₀ , d') , (λ ()) ]ᵃ) • w ↑ ↑ ≈⟨ special-assoc (□ ^ 3 • □) (□ ^ 4) auto ⟩
  Ex • CZ^ (- ₁) • [ (₀ , d') , (λ ()) ]ᵃ • w ↑ ↑ ≈⟨ (cright cright comm-abox-w↑ ((₀ , d') , (λ ())) (w ↑)) ⟩
  Ex • CZ^ (- ₁) • w ↑ ↑ • [ (₀ , d') , (λ ()) ]ᵃ ≈⟨ (cright sym assoc) ⟩
  Ex • (CZ^ (- ₁) • w ↑ ↑) • [ (₀ , d') , (λ ()) ]ᵃ ≈⟨ (((cright cleft  word-comm (toℕ m1) 1 ( lemma-comm-CZ-w↑ w)))) ⟩
  Ex • (w ↑ ↑ • CZ^ (- ₁)) • [ (₀ , d') , (λ ()) ]ᵃ ≈⟨ special-assoc (□ • □ ^ 2 • □) (□ ^ 2 • □ ^ 2) auto ⟩
  (Ex • w ↑ ↑) • CZ^ (- ₁) • [ (₀ , d') , (λ ()) ]ᵃ ≈⟨ ( cleft lemma-comm-Ex-w↑↑ w) ⟩
  (w ↑ ↑ • Ex) • CZ^ (- ₁) • [ (₀ , d') , (λ ()) ]ᵃ ≈⟨  assoc ⟩
  w ↑ ↑ • [ d ]ᵈ ∎
  where
  open PB ((₃₊ n) QRel,_===_)  
  open PP ((₃₊ n) QRel,_===_)
  open SR word-setoid
  open Lemmas3
  open Pattern-Assoc
  m1 : ℤ ₚ
  m1 = - ₁

comm-dbox-w↑↑' {₁₊ n} a@(₁₊ _) d' w = let d = (a , d') in  begin
  [ a , d' ]ᵈ • w ↑ ↑ ≈⟨ refl ⟩
  (Ex • CZ^ (- ₁) • [ (a , d') , (λ ()) ]ᵃ) • w ↑ ↑ ≈⟨ special-assoc (□ ^ 3 • □) (□ ^ 4) auto ⟩
  Ex • CZ^ (- ₁) • [ (a , d') , (λ ()) ]ᵃ • w ↑ ↑ ≈⟨ (cright cright comm-abox-w↑ ((a , d') , (λ ())) (w ↑)) ⟩
  Ex • CZ^ (- ₁) • w ↑ ↑ • [ (a , d') , (λ ()) ]ᵃ ≈⟨ (cright sym assoc) ⟩
  Ex • (CZ^ (- ₁) • w ↑ ↑) • [ (a , d') , (λ ()) ]ᵃ ≈⟨ (((cright cleft  word-comm (toℕ m1) 1 ( lemma-comm-CZ-w↑ w)))) ⟩
  Ex • (w ↑ ↑ • CZ^ (- ₁)) • [ (a , d') , (λ ()) ]ᵃ ≈⟨ special-assoc (□ • □ ^ 2 • □) (□ ^ 2 • □ ^ 2) auto ⟩
  (Ex • w ↑ ↑) • CZ^ (- ₁) • [ (a , d') , (λ ()) ]ᵃ ≈⟨ ( cleft lemma-comm-Ex-w↑↑ w) ⟩
  (w ↑ ↑ • Ex) • CZ^ (- ₁) • [ (a , d') , (λ ()) ]ᵃ ≈⟨  assoc ⟩
  w ↑ ↑ • [ d ]ᵈ ∎
  where
  open PB ((₃₊ n) QRel,_===_)  
  open PP ((₃₊ n) QRel,_===_)
  open SR word-setoid
  open Lemmas3
  open Pattern-Assoc
  m1 : ℤ ₚ
  m1 = - ₁


comm-dbox-w↑↑ : let open PB ((₂₊ n) QRel,_===_) in
  ∀ d (w : Word (Gen n)) -> [ d ]ᵈ • w ↑ ↑ ≈ w ↑ ↑ • [ d ]ᵈ
comm-dbox-w↑↑ {n} d@(a , b) w = comm-dbox-w↑↑' a b w

-}

lemma-A10 : let open PB ((₁₊ n) QRel,_===_) in
  [ (₁ , ₀) , (λ ()) ]ᵃ ≈ H
lemma-A10 {n} = begin
  [ (₁ , ₀) , (λ ()) ]ᵃ ≈⟨ refl ⟩
  ⟦ (a , λ ()) ⁻¹ , HS^ -b/a ⟧ₘ₊ ≡⟨ Eq.cong (\ xx -> ⟦ (a , λ ()) ⁻¹ , HS^ xx ⟧ₘ₊) aux ⟩
  ⟦ (a , λ ()) ⁻¹ , HS^ ₀ ⟧ₘ₊ ≈⟨ cong refl right-unit ⟩
  ⟦ (a , λ ()) ⁻¹ ⟧ₘ • H ≈⟨ (cleft aux-MM (((a , λ ()) ⁻¹) .proj₂) (λ ()) inv-₁) ⟩
  ⟦ (₁ , λ ()) ⟧ₘ • H ≈⟨ (cleft sym lemma-M1) ⟩
  ε • H ≈⟨ left-unit ⟩
  H ∎
  where
  open Lemmas0 n
  a = ₁
  b = ₀
  a⁻¹ = ((a , λ ()) ⁻¹) .proj₁
  -b/a = - b * a⁻¹
  aux : -b/a ≡ ₀
  aux = Eq.trans (Eq.cong₂ _*_ (-0#≈0#) inv-₁) auto
  open PB ((₁₊ n) QRel,_===_)  
  open PP ((₁₊ n) QRel,_===_)
  open SR word-setoid

aux-a≠0⇒ab≠0 : ∀ (a b : ℤ ₚ) (nz : a ≢ ₀) -> _≢_ {A = ℤ ₚ × ℤ ₚ} (a , b) (₀ , ₀)
aux-a≠0⇒ab≠0 a b nz eq0 = ⊥-elim (nz (Eq.cong proj₁ eq0))


lemma-Aa0 : let open PB ((₁₊ n) QRel,_===_) in
  ∀ (a*@(a , nz) : ℤ* ₚ) -> [ (a , ₀) , aux-a≠0⇒ab≠0 a ₀ nz ]ᵃ ≈ ZM (a* ⁻¹) • H
lemma-Aa0 {n} a*@(₀ , nz) = ⊥-elim (nz auto)
lemma-Aa0 {n} a*@(a@(₁₊ _) , nz) = begin
  [ (a , ₀) , aux-a≠0⇒ab≠0 a ₀ nz ]ᵃ ≈⟨ refl ⟩
  ⟦ a* ⁻¹ , HS^ -b/a ⟧ₘ₊ ≡⟨ Eq.cong (\ xx -> ⟦ a* ⁻¹ , HS^ xx ⟧ₘ₊) aux ⟩
  ⟦ a* ⁻¹ , HS^ ₀ ⟧ₘ₊ ≈⟨ cong refl right-unit ⟩
  ⟦ a* ⁻¹ ⟧ₘ • H ∎
  where
  open Lemmas0 n
  b = ₀
  a⁻¹ = ((a , nz) ⁻¹) .proj₁
  -b/a = - b * a⁻¹
  aux : -b/a ≡ ₀
  aux = Eq.trans (Eq.cong₂ _*_ (-0#≈0#) auto) auto
  open PB ((₁₊ n) QRel,_===_)  
  open PP ((₁₊ n) QRel,_===_)
  open SR word-setoid


lemma-Ex-M-n : let open PB ((₂₊ n) QRel,_===_) in
  ∀ m -> Ex • ZM m ≈ ZM m ↑ • Ex
lemma-Ex-M-n {n} m@x' = by-emb' (lemma-Ex-M m) aux aux2
  where
  x = x' .proj₁
  x⁻¹ = ((x' ⁻¹) .proj₁ )
  open PB ((₂₊ n) QRel,_===_)  
  open PP ((₂₊ n) QRel,_===_)
  open SR word-setoid
  open Pattern-Assoc
  open import N.Embeding-2n p-2 p-prime n

  aux : f* (Ex • ZM m) ≈ Ex • ZM m
  aux = cong refl (lemma-f*-M m)
  aux2 : f* (ZM m ↑ • Ex) ≈ ZM m ↑ • Ex
  aux2 = cong (lemma-f*-M↑ m) refl

