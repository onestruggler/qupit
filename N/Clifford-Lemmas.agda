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

module N.Clifford-Lemmas
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

module Symplectic-Simplified where

open import N.Symplectic p-2 p-prime as NSym
open import N.Clifford-Mod-Scalar p-2 p-prime g* g-gen
open Symplectic hiding (_QRel,_===_)

open Clifford-Relations

open Lemmas-Clifford
open Clifford-GroupLike
module CLemmas1 (n : ℕ) where
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

{-

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
  f-well-defined {₁₊ n} (semi-MS x) = lemma-semi-MS x
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

    
  g-well-defined {₁₊ n} Sim.semi-MS = PB.axiom (_QRel,_===₁_.semi-MS ((g , g≠0)))
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
