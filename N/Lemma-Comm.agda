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
open import Presentation.Tactics hiding ([_] ; inspect)
open import Data.Nat.Primality



module N.Lemma-Comm (p-2 : ℕ) (p-prime : Prime (2+ p-2)) (n : ℕ)  where

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
open import N.Lemmas-2Qupit p-2 p-prime
open import N.NF2-Sym p-2 p-prime
open Lemmas-2Q 2
open Symplectic
open Lemmas-Sym

open import N.NF1-Sym p-2 p-prime
open import N.Ex-Sym p-2 p-prime
open Lemmas0a
open import N.Cosets p-2 p-prime

open LM2
open import N.Completeness1-Sym p-2 p-prime renaming (module Completeness to CP1) using ()

open PB ((₂₊ n) QRel,_===_)
open PP ((₂₊ n) QRel,_===_)
open SR word-setoid
open Pattern-Assoc


aux-comm-S^k-H↑ : ∀ k -> S^ k • H ↑ ≈ H ↑ • S^ k
aux-comm-S^k-H↑ k = begin
  S^ k • H ↑ ≈⟨ (cleft refl) ⟩
  S ^ toℕ k • H ↑ ≈⟨ lemma-comm-Sᵏ-w↑ (toℕ k) [ H-gen ]ʷ ⟩
  H ↑ • S ^ toℕ k ≈⟨ (cright sym refl) ⟩
  H ↑ • S^ k ∎

aux-comm-c-H↑ : ∀ c -> ⟦ c ⟧ₕₛ • H ↑ ≈ H ↑ • ⟦ c ⟧ₕₛ
aux-comm-c-H↑ c@ε = begin
  ⟦ c ⟧ₕₛ • H ↑ ≈⟨ trans left-unit (sym right-unit) ⟩
  H ↑ • ⟦ c ⟧ₕₛ ∎
aux-comm-c-H↑ c@(HS^ k) = begin
  ⟦ c ⟧ₕₛ • H ↑ ≈⟨ assoc ⟩
  H • S^ k • H ↑ ≈⟨ (cright aux-comm-S^k-H↑ k) ⟩
  H • H ↑ • S^ k ≈⟨ sym assoc ⟩
  (H • H ↑) • S^ k ≈⟨ (cleft sym (axiom comm-H)) ⟩
  (H ↑ • H) • S^ k ≈⟨ assoc ⟩
  H ↑ • ⟦ c ⟧ₕₛ ∎

aux-comm-m-H↑ : ∀ m -> ⟦ m ⟧ₘ • H ↑ ≈ H ↑ • ⟦ m ⟧ₘ
aux-comm-m-H↑ m = begin
  ⟦ m ⟧ₘ • H ↑ ≈⟨ refl ⟩
  (S^ x • H • S^ x⁻¹ • H • S^ x • H) • H ↑ ≈⟨ special-assoc (□ ^ 6 • □) (□ ^ 5 • □ ^ 2) auto ⟩
  (S^ x • H • S^ x⁻¹ • H • S^ x) • H • H ↑ ≈⟨ (cright sym (axiom comm-H)) ⟩
  (S^ x • H • S^ x⁻¹ • H • S^ x) • H ↑ • H ≈⟨ special-assoc (□ ^ 5 • □ ^ 2) (□ ^ 4 • □ ^ 2 • □) auto ⟩
  (S^ x • H • S^ x⁻¹ • H) • (S^ x • H ↑) • H ≈⟨ (cright cleft aux-comm-S^k-H↑ x) ⟩
  (S^ x • H • S^ x⁻¹ • H) • (H ↑ • S^ x) • H ≈⟨ special-assoc ((□ ^ 4 • □ ^ 2 • □)) (□ ^ 3 • □ ^ 2 • □ ^ 2) auto ⟩
  (S^ x • H • S^ x⁻¹) • (H • H ↑) • S^ x • H ≈⟨ (cright cleft sym (axiom comm-H)) ⟩
  (S^ x • H • S^ x⁻¹) • (H ↑ • H) • S^ x • H ≈⟨ special-assoc (□ ^ 3 • □ ^ 2 • □ ^ 2) (□ ^ 2 • □ ^ 2 • □ ^ 3) auto ⟩
  (S^ x • H) • (S^ x⁻¹ • H ↑) • H • S^ x • H ≈⟨ (cright cleft aux-comm-S^k-H↑ x⁻¹) ⟩
  (S^ x • H) • (H ↑ • S^ x⁻¹) • H • S^ x • H ≈⟨ special-assoc ((□ ^ 2 • □ ^ 2 • □ ^ 3)) ((□ • □ ^ 2 • □ ^ 4)) auto ⟩
  S^ x • (H • H ↑) • S^ x⁻¹ • H • S^ x • H ≈⟨ (cright cleft sym (axiom comm-H)) ⟩
  S^ x • (H ↑ • H) • S^ x⁻¹ • H • S^ x • H ≈⟨ special-assoc ((□ • □ ^ 2 • □ ^ 4)) ((□ ^ 2 • □ ^ 5)) auto ⟩
  (S^ x • H ↑) • H • S^ x⁻¹ • H • S^ x • H ≈⟨ (cleft aux-comm-S^k-H↑ x) ⟩
  (H ↑ • S^ x) • H • S^ x⁻¹ • H • S^ x • H ≈⟨ assoc ⟩
  H ↑ • ⟦ m ⟧ₘ ∎
  where
  x = m .proj₁
  x⁻¹ = ((m ⁻¹) .proj₁ )


aux-comm-mc-H↑ : ∀ mc -> ⟦ mc ⟧ₘ₊ • H ↑ ≈ H ↑ • ⟦ mc ⟧ₘ₊
aux-comm-mc-H↑ mc@(m , c) = begin
  ⟦ mc ⟧ₘ₊ • H ↑ ≈⟨ assoc ⟩
  ⟦ m ⟧ₘ • ⟦ c ⟧ₕₛ • H ↑ ≈⟨ (cright aux-comm-c-H↑ c) ⟩
  ⟦ m ⟧ₘ • H ↑ • ⟦ c ⟧ₕₛ ≈⟨ sym assoc ⟩
  (⟦ m ⟧ₘ • H ↑) • ⟦ c ⟧ₕₛ ≈⟨ cong (aux-comm-m-H↑ m) refl ⟩
  (H ↑ • ⟦ m ⟧ₘ) • ⟦ c ⟧ₕₛ ≈⟨ assoc ⟩
  H ↑ • ⟦ mc ⟧ₘ₊ ∎


aux-comm-S^k-S↑ : ∀ k -> S^ k • S ↑ ≈ S ↑ • S^ k
aux-comm-S^k-S↑ k = begin
  S^ k • S ↑ ≈⟨ (cleft refl) ⟩
  S ^ toℕ k • S ↑ ≈⟨ lemma-comm-Sᵏ-w↑ (toℕ k) S ⟩
  S ↑ • S ^ toℕ k ≈⟨ (cright sym refl) ⟩
  S ↑ • S^ k ∎

aux-comm-c-S↑ : ∀ c -> ⟦ c ⟧ₕₛ • S ↑ ≈ S ↑ • ⟦ c ⟧ₕₛ
aux-comm-c-S↑ c@ε = begin
  ⟦ c ⟧ₕₛ • S ↑ ≈⟨ trans left-unit (sym right-unit) ⟩
  S ↑ • ⟦ c ⟧ₕₛ ∎
aux-comm-c-S↑ c@(HS^ k) = begin
  ⟦ c ⟧ₕₛ • S ↑ ≈⟨ assoc ⟩
  H • S^ k • S ↑ ≈⟨ (cright aux-comm-S^k-S↑ k) ⟩
  H • S ↑ • S^ k ≈⟨ sym assoc ⟩
  (H • S ↑) • S^ k ≈⟨ (cleft sym (axiom comm-H)) ⟩
  (S ↑ • H) • S^ k ≈⟨ assoc ⟩
  S ↑ • ⟦ c ⟧ₕₛ ∎

open Duality

aux-comm-c-S^k↑ : ∀ c k -> ⟦ c ⟧ₕₛ • S^ k ↑ ≈ S^ k ↑ • ⟦ c ⟧ₕₛ
aux-comm-c-S^k↑ c k = begin
  ⟦ c ⟧ₕₛ • S^ k ↑ ≈⟨ cright sym (refl' (aux-↑ S (toℕ k))) ⟩
  ⟦ c ⟧ₕₛ • S ↑ ^ toℕ k ≈⟨ word-comm 1 (toℕ k) (aux-comm-c-S↑ c) ⟩
  S ↑ ^ toℕ k • ⟦ c ⟧ₕₛ ≈⟨ cleft refl' (aux-↑ S (toℕ k)) ⟩
  S^ k ↑ • ⟦ c ⟧ₕₛ ∎



aux-comm-c-H^k↑ : ∀ c k -> ⟦ c ⟧ₕₛ • H^ k ↑ ≈ H^ k ↑ • ⟦ c ⟧ₕₛ
aux-comm-c-H^k↑ c k = begin
  ⟦ c ⟧ₕₛ • H^ k ↑ ≈⟨ cright sym (refl' (aux-↑ H (toℕ k))) ⟩
  ⟦ c ⟧ₕₛ • H ↑ ^ toℕ k ≈⟨ word-comm 1 (toℕ k) (aux-comm-c-H↑ c) ⟩
  H ↑ ^ toℕ k • ⟦ c ⟧ₕₛ ≈⟨ cleft refl' (aux-↑ H (toℕ k)) ⟩
  H^ k ↑ • ⟦ c ⟧ₕₛ ∎


aux-comm-m-S↑ : ∀ m -> ⟦ m ⟧ₘ • S ↑ ≈ S ↑ • ⟦ m ⟧ₘ
aux-comm-m-S↑ m = begin
  ⟦ m ⟧ₘ • S ↑ ≈⟨ (cleft refl) ⟩
  (S^ x • H • S^ x⁻¹ • H • S^ x • H) • S ↑ ≈⟨ special-assoc (□ ^ 6 • □) (□ ^ 5 • □ ^ 2) auto ⟩
  (S^ x • H • S^ x⁻¹ • H • S^ x) • H • S ↑ ≈⟨ (cright sym (axiom comm-H)) ⟩
  (S^ x • H • S^ x⁻¹ • H • S^ x) • S ↑ • H ≈⟨ special-assoc (□ ^ 5 • □ ^ 2) (□ ^ 4 • □ ^ 2 • □) auto ⟩
  (S^ x • H • S^ x⁻¹ • H) • (S^ x • S ↑) • H ≈⟨ (cright cleft aux-comm-S^k-S↑ x) ⟩
  (S^ x • H • S^ x⁻¹ • H) • (S ↑ • S^ x) • H ≈⟨ special-assoc ((□ ^ 4 • □ ^ 2 • □)) (□ ^ 3 • □ ^ 2 • □ ^ 2) auto ⟩
  (S^ x • H • S^ x⁻¹) • (H • S ↑) • S^ x • H ≈⟨ (cright cleft sym (axiom comm-H)) ⟩
  (S^ x • H • S^ x⁻¹) • (S ↑ • H) • S^ x • H ≈⟨ special-assoc (□ ^ 3 • □ ^ 2 • □ ^ 2) (□ ^ 2 • □ ^ 2 • □ ^ 3) auto ⟩
  (S^ x • H) • (S^ x⁻¹ • S ↑) • H • S^ x • H ≈⟨ (cright cleft aux-comm-S^k-S↑ x⁻¹) ⟩
  (S^ x • H) • (S ↑ • S^ x⁻¹) • H • S^ x • H ≈⟨ special-assoc ((□ ^ 2 • □ ^ 2 • □ ^ 3)) ((□ • □ ^ 2 • □ ^ 4)) auto ⟩
  S^ x • (H • S ↑) • S^ x⁻¹ • H • S^ x • H ≈⟨ (cright cleft sym (axiom comm-H)) ⟩
  S^ x • (S ↑ • H) • S^ x⁻¹ • H • S^ x • H ≈⟨ special-assoc ((□ • □ ^ 2 • □ ^ 4)) ((□ ^ 2 • □ ^ 5)) auto ⟩
  (S^ x • S ↑) • H • S^ x⁻¹ • H • S^ x • H ≈⟨ (cleft aux-comm-S^k-S↑ x) ⟩
  (S ↑ • S^ x) • H • S^ x⁻¹ • H • S^ x • H ≈⟨ assoc ⟩
  S ↑ • ⟦ m ⟧ₘ ∎
  where
  x = m .proj₁
  x⁻¹ = ((m ⁻¹) .proj₁ )

aux-comm-m-S^k↑ : ∀ m k -> ⟦ m ⟧ₘ • S^ k ↑ ≈ S^ k ↑ • ⟦ m ⟧ₘ
aux-comm-m-S^k↑ m k = begin
  ⟦ m ⟧ₘ • S^ k ↑ ≈⟨ cright sym (refl' (aux-↑ S (toℕ k))) ⟩
  ⟦ m ⟧ₘ • S ↑ ^ toℕ k ≈⟨ word-comm 1 (toℕ k) (aux-comm-m-S↑ m) ⟩
  S ↑ ^ toℕ k • ⟦ m ⟧ₘ ≈⟨ cleft refl' (aux-↑ S (toℕ k)) ⟩
  S^ k ↑ • ⟦ m ⟧ₘ ∎



aux-comm-mc-S↑ : ∀ mc -> ⟦ mc ⟧ₘ₊ • S ↑ ≈ S ↑ • ⟦ mc ⟧ₘ₊
aux-comm-mc-S↑ mc@(m , c) = begin
  ⟦ mc ⟧ₘ₊ • S ↑ ≈⟨ assoc ⟩
  ⟦ m ⟧ₘ • ⟦ c ⟧ₕₛ • S ↑ ≈⟨ (cright aux-comm-c-S↑ c) ⟩
  ⟦ m ⟧ₘ • S ↑ • ⟦ c ⟧ₕₛ ≈⟨ sym assoc ⟩
  (⟦ m ⟧ₘ • S ↑) • ⟦ c ⟧ₕₛ ≈⟨ cong (aux-comm-m-S↑ m) refl ⟩
  (S ↑ • ⟦ m ⟧ₘ) • ⟦ c ⟧ₕₛ ≈⟨ assoc ⟩
  S ↑ • ⟦ mc ⟧ₘ₊ ∎

aux-comm-nf1-S↑ : ∀ nf1 -> ⟦ nf1 ⟧₁ • S ↑ ≈ S ↑ • ⟦ nf1 ⟧₁
aux-comm-nf1-S↑ nf1@(s , mc) = begin
  ⟦ nf1 ⟧₁ • S ↑ ≈⟨ assoc ⟩
  S^ s • ⟦ mc ⟧ₘ₊ • S ↑ ≈⟨ (cright aux-comm-mc-S↑ mc) ⟩
  S^ s • S ↑ • ⟦ mc ⟧ₘ₊ ≈⟨ sym assoc ⟩
  (S^ s • S ↑) • ⟦ mc ⟧ₘ₊ ≈⟨ (cleft aux-comm-S^k-S↑ s) ⟩
  (S ↑ • S^ s) • ⟦ mc ⟧ₘ₊ ≈⟨ assoc ⟩
  S ↑ • ⟦ nf1 ⟧₁ ∎

aux-comm-nf1-H↑ : ∀ nf1 -> ⟦ nf1 ⟧₁ • H ↑ ≈ H ↑ • ⟦ nf1 ⟧₁
aux-comm-nf1-H↑ nf1@(s , mc) = begin
  ⟦ nf1 ⟧₁ • H ↑ ≈⟨ assoc ⟩
  S^ s • ⟦ mc ⟧ₘ₊ • H ↑ ≈⟨ (cright aux-comm-mc-H↑ mc) ⟩
  S^ s • H ↑ • ⟦ mc ⟧ₘ₊ ≈⟨ sym assoc ⟩
  (S^ s • H ↑) • ⟦ mc ⟧ₘ₊ ≈⟨ (cleft aux-comm-S^k-H↑ s) ⟩
  (H ↑ • S^ s) • ⟦ mc ⟧ₘ₊ ≈⟨ assoc ⟩
  H ↑ • ⟦ nf1 ⟧₁ ∎

aux-comm-S^k↑-H : ∀ k -> S^ k ↑ • H ≈ H • S^ k ↑
aux-comm-S^k↑-H k = begin
  S^ k ↑ • H ≈⟨ sym (lemma-comm-H-w↑ (S^ k)) ⟩
  H • S^ k ↑ ∎

open Duality

aux-comm-CZ^a-S^b↑ : ∀ a b -> CZ^ a • S^ b ↑ ≈ S^ b ↑ • CZ^ a
aux-comm-CZ^a-S^b↑ a b = begin
  CZ^ a • S^ b ↑ ≈⟨ (cright sym (refl' (aux-↑ S (toℕ b)))) ⟩
  CZ^ a • S ↑ ^ toℕ b ≈⟨ word-comm (toℕ a) (toℕ b) (axiom comm-CZ-S↑) ⟩
  S ↑ ^ toℕ b • CZ^ a ≈⟨ (cleft refl' (aux-↑ S (toℕ b))) ⟩
  S^ b ↑ • CZ^ a ∎


aux-comm-CZ^a-S^b↑' : ∀ a b -> CZ ^ a • (S ^ b) ↑ ≈ (S ^ b) ↑ • CZ ^ a
aux-comm-CZ^a-S^b↑' a b = begin
  CZ ^ a • (S ^ b) ↑ ≈⟨ (cright sym (refl' (aux-↑ S (b)))) ⟩
  CZ ^ a • S ↑  ^ b ≈⟨ word-comm (a) (b) (axiom comm-CZ-S↑) ⟩
  S ↑  ^ b • CZ ^ a ≈⟨ (cleft refl' (aux-↑ S (b))) ⟩
  (S ^ b) ↑ • CZ ^ a ∎

open import N.Lemmas-2Qupit-Sym

aux-comm-CX-S^k↑ : ∀ k -> CX • S^ k ↑ ≈ S^ k ↑ • CX
aux-comm-CX-S^k↑ k = begin
  CX • S^ k ↑ ≈⟨ special-assoc (□ ^ 3 • □) (□ ^ 2 • □ ^ 2) auto ⟩
  (H^ ₃ • CZ) • H • S^ k ↑ ≈⟨ cright sym (aux-comm-S^k↑-H k) ⟩
  (H^ ₃ • CZ) • S^ k ↑ • H ≈⟨ by-assoc auto ⟩
  H^ ₃ • (CZ • S^ k ↑) • H ≈⟨ cright cleft aux-comm-CZ^a-S^b↑ ₁ k ⟩
  H^ ₃ • (S^ k ↑ • CZ) • H ≈⟨ trans (by-assoc auto) assoc ⟩
  (H^ ₃ • S^ k ↑) • CZ • H ≈⟨ cleft word-comm 3 1 (sym (aux-comm-S^k↑-H k)) ⟩
  (S^ k ↑ • H^ ₃) • CZ • H ≈⟨ assoc ⟩
  S^ k ↑ • CX ∎


aux-comm-CX-S^k↑-ℕ : ∀ k -> CX • (S ^ k) ↑ ≈ (S ^ k) ↑ • CX
aux-comm-CX-S^k↑-ℕ k = begin
  CX • (S ^ k) ↑ ≈⟨ special-assoc (□ ^ 3 • □) (□ ^ 2 • □ ^ 2) auto ⟩
  (H^ ₃ • CZ) • H • (S ^ k) ↑ ≈⟨ cright (lemma-comm-H-w↑ (S ^ k)) ⟩
  (H^ ₃ • CZ) • (S ^ k) ↑ • H ≈⟨ by-assoc auto ⟩
  H^ ₃ • (CZ • (S ^ k) ↑) • H ≈⟨ cright cleft aux-comm-CZ^a-S^b↑' ₁ k ⟩
  H^ ₃ • ((S ^ k) ↑ • CZ) • H ≈⟨ trans (by-assoc auto) assoc ⟩
  (H^ ₃ • (S ^ k) ↑) • CZ • H ≈⟨ cleft lemma-comm-Hᵏ-w↑ 3 (S ^ k) ⟩
  ((S ^ k) ↑ • H^ ₃) • CZ • H ≈⟨ assoc ⟩
  (S ^ k) ↑ • CX ∎



aux-comm-CX^a-S^k↑ : ∀ a k -> CX^ a • S^ k ↑ ≈ S^ k ↑ • CX^ a
aux-comm-CX^a-S^k↑ a k = word-comm (toℕ a) 1 (aux-comm-CX-S^k↑ k)

aux-comm-CX^a-CX^a' : ∀ a -> CX ^ a ≈ H ↓ ^ 3 • CZ ^ a • H ↓
aux-comm-CX^a-CX^a' a@0 = by-assoc-and (sym (axiom order-H)) auto auto
aux-comm-CX^a-CX^a' a@1 = refl
aux-comm-CX^a-CX^a' a@(₂₊ a') = begin
  CX ^ a ≈⟨ refl ⟩
  CX • CX ^ (₁₊ a') ≈⟨ cright aux-comm-CX^a-CX^a' (₁₊ a') ⟩
  (H ↓ ^ 3 • CZ • H ↓) • H ↓ ^ 3 • CZ ^ ₁₊ a' • H ↓ ≈⟨ sym assoc ⟩
  ((H ↓ ^ 3 • CZ • H ↓) • H ↓ ^ 3) • CZ ^ ₁₊ a' • H ↓ ≈⟨ cleft rewrite-sym0 100 auto ⟩
  (H ↓ ^ 3 • CZ) • CZ ^ (₁₊ a') • H ↓ ≈⟨ special-assoc (□ ^ 2 • □ ^ 2) (□ • □ ^ 2 • □) auto ⟩
  H ↓ ^ 3 • (CZ • CZ ^ (₁₊ a')) • H ↓ ≈⟨ refl ⟩
  H ↓ ^ 3 • CZ ^ a • H ↓ ∎
  where
  open Sym0-Rewriting (₁₊ n)


aux-comm-CX^a-S^k↑' : ∀ a k -> (H ↓ ^ 3 • CZ^ a • H ↓) • S^ k ↑ ≈ S^ k ↑ • (H ↓ ^ 3 • CZ^ a • H ↓)
aux-comm-CX^a-S^k↑' a k = begin
  (H ↓ ^ 3 • CZ^ a • H ↓) • S^ k ↑ ≈⟨ cleft sym (aux-comm-CX^a-CX^a' (toℕ a)) ⟩
  CX^ a • S^ k ↑ ≈⟨ aux-comm-CX^a-S^k↑ a k ⟩
  S^ k ↑ • CX^ a ≈⟨ cright aux-comm-CX^a-CX^a' (toℕ a) ⟩
  S^ k ↑ • (H ↓ ^ 3 • CZ^ a • H ↓) ∎



aux-comm-m-S^ : ∀ m k -> ⟦ m ⟧ₘ • S^ k ↑ ≈ S^ k ↑ • ⟦ m ⟧ₘ
aux-comm-m-S^ m k = begin
  ⟦ m ⟧ₘ • S^ k ↑ ≈⟨ cright sym (refl' (aux-↑ S (toℕ k))) ⟩
  ⟦ m ⟧ₘ • S ↑ ^ toℕ k ≈⟨ word-comm 1 (toℕ k) (aux-comm-m-S↑ m) ⟩
  S ↑ ^ toℕ k • ⟦ m ⟧ₘ ≈⟨ cleft refl' (aux-↑ S (toℕ k)) ⟩
  S^ k ↑ • ⟦ m ⟧ₘ ∎

aux-comm-mc-S^ : ∀ mc k -> ⟦ mc ⟧ₘ₊ • S^ k ↑ ≈ S^ k ↑ • ⟦ mc ⟧ₘ₊
aux-comm-mc-S^ mc@(m , c) k = begin
  ⟦ mc ⟧ₘ₊ • S^ k ↑ ≈⟨ assoc ⟩
  ⟦ m ⟧ₘ • ⟦ c ⟧ₕₛ • S^ k ↑ ≈⟨ cright aux-comm-c-S^k↑ c k ⟩
  ⟦ m ⟧ₘ • S^ k ↑ • ⟦ c ⟧ₕₛ ≈⟨ sym assoc ⟩
  (⟦ m ⟧ₘ • S^ k ↑) • ⟦ c ⟧ₕₛ ≈⟨ cleft aux-comm-m-S^ m k ⟩
  (S^ k ↑ • ⟦ m ⟧ₘ) • ⟦ c ⟧ₕₛ ≈⟨ assoc ⟩
  S^ k ↑ • ⟦ m ⟧ₘ • ⟦ c ⟧ₕₛ ≈⟨ refl ⟩
  S^ k ↑ • ⟦ mc ⟧ₘ₊ ∎


aux-comm-MM : ∀ m m' -> M m • M m' ↑ ≈ M m' ↑ • M m
aux-comm-MM m m'@x' = begin
  M m • (S^ x • H • S^ x⁻¹ • H • S^ x • H) ↑ ≈⟨ sym assoc ⟩
  (M m • S^ x ↑) • (H • S^ x⁻¹ • H • S^ x • H) ↑ ≈⟨ cleft aux-comm-m-S^ m (m' .proj₁) ⟩
  (S^ x ↑ • M m) • (H • S^ x⁻¹ • H • S^ x • H) ↑ ≈⟨ special-assoc (□ ^ 2 • □ ^ 2) (□ • □ ^ 2 • □) auto ⟩
  S^ x ↑ • (M m • H ↑) • (S^ x⁻¹ • H • S^ x • H) ↑ ≈⟨ cright cleft aux-comm-m-H↑ m ⟩
  S^ x ↑ • (H ↑ • M m) • (S^ x⁻¹ • H • S^ x • H) ↑ ≈⟨ cright special-assoc (□ ^ 2 • □ ^ 2) (□ • □ ^ 2 • □) auto  ⟩
  S^ x ↑ • H ↑ • (M m • S^ x⁻¹ ↑) • (H • S^ x • H) ↑ ≈⟨ cright cright cleft aux-comm-m-S^ m  x⁻¹ ⟩
  S^ x ↑ • H ↑ • (S^ x⁻¹ ↑ • M m) • (H • S^ x • H) ↑ ≈⟨ cright cright special-assoc (□ ^ 2 • □ ^ 2) (□ • □ ^ 2 • □) auto ⟩
  S^ x ↑ • H ↑ • S^ x⁻¹ ↑ • (M m • H ↑) • (S^ x • H) ↑ ≈⟨ cright cright cright cleft aux-comm-m-H↑ m ⟩
  S^ x ↑ • H ↑ • S^ x⁻¹ ↑ • (H ↑ • M m) • (S^ x • H) ↑ ≈⟨ cright cright cright special-assoc (□ ^ 2 • □ ^ 2) (□ • □ ^ 2 • □) auto ⟩
  S^ x ↑ • H ↑ • S^ x⁻¹ ↑ • H ↑ • (M m • S^ x ↑) • H ↑ ≈⟨ cright cright cright cright cleft aux-comm-m-S^ m (m' .proj₁) ⟩
  S^ x ↑ • H ↑ • S^ x⁻¹ ↑ • H ↑ • (S^ x ↑ • M m) • H ↑ ≈⟨ cright cright cright cright assoc ⟩
  S^ x ↑ • H ↑ • S^ x⁻¹ ↑ • H ↑ • S^ x ↑ • M m • H ↑ ≈⟨  cright cright cright cright cright aux-comm-m-H↑ m ⟩
  S^ x ↑ • H ↑ • S^ x⁻¹ ↑ • H ↑ • S^ x ↑ • H ↑ • M m ≈⟨ special-assoc (□ ^ 7) (□ ^ 6 • □) auto ⟩
  M m' ↑ • M m ∎
    where
    x = x' .proj₁
    x⁻¹ = ((x' ⁻¹) .proj₁ )


aux-comm-CM : ∀ c m' -> ⟦ c ⟧ₕₛ • ⟦ m' ⟧ₘ ↑ ≈ ⟦ m' ⟧ₘ ↑ • ⟦ c ⟧ₕₛ
aux-comm-CM c m'@x' = begin
  ⟦ c ⟧ₕₛ • (S^ x • H • S^ x⁻¹ • H • S^ x • H) ↑ ≈⟨ sym assoc ⟩
  (⟦ c ⟧ₕₛ • S^ x ↑) • (H • S^ x⁻¹ • H • S^ x • H) ↑ ≈⟨ cleft aux-comm-c-S^k↑ c (m' .proj₁) ⟩
  (S^ x ↑ • ⟦ c ⟧ₕₛ) • (H • S^ x⁻¹ • H • S^ x • H) ↑ ≈⟨ special-assoc (□ ^ 2 • □ ^ 2) (□ • □ ^ 2 • □) auto ⟩
  S^ x ↑ • (⟦ c ⟧ₕₛ • H ↑) • (S^ x⁻¹ • H • S^ x • H) ↑ ≈⟨ cright cleft aux-comm-c-H↑ c ⟩
  S^ x ↑ • (H ↑ • ⟦ c ⟧ₕₛ) • (S^ x⁻¹ • H • S^ x • H) ↑ ≈⟨ cright special-assoc (□ ^ 2 • □ ^ 2) (□ • □ ^ 2 • □) auto  ⟩
  S^ x ↑ • H ↑ • (⟦ c ⟧ₕₛ • S^ x⁻¹ ↑) • (H • S^ x • H) ↑ ≈⟨ cright cright cleft aux-comm-c-S^k↑ c  x⁻¹ ⟩
  S^ x ↑ • H ↑ • (S^ x⁻¹ ↑ • ⟦ c ⟧ₕₛ) • (H • S^ x • H) ↑ ≈⟨ cright cright special-assoc (□ ^ 2 • □ ^ 2) (□ • □ ^ 2 • □) auto ⟩
  S^ x ↑ • H ↑ • S^ x⁻¹ ↑ • (⟦ c ⟧ₕₛ • H ↑) • (S^ x • H) ↑ ≈⟨ cright cright cright cleft aux-comm-c-H↑ c ⟩
  S^ x ↑ • H ↑ • S^ x⁻¹ ↑ • (H ↑ • ⟦ c ⟧ₕₛ) • (S^ x • H) ↑ ≈⟨ cright cright cright special-assoc (□ ^ 2 • □ ^ 2) (□ • □ ^ 2 • □) auto ⟩
  S^ x ↑ • H ↑ • S^ x⁻¹ ↑ • H ↑ • (⟦ c ⟧ₕₛ • S^ x ↑) • H ↑ ≈⟨ cright cright cright cright cleft aux-comm-c-S^k↑ c (m' .proj₁) ⟩
  S^ x ↑ • H ↑ • S^ x⁻¹ ↑ • H ↑ • (S^ x ↑ • ⟦ c ⟧ₕₛ) • H ↑ ≈⟨ cright cright cright cright assoc ⟩
  S^ x ↑ • H ↑ • S^ x⁻¹ ↑ • H ↑ • S^ x ↑ • ⟦ c ⟧ₕₛ • H ↑ ≈⟨  cright cright cright cright cright aux-comm-c-H↑ c ⟩
  S^ x ↑ • H ↑ • S^ x⁻¹ ↑ • H ↑ • S^ x ↑ • H ↑ • ⟦ c ⟧ₕₛ ≈⟨ special-assoc (□ ^ 7) (□ ^ 6 • □) auto ⟩
  M m' ↑ • ⟦ c ⟧ₕₛ ∎
    where
    x = x' .proj₁
    x⁻¹ = ((x' ⁻¹) .proj₁ )

aux-comm-CC : ∀ c c' -> ⟦ c ⟧ₕₛ • ⟦ c' ⟧ₕₛ ↑ ≈ ⟦ c' ⟧ₕₛ ↑ • ⟦ c ⟧ₕₛ
aux-comm-CC c@(ε) c'@(ε) = refl
aux-comm-CC c@(ε) c'@(HS^ k') = trans left-unit (sym right-unit)
aux-comm-CC c@(HS^ k) c'@(ε) = trans right-unit (sym left-unit)
aux-comm-CC c@(HS^ k) c'@(HS^ k') = begin
  ⟦ c ⟧ₕₛ • ⟦ c' ⟧ₕₛ ↑ ≈⟨ assoc ⟩
  H • S^ k • H ↑ • S^ k' ↑ ≈⟨ sym (cong refl assoc) ⟩
  H • (S^ k • H ↑) • S^ k' ↑ ≈⟨ cright cleft lemma-comm-Sᵏ-w↑ (toℕ k) H ⟩
  H • (H ↑ • S^ k) • S^ k' ↑ ≈⟨ special-assoc (□ • □ ^ 2 • □) (□ ^ 2 • □ ^ 2 ) auto ⟩
  (H • H ↑) • S^ k • S^ k' ↑ ≈⟨ cong (sym (axiom comm-H)) (lemma-comm-Sᵏ-w↑ (toℕ k) (S^ k')) ⟩
  (H ↑ • H) • S^ k' ↑ • S^ k ≈⟨ special-assoc (□ ^ 2 • □ ^ 2 ) (□ • □ ^ 2 • □) auto ⟩
  H ↑ • (H • S^ k' ↑) • S^ k ≈⟨ cright cleft lemma-comm-H-w↑ (S^ k') ⟩
  H ↑ • (S^ k' ↑ • H) • S^ k ≈⟨ special-assoc (□ • □ ^ 2 • □) (□ ^ 2 • □ ^ 2 ) auto  ⟩
  ⟦ c' ⟧ₕₛ ↑ • ⟦ c ⟧ₕₛ ∎

aux-comm-MC : ∀ m c' -> ⟦ m ⟧ₘ • ⟦ c' ⟧ₕₛ ↑  ≈ ⟦ c' ⟧ₕₛ ↑ • ⟦ m ⟧ₘ
aux-comm-MC m c'@(ε) = trans right-unit (sym left-unit)
aux-comm-MC m c'@(HS^ k) = begin
  ⟦ m ⟧ₘ • ⟦ c' ⟧ₕₛ ↑  ≈⟨ sym assoc ⟩
  (⟦ m ⟧ₘ • H ↑) • S^ k ↑  ≈⟨ cleft aux-comm-m-H↑ m ⟩
  (H ↑ • ⟦ m ⟧ₘ) • S^ k ↑  ≈⟨ assoc ⟩
  H ↑ • ⟦ m ⟧ₘ • S^ k ↑  ≈⟨ cright aux-comm-m-S^k↑ m k ⟩
  H ↑ • S^ k ↑ • ⟦ m ⟧ₘ  ≈⟨ sym assoc ⟩
  ⟦ c' ⟧ₕₛ ↑ • ⟦ m ⟧ₘ ∎


aux-comm-MMC : ∀ m m' c' -> ⟦ m ⟧ₘ • ⟦ m' , c' ⟧ₘ₊ ↑ ≈ ⟦ m' , c' ⟧ₘ₊ ↑ • ⟦ m ⟧ₘ
aux-comm-MMC m m'@x' c' = begin
  ⟦ m ⟧ₘ • ⟦ m' , c' ⟧ₘ₊ ↑ ≈⟨ sym assoc ⟩
  (⟦ m ⟧ₘ • ⟦ m' ⟧ₘ ↑) • ⟦ c' ⟧ₕₛ ↑ ≈⟨ cleft (aux-comm-MM m m') ⟩
  (⟦ m' ⟧ₘ ↑ • ⟦ m ⟧ₘ) • ⟦ c' ⟧ₕₛ ↑ ≈⟨ assoc ⟩
  ⟦ m' ⟧ₘ ↑ • (⟦ m ⟧ₘ • ⟦ c' ⟧ₕₛ ↑) ≈⟨ cright  aux-comm-MC m c' ⟩
  ⟦ m' ⟧ₘ ↑ • (⟦ c' ⟧ₕₛ ↑ • ⟦ m ⟧ₘ) ≈⟨ sym assoc ⟩
  ⟦ m' , c' ⟧ₘ₊ ↑ • ⟦ m ⟧ₘ ∎


aux-comm-MCMC : ∀ m c m' c' -> ⟦ m , c ⟧ₘ₊ • ⟦ m' , c' ⟧ₘ₊ ↑ ≈ ⟦ m' , c' ⟧ₘ₊ ↑ • ⟦ m , c ⟧ₘ₊
aux-comm-MCMC m c m'@x' c' = begin
  ⟦ m , c ⟧ₘ₊ • ⟦ m' , c' ⟧ₘ₊ ↑ ≈⟨ special-assoc (□ ^ 2 • □ ^ 2 ) (□ • □ ^ 2 • □) auto ⟩
  ⟦ m ⟧ₘ • (⟦ c ⟧ₕₛ • ⟦ m' ⟧ₘ ↑) • ⟦ c' ⟧ₕₛ ↑ ≈⟨ cright cleft aux-comm-CM c m' ⟩
  ⟦ m ⟧ₘ • (⟦ m' ⟧ₘ ↑ • ⟦ c ⟧ₕₛ) • ⟦ c' ⟧ₕₛ ↑ ≈⟨ special-assoc (□ • □ ^ 2 • □) (□ ^ 2 • □ ^ 2 ) auto ⟩
  (⟦ m ⟧ₘ • ⟦ m' ⟧ₘ ↑) • ⟦ c ⟧ₕₛ • ⟦ c' ⟧ₕₛ ↑ ≈⟨ cong (aux-comm-MM m m') (aux-comm-CC c c') ⟩
  (⟦ m' ⟧ₘ ↑ • ⟦ m ⟧ₘ) • ⟦ c' ⟧ₕₛ ↑ • ⟦ c ⟧ₕₛ ≈⟨ special-assoc (□ ^ 2 • □ ^ 2 ) (□ • □ ^ 2 • □) auto ⟩
  ⟦ m' ⟧ₘ ↑ • (⟦ m ⟧ₘ • ⟦ c' ⟧ₕₛ ↑) • ⟦ c ⟧ₕₛ ≈⟨ cright cleft aux-comm-MC m c' ⟩
  ⟦ m' ⟧ₘ ↑ • (⟦ c' ⟧ₕₛ ↑ • ⟦ m ⟧ₘ) • ⟦ c ⟧ₕₛ ≈⟨ special-assoc (□ • □ ^ 2 • □) (□ ^ 2 • □ ^ 2 ) auto ⟩
  ⟦ m' , c' ⟧ₘ₊ ↑ • ⟦ m , c ⟧ₘ₊ ∎


aux-comm-CMC : ∀ c m' c' -> ⟦ c ⟧ₕₛ • ⟦ m' , c' ⟧ₘ₊ ↑ ≈ ⟦ m' , c' ⟧ₘ₊ ↑ • ⟦ c ⟧ₕₛ
aux-comm-CMC c m'@x' c' = begin
  ⟦ c ⟧ₕₛ • ⟦ m' , c' ⟧ₘ₊ ↑ ≈⟨ sym assoc ⟩
  (⟦ c ⟧ₕₛ • ⟦ m' ⟧ₘ ↑) • ⟦ c' ⟧ₕₛ ↑ ≈⟨  cleft aux-comm-CM c m' ⟩
  (⟦ m' ⟧ₘ ↑ • ⟦ c ⟧ₕₛ) • ⟦ c' ⟧ₕₛ ↑ ≈⟨ assoc ⟩
  (⟦ m' ⟧ₘ ↑) • ⟦ c ⟧ₕₛ • ⟦ c' ⟧ₕₛ ↑ ≈⟨ cright (aux-comm-CC c c') ⟩
  ⟦ m' ⟧ₘ ↑ • ⟦ c' ⟧ₕₛ ↑ • ⟦ c ⟧ₕₛ ≈⟨ sym assoc ⟩
  ⟦ m' , c' ⟧ₘ₊ ↑ • ⟦ c ⟧ₕₛ ∎


aux-comm-CSMC : ∀ c s m' c' -> ⟦ c ⟧ₕₛ • ⟦ s , m' , c' ⟧₁ ↑ ≈ ⟦ s , m' , c' ⟧₁ ↑ • ⟦ c ⟧ₕₛ
aux-comm-CSMC c s m'@x' c' = begin
  ⟦ c ⟧ₕₛ • ⟦ s , m' , c' ⟧₁ ↑ ≈⟨ sym assoc ⟩
  (⟦ c ⟧ₕₛ • S^ s ↑) • ⟦ m' , c' ⟧ₘ₊ ↑ ≈⟨  cleft aux-comm-c-S^k↑ c s ⟩
  (S^ s ↑ • ⟦ c ⟧ₕₛ) • ⟦ m' , c' ⟧ₘ₊ ↑ ≈⟨ assoc ⟩
  S^ s ↑ • ⟦ c ⟧ₕₛ • ⟦ m' , c' ⟧ₘ₊ ↑ ≈⟨ cright (aux-comm-CMC c m' c') ⟩
  S^ s ↑ • ⟦ m' , c' ⟧ₘ₊ ↑ • ⟦ c ⟧ₕₛ ≈⟨ sym assoc ⟩
  ⟦ s , m' , c' ⟧₁ ↑ • ⟦ c ⟧ₕₛ ∎


aux-comm-MSMC : ∀ mc nf1 -> ⟦ mc ⟧ₘ • ⟦ nf1 ⟧₁ ↑ ≈ ⟦ nf1 ⟧₁ ↑ • ⟦ mc ⟧ₘ
aux-comm-MSMC m nf1@(s' , m' , c') = begin
  ⟦ m ⟧ₘ • ⟦ s' , m' , c' ⟧₁ ↑ ≈⟨ sym assoc ⟩
  (⟦ m ⟧ₘ • S^ s' ↑) • ⟦ m' , c' ⟧ₘ₊ ↑ ≈⟨ cleft aux-comm-m-S^ m s' ⟩
  (S^ s' ↑ • ⟦ m ⟧ₘ) • ⟦ m' , c' ⟧ₘ₊ ↑ ≈⟨ assoc ⟩
  S^ s' ↑ • ⟦ m ⟧ₘ • ⟦ m' , c' ⟧ₘ₊ ↑ ≈⟨ cright aux-comm-MMC m m' c' ⟩
  S^ s' ↑ • ⟦ m' , c' ⟧ₘ₊ ↑ • ⟦ m ⟧ₘ ≈⟨ sym assoc ⟩
  ⟦ s' , m' , c' ⟧₁ ↑ • ⟦ m ⟧ₘ ∎


aux-comm-MCSMC : ∀ mc nf1 -> ⟦ mc ⟧ₘ₊ • ⟦ nf1 ⟧₁ ↑ ≈ ⟦ nf1 ⟧₁ ↑ • ⟦ mc ⟧ₘ₊
aux-comm-MCSMC mc@(m , c) nf1@(s' , m' , c') = begin
  ⟦ m , c ⟧ₘ₊ • ⟦ s' , m' , c' ⟧₁ ↑ ≈⟨ sym assoc ⟩
  (⟦ m , c ⟧ₘ₊ • S^ s' ↑) • ⟦ m' , c' ⟧ₘ₊ ↑ ≈⟨ cleft aux-comm-mc-S^ (m , c) s' ⟩
  (S^ s' ↑ • ⟦ m , c ⟧ₘ₊) • ⟦ m' , c' ⟧ₘ₊ ↑ ≈⟨ assoc ⟩
  S^ s' ↑ • ⟦ m , c ⟧ₘ₊ • ⟦ m' , c' ⟧ₘ₊ ↑ ≈⟨ cright aux-comm-MCMC m c m' c' ⟩
  S^ s' ↑ • ⟦ m' , c' ⟧ₘ₊ ↑ • ⟦ m , c ⟧ₘ₊ ≈⟨ sym assoc ⟩
  ⟦ s' , m' , c' ⟧₁ ↑ • ⟦ m , c ⟧ₘ₊ ∎


