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



module N.Ex-Sym2n (p-2 : ℕ) (p-prime : Prime (2+ p-2))  where

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
open import N.Ex-Sym p-2 p-prime
open import N.Ex-Sym2 p-2 p-prime
open Lemmas0a


private
  variable
    n : ℕ

open Symplectic
open Lemmas-Sym

open Symplectic-GroupLike

open import Data.Nat.DivMod
open import Data.Fin.Properties


open Duality



lemma-HCZHS : let open PB ((₂₊ n) QRel,_===_) in
  S ↑ • S ↓ • CZ • H ↑ • CZ • H ↑ ≈ H ↑ • CZ • H ↑ • S ↑
lemma-HCZHS {n} = begin
  S ↑ • S ↓ • CZ • H ↑ • CZ • H ↑ ≈⟨ general-comm auto ⟩
  S ↑ • (CZ • H ↑ • CZ) • H ↑ • S ↓ ≈⟨ (cright (cleft axiom selinger-c10)) ⟩
  S ↑ • (S⁻¹ ↑ • H ↑ • S⁻¹ ↑ • CZ • H ↑ • S⁻¹ ↑ • S⁻¹ ↓) • H ↑ • S ↓ ≈⟨ (cright cright general-comm auto) ⟩
  S ↑ • (S⁻¹ ↑ • H ↑ • S⁻¹ ↑ • CZ • H ↑ • S⁻¹ ↑ • S⁻¹ ↓) • S ↓ • H ↑ ≈⟨ special-assoc (□ • □ ^ 7 • □ ^ 2) (□ ^ 2 • □ ^ 5 • □ ^ 2 • □) auto ⟩
  (S ↑ • S⁻¹ ↑) • (H ↑ • S⁻¹ ↑ • CZ • H ↑ • S⁻¹ ↑) • (S⁻¹ ↓ • S ↓) • H ↑ ≈⟨ cong ((aux0)) (cright trans (cong aux1 refl) left-unit) ⟩
  ε • (H ↑ • S⁻¹ ↑ • CZ • H ↑ • S⁻¹ ↑) • H ↑ ≈⟨ left-unit ⟩
  (H ↑ • S⁻¹ ↑ • CZ • H ↑ • S⁻¹ ↑) • H ↑ ≈⟨ special-assoc (□ ^ 5 • □) (□ • □ ^ 2 • □ ^ 3) auto ⟩
  H ↑ • (S⁻¹ ↑ • CZ) • H ↑ • S⁻¹ ↑ • H ↑ ≈⟨ (cright cleft sym aux2) ⟩
  H ↑ • (CZ • S⁻¹ ↑) • H ↑ • S⁻¹ ↑ • H ↑ ≈⟨ by-assoc auto ⟩
  (H ↑ • CZ) • S⁻¹ ↑ • H ↑ • S⁻¹ ↑ • H ↑ ≈⟨ (cright lemma-cong↑ _ _ lemma-S⁻¹HS⁻¹H) ⟩
  (H ↑ • CZ) • (H • S) ↑ ≈⟨ by-assoc auto ⟩
  H ↑ • CZ • H ↑ • S ↑ ∎
  where
  open PB ((₂₊ n) QRel,_===_)
  open PP ((₂₊ n) QRel,_===_)
  module M1P = PP ((₁₊ n) QRel,_===_)
  module M1B = PB ((₁₊ n) QRel,_===_)
  open SR word-setoid
  open Pattern-Assoc
  open Commuting-Symplectic n
  open Symplectic-GroupLike
  open Basis-Change _ ((₂₊ n) QRel,_===_) grouplike
  aux0 : S ↑ • S⁻¹ ↑ ≈ ε
  aux0 = begin
    S ↑ • S⁻¹ ↑ ≈⟨ sym (cright refl' (aux-↑ S p-1)) ⟩
    S ↑ • S ↑ ^ p-1 ≈⟨ refl' (aux-↑ S p) ⟩
    (S ^ p) ↑ ≈⟨ lemma-cong↑ _ _ (M1B.axiom order-S) ⟩ 
    ε ∎

  aux1 : S⁻¹ ↓ • S ↓ ≈ ε
  aux1 = begin
    S⁻¹ ↓ • S ↓ ≈⟨ word-comm p-1 1 refl ⟩
    S ^ p ≈⟨ axiom order-S ⟩
    ε ∎

  aux2 : CZ • S⁻¹ ↑ ≈ S⁻¹ ↑ • CZ
  aux2 = begin
    CZ • S⁻¹ ↑ ≈⟨ (cright sym (refl' (aux-↑ S p-1))) ⟩
    CZ • S ↑ ^ p-1 ≈⟨ word-comm 1 p-1 (axiom comm-CZ-S↑) ⟩
    S ↑ ^ p-1 • CZ ≈⟨ (cleft refl' (aux-↑ S p-1)) ⟩
    S⁻¹ ↑ • CZ ∎


lemma-HCZHS-dual : let open PB ((₂₊ n) QRel,_===_) in
  S ↓ • S ↑ • CZ • H ↓ • CZ • H ↓ ≈ H ↓ • CZ • H ↓ • S ↓
lemma-HCZHS-dual {n} = begin
  S ↓ • S ↑ • CZ • H ↓ • CZ • H ↓ ≈⟨ general-comm auto ⟩
  S ↓ • (CZ • H ↓ • CZ) • H ↓ • S ↑ ≈⟨ (cright (cleft axiom selinger-c11)) ⟩
  S ↓ • (S⁻¹ ↓ • H ↓ • S⁻¹ ↓ • CZ • H ↓ • S⁻¹ ↓ • S⁻¹ ↑) • H ↓ • S ↑ ≈⟨ (cright cright general-comm auto) ⟩
  S ↓ • (S⁻¹ ↓ • H ↓ • S⁻¹ ↓ • CZ • H ↓ • S⁻¹ ↓ • S⁻¹ ↑) • S ↑ • H ↓ ≈⟨ special-assoc (□ • □ ^ 7 • □ ^ 2) (□ ^ 2 • □ ^ 5 • □ ^ 2 • □) auto ⟩
  (S ↓ • S⁻¹ ↓) • (H ↓ • S⁻¹ ↓ • CZ • H ↓ • S⁻¹ ↓) • (S⁻¹ ↑ • S ↑) • H ↓ ≈⟨ cong ((aux0)) (cright trans (cong aux1 refl) left-unit) ⟩
  ε • (H ↓ • S⁻¹ ↓ • CZ • H ↓ • S⁻¹ ↓) • H ↓ ≈⟨ left-unit ⟩
  (H ↓ • S⁻¹ ↓ • CZ • H ↓ • S⁻¹ ↓) • H ↓ ≈⟨ special-assoc (□ ^ 5 • □) (□ • □ ^ 2 • □ ^ 3) auto ⟩
  H ↓ • (S⁻¹ ↓ • CZ) • H ↓ • S⁻¹ ↓ • H ↓ ≈⟨ (cright cleft sym aux2) ⟩
  H ↓ • (CZ • S⁻¹ ↓) • H ↓ • S⁻¹ ↓ • H ↓ ≈⟨ by-assoc auto ⟩
  (H ↓ • CZ) • S⁻¹ ↓ • H ↓ • S⁻¹ ↓ • H ↓ ≈⟨ (cright lemma-S⁻¹HS⁻¹H) ⟩
  (H ↓ • CZ) • (H • S) ↓ ≈⟨ by-assoc auto ⟩
  H ↓ • CZ • H ↓ • S ↓ ∎
  where
  open PB ((₂₊ n) QRel,_===_)
  open PP ((₂₊ n) QRel,_===_)
  module M1P = PP ((₁₊ n) QRel,_===_)
  module M1B = PB ((₁₊ n) QRel,_===_)
  open SR word-setoid
  open Pattern-Assoc
  open Commuting-Symplectic n
  open Symplectic-GroupLike
  open Basis-Change _ ((₂₊ n) QRel,_===_) grouplike
  aux0 : S ↓ • S⁻¹ ↓ ≈ ε
  aux0 = begin
    S ↓ • S⁻¹ ↓ ≈⟨ sym (cright refl' auto) ⟩
    S ↓ • S ↓ ^ p-1 ≈⟨ refl' auto ⟩
    (S ^ p) ↓ ≈⟨ axiom order-S ⟩
    ε ∎

  aux1 : S⁻¹ ↑ • S ↑ ≈ ε
  aux1 = begin
    S⁻¹ ↑ • S ↑ ≈⟨ lemma-cong↑ _ _ (M1P.word-comm p-1 1 M1B.refl) ⟩
    (S ^ p) ↑ ≈⟨ lemma-cong↑ _ _  (M1B.axiom order-S) ⟩
    ε ∎

  aux2 : CZ • S⁻¹ ↓ ≈ S⁻¹ ↓ • CZ
  aux2 = begin
    CZ • S⁻¹ ↓ ≈⟨ (cright sym (refl' (auto))) ⟩
    CZ • S ↓ ^ p-1 ≈⟨ word-comm 1 p-1 (axiom comm-CZ-S↓) ⟩
    S ↓ ^ p-1 • CZ ≈⟨ (cleft refl' (auto)) ⟩
    S⁻¹ ↓ • CZ ∎


lemma-HCZHS^k : let open PB ((₂₊ n) QRel,_===_) in ∀ k -> 
  S ↑ ^ k • S ^ k • CZ ^ k • H ↑ • CZ • H ↑ ≈ H ↑ • CZ • H ↑ • S ↑ ^ k
lemma-HCZHS^k {n} k@0 = by-assoc auto
  where
  open PB ((₂₊ n) QRel,_===_)
  open PP ((₂₊ n) QRel,_===_)
lemma-HCZHS^k {n} k@1 = lemma-HCZHS
lemma-HCZHS^k {n} k@(₂₊ k') = begin
  S ↑ ^ k • S ^ k • CZ ^ k • H ↑ • CZ • H ↑ ≈⟨ rewrite-sym0 100 auto ⟩
  (S ↑ • S ↑ ^ (₁₊ k')) • (S ↓ • S ↓ ^ (₁₊ k')) • CZ ^ k • H ↑ • CZ • H ↑ ≈⟨ special-assoc (□ ^ 2 • □ ^ 2 • □ ^ 4) (□ • □ ^ 2 • □ • □ • □ ^ 3)  auto ⟩
  S ↑ • (S ↑ ^ (₁₊ k') • S ↓) • S ↓ ^ (₁₊ k') • CZ ^ k • H ↑ • CZ • H ↑ ≈⟨ (cright cleft word-comm (₁₊ k') 1 (axiom comm-S)) ⟩
  S ↑ • (S ↓ • S ↑ ^ (₁₊ k')) • S ↓ ^ (₁₊ k') • (CZ • CZ ^ (₁₊ k')) • H ↑ • CZ • H ↑ ≈⟨ special-assoc (□ • □ ^ 2 • □ • □ ^ 2 • □ ^ 3) (□ ^ 3 • □ ^ 2 • □ ^ 4) auto ⟩
  (S ↑ • S ↓ • S ↑ ^ (₁₊ k')) • (S ↓ ^ (₁₊ k') • CZ) • CZ ^ (₁₊ k') • H ↑ • CZ • H ↑ ≈⟨ (cright cleft word-comm (₁₊ k') 1 (sym (axiom comm-CZ-S↓))) ⟩
  (S ↑ • S ↓ • S ↑ ^ (₁₊ k')) • (CZ • S ↓ ^ (₁₊ k')) • CZ ^ (₁₊ k') • H ↑ • CZ • H ↑ ≈⟨ special-assoc (□ ^ 3 • □ ^ 2 • □ ^ 4) (□ ^ 2 • □ ^ 2 • □ ^ 5) auto ⟩
  (S ↑ • S ↓) • (S ↑ ^ (₁₊ k') • CZ) • S ↓ ^ (₁₊ k') • CZ ^ (₁₊ k') • H ↑ • CZ • H ↑ ≈⟨ (cright cleft word-comm (₁₊ k') 1 (sym (axiom comm-CZ-S↑))) ⟩
  (S ↑ • S ↓) • (CZ • S ↑ ^ (₁₊ k')) • S ↓ ^ (₁₊ k') • CZ ^ (₁₊ k') • H ↑ • CZ • H ↑ ≈⟨ by-assoc auto ⟩
  (S ↑ • S ↓ • CZ) • (S ↑ ^ (₁₊ k') • S ↓ ^ (₁₊ k') • CZ ^ (₁₊ k') • H ↑ • CZ • H ↑) ≈⟨ ( cright lemma-HCZHS^k (₁₊ k')) ⟩
  (S ↑ • S ↓ • CZ) • (H ↑ • CZ • H ↑ • S ↑ ^ (₁₊ k')) ≈⟨ by-assoc auto ⟩
  (S ↑ • S ↓ • CZ • H ↑ • CZ • H ↑) • S ↑ ^ (₁₊ k') ≈⟨ (cleft lemma-HCZHS) ⟩
  (H ↑ • CZ • H ↑ • S ↑) • S ↑ ^ (₁₊ k') ≈⟨ by-assoc auto ⟩
  H ↑ • CZ • H ↑ • S ↑ ^ k ∎
  where
  open PB ((₂₊ n) QRel,_===_)
  open PP ((₂₊ n) QRel,_===_)
  open SR word-setoid
  open Commuting-Symplectic (n)
  open Sym0-Rewriting (suc n)
  open Pattern-Assoc

open import N.Lemmas-2Qupit-Sym p-2 p-prime

lemma-semi-HH↑-CZ^k' : let open PB ((₂₊ n) QRel,_===_) in ∀ k ->

  H ↑ ^ 2 • CZ^ k ≈ CZ^ (- k) • H ↑ ^ 2

lemma-semi-HH↑-CZ^k' {n} k = lemma-semi-HH↑-CZ^k k
  where
  open import N.Lemmas-2Qupit-Sym p-2 p-prime as Q2
  open Q2.Lemmas-2Q n


lemma-semi-HH↑-CZ^k'-ℕ : let open PB ((₂₊ n) QRel,_===_) in ∀ k -> let -k = p-1 Nat.* k in 

  H ↑ ^ 2 • CZ ^ k ≈ CZ ^ -k • H ↑ ^ 2

lemma-semi-HH↑-CZ^k'-ℕ {n} k = begin
  H ↑ ^ 2 • CZ ^ k ≈⟨ lemma-semi-HH↑-CZ^k′ k ⟩
  CZ^ ₋₁ ^ k • HH ↑ ≈⟨ (cleft ( lemma-^^ CZ (toℕ ₚ₋₁) k)) ⟩
  CZ ^ (toℕ ₚ₋₁ Nat.* k) • HH ↑ ≈⟨ (cleft refl' (Eq.cong (CZ ^_) (Eq.cong (Nat._* k) lemma-toℕ-ₚ₋₁))) ⟩
  CZ ^ -k • H ↑ ^ 2 ∎
  where
  -k = p-1 Nat.* k
  open PB ((₂₊ n) QRel,_===_)
  open PP ((₂₊ n) QRel,_===_)
  module M1P = PP ((₁₊ n) QRel,_===_)
  module M1B = PB ((₁₊ n) QRel,_===_)
  open SR word-setoid
  open Pattern-Assoc
  open Commuting-Symplectic n
  open Symplectic-GroupLike
  open Basis-Change _ ((₂₊ n) QRel,_===_) grouplike
  open import N.Lemmas-2Qupit-Sym p-2 p-prime as Q2
  open Q2.Lemmas-2Q n


lemma-XCS^k : let open PB ((₂₊ n) QRel,_===_) in ∀ k -> 
  S^ k ↑ • S^ k • CZ^ (- k) • H ↑ ^ 3 • CZ • H ↑ ≈ H ↑ ^ 3 • CZ • H ↑ • S^ k ↑
lemma-XCS^k {n} k = bbc (HH ↑) ε auxn
  where
  open PB ((₂₊ n) QRel,_===_)
  open PP ((₂₊ n) QRel,_===_)
  module M1P = PP ((₁₊ n) QRel,_===_)
  module M1B = PB ((₁₊ n) QRel,_===_)
  open SR word-setoid
  open Pattern-Assoc
  open Sym0-Rewriting (suc n)
  open Commuting-Symplectic n
  open Symplectic-GroupLike
  open Basis-Change _ ((₂₊ n) QRel,_===_) grouplike
  open import N.Lemmas-2Qupit-Sym p-2 p-prime as Q2
  open Q2.Lemmas-2Q n
  open import Algebra.Properties.Ring (+-*-ring p-2)

  auxn : HH ↑ • ((S^ k ↑) • S^ k • CZ^ (- k) • ((H ↑) • (H ↑) • (H ↑)) • CZ • (H ↑)) • ε
    ≈ HH ↑ • (((H ↑) • (H ↑) • (H ↑)) • CZ • (H ↑) • (S^ k ↑)) • ε
  auxn = begin
    HH ↑ • ((S^ k ↑) • S^ k • CZ^ (- k) • ((H ↑) • (H ↑) • (H ↑)) • CZ • (H ↑)) • ε ≈⟨ (cright right-unit) ⟩
    HH ↑ • ((S^ k ↑) • S^ k • CZ^ (- k) • ((H ↑) • (H ↑) • (H ↑)) • CZ • (H ↑)) ≈⟨ by-assoc auto ⟩
    (HH ↑ • S^ k ↑) • (S^ k • CZ^ (- k) • ((H ↑) • (H ↑) • (H ↑)) • CZ • (H ↑)) ≈⟨ (cleft lemma-cong↑ _ _ ((Q2.lemma-Induction (M1B.trans M1B.assoc (M1B.axiom comm-HHS)) (toℕ k)))) ⟩
    (S^ k ↑ • HH ↑) • (S^ k • CZ^ (- k) • ((H ↑) • (H ↑) • (H ↑)) • CZ • (H ↑)) ≈⟨ special-assoc (□ ^ 2 • (□ • □ • □)) (□ • □ ^ 2 • □ • □) auto ⟩
    S^ k ↑ • (HH ↑ • S^ k) • CZ^ (- k) • ((H ↑) • (H ↑) • (H ↑)) • CZ • (H ↑) ≈⟨ (cright cleft word-comm 1 (toℕ k) ( ((sym (lemma-comm-S-w↑ ([ H-gen ]ʷ • [ H-gen ]ʷ)))))) ⟩
    S^ k ↑ • (S^ k • HH ↑) • CZ^ (- k) • ((H ↑) • (H ↑) • (H ↑)) • CZ • (H ↑) ≈⟨ special-assoc (□ • □ ^ 2 • □ • □) (□ ^ 2 • □ ^ 2 • □ ) auto  ⟩
    (S^ k ↑ • S^ k) • (HH ↑ • CZ^ (- k)) • ((H ↑) • (H ↑) • (H ↑)) • CZ • (H ↑) ≈⟨ (cright cleft (lemma-semi-HH↑-CZ^k' (- k))) ⟩
    (S^ k ↑ • S^ k) • (CZ^ (- - k) • HH ↑) • ((H ↑) • (H ↑) • (H ↑)) • CZ • (H ↑) ≈⟨ special-assoc (□ ^ 2 • □ ^ 2 • □) (□ ^ 3 • □ • □) auto ⟩
    (S^ k ↑ • S^ k • CZ^ (- - k)) • HH ↑ • ((H ↑) • (H ↑) • (H ↑)) • CZ • (H ↑) ≡⟨ Eq.cong (\ xx -> (S^ k ↑ • S^ k • CZ^ (xx)) • HH ↑ • ((H ↑) • (H ↑) • (H ↑)) • CZ • (H ↑)) (-‿involutive k) ⟩
    (S^ k ↑ • S^ k • CZ^ (k)) • HH ↑ • ((H ↑) • (H ↑) • (H ↑)) • CZ • (H ↑) ≈⟨ (cright rewrite-sym0 100 auto) ⟩
    (S^ k ↑ • S^ k • CZ^ (k)) • H ↑ • CZ • (H ↑) ≈⟨ special-assoc (□ ^ 3 • □ ^ 3) (□ ^ 6) auto ⟩
    S^ k ↑ • S^ k • CZ^ (k) • H ↑ • CZ • (H ↑) ≈⟨ (cleft sym (refl' (aux-↑ S (toℕ k)))) ⟩
    S ↑ ^ toℕ k • S^ k • CZ^ (k) • H ↑ • CZ • (H ↑) ≈⟨ lemma-HCZHS^k (toℕ k) ⟩
    H ↑ • CZ • H ↑ • (S ↑ ^ toℕ k) ≈⟨ (cright cright cright refl' (aux-↑ S (toℕ k))) ⟩
    H ↑ • CZ • H ↑ • (S^ k ↑) ≈⟨ (cleft rewrite-sym0 100 auto) ⟩
    (HH ↑ • ((H ↑) • (H ↑) • (H ↑))) • CZ • (H ↑) • (S^ k ↑) ≈⟨ by-assoc auto ⟩
    HH ↑ • (((H ↑) • (H ↑) • (H ↑)) • CZ • (H ↑) • (S^ k ↑)) ≈⟨ (cright sym right-unit) ⟩
    HH ↑ • (((H ↑) • (H ↑) • (H ↑)) • CZ • (H ↑) • (S^ k ↑)) • ε ∎



lemma-XCS^k-ℕ : let open PB ((₂₊ n) QRel,_===_) in ∀ k -> let -k = p-1 Nat.* k in 
  (S ^ k) ↑ • S ^ k • CZ ^ -k • XC ≈ XC • (S ^ k) ↑
lemma-XCS^k-ℕ {n} k = bbc (HH ↑) ε aux0
  where
  open PB ((₂₊ n) QRel,_===_)
  open PP ((₂₊ n) QRel,_===_)
  module M1P = PP ((₁₊ n) QRel,_===_)
  module M1B = PB ((₁₊ n) QRel,_===_)
  open SR word-setoid
  open Pattern-Assoc
  open Sym0-Rewriting (suc n)
  open Commuting-Symplectic n
  open Symplectic-GroupLike
  open Basis-Change _ ((₂₊ n) QRel,_===_) grouplike
  open import N.Lemmas-2Qupit-Sym p-2 p-prime as Q2
  open Q2.Lemmas-2Q n
  open import Algebra.Properties.Ring (+-*-ring p-2)

  -k = p-1 Nat.* k
  nnk = p-1 Nat.* -k
  aux0 : HH ↑ • ((S ^ k) ↑ • S ^ k • CZ ^ -k • XC) • ε ≈ HH ↑ • (XC • (S ^ k) ↑) • ε
  aux0 = begin
    HH ↑ • ((S ^ k) ↑ • S ^ k • CZ ^ -k • XC) • ε ≈⟨ (cright right-unit) ⟩
    HH ↑ • ((S ^ k) ↑ • S ^ k • CZ ^ -k • XC) ≈⟨ sym assoc ⟩
    (HH ↑ • (S ^ k) ↑) • S ^ k • CZ ^ -k • XC ≈⟨ (cleft lemma-cong↑ _ _ (M1P.word-comm 1 k (M1B.trans M1B.assoc (M1B.axiom comm-HHS)))) ⟩
    ((S ^ k) ↑ • HH ↑) • S ^ k • CZ ^ -k • XC ≈⟨ assoc ⟩
    (S ^ k) ↑ • HH ↑ • S ^ k • CZ ^ -k • XC ≈⟨ (cright sym assoc) ⟩
    (S ^ k) ↑ • (HH ↑ • S ^ k) • CZ ^ -k • XC ≈⟨ (cright cleft sym (lemma-comm-Sᵏ-w↑ k HH)) ⟩
    (S ^ k) ↑ • (S ^ k • HH ↑) • CZ ^ -k • XC ≈⟨ (cright assoc) ⟩
    (S ^ k) ↑ • S ^ k • HH ↑ • CZ ^ -k • XC ≈⟨ (cright cright sym assoc) ⟩
    (S ^ k) ↑ • S ^ k • (HH ↑ • CZ ^ -k) • XC ≈⟨ (cright cright cleft lemma-semi-HH↑-CZ^k'-ℕ -k) ⟩
    (S ^ k) ↑ • S ^ k • (CZ ^ nnk • HH ↑) • XC ≈⟨ (cright cright assoc) ⟩
    (S ^ k) ↑ • S ^ k • CZ ^ nnk • HH ↑ • XC ≈⟨ (cright cright cright rewrite-sym0 100 auto) ⟩
    (S ^ k) ↑ • S ^ k • CZ ^ nnk • H ↑ • CZ • H ↑ ≈⟨ (cright cright cleft aux-1) ⟩
    (S ^ k) ↑ • S ^ k • CZ ^ k • H ↑ • CZ • H ↑ ≈⟨ (cleft sym (refl' (aux-↑ S k))) ⟩
    (S ↑ ^ k) • S ^ k • CZ ^ k • H ↑ • CZ • H ↑ ≈⟨ lemma-HCZHS^k k ⟩
    H ↑ • CZ • H ↑ • (S ↑ ^ k) ≈⟨ (cright cright cright refl' (aux-↑ S k)) ⟩
    H ↑ • CZ • H ↑ • (S ^ k) ↑ ≈⟨ special-assoc (□ ^ 4) (□ ^ 3 • □) auto ⟩
    (H ↑ • CZ • H ↑) • (S ^ k) ↑ ≈⟨ (cleft rewrite-sym0 100 auto) ⟩
    (HH ↑ • XC) • (S ^ k) ↑ ≈⟨ assoc ⟩
    HH ↑ • XC • (S ^ k) ↑ ≈⟨ (cright sym right-unit) ⟩
    HH ↑ • (XC • (S ^ k) ↑) • ε ∎
    where

    aux3 :  CZ ^ (p-1 Nat.* p-1) ≈ CZ
    aux3 = begin
      CZ ^ (p-1 Nat.* p-1) ≈⟨ lemma-CZ^k-% (p-1 Nat.* p-1) ⟩
      CZ ^ ((p-1 Nat.* p-1) Nat.% p) ≡⟨ Eq.cong (CZ ^_) (Eq.sym (Eq.cong₂ (\ xx yy -> ((xx Nat.* yy) Nat.% p)) (lemma-toℕ₋₁ {p-1}) (lemma-toℕ₋₁ {p-1}))) ⟩
      CZ ^ ((toℕ (₋₁ {p-1}) Nat.* toℕ (₋₁ {p-1})) Nat.% p) ≡⟨ Eq.cong (CZ ^_) (Eq.sym (toℕ-fromℕ< (m%n<n (toℕ (₋₁ {p-1}) Nat.* toℕ (₋₁ {p-1})) p))) ⟩
      CZ ^ (toℕ (fromℕ< (m%n<n (toℕ (₋₁ {p-1}) Nat.* toℕ (₋₁ {p-1})) p))) ≈⟨ refl ⟩
      CZ ^ (toℕ (₋₁ {p-1} * ₋₁)) ≡⟨ Eq.cong (\ xx -> CZ ^ (toℕ xx)) aux-₋₁*₋₁=₁ ⟩
      CZ ^ (toℕ 1ₚ) ≈⟨ refl ⟩
      CZ ∎

    aux-1 : CZ ^ nnk ≈ CZ ^ k
    aux-1 = begin
      CZ ^ nnk ≈⟨ refl' (Eq.cong (CZ ^_) (Eq.sym (NP.*-assoc p-1 p-1 k))) ⟩
      CZ ^ (p-1 Nat.* p-1 Nat.* k) ≈⟨ sym (lemma-^^ CZ ((p-1 Nat.* p-1)) k) ⟩
      (CZ ^ (p-1 Nat.* p-1)) ^ k ≈⟨ lemma-^-cong (CZ ^ (p-1 Nat.* p-1)) CZ k aux3 ⟩
      CZ ^ k ∎





lemma-XCS^k' : let open PB ((₂₊ n) QRel,_===_) in ∀ k -> 
  S^ k ↑ • S^ k • CZ^ (- k) • H ↑ ^ 3 • CZ • H ↑ ≈ (H ↑ ^ 3 • CZ • H ↑) • S^ k ↑
lemma-XCS^k' {n} k = trans (lemma-XCS^k k) (special-assoc (□ ^ 4) (□ ^ 3 • □) auto)
  where
  open PB ((₂₊ n) QRel,_===_)
  open PP ((₂₊ n) QRel,_===_)
  open Pattern-Assoc

{-

lemma-CXS^k : let open PB ((₂₊ n) QRel,_===_) in ∀ k -> 
  S^ k • S^ k ↑ • CZ^ (- k) • H^ ₃ • CZ • H ≈ (H^ ₃ • CZ • H) • S^ k
lemma-CXS^k {n} k = {!!}
  where
  open PB ((₂₊ n) QRel,_===_)
  open PP ((₂₊ n) QRel,_===_)
  module M1P = PP ((₁₊ n) QRel,_===_)
  module M1B = PB ((₁₊ n) QRel,_===_)
  open SR word-setoid
  open Pattern-Assoc
  open Sym0-Rewriting (suc n)
  open Commuting-Symplectic n
  open Symplectic-GroupLike
  open Basis-Change _ ((₂₊ n) QRel,_===_) grouplike
  open import N.Lemmas-2Qupit-Sym p-2 p-prime as Q2
  open Q2.Lemmas-2Q n
  open import Algebra.Properties.Ring (+-*-ring p-2)

  aux1 : dual (S^ k ↑ • S^ k • CZ^ (- k) • H ↑ ^ 3 • CZ • H ↑) ≈ S^ k • S^ k ↑ • CZ^ (- k) • H ^ 3 • CZ • H
  aux1 = begin
    dual (S^ k ↑ • S^ k • CZ^ (- k) • H ↑ ^ 3 • CZ • H ↑) ≈⟨ special-assoc (□ ^ 4) (□ ^ 3 • □) auto ⟩
    dual (S^ k ↑ • S^ k • CZ^ (- k)) • H ^ 3 • CZ • H ≈⟨ (cleft cong (refl' (aux-dual-S^k↑ (toℕ k))) (cong (refl' (aux-dual-S^k (toℕ k))) (refl' (aux-dual-CZ^k (toℕ (- k)))))) ⟩
    (S^ k • S^ k ↑ • CZ^ (- k)) • H ^ 3 • CZ • H ≈⟨ sym (special-assoc (□ ^ 4) (□ ^ 3 • □) auto) ⟩
    S^ k • S^ k ↑ • CZ^ (- k) • H ^ 3 • CZ • H ∎

  aux2 : dual ((H ↑ ^ 3 • CZ • H ↑) • S^ k ↑) ≈ (H ^ 3 • CZ • H) • S^ k
  aux2 = begin
    dual ((H ↑ ^ 3 • CZ • H ↑) • S^ k ↑) ≈⟨ (cright refl' (aux-dual-S^k↑ (toℕ k))) ⟩
    (H ^ 3 • CZ • H) • S^ k ∎


lemma-CXS^k-ℕ : let open PB ((₂₊ 0) QRel,_===_) in ∀ k -> let -k = p-1 Nat.* k in 
  S ^ k • (S ^ k) ↑ • CZ ^ -k • H^ ₃ • CZ • H ≈ (H^ ₃ • CZ • H) • S ^ k
lemma-CXS^k-ℕ k = by-duality' (lemma-XCS^k-ℕ k) aux1 aux2
  where
  open PB ((₂₊ 0) QRel,_===_)
  open PP ((₂₊ 0) QRel,_===_)
  module M1P = PP ((₁₊ 0) QRel,_===_)
  module M1B = PB ((₁₊ 0) QRel,_===_)
  open SR word-setoid
  open Pattern-Assoc
  open Sym0-Rewriting (suc 0)
  open Commuting-Symplectic 0
  open Symplectic-GroupLike
  open Basis-Change _ ((₂₊ 0) QRel,_===_) grouplike
  open import N.Lemmas-2Qupit-Sym p-2 p-prime as Q2
  open Q2.Lemmas-2Q 0
  open import Algebra.Properties.Ring (+-*-ring p-2)
  -k = p-1 Nat.* k
  aux1 : dual ((S ^ k) ↑ • S ^ k • CZ ^ (-k) • H ↑ ^ 3 • CZ • H ↑) ≈ S ^ k • (S ^ k) ↑ • CZ ^ -k • H ^ 3 • CZ • H
  aux1 = begin
    dual ((S ^ k) ↑ • S ^ k • CZ ^ -k • H ↑ ^ 3 • CZ • H ↑) ≈⟨ special-assoc (□ ^ 4) (□ ^ 3 • □) auto ⟩
    dual ((S ^ k) ↑ • S ^ k • CZ ^ -k) • H ^ 3 • CZ • H ≈⟨ (cleft cong (refl' (aux-dual-S^k↑ (k))) (cong (refl' (aux-dual-S^k (k))) (refl' (aux-dual-CZ^k (-k))))) ⟩
    (S ^ k • (S ^ k) ↑ • CZ ^ -k) • H ^ 3 • CZ • H ≈⟨ sym (special-assoc (□ ^ 4) (□ ^ 3 • □) auto) ⟩
    S ^ k • (S ^ k) ↑ • CZ ^ -k • H ^ 3 • CZ • H ∎

  aux2 : dual ((H ↑ ^ 3 • CZ • H ↑) • (S ^ k) ↑) ≈ (H ^ 3 • CZ • H) • S ^ k
  aux2 = begin
    dual ((H ↑ ^ 3 • CZ • H ↑) • (S ^ k) ↑) ≈⟨ (cright refl' (aux-dual-S^k↑ (k))) ⟩
    (H ^ 3 • CZ • H) • S ^ k ∎



lemma-CXS-ℕ : let open PB ((₂₊ 0) QRel,_===_) in 
  S • S ↑ • CZ ^ p-1 • CX ≈ CX • S
lemma-CXS-ℕ = begin
  S • S ↑ • CZ ^ p-1 • CX ≈⟨ (cright cright cong (refl' (Eq.cong (CZ ^_) (Eq.sym (NP.*-identityʳ p-1)))) refl) ⟩
  S ^ k • (S ^ k) ↑ • CZ ^ -k • H^ ₃ • CZ • H ≈⟨ lemma-CXS^k-ℕ 1 ⟩
  CX • S ∎
  where
  k = 1
  open PB ((₂₊ 0) QRel,_===_)
  open PP ((₂₊ 0) QRel,_===_)
  module M1P = PP ((₁₊ 0) QRel,_===_)
  module M1B = PB ((₁₊ 0) QRel,_===_)
  open SR word-setoid
  open Pattern-Assoc
  open Sym0-Rewriting (suc 0)
  open Commuting-Symplectic 0
  open Symplectic-GroupLike
  open Basis-Change _ ((₂₊ 0) QRel,_===_) grouplike
  open import N.Lemmas-2Qupit-Sym p-2 p-prime as Q2
  open Q2.Lemmas-2Q 0
  open import Algebra.Properties.Ring (+-*-ring p-2)
  -k = p-1 Nat.* k
  aux1 : dual ((S ^ k) ↑ • S ^ k • CZ ^ (-k) • H ↑ ^ 3 • CZ • H ↑) ≈ S ^ k • (S ^ k) ↑ • CZ ^ -k • H ^ 3 • CZ • H
  aux1 = begin
    dual ((S ^ k) ↑ • S ^ k • CZ ^ -k • H ↑ ^ 3 • CZ • H ↑) ≈⟨ special-assoc (□ ^ 4) (□ ^ 3 • □) auto ⟩
    dual ((S ^ k) ↑ • S ^ k • CZ ^ -k) • H ^ 3 • CZ • H ≈⟨ (cleft cong (refl' (aux-dual-S^k↑ (k))) (cong (refl' (aux-dual-S^k (k))) (refl' (aux-dual-CZ^k (-k))))) ⟩
    (S ^ k • (S ^ k) ↑ • CZ ^ -k) • H ^ 3 • CZ • H ≈⟨ sym (special-assoc (□ ^ 4) (□ ^ 3 • □) auto) ⟩
    S ^ k • (S ^ k) ↑ • CZ ^ -k • H ^ 3 • CZ • H ∎

  aux2 : dual ((H ↑ ^ 3 • CZ • H ↑) • (S ^ k) ↑) ≈ (H ^ 3 • CZ • H) • S ^ k
  aux2 = begin
    dual ((H ↑ ^ 3 • CZ • H ↑) • (S ^ k) ↑) ≈⟨ (cright refl' (aux-dual-S^k↑ (k))) ⟩
    (H ^ 3 • CZ • H) • S ^ k ∎
-}



{-
lemma-H↑CZ↑HS↑ : let open PB ((₂₊ n) QRel,_===_) in
  S ↑ • S ↓ • CZ • H ↑ • CZ • H ↑ ≈ H ↑ • CZ • H ↑ • S ↑
lemma-H↑CZ↑HS↑ {n} = begin
  S ↑ • S ↓ • CZ • H ↑ • CZ • H ↑ ≈⟨ {!!} ⟩
  S ↑ • (CZ • H ↑ • CZ) • H ↑ • S ↓ ≈⟨ (cright (cleft axiom selinger-c10)) ⟩
  S ↑ • (S⁻¹ ↑ • H ↑ • S⁻¹ ↑ • CZ • H ↑ • S⁻¹ ↑ • S⁻¹ ↓) • H ↑ • S ↓ ≈⟨ {!!} ⟩
  (H ↑ • CZ • S⁻¹ ↑) • (H ↑ • S⁻¹ ↑ • H ↑) ≈⟨ (cright lemma-cong↑ _ _ {!!}) ⟩
  (H ↑ • CZ • S⁻¹ ↑) • (S • H • S) ↑ ≈⟨ {!!} 100 {!!} ⟩
  H ↑ • CZ • H ↑ • S ↑ ∎
  where
  open PB ((₂₊ n) QRel,_===_)
  open PP ((₂₊ n) QRel,_===_)
  open SR word-setoid


lemma-H↑CZ↑HS↑S↑ : let open PB ((₂₊ n) QRel,_===_) in
  S⁻¹ ↑ • S⁻¹ ↓ • CZ ^ 2 • H ↑ • CZ • H ↑ ≈ H ↑ • CZ • H ↑ • S⁻¹ ↑
lemma-H↑CZ↑HS↑S↑ {n} = begin
  S⁻¹ ↑ • S⁻¹ ↓ • CZ ^ 2 • H ↑ • CZ • H ↑ ≈⟨ rewrite-sym0 100 auto ⟩
  (S ↑ • S ↓ • CZ) • (S ↑ • S ↓ • CZ • H ↑ • CZ • H ↑) ≈⟨ ( cright lemma-H↑CZ↑HS↑) ⟩
  (S ↑ • S ↓ • CZ) • (H ↑ • CZ • H ↑ • S ↑) ≈⟨ by-assoc auto ⟩
  (S ↑ • S ↓ • CZ • H ↑ • CZ • H ↑) • S ↑ ≈⟨ (cleft lemma-H↑CZ↑HS↑) ⟩
  (H ↑ • CZ • H ↑ • S ↑) • S ↑ ≈⟨ by-assoc auto ⟩
  H ↑ • CZ • H ↑ • S⁻¹ ↑ ∎
  where
  open PB ((₂₊ n) QRel,_===_)
  open PP ((₂₊ n) QRel,_===_)
  open SR word-setoid
--    open Powers0-Symplectic (suc n)
  open Commuting-Symplectic (n)
  open Sym0-Rewriting (suc n)    

lemma-S↓H↓CZ↓H : let open PB ((₂₊ n) QRel,_===_) in
  S • H • CZ • H ≈ H • CZ • H • CZ • S ↑ • S
lemma-S↓H↓CZ↓H {n} = sym (begin
  H • CZ • H • CZ • S ↑ • S ≈⟨ by-assoc auto ⟩
  H • (CZ • H • CZ) • S ↑ • S ≈⟨ (cright (cleft axiom selinger-c11)) ⟩
  H • (S⁻¹ ↓ • H ↓ • S⁻¹ ↓ • CZ • H ↓ • S⁻¹ ↓ • S⁻¹ ↑) • S ↑ • S ≈⟨ general-powers0 100 auto ⟩
  (H • S⁻¹ ↓ • H ↓) • S⁻¹ ↓ • CZ • H ↓ ≈⟨ (cleft lemma-HSSH) ⟩
  (S • H • S) • S⁻¹ ↓ • CZ • H ↓ ≈⟨ ? ⟩
  S • H • CZ • H ∎)
  where
  open PB ((₂₊ n) QRel,_===_)
  open PP ((₂₊ n) QRel,_===_)
  open SR word-setoid
--    open Powers0-Symplectic (suc n)
  open Commuting-Symplectic (n)

lemma-S↓²H↓CZ↓H : let open PB ((₂₊ n) QRel,_===_) in
  S⁻¹ ↓ • H ↓ • CZ • H ↓ ≈ H ↓ • CZ • H ↓ • CZ ^ 2 • S⁻¹ ↑ • S⁻¹ ↓
lemma-S↓²H↓CZ↓H {n@(₀)} = begin
  S⁻¹ ↓ • H ↓ • CZ • H ↓ ≈⟨ assoc ⟩
  S ↓ • S ↓ • H ↓ • CZ • H ↓ ≈⟨ (cright lemma-S↓H↓CZ↓H) ⟩
  S ↓ • H ↓ • CZ • H ↓ • CZ • S ↑ • S ↓ ≈⟨ by-assoc auto ⟩
  (S ↓ • H ↓ • CZ • H ↓) • CZ • S ↑ • S ↓ ≈⟨ (cleft lemma-S↓H↓CZ↓H) ⟩
  (H ↓ • CZ • H ↓ • CZ • S ↑ • S) • CZ • S ↑ • S ↓ ≈⟨ by-assoc auto ⟩
  (H ↓ • CZ • H ↓) • CZ • S ↑  • S ↓ • CZ • S ↑ • S ↓ ≈⟨ ( general-comm auto) ⟩
  H ↓ • CZ • H ↓ • CZ ^ 2 • S⁻¹ ↑ • S⁻¹ ↓ ∎
  where
  open PB ((₂₊ n) QRel,_===_)
  open PP ((₂₊ n) QRel,_===_)
  open SR word-setoid
--    open Powers0-Symplectic (suc n)
  open Commuting-Symplectic (n)
lemma-S↓²H↓CZ↓H {n@(suc _)} = begin
  S⁻¹ ↓ • H ↓ • CZ • H ↓ ≈⟨ assoc ⟩
  S ↓ • S ↓ • H ↓ • CZ • H ↓ ≈⟨ (cright lemma-S↓H↓CZ↓H) ⟩
  S ↓ • H ↓ • CZ • H ↓ • CZ • S ↑ • S ↓ ≈⟨ by-assoc auto ⟩
  (S ↓ • H ↓ • CZ • H ↓) • CZ • S ↑ • S ↓ ≈⟨ (cleft lemma-S↓H↓CZ↓H) ⟩
  (H ↓ • CZ • H ↓ • CZ • S ↑ • S) • CZ • S ↑ • S ↓ ≈⟨ by-assoc auto ⟩
  (H ↓ • CZ • H ↓) • CZ • S ↑  • S ↓ • CZ • S ↑ • S ↓ ≈⟨ ( general-comm auto) ⟩
  H ↓ • CZ • H ↓ • CZ ^ 2 • S⁻¹ ↑ • S⁻¹ ↓ ∎
  where
  open PB ((₂₊ n) QRel,_===_)
  open PP ((₂₊ n) QRel,_===_)
  open SR word-setoid
--    open Powers0-Symplectic (suc n)
  open Commuting-Symplectic (n)

-}




{-


lemma-CZHCZCZ : let open PB ((₂₊ n) QRel,_===_) in
  CZ • H ↑ • CZ • CZ ≈ S • S ↑ • H ↑ ^ 3 • CZ • S ↑ • H ↑ • S ↑
lemma-CZHCZCZ {n@(₀)} = begin
  CZ • H ↑ • CZ • CZ ≈⟨ sym (trans assoc (cong refl assoc)) ⟩
  (CZ • H ↑ • CZ) • CZ ≈⟨ cong (axiom selinger-c10) refl ⟩
  (S⁻¹ ↑ • H ↑ • S⁻¹ ↑ • CZ • H ↑ • S⁻¹ ↑ • S⁻¹ ↓) • CZ ≈⟨ general-comm auto ⟩
  (S⁻¹ ↑ • H ↑ • S⁻¹ ↑) • (CZ • H ↑ • CZ) • S⁻¹ ↑ • S⁻¹ ↓ ≈⟨ (cright (cleft axiom selinger-c10)) ⟩
  (S⁻¹ ↑ • H ↑ • S⁻¹ ↑) • (S⁻¹ ↑ • H ↑ • S⁻¹ ↑ • CZ • H ↑ • S⁻¹ ↑ • S⁻¹ ↓) • S⁻¹ ↑ • S⁻¹ ↓ ≈⟨ rewrite-sym0 100 auto ⟩
  (S⁻¹ ↑ • H ↑ • S⁻¹ ↑) • (S⁻¹ ↑ • H ↑ • S⁻¹ ↑ • CZ • H ↑ • S ↑ • S ↓)  ≈⟨ rewrite-sym0 100 auto ⟩
  (S⁻¹ ↑ • H ↑ • S ↑ • H ↑ • S⁻¹ ↑ • CZ • H ↑ • S ↑ • S ↓)  ≈⟨ general-powers0 100 auto ⟩
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
  (S⁻¹ ↑ • H ↑ • S⁻¹ ↑ • CZ • H ↑ • S⁻¹ ↑ • S⁻¹ ↓) • CZ ≈⟨ general-comm auto ⟩
  (S⁻¹ ↑ • H ↑ • S⁻¹ ↑) • (CZ • H ↑ • CZ) • S⁻¹ ↑ • S⁻¹ ↓ ≈⟨ (cright (cleft axiom selinger-c10)) ⟩
  (S⁻¹ ↑ • H ↑ • S⁻¹ ↑) • (S⁻¹ ↑ • H ↑ • S⁻¹ ↑ • CZ • H ↑ • S⁻¹ ↑ • S⁻¹ ↓) • S⁻¹ ↑ • S⁻¹ ↓ ≈⟨ rewrite-sym0 100 auto ⟩
  (S⁻¹ ↑ • H ↑ • S⁻¹ ↑) • (S⁻¹ ↑ • H ↑ • S⁻¹ ↑ • CZ • H ↑ • S ↑ • S ↓)  ≈⟨ rewrite-sym0 100 auto ⟩
  (S⁻¹ ↑ • H ↑ • S ↑ • H ↑ • S⁻¹ ↑ • CZ • H ↑ • S ↑ • S ↓)  ≈⟨ general-powers0 100 auto ⟩
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
  CZ • (S  ^ 2 • H  • S  ^ 2 • CZ • H  • S  ^ 2 • S⁻¹ ↑) ≈⟨ general-comm auto ⟩
  S  ^ 2 • (CZ • H • CZ) • S  ^ 2 • H  • S  ^ 2 • S⁻¹ ↑ ≈⟨ (cright (cleft axiom selinger-c11)) ⟩
  S  ^ 2 • (S  ^ 2 • H  • S  ^ 2 • CZ • H  • S  ^ 2 • S⁻¹ ↑) • S  ^ 2 • H • S  ^ 2 • S⁻¹ ↑ ≈⟨ general-comm auto ⟩
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
  CZ • (S  ^ 2 • H  • S  ^ 2 • CZ • H  • S  ^ 2 • S⁻¹ ↑) ≈⟨ general-comm auto ⟩
  S  ^ 2 • (CZ • H • CZ) • S  ^ 2 • H  • S  ^ 2 • S⁻¹ ↑ ≈⟨ (cright (cleft axiom selinger-c11)) ⟩
  S  ^ 2 • (S  ^ 2 • H  • S  ^ 2 • CZ • H  • S  ^ 2 • S⁻¹ ↑) • S  ^ 2 • H • S  ^ 2 • S⁻¹ ↑ ≈⟨ general-comm auto ⟩
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
  (S  ^ 2 • H  • S  ^ 2 • CZ • H  • S  ^ 2 • S⁻¹ ↑) • CZ ≈⟨ general-comm auto ⟩
  (S  ^ 2 • H  • S  ^ 2) • (CZ • H • CZ) • S  ^ 2 • S⁻¹ ↑ ≈⟨ (cright (cleft axiom selinger-c11)) ⟩
  (S  ^ 2 • H  • S  ^ 2) • (S  ^ 2 • H • S  ^ 2 • CZ • H  • S  ^ 2 • S⁻¹ ↑) • S  ^ 2 • S⁻¹ ↑ ≈⟨ rewrite-sym0 100 auto ⟩
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
  (S  ^ 2 • H  • S  ^ 2 • CZ • H  • S  ^ 2 • S⁻¹ ↑) • CZ ≈⟨ general-comm auto ⟩
  (S  ^ 2 • H  • S  ^ 2) • (CZ • H • CZ) • S  ^ 2 • S⁻¹ ↑ ≈⟨ (cright (cleft axiom selinger-c11)) ⟩
  (S  ^ 2 • H  • S  ^ 2) • (S  ^ 2 • H • S  ^ 2 • CZ • H  • S  ^ 2 • S⁻¹ ↑) • S  ^ 2 • S⁻¹ ↑ ≈⟨ rewrite-sym0 100 auto ⟩
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

-}



{-
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
-}



lemma-CZH↓CZ^k : let open PB ((₂₊ n) QRel,_===_) in ∀ k' -> let k = suc k' in
  CZ • H ↓ • CZ ^ k ≈ (S⁻¹ ↓ • H ↓ • S⁻¹ ↓) ^ k • CZ • H ↓ • S⁻¹ ↓ ^ k • S⁻¹ ↑ ^ k
lemma-CZH↓CZ^k {n} k'@0 = let k = suc k' in begin
  CZ • H ↓ • CZ ^ k ≈⟨ axiom selinger-c11 ⟩
  S⁻¹ ↓ • H ↓ • S⁻¹ ↓ • CZ • H ↓ • S⁻¹ ↓ • S⁻¹ ↑ ≈⟨ special-assoc (□ ^ 7) (□ ^ 3 • □ ^ 4) auto ⟩
  (S⁻¹ ↓ • H ↓ • S⁻¹ ↓) ^ k • CZ • H ↓ • S⁻¹ ↓ ^ k • S⁻¹ ↑ ^ k ∎
  where
  open PB ((₂₊ n) QRel,_===_)
  open PP ((₂₊ n) QRel,_===_)
  open SR word-setoid
  open Commuting-Symplectic (n)
  open Sym0-Rewriting (suc n)
  open Pattern-Assoc
lemma-CZH↓CZ^k {n} k'@(suc k'') = begin
  CZ • H ↓ • CZ ^ k ≈⟨ special-assoc (□ ^ 4) (□ ^ 3 • □) auto ⟩
  (CZ • H ↓ • CZ) • CZ ^ k' ≈⟨ (cleft lemma-CZH↓CZ^k 0) ⟩
  ((S⁻¹ ↓ • H ↓ • S⁻¹ ↓) • CZ • H ↓ • S⁻¹ ↓ • S⁻¹ ↑) • CZ ^ k' ≈⟨ special-assoc (□ ^ 5 • □) (□ ^ 4 • □ ^ 2) auto ⟩
  ((S⁻¹ ↓ • H ↓ • S⁻¹ ↓) • CZ • H ↓ • S⁻¹ ↓) • S⁻¹ ↑ • CZ ^ k' ≈⟨ (cright cleft sym (refl' (lemma-^-↑ S p-1)) ) ⟩
  ((S⁻¹ ↓ • H ↓ • S⁻¹ ↓) • CZ • H ↓ • S⁻¹ ↓) • S ↑ ^ p-1 • CZ ^ k' ≈⟨ (cright word-comm p-1 k' (sym (axiom comm-CZ-S↑))) ⟩
  ((S⁻¹ ↓ • H ↓ • S⁻¹ ↓) • CZ • H ↓ • S⁻¹ ↓) • CZ ^ k' • S ↑ ^ p-1 ≈⟨ special-assoc (□ ^ 4 • □ ^ 2) (□ ^ 3 • □ ^ 2 • □) auto ⟩
  ((S⁻¹ ↓ • H ↓ • S⁻¹ ↓) • CZ • H ↓) • (S⁻¹ ↓ • CZ ^ k') • S ↑ ^ p-1 ≈⟨ (cright cleft (cleft lemma-cong↓-S^ (₁₊ p-2))) ⟩
  ((S⁻¹ ↓ • H ↓ • S⁻¹ ↓) • CZ • H ↓) • (S ↓ ^ p-1 • CZ ^ k') • S ↑ ^ p-1 ≈⟨ (cright cleft word-comm p-1 k' (sym (axiom comm-CZ-S↓))) ⟩
  ((S⁻¹ ↓ • H ↓ • S⁻¹ ↓) • CZ • H ↓) • (CZ ^ k' • S ↓ ^ p-1) • S ↑ ^ p-1 ≈⟨ (cright cleft (cright sym (lemma-cong↓-S^ (₁₊ p-2)))) ⟩
  ((S⁻¹ ↓ • H ↓ • S⁻¹ ↓) • CZ • H ↓) • (CZ ^ k' • S⁻¹ ↓) • S ↑ ^ p-1 ≈⟨ special-assoc (□ ^ 3 • □ ^ 2 • □ ^ 2) (□  • □ ^ 3 • □ ^ 3) auto ⟩
  (S⁻¹ ↓ • H ↓ • S⁻¹ ↓) • (CZ • H ↓ • CZ ^ k') • S⁻¹ ↓ • S ↑ ^ p-1 ≈⟨ (cright (cleft lemma-CZH↓CZ^k k'')) ⟩
  (S⁻¹ ↓ • H ↓ • S⁻¹ ↓) • ((S⁻¹ ↓ • H ↓ • S⁻¹ ↓) ^ k' • CZ • H ↓ • S⁻¹ ↓ ^ k' • S⁻¹ ↑ ^ k') • S⁻¹ ↓ • S ↑ ^ p-1 ≈⟨ special-assoc (□ • □ ^ 5 • □ ^ 2) (□ ^ 2 • □ • □ • □ • □ ^ 2 • □) auto ⟩
  ((S⁻¹ ↓ • H ↓ • S⁻¹ ↓) ^ k) • CZ • H ↓ • S⁻¹ ↓ ^ k' • (S⁻¹ ↑ ^ k' • S⁻¹ ↓) • S ↑ ^ p-1 ≈⟨ (cright cright cright cright cleft (cleft refl' (lemma-^-↑ S⁻¹ k'))) ⟩
  ((S⁻¹ ↓ • H ↓ • S⁻¹ ↓) ^ k) • CZ • H ↓ • S⁻¹ ↓ ^ k' • ((S⁻¹ ^ k') ↑ • S⁻¹ ↓) • S ↑ ^ p-1 ≈⟨ (cright cright cright cright cleft sym (lemma-comm-Sᵏ-w↑ p-1 (S⁻¹ ^ k'))) ⟩
  ((S⁻¹ ↓ • H ↓ • S⁻¹ ↓) ^ k) • CZ • H ↓ • S⁻¹ ↓ ^ k' • (S⁻¹ ↓ • (S⁻¹ ^ k') ↑) • S ↑ ^ p-1 ≈⟨ (cright cright cright cright cleft (cright sym (refl' (lemma-^-↑ S⁻¹ k')))) ⟩
  ((S⁻¹ ↓ • H ↓ • S⁻¹ ↓) ^ k) • CZ • H ↓ • S⁻¹ ↓ ^ k' • (S⁻¹ ↓ • S⁻¹ ↑ ^ k') • S ↑ ^ p-1 ≈⟨ special-assoc (□ • □ • □ • □ • □ ^ 2 • □) (□ • □ • □ • □ ^ 2 • □ ^ 2) auto ⟩
  ((S⁻¹ ↓ • H ↓ • S⁻¹ ↓) ^ k) • CZ • H ↓ • (S⁻¹ ↓ ^ k' • S⁻¹ ↓) • S⁻¹ ↑ ^ k' • S ↑ ^ p-1 ≈⟨ (cright cright cright cright (cright sym (sym (refl' (lemma-^-↑ S p-1))))) ⟩
  ((S⁻¹ ↓ • H ↓ • S⁻¹ ↓) ^ k) • CZ • H ↓ • (S⁻¹ ↓ ^ k' • S⁻¹ ↓) • S⁻¹ ↑ ^ k' • S⁻¹ ↑ ≈⟨ (cright cright cright cright aux) ⟩
  ((S⁻¹ ↓ • H ↓ • S⁻¹ ↓) ^ k) • CZ • H ↓ • (S⁻¹ ↓ ^ k' • S⁻¹ ↓) • S⁻¹ ↑ ^ k ≈⟨ (cright cright cright (cleft word-comm k' 1 refl)) ⟩
  ((S⁻¹ ↓ • H ↓ • S⁻¹ ↓) ^ k) • CZ • H ↓ • (S⁻¹ ↓ • S⁻¹ ↓ ^ k') • S⁻¹ ↑ ^ k ≈⟨ refl ⟩
  (S⁻¹ ↓ • H ↓ • S⁻¹ ↓) ^ k • CZ • H ↓ • S⁻¹ ↓ ^ k • S⁻¹ ↑ ^ k ∎
  where
  open PB ((₂₊ n) QRel,_===_)
  open PP ((₂₊ n) QRel,_===_)
  open SR word-setoid
  open Commuting-Symplectic (n)
  open Sym0-Rewriting (suc n)
  open Pattern-Assoc
  module M1P = PP ((₁₊ n) QRel,_===_)
  module M1B = PB ((₁₊ n) QRel,_===_)
  k = suc k'
  aux : S⁻¹ ↑ ^ k' • S⁻¹ ↑ ≈ S⁻¹ ↑ ^ k
  aux = begin
    S⁻¹ ↑ ^ k' • S⁻¹ ↑ ≈⟨ (cleft refl' (lemma-^-↑ S⁻¹ k')) ⟩
    (S⁻¹ ^ k') ↑ • S⁻¹ ↑ ≈⟨ lemma-cong↑ _ _ (M1P.word-comm k' p-1 (M1P.word-comm p-1 1 M1B.refl)) ⟩
    S⁻¹ ↑ • (S⁻¹ ^ k') ↑ ≈⟨ (cright sym (refl' (lemma-^-↑ S⁻¹ k'))) ⟩
    S⁻¹ ↑ • (S⁻¹ ↑ ^ k') ≈⟨ refl ⟩
    S⁻¹ ↑ ^ k  ∎





-- eqn 17 in Peter's clifford supplement.
lemma-eqn17↓ : let open PB ((₂₊ n) QRel,_===_) in
  H ↓ • CZ • S⁻¹ ↓ • H ↓ • H ↑ • CZ ≈ CZ • S ↓ • H ↓ • H ↑ • CZ • S⁻¹ ↑ • H ↑ • S⁻¹ ↑
lemma-eqn17↓ {n@0} = begin
      H ↓ • CZ • S⁻¹ ↓ • H ↓ • H ↑ • CZ ≈⟨  special-assoc (□ ^ 6) (□ ^ 4 • □ ^ 2) auto ⟩
      (H ↓ • CZ • S⁻¹ ↓ • H ↓) • H ↑ • CZ ≈⟨  (cright trans (sym left-unit) (cong (sym (axiom order-CZ)) refl)) ⟩
      (H ↓ • CZ • S⁻¹ ↓ • H ↓) • CZ ^ p • H ↑ • CZ ≈⟨  special-assoc (□ ^ 4 • □ ^ 2 • □ ^ 2) (□ ^ 5 • □ ^ 3) auto ⟩
      (H ↓ • CZ • S⁻¹ ↓ • H ↓ • CZ) • CZ ^ p-1 • H ↑ • CZ ≈⟨  (cleft by-assoc auto) ⟩
      (H ↓ • (CZ • S⁻¹ ↓) • H ↓ • CZ) • CZ ^ p-1 • H ↑ • CZ ≈⟨  (cleft (cright (cleft (cright lemma-cong↓-S^ (₁₊ p-2))))) ⟩
      (H ↓ • (CZ • S ↓ ^ p-1) • H ↓ • CZ) • CZ ^ p-1 • H ↑ • CZ ≈⟨  (cleft cright (cleft word-comm 1 p-1 (axiom comm-CZ-S↓))) ⟩
      (H ↓ • (S ↓ ^ p-1 • CZ) • H ↓ • CZ) • CZ ^ p-1 • H ↑ • CZ ≈⟨  special-assoc (((□ • □ ^ 2 • □ ^ 2) • □ ^ 3)) (□ ^ 2 • □ ^ 2 • □ ^ 2 • □ ^ 2) auto ⟩
      (H ↓ • S ↓ ^ p-1) • (CZ • H ↓) • (CZ • CZ ^ p-1) • H ↑ • CZ ≈⟨  (cright cright cleft word-comm 1 p-1 refl) ⟩
      (H ↓ • S ↓ ^ p-1) • (CZ • H ↓) • (CZ ^ p-1 • CZ) • H ↑ • CZ ≈⟨  special-assoc (□ ^ 2 • □ ^ 2 • □ ^ 2 • □ ^ 2) (□ ^ 2 • □ ^ 3 • □ ^ 3) auto ⟩
      (H ↓ • S ↓ ^ p-1) • (CZ • H ↓ • CZ ^ p-1) • CZ • H ↑ • CZ ≈⟨  (cright cleft lemma-CZH↓CZ^k p-2) ⟩
      (H ↓ • S ↓ ^ p-1) • ((S⁻¹ ↓ • H ↓ • S⁻¹ ↓) ^ p-1 • CZ • H ↓ • S⁻¹ ↓ ^ p-1 • S⁻¹ ↑ ^ p-1) • CZ • H ↑ • CZ ≈⟨ (cright cleft (cleft lemma-^-cong ((S⁻¹ ↓ • H ↓ • S⁻¹ ↓)) ((H⁻¹ ↓ • S ↓ • H ↓)) p-1 (lemma-S⁻¹HS⁻¹))) ⟩
      (H ↓ • S ↓ ^ p-1) • ((H⁻¹ ↓ • S ↓ • H ↓) ^ p-1 • CZ • H ↓ • S⁻¹ ↓ ^ p-1 • S⁻¹ ↑ ^ p-1) • CZ • H ↑ • CZ ≈⟨ (cright cleft cleft refl' auto) ⟩
      (H ↓ • S ↓ ^ p-1) • (((H⁻¹ • S • H) ^ p-1) ↓ • CZ • H ↓ • S⁻¹ ↓ ^ p-1 • S⁻¹ ↑ ^ p-1) • CZ • H ↑ • CZ ≈⟨ (cright cleft cleft (aux-[H⁻¹SH]^k p-1)) ⟩
      (H ↓ • S ↓ ^ p-1) • ((H⁻¹ • S ^ p-1 • H) ↓ • CZ • H ↓ • S⁻¹ ↓ ^ p-1 • S⁻¹ ↑ ^ p-1) • CZ • H ↑ • CZ ≈⟨ special-assoc (□ ^ 2 • (□ ^ 3 • □ ^ 4) • □ ^ 3) (□ ^ 5 • □ ^ 7) auto ⟩
      (H ↓ • S ↓ ^ p-1 • H⁻¹ ↓ • S⁻¹ ↓ • H ↓) • CZ • H ↓ • S⁻¹ ↓ ^ p-1 • S⁻¹ ↑ ^ p-1 • CZ • H ↑ • CZ ≈⟨ (cleft (cright cleft sym (lemma-cong↓-S^ (₁₊ p-2)) )) ⟩
      (H ↓ • S⁻¹ ↓ • H⁻¹ ↓ • S⁻¹ ↓ • H ↓) • CZ • H ↓ • S⁻¹ ↓ ^ p-1 • S⁻¹ ↑ ^ p-1 • CZ • H ↑ • CZ ≈⟨ (cleft aux-HS⁻¹H⁻¹S⁻¹H) ⟩
       S ↓ • CZ • H ↓ • S⁻¹ ↓ ^ p-1 • S⁻¹ ↑ ^ p-1 • CZ • H ↑ • CZ ≈⟨ (cright cright cright cong refl (cleft aux)) ⟩ -- aux-S⁻¹⁻¹
       S ↓ • CZ • H ↓ • (S⁻¹ ^ p-1) ↓ • S ↑ • CZ • H ↑ • CZ ≈⟨ (cright cright cright ( cleft aux-S⁻¹⁻¹)) ⟩
       S ↓ • CZ • H ↓ • S ↓ • S ↑ • CZ • H ↑ • CZ ≈⟨ by-assoc auto ⟩
       (S ↓ • CZ • H ↓ • S ↓ • S ↑) • CZ • H ↑ • CZ ≈⟨ (cright axiom selinger-c10) ⟩
       (S ↓ • CZ • H ↓ • S ↓ • S ↑) • S⁻¹ ↑ • H ↑ • S⁻¹ ↑ • CZ • H ↑ • S⁻¹ ↑ • S⁻¹ ↓ ≈⟨ by-assoc auto ⟩
       (S ↓ • CZ • H ↓ • S ↓) • (S ↑ • S⁻¹ ↑) • H ↑ • S⁻¹ ↑ • CZ • H ↑ • S⁻¹ ↑ • S⁻¹ ↓ ≈⟨ (cright cong (lemma-cong↑ _ _ (M1B.axiom order-S)) refl) ⟩
       (S ↓ • CZ • H ↓ • S ↓) • ε • H ↑ • S⁻¹ ↑ • CZ • H ↑ • S⁻¹ ↑ • S⁻¹ ↓ ≈⟨ (cright left-unit) ⟩
       (S ↓ • CZ • H ↓ • S ↓) • H ↑ • S⁻¹ ↑ • CZ • H ↑ • S⁻¹ ↑ • S⁻¹ ↓ ≈⟨ by-assoc auto ⟩
       (S ↓ • CZ • H ↓ • S ↓ • H ↑) • S⁻¹ ↑ • CZ • H ↑ • S⁻¹ ↑ • S⁻¹ ↓ ≈⟨ (cleft general-comm auto) ⟩
       (S ↓ • CZ • H ↓ • H ↑ • S ↓) • S⁻¹ ↑ • CZ • H ↑ • S⁻¹ ↑ • S⁻¹ ↓ ≈⟨ by-assoc auto ⟩
       (S ↓ • CZ • H ↓ • H ↑) • (S ↓ • S⁻¹ ↑) • CZ • H ↑ • S⁻¹ ↑ • S⁻¹ ↓ ≈⟨ (cright cleft lemma-comm-S-w↑ S⁻¹) ⟩
       (S ↓ • CZ • H ↓ • H ↑) • (S⁻¹ ↑ • S ↓) • CZ • H ↑ • S⁻¹ ↑ • S⁻¹ ↓ ≈⟨ special-assoc (□ ^ 4 • □ ^ 2 • □ ^ 4) (□ ^ 5 • □ ^ 3 • □ ^ 2) auto ⟩
       (S ↓ • CZ • H ↓ • H ↑ • S⁻¹ ↑) • (S ↓ • CZ • H ↑) • S⁻¹ ↑ • S⁻¹ ↓ ≈⟨ (cright cleft rewrite-sym0 100 auto) ⟩
       (S ↓ • CZ • H ↓ • H ↑ • S⁻¹ ↑) • (CZ • H ↑ • S ↓) • S⁻¹ ↑ • S⁻¹ ↓ ≈⟨ special-assoc (□ ^ 5 • □ ^ 3 • □ ^ 2) (□ ^ 7 • □ ^ 2 • □) auto ⟩
       (S ↓ • CZ • H ↓ • H ↑ • S⁻¹ ↑ • CZ • H ↑) • (S ↓ • S⁻¹ ↑) • S⁻¹ ↓ ≈⟨ (cright cleft lemma-comm-S-w↑ S⁻¹) ⟩
       (S ↓ • CZ • H ↓ • H ↑ • S⁻¹ ↑ • CZ • H ↑) • (S⁻¹ ↑ • S ↓) • S⁻¹ ↓ ≈⟨ special-assoc (□ ^ 7 • □ ^ 2 • □ ) (□ ^ 8 • □ ^ 2) auto ⟩
       (S ↓ • CZ • H ↓ • H ↑ • S⁻¹ ↑ • CZ • H ↑ • S⁻¹ ↑) • S ↓ • S⁻¹ ↓ ≈⟨ (cright (axiom order-S)) ⟩
       (S ↓ • CZ • H ↓ • H ↑ • S⁻¹ ↑ • CZ • H ↑ • S⁻¹ ↑) • ε ≈⟨ right-unit ⟩
       (S ↓ • CZ • H ↓ • H ↑ • S⁻¹ ↑ • CZ • H ↑ • S⁻¹ ↑) ≈⟨ by-assoc auto ⟩
       (S ↓ • CZ • H ↓ • H ↑) • S⁻¹ ↑ • CZ • H ↑ • S⁻¹ ↑ ≈⟨ (cleft general-comm auto) ⟩
       (CZ • S ↓ • H ↓ • H ↑) • S⁻¹ ↑ • CZ • H ↑ • S⁻¹ ↑ ≈⟨ special-assoc (□ ^ 4 • □ ^ 4) (□ ^ 4 • □ ^ 2 • □ ^ 2) auto ⟩
       (CZ • S ↓ • H ↓ • H ↑) • (S⁻¹ ↑ • CZ) • H ↑ • S⁻¹ ↑ ≈⟨ (cright cleft aux2) ⟩
       (CZ • S ↓ • H ↓ • H ↑) • (CZ • S⁻¹ ↑) • H ↑ • S⁻¹ ↑ ≈⟨ by-assoc auto ⟩
      CZ • S ↓ • H ↓ • H ↑ • CZ • S⁻¹ ↑ • H ↑ • S⁻¹ ↑ ∎
  where
  open PB ((₂₊ n) QRel,_===_)
  module M1B = PB ((₁₊ n) QRel,_===_)
  module M1P = PP ((₁₊ n) QRel,_===_)
  open PP ((₂₊ n) QRel,_===_)
  open SR word-setoid
  open Commuting-Symplectic (n)
  open Sym0-Rewriting (suc n)
  open Pattern-Assoc
  aux : S⁻¹ ↑ ^ p-1 ≈ S ↑
  aux = begin
    S⁻¹ ↑ ^ p-1 ≈⟨ refl' (lemma-^-↑ S⁻¹ p-1) ⟩
    (S⁻¹ ^ p-1) ↑ ≈⟨ lemma-cong↑ _ _ aux-S⁻¹⁻¹ ⟩
    S ↑ ∎
  aux2 : S⁻¹ ↑ • CZ ≈ CZ • S⁻¹ ↑
  aux2 = begin
    S⁻¹ ↑ • CZ ≈⟨ (cleft sym (refl' (lemma-^-↑ S p-1))) ⟩
    S ↑ ^  p-1 • CZ ≈⟨ word-comm p-1 1 (sym (axiom comm-CZ-S↑)) ⟩
    CZ • S ↑ ^  p-1 ≈⟨ (cright refl' (lemma-^-↑ S p-1)) ⟩
    CZ • S⁻¹ ↑ ∎

lemma-eqn17↓ {n@(suc _)} = begin
      H ↓ • CZ • S⁻¹ ↓ • H ↓ • H ↑ • CZ ≈⟨  special-assoc (□ ^ 6) (□ ^ 4 • □ ^ 2) auto ⟩
      (H ↓ • CZ • S⁻¹ ↓ • H ↓) • H ↑ • CZ ≈⟨  (cright trans (sym left-unit) (cong (sym (axiom order-CZ)) refl)) ⟩
      (H ↓ • CZ • S⁻¹ ↓ • H ↓) • CZ ^ p • H ↑ • CZ ≈⟨  special-assoc (□ ^ 4 • □ ^ 2 • □ ^ 2) (□ ^ 5 • □ ^ 3) auto ⟩
      (H ↓ • CZ • S⁻¹ ↓ • H ↓ • CZ) • CZ ^ p-1 • H ↑ • CZ ≈⟨  (cleft by-assoc auto) ⟩
      (H ↓ • (CZ • S⁻¹ ↓) • H ↓ • CZ) • CZ ^ p-1 • H ↑ • CZ ≈⟨  (cleft (cright (cleft (cright lemma-cong↓-S^ (₁₊ p-2))))) ⟩
      (H ↓ • (CZ • S ↓ ^ p-1) • H ↓ • CZ) • CZ ^ p-1 • H ↑ • CZ ≈⟨  (cleft cright (cleft word-comm 1 p-1 (axiom comm-CZ-S↓))) ⟩
      (H ↓ • (S ↓ ^ p-1 • CZ) • H ↓ • CZ) • CZ ^ p-1 • H ↑ • CZ ≈⟨  special-assoc (((□ • □ ^ 2 • □ ^ 2) • □ ^ 3)) (□ ^ 2 • □ ^ 2 • □ ^ 2 • □ ^ 2) auto ⟩
      (H ↓ • S ↓ ^ p-1) • (CZ • H ↓) • (CZ • CZ ^ p-1) • H ↑ • CZ ≈⟨  (cright cright cleft word-comm 1 p-1 refl) ⟩
      (H ↓ • S ↓ ^ p-1) • (CZ • H ↓) • (CZ ^ p-1 • CZ) • H ↑ • CZ ≈⟨  special-assoc (□ ^ 2 • □ ^ 2 • □ ^ 2 • □ ^ 2) (□ ^ 2 • □ ^ 3 • □ ^ 3) auto ⟩
      (H ↓ • S ↓ ^ p-1) • (CZ • H ↓ • CZ ^ p-1) • CZ • H ↑ • CZ ≈⟨  (cright cleft lemma-CZH↓CZ^k p-2) ⟩
      (H ↓ • S ↓ ^ p-1) • ((S⁻¹ ↓ • H ↓ • S⁻¹ ↓) ^ p-1 • CZ • H ↓ • S⁻¹ ↓ ^ p-1 • S⁻¹ ↑ ^ p-1) • CZ • H ↑ • CZ ≈⟨ (cright cleft (cleft lemma-^-cong ((S⁻¹ ↓ • H ↓ • S⁻¹ ↓)) ((H⁻¹ ↓ • S ↓ • H ↓)) p-1 (lemma-S⁻¹HS⁻¹))) ⟩
      (H ↓ • S ↓ ^ p-1) • ((H⁻¹ ↓ • S ↓ • H ↓) ^ p-1 • CZ • H ↓ • S⁻¹ ↓ ^ p-1 • S⁻¹ ↑ ^ p-1) • CZ • H ↑ • CZ ≈⟨ (cright cleft cleft refl' auto) ⟩
      (H ↓ • S ↓ ^ p-1) • (((H⁻¹ • S • H) ^ p-1) ↓ • CZ • H ↓ • S⁻¹ ↓ ^ p-1 • S⁻¹ ↑ ^ p-1) • CZ • H ↑ • CZ ≈⟨ (cright cleft cleft (aux-[H⁻¹SH]^k p-1)) ⟩
      (H ↓ • S ↓ ^ p-1) • ((H⁻¹ • S ^ p-1 • H) ↓ • CZ • H ↓ • S⁻¹ ↓ ^ p-1 • S⁻¹ ↑ ^ p-1) • CZ • H ↑ • CZ ≈⟨ special-assoc (□ ^ 2 • (□ ^ 3 • □ ^ 4) • □ ^ 3) (□ ^ 5 • □ ^ 7) auto ⟩
      (H ↓ • S ↓ ^ p-1 • H⁻¹ ↓ • S⁻¹ ↓ • H ↓) • CZ • H ↓ • S⁻¹ ↓ ^ p-1 • S⁻¹ ↑ ^ p-1 • CZ • H ↑ • CZ ≈⟨ (cleft (cright cleft sym (lemma-cong↓-S^ (₁₊ p-2)) )) ⟩
      (H ↓ • S⁻¹ ↓ • H⁻¹ ↓ • S⁻¹ ↓ • H ↓) • CZ • H ↓ • S⁻¹ ↓ ^ p-1 • S⁻¹ ↑ ^ p-1 • CZ • H ↑ • CZ ≈⟨ (cleft aux-HS⁻¹H⁻¹S⁻¹H) ⟩
       S ↓ • CZ • H ↓ • S⁻¹ ↓ ^ p-1 • S⁻¹ ↑ ^ p-1 • CZ • H ↑ • CZ ≈⟨ (cright cright cright cong refl (cleft aux)) ⟩ -- aux-S⁻¹⁻¹
       S ↓ • CZ • H ↓ • (S⁻¹ ^ p-1) ↓ • S ↑ • CZ • H ↑ • CZ ≈⟨ (cright cright cright ( cleft aux-S⁻¹⁻¹)) ⟩
       S ↓ • CZ • H ↓ • S ↓ • S ↑ • CZ • H ↑ • CZ ≈⟨ by-assoc auto ⟩
       (S ↓ • CZ • H ↓ • S ↓ • S ↑) • CZ • H ↑ • CZ ≈⟨ (cright axiom selinger-c10) ⟩
       (S ↓ • CZ • H ↓ • S ↓ • S ↑) • S⁻¹ ↑ • H ↑ • S⁻¹ ↑ • CZ • H ↑ • S⁻¹ ↑ • S⁻¹ ↓ ≈⟨ by-assoc auto ⟩
       (S ↓ • CZ • H ↓ • S ↓) • (S ↑ • S⁻¹ ↑) • H ↑ • S⁻¹ ↑ • CZ • H ↑ • S⁻¹ ↑ • S⁻¹ ↓ ≈⟨ (cright cong (lemma-cong↑ _ _ (M1B.axiom order-S)) refl) ⟩
       (S ↓ • CZ • H ↓ • S ↓) • ε • H ↑ • S⁻¹ ↑ • CZ • H ↑ • S⁻¹ ↑ • S⁻¹ ↓ ≈⟨ (cright left-unit) ⟩
       (S ↓ • CZ • H ↓ • S ↓) • H ↑ • S⁻¹ ↑ • CZ • H ↑ • S⁻¹ ↑ • S⁻¹ ↓ ≈⟨ by-assoc auto ⟩
       (S ↓ • CZ • H ↓ • S ↓ • H ↑) • S⁻¹ ↑ • CZ • H ↑ • S⁻¹ ↑ • S⁻¹ ↓ ≈⟨ (cleft general-comm auto) ⟩
       (S ↓ • CZ • H ↓ • H ↑ • S ↓) • S⁻¹ ↑ • CZ • H ↑ • S⁻¹ ↑ • S⁻¹ ↓ ≈⟨ by-assoc auto ⟩
       (S ↓ • CZ • H ↓ • H ↑) • (S ↓ • S⁻¹ ↑) • CZ • H ↑ • S⁻¹ ↑ • S⁻¹ ↓ ≈⟨ (cright cleft lemma-comm-S-w↑ S⁻¹) ⟩
       (S ↓ • CZ • H ↓ • H ↑) • (S⁻¹ ↑ • S ↓) • CZ • H ↑ • S⁻¹ ↑ • S⁻¹ ↓ ≈⟨ special-assoc (□ ^ 4 • □ ^ 2 • □ ^ 4) (□ ^ 5 • □ ^ 3 • □ ^ 2) auto ⟩
       (S ↓ • CZ • H ↓ • H ↑ • S⁻¹ ↑) • (S ↓ • CZ • H ↑) • S⁻¹ ↑ • S⁻¹ ↓ ≈⟨ (cright cleft rewrite-sym0 100 auto) ⟩
       (S ↓ • CZ • H ↓ • H ↑ • S⁻¹ ↑) • (CZ • H ↑ • S ↓) • S⁻¹ ↑ • S⁻¹ ↓ ≈⟨ special-assoc (□ ^ 5 • □ ^ 3 • □ ^ 2) (□ ^ 7 • □ ^ 2 • □) auto ⟩
       (S ↓ • CZ • H ↓ • H ↑ • S⁻¹ ↑ • CZ • H ↑) • (S ↓ • S⁻¹ ↑) • S⁻¹ ↓ ≈⟨ (cright cleft lemma-comm-S-w↑ S⁻¹) ⟩
       (S ↓ • CZ • H ↓ • H ↑ • S⁻¹ ↑ • CZ • H ↑) • (S⁻¹ ↑ • S ↓) • S⁻¹ ↓ ≈⟨ special-assoc (□ ^ 7 • □ ^ 2 • □ ) (□ ^ 8 • □ ^ 2) auto ⟩
       (S ↓ • CZ • H ↓ • H ↑ • S⁻¹ ↑ • CZ • H ↑ • S⁻¹ ↑) • S ↓ • S⁻¹ ↓ ≈⟨ (cright (axiom order-S)) ⟩
       (S ↓ • CZ • H ↓ • H ↑ • S⁻¹ ↑ • CZ • H ↑ • S⁻¹ ↑) • ε ≈⟨ right-unit ⟩
       (S ↓ • CZ • H ↓ • H ↑ • S⁻¹ ↑ • CZ • H ↑ • S⁻¹ ↑) ≈⟨ by-assoc auto ⟩
       (S ↓ • CZ • H ↓ • H ↑) • S⁻¹ ↑ • CZ • H ↑ • S⁻¹ ↑ ≈⟨ (cleft general-comm auto) ⟩
       (CZ • S ↓ • H ↓ • H ↑) • S⁻¹ ↑ • CZ • H ↑ • S⁻¹ ↑ ≈⟨ special-assoc (□ ^ 4 • □ ^ 4) (□ ^ 4 • □ ^ 2 • □ ^ 2) auto ⟩
       (CZ • S ↓ • H ↓ • H ↑) • (S⁻¹ ↑ • CZ) • H ↑ • S⁻¹ ↑ ≈⟨ (cright cleft aux2) ⟩
       (CZ • S ↓ • H ↓ • H ↑) • (CZ • S⁻¹ ↑) • H ↑ • S⁻¹ ↑ ≈⟨ by-assoc auto ⟩
      CZ • S ↓ • H ↓ • H ↑ • CZ • S⁻¹ ↑ • H ↑ • S⁻¹ ↑ ∎
  where
  open PB ((₂₊ n) QRel,_===_)
  module M1B = PB ((₁₊ n) QRel,_===_)
  module M1P = PP ((₁₊ n) QRel,_===_)
  open PP ((₂₊ n) QRel,_===_)
  open SR word-setoid
  open Commuting-Symplectic (n)
  open Sym0-Rewriting (suc n)
  open Pattern-Assoc
  aux : S⁻¹ ↑ ^ p-1 ≈ S ↑
  aux = begin
    S⁻¹ ↑ ^ p-1 ≈⟨ refl' (lemma-^-↑ S⁻¹ p-1) ⟩
    (S⁻¹ ^ p-1) ↑ ≈⟨ lemma-cong↑ _ _ aux-S⁻¹⁻¹ ⟩
    S ↑ ∎
  aux2 : S⁻¹ ↑ • CZ ≈ CZ • S⁻¹ ↑
  aux2 = begin
    S⁻¹ ↑ • CZ ≈⟨ (cleft sym (refl' (lemma-^-↑ S p-1))) ⟩
    S ↑ ^  p-1 • CZ ≈⟨ word-comm p-1 1 (sym (axiom comm-CZ-S↑)) ⟩
    CZ • S ↑ ^  p-1 ≈⟨ (cright refl' (lemma-^-↑ S p-1)) ⟩
    CZ • S⁻¹ ↑ ∎

lemma-S^kHCZH'-dual : let open PB ((₂₊ n) QRel,_===_) in  ∀ k' -> let k = suc k' in
  (S ^ k) ↓ • H ↓ • CZ • H ↓ ≈ H ↓ • CZ • H ↓ • CZ ^ k • (S ^ k) ↑ • (S ^ k) ↓
lemma-S^kHCZH'-dual {n} ₀ = lemma-SHCZH
  where
  open PB ((₂₊ n) QRel,_===_)
  open PP ((₂₊ n) QRel,_===_)
  open SR word-setoid
  open Commuting-Symplectic (n)
lemma-S^kHCZH'-dual {n} k'@(₁₊ l) = let k = suc k' in begin
  (S ^ k) ↓ • H ↓ • CZ • H ↓ ≈⟨ assoc ⟩
  S ↓ • (S ^ k') ↓ • H ↓ • CZ • H ↓ ≈⟨ (cright lemma-S^kHCZH'-dual l  ) ⟩
  S ↓ • H ↓ • CZ • H ↓ • CZ ^ k' • (S ^ k') ↑ • (S ^ k') ↓ ≈⟨ by-assoc auto ⟩
  (S ↓ • H ↓ • CZ • H ↓) • CZ ^ k' • (S ^ k') ↑ • (S ^ k') ↓ ≈⟨ (cleft lemma-SHCZH) ⟩
  (H ↓ • CZ • H ↓ • CZ • S ↑ • S ↓) • CZ ^ k' • (S ^ k') ↑ • (S ^ k') ↓ ≈⟨ by-assoc auto ⟩
  (H ↓ • CZ • H ↓ • CZ • S ↑) • (S ↓ • CZ ^ k') • (S ^ k') ↑ • (S ^ k') ↓ ≈⟨ (cright cleft word-comm 1 k' (sym (axiom comm-CZ-S↓))) ⟩
  (H ↓ • CZ • H ↓ • CZ • S ↑) • (CZ ^ k' • S ↓) • (S ^ k') ↑ • (S ^ k') ↓ ≈⟨ special-assoc (□ ^ 5 • □ ^ 2 • □ ^ 2) (□ ^ 4 • □ ^ 2 • □ ^ 3) auto ⟩
  (H ↓ • CZ • H ↓ • CZ) • (S ↑ • CZ ^ k') • S ↓ • (S ^ k') ↑ • (S ^ k') ↓ ≈⟨ (cright cleft word-comm 1 k' (sym (axiom comm-CZ-S↑))) ⟩
  (H ↓ • CZ • H ↓ • CZ) • (CZ ^ k' • S ↑) • S ↓ • (S ^ k') ↑ • (S ^ k') ↓ ≈⟨ trans (by-assoc auto) assoc ⟩
  (H ↓ • CZ • H ↓ • CZ • CZ ^ k') • S ↑ • (S ↓ • (S ^ k') ↑) • (S ^ k') ↓ ≈⟨ cright cright cleft (cright refl) ⟩
  (H ↓ • CZ • H ↓ • CZ • CZ ^ k') • S ↑ • (S ↓ • (S ^ k') ↑) • (S ^ k') ↓ ≈⟨ (cright cright cleft lemma-comm-S-w↑ (S ^ k')) ⟩
  (H ↓ • CZ • H ↓ • CZ • CZ ^ k') • S ↑ • ((S ^ k') ↑ • S ↓) • (S ^ k') ↓ ≈⟨ special-assoc (□ ^ 5 • □ • □ ^ 2 • □) (□ ^ 5 • □ ^ 2 • □ ^ 2) auto ⟩
  (H ↓ • CZ • H ↓ • CZ • CZ ^ k') • (S ↑ • (S ^ k') ↑) • (S • S ^ k') ↓ ≈⟨ refl ⟩
  (H ↓ • CZ • H ↓ • CZ • CZ ^ k') • (S ^ k) ↑ • (S ^ k) ↓ ≈⟨ (cright cleft sym (refl)) ⟩
  (H ↓ • CZ • H ↓ • CZ • CZ ^ k') • (S ^ k) ↑ • (S ^ k) ↓ ≈⟨ by-assoc auto ⟩
  H ↓ • CZ • H ↓ • CZ ^ k • (S ^ k) ↑ • (S ^ k) ↓ ∎
  where
  open PB ((₂₊ n) QRel,_===_)
  open PP ((₂₊ n) QRel,_===_)
  open SR word-setoid
  open Commuting-Symplectic (n)
  open Pattern-Assoc




lemma-comm-S-Ex'↑ : let open PB ((₂₊ n) QRel,_===_) in
  S ↑ • H ↑ • CZ • H ↑ • H • CZ • H ≈ H ↑ • CZ • H ↑ • H • CZ • H • S
lemma-comm-S-Ex'↑ {n@0}  = begin
  S ↑ • H ↑ • CZ • H ↑ • H • CZ • H ≈⟨ by-assoc auto ⟩
  (S ↑ • H ↑ • CZ • H ↑) • H • CZ • H ≈⟨ (cleft lemma-SHCZH') ⟩
  (H ↑ • CZ • H ↑ • CZ • S • S ↑) • H • CZ • H ≈⟨ general-comm  auto ⟩
  (H ↑ • CZ • H ↑ • CZ • S • H) • S ↑ • CZ • H ≈⟨ (cright general-comm  auto) ⟩
  (H ↑ • CZ • H ↑ • CZ • S • H) • CZ • H • S ↑ ≈⟨ by-assoc auto ⟩
  (H ↑ • CZ • H ↑ • CZ) • (S • H • CZ • H) • S ↑ ≈⟨ (cright (cleft lemma-SHCZH)) ⟩
  (H ↑ • CZ • H ↑ • CZ) • (H • CZ • H • CZ • S ↑ • S) • S ↑ ≈⟨ by-assoc auto ⟩
  (H ↑ • CZ • H ↑) • (CZ • H • CZ) • H • CZ • S ↑ • S • S ↑ ≈⟨ (cright (cleft axiom selinger-c11)) ⟩
  (H ↑ • CZ • H ↑) • (S⁻¹ • H • S⁻¹ • CZ • H • S⁻¹ • S⁻¹ ↑) • H • CZ • S ↑ • S • S ↑ ≈⟨ (cright cright general-comm auto) ⟩
  (H ↑ • CZ • H ↑) • (S⁻¹ • H • S⁻¹ • CZ • H • S⁻¹ • S⁻¹ ↑) • S ↑ • H • CZ • S • S ↑ ≈⟨ cright special-assoc (□ ^ 7 • □ ^ 5) (□ ^ 6 • □ ^ 2 • □ ^ 4) auto ⟩
  (H ↑ • CZ • H ↑) • (S⁻¹ • H • S⁻¹ • CZ • H • S⁻¹) • (S⁻¹ ↑ • S ↑) • H • CZ • S • S ↑ ≈⟨ (cright cright cleft (cleft refl)) ⟩
  (H ↑ • CZ • H ↑) • (S⁻¹ • H • S⁻¹ • CZ • H • S⁻¹) • (S⁻¹ ↑ • S ↑) • H • CZ • S • S ↑ ≈⟨ (cright cright cleft lemma-cong↑ _ _ (M1P.word-comm p-1 1 M1B.refl)) ⟩
  (H ↑ • CZ • H ↑) • (S⁻¹ • H • S⁻¹ • CZ • H • S⁻¹) • (S ↑ • S⁻¹ ↑) • H • CZ • S • S ↑ ≈⟨ (cright cright cleft lemma-cong↑ _ _ (M1B.axiom order-S)) ⟩
  (H ↑ • CZ • H ↑) • (S⁻¹ • H • S⁻¹ • CZ • H • S⁻¹) • ε • H • CZ • S • S ↑ ≈⟨ (cright cright left-unit) ⟩
  (H ↑ • CZ • H ↑) • (S⁻¹ • H • S⁻¹ • CZ • H • S⁻¹) • H • CZ • S • S ↑ ≈⟨ (cright special-assoc (□ ^ 6 • □ ^ 4) (□ ^ 4 • □ ^ 3 • □ ^ 3) auto) ⟩
  (H ↑ • CZ • H ↑) • (S⁻¹ • H • S⁻¹ • CZ) • (H • S⁻¹ • H) • CZ • S • S ↑ ≈⟨ (cright (cright cright cright sym (axiom comm-S))) ⟩
  (H ↑ • CZ • H ↑) • (S⁻¹ • H • S⁻¹ • CZ) • (H • S⁻¹ • H) • CZ • S ↑ • S ≈⟨ (cright (cright (cleft lemma-HS⁻¹H))) ⟩ 
  (H ↑ • CZ • H ↑) • (S⁻¹ • H • S⁻¹ • CZ) • (S • H • S) • CZ • S ↑ • S ≈⟨ (cright cleft cright cright (cleft refl)) ⟩
  (H ↑ • CZ • H ↑) • (S⁻¹ • H • (S) ^ p-1 • CZ) • (S • H • S) • CZ • S ↑ • S ≈⟨ (cright cleft cright cright word-comm p-1 1 (sym (axiom comm-CZ-S↓))) ⟩
  (H ↑ • CZ • H ↑) • (S⁻¹ • H • CZ • (S) ^ p-1) • (S • H • S) • CZ • S ↑ • S ≈⟨ (cright special-assoc (□ ^ 4 • □ ^ 3 • □ ^ 3) (□ ^ 3 • □ ^ 2 • □ ^ 5) auto) ⟩
  (H ↑ • CZ • H ↑) • (S⁻¹ • H • CZ) • (S ^ p-1 • S) • H • S • CZ • S ↑ • S ≈⟨ (cright cright cleft word-comm p-1 1 refl) ⟩
  (H ↑ • CZ • H ↑) • (S⁻¹ • H • CZ) • (S • S ^ p-1) • H • S • CZ • S ↑ • S ≈⟨ (cright cright cleft (cright sym (refl))) ⟩
  (H ↑ • CZ • H ↑) • (S⁻¹ • H • CZ) • (S • S⁻¹) • H • S • CZ • S ↑ • S ≈⟨ (cright cright cleft axiom order-S) ⟩
  (H ↑ • CZ • H ↑) • (S⁻¹ • H • CZ) • (ε) • H • S • CZ • S ↑ • S ≈⟨ (cright cright left-unit) ⟩
  (H ↑ • CZ • H ↑) • (S⁻¹ • H • CZ) • H • S • CZ • S ↑ • S ≈⟨ (cright special-assoc (□ ^ 3 • □ ^ 5) (□ ^ 4 • □ ^ 4) auto) ⟩
  (H ↑ • CZ • H ↑) • (S⁻¹ • H • CZ • H) • S • CZ • S ↑ • S ≈⟨ (cright cleft lemma-S^kHCZH'-dual p-2) ⟩
  (H ↑ • CZ • H ↑) • (H • CZ • H • CZ ^ p-1 • S⁻¹ ↑ • S⁻¹) • S • CZ • S ↑ • S ≈⟨ cright special-assoc (□ ^ 6 • □ ^ 4) (□ ^ 5 • □ ^ 2 • □ ^ 3) auto ⟩
  (H ↑ • CZ • H ↑) • (H • CZ • H • CZ ^ p-1 • S⁻¹ ↑) • (S⁻¹ • S) • CZ • S ↑ • S ≈⟨ (cright cright (cleft word-comm p-1 1 refl)) ⟩
  (H ↑ • CZ • H ↑) • (H • CZ • H • CZ ^ p-1 • S⁻¹ ↑) • (S • S⁻¹) • CZ • S ↑ • S ≈⟨ (cright cright cleft axiom order-S) ⟩
  (H ↑ • CZ • H ↑) • (H • CZ • H • CZ ^ p-1 • S⁻¹ ↑) • ε • CZ • S ↑ • S ≈⟨ (cright cright left-unit) ⟩
  (H ↑ • CZ • H ↑) • (H • CZ • H • CZ ^ p-1 • S⁻¹ ↑) • CZ • S ↑ • S ≈⟨ (cright cright general-comm auto) ⟩
  (H ↑ • CZ • H ↑) • (H • CZ • H • CZ ^ p-1 • S⁻¹ ↑) • S ↑ • CZ • S ≈⟨ cright special-assoc (□ ^ 5 • □ ^ 3) (□ ^ 4 • □ ^ 2 • □ ^ 2) auto ⟩
  (H ↑ • CZ • H ↑) • (H • CZ • H • CZ ^ p-1) • (S⁻¹ ↑ • S ↑) • CZ • S ≈⟨ (cright cright cleft lemma-cong↑ _ _ aux-S⁻¹↓-S↓) ⟩
  (H ↑ • CZ • H ↑) • (H • CZ • H • CZ ^ p-1) • ε • CZ • S ≈⟨ (cright cright left-unit) ⟩
  (H ↑ • CZ • H ↑) • (H • CZ • H • CZ ^ p-1) • CZ • S ≈⟨ (cright special-assoc (□ ^ 4 • □ ^ 2) (□ ^ 3 • □ ^ 2 • □) auto) ⟩
  (H ↑ • CZ • H ↑) • (H • CZ • H) • (CZ ^ p-1 • CZ) • S ≈⟨ (cright cright cleft word-comm p-1 1 refl) ⟩
  (H ↑ • CZ • H ↑) • (H • CZ • H) • (CZ • CZ ^ p-1) • S ≈⟨ (cright cright cleft axiom order-CZ) ⟩
  (H ↑ • CZ • H ↑) • (H • CZ • H) • (ε) • S ≈⟨ by-assoc auto ⟩
  H ↑ • CZ • H ↑ • H • CZ • H • S ∎
  where
  open PB ((₂₊ n) QRel,_===_)
  open PP ((₂₊ n) QRel,_===_)
  open SR word-setoid
  open Commuting-Symplectic (n)
  open Pattern-Assoc
  module M1P = PP ((₁₊ n) QRel,_===_)
  module M1B = PB ((₁₊ n) QRel,_===_)

lemma-comm-S-Ex'↑ {n@(suc _)}  = begin
  S ↑ • H ↑ • CZ • H ↑ • H • CZ • H ≈⟨ by-assoc auto ⟩
  (S ↑ • H ↑ • CZ • H ↑) • H • CZ • H ≈⟨ (cleft lemma-SHCZH') ⟩
  (H ↑ • CZ • H ↑ • CZ • S • S ↑) • H • CZ • H ≈⟨ general-comm  auto ⟩
  (H ↑ • CZ • H ↑ • CZ • S • H) • S ↑ • CZ • H ≈⟨ (cright general-comm  auto) ⟩
  (H ↑ • CZ • H ↑ • CZ • S • H) • CZ • H • S ↑ ≈⟨ by-assoc auto ⟩
  (H ↑ • CZ • H ↑ • CZ) • (S • H • CZ • H) • S ↑ ≈⟨ (cright (cleft lemma-SHCZH)) ⟩
  (H ↑ • CZ • H ↑ • CZ) • (H • CZ • H • CZ • S ↑ • S) • S ↑ ≈⟨ by-assoc auto ⟩
  (H ↑ • CZ • H ↑) • (CZ • H • CZ) • H • CZ • S ↑ • S • S ↑ ≈⟨ (cright (cleft axiom selinger-c11)) ⟩
  (H ↑ • CZ • H ↑) • (S⁻¹ • H • S⁻¹ • CZ • H • S⁻¹ • S⁻¹ ↑) • H • CZ • S ↑ • S • S ↑ ≈⟨ (cright cright general-comm auto) ⟩
  (H ↑ • CZ • H ↑) • (S⁻¹ • H • S⁻¹ • CZ • H • S⁻¹ • S⁻¹ ↑) • S ↑ • H • CZ • S • S ↑ ≈⟨ cright special-assoc (□ ^ 7 • □ ^ 5) (□ ^ 6 • □ ^ 2 • □ ^ 4) auto ⟩
  (H ↑ • CZ • H ↑) • (S⁻¹ • H • S⁻¹ • CZ • H • S⁻¹) • (S⁻¹ ↑ • S ↑) • H • CZ • S • S ↑ ≈⟨ (cright cright cleft (cleft refl)) ⟩
  (H ↑ • CZ • H ↑) • (S⁻¹ • H • S⁻¹ • CZ • H • S⁻¹) • (S⁻¹ ↑ • S ↑) • H • CZ • S • S ↑ ≈⟨ (cright cright cleft lemma-cong↑ _ _ (M1P.word-comm p-1 1 M1B.refl)) ⟩
  (H ↑ • CZ • H ↑) • (S⁻¹ • H • S⁻¹ • CZ • H • S⁻¹) • (S ↑ • S⁻¹ ↑) • H • CZ • S • S ↑ ≈⟨ (cright cright cleft lemma-cong↑ _ _ (M1B.axiom order-S)) ⟩
  (H ↑ • CZ • H ↑) • (S⁻¹ • H • S⁻¹ • CZ • H • S⁻¹) • ε • H • CZ • S • S ↑ ≈⟨ (cright cright left-unit) ⟩
  (H ↑ • CZ • H ↑) • (S⁻¹ • H • S⁻¹ • CZ • H • S⁻¹) • H • CZ • S • S ↑ ≈⟨ (cright special-assoc (□ ^ 6 • □ ^ 4) (□ ^ 4 • □ ^ 3 • □ ^ 3) auto) ⟩
  (H ↑ • CZ • H ↑) • (S⁻¹ • H • S⁻¹ • CZ) • (H • S⁻¹ • H) • CZ • S • S ↑ ≈⟨ (cright (cright cright cright sym (axiom comm-S))) ⟩
  (H ↑ • CZ • H ↑) • (S⁻¹ • H • S⁻¹ • CZ) • (H • S⁻¹ • H) • CZ • S ↑ • S ≈⟨ (cright (cright (cleft lemma-HS⁻¹H))) ⟩ 
  (H ↑ • CZ • H ↑) • (S⁻¹ • H • S⁻¹ • CZ) • (S • H • S) • CZ • S ↑ • S ≈⟨ (cright cleft cright cright (cleft refl)) ⟩
  (H ↑ • CZ • H ↑) • (S⁻¹ • H • (S) ^ p-1 • CZ) • (S • H • S) • CZ • S ↑ • S ≈⟨ (cright cleft cright cright word-comm p-1 1 (sym (axiom comm-CZ-S↓))) ⟩
  (H ↑ • CZ • H ↑) • (S⁻¹ • H • CZ • (S) ^ p-1) • (S • H • S) • CZ • S ↑ • S ≈⟨ (cright special-assoc (□ ^ 4 • □ ^ 3 • □ ^ 3) (□ ^ 3 • □ ^ 2 • □ ^ 5) auto) ⟩
  (H ↑ • CZ • H ↑) • (S⁻¹ • H • CZ) • (S ^ p-1 • S) • H • S • CZ • S ↑ • S ≈⟨ (cright cright cleft word-comm p-1 1 refl) ⟩
  (H ↑ • CZ • H ↑) • (S⁻¹ • H • CZ) • (S • S ^ p-1) • H • S • CZ • S ↑ • S ≈⟨ (cright cright cleft (cright sym (refl))) ⟩
  (H ↑ • CZ • H ↑) • (S⁻¹ • H • CZ) • (S • S⁻¹) • H • S • CZ • S ↑ • S ≈⟨ (cright cright cleft axiom order-S) ⟩
  (H ↑ • CZ • H ↑) • (S⁻¹ • H • CZ) • (ε) • H • S • CZ • S ↑ • S ≈⟨ (cright cright left-unit) ⟩
  (H ↑ • CZ • H ↑) • (S⁻¹ • H • CZ) • H • S • CZ • S ↑ • S ≈⟨ (cright special-assoc (□ ^ 3 • □ ^ 5) (□ ^ 4 • □ ^ 4) auto) ⟩
  (H ↑ • CZ • H ↑) • (S⁻¹ • H • CZ • H) • S • CZ • S ↑ • S ≈⟨ (cright cleft lemma-S^kHCZH'-dual p-2) ⟩
  (H ↑ • CZ • H ↑) • (H • CZ • H • CZ ^ p-1 • S⁻¹ ↑ • S⁻¹) • S • CZ • S ↑ • S ≈⟨ cright special-assoc (□ ^ 6 • □ ^ 4) (□ ^ 5 • □ ^ 2 • □ ^ 3) auto ⟩
  (H ↑ • CZ • H ↑) • (H • CZ • H • CZ ^ p-1 • S⁻¹ ↑) • (S⁻¹ • S) • CZ • S ↑ • S ≈⟨ (cright cright (cleft word-comm p-1 1 refl)) ⟩
  (H ↑ • CZ • H ↑) • (H • CZ • H • CZ ^ p-1 • S⁻¹ ↑) • (S • S⁻¹) • CZ • S ↑ • S ≈⟨ (cright cright cleft axiom order-S) ⟩
  (H ↑ • CZ • H ↑) • (H • CZ • H • CZ ^ p-1 • S⁻¹ ↑) • ε • CZ • S ↑ • S ≈⟨ (cright cright left-unit) ⟩
  (H ↑ • CZ • H ↑) • (H • CZ • H • CZ ^ p-1 • S⁻¹ ↑) • CZ • S ↑ • S ≈⟨ (cright cright general-comm auto) ⟩
  (H ↑ • CZ • H ↑) • (H • CZ • H • CZ ^ p-1 • S⁻¹ ↑) • S ↑ • CZ • S ≈⟨ cright special-assoc (□ ^ 5 • □ ^ 3) (□ ^ 4 • □ ^ 2 • □ ^ 2) auto ⟩
  (H ↑ • CZ • H ↑) • (H • CZ • H • CZ ^ p-1) • (S⁻¹ ↑ • S ↑) • CZ • S ≈⟨ (cright cright cleft lemma-cong↑ _ _ aux-S⁻¹↓-S↓) ⟩
  (H ↑ • CZ • H ↑) • (H • CZ • H • CZ ^ p-1) • ε • CZ • S ≈⟨ (cright cright left-unit) ⟩
  (H ↑ • CZ • H ↑) • (H • CZ • H • CZ ^ p-1) • CZ • S ≈⟨ (cright special-assoc (□ ^ 4 • □ ^ 2) (□ ^ 3 • □ ^ 2 • □) auto) ⟩
  (H ↑ • CZ • H ↑) • (H • CZ • H) • (CZ ^ p-1 • CZ) • S ≈⟨ (cright cright cleft word-comm p-1 1 refl) ⟩
  (H ↑ • CZ • H ↑) • (H • CZ • H) • (CZ • CZ ^ p-1) • S ≈⟨ (cright cright cleft axiom order-CZ) ⟩
  (H ↑ • CZ • H ↑) • (H • CZ • H) • (ε) • S ≈⟨ by-assoc auto ⟩
  H ↑ • CZ • H ↑ • H • CZ • H • S ∎
  where
  open PB ((₂₊ n) QRel,_===_)
  open PP ((₂₊ n) QRel,_===_)
  open SR word-setoid
  open Commuting-Symplectic (n)
  open Pattern-Assoc
  module M1P = PP ((₁₊ n) QRel,_===_)
  module M1B = PB ((₁₊ n) QRel,_===_)



-- eqn 16 in Peter's clifford supplement.
lemma-eqn16↑  : let open PB ((₂₊ n) QRel,_===_) in
  S ↑ • H ↑ • CZ • H ↑ • H • CZ ≈ H ↑ • CZ • H ↑ • H • CZ • S⁻¹ • H • S⁻¹
lemma-eqn16↑ {n} = bbc ε (H) aux00
  where
  open PB ((₂₊ n) QRel,_===_)
  module PB1 = PB ((₁₊ n) QRel,_===_)
  open PP ((₂₊ n) QRel,_===_)
  open SR word-setoid
  open Pattern-Assoc
  open Commuting-Symplectic (n)
  open Sym0-Rewriting (suc n)
  k = 2
  open Symplectic-GroupLike
  open Basis-Change _ ((₂₊ n) QRel,_===_) grouplike
  aux00 : ε • (S ↑  • H ↑ • CZ • H ↑ • (H ↓) • CZ) • H ↓ ≈ ε • (H ↑ • CZ • H ↑ • (H ↓) • CZ • (S⁻¹ ↓) • (H ↓) • (S⁻¹ ↓)) • H ↓
  aux00 = begin
    ε • (S ↑  • H ↑ • CZ • H ↑ • (H ↓) • CZ) • H ↓ ≈⟨ left-unit ⟩
    (S ↑  • H ↑ • CZ • H ↑ • (H ↓) • CZ) • H ↓ ≈⟨ by-assoc auto ⟩
    S ↑  • H ↑ • CZ • H ↑ • (H ↓) • CZ • H ↓ ≈⟨ lemma-comm-S-Ex'↑ ⟩
    H ↑ • CZ • H ↑ • H ↓ • CZ • H ↓ • S ↓ ≈⟨ by-assoc auto ⟩
    (H ↑ • CZ • H ↑ • H ↓ • CZ) • H ↓ • S ↓ ≈⟨ (cright (sym lemma-S⁻¹HS⁻¹H)) ⟩
    (H ↑ • CZ • H ↑ • H ↓ • CZ) • (S⁻¹ ↓) • (H ↓) • (S⁻¹ ↓) • H ↓ ≈⟨ special-assoc (□ ^ 5 • □ ^ 4) (□ ^ 8 • □) auto ⟩
    (H ↑ • CZ • H ↑ • (H ↓) • CZ • (S⁻¹ ↓) • (H ↓) • (S⁻¹ ↓)) • H ↓ ≈⟨ sym left-unit ⟩
    ε • (H ↑ • CZ • H ↑ • (H ↓) • CZ • (S⁻¹ ↓) • (H ↓) • (S⁻¹ ↓)) • H ↓ ∎



-- eqn 18 in Peter's clifford supplement.
lemma-comm-Ex-H' : let open PB ((₂₊ n) QRel,_===_) in
  H ↓ • CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑ • CZ ≈ (CZ • H • H ↑ • CZ • H • H ↑ • CZ) • H ↑
lemma-comm-Ex-H' {n} = begin
  H ↓ • CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑ • CZ ≈⟨ rewrite-sym0 100 auto ⟩
  (H ↓ • CZ • H ↓ • H ↑ • CZ • H ↓) • ε • H ↑ • CZ ≈⟨ cright cleft  sym (axiom order-CZ) ⟩
  (H ↓ • CZ • H ↓ • H ↑ • CZ • H ↓) • (CZ • CZ ^ p-1) • H ↑ • CZ ≈⟨ cright cleft word-comm 1 p-1 refl ⟩
  (H ↓ • CZ • H ↓ • H ↑ • CZ • H ↓) • (CZ ^ p-1 • CZ) • H ↑ • CZ ≈⟨ special-assoc (□ ^ 6 • □ ^ 2 • □ ^ 2) (□ ^ 4 • □ ^ 3 • □ ^ 3) auto ⟩
  (H • CZ • H ↓ • H ↑) • (CZ • H ↓ • CZ ^ p-1) • CZ • H ↑ • CZ ≈⟨ (cright (cleft lemma-CZHCZ^k p-2)) ⟩ --lemma-CZHCZ^k
  (H • CZ • H ↓ • H ↑) • ((S⁻¹ • H • S⁻¹) ^ k • CZ • H • S⁻¹ ^ k • S⁻¹ ↑ ^ k) • CZ • H ↑ • CZ ≈⟨ (cright cleft cleft lemma-[S⁻¹HS⁻¹]^k p-1) ⟩
  (H • CZ • H ↓ • H ↑) • ((H ^ 3 • S⁻¹ • H) • CZ • H • S⁻¹ ^ k • S⁻¹ ↑ ^ k) • CZ • H ↑ • CZ ≈⟨ (  special-assoc (□ ^ 4 • (□ ^ 3 • □ ^ 4) • □ ^ 3) (□ ^ 5 • □ ^ 9) auto) ⟩
  (H • CZ • H ↓ • H ↑ • H ^ 3) • S⁻¹ • H • CZ • H • S⁻¹ ^ k • S⁻¹ ↑ ^ k • CZ • H ↑ • CZ ≈⟨ (  cleft rewrite-sym0 100 auto) ⟩
  (H • CZ • H ↑) • S⁻¹ • H • CZ • H • S⁻¹ ^ k • S⁻¹ ↑ ^ k • CZ • H ↑ • CZ ≈⟨ (  by-assoc auto) ⟩
  (H • CZ) • (H ↑ • S⁻¹) • H • CZ • H • S⁻¹ ^ k • S⁻¹ ↑ ^ k • CZ • H ↑ • CZ ≈⟨ (  cright cleft word-comm 1 p-1 (axiom comm-S)) ⟩
  (H • CZ) • (S⁻¹ • H ↑) • H • CZ • H • S⁻¹ ^ k • S⁻¹ ↑ ^ k • CZ • H ↑ • CZ ≈⟨ (  special-assoc (□ ^ 2 • □ ^ 2 • □ ^ 8) (□ ^ 3 • □ ^ 2 • □ ^ 7) auto) ⟩
  (H • CZ • S⁻¹) • (H ↑ • H) • CZ • H • S⁻¹ ^ k • S⁻¹ ↑ ^ k • CZ • H ↑ • CZ ≈⟨ (  cright cleft axiom comm-H) ⟩
  (H • CZ • S⁻¹) • (H • H ↑) • CZ • H • S⁻¹ ^ k • S⁻¹ ↑ ^ k • CZ • H ↑ • CZ ≈⟨ (  special-assoc (□ ^ 3 • □ ^ 2 • □ ^ 7) (□ ^ 6 • □ ^ 6) auto) ⟩
  (H • CZ • S⁻¹ • H • H ↑ • CZ) • H • S⁻¹ ^ k • S⁻¹ ↑ ^ k • CZ • H ↑ • CZ ≈⟨ (cleft lemma-eqn17↓) ⟩
  (CZ • S • H  • H ↑ • CZ • S⁻¹ ↑ • H ↑ • S⁻¹ ↑) • H • S⁻¹ ^ k • S⁻¹ ↑ ^ k • CZ • H ↑ • CZ ≈⟨ special-assoc (□ ^ 8 • □ ^ 6) (□ ^ 5 • □ ^ 5 • □ ^ 2 • □ ^ 2) auto ⟩
  (CZ • S • H  • H ↑ • CZ) • (S⁻¹ ↑ • H ↑ • S⁻¹ ↑ • H • S⁻¹ ^ k) • (S⁻¹ ↑ ^ k • CZ) • H ↑ • CZ ≈⟨ cong (rewrite-sym0 100 auto) (cright cleft word-comm k 1 (aux0)) ⟩
  (CZ • H ↑ • S • H • CZ) • (S⁻¹ ↑ • H ↑ • S⁻¹ ↑ • H • S⁻¹ ^ k) • (CZ • S⁻¹ ↑ ^ k) • H ↑ • CZ ≈⟨ special-assoc (□ ^ 5 • □ ^ 5 • □ ^ 2 • □ ^ 2) (□ ^ 4 • □ ^ 2 • □ ^ 4 • □ ^ 2 • □ ^ 2) auto ⟩
  (CZ • H ↑ • S • H) • (CZ • S⁻¹ ↑) • (H ↑ • S⁻¹ ↑ • H • S⁻¹ ^ k) • (CZ • S⁻¹ ↑ ^ k) • H ↑ • CZ ≈⟨ (cright cleft sym aux0) ⟩
  (CZ • H ↑ • S • H) • (S⁻¹ ↑ • CZ) • (H ↑ • S⁻¹ ↑ • H • S⁻¹ ^ k) • (CZ • S⁻¹ ↑ ^ k) • H ↑ • CZ ≈⟨ special-assoc (□ ^ 4 • □ ^ 2 • □ ^ 4 • □ ^ 2 • □ ^ 2) (□ ^ 3 • □ ^ 2 • □ •  □ ^ 4 • □ ^ 2 • □ ^ 2) auto ⟩
  (CZ • H ↑ • S) • (H • S⁻¹ ↑) • CZ • (H ↑ • S⁻¹ ↑ • H • S⁻¹ ^ k) • (CZ • S⁻¹ ↑ ^ k) • H ↑ • CZ ≈⟨ (cright cleft lemma-comm-H-w↑ (S ^ ₁₊ p-2)) ⟩
  (CZ • H ↑ • S) • (S⁻¹ ↑ • H) • CZ • (H ↑ • S⁻¹ ↑ • H • S⁻¹ ^ k) • (CZ • S⁻¹ ↑ ^ k) • H ↑ • CZ ≈⟨ special-assoc (□ ^ 3 • □ ^ 2 • □ •  □ ^ 4 • □ ^ 2 • □ ^ 2) (□ ^ 2 • □ ^ 2 • □ • □ • □ ^ 4 • □ ^ 2 • □ ^ 2) auto ⟩
  (CZ • H ↑) • (S • S⁻¹ ↑) • H • CZ • (H ↑ • S⁻¹ ↑ • H • S⁻¹ ^ k) • (CZ • S⁻¹ ↑ ^ k) • H ↑ • CZ ≈⟨ (cright cleft lemma-comm-S-w↑ (S ^ ₁₊ p-2)) ⟩
  (CZ • H ↑) • (S⁻¹ ↑ • S) • H • CZ • (H ↑ • S⁻¹ ↑ • H • S⁻¹ ^ k) • (CZ • S⁻¹ ↑ ^ k) • H ↑ • CZ ≈⟨ special-assoc  (□ ^ 2 • □ ^ 2 • □ • □ • □ ^ 4 • □ ^ 2 • □ ^ 2) (□ ^ 3 • □ ^ 6 • □ ^ 2 • □ ^ 3) auto ⟩
  (CZ • H ↑ • S⁻¹ ↑) • (S • H • CZ • H ↑ • S⁻¹ ↑ • H) • (S⁻¹ ^ k • CZ) • S⁻¹ ↑ ^ k • H ↑ • CZ ≈⟨ (cright cright cleft word-comm k 1 (word-comm p-1 1 (sym (axiom comm-CZ-S↓)))) ⟩
  (CZ • H ↑ • S⁻¹ ↑) • (S • H • CZ • H ↑ • S⁻¹ ↑ • H) • (CZ • S⁻¹ ^ k) • S⁻¹ ↑ ^ k • H ↑ • CZ ≈⟨ by-assoc auto ⟩
  (CZ • H ↑ • S⁻¹ ↑) • (S • H • CZ • H ↑) • (S⁻¹ ↑ • H) • (CZ • S⁻¹ ^ k) • S⁻¹ ↑ ^ k • H ↑ • CZ ≈⟨ (cright cright cleft sym (lemma-comm-H-w↑ (S ^ ₁₊ p-2))) ⟩
  (CZ • H ↑ • S⁻¹ ↑) • (S • H • CZ • H ↑) • (H • S⁻¹ ↑) • (CZ • S⁻¹ ^ k) • S⁻¹ ↑ ^ k • H ↑ • CZ ≈⟨ special-assoc (□ ^ 3 • □ ^ 4 • □ ^ 2 • □ ^ 2 • □ ^ 3) (□ ^ 3 • □ ^ 4 • □ • □ ^ 2 • □ ^ 4) auto ⟩
  (CZ • H ↑ • S⁻¹ ↑) • (S • H • CZ • H ↑) • H • (S⁻¹ ↑ • CZ) • S⁻¹ ^ k • S⁻¹ ↑ ^ k • H ↑ • CZ ≈⟨ (cright cright cright cleft aux0) ⟩
  (CZ • H ↑ • S⁻¹ ↑) • (S • H • CZ • H ↑) • H • (CZ • S⁻¹ ↑) • S⁻¹ ^ k • S⁻¹ ↑ ^ k • H ↑ • CZ ≈⟨ special-assoc  (□ ^ 3 • □ ^ 4 • □ • □ ^ 2 • □ ^ 4) (□ ^ 3 • □ ^ 6 • □ ^ 5) auto ⟩
  (CZ • H ↑ • S⁻¹ ↑) • (S • H • CZ • H ↑ • H • CZ) • S⁻¹ ↑ • S⁻¹ ^ k • S⁻¹ ↑ ^ k • H ↑ • CZ ≈⟨ (cright cong (rewrite-sym0 100 auto) (sym assoc)) ⟩
  (CZ • H ↑ • S⁻¹ ↑) • (S • H • CZ • H • H ↑ • CZ) • (S⁻¹ ↑ • S⁻¹ ^ k) • S⁻¹ ↑ ^ k • H ↑ • CZ ≈⟨ (cright cright cleft word-comm 1 k (sym (lemma-comm-Sᵏ-w↑ (₁₊ p-2) (S ^ ₁₊ p-2)))) ⟩
  (CZ • H ↑ • S⁻¹ ↑) • (S • H • CZ • H • H ↑ • CZ) • (S⁻¹ ^ k • S⁻¹ ↑) • S⁻¹ ↑ ^ k • H ↑ • CZ ≈⟨ (cright cright special-assoc (□ ^ 2 • □ ^ 3) (□ • □ ^ 2 • □ ^ 2) auto) ⟩
  (CZ • H ↑ • S⁻¹ ↑) • (S • H • CZ • H • H ↑ • CZ) • S⁻¹ ^ k • (S⁻¹ ↑ • S⁻¹ ↑ ^ k) • H ↑ • CZ ≈⟨ refl ⟩
  (CZ • H ↑ • S⁻¹ ↑) • (S • H • CZ • H • H ↑ • CZ) • S⁻¹ ^ k • (S⁻¹ ↑ ^ p) • H ↑ • CZ ≈⟨ (cright cright cright cleft aux1) ⟩
  (CZ • H ↑ • S⁻¹ ↑) • (S • H • CZ • H • H ↑ • CZ) • S⁻¹ ^ k • (ε) • H ↑ • CZ ≈⟨ (cright cright cright left-unit) ⟩
  (CZ • H ↑ • S⁻¹ ↑) • (S • H • CZ • H • H ↑ • CZ) • S⁻¹ ^ k • H ↑ • CZ ≈⟨ (cright cright cleft aux3) ⟩
  (CZ • H ↑ • S⁻¹ ↑) • (S • H • CZ • H • H ↑ • CZ) • S • H ↑ • CZ ≈⟨ (cright (cleft lemma-eqn16)) ⟩
  (CZ • H ↑ • S⁻¹ ↑) • (H • CZ • H • H ↑ • CZ • S⁻¹ ↑ • H ↑ • S⁻¹ ↑) • S • H ↑ • CZ ≈⟨ special-assoc (□ ^ 3 • □ ^ 8 • □ ^ 3) (□ ^ 2 • □ ^ 2 • □ ^ 10) auto ⟩
  (CZ • H ↑) • (S⁻¹ ↑ • H) • CZ • H • H ↑ • CZ • S⁻¹ ↑ • H ↑ • S⁻¹ ↑ • S • H ↑ • CZ ≈⟨ (cright cleft sym (lemma-comm-H-w↑ (S ^ ₁₊ p-2))) ⟩
  (CZ • H ↑) • (H • S⁻¹ ↑) • CZ • H • H ↑ • CZ • S⁻¹ ↑ • H ↑ • S⁻¹ ↑ • S • H ↑ • CZ ≈⟨ special-assoc (□ ^ 2 • □ ^ 2 • □ ^ 10)  (□ ^ 3 • □ ^ 2 • □ ^ 9) auto ⟩
  (CZ • H ↑ • H) • (S⁻¹ ↑ • CZ) • H • H ↑ • CZ • S⁻¹ ↑ • H ↑ • S⁻¹ ↑ • S • H ↑ • CZ ≈⟨ (cright cleft aux0) ⟩
  (CZ • H ↑ • H) • (CZ • S⁻¹ ↑) • H • H ↑ • CZ • S⁻¹ ↑ • H ↑ • S⁻¹ ↑ • S • H ↑ • CZ ≈⟨ special-assoc  (□ ^ 3 • □ ^ 2 • □ ^ 9) (□ ^ 4 • □ ^ 2 • □ ^ 8) auto ⟩
  (CZ • H ↑ • H • CZ) • (S⁻¹ ↑ • H) • H ↑ • CZ • S⁻¹ ↑ • H ↑ • S⁻¹ ↑ • S • H ↑ • CZ ≈⟨ (cright cleft sym (lemma-comm-H-w↑ (S ^ ₁₊ p-2))) ⟩
  (CZ • H ↑ • H • CZ) • (H • S⁻¹ ↑) • H ↑ • CZ • S⁻¹ ↑ • H ↑ • S⁻¹ ↑ • S • H ↑ • CZ ≈⟨ special-assoc  (□ ^ 4 • □ ^ 2 • □ ^ 8) (□ ^ 5 • □ ^ 3 • □ ^ 3 • □ ^ 3) auto ⟩
  (CZ • H ↑ • H • CZ • H) • (S⁻¹ ↑ • H ↑ • CZ) • (S⁻¹ ↑ • H ↑ • S⁻¹ ↑) • S • H ↑ • CZ ≈⟨ (cright cright cleft lemma-cong↑ _ _ (lemma-[S⁻¹HS⁻¹]^k 1)) ⟩
  (CZ • H ↑ • H • CZ • H) • (S⁻¹ ↑ • H ↑ • CZ) • (H ^ 3 • S • H) ↑ • S • H ↑ • CZ ≈⟨ (cright cright cleft rewrite-sym0 100 auto) ⟩
  (CZ • H ↑ • H • CZ • H) • (S⁻¹ ↑ • H ↑ • CZ) • (H • S • H ^ 3) ↑ • S • H ↑ • CZ ≈⟨ (cright cright cright sym assoc) ⟩
  (CZ • H ↑ • H • CZ • H) • (S⁻¹ ↑ • H ↑ • CZ) • (H • S • H ^ 3) ↑ • (S • H ↑) • CZ ≈⟨ (cright cright cright cleft sym (axiom comm-S)) ⟩
  (CZ • H ↑ • H • CZ • H) • (S⁻¹ ↑ • H ↑ • CZ) • (H • S • H ^ 3) ↑ • (H ↑ • S) • CZ ≈⟨ (cright cright rewrite-sym0 100 auto) ⟩
  (CZ • H ↑ • H • CZ • H) • (S⁻¹ ↑ • H ↑ • CZ) • H ↑ • S ↑ • S • CZ ≈⟨ special-assoc (□ ^ 5 • □ ^ 3 • □ ^ 4) (□ ^ 5 • □ ^ 4 • □ ^ 3) auto ⟩
  (CZ • H ↑ • H • CZ • H) • (S⁻¹ ↑ • H ↑ • CZ • H ↑) • S ↑ • S • CZ ≈⟨ (cright cleft lemma-S^kHCZH' p-2) ⟩
  (CZ • H ↑ • H • CZ • H) • (H ↑ • CZ • H ↑ • CZ ^ k • (S ^ k) ↓ • (S ^ k) ↑) • S ↑ • S • CZ ≈⟨ special-assoc (□ ^ 5 • □ ^ 6 • □ ^ 3) (□ ^ 5 • □ ^ 5 • □ ^ 2 • □ ^ 2) auto ⟩
  (CZ • H ↑ • H • CZ • H) • (H ↑ • CZ • H ↑ • CZ ^ k • (S ^ k) ↓) • ((S ^ k) ↑ • S ↑) • S • CZ ≈⟨ (cright cright cleft lemma-cong↑ _ _ (PP1.word-comm k 1 (PB1.refl))) ⟩
  (CZ • H ↑ • H • CZ • H) • (H ↑ • CZ • H ↑ • CZ ^ k • (S ^ k) ↓) • (S ↑ • (S ^ k) ↑) • S • CZ ≈⟨ (cright cright cleft cright sym (refl' (aux-↑ S k))) ⟩
  (CZ • H ↑ • H • CZ • H) • (H ↑ • CZ • H ↑ • CZ ^ k • (S ^ k) ↓) • (S ↑ • (S ↑ ^ k)) • S • CZ ≈⟨ refl ⟩
  (CZ • H ↑ • H • CZ • H) • (H ↑ • CZ • H ↑ • CZ ^ k • (S ^ k) ↓) • ((S ↑ ^ p)) • S • CZ ≈⟨ (cright cright cleft refl' (aux-↑ S p)) ⟩
  (CZ • H ↑ • H • CZ • H) • (H ↑ • CZ • H ↑ • CZ ^ k • (S ^ k) ↓) • ((S ^ p) ↑) • S • CZ ≈⟨ (cright cright cleft lemma-cong↑ _ _ (PB1.axiom order-S)) ⟩
  (CZ • H ↑ • H • CZ • H) • (H ↑ • CZ • H ↑ • CZ ^ k • (S ^ k) ↓) • ε • S • CZ ≈⟨ (cright cright left-unit) ⟩
  (CZ • H ↑ • H • CZ • H) • (H ↑ • CZ • H ↑ • CZ ^ k • (S ^ k) ↓) • S • CZ ≈⟨ special-assoc (□ ^ 5 • □ ^ 5 • □ ^ 2) (□ ^ 5 • □ ^ 4 • □ ^ 2 • □ ) auto ⟩
  (CZ • H ↑ • H • CZ • H) • (H ↑ • CZ • H ↑ • CZ ^ k) • ((S ^ k) ↓ • S) • CZ ≈⟨ (cright cright cleft word-comm k 1 refl) ⟩
  (CZ • H ↑ • H • CZ • H) • (H ↑ • CZ • H ↑ • CZ ^ k) • (S • (S ^ k)) • CZ ≈⟨ (cright cright cleft axiom order-S) ⟩
  (CZ • H ↑ • H • CZ • H) • (H ↑ • CZ • H ↑ • CZ ^ k) • ε • CZ ≈⟨ (cright cright left-unit) ⟩
  (CZ • H ↑ • H • CZ • H) • (H ↑ • CZ • H ↑ • CZ ^ k) • CZ ≈⟨ special-assoc (□ ^ 5 • □ ^ 4 • □ ^ 1) (□ ^ 5 • □ ^ 3 • □ ^ 2 ) auto ⟩
  (CZ • H ↑ • H • CZ • H) • (H ↑ • CZ • H ↑) • CZ ^ k • CZ ≈⟨ (cright cright word-comm k 1 refl) ⟩
  (CZ • H ↑ • H • CZ • H) • (H ↑ • CZ • H ↑) • CZ • CZ ^ k ≈⟨ (cright cright axiom order-CZ) ⟩
  (CZ • H ↑ • H • CZ • H) • (H ↑ • CZ • H ↑) • ε ≈⟨ (cright right-unit) ⟩
  (CZ • H ↑ • H • CZ • H) • (H ↑ • CZ • H ↑) ≈⟨ general-comm auto ⟩
  (CZ • H • H ↑ • CZ • H • H ↑ • CZ) • H ↑ ∎
  where
  open Lemmas0 (₁₊ n)
  open Commuting-Symplectic n
  open Sym0-Rewriting (₁₊ n)
  module PP1 = PP ((₁₊ n) QRel,_===_)
  module PB1 = PB ((₁₊ n) QRel,_===_)
  open PB ((₂₊ n) QRel,_===_)
  open PP ((₂₊ n) QRel,_===_)
  open SR word-setoid
  open Pattern-Assoc
  k = p-1
  aux0 : S⁻¹ ↑ • CZ ≈ CZ • S⁻¹ ↑
  aux0 = begin
    S⁻¹ ↑ • CZ ≈⟨ (cleft refl' (Eq.sym (aux-↑ S p-1))) ⟩
    S ↑ ^ p-1 • CZ ≈⟨ word-comm p-1 1 (sym (axiom comm-CZ-S↑)) ⟩
    CZ • S ↑ ^ p-1 ≈⟨ (cright refl' ( aux-↑ S p-1)) ⟩
    CZ • S⁻¹ ↑ ∎

  aux1 : S⁻¹ ↑ ^ p ≈ ε
  aux1 = begin
    S⁻¹ ↑ ^ p ≈⟨ lemma-^-cong (S⁻¹ ↑) (S ↑ ^ p-1) p (refl' (Eq.sym (aux-↑ S p-1))) ⟩
    (S ↑ ^ p-1) ^ p ≈⟨ lemma-^^' (S ↑) p-1 p ⟩
    (S ↑ ^ p) ^ p-1 ≈⟨ lemma-^-cong (S ↑ ^ p) ((S ^ p) ↑) p-1 (refl' (aux-↑ S p)) ⟩
    (S ^ p) ↑ ^ p-1 ≈⟨ lemma-^-cong ((S  ^ p) ↑) ε  p-1 (axiom (cong↑ order-S)) ⟩
    ε ^ p-1 ≈⟨ lemma-ε^k=ε (₁₊ p-2) ⟩
    ε ∎

  aux3 : S⁻¹ ^ p-1 ≈ S
  aux3 = begin
    S⁻¹ ^ p-1 ≈⟨ lemma-^^ S p-1 p-1 ⟩
    S ^ (p-1 Nat.* p-1) ≈⟨ lemma-S^k-% (p-1 Nat.* p-1) ⟩
    S ^ ((p-1 Nat.* p-1) Nat.% p) ≡⟨ Eq.cong (S ^_) (Eq.sym (Eq.cong₂ (\ xx yy -> ((xx Nat.* yy) Nat.% p)) (lemma-toℕ₋₁ {p-1}) (lemma-toℕ₋₁ {p-1}))) ⟩
    S ^ ((toℕ (₋₁ {p-1}) Nat.* toℕ (₋₁ {p-1})) Nat.% p) ≡⟨ Eq.cong (S ^_) (Eq.sym (toℕ-fromℕ< (m%n<n (toℕ (₋₁ {p-1}) Nat.* toℕ (₋₁ {p-1})) p))) ⟩
    S ^ (toℕ (fromℕ< (m%n<n (toℕ (₋₁ {p-1}) Nat.* toℕ (₋₁ {p-1})) p))) ≈⟨ refl ⟩
    S ^ (toℕ (₋₁ {p-1} * ₋₁)) ≡⟨ Eq.cong (\ xx -> S ^ (toℕ xx)) aux-₋₁*₋₁=₁ ⟩
    S ^ (toℕ 1ₚ) ≈⟨ refl ⟩
    S ∎


open import N.Embeding-2n p-2 p-prime
open Lemmas0b hiding (lemma-comm-Ex-H')

lemma-comm-Ex-H↑'-n : let open PB ((₂₊ n) QRel,_===_) in
  H ↑ • CZ • H ↑ • H • CZ • H ↑ • H • CZ ≈ (CZ • H ↑ • H • CZ • H ↑ • H • CZ) • H
lemma-comm-Ex-H↑'-n {n} = by-emb n lemma-comm-Ex-H↑'

lemma-comm-Ex-H-n : let open PB ((₂₊ n) QRel,_===_) in
  H ↑ • Ex ≈ Ex • H
lemma-comm-Ex-H-n {n} = by-emb n lemma-comm-Ex-H




lemma-comm-Ex-CZ'-n : let open PB ((₂₊ n) QRel,_===_) in
  CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑ ≈ (H ↓ • H ↑ • CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑) • CZ
lemma-comm-Ex-CZ'-n {n} = by-emb n lemma-comm-Ex-CZ'

lemma-comm-Ex-CZ-n : let open PB ((₂₊ n) QRel,_===_) in
  CZ • Ex ≈ Ex • CZ
lemma-comm-Ex-CZ-n {n} = by-emb n lemma-comm-Ex-CZ

open import N.Lemmas-2Qupit-Sym p-2 p-prime as L2Q
open L2Q.Lemmas-2Q 0


lemma-order-Ex-n : let open PB ((₂₊ n) QRel,_===_) in
  Ex ^ 2 ≈ ε
lemma-order-Ex-n {n} = by-emb n lemma-order-Ex


open import N.Ex-Sym1 p-2 p-prime
open Lemmas0a1

open import Algebra.Properties.Ring (+-*-ring p-2)

lemma-CZCZ^aHCZ^k-n : let open PB ((₂₊ n) QRel,_===_) in ∀ a k -> (nzk : k ≢ ₀) -> 
  let
  j = suc a
  k' = toℕ k
  k* : ℤ* ₚ
  k* = (k , nzk)
  -k = - k
  k⁻¹ = ((k* ⁻¹) .proj₁)
  -k⁻¹ = - k⁻¹
  in

  CZ ^ j • H • CZ^ k ≈ (S^ -k⁻¹) ^ a • (CZ • H • CZ^ k) • (H ^ 3 • S^ k⁻¹ ^ a • H) • (S^ -k ^ a) ↑

lemma-CZCZ^aHCZ^k-n {n} a k nzk = by-emb' n (lemma-CZCZ^aHCZ^k a k nzk) aux aux2
  where
  open PB ((₂₊ n) QRel,_===_)
  open PP ((₂₊ n) QRel,_===_)
  open SR word-setoid
  open Pattern-Assoc
  j = suc a
  k' = toℕ k
  k* : ℤ* ₚ
  k* = (k , nzk)
  -k = - k
  k⁻¹ = ((k* ⁻¹) .proj₁)
  -k⁻¹ = - k⁻¹

  aux : f* n (CZ ^ j • H • CZ^ k) ≈ CZ ^ j • H • CZ^ k
  aux = cong (lemma-f* n CZ j) (cright lemma-f* n CZ (toℕ k) )
  aux2 : f* n ((S^ -k⁻¹) ^ a • (CZ • H • CZ^ k) • (H ^ 3 • S^ k⁻¹ ^ a • H) • (S^ -k ^ a) ↑) ≈ (S^ -k⁻¹) ^ a • (CZ • H • CZ^ k) • (H ^ 3 • S^ k⁻¹ ^ a • H) • (S^ -k ^ a) ↑
  aux2 = cong (lemma-f*^^ n S (toℕ (-k⁻¹)) a) (cong (cright cright lemma-f* n CZ (toℕ k)) (cong (cright cleft lemma-f*^^ n S (toℕ k⁻¹) a) (lemma-f*S^^↑ n (toℕ -k) a)))




lemma-CZCZ^aHCZ^k'-n : let open PB ((₂₊ n) QRel,_===_) in ∀ a k -> (nzk : k ≢ ₀) -> 
  let
    j = suc a
    k' = toℕ k
    k* : ℤ* ₚ
    k* = (k , nzk)
    -k = - k
    k⁻¹ = ((k* ⁻¹) .proj₁)
    -k⁻¹ = - k⁻¹
  in

  CZ ^ j • H • CZ^ k ≈ S^ -k⁻¹ ^ j • H • CZ^ k • H ^ 3 • S^ k⁻¹ ^ j • H • (S^ -k ^ j) ↑

lemma-CZCZ^aHCZ^k'-n {n} a k nzk = by-emb' n (lemma-CZCZ^aHCZ^k' a k nzk) aux aux2
  where
  open PB ((₂₊ n) QRel,_===_)
  open PP ((₂₊ n) QRel,_===_)
  open SR word-setoid
  open Pattern-Assoc
  j = suc a
  k' = toℕ k
  k* : ℤ* ₚ
  k* = (k , nzk)
  -k = - k
  k⁻¹ = ((k* ⁻¹) .proj₁)
  -k⁻¹ = - k⁻¹
  aux : f* n (CZ ^ j • H • CZ^ k) ≈ CZ ^ j • H • CZ^ k
  aux = cong (lemma-f* n CZ j) (cright lemma-f* n CZ (toℕ k) )
  aux2 : f* n (S^ -k⁻¹ ^ j • H • CZ^ k • H ^ 3 • S^ k⁻¹ ^ j • H • (S^ -k ^ j) ↑) ≈ S^ -k⁻¹ ^ j • H • CZ^ k • H ^ 3 • S^ k⁻¹ ^ j • H • (S^ -k ^ j) ↑
  aux2 = cong (lemma-f*^^ n S (toℕ -k⁻¹) j) (cright cong (lemma-f* n CZ (toℕ k)) (cright cong (lemma-f*^^ n S (toℕ k⁻¹) j) (cright lemma-f*S^^↑ n (toℕ -k) j)))


abstract

  lemma-CZCZ^aH³CZ^k'-n : let open PB ((₂₊ n) QRel,_===_) in ∀ (a : ℕ) (k : ℤ ₚ) -> (nzk : k ≢ ₀) -> 
    let
      j : ℕ
      j = suc a
      k* : ℤ* ₚ
      k* = (k , nzk)
      -k : ℤ ₚ
      -k = - k
      k⁻¹ : ℤ ₚ
      k⁻¹ = ((k* ⁻¹) .proj₁)
      -k⁻¹ : ℤ ₚ
      -k⁻¹ = - k⁻¹
    in

    CZ ^ j • H ^ 3 • CZ^ k ≈ S^ k⁻¹ ^ j • H • CZ^ -k • H • S^ -k⁻¹ ^ j • H • (S^ k ^ j) ↑

  lemma-CZCZ^aH³CZ^k'-n {n} a k nzk = by-emb' n (lemma-CZCZ^aH³CZ^k' a k nzk) aux aux2
    where
    open PB ((₂₊ n) QRel,_===_)
    open PP ((₂₊ n) QRel,_===_)
    j : ℕ
    j = suc a
    k* : ℤ* ₚ
    k* = (k , nzk)
    -k : ℤ ₚ
    -k = - k
    k⁻¹ : ℤ ₚ
    k⁻¹ = ((k* ⁻¹) .proj₁)
    -k⁻¹ : ℤ ₚ
    -k⁻¹ = - k⁻¹
    aux : f* n (CZ ^ j • H ^ 3 • CZ^ k) ≈ CZ ^ j • H ^ 3 • CZ^ k
    aux = cong (lemma-f* n CZ j) (cright lemma-f* n CZ (toℕ k) )
    aux2 : f*  n (S^ k⁻¹ ^ j • H • CZ^ -k • H • S^ -k⁻¹ ^ j • H • (S^ k ^ j) ↑) ≈ S^ k⁻¹ ^ j • H • CZ^ -k • H • S^ -k⁻¹ ^ j • H • (S^ k ^ j) ↑
    aux2 = cong (lemma-f*^^ n S (toℕ k⁻¹) j) (cright cong (lemma-f* n CZ (toℕ -k)) (cright cong (lemma-f*^^ n S (toℕ -k⁻¹) j) (cright lemma-f*S^^↑ n (toℕ k) j)))



lemma-Ex-S↑-n : let open PB ((₂₊ n) QRel,_===_) in 

  Ex • S ↑ ≈ S • Ex

lemma-Ex-S↑-n {n} = by-emb n lemma-Ex-S↑


lemma-Ex-H↑-n : let open PB ((₂₊ n) QRel,_===_) in 

  Ex • H ↑ ≈ H • Ex

lemma-Ex-H↑-n {n} = by-emb n lemma-Ex-H↑



