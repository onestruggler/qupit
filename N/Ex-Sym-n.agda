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



module N.Ex-Sym-n (p-2 : ℕ) (p-prime : Prime (2+ p-2))  where

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
open Lemmas0a
module Lemmas0b where

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

  lemma-HCZHS' : let n = 0 in let open PB ((₂₊ n) QRel,_===_) in
    S • S ↑ • CZ • H • CZ • H ≈ H • CZ • H • S
  lemma-HCZHS' = by-duality' lemma-HCZHS refl refl
    where
    open PB ((₂₊ 0) QRel,_===_)
    open PP ((₂₊ 0) QRel,_===_)
    module M1P = PP ((₁₊ 0) QRel,_===_)
    module M1B = PB ((₁₊ 0) QRel,_===_)
    open SR word-setoid
    open Pattern-Assoc
    open Commuting-Symplectic 0



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



  lemma-semi-HH↑-CZ^k' : let open PB ((₂₊ 0) QRel,_===_) in ∀ k ->

    H ↑ ^ 2 • CZ^ k ≈ CZ^ (- k) • H ↑ ^ 2

  lemma-semi-HH↑-CZ^k' k = by-duality' (lemma-semi-HH↓-CZ^k' k) (cright refl' (aux-dual-CZ^k (toℕ k))) (cleft refl' (aux-dual-CZ^k (toℕ (fromℕ< _))))
    where
    open PB ((₂₊ 0) QRel,_===_)
    open PP ((₂₊ 0) QRel,_===_)
    module M1P = PP ((₁₊ 0) QRel,_===_)
    module M1B = PB ((₁₊ 0) QRel,_===_)
    open SR word-setoid
    open Pattern-Assoc
    open Commuting-Symplectic 0
    open Symplectic-GroupLike
    open Basis-Change _ ((₂₊ 0) QRel,_===_) grouplike
    open import N.Lemmas-2Qupit-Sym p-2 p-prime as Q2
    open Q2.Lemmas-2Q 0


  lemma-semi-HH↑-CZ^k'-ℕ : let open PB ((₂₊ 0) QRel,_===_) in ∀ k -> let -k = p-1 Nat.* k in 

    H ↑ ^ 2 • CZ ^ k ≈ CZ ^ -k • H ↑ ^ 2

  lemma-semi-HH↑-CZ^k'-ℕ k = begin
    H ↑ ^ 2 • CZ ^ k ≈⟨ lemma-semi-HH↑-CZ^k′ k ⟩
    CZ^ ₋₁ ^ k • HH ↑ ≈⟨ (cleft ( lemma-^^ CZ (toℕ ₚ₋₁) k)) ⟩
    CZ ^ (toℕ ₚ₋₁ Nat.* k) • HH ↑ ≈⟨ (cleft refl' (Eq.cong (CZ ^_) (Eq.cong (Nat._* k) lemma-toℕ-ₚ₋₁))) ⟩
    CZ ^ -k • H ↑ ^ 2 ∎
    where
    -k = p-1 Nat.* k
    open PB ((₂₊ 0) QRel,_===_)
    open PP ((₂₊ 0) QRel,_===_)
    module M1P = PP ((₁₊ 0) QRel,_===_)
    module M1B = PB ((₁₊ 0) QRel,_===_)
    open SR word-setoid
    open Pattern-Assoc
    open Commuting-Symplectic 0
    open Symplectic-GroupLike
    open Basis-Change _ ((₂₊ 0) QRel,_===_) grouplike
    open import N.Lemmas-2Qupit-Sym p-2 p-prime as Q2
    open Q2.Lemmas-2Q 0


  lemma-XCS^k : let open PB ((₂₊ 0) QRel,_===_) in ∀ k -> 
    S^ k ↑ • S^ k • CZ^ (- k) • H ↑ ^ 3 • CZ • H ↑ ≈ H ↑ ^ 3 • CZ • H ↑ • S^ k ↑
  lemma-XCS^k k = bbc (HH ↑) ε aux0
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

    aux0 : HH ↑ • ((S^ k ↑) • S^ k • CZ^ (- k) • ((H ↑) • (H ↑) • (H ↑)) • CZ • (H ↑)) • ε
      ≈ HH ↑ • (((H ↑) • (H ↑) • (H ↑)) • CZ • (H ↑) • (S^ k ↑)) • ε
    aux0 = begin
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



  lemma-XCS^k-ℕ : let open PB ((₂₊ 0) QRel,_===_) in ∀ k -> let -k = p-1 Nat.* k in 
    (S ^ k) ↑ • S ^ k • CZ ^ -k • XC ≈ XC • (S ^ k) ↑
  lemma-XCS^k-ℕ k = bbc (HH ↑) ε aux0
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





  lemma-XCS^k' : let open PB ((₂₊ 0) QRel,_===_) in ∀ k -> 
    S^ k ↑ • S^ k • CZ^ (- k) • H ↑ ^ 3 • CZ • H ↑ ≈ (H ↑ ^ 3 • CZ • H ↑) • S^ k ↑
  lemma-XCS^k' k = trans (lemma-XCS^k k) (special-assoc (□ ^ 4) (□ ^ 3 • □) auto)
    where
    open PB ((₂₊ 0) QRel,_===_)
    open PP ((₂₊ 0) QRel,_===_)
    open Pattern-Assoc


  lemma-CXS^k : let open PB ((₂₊ 0) QRel,_===_) in ∀ k -> 
    S^ k • S^ k ↑ • CZ^ (- k) • H^ ₃ • CZ • H ≈ (H^ ₃ • CZ • H) • S^ k
  lemma-CXS^k k = by-duality' (lemma-XCS^k' k) aux1 aux2
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
    open Powers0-Symplectic (suc n)
    open Commuting-Symplectic (n)
    open Sym0-Rewriting (suc n)    

  lemma-S↓H↓CZ↓H : let open PB ((₂₊ n) QRel,_===_) in
    S • H • CZ • H ≈ H • CZ • H • CZ • S ↑ • S
  lemma-S↓H↓CZ↓H {n} = sym (begin
    H • CZ • H • CZ • S ↑ • S ≈⟨ by-assoc auto ⟩
    H • (CZ • H • CZ) • S ↑ • S ≈⟨ (cright (cleft axiom selinger-c11)) ⟩
    H • (S⁻¹ ↓ • H ↓ • S⁻¹ ↓ • CZ • H ↓ • S⁻¹ ↓ • S⁻¹ ↑) • S ↑ • S ≈⟨ general-powers0 100 auto ⟩
    (H • S⁻¹ ↓ • H ↓) • S⁻¹ ↓ • CZ • H ↓ ≈⟨ (cleft lemma-HSSH) ⟩
    (S • H • S) • S⁻¹ ↓ • CZ • H ↓ ≈⟨ general-powers0 100 auto ⟩
    S • H • CZ • H ∎)
    where
    open PB ((₂₊ n) QRel,_===_)
    open PP ((₂₊ n) QRel,_===_)
    open SR word-setoid
    open Powers0-Symplectic (suc n)
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
    open Powers0-Symplectic (suc n)
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
    open Powers0-Symplectic (suc n)
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



  open PB (₂ QRel,_===_)
  open PP (₂ QRel,_===_)
  open SR word-setoid
  open Pattern-Assoc
  
  lemma-eqn17↓ : H • CZ • S⁻¹ • H • H ↑ • CZ ≈ CZ • S • H • H ↑ • CZ • S⁻¹ ↑ • H ↑ • S⁻¹ ↑
  lemma-eqn17↓ = by-duality' lemma-eqn17 aux1 aux2
    where
    aux1 : dual (H ↑ • CZ • S⁻¹ ↑ • H ↑ • H • CZ) ≈ H • CZ • S⁻¹ • H • H ↑ • CZ
    aux1 = begin
      dual (H ↑ • CZ • S⁻¹ ↑ • H ↑ • H • CZ) ≈⟨ (cright cright cong (refl' (aux-dual-S^k↑ p-1)) refl) ⟩
      H • CZ • S⁻¹ • H • H ↑ • CZ ∎
    aux2 : dual (CZ • S ↑ • H ↑ • H • CZ • S⁻¹ • H • S⁻¹) ≈ CZ • S • H • H ↑ • CZ • S⁻¹ ↑ • H ↑ • S⁻¹ ↑
    aux2 = begin
      dual (CZ • S ↑ • H ↑ • H • CZ • S⁻¹ • H • S⁻¹) ≈⟨ (cright cright cright cright cright cong (refl' (aux-dual-S^k p-1)) (cright  refl' (aux-dual-S^k p-1))) ⟩
      CZ • S • H • H ↑ • CZ • S⁻¹ ↑ • H ↑ • S⁻¹ ↑ ∎


{-



  lemma-eqn16↑ : let open PB ((₂₊ n) QRel,_===_) in
    S ↑ • H ↑ • CZ • H ↑ • H • CZ ≈ H ↑ • CZ • H ↑ • H • CZ • S⁻¹ • H • S⁻¹
  lemma-eqn16↑ {n@₀} = begin
    S ↑ • H ↑ • CZ • H ↑ • H • CZ ≈⟨ general-powers0 100 auto ⟩
    S ↑ • H ↑ • (CZ • H ↑ • CZ • CZ) • CZ • H • CZ ≈⟨ (cright (cright (cleft lemma-CZHCZCZ))) ⟩
    S ↑ • H ↑ • (S • S ↑  • H ↑  ^ 3 • CZ • S ↑  • H ↑  • S ↑) • CZ • H • CZ ≈⟨ by-assoc auto ⟩
    (S ↑ • H ↑ • S • S ↑  • H ↑  ^ 3 • CZ • S ↑  • H ↑  • S ↑) • (CZ • H • CZ) ≈⟨ (cright (axiom selinger-c11)) ⟩
    (S ↑ • H ↑ • S • S ↑  • H ↑  ^ 3 • CZ • S ↑  • H ↑  • S ↑) • (S⁻¹ ↓ • H ↓ • S⁻¹ ↓ • CZ • H ↓ • S⁻¹ ↓ • S⁻¹ ↑) ≈⟨ general-comm auto ⟩
    (S ↑ • H ↑ • S ↑ • H ↑  ^ 3 • CZ • S ↑ • H ↑) • (S ^ 3 • H • S⁻¹ • CZ • H • S⁻¹ • S ↑  ^ 3) ≈⟨ general-powers0 100 auto ⟩
    (S ↑ • H ↑ • S ↑ • H ↑  ^ 3 • CZ • S ↑ • H ↑ ) • (H • S⁻¹ • CZ • H • S⁻¹) ≈⟨ by-assoc auto ⟩
    (S ↑ • H ↑ • S ↑ • H ↑) • H ↑ ^ 2 • CZ • S ↑ • H ↑  • (H • S⁻¹ • CZ • H • S⁻¹) ≈⟨ (cleft lemma-cong↑ _ _ lemma-SHSH') ⟩
    (H ↑ ^ 3 • S⁻¹ ↑) • H ↑ ^ 2 • CZ • S ↑ • H ↑  • (H • S⁻¹ • CZ • H • S⁻¹) ≈⟨ rewrite-sym0 100 auto ⟩
    H ↑ • CZ • H ↑ • (H • S⁻¹ • CZ • H • S⁻¹) ≈⟨ general-comm auto ⟩
    H ↑ • CZ • H ↑ • H • CZ • S⁻¹ • H • S⁻¹ ∎
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
    (S ↑ • H ↑ • S • S ↑  • H ↑  ^ 3 • CZ • S ↑  • H ↑  • S ↑) • (S⁻¹ ↓ • H ↓ • S⁻¹ ↓ • CZ • H ↓ • S⁻¹ ↓ • S⁻¹ ↑) ≈⟨ general-comm auto ⟩
    (S ↑ • H ↑ • S ↑ • H ↑  ^ 3 • CZ • S ↑ • H ↑) • (S ^ 3 • H • S⁻¹ • CZ • H • S⁻¹ • S ↑  ^ 3) ≈⟨ general-powers0 100 auto ⟩
    (S ↑ • H ↑ • S ↑ • H ↑  ^ 3 • CZ • S ↑ • H ↑ ) • (H • S⁻¹ • CZ • H • S⁻¹) ≈⟨ by-assoc auto ⟩
    (S ↑ • H ↑ • S ↑ • H ↑) • H ↑ ^ 2 • CZ • S ↑ • H ↑  • (H • S⁻¹ • CZ • H • S⁻¹) ≈⟨ (cleft lemma-cong↑ _ _ lemma-SHSH') ⟩
    (H ↑ ^ 3 • S⁻¹ ↑) • H ↑ ^ 2 • CZ • S ↑ • H ↑  • (H • S⁻¹ • CZ • H • S⁻¹) ≈⟨ rewrite-sym0 100 auto ⟩
    H ↑ • CZ • H ↑ • (H • S⁻¹ • CZ • H • S⁻¹) ≈⟨ general-comm auto ⟩
    H ↑ • CZ • H ↑ • H • CZ • S⁻¹ • H • S⁻¹ ∎
    where
    open PB ((₂₊ n) QRel,_===_)
    open PP ((₂₊ n) QRel,_===_)
    open SR word-setoid
    open Powers0-Symplectic (suc n)
    open Commuting-Symplectic (n)
    open Sym0-Rewriting (suc n)
-}
  open Duality
  open Lemmas0 1


  -- eqn 18 in Peter's clifford supplement.
  lemma-comm-Ex-H' : 
    H ↓ • CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑ • CZ ≈ (CZ • H • H ↑ • CZ • H • H ↑ • CZ) • H ↑
  lemma-comm-Ex-H' = begin
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
    open Commuting-Symplectic 0
    open Sym0-Rewriting ₁
    module PP1 = PP (1 QRel,_===_)
    module PB1 = PB (1 QRel,_===_)
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



  lemma-comm-Ex-H↑' :
    H ↑ • CZ • H ↑ • H • CZ • H ↑ • H • CZ ≈ (CZ • H ↑ • H • CZ • H ↑ • H • CZ) • H
  lemma-comm-Ex-H↑' = by-duality lemma-comm-Ex-H'


  lemma-comm-Ex-H : 
    H ↑ • Ex ≈ Ex • H
  lemma-comm-Ex-H = begin
    H ↑ • CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑ ≈⟨ general-comm auto ⟩
    (H ↑ • CZ • H ↑ • H • CZ • H ↑ • H • CZ) • H ↓ • H ↑ ≈⟨ (cleft lemma-comm-Ex-H↑') ⟩
    ((CZ • H ↑ • H • CZ • H ↑ • H • CZ) • H) • H ↓ • H ↑ ≈⟨ general-comm auto ⟩
    Ex • H ∎
    where
    open Commuting-Symplectic 0
    open Sym0-Rewriting 1



  lemma-comm-Ex-CZ' : 
    CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑ ≈ (H ↓ • H ↑ • CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑) • CZ
  lemma-comm-Ex-CZ' = begin
    CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑ ≈⟨ general-comm auto ⟩
    ((CZ • H ↑ • H • CZ • H ↑ • H • CZ) • H) • H ↑ ≈⟨ (cleft sym lemma-comm-Ex-H↑') ⟩
    (H ↑ • CZ • H ↑  • H • CZ • H ↑  • H • CZ) • H ↑ ≈⟨ general-comm auto ⟩
    H ↑ • (CZ • H • H ↑ • CZ • H • H ↑ • CZ) • H ↑ ≈⟨ (cright sym lemma-comm-Ex-H') ⟩
    H ↑ • H ↓ • CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑ • CZ ≈⟨ general-comm auto ⟩
    (H ↓ • H ↑ • CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑) • CZ ∎
    where
    open Commuting-Symplectic 0
    open Sym0-Rewriting 1


  lemma-comm-Ex-CZ : 
    CZ • Ex ≈ Ex • CZ
  lemma-comm-Ex-CZ = begin
    CZ • Ex ≈⟨ refl ⟩
    CZ • CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑ ≈⟨ (cright lemma-comm-Ex-CZ') ⟩
    CZ • (H ↓ • H ↑ • CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑) • CZ ≈⟨ sym assoc ⟩
    Ex • CZ ∎
    where
    open Commuting-Symplectic 0
    open Sym0-Rewriting 1

  open import N.Lemmas-2Qupit-Sym p-2 p-prime as L2Q
  open L2Q.Lemmas-2Q 0


  lemma-order-Ex : 
    Ex ^ 2 ≈ ε
  lemma-order-Ex = begin
    Ex ^ 2 ≈⟨ refl ⟩
    (CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑) • (CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑) ≈⟨ (cright lemma-comm-Ex-CZ') ⟩
    (CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑) • ((H ↓ • H ↑ • CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑) • CZ) ≈⟨ general-comm auto ⟩
    ((CZ • H ↑ • H • CZ • H ↑ • H • CZ) • H) • H ↑ ^ 2 • (H ↓ • CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑ • CZ) ≈⟨ cong (sym lemma-comm-Ex-H↑') (cong refl lemma-comm-Ex-H') ⟩
    (H ↑  • CZ • H ↑  • H • CZ • H ↑  • H • CZ) • H ↑ ^ 2 • ((CZ • H • H ↑ • CZ • H • H ↑ • CZ) • H ↑) ≈⟨ general-comm auto ⟩
    (H ↑  • CZ • H ↑  • H • CZ • H ↑  • H) • (CZ • H ↑ ^ 2) • ((CZ • H ↑ • H • CZ • H • H ↑ • CZ) • H ↑) ≈⟨ (cright (cleft lemma-semi-CZ-HH↑)) ⟩
    (H ↑  • CZ • H ↑  • H • CZ • H ↑  • H) • (H ↑ ^ 2 • CZ^ ₋₁) • ((CZ • H ↑ • H • CZ • H • H ↑ • CZ) • H ↑) ≈⟨ cright cleft cright refl' (Eq.cong (CZ ^_) (lemma-toℕ₋₁ {p-1})) ⟩
    (H ↑  • CZ • H ↑  • H • CZ • H ↑  • H) • (H ↑ ^ 2 • CZ ^ p-1) • ((CZ • H ↑ • H • CZ • H • H ↑ • CZ) • H ↑) ≈⟨ special-assoc (□ ^ 7 • □ ^ 2 • (□ ^ 7 • □)) (□ ^ 7 • □ • □ ^ 2 • □ ^ 7) auto ⟩
    (H ↑  • CZ • H ↑  • H • CZ • H ↑  • H) • (H ↑ ^ 2) • (CZ ^ p-1 • CZ) • H ↑ • H • CZ • H • H ↑ • CZ • H ↑ ≈⟨ (cright cright cleft word-comm p-1 1 refl) ⟩
    (H ↑  • CZ • H ↑  • H • CZ • H ↑  • H) • (H ↑ ^ 2) • (CZ • CZ ^ p-1) • H ↑ • H • CZ • H • H ↑ • CZ • H ↑ ≈⟨ (cright cright trans (cong (axiom order-CZ) refl) left-unit) ⟩
    (H ↑  • CZ • H ↑  • H • CZ • H ↑  • H) • (H ↑ ^ 2) • H ↑ • H • CZ • H • H ↑ • CZ • H ↑ ≈⟨ general-comm auto ⟩
    (H ↑  • CZ • H ↑  • H • CZ • H ^ 2) • (H ↑ ^ 4) • CZ • H • H ↑ • CZ • H ↑ ≈⟨ rewrite-sym0 100 auto ⟩
    (H ↑  • CZ • H ↑  • H) • (CZ • H ^ 2) • CZ • H • H ↑ • CZ • H ↑ ≈⟨ (cright cleft lemma-semi-CZ-HH↓) ⟩
    (H ↑  • CZ • H ↑  • H) • (H ^ 2 • (CZ^ ₋₁)) • CZ • H • H ↑ • CZ • H ↑ ≈⟨ (cright cleft cright refl' (Eq.cong (CZ ^_) (lemma-toℕ₋₁ {p-1}))) ⟩
    (H ↑  • CZ • H ↑  • H) • (H ^ 2 • CZ ^ p-1) • CZ • H • H ↑ • CZ • H ↑ ≈⟨ special-assoc (□ ^ 4 • □ ^ 2 • □ ^ 5) (□ ^ 4 • □ • □ ^ 2 • □ ^ 4) auto ⟩
    (H ↑  • CZ • H ↑  • H) • H ^ 2 • (CZ ^ p-1 • CZ) • H • H ↑ • CZ • H ↑ ≈⟨ (cright cright cleft word-comm p-1 1 refl) ⟩
    (H ↑  • CZ • H ↑  • H) • H ^ 2 • (CZ • CZ ^ p-1) • H • H ↑ • CZ • H ↑ ≈⟨ (cright cright trans (cong (axiom order-CZ) refl) left-unit) ⟩
    (H ↑  • CZ • H ↑  • H) • H ^ 2 • H • H ↑ • CZ • H ↑ ≈⟨ rewrite-sym0 100 auto ⟩
    H ↑ • (CZ • H ↑ ^ 2) • CZ • H ↑ ≈⟨ (cright cleft lemma-semi-CZ-HH↑) ⟩
    H ↑ • (H ↑ ^ 2 • CZ^ ₋₁) • CZ • H ↑ ≈⟨ special-assoc (□ • □ ^ 2 • □ ^ 2) (□ • □ • □ ^ 2 • □) auto ⟩
    H ↑ • H ↑ ^ 2 • (CZ^ ₋₁ • CZ) • H ↑ ≈⟨ (cright cright cleft cleft refl' (Eq.cong (CZ ^_) (lemma-toℕ₋₁ {p-1})))⟩
    H ↑ • H ↑ ^ 2 • (CZ ^ p-1 • CZ) • H ↑ ≈⟨ (cright cright cleft word-comm p-1 1 refl) ⟩
    H ↑ • H ↑ ^ 2 • (CZ • CZ ^ p-1) • H ↑ ≈⟨ (cright cright trans (cong (axiom order-CZ) refl) left-unit) ⟩
    H ↑ • H ↑ ^ 2 • H ↑ ≈⟨ rewrite-sym0 100 auto ⟩
    ε ∎
    where
    open Commuting-Symplectic 0
    open Sym0-Rewriting 1

  open import N.Ex-Sym1 p-2 p-prime
  open Lemmas0a1

  open import Algebra.Properties.Ring (+-*-ring p-2)

  lemma-CZCZ^aHCZ^k : ∀ a k -> (nzk : k ≢ ₀) -> 
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
    
  lemma-CZCZ^aHCZ^k (a@0) k nzk = begin
    CZ ^ j • H • CZ^ k ≈⟨ sym (trans left-unit right-unit) ⟩
    ε • (CZ • H • CZ^ k) • ε ≈⟨ (cright cright rewrite-sym0 100 auto) ⟩
    ε • (CZ • H • CZ^ k) • (H ^ 3 • ε • H) • ε ≈⟨ refl ⟩
    (S^ -k⁻¹) ^ a • (CZ • H • CZ^ k) • (H ^ 3 • S^ k⁻¹ ^ a • H) • (S^ -k ^ a) ↑ ∎
    where
    open Sym0-Rewriting 1

    j = suc a
    k' = toℕ k
    k* : ℤ* ₚ
    k* = (k , nzk)
    -k = - k
    k⁻¹ = ((k* ⁻¹) .proj₁)
    -k⁻¹ = - k⁻¹

  lemma-CZCZ^aHCZ^k (a@(suc a-1)) k nzk = begin
    CZ ^ j • H • CZ^ k ≈⟨ refl ⟩
    (CZ • CZ ^ a) • H • CZ^ k ≈⟨ (cleft word-comm 1 a refl) ⟩
    (CZ ^ a • CZ) • H • CZ^ k ≈⟨ assoc ⟩
    CZ ^ a • CZ • H • CZ ^ k' ≈⟨ (cright lemma-CZHCZ^-k k) ⟩
    CZ ^ a • (S⁻¹ • H • S⁻¹) ^ k' • CZ • H • S⁻¹ ^ k' • S⁻¹ ↑ ^ k' ≈⟨ (cright cleft lemma-[S⁻¹HS⁻¹]^k k') ⟩
    CZ ^ a • (H ^ 3 • S ^ k' • H) • CZ • H • S⁻¹ ^ k' • S⁻¹ ↑ ^ k' ≈⟨ (cright cleft refl) ⟩
    CZ ^ a • (H ^ 3 • S^ (k* .proj₁) • H) • CZ • H • S⁻¹ ^ k' • S⁻¹ ↑ ^ k' ≈⟨ (cright cleft lemma-Euler' k*) ⟩
    CZ ^ a • ((S^ -k⁻¹ • H • S^ -k) • M k* ) • CZ • H • S⁻¹ ^ k' • S⁻¹ ↑ ^ k' ≈⟨ special-assoc (□ • (□ ^ 3 • □) • □ ^ 4) (□ ^ 2 • □ ^ 2 • □ ^ 2 • □ ^ 3) auto ⟩
    (CZ ^ a • S^ -k⁻¹) • (H • S^ -k) • (M k* • CZ) • H • S⁻¹ ^ k' • S⁻¹ ↑ ^ k' ≈⟨ cong (word-comm a (toℕ -k⁻¹) (axiom comm-CZ-S↓)) (cright cleft axiom (semi-M↓CZ k*)) ⟩
    (S^ -k⁻¹ • CZ ^ a) • (H • S^ -k) • (CZ^ k • M k*) • H • S⁻¹ ^ k' • S⁻¹ ↑ ^ k' ≈⟨ special-assoc (□ ^ 2 • □ ^ 2 • □ ^ 2 • □ ^ 3) (□ ^ 3 • □ ^ 2 • □ ^ 4) auto ⟩
    (S^ -k⁻¹ • CZ ^ a • H) • (S^ -k • CZ^ k) • M k* • H • S⁻¹ ^ k' • S⁻¹ ↑ ^ k' ≈⟨ (cright cleft word-comm (toℕ -k) (toℕ k) (sym (axiom comm-CZ-S↓))) ⟩
    (S^ -k⁻¹ • CZ ^ a • H) • (CZ^ k • S^ -k) • M k* • H • S⁻¹ ^ k' • S⁻¹ ↑ ^ k' ≈⟨ special-assoc  (□ ^ 3 • □ ^ 2 • □ ^ 4) (□ • □ ^ 3 • □ • □ ^ 2 • □ ^ 2) auto ⟩
    S^ -k⁻¹ • (CZ ^ a • H • CZ^ k) • S^ -k • (M k* • H) • S⁻¹ ^ k' • S⁻¹ ↑ ^ k' ≈⟨ (cright cright cright cleft sym (semi-HM' k*)) ⟩
    S^ -k⁻¹ • (CZ ^ a • H • CZ^ k) • S^ -k • (H • M (k* ⁻¹)) • S⁻¹ ^ k' • S⁻¹ ↑ ^ k' ≈⟨ special-assoc (□ • □ ^ 3 • □ • □ ^ 2 • □ ^ 2) ((□ • □ ^ 3 • □ ^ 2) • □ ^ 2 • □) auto ⟩
    (S^ -k⁻¹ • (CZ ^ a • H • CZ^ k) • S^ -k • H) • (M (k* ⁻¹) • S⁻¹ ^ k') • S⁻¹ ↑ ^ k' ≈⟨ (cright cleft aux1) ⟩
    (S^ -k⁻¹ • (CZ ^ a • H • CZ^ k) • S^ -k • H) • (S^ -k⁻¹ • M (k* ⁻¹)) • S⁻¹ ↑ ^ k' ≈⟨ special-assoc ((□ • □ ^ 3 • □ ^ 2) • □ ^ 2 • □) (□ ^ 4 • (□ ^ 3 • □) • □) auto ⟩
    (S^ -k⁻¹ • (CZ ^ a • H • CZ^ k)) • ((S^ -k • H • S^ -k⁻¹) • M (k* ⁻¹)) • S⁻¹ ↑ ^ k' ≈⟨ sym (cright cleft cleft (cleft refl' (Eq.cong S^ (Eq.cong -_ (inv-involutive k*))))) ⟩
    (S^ -k⁻¹ • (CZ ^ a • H • CZ^ k)) • ((S^ (- ((k* ⁻¹ ⁻¹) .proj₁)) • H • S^ -k⁻¹) • M (k* ⁻¹)) • S⁻¹ ↑ ^ k' ≈⟨ (cright cleft sym (lemma-Euler' (k* ⁻¹))) ⟩
    (S^ -k⁻¹ • (CZ ^ a • H • CZ^ k)) • (H ^ 3 • S^ k⁻¹ • H) • S⁻¹ ↑ ^ k' ≈⟨ (cright cright refl' (aux-↑ S⁻¹ k')) ⟩
    (S^ -k⁻¹ • (CZ ^ a • H • CZ^ k)) • (H ^ 3 • S^ k⁻¹ • H) • (S⁻¹ ^ k') ↑  ≈⟨ (cright cright lemma-cong↑ _ _ (lemma-S⁻¹^k k)) ⟩
    (S^ -k⁻¹ • (CZ ^ a • H • CZ^ k)) • (H ^ 3 • S^ k⁻¹ • H) • (S^ -k) ↑  ≈⟨ (cleft cright lemma-CZCZ^aHCZ^k a-1 k nzk) ⟩

    (S^ -k⁻¹ • (S^ -k⁻¹) ^ a-1 • (CZ • H • CZ^ k) • (H ^ 3 • (S^ k⁻¹) ^ a-1 • H) • ((S^ -k) ^ a-1) ↑) • (H ^ 3 • S^ k⁻¹ • H) • (S^ -k) ↑ ≈⟨ special-assoc (□ ^ 5 • □ ^ 2) (□ ^ 2 • □ • □ • □ ^ 2 • □) auto ⟩
    (S^ -k⁻¹ • (S^ -k⁻¹) ^ a-1) • (CZ • H • CZ^ k) • (H ^ 3 • (S^ k⁻¹) ^ a-1 • H) • ((S^ -k ^ a-1) ↑ • (H ^ 3 • S^ k⁻¹ • H)) • (S^ -k) ↑ ≈⟨ cong (aux-ww^k (S^ -k⁻¹) a-1) (cright cright cleft aux2') ⟩
    (S^ -k⁻¹) ^ a • (CZ • H • CZ^ k) • (H ^ 3 • (S^ k⁻¹) ^ a-1 • H) • ((H ^ 3 • S^ k⁻¹ • H) • (S^ -k ^ a-1) ↑) • (S^ -k) ↑ ≈⟨ (cright cright special-assoc (□ • □ ^ 2 • □) (□ ^ 2 • □ ^ 2) auto) ⟩
    (S^ -k⁻¹) ^ a • (CZ • H • CZ^ k) • ((H ^ 3 • (S^ k⁻¹) ^ a-1 • H) • (H ^ 3 • S^ k⁻¹ • H)) • (S^ -k ^ a-1) ↑ • (S^ -k) ↑ ≈⟨ (cright cright cong (special-assoc (□ ^ 3 • □ ^ 3) (□ • □ • □ ^ 2 • □ ^ 2) auto) (lemma-cong↑ _ _ (PP1.word-comm a-1 (toℕ -k) (PP1.word-comm (toℕ -k) 1 PB1.refl)))) ⟩
    (S^ -k⁻¹) ^ a • (CZ • H • CZ^ k) • (H ^ 3 • (S^ k⁻¹) ^ a-1 • (H • H ^ 3) • S^ k⁻¹ • H) • (S^ -k) ↑ • (S^ -k ^ a-1) ↑ ≈⟨ (cright cright cong (cright cright cleft axiom order-H) (lemma-cong↑ _ _ (aux-ww^k (S^ -k) a-1))) ⟩
    (S^ -k⁻¹) ^ a • (CZ • H • CZ^ k) • (H ^ 3 • (S^ k⁻¹) ^ a-1 • ε • S^ k⁻¹ • H) • (S^ -k ^ a) ↑ ≈⟨ (cright cright cleft (cright cright left-unit)) ⟩
    (S^ -k⁻¹) ^ a • (CZ • H • CZ^ k) • (H ^ 3 • (S^ k⁻¹) ^ a-1 • S^ k⁻¹ • H) • (S^ -k ^ a) ↑ ≈⟨ (cright cright cleft cright sym assoc) ⟩
    (S^ -k⁻¹) ^ a • (CZ • H • CZ^ k) • (H ^ 3 • (S^ k⁻¹ ^ a-1 • S^ k⁻¹) • H) • (S^ -k ^ a) ↑ ≈⟨ (cright cright cleft cright cleft word-comm a-1 (toℕ k⁻¹) (word-comm (toℕ k⁻¹) 1 refl)) ⟩
    (S^ -k⁻¹) ^ a • (CZ • H • CZ^ k) • (H ^ 3 • (S^ k⁻¹ • S^ k⁻¹ ^ a-1) • H) • (S^ -k ^ a) ↑ ≈⟨ (cright cright cleft cright cleft aux-ww^k (S^ k⁻¹) a-1) ⟩
    (S^ -k⁻¹) ^ a • (CZ • H • CZ^ k) • (H ^ 3 • S^ k⁻¹ ^ a • H) • (S^ -k ^ a) ↑ ∎
    where
    module PB1 = PB (1 QRel,_===_)
    module PP1 = PP (1 QRel,_===_)
    j = suc a
    k' = toℕ k
    k* : ℤ* ₚ
    k* = (k , nzk)
    -k = - k
    k⁻¹ = ((k* ⁻¹) .proj₁)
    -k⁻¹ = - k⁻¹
    aux1 : M (k* ⁻¹) • S⁻¹ ^ k' ≈ S^ -k⁻¹ • M (k* ⁻¹)
    aux1 = begin
      M (k* ⁻¹) • S⁻¹ ^ k' ≈⟨ (cright lemma-S⁻¹^k k) ⟩
      M (k* ⁻¹) • S^ -k ≈⟨ lemma-MS^k k⁻¹ -k ((k* ⁻¹) .proj₂) ⟩
      S^ (-k * (k⁻¹ * k⁻¹)) • M (k* ⁻¹) ≈⟨ (cleft refl' (Eq.cong S^ (Eq.sym (*-assoc -k k⁻¹ k⁻¹)))) ⟩
      S^ (-k * k⁻¹ * k⁻¹) • M (k* ⁻¹) ≈⟨ (cleft refl' (Eq.cong (\ xx -> S^ (xx * k⁻¹)) (Eq.sym (-‿distribˡ-* k k⁻¹)))) ⟩
      S^ (- (k * k⁻¹) * k⁻¹) • M (k* ⁻¹) ≈⟨ (cleft refl' (Eq.cong (\ xx -> S^ (- xx * k⁻¹)) (lemma-⁻¹ʳ k {{nztoℕ {y = k} {nzk}}}))) ⟩
      S^ (- (1ₚ) * k⁻¹) • M (k* ⁻¹) ≈⟨ (cleft refl' (Eq.cong S^ (-1*x≈-x k⁻¹))) ⟩
      S^ (-k⁻¹) • M (k* ⁻¹) ≈⟨ refl ⟩
      S^ -k⁻¹ • M (k* ⁻¹) ∎


    aux2' : ((S^ -k) ^ a-1) ↑ • (H ^ 3 • S^ k⁻¹ • H) ≈ (H ^ 3 • S^ k⁻¹ • H) • ((S^ -k) ^ a-1) ↑
    aux2' = begin
      ((S^ -k) ^ a-1) ↑ • (H ^ 3 • S^ k⁻¹ • H) ≈⟨ sym assoc ⟩
      (((S^ -k) ^ a-1) ↑ • H ^ 3) • S^ k⁻¹ • H ≈⟨ (cleft sym (lemma-comm-Hᵏ-w↑ (₃₊ 0) (S^ -k ^ a-1))) ⟩
      (H ^ 3 • ((S^ -k) ^ a-1) ↑) • S^ k⁻¹ • H ≈⟨ special-assoc (□ ^ 2 • □ ^ 2) (□ • □ ^ 2 • □) auto ⟩
      H ^ 3 • (((S^ -k) ^ a-1) ↑ • S^ k⁻¹) • H ≈⟨ (cright cleft sym (lemma-comm-Sᵏ-w↑ (toℕ k⁻¹) (((S^ -k) ^ a-1)))) ⟩
      H ^ 3 • (S^ k⁻¹ • ((S^ -k) ^ a-1) ↑) • H ≈⟨ (cright assoc) ⟩
      H ^ 3 • S^ k⁻¹ • ((S^ -k) ^ a-1) ↑ • H ≈⟨ (cright cright sym (lemma-comm-H-w↑ (S^ -k ^ a-1))) ⟩
      H ^ 3 • S^ k⁻¹ • H • ((S^ -k) ^ a-1) ↑ ≈⟨ special-assoc (□ ^ 4 ) (□ ^ 3 • □) auto ⟩
      (H ^ 3 • S^ k⁻¹ • H) • ((S^ -k) ^ a-1) ↑ ∎



  lemma-CZCZ^aHCZ^k' : ∀ a k -> (nzk : k ≢ ₀) -> 
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

  lemma-CZCZ^aHCZ^k' a k nzk = 
    let
      j = suc a
      k' = toℕ k
      k* : ℤ* ₚ
      k* = (k , nzk)
      -k = - k
      k⁻¹ = ((k* ⁻¹) .proj₁)
      -k⁻¹ = - k⁻¹
    in sym (begin
      S^ -k⁻¹ ^ j • H • CZ^ k • H ^ 3 • S^ k⁻¹ ^ j • H • (S^ -k ^ j) ↑ ≈⟨ sym assoc ⟩
      (S^ -k⁻¹ ^ j • H) • CZ^ k • H ^ 3 • (S^ k⁻¹ ^ j) • H • (S^ -k ^ j) ↑ ≈⟨ (cright sym left-unit) ⟩
      (S^ -k⁻¹ ^ j • H) • ε • CZ^ k • H ^ 3 • (S^ k⁻¹ ^ j) • H • (S^ -k ^ j) ↑ ≈⟨ (cright cleft sym (lemma-S^-k+k k)) ⟩
      (S^ -k⁻¹ ^ j • H) • (S^ -k • S^ k) • CZ^ k • H ^ 3 • (S^ k⁻¹ ^ j) • H • (S^ -k ^ j) ↑ ≈⟨ special-assoc (□ ^ 2 • □ ^ 2 • □ ^ 2) (□ ^ 3 • □ ^ 2 • □) auto ⟩
      (S^ -k⁻¹ ^ j • H • S^ -k) • (S^ k • CZ^ k) • H ^ 3 • (S^ k⁻¹ ^ j) • H • (S^ -k ^ j) ↑ ≈⟨ (cright cleft word-comm (toℕ k) (toℕ k) (sym (axiom comm-CZ-S↓))) ⟩
      (S^ -k⁻¹ ^ j • H • S^ -k) • (CZ^ k • S^ k) • H ^ 3 • (S^ k⁻¹ ^ j) • H • (S^ -k ^ j) ↑ ≈⟨ (cright special-assoc (□ ^ 2 • □ ^ 4) (□ • □ ^ 2 • □ ^ 3) auto) ⟩
      (S^ -k⁻¹ ^ j • H • S^ -k) • (CZ^ k) • (S^ k • H ^ 3) • (S^ k⁻¹ ^ j) • H • (S^ -k ^ j) ↑ ≈⟨ (cright cleft sym right-unit) ⟩
      (S^ -k⁻¹ ^ j • H • S^ -k) • (CZ^ k • ε) • (S^ k • H ^ 3) • (S^ k⁻¹ ^ j) • H • (S^ -k ^ j) ↑ ≈⟨ (cright cleft cright lemma-M1) ⟩
      (S^ -k⁻¹ ^ j • H • S^ -k) • (CZ^ k • M₁) • (S^ k • H ^ 3) • (S^ k⁻¹ ^ j) • H • (S^ -k ^ j) ↑ ≈⟨ (cright cright cright (cleft sym (aux-ww^k (S^ k⁻¹) a))) ⟩
      (S^ -k⁻¹ ^ j • H • S^ -k) • (CZ^ k • M₁) • (S^ k • H ^ 3) • (S^  k⁻¹ • S^ k⁻¹ ^ a) • H • (S^ -k ^ j) ↑ ≈⟨ (cright cright special-assoc (□ ^ 2 • □ ^ 2 • □ ) (□ ^ 3 • □ ^ 2) auto) ⟩
      (S^ -k⁻¹ ^ j • H • S^ -k) • (CZ^ k • M₁) • (S^ k • H ^ 3 • S^  k⁻¹) • S^ k⁻¹ ^ a • H • (S^ -k ^ j) ↑ ≈⟨ (cright (cright cong (cong (refl' (Eq.cong S^ (Eq.sym (-‿involutive k)))) (cright refl' (Eq.cong S^ (aux-k⁻¹=-[-k⁻¹] k*)))) refl)) ⟩
      
      (S^ -k⁻¹ ^ j • H • S^ (- k)) • (CZ^ k • M₁) • (S^ (- b) • H ^ 3 • S^ (-b⁻¹)) • S^ k⁻¹ ^ a • H • (S^ -k ^ j) ↑ ≈⟨ (cright cleft cright aux-MM (λ ()) ((k* *' -' b' ⁻¹) .proj₂) (Eq.sym (aux-k*-[-k]⁻¹ k*))) ⟩
      (S^ -k⁻¹ ^ j • H • S^ (- k)) • (CZ^ k • M (k* *' -' b' ⁻¹)) • (S^ (- b) • H ^ 3 • S^ (-b⁻¹)) • S^ k⁻¹ ^ a • H • (S^ -k ^ j) ↑ ≈⟨ (cright cleft (cright sym (axiom (M-mul k* (-' b' ⁻¹))))) ⟩
      (S^ -k⁻¹ ^ j • H • S^ (- k)) • (CZ^ k • M k* • M (-' b' ⁻¹)) • (S^ (- b) • H ^ 3 • S^ (-b⁻¹)) • S^ k⁻¹ ^ a • H • (S^ -k ^ j) ↑ ≈⟨ (cright special-assoc (□ ^ 3 • □ ^ 3 • □) (□ ^ 2 • □ ^ 4 • □) auto) ⟩
      (S^ -k⁻¹ ^ j • H • S^ (- k)) • (CZ^ k • M k*) • (M (-' b' ⁻¹) • (S^ (- b) • H ^ 3 • S^ (-b⁻¹))) • S^ k⁻¹ ^ a • H • (S^ -k ^ j) ↑ ≈⟨ (cright cright cleft sym (lemma-Euler′' (-' k*))) ⟩
      (S^ -k⁻¹ ^ j • H • S^ (- k)) • (CZ^ k • M k*) • (H • S^ ((-' k*) .proj₁) • H ^ 3) • S^ k⁻¹ ^ a • H • (S^ -k ^ j) ↑ ≈⟨ refl ⟩
      (S^ -k⁻¹ ^ j • H • S^ (- k)) • (CZ^ k • M k*) • (H • S^ -k • H ^ 3) • S^ k⁻¹ ^ a • H • (S^ -k ^ j) ↑ ≈⟨ (cright cleft sym (axiom (semi-M↓CZ k*))) ⟩
      (S^ -k⁻¹ ^ j • H • S^ (- k)) • (M k* • CZ) • (H • S^ -k • H ^ 3) • S^ k⁻¹ ^ a • H • (S^ -k ^ j) ↑ ≈⟨ special-assoc (□ ^ 3 • □ ^ 2 • □) (□ ^ 6 ) auto ⟩
      (S^ -k⁻¹ ^ j) • H • S^ (- k) • M k* • CZ • (H • S^ -k • H ^ 3) • S^ k⁻¹ ^ a • H • (S^ -k ^ j) ↑ ≈⟨ (cleft sym (aux-ww^k (S^ -k⁻¹) a)) ⟩
      (S^ -k⁻¹ • S^ -k⁻¹ ^ a) • H • S^ (- k) • M k* • CZ • (H • S^ -k • H ^ 3) • S^ k⁻¹ ^ a • H • (S^ -k ^ j) ↑ ≈⟨ (cleft word-comm 1 a refl) ⟩
      (S^ -k⁻¹ ^ a • S^ -k⁻¹) • H • S^ (- k) • M k* • CZ • (H • S^ -k • H ^ 3) • S^ k⁻¹ ^ a • H • (S^ -k ^ j) ↑ ≈⟨ special-assoc (□ ^ 2 • □ ^ 8) (□ • (□ ^ 3 • □) • □ ^ 5) auto ⟩
      (S^ -k⁻¹) ^ a • ((S^ -k⁻¹ • H • S^ (- k)) • M k*) • CZ • (H • S^ -k • H ^ 3) • S^ k⁻¹ ^ a • H • (S^ -k ^ j) ↑ ≈⟨ (cright special-assoc (□ ^ 2 • □ • □ ^ 3 • □ ^ 3) ((□ ^ 2 • □ ^ 3) • □ ^ 3 • □) auto) ⟩
      (S^ -k⁻¹) ^ a • (((S^ -k⁻¹ • H • S^ (- k)) • M k*) • CZ • H • S^ -k) • (H ^ 3 • S^ k⁻¹ ^ a • H) • (S^ -k ^ j) ↑ ≈⟨ (cright cong (cleft sym (lemma-Euler' k*)) refl) ⟩
      (S^ -k⁻¹) ^ a • ((H ^ 3 • S^ k • H) • CZ • H • S^ -k) • (H ^ 3 • S^ k⁻¹ ^ a • H) • (S^ -k ^ j) ↑ ≈⟨ sym (cright cright cright lemma-cong↑ _ _ (aux-ww^k (S^ -k) a)) ⟩
      (S^ -k⁻¹) ^ a • ((H ^ 3 • S^ k • H) • CZ • H • S^ -k) • ((H ^ 3 • S^ k⁻¹ ^ a • H)) • S^ -k ↑ • (S^ -k ^ a) ↑ ≈⟨ (cright cright sym assoc) ⟩
      (S^ -k⁻¹) ^ a • ((H ^ 3 • S^ k • H) • CZ • H • S^ -k) • ((H ^ 3 • S^ k⁻¹ ^ a • H) • S^ -k ↑) • (S^ -k ^ a) ↑ ≈⟨ (cright cleft cright cright cright sym (lemma-S⁻¹^k k)) ⟩
      (S^ -k⁻¹) ^ a • ((H ^ 3 • S ^ k' • H) • CZ • H • S⁻¹ ^ k') • ((H ^ 3 • S^ k⁻¹ ^ a • H) • S^ -k ↑) • (S^ -k ^ a) ↑ ≈⟨ (cright cright cleft sym aux2') ⟩
      (S^ -k⁻¹) ^ a • ((H ^ 3 • S ^ k' • H) • CZ • H • S⁻¹ ^ k') • (S^ -k ↑ • (H ^ 3 • S^ k⁻¹ ^ a • H)) • (S^ -k ^ a) ↑ ≈⟨ (cright cright cleft (cleft sym (lemma-cong↑ _ _ (lemma-S⁻¹^k k)))) ⟩
      (S^ -k⁻¹) ^ a • ((H ^ 3 • S ^ k' • H) • CZ • H • S⁻¹ ^ k') • ((S⁻¹ ^ k') ↑ • (H ^ 3 • S^ k⁻¹ ^ a • H)) • (S^ -k ^ a) ↑ ≈⟨ (cright cright cleft (cleft sym (refl' (aux-↑ S⁻¹ k')))) ⟩
      (S^ -k⁻¹) ^ a • ((H ^ 3 • S ^ k' • H) • CZ • H • S⁻¹ ^ k') • (S⁻¹ ↑ ^ k' • (H ^ 3 • S^ k⁻¹ ^ a • H)) • (S^ -k ^ a) ↑ ≈⟨ (cright special-assoc (□ ^ 4 • □ ^ 2 • □) (□ ^ 5 • □ ^ 2) auto) ⟩
      (S^ -k⁻¹) ^ a • ((H ^ 3 • S ^ k' • H) • CZ • H • S⁻¹ ^ k' • S⁻¹ ↑ ^ k') • (H ^ 3 • S^ k⁻¹ ^ a • H) • (S^ -k ^ a) ↑ ≈⟨ (cright (cleft cleft sym (lemma-[S⁻¹HS⁻¹]^k k'))) ⟩
      (S^ -k⁻¹) ^ a • ((S⁻¹ • H • S⁻¹) ^ k' • CZ • H • S⁻¹ ^ k' • S⁻¹ ↑ ^ k') • (H ^ 3 • S^ k⁻¹ ^ a • H) • (S^ -k ^ a) ↑ ≈⟨ (cright cleft sym (lemma-CZHCZ^-k k)) ⟩
      (S^ -k⁻¹) ^ a • (CZ • H • CZ^ k) • (H ^ 3 • S^ k⁻¹ ^ a • H) • (S^ -k ^ a) ↑ ≈⟨ sym (lemma-CZCZ^aHCZ^k a k nzk) ⟩
      CZ ^ j • H • CZ^ k ∎)

    where
    j = suc a
    k' = toℕ k
    k* : ℤ* ₚ
    k* = (k , nzk)
    -k = - k
    k⁻¹ = ((k* ⁻¹) .proj₁)
    -k⁻¹ = - k⁻¹
    b' = (-' k*)
    b = b' .proj₁
    -b⁻¹ = - ((b' ⁻¹) .proj₁)
    
    aux2' : ((S^ -k)) ↑ • (H ^ 3 • S^ k⁻¹ ^ a • H) ≈ (H ^ 3 • S^ k⁻¹ ^ a • H) • ((S^ -k)) ↑
    aux2' = begin
      ((S^ -k)) ↑ • (H ^ 3 • S^ k⁻¹ ^ a • H) ≈⟨ sym assoc ⟩
      (((S^ -k)) ↑ • H ^ 3) • S^ k⁻¹ ^ a • H ≈⟨ (cleft sym (lemma-comm-Hᵏ-w↑ (₃₊ 0) (S^ -k))) ⟩
      (H ^ 3 • ((S^ -k)) ↑) • S^ k⁻¹ ^ a • H ≈⟨ special-assoc (□ ^ 2 • □ ^ 2) (□ • □ ^ 2 • □) auto ⟩
      H ^ 3 • (((S^ -k)) ↑ • S^ k⁻¹ ^ a) • H ≈⟨ (cright cleft (cright lemma-^^ S (toℕ k⁻¹) a)) ⟩
      H ^ 3 • (((S^ -k)) ↑ • S ^ (toℕ k⁻¹ Nat.* a)) • H ≈⟨ (cright cleft sym (lemma-comm-Sᵏ-w↑ ((toℕ k⁻¹ Nat.* a)) (S^ -k))) ⟩
      H ^ 3 • (S ^ (toℕ k⁻¹ Nat.* a) • S^ -k ↑) • H ≈⟨ (cright cleft (cleft sym (lemma-^^ S (toℕ k⁻¹) a))) ⟩
      H ^ 3 • (S^ k⁻¹ ^ a • ((S^ -k)) ↑) • H ≈⟨ (cright assoc) ⟩
      H ^ 3 • S^ k⁻¹ ^ a • ((S^ -k)) ↑ • H ≈⟨ (cright cright sym (lemma-comm-H-w↑ (S^ -k))) ⟩
      H ^ 3 • S^ k⁻¹ ^ a • H • ((S^ -k)) ↑ ≈⟨ special-assoc (□ ^ 4 ) (□ ^ 3 • □) auto ⟩
      (H ^ 3 • S^ k⁻¹ ^ a • H) • ((S^ -k)) ↑ ∎

  abstract

    lemma-CZCZ^aH³CZ^k' : ∀ (a : ℕ) (k : ℤ ₚ) -> (nzk : k ≢ ₀) -> 
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

    lemma-CZCZ^aH³CZ^k' a k nzk = 
      begin
        CZ ^ j • H ^ 3 • CZ^ k ≈⟨ (cright assoc) ⟩
        CZ ^ j • H • H ^ 2 • CZ^ k ≈⟨ (cright cright cleft lemma-HH-M-1) ⟩
        CZ ^ j • H • M -'₁ • CZ^ k ≈⟨ (cright cright lemma-M↓CZ^k (- ₁) k (-'₁ .proj₂)) ⟩
        CZ ^ j • H • CZ^ (k * - ₁) • M -'₁ ≈⟨ (cright cright  cong (refl' (Eq.cong CZ^ (Eq.sym (Eq.trans (Eq.cong -_ (Eq.sym (*-identityʳ k ))) ((-‿distribʳ-* k ₁)) )))) (sym lemma-HH-M-1)) ⟩
        CZ ^ j • H • CZ^ -k • H ^ 2 ≈⟨ special-assoc (□ ^ 4) (□ ^ 3 • □) auto ⟩
        (CZ ^ j • H • CZ^ -k) • H ^ 2 ≈⟨ (cleft lemma-CZCZ^aHCZ^k' a (- k) ((-' k*) .proj₂)) ⟩
        (S^ -k⁻¹' ^ j • H • CZ^ k' • H ^ 3 • S^ k⁻¹' ^ j • H • (S^ -k' ^ j) ↑) • H ^ 2 ≈⟨ special-assoc (□ ^ 7 • □) (□ ^ 6 • □ ^ 2) auto ⟩
        (S^ -k⁻¹' ^ j • H • CZ^ k' • H ^ 3 • S^ k⁻¹' ^ j • H) • (S^ -k' ^ j) ↑ • H ^ 2 ≈⟨ (cright sym (lemma-comm-Hᵏ-w↑ 2 ((S^ -k' ^ j)))) ⟩
        (S^ -k⁻¹' ^ j • H • CZ^ k' • H ^ 3 • S^ k⁻¹' ^ j • H) • H ^ 2 • (S^ -k' ^ j) ↑ ≈⟨ (cleft (cright cright cright special-assoc (□ ^ 3 • □ ^ 2) (□ • (□ ^ 2 • □) • □) auto)) ⟩
        (S^ -k⁻¹' ^ j • H • CZ^ k' • H • (H ^ 2 • S^ k⁻¹' ^ j) • H) • H ^ 2 • (S^ -k' ^ j) ↑ ≈⟨ (cleft (cright cright cright  (cright (cleft word-comm 1 j (word-comm 1 (toℕ k⁻¹') (trans assoc (axiom comm-HHS))))))) ⟩
        (S^ -k⁻¹' ^ j • H • CZ^ k' • H • (S^ k⁻¹' ^ j • H ^ 2) • H) • H ^ 2 • (S^ -k' ^ j) ↑ ≈⟨ special-assoc ((□ • □ • □ • □ • □ ^ 2 • □) • □ ^ 2) (□ ^ 5 • □ ^ 4) auto ⟩
        (S^ -k⁻¹' ^ j • H • CZ^ k' • H • S^ k⁻¹' ^ j) • H ^ 2 • H • H ^ 2 • (S^ -k' ^ j) ↑ ≈⟨ (cright rewrite-sym0 100 auto) ⟩
        (S^ -k⁻¹' ^ j • H • CZ^ k' • H • S^ k⁻¹' ^ j) • (H ^ 2 • H • H ^ 2) • (S^ -k' ^ j) ↑ ≈⟨ (cright cleft rewrite-sym0 100 auto) ⟩
        (S^ -k⁻¹' ^ j • H • CZ^ k' • H • S^ k⁻¹' ^ j) • H • (S^ -k' ^ j) ↑ ≈⟨ special-assoc (□ ^ 5 • □ ^ 2) (□ ^ 7) auto ⟩
        S^ -k⁻¹' ^ j • H • CZ^ k' • H • S^ k⁻¹' ^ j • H • (S^ -k' ^ j) ↑ ≈⟨ cong (refl' (Eq.cong (\ xx -> S^ xx ^ j) (Eq.sym (aux-k⁻¹=-[-k⁻¹] k*)))) (cright cong refl (cright  cong (refl' (Eq.cong (\ xx -> S^ xx ^ j) (inv-neg-comm k*))) (cright refl' (Eq.cong (\ xx -> ((S^ xx ^ j) ↑)) (-‿involutive k))))) ⟩

        S^ k⁻¹ ^ j • H • CZ^ -k • H • S^ -k⁻¹ ^ j • H • (S^ k ^ j) ↑ ∎
      where
      j : ℕ
      j = suc a

      -k : ℤ ₚ
      -k = - k

      k* : ℤ* ₚ
      k* = (k , nzk)
      k⁻¹ : ℤ ₚ
      k⁻¹ = ((k* ⁻¹) .proj₁)
      -k⁻¹ : ℤ ₚ
      -k⁻¹ = - k⁻¹
      
      k' : ℤ ₚ
      k' = - k
      k*' : ℤ* ₚ
      k*' = (- k , (-' k*) .proj₂ )
      -k' : ℤ ₚ
      -k' = - - k
      k⁻¹' : ℤ ₚ
      k⁻¹' = ((k*' ⁻¹) .proj₁)
      -k⁻¹' : ℤ ₚ
      -k⁻¹' = - k⁻¹'
      open Sym0-Rewriting 1


  lemma-Ex-S↑ : 

    Ex • S ↑ ≈ S • Ex

  lemma-Ex-S↑ = begin
    Ex • (S ↑) ≈⟨ sym right-unit ⟩
    (Ex • (S ↑)) • ε ≈⟨ (cright sym lemma-order-Ex) ⟩
    (Ex • (S ↑)) • Ex ^ 2 ≈⟨ by-assoc auto ⟩
    Ex • (S ↑ • Ex) • Ex ≈⟨ cong refl (cong (lemma-comm-Ex-S) refl) ⟩
    Ex • (Ex • S) • Ex ≈⟨ by-assoc auto ⟩
    (Ex • Ex) • S • Ex ≈⟨ cong lemma-order-Ex refl ⟩
    ε • S • Ex ≈⟨ left-unit ⟩
    S • Ex ∎


  lemma-Ex-H↑ : 

    Ex • H ↑ ≈ H • Ex

  lemma-Ex-H↑ = begin
    Ex • (H ↑) ≈⟨ sym right-unit ⟩
    (Ex • (H ↑)) • ε ≈⟨ (cright sym lemma-order-Ex) ⟩
    (Ex • (H ↑)) • Ex ^ 2 ≈⟨ by-assoc auto ⟩
    Ex • (H ↑ • Ex) • Ex ≈⟨ cong refl (cong (lemma-comm-Ex-H) refl) ⟩
    Ex • (Ex • H) • Ex ≈⟨ by-assoc auto ⟩
    (Ex • Ex) • H • Ex ≈⟨ cong lemma-order-Ex refl ⟩
    ε • H • Ex ≈⟨ left-unit ⟩
    H • Ex ∎



{-




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

    CZ ^ k • S⁻¹ ↑ ≈ S⁻¹ ↑ • CZ ^ k
    
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
  open Lemmas2 hiding (n)
  
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


module Lemmas3 where
  variable
    n : ℕ

  open Symplectic
  open import Zp.ModularArithmetic
  open Rewriting-Symplectic
  open Rewriting


  lemma-comm-Ex-w↑↑ : ∀ {n} w → let open PB ((₂₊ n) QRel,_===_) in
    
    Ex • w ↑ ↑ ≈ w ↑ ↑ • Ex
    
  lemma-comm-Ex-w↑↑ {n} [ H-gen ]ʷ = rewrite-sym (suc n) 1000 auto
  lemma-comm-Ex-w↑↑ {n} [ S-gen ]ʷ = rewrite-sym (suc n) 1000 auto
  lemma-comm-Ex-w↑↑ {n} [ CZ-gen ]ʷ = rewrite-sym (suc n) 1000 auto
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



{-
  lemma-comm-Ex-S↑↑ : let open PB ((₃₊ n) QRel,_===_) in
    Ex • S ↑ ↑ ≈ S ↑ ↑ • Ex
  lemma-comm-Ex-S↑↑ {n} = {!!}
    where
    open PB ((₂₊ n) QRel,_===_)
    open PP ((₂₊ n) QRel,_===_)
    open SR word-setoid
    open Powers0-Symplectic (suc n)


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

-}




-}


