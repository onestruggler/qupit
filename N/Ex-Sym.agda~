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



module N.Ex-Sym (p-2 : ℕ) (p-prime : Prime (2+ p-2))  where

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
module Lemmas0a where

  private
    variable
      n : ℕ
      
  open Symplectic
  open Lemmas-Sym

  open Symplectic-GroupLike

  open import Data.Nat.DivMod
  open import Data.Fin.Properties

  lemma-HS⁻¹HS⁻¹ : let open PB ((₁₊ n) QRel,_===_) in

    H • S⁻¹ • H • S⁻¹ ≈ S • H

  lemma-HS⁻¹HS⁻¹ {n} = begin
    H • S⁻¹ • H • S⁻¹ ≈⟨ trans (sym left-unit) (sym (cong  (axiom order-SH) refl)) ⟩
    (S • H) ^ 3 • (H • S⁻¹ • H • S⁻¹)  ≈⟨ (cleft by-assoc auto) ⟩
    (S • H • S • H • S • H) • H • S⁻¹ • H • S⁻¹  ≈⟨ by-assoc auto ⟩
    S • (H • S • H • S • H • H) • S⁻¹ • H • S⁻¹  ≈⟨ (cright cleft rewrite-sym0 100 auto) ⟩
    S • (HH • H • S • H • S) • S⁻¹ • H • S⁻¹  ≈⟨ by-assoc auto ⟩
    S • (HH • H • S • H) • (S • S⁻¹) • H • S⁻¹  ≈⟨ (cright cright cleft axiom order-S) ⟩
    S • (HH • H • S • H) • (ε) • H • S⁻¹  ≈⟨ by-assoc auto ⟩
    S • (HH • H • S • HH) • S⁻¹  ≈⟨ (cright cleft rewrite-sym0 100 auto) ⟩
    S • (H • S) • S⁻¹  ≈⟨ by-assoc auto ⟩
    (S • H) • S • S⁻¹  ≈⟨ cong refl (axiom order-S) ⟩
    (S • H) • ε  ≈⟨ right-unit ⟩
    S • H ∎
    where
    open PB ((₁₊ n) QRel,_===_)
    open PP ((₁₊ n) QRel,_===_)
    open SR word-setoid
    open Pattern-Assoc
    open Sym0-Rewriting n
    

  lemma-S⁻¹HS⁻¹ : let open PB ((₁₊ n) QRel,_===_) in

    S⁻¹ • H • S⁻¹ ≈ H⁻¹ • S • H

  lemma-S⁻¹HS⁻¹ {n} = bbc H ε aux00
    where
    open PB ((₁₊ n) QRel,_===_)
    open PP ((₁₊ n) QRel,_===_)
    open SR word-setoid
    open Pattern-Assoc
    open Sym0-Rewriting n
    open Symplectic-GroupLike
    open Basis-Change _ ((₁₊ n) QRel,_===_) grouplike
    aux00 : H • (S⁻¹ • H • S⁻¹) • ε ≈ H • (H⁻¹ • S • H) • ε
    aux00 = begin
      H • (S⁻¹ • H • S⁻¹) • ε ≈⟨ cong refl right-unit ⟩
      H • (S⁻¹ • H • S⁻¹) ≈⟨ refl ⟩
      H • S⁻¹ • H • S⁻¹ ≈⟨ lemma-HS⁻¹HS⁻¹ ⟩
      S • H ≈⟨ sym left-unit ⟩
      ε • S • H ≈⟨ sym (cong (axiom order-H) refl) ⟩
      (H • H⁻¹) • S • H ≈⟨ assoc ⟩
      H • (H⁻¹ • S • H) ≈⟨ sym (cong refl right-unit) ⟩
      H • (H⁻¹ • S • H) • ε ∎


  lemma-S⁻¹HS⁻¹H : let open PB ((₁₊ n) QRel,_===_) in

    S⁻¹ • H • S⁻¹ • H ≈ H • S

  lemma-S⁻¹HS⁻¹H {n} = bbc ε H aux00
    where
    open PB ((₁₊ n) QRel,_===_)
    open PP ((₁₊ n) QRel,_===_)
    open SR word-setoid
    open Pattern-Assoc
    open Sym0-Rewriting n
    open Symplectic-GroupLike
    open Basis-Change _ ((₁₊ n) QRel,_===_) grouplike
    aux00 : ε • (S⁻¹ • H • S⁻¹ • H) • H ≈ ε • (H • S) • H
    aux00 = begin
      ε • (S⁻¹ • H • S⁻¹ • H) • H ≈⟨ left-unit ⟩
      (S⁻¹ • H • S⁻¹ • H) • H ≈⟨ special-assoc (□ ^ 4 • □) (□ ^ 3 • □ ^ 2) auto ⟩
      (S⁻¹ • H • S⁻¹) • H • H ≈⟨ (cleft lemma-S⁻¹HS⁻¹) ⟩
      (H⁻¹ • S • H) • H • H ≈⟨ rewrite-sym0 100 auto ⟩
      (H • S) • H ≈⟨ sym left-unit ⟩
      ε • (H • S) • H ∎


  lemma-S⁻¹HS⁻¹' : let open PB ((₂₊ n) QRel,_===_) in

    S⁻¹ ↑ • H ↑ • S⁻¹ ↑ ≈ H⁻¹ ↑ • S ↑ • H ↑

  lemma-S⁻¹HS⁻¹' {n} = begin
    S⁻¹ ↑ • H ↑ • S⁻¹ ↑ ≈⟨ refl ⟩
    (S⁻¹ • H • S⁻¹) ↑ ≈⟨ lemma-cong↑ _ _ lemma-S⁻¹HS⁻¹ ⟩
    (H⁻¹ • S • H) ↑ ≈⟨ refl ⟩
    H⁻¹ ↑ • S ↑ • H ↑ ∎
    where
    open PB ((₂₊ n) QRel,_===_)
    open PP ((₂₊ n) QRel,_===_)
    open SR word-setoid
    open Pattern-Assoc
    open Sym0-Rewriting (suc n)
    open Symplectic-GroupLike
    open Basis-Change _ ((₁₊ n) QRel,_===_) grouplike


  aux-[H⁻¹SH]^k : let open PB ((₁₊ n) QRel,_===_) in
    ∀ k -> (H⁻¹ • S • H) ^ k ≈ H⁻¹ • S ^ k • H
  aux-[H⁻¹SH]^k {n} k@0 = rewrite-sym0 100 auto
    where
    open PB ((₁₊ n) QRel,_===_)
    open PP ((₁₊ n) QRel,_===_)
    open SR word-setoid
    open Pattern-Assoc
    open Sym0-Rewriting n
    open Symplectic-GroupLike
    open Basis-Change _ ((₁₊ n) QRel,_===_) grouplike
  aux-[H⁻¹SH]^k {n} k@1 = PB.refl
  aux-[H⁻¹SH]^k {n} k@(₂₊ k') = begin
    (H⁻¹ • S • H) ^ k ≈⟨ cong refl (aux-[H⁻¹SH]^k (suc k')) ⟩
    (H⁻¹ • S • H) • H⁻¹ • S ^ suc k' • H ≈⟨ by-assoc auto ⟩
    (H⁻¹ • S • H • H⁻¹) • S ^ suc k' • H ≈⟨ (cleft rewrite-sym0 100 auto) ⟩
    (H⁻¹ • S) • S ^ suc k' • H ≈⟨ special-assoc (□ ^ 2 • □ • □) (□ • □ ^ 2 • □) auto ⟩
    H⁻¹ • S ^ k • H ∎
    where
    open PB ((₁₊ n) QRel,_===_)
    open PP ((₁₊ n) QRel,_===_)
    open SR word-setoid
    open Pattern-Assoc
    open Sym0-Rewriting n
    open Symplectic-GroupLike
    open Basis-Change _ ((₁₊ n) QRel,_===_) grouplike



  aux-H⁻¹S⁻¹H⁻¹S⁻¹H⁻¹S⁻¹ : let open PB ((₁₊ n) QRel,_===_) in
    H⁻¹ • S⁻¹ • H⁻¹ • S⁻¹ • H⁻¹ • S⁻¹ ≈ ε
  aux-H⁻¹S⁻¹H⁻¹S⁻¹H⁻¹S⁻¹ {n} = begin
    H⁻¹ • S⁻¹ • H⁻¹ • S⁻¹ • H⁻¹ • S⁻¹ ≈⟨ trans (by-assoc auto) (sym assoc) ⟩
    (H⁻¹ • S⁻¹) WB.^' 3 ≈⟨ lemma-cong-inv (axiom order-SH) ⟩
    ε ∎
    where
    open PB ((₁₊ n) QRel,_===_)
    open PP ((₁₊ n) QRel,_===_)
    open SR word-setoid
    open Pattern-Assoc
    open Sym0-Rewriting n
    open Symplectic-GroupLike
    open Basis-Change _ ((₁₊ n) QRel,_===_) grouplike
    open Group-Lemmas _ ((₁₊ n) QRel,_===_) grouplike renaming (_⁻¹ to _⁻¹′)

  aux-H⁻¹S⁻¹H⁻¹S⁻¹H⁻¹ : let open PB ((₁₊ n) QRel,_===_) in
    H⁻¹ • S⁻¹ • H⁻¹ • S⁻¹ • H⁻¹ ≈ S
  aux-H⁻¹S⁻¹H⁻¹S⁻¹H⁻¹ {n} = begin
    H⁻¹ • S⁻¹ • H⁻¹ • S⁻¹ • H⁻¹ ≈⟨ bbc ε S⁻¹ aux00 ⟩
    S ∎
    where
    open PB ((₁₊ n) QRel,_===_)
    open PP ((₁₊ n) QRel,_===_)
    open SR word-setoid
    open Pattern-Assoc
    open Sym0-Rewriting n
    open Symplectic-GroupLike
    open Basis-Change _ ((₁₊ n) QRel,_===_) grouplike
    aux00 : ε • (H⁻¹ • S⁻¹ • H⁻¹ • S⁻¹ • H⁻¹) • S⁻¹ ≈ ε • S • S⁻¹
    aux00 = begin
      ε • (H⁻¹ • S⁻¹ • H⁻¹ • S⁻¹ • H⁻¹) • S⁻¹ ≈⟨ left-unit ⟩
      (H⁻¹ • S⁻¹ • H⁻¹ • S⁻¹ • H⁻¹) • S⁻¹ ≈⟨ special-assoc (□ ^ 5 • □) (□ ^ 6) auto ⟩
      H⁻¹ • S⁻¹ • H⁻¹ • S⁻¹ • H⁻¹ • S⁻¹ ≈⟨ aux-H⁻¹S⁻¹H⁻¹S⁻¹H⁻¹S⁻¹ ⟩
      ε ≈⟨ sym (axiom order-S) ⟩
      S • S⁻¹ ≈⟨ sym left-unit ⟩
      ε • S • S⁻¹ ∎


  aux-HS⁻¹H⁻¹S⁻¹H : let open PB ((₁₊ n) QRel,_===_) in
    H • S⁻¹ • H⁻¹ • S⁻¹ • H ≈ S
  aux-HS⁻¹H⁻¹S⁻¹H {n} = begin
    H • S⁻¹ • H⁻¹ • S⁻¹ • H ≈⟨ bbc HH HH aux00 ⟩
    S ∎
    where
    open PB ((₁₊ n) QRel,_===_)
    open PP ((₁₊ n) QRel,_===_)
    open SR word-setoid
    open Pattern-Assoc
    open Sym0-Rewriting n
    open Symplectic-GroupLike
    open Basis-Change _ ((₁₊ n) QRel,_===_) grouplike
    aux00 : HH • (H • S⁻¹ • H⁻¹ • S⁻¹ • H) • HH ≈ HH • S • HH
    aux00 = begin
      HH • (H • S⁻¹ • H⁻¹ • S⁻¹ • H) • HH ≈⟨ special-assoc (□ ^ 2 • □ ^ 5 • □ ^ 2) (□ ^ 3 • □ • □ • □ • □ ^ 3) auto ⟩
      (H⁻¹ • S⁻¹ • H⁻¹ • S⁻¹ • H⁻¹) ≈⟨ aux-H⁻¹S⁻¹H⁻¹S⁻¹H⁻¹ ⟩
      S ≈⟨ rewrite-sym0 100 auto ⟩
      HH • S • HH ∎


  lemma-HS⁻¹H : let open PB ((₁₊ n) QRel,_===_) in

    H • S⁻¹ • H ≈ S • H • S

  lemma-HS⁻¹H {n} = begin
    H • S⁻¹ • H ≈⟨ bbc ε  S⁻¹ aux00 ⟩
    S • H • S ∎
    where
    open PB ((₁₊ n) QRel,_===_)
    open PP ((₁₊ n) QRel,_===_)
    open SR word-setoid
    open Pattern-Assoc
    open Sym0-Rewriting n
    open Symplectic-GroupLike
    open Basis-Change _ ((₁₊ n) QRel,_===_) grouplike
    aux00 : ε • (H • S⁻¹ • H) • S⁻¹ ≈ ε • (S • H • S) • S⁻¹
    aux00 = begin
      ε • (H • S⁻¹ • H) • S⁻¹ ≈⟨ left-unit ⟩
      (H • S⁻¹ • H) • S⁻¹ ≈⟨ trans assoc (cong refl assoc) ⟩
      H • S⁻¹ • H • S⁻¹ ≈⟨ lemma-HS⁻¹HS⁻¹ ⟩
      (S • H) ≈⟨ sym right-unit ⟩
      (S • H) • ε ≈⟨ (cright sym (axiom order-S)) ⟩
      (S • H) • S • S⁻¹ ≈⟨ by-assoc auto ⟩
      (S • H • S) • S⁻¹ ≈⟨ sym left-unit ⟩
      ε • (S • H • S) • S⁻¹ ∎

  aux-S⁻¹⁻¹ : let open PB ((₁₊ n) QRel,_===_) in
    S⁻¹ ^ p-1 ≈ S
  aux-S⁻¹⁻¹ {n} = lemma-right-cancel {h = S⁻¹} aux00
    where
    open PB ((₁₊ n) QRel,_===_)
    open PP ((₁₊ n) QRel,_===_)
    open SR word-setoid
    open Pattern-Assoc
    open Sym0-Rewriting n
    open Symplectic-GroupLike
    open Basis-Change _ ((₁₊ n) QRel,_===_) grouplike
    open Group-Lemmas _ ((₁₊ n) QRel,_===_) grouplike renaming (_⁻¹ to _⁻¹′)
    aux00 : S⁻¹ ^ p-1 • S⁻¹ ≈ S • S⁻¹
    aux00 = begin
      S⁻¹ ^ p-1 • S⁻¹ ≈⟨ word-comm p-1 1 refl ⟩
      S⁻¹ • S⁻¹ ^ p-1 ≈⟨ refl ⟩
      S⁻¹ ^ p ≈⟨ lemma-^^ S p-1 p ⟩
      S ^ (p-1 Nat.* p) ≡⟨ Eq.cong (S ^_) (NP.*-comm p-1 p) ⟩
      S ^ (p Nat.* p-1) ≈⟨ sym (lemma-^^ S p p-1) ⟩
      (S ^ p) ^ p-1 ≈⟨ lemma-^-cong (S ^ p) ε p-1 (axiom order-S) ⟩
      ε ^ p-1 ≈⟨ lemma-ε^k=ε (₁₊ p-2) ⟩
      ε ≈⟨ sym (axiom order-S) ⟩
      S • S⁻¹ ∎


  aux-CZ⁻¹⁻¹ : let open PB ((₂₊ n) QRel,_===_) in
    CZ⁻¹ ^ p-1 ≈ CZ
  aux-CZ⁻¹⁻¹ {n} = lemma-right-cancel {h = CZ⁻¹} aux00
    where
    open PB ((₂₊ n) QRel,_===_)
    open PP ((₂₊ n) QRel,_===_)
    open SR word-setoid
    open Pattern-Assoc
    open Sym0-Rewriting (₁₊ n)
    open Symplectic-GroupLike
    open Basis-Change _ ((₂₊ n) QRel,_===_) grouplike
    open Group-Lemmas _ ((₂₊ n) QRel,_===_) grouplike renaming (_⁻¹ to _⁻¹′)
    aux00 : CZ⁻¹ ^ p-1 • CZ⁻¹ ≈ CZ • CZ⁻¹
    aux00 = begin
      CZ⁻¹ ^ p-1 • CZ⁻¹ ≈⟨ word-comm p-1 1 refl ⟩
      CZ⁻¹ • CZ⁻¹ ^ p-1 ≈⟨ refl ⟩
      CZ⁻¹ ^ p ≈⟨ lemma-^^ CZ p-1 p ⟩
      CZ ^ (p-1 Nat.* p) ≡⟨ Eq.cong (CZ ^_) (NP.*-comm p-1 p) ⟩
      CZ ^ (p Nat.* p-1) ≈⟨ sym (lemma-^^ CZ p p-1) ⟩
      (CZ ^ p) ^ p-1 ≈⟨ lemma-^-cong (CZ ^ p) ε p-1 (axiom order-CZ) ⟩
      ε ^ p-1 ≈⟨ lemma-ε^k=ε (₁₊ p-2) ⟩
      ε ≈⟨ sym (axiom order-CZ) ⟩
      CZ • CZ⁻¹ ∎

  lemma-[S⁻¹HS⁻¹]^k : let open PB ((₁₊ n) QRel,_===_) in ∀ k -> (S⁻¹ • H • S⁻¹) ^ k ≈ H ^ 3 • S ^ k • H
  lemma-[S⁻¹HS⁻¹]^k {n} k@0 = by-assoc-and (sym (axiom order-H)) auto auto
    where
    open PB ((₁₊ n) QRel,_===_)
    open PP ((₁₊ n) QRel,_===_)
    open SR word-setoid
    open Pattern-Assoc
    open Sym0-Rewriting n
  lemma-[S⁻¹HS⁻¹]^k {n} k@1 = lemma-S⁻¹HS⁻¹
  lemma-[S⁻¹HS⁻¹]^k {n} k@(₂₊ k') = begin
    (S⁻¹ • H • S⁻¹) ^ k ≈⟨ refl ⟩
    (S⁻¹ • H • S⁻¹) • (S⁻¹ • H • S⁻¹) ^ (₁₊ k') ≈⟨ cong refl refl ⟩
    (S⁻¹ • H • S⁻¹) ^ 1 • (S⁻¹ • H • S⁻¹) ^ (₁₊ k') ≈⟨ cong ( lemma-[S⁻¹HS⁻¹]^k ₁) (lemma-[S⁻¹HS⁻¹]^k (₁₊ k')) ⟩
    (H ^ 3 • S ^ 1 • H) • (H ^ 3 • S ^ (₁₊ k') • H) ≈⟨ special-assoc (□ ^ 3 • □ ^ 3) (□ ^ 2 • □ ^ 2 • □ ^ 2) auto ⟩
    (H ^ 3 • S ^ 1) • (H • H ^ 3) • S ^ (₁₊ k') • H ≈⟨ (cright cong (axiom order-H) refl) ⟩
    (H ^ 3 • S ^ 1) • (ε) • S ^ (₁₊ k') • H ≈⟨ cong refl left-unit ⟩
    (H ^ 3 • S ^ 1) • S ^ (₁₊ k') • H ≈⟨ special-assoc (□ ^ 2 • □ ^ 2) (□ • □ ^ 2 • □) auto ⟩
    H ^ 3 • S ^ k • H ∎
    where
    open PB ((₁₊ n) QRel,_===_)
    open PP ((₁₊ n) QRel,_===_)
    open SR word-setoid
    open Pattern-Assoc
    open Sym0-Rewriting n
    open Symplectic-GroupLike



  lemma-SHCZH : let open PB ((₂₊ n) QRel,_===_) in
    S • H • CZ • H ≈ H • CZ • H • CZ • S ↑ • S ↓
  lemma-SHCZH {n} = sym (begin
    H • CZ • H • CZ • S ↑ • S ≈⟨ by-assoc auto ⟩
    H • (CZ • H • CZ) • S ↑ • S ≈⟨ (cright (cleft axiom selinger-c11)) ⟩
    H • (S⁻¹ ↓ • H ↓ • S⁻¹ ↓ • CZ • H ↓ • S⁻¹ ↓ • S⁻¹ ↑) • S ↑ • S ≈⟨ special-assoc (□ • □ ^ 7 • □ ^ 2) (□ • □ ^ 6 • □ ^ 2 • □) auto ⟩
    H • (S⁻¹ ↓ • H ↓ • S⁻¹ ↓ • CZ • H ↓ • S⁻¹ ↓) • (S⁻¹ ↑ • S ↑) • S ≈⟨ refl ⟩
    H • (S⁻¹ ↓ • H ↓ • S⁻¹ ↓ • CZ • H ↓ • S⁻¹ ↓) • (S⁻¹ • S) ↑ • S ≈⟨ (cright cright cleft (lemma-cong↑ _ _ (M1P.word-comm p-1 1 M1B.refl))) ⟩
    H • (S⁻¹ ↓ • H ↓ • S⁻¹ ↓ • CZ • H ↓ • S⁻¹ ↓) • (S • S⁻¹) ↑ • S ≈⟨ (cright cright cleft lemma-cong↑ _ _ M1B.refl) ⟩
    H • (S⁻¹ ↓ • H ↓ • S⁻¹ ↓ • CZ • H ↓ • S⁻¹ ↓) • (S ^ p) ↑ • S ≈⟨ (cright cright cleft lemma-cong↑ _ _ (M1B.axiom order-S)) ⟩
    H • (S⁻¹ ↓ • H ↓ • S⁻¹ ↓ • CZ • H ↓ • S⁻¹ ↓) • ε ↑ • S ≈⟨ by-assoc auto ⟩
    H • (S⁻¹ ↓ • H ↓ • S⁻¹ ↓ • CZ • H ↓ • S⁻¹ ↓) • S ≈⟨ special-assoc (□ • □ ^ 6 • □) (□ ^ 6 • □ ^ 2) auto ⟩
    (H • S⁻¹ ↓ • H ↓ • S⁻¹ ↓ • CZ • H ↓) • S⁻¹ ↓ • S ≈⟨ (cright cleft lemma-cong↓-S^ p-1) ⟩
    (H • S⁻¹ ↓ • H ↓ • S⁻¹ ↓ • CZ • H ↓) • S⁻¹ • S ≈⟨ (cright word-comm p-1 1 refl) ⟩
    (H • S⁻¹ ↓ • H ↓ • S⁻¹ ↓ • CZ • H ↓) • S • S⁻¹ ≈⟨ (cright axiom order-S) ⟩
    (H • S⁻¹ ↓ • H ↓ • S⁻¹ ↓ • CZ • H ↓) • ε ≈⟨ right-unit ⟩
    (H • S⁻¹ ↓ • H ↓ • S⁻¹ ↓ • CZ • H ↓) ≈⟨ (cright cong (lemma-cong↓-S^ p-1) (cright cong (lemma-cong↓-S^ p-1) (cright refl))) ⟩
    (H • S⁻¹ • H • S⁻¹ • CZ • H) ≈⟨ special-assoc (□ ^ 6) (□ ^ 4 • □ ^ 2) auto ⟩
    (H • S⁻¹ • H • S⁻¹) • CZ • H ≈⟨ (cleft lemma-HS⁻¹HS⁻¹) ⟩
    (S • H) • CZ • H ≈⟨ general-comm auto ⟩
    S • H • CZ • H ∎)
    where
    open PB ((₂₊ n) QRel,_===_)
    open PP ((₂₊ n) QRel,_===_)
    module M1P = PP ((₁₊ n) QRel,_===_)
    module M1B = PB ((₁₊ n) QRel,_===_)
    open SR word-setoid
    open Pattern-Assoc
    open Commuting-Symplectic n


  lemma-SHCZH' : let open PB ((₂₊ n) QRel,_===_) in
    S ↑ • H ↑ • CZ • H ↑ ≈ H ↑ • CZ • H ↑ • CZ • S ↓ • S ↑
  lemma-SHCZH' {n} = sym (begin
    H ↑ • CZ • H ↑ • CZ • S ↓ • S ↑ ≈⟨ by-assoc auto ⟩
    H ↑ • (CZ • H ↑ • CZ) • S ↓ • S ↑ ≈⟨ (cright (cleft axiom selinger-c10)) ⟩
    H ↑ • (S⁻¹ ↑ • H ↑ • S⁻¹ ↑ • CZ • H ↑ • S⁻¹ ↑ • S⁻¹ ↓) • S ↓ • S ↑ ≈⟨ special-assoc (□ • □ ^ 7 • □ ^ 2) (□ • □ ^ 6 • □ ^ 2 • □) auto ⟩
    H ↑ • (S⁻¹ ↑ • H ↑ • S⁻¹ ↑ • CZ • H ↑ • S⁻¹ ↑) • (S⁻¹ ↓ • S ↓) • S ↑ ≈⟨ refl ⟩
    H ↑ • (S⁻¹ ↑ • H ↑ • S⁻¹ ↑ • CZ • H ↑ • S⁻¹ ↑) • (S⁻¹ • S) ↓ • S ↑ ≈⟨ (cright cright cleft ((word-comm p-1 1 refl))) ⟩
    H ↑ • (S⁻¹ ↑ • H ↑ • S⁻¹ ↑ • CZ • H ↑ • S⁻¹ ↑) • (S • S⁻¹) ↓ • S ↑ ≈⟨ (cright cright cleft refl) ⟩
    H ↑ • (S⁻¹ ↑ • H ↑ • S⁻¹ ↑ • CZ • H ↑ • S⁻¹ ↑) • (S ^ p) ↓ • S ↑ ≈⟨ (cright cright cleft (axiom order-S)) ⟩
    H ↑ • (S⁻¹ ↑ • H ↑ • S⁻¹ ↑ • CZ • H ↑ • S⁻¹ ↑) • ε ↓ • S ↑ ≈⟨ by-assoc auto ⟩
    H ↑ • (S⁻¹ ↑ • H ↑ • S⁻¹ ↑ • CZ • H ↑ • S⁻¹ ↑) • S ↑ ≈⟨ special-assoc (□ • □ ^ 6 • □) (□ ^ 6 • □ ^ 2) auto ⟩
    (H ↑ • S⁻¹ ↑ • H ↑ • S⁻¹ ↑ • CZ • H ↑) • S⁻¹ ↑ • S ↑ ≈⟨ (cright cleft refl) ⟩
    (H ↑ • S⁻¹ ↑ • H ↑ • S⁻¹ ↑ • CZ • H ↑) • S⁻¹ ↑ • S ↑ ≈⟨ (cright lemma-cong↑ _ _ (M1P.word-comm p-1 1 M1B.refl)) ⟩
    (H ↑ • S⁻¹ ↑ • H ↑ • S⁻¹ ↑ • CZ • H ↑) • S ↑ • S⁻¹ ↑ ≈⟨ (cright lemma-cong↑ _ _ (M1B.axiom order-S)) ⟩
    (H ↑ • S⁻¹ ↑ • H ↑ • S⁻¹ ↑ • CZ • H ↑) • ε ≈⟨ right-unit ⟩
    (H ↑ • S⁻¹ ↑ • H ↑ • S⁻¹ ↑ • CZ • H ↑) ≈⟨ refl ⟩
    (H ↑ • S⁻¹ ↑ • H ↑ • S⁻¹ ↑ • CZ • H ↑) ≈⟨ special-assoc (□ ^ 6) (□ ^ 4 • □ ^ 2) auto ⟩
    (H ↑ • S⁻¹ ↑ • H ↑ • S⁻¹ ↑) • CZ • H ↑ ≈⟨ (cleft lemma-cong↑ _ _ (lemma-HS⁻¹HS⁻¹)) ⟩
    (S ↑ • H ↑) • CZ • H ↑  ≈⟨ general-comm auto ⟩
    S ↑ • H ↑ • CZ • H ↑ ∎)
    where
    open PB ((₂₊ n) QRel,_===_)
    open PP ((₂₊ n) QRel,_===_)
    module M1P = PP ((₁₊ n) QRel,_===_)
    module M1B = PB ((₁₊ n) QRel,_===_)
    open SR word-setoid
    open Pattern-Assoc
    open Commuting-Symplectic n


  -- lemma-S^k↑ : let open PB ((₂₊ n) QRel,_===_) in  ∀ k ->
  --   (S ^ k) ↑ ≈ (S ↑) ^ k



  lemma-S^kHCZH' : let open PB ((₂₊ n) QRel,_===_) in  ∀ k' -> let k = suc k' in
    (S ^ k) ↑ • H ↑ • CZ • H ↑ ≈ H ↑ • CZ • H ↑ • CZ ^ k • (S ^ k) ↓ • (S ^ k) ↑
  lemma-S^kHCZH' {n} ₀ = lemma-SHCZH'
    where
    open PB ((₂₊ n) QRel,_===_)
    open PP ((₂₊ n) QRel,_===_)
    open SR word-setoid
    open Commuting-Symplectic (n)
  lemma-S^kHCZH' {n} k'@(₁₊ l) = let k = suc k' in begin
    (S ^ k) ↑ • H ↑ • CZ • H ↑ ≈⟨ assoc ⟩
    S ↑ • (S ^ k') ↑ • H ↑ • CZ • H ↑ ≈⟨ (cright lemma-S^kHCZH' l  ) ⟩
    S ↑ • H ↑ • CZ • H ↑ • CZ ^ k' • (S ^ k') ↓ • (S ^ k') ↑ ≈⟨ by-assoc auto ⟩
    (S ↑ • H ↑ • CZ • H ↑) • CZ ^ k' • (S ^ k') ↓ • (S ^ k') ↑ ≈⟨ (cleft lemma-SHCZH') ⟩
    (H ↑ • CZ • H ↑ • CZ • S ↓ • S ↑) • CZ ^ k' • (S ^ k') ↓ • (S ^ k') ↑ ≈⟨ by-assoc auto ⟩
    (H ↑ • CZ • H ↑ • CZ • S ↓) • (S ↑ • CZ ^ k') • (S ^ k') ↓ • (S ^ k') ↑ ≈⟨ (cright cleft word-comm 1 k' (sym (axiom comm-CZ-S↑))) ⟩
    (H ↑ • CZ • H ↑ • CZ • S ↓) • (CZ ^ k' • S ↑) • (S ^ k') ↓ • (S ^ k') ↑ ≈⟨ special-assoc (□ ^ 5 • □ ^ 2 • □ ^ 2) (□ ^ 4 • □ ^ 2 • □ ^ 3) auto ⟩
    (H ↑ • CZ • H ↑ • CZ) • (S ↓ • CZ ^ k') • S ↑ • (S ^ k') ↓ • (S ^ k') ↑ ≈⟨ (cright cleft word-comm 1 k' (sym (axiom comm-CZ-S↓))) ⟩
    (H ↑ • CZ • H ↑ • CZ) • (CZ ^ k' • S ↓) • S ↑ • (S ^ k') ↓ • (S ^ k') ↑ ≈⟨ trans (by-assoc auto) assoc ⟩
    (H ↑ • CZ • H ↑ • CZ • CZ ^ k') • S ↓ • (S ↑ • (S ^ k') ↓) • (S ^ k') ↑ ≈⟨ cright cright cleft (cright lemma-cong↓-S^ k') ⟩
    (H ↑ • CZ • H ↑ • CZ • CZ ^ k') • S ↓ • (S ↑ • (S ^ k')) • (S ^ k') ↑ ≈⟨ (cright cright cleft word-comm 1 k' (axiom comm-S)) ⟩
    (H ↑ • CZ • H ↑ • CZ • CZ ^ k') • S ↓ • ((S ^ k') • S ↑) • (S ^ k') ↑ ≈⟨ special-assoc (□ ^ 5 • □ • □ ^ 2 • □) (□ ^ 5 • □ ^ 2 • □ ^ 2) auto ⟩
    (H ↑ • CZ • H ↑ • CZ • CZ ^ k') • (S • S ^ k') • (S • S ^ k') ↑ ≈⟨ refl ⟩
    (H ↑ • CZ • H ↑ • CZ • CZ ^ k') • (S ^ k) • (S ^ k) ↑ ≈⟨ (cright cleft sym (lemma-cong↓-S^ k)) ⟩
    (H ↑ • CZ • H ↑ • CZ • CZ ^ k') • (S ^ k) ↓ • (S ^ k) ↑ ≈⟨ by-assoc auto ⟩
    H ↑ • CZ • H ↑ • CZ ^ k • (S ^ k) ↓ • (S ^ k) ↑ ∎
    where
    open PB ((₂₊ n) QRel,_===_)
    open PP ((₂₊ n) QRel,_===_)
    open SR word-setoid
    open Commuting-Symplectic (n)
    open Pattern-Assoc

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


  aux-S⁻¹↓-S↓ : let open PB ((₁₊ n) QRel,_===_) in S⁻¹ ↓ • S ↓ ≈ ε
  aux-S⁻¹↓-S↓ {n} = begin
    S⁻¹ • S ≈⟨ word-comm p-1 1 refl ⟩
    S • S⁻¹ ≈⟨ axiom order-S ⟩
    ε ∎
    where
    open PB ((₁₊ n) QRel,_===_)
    open PP ((₁₊ n) QRel,_===_)
    open SR word-setoid
    open Pattern-Assoc
    module M1P = PP ((n) QRel,_===_)
    module M1B = PB ((n) QRel,_===_)

  lemma-comm-S-Ex' : let open PB ((₂₊ n) QRel,_===_) in
    S ↓ • H ↓ • CZ • H • H ↑ • CZ • H ↑ ≈ H • CZ • H • H ↑ • CZ • H ↑ • S ↑
  lemma-comm-S-Ex' {n}  = begin
    S • H • CZ • H • H ↑ • CZ • H ↑ ≈⟨ by-assoc auto ⟩
    (S • H • CZ • H) • H ↑ • CZ • H ↑ ≈⟨ (cleft lemma-SHCZH) ⟩
    (H • CZ • H • CZ • S ↑ • S) • H ↑ • CZ • H ↑ ≈⟨ general-comm  auto ⟩
    (H • CZ • H • CZ • S ↑ • H ↑) • S ↓ • CZ • H ↑ ≈⟨ (cright general-comm  auto) ⟩
    (H • CZ • H • CZ • S ↑ • H ↑) • CZ • H ↑ • S ↓ ≈⟨ by-assoc auto ⟩
    (H • CZ • H • CZ) • (S ↑ • H ↑ • CZ • H ↑) • S ↓ ≈⟨ (cright (cleft lemma-SHCZH')) ⟩
    (H • CZ • H • CZ) • (H ↑ • CZ • H ↑ • CZ • S ↓ • S ↑) • S ↓ ≈⟨ by-assoc auto ⟩
    (H • CZ • H) • (CZ • H ↑ • CZ) • H ↑ • CZ • S ↓ • S ↑ • S ↓ ≈⟨ (cright (cleft axiom selinger-c10)) ⟩
    (H • CZ • H) • (S⁻¹ ↑ • H ↑ • S⁻¹ ↑ • CZ • H ↑ • S⁻¹ ↑ • S⁻¹ ↓) • H ↑ • CZ • S ↓ • S ↑ • S ↓ ≈⟨ (cright cright general-comm auto) ⟩
    (H • CZ • H) • (S⁻¹ ↑ • H ↑ • S⁻¹ ↑ • CZ • H ↑ • S⁻¹ ↑ • S⁻¹ ↓) • S ↓ • H ↑ • CZ • S ↑ • S ↓ ≈⟨ cright special-assoc (□ ^ 7 • □ ^ 5) (□ ^ 6 • □ ^ 2 • □ ^ 4) auto ⟩
    (H • CZ • H) • (S⁻¹ ↑ • H ↑ • S⁻¹ ↑ • CZ • H ↑ • S⁻¹ ↑) • (S⁻¹ ↓ • S ↓) • H ↑ • CZ • S ↑ • S ↓ ≈⟨ (cright cright cleft (cleft lemma-cong↓-S^ (₁₊ p-2))) ⟩
    (H • CZ • H) • (S⁻¹ ↑ • H ↑ • S⁻¹ ↑ • CZ • H ↑ • S⁻¹ ↑) • (S⁻¹ • S) • H ↑ • CZ • S ↑ • S ↓ ≈⟨ (cright cright cleft word-comm p-1 1 refl) ⟩
    (H • CZ • H) • (S⁻¹ ↑ • H ↑ • S⁻¹ ↑ • CZ • H ↑ • S⁻¹ ↑) • (S • S⁻¹) • H ↑ • CZ • S ↑ • S ↓ ≈⟨ (cright cright cleft axiom order-S) ⟩
    (H • CZ • H) • (S⁻¹ ↑ • H ↑ • S⁻¹ ↑ • CZ • H ↑ • S⁻¹ ↑) • ε • H ↑ • CZ • S ↑ • S ↓ ≈⟨ (cright cright left-unit) ⟩
    (H • CZ • H) • (S⁻¹ ↑ • H ↑ • S⁻¹ ↑ • CZ • H ↑ • S⁻¹ ↑) • H ↑ • CZ • S ↑ • S ↓ ≈⟨ (cright special-assoc (□ ^ 6 • □ ^ 4) (□ ^ 4 • □ ^ 3 • □ ^ 3) auto) ⟩
    (H • CZ • H) • (S⁻¹ ↑ • H ↑ • S⁻¹ ↑ • CZ) • (H ↑ • S⁻¹ ↑ • H ↑) • CZ • S ↑ • S ↓ ≈⟨ (cright (cright cright cright axiom comm-S)) ⟩
    (H • CZ • H) • (S⁻¹ ↑ • H ↑ • S⁻¹ ↑ • CZ) • (H ↑ • S⁻¹ ↑ • H ↑) • CZ • S ↓ • S ↑ ≈⟨ (cright (cright (cleft lemma-cong↑ _ _ lemma-HS⁻¹H))) ⟩ 
    (H • CZ • H) • (S⁻¹ ↑ • H ↑ • S⁻¹ ↑ • CZ) • (S • H • S) ↑ • CZ • S ↓ • S ↑ ≈⟨ (cright cleft cright cright (cleft lemma-cong↑-S^ (₁₊ p-2))) ⟩
    (H • CZ • H) • (S⁻¹ ↑ • H ↑ • (S ↑) ^ p-1 • CZ) • (S • H • S) ↑ • CZ • S ↓ • S ↑ ≈⟨ (cright cleft cright cright word-comm p-1 1 (sym (axiom comm-CZ-S↑))) ⟩
    (H • CZ • H) • (S⁻¹ ↑ • H ↑ • CZ • (S ↑) ^ p-1) • (S • H • S) ↑ • CZ • S ↓ • S ↑ ≈⟨ (cright special-assoc (□ ^ 4 • □ ^ 3 • □ ^ 3) (□ ^ 3 • □ ^ 2 • □ ^ 5) auto) ⟩
    (H • CZ • H) • (S⁻¹ ↑ • H ↑ • CZ) • (S ↑ ^ p-1 • S ↑) • H ↑ • S ↑ • CZ • S ↓ • S ↑ ≈⟨ (cright cright cleft word-comm p-1 1 refl) ⟩
    (H • CZ • H) • (S⁻¹ ↑ • H ↑ • CZ) • (S ↑ • S ↑ ^ p-1) • H ↑ • S ↑ • CZ • S ↓ • S ↑ ≈⟨ (cright cright cleft (cright sym (lemma-cong↑-S^ (₁₊ p-2)))) ⟩
    (H • CZ • H) • (S⁻¹ ↑ • H ↑ • CZ) • (S ↑ • S⁻¹ ↑) • H ↑ • S ↑ • CZ • S ↓ • S ↑ ≈⟨ (cright cright cleft axiom (cong↑ order-S)) ⟩
    (H • CZ • H) • (S⁻¹ ↑ • H ↑ • CZ) • (ε) • H ↑ • S ↑ • CZ • S ↓ • S ↑ ≈⟨ (cright cright left-unit) ⟩
    (H • CZ • H) • (S⁻¹ ↑ • H ↑ • CZ) • H ↑ • S ↑ • CZ • S ↓ • S ↑ ≈⟨ (cright special-assoc (□ ^ 3 • □ ^ 5) (□ ^ 4 • □ ^ 4) auto) ⟩
    (H • CZ • H) • (S⁻¹ ↑ • H ↑ • CZ • H ↑) • S ↑ • CZ • S ↓ • S ↑ ≈⟨ (cright cleft lemma-S^kHCZH' p-2) ⟩
    (H • CZ • H) • (H ↑ • CZ • H ↑ • CZ ^ p-1 • S⁻¹ ↓ • S⁻¹ ↑) • S ↑ • CZ • S ↓ • S ↑ ≈⟨ cright special-assoc (□ ^ 6 • □ ^ 4) (□ ^ 5 • □ ^ 2 • □ ^ 3) auto ⟩
    (H • CZ • H) • (H ↑ • CZ • H ↑ • CZ ^ p-1 • S⁻¹ ↓) • (S⁻¹ ↑ • S ↑) • CZ • S ↓ • S ↑ ≈⟨ (cright cright (cleft lemma-cong↑ _ _ (M1P.word-comm p-1 1 M1B.refl))) ⟩
    (H • CZ • H) • (H ↑ • CZ • H ↑ • CZ ^ p-1 • S⁻¹ ↓) • (S ↑ • S⁻¹ ↑) • CZ • S ↓ • S ↑ ≈⟨ (cright cright cleft lemma-cong↑ _ _  (M1B.axiom order-S)) ⟩
    (H • CZ • H) • (H ↑ • CZ • H ↑ • CZ ^ p-1 • S⁻¹ ↓) • ε • CZ • S ↓ • S ↑ ≈⟨ (cright cright left-unit) ⟩
    (H • CZ • H) • (H ↑ • CZ • H ↑ • CZ ^ p-1 • S⁻¹ ↓) • CZ • S ↓ • S ↑ ≈⟨ (cright cright general-comm auto) ⟩
    (H • CZ • H) • (H ↑ • CZ • H ↑ • CZ ^ p-1 • S⁻¹ ↓) • S ↓ • CZ • S ↑ ≈⟨ cright special-assoc (□ ^ 5 • □ ^ 3) (□ ^ 4 • □ ^ 2 • □ ^ 2) auto ⟩
    (H • CZ • H) • (H ↑ • CZ • H ↑ • CZ ^ p-1) • (S⁻¹ ↓ • S ↓) • CZ • S ↑ ≈⟨ (cright cright cleft aux-S⁻¹↓-S↓) ⟩
    (H • CZ • H) • (H ↑ • CZ • H ↑ • CZ ^ p-1) • ε • CZ • S ↑ ≈⟨ (cright cright left-unit) ⟩
    (H • CZ • H) • (H ↑ • CZ • H ↑ • CZ ^ p-1) • CZ • S ↑ ≈⟨ (cright special-assoc (□ ^ 4 • □ ^ 2) (□ ^ 3 • □ ^ 2 • □) auto) ⟩
    (H • CZ • H) • (H ↑ • CZ • H ↑) • (CZ ^ p-1 • CZ) • S ↑ ≈⟨ (cright cright cleft word-comm p-1 1 refl) ⟩
    (H • CZ • H) • (H ↑ • CZ • H ↑) • (CZ • CZ ^ p-1) • S ↑ ≈⟨ (cright cright cleft axiom order-CZ) ⟩
    (H • CZ • H) • (H ↑ • CZ • H ↑) • (ε) • S ↑ ≈⟨ by-assoc auto ⟩
    H • CZ • H • H ↑ • CZ • H ↑ • S ↑ ∎
    where
    open PB ((₂₊ n) QRel,_===_)
    open PP ((₂₊ n) QRel,_===_)
    open SR word-setoid
    open Commuting-Symplectic (n)
    open Pattern-Assoc
    module M1P = PP ((₁₊ n) QRel,_===_)
    module M1B = PB ((₁₊ n) QRel,_===_)


  aux-CZ⁻¹-CZ : let open PB ((₂₊ n) QRel,_===_) in CZ^ ₋₁ • CZ ≈ ε
  aux-CZ⁻¹-CZ {n} = begin
    CZ^ ₋₁ • CZ ≈⟨ word-comm (toℕ ₋₁) 1 refl ⟩
    CZ • CZ^ ₋₁ ≡⟨ Eq.cong (CZ •_) ( Eq.cong (CZ ^_) (toℕ-fromℕ<  (NP.n<1+n p-1))) ⟩
    CZ • CZ ^ p-1 ≈⟨ axiom order-CZ ⟩
    ε ∎
    where
    open PB ((₂₊ n) QRel,_===_)
    open PP ((₂₊ n) QRel,_===_)
    open SR word-setoid
    open Commuting-Symplectic (n)
    open Sym0-Rewriting (suc n)
    open Lemmas-2Q n
    open Pattern-Assoc

  lemma-order-ₕ|ₕ : let open PB ((₂₊ n) QRel,_===_) in
    ₕ|ₕ ^ 2 ≈ ε
  lemma-order-ₕ|ₕ {n} = begin
    ₕ|ₕ ^ 2 ≈⟨ general-comm auto ⟩
    H • (CZ • HH) • CZ • H ≈⟨ (cright cleft lemma-semi-CZ-HH↓) ⟩
    H • (HH • CZ^ ₋₁) • CZ • H ≈⟨ special-assoc (□ • □ ^ 2 • □ ^ 2) (□ ^ 2 • □ ^ 2 • □) auto ⟩
    (H • HH) • (CZ^ ₋₁ • CZ) • H ≈⟨ (cright cleft aux-CZ⁻¹-CZ) ⟩
    (H • HH) • (ε) • H ≈⟨ rewrite-sym0 100 auto ⟩
    ε ∎
    where
    open PB ((₂₊ n) QRel,_===_)
    open PP ((₂₊ n) QRel,_===_)
    open SR word-setoid
    open Commuting-Symplectic (n)
    open Sym0-Rewriting (suc n)
    open Lemmas-2Q n
    open Pattern-Assoc

  lemma-order-ʰ|ʰ : let open PB ((₂₊ n) QRel,_===_) in
    ʰ|ʰ ^ 2 ≈ ε
  lemma-order-ʰ|ʰ {n} = begin
    ʰ|ʰ ^ 2 ≈⟨ general-comm auto ⟩
    H ↑ • (CZ • HH ↑) • CZ • H ↑ ≈⟨ (cright cleft lemma-semi-CZ-HH↑) ⟩
    H ↑ • (HH ↑ • CZ^ ₋₁) • CZ • H ↑ ≈⟨ special-assoc (□ • □ ^ 2 • □ ^ 2) (□ ^ 2 • □ ^ 2 • □) auto ⟩
    (H ↑ • HH ↑) • (CZ^ ₋₁ • CZ) • H ↑ ≈⟨ (cright cleft aux-CZ⁻¹-CZ) ⟩
    (H ↑ • HH ↑) • (ε) • H ↑ ≈⟨ rewrite-sym0 100 auto ⟩
    ε ∎
    where
    open PB ((₂₊ n) QRel,_===_)
    open PP ((₂₊ n) QRel,_===_)
    open SR word-setoid
    open Commuting-Symplectic (n)
    open Sym0-Rewriting (suc n)
    open Lemmas-2Q n
    open Pattern-Assoc

  lemma-comm-S↑-Ex' : let open PB ((₂₊ n) QRel,_===_) in
    S ↑ • H ↑ • CZ • H ↑ • H ↓ • CZ • H ↓ ≈ H ↑ • CZ • H ↑ • H ↓ • CZ • H ↓ • S ↓
  lemma-comm-S↑-Ex' {n}  = bbc (H • CZ • H • H ↑ • CZ • H ↑) (H • CZ • H • H ↑ • CZ • H ↑) aux0
    where
    open PB ((₂₊ n) QRel,_===_)
    open PP ((₂₊ n) QRel,_===_)
    open SR word-setoid
    open Commuting-Symplectic (n)
    open Sym0-Rewriting (suc n)    
    
    open Symplectic-GroupLike
    open Basis-Change _ ((₂₊ n) QRel,_===_) grouplike

    aux0 : (H • CZ • H • H ↑ • CZ • H ↑) • (S ↑ • H ↑ • CZ • H ↑ • H • CZ • H) • H • CZ • H • H ↑ • CZ • H ↑ ≈
      (H • CZ • H • H ↑ • CZ • H ↑ ) • (H ↑ • CZ • H ↑ • H • CZ • H • S) • H • CZ • H • H ↑ • CZ • H ↑
    aux0 = begin
      (H • CZ • H • H ↑ • CZ • H ↑) • (S ↑ • H ↑ • CZ • H ↑ • H • CZ • H) • H • CZ • H • H ↑ • CZ • H ↑  ≈⟨ general-comm auto ⟩
      (H • CZ • H • H ↑ • CZ • H ↑) • (S ↑ • H ↑ • CZ • H ↑) • (H • CZ • H) ^ 2 • H ↑ • CZ • H ↑  ≈⟨ (cright cright cleft lemma-order-ₕ|ₕ) ⟩
      (H • CZ • H • H ↑ • CZ • H ↑) • (S ↑ • H ↑ • CZ • H ↑) • ε • H ↑ • CZ • H ↑  ≈⟨ general-comm auto ⟩
      (H • CZ • H • H ↑ • CZ • H ↑) • S ↑ • (H ↑ • CZ • H ↑) ^ 2  ≈⟨ (cright cright lemma-order-ʰ|ʰ) ⟩
      (H • CZ • H • H ↑ • CZ • H ↑) • S ↑ • ε  ≈⟨ general-comm auto ⟩
      H • CZ • H • H ↑ • CZ • H ↑ • S ↑  ≈⟨ sym lemma-comm-S-Ex' ⟩
      S • H • CZ • H • H ↑ • CZ • H ↑ ≈⟨ sym left-unit ⟩
      ε • S • H • CZ • H • H ↑ • CZ • H ↑ ≈⟨ (cleft sym lemma-order-ₕ|ₕ) ⟩
      (H • CZ • H) ^ 2 • S • H • CZ • H • H ↑ • CZ • H ↑ ≈⟨ general-comm auto ⟩
      (H • CZ • H) • ε • H • CZ • H • S • H • CZ • H • H ↑ • CZ • H ↑ ≈⟨ (cright cleft sym lemma-order-ʰ|ʰ) ⟩
      (H • CZ • H) • (H ↑ • CZ • H ↑) ^ 2 • H • CZ • H • S • H • CZ • H • H ↑ • CZ • H ↑ ≈⟨ general-comm auto ⟩
      (H • CZ • H • H ↑ • CZ • H ↑ ) • (H ↑ • CZ • H ↑ • H • CZ • H • S) • H • CZ • H • H ↑ • CZ • H ↑ ∎


  lemma-comm-S↑-Ex'' : let open PB ((₂₊ n) QRel,_===_) in
    S ↑ • H ↑ • CZ • H ↑ • H ↓ • CZ • H ↓ ≈ (H ↑ • CZ • H ↑ • H ↓ • CZ • H ↓) • S ↓
  lemma-comm-S↑-Ex'' {n}  = begin
    S ↑ • H ↑ • CZ • H ↑ • H ↓ • CZ • H ↓ ≈⟨ lemma-comm-S↑-Ex' ⟩
    H ↑ • CZ • H ↑ • H ↓ • CZ • H ↓ • S ↓ ≈⟨ by-assoc auto ⟩
    (H ↑ • CZ • H ↑ • H ↓ • CZ • H ↓) • S ↓ ∎
    where
    open PB ((₂₊ n) QRel,_===_)
    open PP ((₂₊ n) QRel,_===_)
    open SR word-setoid
    open Commuting-Symplectic (n)
    open Sym0-Rewriting (suc n)    
    
    open Symplectic-GroupLike
    open Basis-Change _ ((₂₊ n) QRel,_===_) grouplike


  lemma-comm-Ex-S : let open PB ((₂₊ n) QRel,_===_) in
    S ↑ • Ex ≈ Ex • S
  lemma-comm-Ex-S {n@0}  = begin
    S ↑ • CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑ ≈⟨ general-comm auto ⟩
    (CZ • H) • (S ↑ • H ↑ • CZ • H ↑ • H ↓ • CZ • H ↓) • H ↑ ≈⟨ (cright (cleft lemma-comm-S↑-Ex')) ⟩
    (CZ • H) • (H ↑ • CZ • H ↑ • H ↓ • CZ • H ↓ • S ↓) • H ↑ ≈⟨ general-comm auto ⟩
    Ex • S ∎
    where
    open PB ((₂₊ n) QRel,_===_)
    open PP ((₂₊ n) QRel,_===_)
    open SR word-setoid
    open Commuting-Symplectic n
  lemma-comm-Ex-S {n@(suc _)}  = begin
    S ↑ • CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑ ≈⟨ general-comm auto ⟩
    (CZ • H) • (S ↑ • H ↑ • CZ • H ↑ • H ↓ • CZ • H ↓) • H ↑ ≈⟨ (cright (cleft lemma-comm-S↑-Ex')) ⟩
    (CZ • H) • (H ↑ • CZ • H ↑ • H ↓ • CZ • H ↓ • S ↓) • H ↑ ≈⟨ general-comm auto ⟩
    Ex • S ∎
    where
    open PB ((₂₊ n) QRel,_===_)
    open PP ((₂₊ n) QRel,_===_)
    open SR word-setoid
    open Commuting-Symplectic n


  lemma-Ex-Sᵏ : ∀ k → let open PB ((₂₊ n) QRel,_===_) in 
    
    Ex • S ^ k ≈ S ↑ ^ k • Ex
    
  lemma-Ex-Sᵏ {n} ₀ = trans right-unit (sym left-unit)
    where
    open PB ((₂₊ n) QRel,_===_)
  lemma-Ex-Sᵏ {n} ₁ = sym lemma-comm-Ex-S
    where
    open PB ((₂₊ n) QRel,_===_)
  lemma-Ex-Sᵏ {n} (₂₊ k) = begin
    Ex • S • S ^ ₁₊ k ≈⟨ sym assoc ⟩
    (Ex • S) • S ^ ₁₊ k ≈⟨ cong (sym lemma-comm-Ex-S) refl ⟩
    (S ↑ • Ex) • S ^ ₁₊ k ≈⟨ assoc ⟩
    S ↑ • Ex • S ^ ₁₊ k ≈⟨ cong refl (lemma-Ex-Sᵏ (₁₊ k)) ⟩
    S ↑ • S ↑ ^ ₁₊ k • Ex ≈⟨ sym assoc ⟩
    ((S ↑) • (S ↑) ^ ₁₊ k) • Ex ∎
    where
    open PB ((₂₊ n) QRel,_===_)
    open PP ((₂₊ n) QRel,_===_)
    open SR word-setoid




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

  aux-comm-S⁻¹↑-S : let open PB ((₂₊ n) QRel,_===_) in S⁻¹ ↑ • S ≈ S • S⁻¹ ↑
  aux-comm-S⁻¹↑-S {n} = begin
    S⁻¹ ↑ • S ≈⟨ (cleft lemma-cong↑-S^ (₁₊ p-2)) ⟩
    S ↑ ^ p-1 • S ≈⟨ word-comm p-1 1 (axiom comm-S) ⟩
    S • S ↑ ^ p-1 ≈⟨ (cright sym (lemma-cong↑-S^ (₁₊ p-2))) ⟩
    S • S⁻¹ ↑ ∎
    where
    open PB ((₂₊ n) QRel,_===_)
    open PP ((₂₊ n) QRel,_===_)
    open SR word-setoid

  lemma-CZHCZ^k : let open PB ((₂₊ n) QRel,_===_) in ∀ k' -> let k = suc k' in
    CZ • H • CZ ^ k ≈ (S⁻¹ • H • S⁻¹) ^ k • CZ • H • S⁻¹ ^ k • S⁻¹ ↑ ^ k
  lemma-CZHCZ^k {n} k'@0 = let k = suc k' in begin
    CZ • H • CZ ^ k ≈⟨ axiom selinger-c11 ⟩
    S⁻¹ • H • S⁻¹ • CZ • H • S⁻¹ • S⁻¹ ↑ ≈⟨ special-assoc (□ ^ 7) (□ ^ 3 • □ ^ 4) auto ⟩
    (S⁻¹ • H • S⁻¹) ^ k • CZ • H • S⁻¹ ^ k • S⁻¹ ↑ ^ k ∎
    where
    open PB ((₂₊ n) QRel,_===_)
    open PP ((₂₊ n) QRel,_===_)
    open SR word-setoid
    open Commuting-Symplectic (n)
    open Sym0-Rewriting (suc n)
    open Pattern-Assoc
  lemma-CZHCZ^k {n} k'@(suc k'') = let k = suc k' in begin
    CZ • H • CZ ^ k ≈⟨ special-assoc (□ ^ 4) (□ ^ 3 • □) auto ⟩
    (CZ • H • CZ) • CZ ^ k' ≈⟨ (cleft lemma-CZHCZ^k 0) ⟩
    ((S⁻¹ • H • S⁻¹) • CZ • H • S⁻¹ • S⁻¹ ↑) • CZ ^ k' ≈⟨ special-assoc (□ ^ 5 • □) (□ ^ 4 • □ ^ 2) auto ⟩
    ((S⁻¹ • H • S⁻¹) • CZ • H • S⁻¹) • S⁻¹ ↑ • CZ ^ k' ≈⟨ (cright cleft lemma-cong↑-S^ (₁₊ p-2)) ⟩
    ((S⁻¹ • H • S⁻¹) • CZ • H • S⁻¹) • S ↑ ^ p-1 • CZ ^ k' ≈⟨ (cright word-comm p-1 k' (sym (axiom comm-CZ-S↑))) ⟩
    ((S⁻¹ • H • S⁻¹) • CZ • H • S⁻¹) • CZ ^ k' • S ↑ ^ p-1 ≈⟨ special-assoc (□ ^ 4 • □ ^ 2) (□ ^ 3 • □ ^ 2 • □) auto ⟩
    ((S⁻¹ • H • S⁻¹) • CZ • H) • (S⁻¹ • CZ ^ k') • S ↑ ^ p-1 ≈⟨ (cright cleft word-comm p-1 k' (sym (axiom comm-CZ-S↓))) ⟩
    ((S⁻¹ • H • S⁻¹) • CZ • H) • (CZ ^ k' • S⁻¹) • S ↑ ^ p-1 ≈⟨ special-assoc (□ ^ 3 • □ ^ 2 • □ ^ 2) (□  • □ ^ 3 • □ ^ 3) auto ⟩
    (S⁻¹ • H • S⁻¹) • (CZ • H • CZ ^ k') • S⁻¹ • S ↑ ^ p-1 ≈⟨ (cright cleft lemma-CZHCZ^k k'') ⟩
    (S⁻¹ • H • S⁻¹) • ((S⁻¹ • H • S⁻¹) ^ k' • CZ • H • S⁻¹ ^ k' • S⁻¹ ↑ ^ k') • S⁻¹ • S ↑ ^ p-1 ≈⟨ special-assoc (□ • □ ^ 5 • □ ^ 2) (□ ^ 2 • □ • □ • □ • □ ^ 2 • □) auto ⟩
    ((S⁻¹ • H • S⁻¹) ^ k) • CZ • H • S⁻¹ ^ k' • (S⁻¹ ↑ ^ k' • S⁻¹) • S ↑ ^ p-1 ≈⟨ (cright cright cright cright cleft word-comm k' p-1 aux-comm-S⁻¹↑-S) ⟩
    ((S⁻¹ • H • S⁻¹) ^ k) • CZ • H • S⁻¹ ^ k' • (S⁻¹ • S⁻¹ ↑ ^ k') • S ↑ ^ p-1 ≈⟨ special-assoc (□ • □ • □ • □ • □ ^ 2 • □) (□ • □ • □ • □ ^ 2 • □ ^ 2) auto ⟩
    ((S⁻¹ • H • S⁻¹) ^ k) • CZ • H • (S⁻¹ ^ k' • S⁻¹) • S⁻¹ ↑ ^ k' • S ↑ ^ p-1 ≈⟨ (cright cright cright cright (cright sym (lemma-cong↑-S^ (₁₊ p-2)))) ⟩
    ((S⁻¹ • H • S⁻¹) ^ k) • CZ • H • (S⁻¹ ^ k' • S⁻¹) • S⁻¹ ↑ ^ k' • S⁻¹ ↑ ≈⟨ (cright cright cright cright word-comm k' 1 refl) ⟩
    ((S⁻¹ • H • S⁻¹) ^ k) • CZ • H • (S⁻¹ ^ k' • S⁻¹) • S⁻¹ ↑ • S⁻¹ ↑ ^ k' ≈⟨ refl ⟩
    ((S⁻¹ • H • S⁻¹) ^ k) • CZ • H • (S⁻¹ ^ k' • S⁻¹) • S⁻¹ ↑ ^ k ≈⟨ (cright cright cright (cleft word-comm k' 1 refl)) ⟩
    ((S⁻¹ • H • S⁻¹) ^ k) • CZ • H • (S⁻¹ • S⁻¹ ^ k') • S⁻¹ ↑ ^ k ≈⟨ refl ⟩
    (S⁻¹ • H • S⁻¹) ^ k • CZ • H • S⁻¹ ^ k • S⁻¹ ↑ ^ k ∎
    where
    open PB ((₂₊ n) QRel,_===_)
    open PP ((₂₊ n) QRel,_===_)
    open SR word-setoid
    open Commuting-Symplectic (n)
    open Sym0-Rewriting (suc n)
    open Pattern-Assoc


  lemma-CZHCZ^-k : let open PB ((₂₊ n) QRel,_===_) in ∀ k' -> let k = toℕ k' in
    CZ • H • CZ^ k' ≈ (S⁻¹ • H • S⁻¹) ^ k • CZ • H • S⁻¹ ^ k • S⁻¹ ↑ ^ k
  lemma-CZHCZ^-k {n} k'@₀ = begin
    CZ • H • CZ^ k' ≈⟨ by-assoc auto ⟩
    (S⁻¹ • H • S⁻¹) ^ k • CZ • H • S⁻¹ ^ k • S⁻¹ ↑ ^ k ∎
    where
    open PB ((₂₊ n) QRel,_===_)
    open PP ((₂₊ n) QRel,_===_)
    open SR word-setoid
    open Commuting-Symplectic (n)
    open Sym0-Rewriting (suc n)
    open Pattern-Assoc
    k = toℕ k'
  lemma-CZHCZ^-k {n} k'@(₁₊ a) = begin
    CZ • H • CZ^ k' ≈⟨ lemma-CZHCZ^k (toℕ a) ⟩
    (S⁻¹ • H • S⁻¹) ^ k • CZ • H • S⁻¹ ^ k • S⁻¹ ↑ ^ k ∎
    where
    open PB ((₂₊ n) QRel,_===_)
    open PP ((₂₊ n) QRel,_===_)
    open SR word-setoid
    open Commuting-Symplectic (n)
    open Sym0-Rewriting (suc n)
    open Pattern-Assoc
    k = toℕ k'




  lemma-CZH↑CZ^k : let open PB ((₂₊ n) QRel,_===_) in ∀ k' -> let k = suc k' in
    CZ • H ↑ • CZ ^ k ≈ (S⁻¹ ↑ • H ↑ • S⁻¹ ↑) ^ k • CZ • H ↑ • S⁻¹ ↑ ^ k • S⁻¹ ^ k
  lemma-CZH↑CZ^k {n} k'@0 = let k = suc k' in begin
    CZ • H ↑ • CZ ^ k ≈⟨ axiom selinger-c10 ⟩
    S⁻¹ ↑ • H ↑ • S⁻¹ ↑ • CZ • H ↑ • S⁻¹ ↑ • S⁻¹ ≈⟨ special-assoc (□ ^ 7) (□ ^ 3 • □ ^ 4) auto ⟩
    (S⁻¹ ↑ • H ↑ • S⁻¹ ↑) ^ k • CZ • H ↑ • S⁻¹ ↑ ^ k • S⁻¹ ^ k ∎
    where
    open PB ((₂₊ n) QRel,_===_)
    open PP ((₂₊ n) QRel,_===_)
    open SR word-setoid
    open Commuting-Symplectic (n)
    open Sym0-Rewriting (suc n)
    open Pattern-Assoc
  lemma-CZH↑CZ^k {n} k'@(suc k'') = let k = suc k' in begin
    CZ • H ↑ • CZ ^ k ≈⟨ special-assoc (□ ^ 4) (□ ^ 3 • □) auto ⟩
    (CZ • H ↑ • CZ) • CZ ^ k' ≈⟨ (cleft lemma-CZH↑CZ^k 0) ⟩
    ((S⁻¹ ↑ • H ↑ • S⁻¹ ↑) • CZ • H ↑ • S⁻¹ ↑ • S⁻¹) • CZ ^ k' ≈⟨ special-assoc (□ ^ 5 • □) (□ ^ 4 • □ ^ 2) auto ⟩
    ((S⁻¹ ↑ • H ↑ • S⁻¹ ↑) • CZ • H ↑ • S⁻¹ ↑) • S⁻¹ • CZ ^ k' ≈⟨ (cright cleft refl ) ⟩
    ((S⁻¹ ↑ • H ↑ • S⁻¹ ↑) • CZ • H ↑ • S⁻¹ ↑) • S ^ p-1 • CZ ^ k' ≈⟨ (cright word-comm p-1 k' (sym (axiom comm-CZ-S↓))) ⟩
    ((S⁻¹ ↑ • H ↑ • S⁻¹ ↑) • CZ • H ↑ • S⁻¹ ↑) • CZ ^ k' • S ^ p-1 ≈⟨ special-assoc (□ ^ 4 • □ ^ 2) (□ ^ 3 • □ ^ 2 • □) auto ⟩
    ((S⁻¹ ↑ • H ↑ • S⁻¹ ↑) • CZ • H ↑) • (S⁻¹ ↑ • CZ ^ k') • S ^ p-1 ≈⟨ (cright cleft (cleft lemma-cong↑-S^ (₁₊ p-2))) ⟩
    ((S⁻¹ ↑ • H ↑ • S⁻¹ ↑) • CZ • H ↑) • (S ↑ ^ p-1 • CZ ^ k') • S ^ p-1 ≈⟨ (cright cleft word-comm p-1 k' (sym (axiom comm-CZ-S↑))) ⟩
    ((S⁻¹ ↑ • H ↑ • S⁻¹ ↑) • CZ • H ↑) • (CZ ^ k' • S ↑ ^ p-1) • S ^ p-1 ≈⟨ (cright cleft (cright sym (lemma-cong↑-S^ (₁₊ p-2)))) ⟩
    ((S⁻¹ ↑ • H ↑ • S⁻¹ ↑) • CZ • H ↑) • (CZ ^ k' • S⁻¹ ↑) • S ^ p-1 ≈⟨ special-assoc (□ ^ 3 • □ ^ 2 • □ ^ 2) (□  • □ ^ 3 • □ ^ 3) auto ⟩
    (S⁻¹ ↑ • H ↑ • S⁻¹ ↑) • (CZ • H ↑ • CZ ^ k') • S⁻¹ ↑ • S ^ p-1 ≈⟨ (cright (cleft lemma-CZH↑CZ^k k'')) ⟩
    (S⁻¹ ↑ • H ↑ • S⁻¹ ↑) • ((S⁻¹ ↑ • H ↑ • S⁻¹ ↑) ^ k' • CZ • H ↑ • S⁻¹ ↑ ^ k' • S⁻¹ ^ k') • S⁻¹ ↑ • S ^ p-1 ≈⟨ special-assoc (□ • □ ^ 5 • □ ^ 2) (□ ^ 2 • □ • □ • □ • □ ^ 2 • □) auto ⟩
    ((S⁻¹ ↑ • H ↑ • S⁻¹ ↑) ^ k) • CZ • H ↑ • S⁻¹ ↑ ^ k' • (S⁻¹ ^ k' • S⁻¹ ↑) • S ^ p-1 ≈⟨ (cright cright cright cright cleft word-comm k' 1 (lemma-comm-Sᵏ-w↑ p-1 S⁻¹)) ⟩
    ((S⁻¹ ↑ • H ↑ • S⁻¹ ↑) ^ k) • CZ • H ↑ • S⁻¹ ↑ ^ k' • (S⁻¹ ↑ • S⁻¹ ^ k') • S ^ p-1 ≈⟨ special-assoc (□ • □ • □ • □ • □ ^ 2 • □) (□ • □ • □ • □ ^ 2 • □ ^ 2) auto ⟩
    ((S⁻¹ ↑ • H ↑ • S⁻¹ ↑) ^ k) • CZ • H ↑ • (S⁻¹ ↑ ^ k' • S⁻¹ ↑) • S⁻¹ ^ k' • S ^ p-1 ≈⟨ (cright cright cright cright (cright sym ( refl))) ⟩
    ((S⁻¹ ↑ • H ↑ • S⁻¹ ↑) ^ k) • CZ • H ↑ • (S⁻¹ ↑ ^ k' • S⁻¹ ↑) • S⁻¹ ^ k' • S⁻¹ ≈⟨ (cright cright cright cright word-comm k' 1 refl) ⟩
    ((S⁻¹ ↑ • H ↑ • S⁻¹ ↑) ^ k) • CZ • H ↑ • (S⁻¹ ↑ ^ k' • S⁻¹ ↑) • S⁻¹ • S⁻¹ ^ k' ≈⟨ refl ⟩
    ((S⁻¹ ↑ • H ↑ • S⁻¹ ↑) ^ k) • CZ • H ↑ • (S⁻¹ ↑ ^ k' • S⁻¹ ↑) • S⁻¹ ^ k ≈⟨ (cright cright cright (cleft word-comm k' 1 refl)) ⟩
    ((S⁻¹ ↑ • H ↑ • S⁻¹ ↑) ^ k) • CZ • H ↑ • (S⁻¹ ↑ • S⁻¹ ↑ ^ k') • S⁻¹ ^ k ≈⟨ refl ⟩
    (S⁻¹ ↑ • H ↑ • S⁻¹ ↑) ^ k • CZ • H ↑ • S⁻¹ ↑ ^ k • S⁻¹ ^ k ∎
    where
    open PB ((₂₊ n) QRel,_===_)
    open PP ((₂₊ n) QRel,_===_)
    open SR word-setoid
    open Commuting-Symplectic (n)
    open Sym0-Rewriting (suc n)
    open Pattern-Assoc



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

  lemma-SHSH' : let open PB ((₁₊ n) QRel,_===_) in

    S • H • S • H ≈ H ^ 3 • S ^ p-1

  lemma-SHSH' {n} = begin
    (S • H • S • H) ≈⟨ trans (sym right-unit) (cright sym (axiom order-S)) ⟩
    (S • H • S • H) • S • S ^ p-1 ≈⟨ (cright cright sym left-unit) ⟩
    (S • H • S • H) • S • ε • S ^ p-1 ≈⟨ (cright cright cleft sym (axiom order-H)) ⟩
    (S • H • S • H) • S • (H • H ^ 3) • S ^ p-1 ≈⟨ by-assoc auto ⟩
    (S • H) ^ 3 • H ^ 3 • S ^ p-1 ≈⟨ (cleft axiom order-SH) ⟩
    ε • H ^ 3 • S ^ p-1 ≈⟨ left-unit ⟩
    H ^ 3 • S ^ p-1 ∎
    where
    open PB ((₁₊ n) QRel,_===_)
    open PP ((₁₊ n) QRel,_===_)
    open SR word-setoid


  lemma-HSHSH : let open PB ((₁₊ n) QRel,_===_) in

    H • S • H • S • H ≈ S ^ p-1

  lemma-HSHSH {n} = begin
    H • S • H • S • H ≈⟨ sym left-unit ⟩
    ε • (H • S • H • S • H) ≈⟨ (cleft sym (axiom order-S)) ⟩
    (S • S ^ p-1) • (H • S • H • S • H) ≈⟨ (cleft word-comm 1 p-1 refl) ⟩
    (S ^ p-1 • S) • (H • S • H • S • H) ≈⟨ assoc ⟩
    S ^ p-1 • S • (H • S • H • S • H) ≈⟨ (cright by-assoc auto) ⟩
    S ^ p-1 • (S • H) ^ 3 ≈⟨ cong refl (axiom order-SH) ⟩
    S ^ p-1 • ε ≈⟨ right-unit ⟩
    S ^ p-1 ∎
    where
    open PB ((₁₊ n) QRel,_===_)
    open PP ((₁₊ n) QRel,_===_)
    open SR word-setoid
    open Sym0-Rewriting n


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


  -- eqn 17 in Peter's clifford supplement.
  lemma-eqn17 : let open PB ((₂₊ n) QRel,_===_) in
    H ↑ • CZ • S⁻¹ ↑ • H ↑ • H • CZ ≈ CZ • S ↑ • H ↑ • H • CZ • S⁻¹ • H • S⁻¹
  lemma-eqn17 {n@0} = begin
        H ↑ • CZ • S⁻¹ ↑ • H ↑ • H • CZ ≈⟨  special-assoc (□ ^ 6) (□ ^ 4 • □ ^ 2) auto ⟩
        (H ↑ • CZ • S⁻¹ ↑ • H ↑) • H • CZ ≈⟨  (cright trans (sym left-unit) (cong (sym (axiom order-CZ)) refl)) ⟩
        (H ↑ • CZ • S⁻¹ ↑ • H ↑) • CZ ^ p • H • CZ ≈⟨  special-assoc (□ ^ 4 • □ ^ 2 • □ ^ 2) (□ ^ 5 • □ ^ 3) auto ⟩
        (H ↑ • CZ • S⁻¹ ↑ • H ↑ • CZ) • CZ ^ p-1 • H • CZ ≈⟨  (cleft by-assoc auto) ⟩
        (H ↑ • (CZ • S⁻¹ ↑) • H ↑ • CZ) • CZ ^ p-1 • H • CZ ≈⟨  (cleft (cright (cleft (cright lemma-cong↑-S^ (₁₊ p-2))))) ⟩
        (H ↑ • (CZ • S ↑ ^ p-1) • H ↑ • CZ) • CZ ^ p-1 • H • CZ ≈⟨  (cleft cright (cleft word-comm 1 p-1 (axiom comm-CZ-S↑))) ⟩
        (H ↑ • (S ↑ ^ p-1 • CZ) • H ↑ • CZ) • CZ ^ p-1 • H • CZ ≈⟨  special-assoc (((□ • □ ^ 2 • □ ^ 2) • □ ^ 3)) (□ ^ 2 • □ ^ 2 • □ ^ 2 • □ ^ 2) auto ⟩
        (H ↑ • S ↑ ^ p-1) • (CZ • H ↑) • (CZ • CZ ^ p-1) • H • CZ ≈⟨  (cright cright cleft word-comm 1 p-1 refl) ⟩
        (H ↑ • S ↑ ^ p-1) • (CZ • H ↑) • (CZ ^ p-1 • CZ) • H • CZ ≈⟨  special-assoc (□ ^ 2 • □ ^ 2 • □ ^ 2 • □ ^ 2) (□ ^ 2 • □ ^ 3 • □ ^ 3) auto ⟩
        (H ↑ • S ↑ ^ p-1) • (CZ • H ↑ • CZ ^ p-1) • CZ • H • CZ ≈⟨  (cright cleft lemma-CZH↑CZ^k p-2) ⟩
        (H ↑ • S ↑ ^ p-1) • ((S⁻¹ ↑ • H ↑ • S⁻¹ ↑) ^ p-1 • CZ • H ↑ • S⁻¹ ↑ ^ p-1 • S⁻¹ ^ p-1) • CZ • H • CZ ≈⟨ (cright cleft (cleft lemma-^-cong ((S⁻¹ ↑ • H ↑ • S⁻¹ ↑)) ((H⁻¹ ↑ • S ↑ • H ↑)) p-1 (lemma-cong↑ _ _ lemma-S⁻¹HS⁻¹))) ⟩
        (H ↑ • S ↑ ^ p-1) • ((H⁻¹ ↑ • S ↑ • H ↑) ^ p-1 • CZ • H ↑ • S⁻¹ ↑ ^ p-1 • S⁻¹ ^ p-1) • CZ • H • CZ ≈⟨ (cright cleft cleft refl' (lemma-^-↑ (H⁻¹ • S • H) p-1)) ⟩
        (H ↑ • S ↑ ^ p-1) • (((H⁻¹ • S • H) ^ p-1) ↑ • CZ • H ↑ • S⁻¹ ↑ ^ p-1 • S⁻¹ ^ p-1) • CZ • H • CZ ≈⟨ (cright cleft cleft lemma-cong↑ _ _ (aux-[H⁻¹SH]^k p-1)) ⟩
        (H ↑ • S ↑ ^ p-1) • ((H⁻¹ • S ^ p-1 • H) ↑ • CZ • H ↑ • S⁻¹ ↑ ^ p-1 • S⁻¹ ^ p-1) • CZ • H • CZ ≈⟨ special-assoc (□ ^ 2 • (□ ^ 3 • □ ^ 4) • □ ^ 3) (□ ^ 5 • □ ^ 7) auto ⟩
        (H ↑ • S ↑ ^ p-1 • H⁻¹ ↑ • S⁻¹ ↑ • H ↑) • CZ • H ↑ • S⁻¹ ↑ ^ p-1 • S⁻¹ ^ p-1 • CZ • H • CZ ≈⟨ (cleft (cright cleft sym (lemma-cong↑-S^ (₁₊ p-2)) )) ⟩
        (H ↑ • S⁻¹ ↑ • H⁻¹ ↑ • S⁻¹ ↑ • H ↑) • CZ • H ↑ • S⁻¹ ↑ ^ p-1 • S⁻¹ ^ p-1 • CZ • H • CZ ≈⟨ (cleft lemma-cong↑ _ _ aux-HS⁻¹H⁻¹S⁻¹H) ⟩
         S ↑ • CZ • H ↑ • S⁻¹ ↑ ^ p-1 • S⁻¹ ^ p-1 • CZ • H • CZ ≈⟨ (cright cright cright cong (refl' (lemma-^-↑ S⁻¹ p-1)) (cleft aux-S⁻¹⁻¹)) ⟩
         S ↑ • CZ • H ↑ • (S⁻¹ ^ p-1) ↑ • S • CZ • H • CZ ≈⟨ (cright cright cright (cleft lemma-cong↑ _ _ aux-S⁻¹⁻¹)) ⟩
         S ↑ • CZ • H ↑ • S ↑ • S • CZ • H • CZ ≈⟨ by-assoc auto ⟩
         (S ↑ • CZ • H ↑ • S ↑ • S) • CZ • H • CZ ≈⟨ (cright axiom selinger-c11) ⟩
         (S ↑ • CZ • H ↑ • S ↑ • S) • S⁻¹ • H • S⁻¹ • CZ • H • S⁻¹ • S⁻¹ ↑ ≈⟨ by-assoc auto ⟩
         (S ↑ • CZ • H ↑ • S ↑) • (S • S⁻¹) • H • S⁻¹ • CZ • H • S⁻¹ • S⁻¹ ↑ ≈⟨ (cright cong (axiom order-S) refl) ⟩
         (S ↑ • CZ • H ↑ • S ↑) • ε • H • S⁻¹ • CZ • H • S⁻¹ • S⁻¹ ↑ ≈⟨ (cright left-unit) ⟩
         (S ↑ • CZ • H ↑ • S ↑) • H • S⁻¹ • CZ • H • S⁻¹ • S⁻¹ ↑ ≈⟨ by-assoc auto ⟩
         (S ↑ • CZ • H ↑ • S ↑ • H) • S⁻¹ • CZ • H • S⁻¹ • S⁻¹ ↑ ≈⟨ (cleft general-comm auto) ⟩
         (S ↑ • CZ • H ↑ • H • S ↑) • S⁻¹ • CZ • H • S⁻¹ • S⁻¹ ↑ ≈⟨ by-assoc auto ⟩
         (S ↑ • CZ • H ↑ • H) • (S ↑ • S⁻¹) • CZ • H • S⁻¹ • S⁻¹ ↑ ≈⟨ (cright cleft word-comm 1 p-1 (axiom comm-S)) ⟩
         (S ↑ • CZ • H ↑ • H) • (S⁻¹ • S ↑) • CZ • H • S⁻¹ • S⁻¹ ↑ ≈⟨ special-assoc (□ ^ 4 • □ ^ 2 • □ ^ 4) (□ ^ 5 • □ ^ 3 • □ ^ 2) auto ⟩
         (S ↑ • CZ • H ↑ • H • S⁻¹) • (S ↑ • CZ • H) • S⁻¹ • S⁻¹ ↑ ≈⟨ (cright cleft rewrite-sym0 100 auto) ⟩
         (S ↑ • CZ • H ↑ • H • S⁻¹) • (CZ • H • S ↑) • S⁻¹ • S⁻¹ ↑ ≈⟨ special-assoc (□ ^ 5 • □ ^ 3 • □ ^ 2) (□ ^ 7 • □ ^ 2 • □) auto ⟩
         (S ↑ • CZ • H ↑ • H • S⁻¹ • CZ • H) • (S ↑ • S⁻¹) • S⁻¹ ↑ ≈⟨ (cright cleft word-comm 1 p-1 (axiom comm-S)) ⟩
         (S ↑ • CZ • H ↑ • H • S⁻¹ • CZ • H) • (S⁻¹ • S ↑) • S⁻¹ ↑ ≈⟨ special-assoc (□ ^ 7 • □ ^ 2 • □ ) (□ ^ 8 • □ ^ 2) auto ⟩
         (S ↑ • CZ • H ↑ • H • S⁻¹ • CZ • H • S⁻¹) • S ↑ • S⁻¹ ↑ ≈⟨ (cright lemma-cong↑ _ _ (M1B.axiom order-S)) ⟩
         (S ↑ • CZ • H ↑ • H • S⁻¹ • CZ • H • S⁻¹) • ε ≈⟨ right-unit ⟩
         (S ↑ • CZ • H ↑ • H • S⁻¹ • CZ • H • S⁻¹) ≈⟨ by-assoc auto ⟩
         (S ↑ • CZ • H ↑ • H) • S⁻¹ • CZ • H • S⁻¹ ≈⟨ (cleft general-comm auto) ⟩
         (CZ • S ↑ • H ↑ • H) • S⁻¹ • CZ • H • S⁻¹ ≈⟨ special-assoc (□ ^ 4 • □ ^ 4) (□ ^ 4 • □ ^ 2 • □ ^ 2) auto ⟩
         (CZ • S ↑ • H ↑ • H) • (S⁻¹ • CZ) • H • S⁻¹ ≈⟨ (cright cleft word-comm p-1 1 (sym (axiom comm-CZ-S↓))) ⟩
         (CZ • S ↑ • H ↑ • H) • (CZ • S⁻¹) • H • S⁻¹ ≈⟨ by-assoc auto ⟩
        CZ • S ↑ • H ↑ • H • CZ • S⁻¹ • H • S⁻¹ ∎
    where
    open PB ((₂₊ n) QRel,_===_)
    module M1B = PB ((₁₊ n) QRel,_===_)
    open PP ((₂₊ n) QRel,_===_)
    open SR word-setoid
    open Commuting-Symplectic (n)
    open Sym0-Rewriting (suc n)
    open Pattern-Assoc

  lemma-eqn17 {n@(suc _)} = begin
        H ↑ • CZ • S⁻¹ ↑ • H ↑ • H • CZ ≈⟨  special-assoc (□ ^ 6) (□ ^ 4 • □ ^ 2) auto ⟩
        (H ↑ • CZ • S⁻¹ ↑ • H ↑) • H • CZ ≈⟨  (cright trans (sym left-unit) (cong (sym (axiom order-CZ)) refl)) ⟩
        (H ↑ • CZ • S⁻¹ ↑ • H ↑) • CZ ^ p • H • CZ ≈⟨  special-assoc (□ ^ 4 • □ ^ 2 • □ ^ 2) (□ ^ 5 • □ ^ 3) auto ⟩
        (H ↑ • CZ • S⁻¹ ↑ • H ↑ • CZ) • CZ ^ p-1 • H • CZ ≈⟨  (cleft by-assoc auto) ⟩
        (H ↑ • (CZ • S⁻¹ ↑) • H ↑ • CZ) • CZ ^ p-1 • H • CZ ≈⟨  (cleft (cright (cleft (cright lemma-cong↑-S^ (₁₊ p-2))))) ⟩
        (H ↑ • (CZ • S ↑ ^ p-1) • H ↑ • CZ) • CZ ^ p-1 • H • CZ ≈⟨  (cleft cright (cleft word-comm 1 p-1 (axiom comm-CZ-S↑))) ⟩
        (H ↑ • (S ↑ ^ p-1 • CZ) • H ↑ • CZ) • CZ ^ p-1 • H • CZ ≈⟨  special-assoc (((□ • □ ^ 2 • □ ^ 2) • □ ^ 3)) (□ ^ 2 • □ ^ 2 • □ ^ 2 • □ ^ 2) auto ⟩
        (H ↑ • S ↑ ^ p-1) • (CZ • H ↑) • (CZ • CZ ^ p-1) • H • CZ ≈⟨  (cright cright cleft word-comm 1 p-1 refl) ⟩
        (H ↑ • S ↑ ^ p-1) • (CZ • H ↑) • (CZ ^ p-1 • CZ) • H • CZ ≈⟨  special-assoc (□ ^ 2 • □ ^ 2 • □ ^ 2 • □ ^ 2) (□ ^ 2 • □ ^ 3 • □ ^ 3) auto ⟩
        (H ↑ • S ↑ ^ p-1) • (CZ • H ↑ • CZ ^ p-1) • CZ • H • CZ ≈⟨  (cright cleft lemma-CZH↑CZ^k p-2) ⟩
        (H ↑ • S ↑ ^ p-1) • ((S⁻¹ ↑ • H ↑ • S⁻¹ ↑) ^ p-1 • CZ • H ↑ • S⁻¹ ↑ ^ p-1 • S⁻¹ ^ p-1) • CZ • H • CZ ≈⟨ (cright cleft (cleft lemma-^-cong ((S⁻¹ ↑ • H ↑ • S⁻¹ ↑)) ((H⁻¹ ↑ • S ↑ • H ↑)) p-1 (lemma-cong↑ _ _ lemma-S⁻¹HS⁻¹))) ⟩
        (H ↑ • S ↑ ^ p-1) • ((H⁻¹ ↑ • S ↑ • H ↑) ^ p-1 • CZ • H ↑ • S⁻¹ ↑ ^ p-1 • S⁻¹ ^ p-1) • CZ • H • CZ ≈⟨ (cright cleft cleft refl' (lemma-^-↑ (H⁻¹ • S • H) p-1)) ⟩
        (H ↑ • S ↑ ^ p-1) • (((H⁻¹ • S • H) ^ p-1) ↑ • CZ • H ↑ • S⁻¹ ↑ ^ p-1 • S⁻¹ ^ p-1) • CZ • H • CZ ≈⟨ (cright cleft cleft lemma-cong↑ _ _ (aux-[H⁻¹SH]^k p-1)) ⟩
        (H ↑ • S ↑ ^ p-1) • ((H⁻¹ • S ^ p-1 • H) ↑ • CZ • H ↑ • S⁻¹ ↑ ^ p-1 • S⁻¹ ^ p-1) • CZ • H • CZ ≈⟨ special-assoc (□ ^ 2 • (□ ^ 3 • □ ^ 4) • □ ^ 3) (□ ^ 5 • □ ^ 7) auto ⟩
        (H ↑ • S ↑ ^ p-1 • H⁻¹ ↑ • S⁻¹ ↑ • H ↑) • CZ • H ↑ • S⁻¹ ↑ ^ p-1 • S⁻¹ ^ p-1 • CZ • H • CZ ≈⟨ (cleft (cright cleft sym (lemma-cong↑-S^ (₁₊ p-2)) )) ⟩
        (H ↑ • S⁻¹ ↑ • H⁻¹ ↑ • S⁻¹ ↑ • H ↑) • CZ • H ↑ • S⁻¹ ↑ ^ p-1 • S⁻¹ ^ p-1 • CZ • H • CZ ≈⟨ (cleft lemma-cong↑ _ _ aux-HS⁻¹H⁻¹S⁻¹H) ⟩
         S ↑ • CZ • H ↑ • S⁻¹ ↑ ^ p-1 • S⁻¹ ^ p-1 • CZ • H • CZ ≈⟨ (cright cright cright cong (refl' (lemma-^-↑ S⁻¹ p-1)) (cleft aux-S⁻¹⁻¹)) ⟩
         S ↑ • CZ • H ↑ • (S⁻¹ ^ p-1) ↑ • S • CZ • H • CZ ≈⟨ (cright cright cright (cleft lemma-cong↑ _ _ aux-S⁻¹⁻¹)) ⟩
         S ↑ • CZ • H ↑ • S ↑ • S • CZ • H • CZ ≈⟨ by-assoc auto ⟩
         (S ↑ • CZ • H ↑ • S ↑ • S) • CZ • H • CZ ≈⟨ (cright axiom selinger-c11) ⟩
         (S ↑ • CZ • H ↑ • S ↑ • S) • S⁻¹ • H • S⁻¹ • CZ • H • S⁻¹ • S⁻¹ ↑ ≈⟨ by-assoc auto ⟩
         (S ↑ • CZ • H ↑ • S ↑) • (S • S⁻¹) • H • S⁻¹ • CZ • H • S⁻¹ • S⁻¹ ↑ ≈⟨ (cright cong (axiom order-S) refl) ⟩
         (S ↑ • CZ • H ↑ • S ↑) • ε • H • S⁻¹ • CZ • H • S⁻¹ • S⁻¹ ↑ ≈⟨ (cright left-unit) ⟩
         (S ↑ • CZ • H ↑ • S ↑) • H • S⁻¹ • CZ • H • S⁻¹ • S⁻¹ ↑ ≈⟨ by-assoc auto ⟩
         (S ↑ • CZ • H ↑ • S ↑ • H) • S⁻¹ • CZ • H • S⁻¹ • S⁻¹ ↑ ≈⟨ (cleft general-comm auto) ⟩
         (S ↑ • CZ • H ↑ • H • S ↑) • S⁻¹ • CZ • H • S⁻¹ • S⁻¹ ↑ ≈⟨ by-assoc auto ⟩
         (S ↑ • CZ • H ↑ • H) • (S ↑ • S⁻¹) • CZ • H • S⁻¹ • S⁻¹ ↑ ≈⟨ (cright cleft word-comm 1 p-1 (axiom comm-S)) ⟩
         (S ↑ • CZ • H ↑ • H) • (S⁻¹ • S ↑) • CZ • H • S⁻¹ • S⁻¹ ↑ ≈⟨ special-assoc (□ ^ 4 • □ ^ 2 • □ ^ 4) (□ ^ 5 • □ ^ 3 • □ ^ 2) auto ⟩
         (S ↑ • CZ • H ↑ • H • S⁻¹) • (S ↑ • CZ • H) • S⁻¹ • S⁻¹ ↑ ≈⟨ (cright cleft rewrite-sym0 100 auto) ⟩
         (S ↑ • CZ • H ↑ • H • S⁻¹) • (CZ • H • S ↑) • S⁻¹ • S⁻¹ ↑ ≈⟨ special-assoc (□ ^ 5 • □ ^ 3 • □ ^ 2) (□ ^ 7 • □ ^ 2 • □) auto ⟩
         (S ↑ • CZ • H ↑ • H • S⁻¹ • CZ • H) • (S ↑ • S⁻¹) • S⁻¹ ↑ ≈⟨ (cright cleft word-comm 1 p-1 (axiom comm-S)) ⟩
         (S ↑ • CZ • H ↑ • H • S⁻¹ • CZ • H) • (S⁻¹ • S ↑) • S⁻¹ ↑ ≈⟨ special-assoc (□ ^ 7 • □ ^ 2 • □ ) (□ ^ 8 • □ ^ 2) auto ⟩
         (S ↑ • CZ • H ↑ • H • S⁻¹ • CZ • H • S⁻¹) • S ↑ • S⁻¹ ↑ ≈⟨ (cright lemma-cong↑ _ _ (M1B.axiom order-S)) ⟩
         (S ↑ • CZ • H ↑ • H • S⁻¹ • CZ • H • S⁻¹) • ε ≈⟨ right-unit ⟩
         (S ↑ • CZ • H ↑ • H • S⁻¹ • CZ • H • S⁻¹) ≈⟨ by-assoc auto ⟩
         (S ↑ • CZ • H ↑ • H) • S⁻¹ • CZ • H • S⁻¹ ≈⟨ (cleft general-comm auto) ⟩
         (CZ • S ↑ • H ↑ • H) • S⁻¹ • CZ • H • S⁻¹ ≈⟨ special-assoc (□ ^ 4 • □ ^ 4) (□ ^ 4 • □ ^ 2 • □ ^ 2) auto ⟩
         (CZ • S ↑ • H ↑ • H) • (S⁻¹ • CZ) • H • S⁻¹ ≈⟨ (cright cleft word-comm p-1 1 (sym (axiom comm-CZ-S↓))) ⟩
         (CZ • S ↑ • H ↑ • H) • (CZ • S⁻¹) • H • S⁻¹ ≈⟨ by-assoc auto ⟩
        CZ • S ↑ • H ↑ • H • CZ • S⁻¹ • H • S⁻¹ ∎
    where
    open PB ((₂₊ n) QRel,_===_)
    module M1B = PB ((₁₊ n) QRel,_===_)
    open PP ((₂₊ n) QRel,_===_)
    open SR word-setoid
    open Commuting-Symplectic (n)
    open Sym0-Rewriting (suc n)
    open Pattern-Assoc


  -- eqn 16 in Peter's clifford supplement.
  lemma-eqn16 : let open PB ((₂₊ n) QRel,_===_) in
    S • H • CZ • H • H ↑ • CZ ≈ H • CZ • H • H ↑ • CZ • S⁻¹ ↑ • H ↑ • S⁻¹ ↑
  lemma-eqn16 {n} = bbc ε (H ↑) aux00
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
    aux00 : ε • (S • H • CZ • H • (H ↑) • CZ) • H ↑ ≈ ε • (H • CZ • H • (H ↑) • CZ • (S⁻¹ ↑) • (H ↑) • (S⁻¹ ↑)) • H ↑
    aux00 = begin
      ε • (S • H • CZ • H • (H ↑) • CZ) • H ↑ ≈⟨ left-unit ⟩
      (S • H • CZ • H • (H ↑) • CZ) • H ↑ ≈⟨ by-assoc auto ⟩
      S • H • CZ • H • (H ↑) • CZ • H ↑ ≈⟨ lemma-comm-S-Ex' ⟩
      H • CZ • H • H ↑ • CZ • H ↑ • S ↑ ≈⟨ by-assoc auto ⟩
      (H • CZ • H • H ↑ • CZ) • H ↑ • S ↑ ≈⟨ (cright lemma-cong↑ _ _ (PB1.sym lemma-S⁻¹HS⁻¹H)) ⟩
      (H • CZ • H • H ↑ • CZ) • (S⁻¹ ↑) • (H ↑) • (S⁻¹ ↑) • H ↑ ≈⟨ special-assoc (□ ^ 5 • □ ^ 4) (□ ^ 8 • □) auto ⟩
      (H • CZ • H • (H ↑) • CZ • (S⁻¹ ↑) • (H ↑) • (S⁻¹ ↑)) • H ↑ ≈⟨ sym left-unit ⟩
      ε • (H • CZ • H • (H ↑) • CZ • (S⁻¹ ↑) • (H ↑) • (S⁻¹ ↑)) • H ↑ ∎
    
