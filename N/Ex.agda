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



module N.Ex (p-2 : ℕ) (p-prime : Prime (2+ p-2))  where

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
open import N.Symplectic-Derived p-2 p-prime

module Lemmas0a where

  private
    variable
      n : ℕ
      
  open Symplectic-Derived-Gen
  open Symplectic-Derived-GroupLike

  open import Data.Nat.DivMod
  open import Data.Fin.Properties


  lemma-S↓HCZH : let open PB ((₂₊ n) QRel,_===_) in
    S • H • CZ • H ≈ H • CZ • H • CZ • S ↑ • S
  lemma-S↓HCZH {n} = sym (begin
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
    (H • S⁻¹ ↓ • H ↓ • S⁻¹ ↓ • CZ • H ↓) ≈⟨ {!!} ⟩
    (H • S⁻¹ ↓ • H ↓) • S⁻¹ ↓ • CZ • H ↓ ≈⟨ (cleft {!!}) ⟩
    (S • H • S) • S⁻¹ ↓ • CZ • H ↓ ≈⟨ general-powers0 100 {!!} ⟩
    S • H • CZ • H ∎)
    where
    open PB ((₂₊ n) QRel,_===_)
    open PP ((₂₊ n) QRel,_===_)
    module M1P = PP ((₁₊ n) QRel,_===_)
    module M1B = PB ((₁₊ n) QRel,_===_)
    open SR word-setoid
    open Pattern-Assoc
    open Powers0-Symplectic (suc n)


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


  lemma-S↑H↑CZ↑H : let open PB ((₂₊ n) QRel,_===_) in
    S ↑ • H ↑ • CZ • H ↑ ≈ H ↑ • CZ • H ↑ • CZ • S ↓ • S ↑
  lemma-S↑H↑CZ↑H {n} = sym (begin
    H ↑ • CZ • H ↑ • CZ • S ↓ • S ↑ ≈⟨ by-assoc auto ⟩
    H ↑ • (CZ • H ↑ • CZ) • S ↓ • S ↑ ≈⟨ (cright ( cleft axiom selinger-c10 )) ⟩
    H ↑ • (S⁻¹ ↑ • H ↑ • S⁻¹ ↑ • CZ • H ↑ • S⁻¹ ↑ • S⁻¹ ↓) • S ↓ • S ↑ ≈⟨ general-powers0 100 {!!} ⟩
    (H ↑ • S⁻¹ ↑ • H ↑) • S⁻¹ ↑ • CZ • H ↑ ≈⟨ (cleft lemma-cong↑ _ _ {!!}) ⟩
    (S ↑ • H ↑ • S ↑) • S⁻¹ ↑ • CZ • H ↑ ≈⟨ general-powers0 100 {!!} ⟩
    S ↑ • H ↑ • CZ • H ↑ ∎)
    where
    open PB ((₂₊ n) QRel,_===_)
    open PP ((₂₊ n) QRel,_===_)
    open SR word-setoid
    open Powers0-Symplectic (suc n)


{-

  lemma-S↑²H↑CZ↑H : let open PB ((₂₊ n) QRel,_===_) in
    S⁻¹ ↑ • H ↑ • CZ • H ↑ ≈ H ↑ • CZ • H ↑ • CZ ^ 2 • S⁻¹ ↓ • S⁻¹ ↑
  lemma-S↑²H↑CZ↑H {n@(₀)} = begin
    S⁻¹ ↑ • H ↑ • CZ • H ↑ ≈⟨ assoc ⟩
    S ↑ • S ↑ • H ↑ • CZ • H ↑ ≈⟨ (cright lemma-S↑H↑CZ↑H) ⟩
    S ↑ • H ↑ • CZ • H ↑ • CZ • S ↓ • S ↑ ≈⟨ by-assoc auto ⟩
    (S ↑ • H ↑ • CZ • H ↑) • CZ • S ↓ • S ↑ ≈⟨ (cleft lemma-S↑H↑CZ↑H) ⟩
    (H ↑ • CZ • H ↑ • CZ • S ↓ • S ↑) • CZ • S ↓ • S ↑ ≈⟨ by-assoc auto ⟩
    (H ↑ • CZ • H ↑) • CZ • S  • S ↑ • CZ • S  • S ↑ ≈⟨ ( general-comm auto) ⟩
    H ↑ • CZ • H ↑ • CZ ^ 2 • S⁻¹ ↓ • S⁻¹ ↑ ∎
    where
    open PB ((₂₊ n) QRel,_===_)
    open PP ((₂₊ n) QRel,_===_)
    open SR word-setoid
    open Powers0-Symplectic (suc n)
    open Commuting-Symplectic (n)
  lemma-S↑²H↑CZ↑H {n@(suc n')} = begin
    S⁻¹ ↑ • H ↑ • CZ • H ↑ ≈⟨ assoc ⟩
    S ↑ • S ↑ • H ↑ • CZ • H ↑ ≈⟨ (cright lemma-S↑H↑CZ↑H) ⟩
    S ↑ • H ↑ • CZ • H ↑ • CZ • S ↓ • S ↑ ≈⟨ by-assoc auto ⟩
    (S ↑ • H ↑ • CZ • H ↑) • CZ • S ↓ • S ↑ ≈⟨ (cleft lemma-S↑H↑CZ↑H) ⟩
    (H ↑ • CZ • H ↑ • CZ • S ↓ • S ↑) • CZ • S ↓ • S ↑ ≈⟨ by-assoc auto ⟩
    (H ↑ • CZ • H ↑) • CZ • S  • S ↑ • CZ • S  • S ↑ ≈⟨ ( general-comm auto) ⟩
    H ↑ • CZ • H ↑ • CZ ^ 2 • S⁻¹ ↓ • S⁻¹ ↑ ∎
    where
    open PB ((₂₊ n) QRel,_===_)
    open PP ((₂₊ n) QRel,_===_)
    open SR word-setoid
    open Powers0-Symplectic (suc n)
    open Commuting-Symplectic (n)

-}

  lemma-H↑CZ↑HS↑ : let open PB ((₂₊ n) QRel,_===_) in
    S ↑ • S ↓ • CZ • H ↑ • CZ • H ↑ ≈ H ↑ • CZ • H ↑ • S ↑
  lemma-H↑CZ↑HS↑ {n} = begin
    S ↑ • S ↓ • CZ • H ↑ • CZ • H ↑ ≈⟨ {!!} ⟩
    S ↑ • (CZ • H ↑ • CZ) • H ↑ • S ↓ ≈⟨ (cright (cleft axiom selinger-c10)) ⟩
    S ↑ • (S⁻¹ ↑ • H ↑ • S⁻¹ ↑ • CZ • H ↑ • S⁻¹ ↑ • S⁻¹ ↓) • H ↑ • S ↓ ≈⟨ {!!} ⟩
    (H ↑ • CZ • S⁻¹ ↑) • (H ↑ • S⁻¹ ↑ • H ↑) ≈⟨ (cright lemma-cong↑ _ _ {!!}) ⟩
    (H ↑ • CZ • S⁻¹ ↑) • (S • H • S) ↑ ≈⟨ general-powers0 100 {!!} ⟩
    H ↑ • CZ • H ↑ • S ↑ ∎
    where
    open PB ((₂₊ n) QRel,_===_)
    open PP ((₂₊ n) QRel,_===_)
    open SR word-setoid
    open Powers0-Symplectic (suc n)

{-
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

  lemma-comm-S-Ex' : let open PB ((₂₊ n) QRel,_===_) in
    S • H • CZ • H • H ↑ • CZ • H ↑ ≈ H • CZ • H • H ↑ • CZ • H ↑ • S ↑
  lemma-comm-S-Ex' {n}  = begin
    S • H • CZ • H • H ↑ • CZ • H ↑ ≈⟨ by-assoc auto ⟩
    (S • H • CZ • H) • H ↑ • CZ • H ↑ ≈⟨ (cleft {!!}) ⟩ -- lemma-S↓H↓CZ↓H
    (H • CZ • H • CZ • S ↑ • S) • H ↑ • CZ • H ↑ ≈⟨ {!!} 1000 auto ⟩
    (H • CZ • H • CZ • S ↑ • H ↑) • S ↓ • CZ • H ↑ ≈⟨ (cright {!!} 1000 auto) ⟩
    (H • CZ • H • CZ • S ↑ • H ↑) • CZ • H ↑ • S ↓ ≈⟨ by-assoc auto ⟩
    (H • CZ • H • CZ) • (S ↑ • H ↑ • CZ • H ↑) • S ↓ ≈⟨ (cright (cleft lemma-S↑H↑CZ↑H)) ⟩
    (H • CZ • H • CZ) • (H ↑ • CZ • H ↑ • CZ • S ↓ • S ↑) • S ↓ ≈⟨ by-assoc auto ⟩
    (H • CZ • H) • (CZ • H ↑ • CZ) • H ↑ • CZ • S ↓ • S ↑ • S ↓ ≈⟨ (cright (cleft axiom selinger-c10)) ⟩
    (H • CZ • H) • (S⁻¹ ↑ • H ↑ • S⁻¹ ↑ • CZ • H ↑ • S⁻¹ ↑ • S⁻¹ ↓) • H ↑ • CZ • S ↓ • S ↑ • S ↓ ≈⟨ (cright {!!} auto) ⟩
    (H • CZ • H) • (S⁻¹ ↑ • H ↑ • S⁻¹ ↑ • CZ • H ↑ • S⁻¹ ↑) • H ↑ • CZ • S ↓ ^ 4 • S ↑ ≈⟨ (cright general-powers0 100 {!!}) ⟩
    (H • CZ • H) • (S⁻¹ ↑ • H ↑ • S⁻¹ ↑ • CZ) • (H ↑ • S⁻¹ ↑ • H ↑) • CZ • S ↓ • S ↑ ≈⟨ (cright (cright (cleft lemma-cong↑ _ _ {!!}))) ⟩ -- lemma-HSSH
    (H • CZ • H) • (S⁻¹ ↑ • H ↑ • S⁻¹ ↑ • CZ) • (S • H • S) ↑ • CZ • S ↓ • S ↑ ≈⟨ (cright {!!} 1000 auto ) ⟩
    (H • CZ • H) • (S⁻¹ ↑ • H ↑ • CZ • H ↑) • S⁻¹ ↑ • CZ • S ↓ ≈⟨ (cright (cleft {!!})) ⟩ -- lemma-S↑²H↑CZ↑H
    (H • CZ • H) • (H ↑ • CZ • H ↑ • CZ ^ 2 • S⁻¹ ↓ • S⁻¹ ↑) • S⁻¹ ↑ • CZ • S ↓ ≈⟨ general-powers0 100 {!!} ⟩
    (H • CZ • H) • (H ↑ • CZ • H ↑ • CZ ^ 2 • S⁻¹ ↓ • S ↑) • CZ • S ↓ ≈⟨ {!!} ⟩
    (H • CZ • H) • (H ↑ • CZ • H ↑ • CZ ^ 3 • S ↓ ^ 3 • S ↑) ≈⟨ general-powers0 100 {!!} ⟩
    H • CZ • H • H ↑ • CZ • H ↑ • S ↑ ∎
    where
    open PB ((₂₊ n) QRel,_===_)
    open PP ((₂₊ n) QRel,_===_)
    open SR word-setoid
    open Powers0-Symplectic (suc n)

{-
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
    (H ↑ • CZ • H ↑) • (S⁻¹ ↓ • H ↓ • S⁻¹ ↓ • CZ • H ↓ • S⁻¹ ↓ • S⁻¹ ↑) • H ↓ • CZ • S ↑ • S ↓ • S ↑ ≈⟨ (cright rewrite-sym0 1000 auto) ⟩
    (H ↑ • CZ • H ↑) • (S⁻¹ ↓ • H ↓ • S⁻¹ ↓ • CZ • H ↓ • S⁻¹ ↓) • H ↓ • CZ • S ↑ ^ 4 • S ↓ ≈⟨ (cright general-powers0 100 auto) ⟩
    (H ↑ • CZ • H ↑) • (S⁻¹ ↓ • H ↓ • S⁻¹ ↓ • CZ) • (H ↓ • S⁻¹ ↓ • H ↓) • CZ • S ↑ • S ↓ ≈⟨ ((cright (cright (cleft lemma-HSSH)))) ⟩
    (H ↑ • CZ • H ↑) • (S⁻¹ ↓ • H ↓ • S⁻¹ ↓ • CZ) • (S • H • S) • CZ • S ↑ • S ↓ ≈⟨ (cright rewrite-sym0 1000 auto) ⟩
    (H ↑ • CZ • H ↑) • (S⁻¹ ↓ • H ↓ • CZ • H ↓) • S⁻¹ ↓ • CZ • S ↑ ≈⟨ (cright cleft lemma-S↓²H↓CZ↓H) ⟩
    (H ↑ • CZ • H ↑) • (H ↓ • CZ • H ↓ • CZ ^ 2 • S⁻¹ ↑ • S⁻¹ ↓) • S⁻¹ ↓ • CZ • S ↑ ≈⟨ general-powers0 100 auto ⟩
    (H ↑ • CZ • H ↑) • (H ↓ • CZ • H ↓ • CZ ^ 2 • S⁻¹ ↑ • S ↓) • CZ • S ↑ ≈⟨ (cright rewrite-sym0 1000 auto) ⟩
    (H ↑ • CZ • H ↑) • (H ↓ • CZ • H ↓ • CZ ^ 3 • S ↑ ^ 3 • S ↓) ≈⟨ general-powers0 100 auto ⟩
    H ↑ • CZ • H ↑ • H ↓ • CZ • H ↓ • S ↓ ∎
    where
    open PB ((₂₊ n) QRel,_===_)
    open PP ((₂₊ n) QRel,_===_)
    open SR word-setoid
    open Powers0-Symplectic (suc n)
    open Commuting-Symplectic (n)
    open Sym0-Rewriting (suc n)    

-}


  lemma-comm-Ex-S : let open PB ((₂₊ n) QRel,_===_) in
    S ↑ • Ex ≈ Ex • S
  lemma-comm-Ex-S {n}  = begin
    S ↑ • CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑ ≈⟨ {!!} auto ⟩
    (S ↑ • CZ • H • H ↑) • CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑ ≈⟨ ({!!} 1000 auto) ⟩
    (CZ • H) • (S ↑ • H ↑ • CZ • H ↑ • H ↓ • CZ • H ↓) • H ↑ ≈⟨ (cright (cleft {!!})) ⟩ -- lemma-comm-S↑-Ex'
    (CZ • H) • (H ↑ • CZ • H ↑ • H ↓ • CZ • H ↓ • S ↓) • H ↑ ≈⟨ {!!} auto ⟩
    Ex • S ∎
    where
    open PB ((₂₊ n) QRel,_===_)
    open PP ((₂₊ n) QRel,_===_)
    open SR word-setoid
    open Powers0-Symplectic (suc n)


{-
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
    H ↑ • CZ • S⁻¹ ↑ • H ↑ • H • CZ ≈ CZ • S ↑ • H ↑ • H • CZ • S ^ 2 • H • S ^ 2
  lemma-eqn17 {n@₀} = begin
        H ↑ • CZ • S⁻¹ ↑ • H ↑ • H • CZ ≈⟨ general-powers0 100 auto ⟩
        (H ↑ • CZ • S⁻¹ ↑ • H ↑ • CZ) • CZ • CZ • H • CZ ≈⟨ rewrite-sym0 100 auto ⟩
        (H ↑ • S⁻¹ ↑) • (CZ • H ↑ • CZ • CZ) • CZ • H • CZ ≈⟨ (cright (cleft lemma-CZHCZCZ)) ⟩
        (H ↑ • S⁻¹ ↑) • (S • S ↑ • H ↑ ^ 3 • CZ • S ↑ • H ↑ • S ↑) • CZ • H • CZ ≈⟨ general-comm auto ⟩
        (H ↑ • S ↑ ^ 3 • H ↑ ^ 3) • CZ • S ↑ • H ↑ • S ↑ • S • CZ • H • CZ ≈⟨ general-powers0 100 auto ⟩
        (CZ • S ↑ • H ↑ • S ↑ • S) • CZ • H • CZ ≈⟨ cong refl (axiom selinger-c11) ⟩
        (CZ • S ↑ • H ↑ • S ↑ • S) • S⁻¹ ↓ • H ↓ • S⁻¹ ↓ • CZ • H ↓ • S⁻¹ ↓ • S⁻¹ ↑ ≈⟨ general-powers0 100 auto ⟩
        (CZ • S ↑ • H ↑ • S ↑) • H ↓ • S⁻¹ ↓ • CZ • H ↓ • S⁻¹ ↓ • S⁻¹ ↑ ≈⟨ general-comm auto ⟩
        (CZ • S ↑ • H ↑) • H ↓ • S⁻¹ ↓ • CZ • H ↓ • S⁻¹ ↓ • S ↑ ^ 3 ≈⟨ general-powers0 100 auto ⟩
        (CZ • S ↑ • H ↑) • H ↓ • S⁻¹ ↓ • CZ • H ↓ • S⁻¹ ↓ ≈⟨ general-comm auto ⟩
        CZ • S ↑ • H ↑ • H • CZ • S ^ 2 • H • S ^ 2 ∎
    where
    open PB ((₂₊ n) QRel,_===_)
    open PP ((₂₊ n) QRel,_===_)
    open SR word-setoid
    open Powers0-Symplectic (suc n)
    open Commuting-Symplectic (n)
    open Sym0-Rewriting (suc n)

  lemma-eqn17 {n@(suc _)} = begin
        H ↑ • CZ • S⁻¹ ↑ • H ↑ • H • CZ ≈⟨ general-powers0 100 auto ⟩
        (H ↑ • CZ • S⁻¹ ↑ • H ↑ • CZ) • CZ • CZ • H • CZ ≈⟨ rewrite-sym0 100 auto ⟩
        (H ↑ • S⁻¹ ↑) • (CZ • H ↑ • CZ • CZ) • CZ • H • CZ ≈⟨ (cright (cleft lemma-CZHCZCZ)) ⟩
        (H ↑ • S⁻¹ ↑) • (S • S ↑ • H ↑ ^ 3 • CZ • S ↑ • H ↑ • S ↑) • CZ • H • CZ ≈⟨ general-comm auto ⟩
        (H ↑ • S ↑ ^ 3 • H ↑ ^ 3) • CZ • S ↑ • H ↑ • S ↑ • S • CZ • H • CZ ≈⟨ general-powers0 100 auto ⟩
        (CZ • S ↑ • H ↑ • S ↑ • S) • CZ • H • CZ ≈⟨ cong refl (axiom selinger-c11) ⟩
        (CZ • S ↑ • H ↑ • S ↑ • S) • S⁻¹ ↓ • H ↓ • S⁻¹ ↓ • CZ • H ↓ • S⁻¹ ↓ • S⁻¹ ↑ ≈⟨ general-powers0 100 auto ⟩
        (CZ • S ↑ • H ↑ • S ↑) • H ↓ • S⁻¹ ↓ • CZ • H ↓ • S⁻¹ ↓ • S⁻¹ ↑ ≈⟨ general-comm auto ⟩
        (CZ • S ↑ • H ↑) • H ↓ • S⁻¹ ↓ • CZ • H ↓ • S⁻¹ ↓ • S ↑ ^ 3 ≈⟨ general-powers0 100 auto ⟩
        (CZ • S ↑ • H ↑) • H ↓ • S⁻¹ ↓ • CZ • H ↓ • S⁻¹ ↓ ≈⟨ general-comm auto ⟩
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
    H  • CZ • S  ^ 2 • H  • H ↑ • CZ ≈ CZ • S  • H  • H ↑ • CZ • S⁻¹ ↑ • H ↑ • S⁻¹ ↑
  lemma-eqn17↓ {n@₀} = begin
        H  • CZ • S  ^ 2 • H • H ↑ • CZ ≈⟨ general-powers0 100 auto ⟩
        (H  • CZ • S  ^ 2 • H  • CZ) • CZ • CZ • H ↑ • CZ ≈⟨ rewrite-sym0 100 auto ⟩
        (H  • S  ^ 2) • (CZ • H • CZ • CZ) • CZ • H ↑ • CZ ≈⟨ (cright (cleft lemma-CZH↓CZCZ)) ⟩
        (H  • S  ^ 2) • (S ↑ • S  • H  ^ 3 • CZ • S • H  • S) • CZ • H ↑ • CZ ≈⟨ general-comm auto ⟩
        (H  • S  ^ 3 • H  ^ 3) • CZ • S  • H  • S • S ↑ • CZ • H ↑ • CZ ≈⟨ general-powers0 100 auto ⟩
        (CZ • S  • H  • S  • S ↑) • CZ • H ↑ • CZ ≈⟨ cong refl (axiom selinger-c10) ⟩
        (CZ • S  • H  • S  • S ↑) • S⁻¹ ↑ • H ↑ • S⁻¹ ↑ • CZ • H ↑ • S⁻¹ ↑ • S⁻¹ ↓ ≈⟨ general-powers0 100 auto ⟩
        (CZ • S  • H  • S ) • H ↑ • S⁻¹ ↑ • CZ • H ↑ • S⁻¹ ↑ • S⁻¹ ↓ ≈⟨ general-comm auto ⟩
        (CZ • S  • H ) • H ↑ • S⁻¹ ↑ • CZ • H ↑ • S⁻¹ ↑ • S  ^ 3 ≈⟨ general-powers0 100 auto ⟩
        (CZ • S  • H ) • H ↑ • S⁻¹ ↑ • CZ • H ↑ • S⁻¹ ↑ ≈⟨ general-comm auto ⟩
        CZ • S  • H  • H ↑ • CZ • S⁻¹ ↑ • H ↑ • S⁻¹ ↑ ∎
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
        (CZ • S  • H  • S  • S ↑) • S⁻¹ ↑ • H ↑ • S⁻¹ ↑ • CZ • H ↑ • S⁻¹ ↑ • S⁻¹ ↓ ≈⟨ general-powers0 100 auto ⟩
        (CZ • S  • H  • S ) • H ↑ • S⁻¹ ↑ • CZ • H ↑ • S⁻¹ ↑ • S⁻¹ ↓ ≈⟨ general-comm auto ⟩
        (CZ • S  • H ) • H ↑ • S⁻¹ ↑ • CZ • H ↑ • S⁻¹ ↑ • S  ^ 3 ≈⟨ general-powers0 100 auto ⟩
        (CZ • S  • H ) • H ↑ • S⁻¹ ↑ • CZ • H ↑ • S⁻¹ ↑ ≈⟨ general-comm auto ⟩
        CZ • S  • H  • H ↑ • CZ • S⁻¹ ↑ • H ↑ • S⁻¹ ↑ ∎
    where
    open PB ((₂₊ n) QRel,_===_)
    open PP ((₂₊ n) QRel,_===_)
    open SR word-setoid
    open Powers0-Symplectic (suc n)
    open Commuting-Symplectic (n)
    open Sym0-Rewriting (suc n)


  -- eqn 16 in Peter's clifford supplement.
  lemma-eqn16 : let open PB ((₂₊ n) QRel,_===_) in
    S • H • CZ • H • H ↑ • CZ ≈ H • CZ • H • H ↑ • CZ • S⁻¹ ↑ • H ↑ • S⁻¹ ↑
  lemma-eqn16 {n@₀} = begin
    S • H • CZ • H • H ↑ • CZ ≈⟨ general-powers0 100 auto ⟩
    S • H • (CZ • H • CZ • CZ) • CZ • H ↑ • CZ ≈⟨ (cright (cright (cleft lemma-CZH↓CZCZ))) ⟩
    S • H • (S ↑ • S  • H  ^ 3 • CZ • S  • H  • S) • CZ • H ↑ • CZ ≈⟨ by-assoc auto ⟩
    (S • H • S ↑ • S  • H  ^ 3 • CZ • S  • H  • S) • (CZ • H ↑ • CZ) ≈⟨ (cright (axiom selinger-c10)) ⟩
    (S • H • S ↑ • S  • H  ^ 3 • CZ • S  • H  • S) • (S⁻¹ ↑ • H ↑ • S⁻¹ ↑ • CZ • H ↑ • S⁻¹ ↑ • S⁻¹ ↓) ≈⟨ general-comm auto ⟩
    (S • H • S • H  ^ 3 • CZ • S • H) • (S ↑ ^ 3 • H ↑ • S⁻¹ ↑ • CZ • H ↑ • S⁻¹ ↑ • S ↓ ^ 3) ≈⟨ general-powers0 100 auto ⟩
    (S • H • S • H  ^ 3 • CZ • S • H ) • (H ↑ • S⁻¹ ↑ • CZ • H ↑ • S⁻¹ ↑) ≈⟨ by-assoc auto ⟩
    (S • H • S • H) • H ^ 2 • CZ • S • H  • (H ↑ • S⁻¹ ↑ • CZ • H ↑ • S⁻¹ ↑) ≈⟨ (cleft lemma-SHSH') ⟩
    (H ^ 3 • S ^ 2) • H ^ 2 • CZ • S • H  • (H ↑ • S⁻¹ ↑ • CZ • H ↑ • S⁻¹ ↑) ≈⟨ rewrite-sym0 100 auto ⟩
    H • CZ • H • (H ↑ • S⁻¹ ↑ • CZ • H ↑ • S⁻¹ ↑) ≈⟨ general-comm auto ⟩
    H • CZ • H • H ↑ • CZ • S⁻¹ ↑ • H ↑ • S⁻¹ ↑ ∎
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
    (S • H • S ↑ • S  • H  ^ 3 • CZ • S  • H  • S) • (S⁻¹ ↑ • H ↑ • S⁻¹ ↑ • CZ • H ↑ • S⁻¹ ↑ • S⁻¹ ↓) ≈⟨ general-comm auto ⟩
    (S • H • S • H  ^ 3 • CZ • S • H) • (S ↑ ^ 3 • H ↑ • S⁻¹ ↑ • CZ • H ↑ • S⁻¹ ↑ • S ↓ ^ 3) ≈⟨ general-powers0 100 auto ⟩
    (S • H • S • H  ^ 3 • CZ • S • H ) • (H ↑ • S⁻¹ ↑ • CZ • H ↑ • S⁻¹ ↑) ≈⟨ by-assoc auto ⟩
    (S • H • S • H) • H ^ 2 • CZ • S • H  • (H ↑ • S⁻¹ ↑ • CZ • H ↑ • S⁻¹ ↑) ≈⟨ (cleft lemma-SHSH') ⟩
    (H ^ 3 • S ^ 2) • H ^ 2 • CZ • S • H  • (H ↑ • S⁻¹ ↑ • CZ • H ↑ • S⁻¹ ↑) ≈⟨ rewrite-sym0 100 auto ⟩
    H • CZ • H • (H ↑ • S⁻¹ ↑ • CZ • H ↑ • S⁻¹ ↑) ≈⟨ general-comm auto ⟩
    H • CZ • H • H ↑ • CZ • S⁻¹ ↑ • H ↑ • S⁻¹ ↑ ∎
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
    (S ↑ • H ↑ • S • S ↑  • H ↑  ^ 3 • CZ • S ↑  • H ↑  • S ↑) • (S⁻¹ ↓ • H ↓ • S⁻¹ ↓ • CZ • H ↓ • S⁻¹ ↓ • S⁻¹ ↑) ≈⟨ general-comm auto ⟩
    (S ↑ • H ↑ • S ↑ • H ↑  ^ 3 • CZ • S ↑ • H ↑) • (S ^ 3 • H • S ^ 2 • CZ • H • S ^ 2 • S ↑  ^ 3) ≈⟨ general-powers0 100 auto ⟩
    (S ↑ • H ↑ • S ↑ • H ↑  ^ 3 • CZ • S ↑ • H ↑ ) • (H • S ^ 2 • CZ • H • S ^ 2) ≈⟨ by-assoc auto ⟩
    (S ↑ • H ↑ • S ↑ • H ↑) • H ↑ ^ 2 • CZ • S ↑ • H ↑  • (H • S ^ 2 • CZ • H • S ^ 2) ≈⟨ (cleft lemma-cong↑ _ _ lemma-SHSH') ⟩
    (H ↑ ^ 3 • S⁻¹ ↑) • H ↑ ^ 2 • CZ • S ↑ • H ↑  • (H • S ^ 2 • CZ • H • S ^ 2) ≈⟨ rewrite-sym0 100 auto ⟩
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
    (S ↑ • H ↑ • S • S ↑  • H ↑  ^ 3 • CZ • S ↑  • H ↑  • S ↑) • (S⁻¹ ↓ • H ↓ • S⁻¹ ↓ • CZ • H ↓ • S⁻¹ ↓ • S⁻¹ ↑) ≈⟨ general-comm auto ⟩
    (S ↑ • H ↑ • S ↑ • H ↑  ^ 3 • CZ • S ↑ • H ↑) • (S ^ 3 • H • S ^ 2 • CZ • H • S ^ 2 • S ↑  ^ 3) ≈⟨ general-powers0 100 auto ⟩
    (S ↑ • H ↑ • S ↑ • H ↑  ^ 3 • CZ • S ↑ • H ↑ ) • (H • S ^ 2 • CZ • H • S ^ 2) ≈⟨ by-assoc auto ⟩
    (S ↑ • H ↑ • S ↑ • H ↑) • H ↑ ^ 2 • CZ • S ↑ • H ↑  • (H • S ^ 2 • CZ • H • S ^ 2) ≈⟨ (cleft lemma-cong↑ _ _ lemma-SHSH') ⟩
    (H ↑ ^ 3 • S⁻¹ ↑) • H ↑ ^ 2 • CZ • S ↑ • H ↑  • (H • S ^ 2 • CZ • H • S ^ 2) ≈⟨ rewrite-sym0 100 auto ⟩
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
    (CZ • S • H  • H ↑ • CZ • S⁻¹ ↑ • H ↑ • S⁻¹ ↑) • S ↑ • H  • S • CZ • H ↑ • CZ ≈⟨ general-powers0 100 auto ⟩
    CZ • S • H  • H ↑ • CZ • S⁻¹ ↑ • H ↑ • H  • S • CZ • H ↑ • CZ ≈⟨ general-comm auto ⟩
    (CZ • H ↑ • S⁻¹ ↑) • (S • H • CZ • H • H ↑ • CZ) • S • H ↑ • CZ ≈⟨ (cright (cleft lemma-eqn16)) ⟩
    (CZ • H ↑ • S⁻¹ ↑) • (H • CZ • H • H ↑ • CZ • S⁻¹ ↑ • H ↑ • S⁻¹ ↑) • S • H ↑ • CZ ≈⟨ general-comm auto ⟩
    (CZ • H ↑ • H • CZ) • (H • S⁻¹ ↑ • H ↑ • CZ) • (S⁻¹ ↑ • H ↑ • S⁻¹ ↑ • H ↑) • S • CZ ≈⟨ (cright (cright (cleft lemma-cong↑ _ _ lemma-SSHSSH))) ⟩
    (CZ • H ↑ • H • CZ) • (H • S⁻¹ ↑ • H ↑ • CZ) • (H ↑ • S ↑) • S • CZ ≈⟨ general-comm auto ⟩
    (CZ • H ↑ • H • CZ • H) • (S⁻¹ ↑ • H ↑ • CZ • H ↑) • S ↑ • S • CZ ≈⟨ (cright (cleft lemma-S↑²H↑CZ↑H)) ⟩
    (CZ • H ↑ • H • CZ • H) • (H ↑ • CZ • H ↑ • CZ ^ 2 • S⁻¹ ↓ • S⁻¹ ↑) • S ↑ • S • CZ ≈⟨ general-powers0 100 auto ⟩
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
    (CZ • S • H  • H ↑ • CZ • S⁻¹ ↑ • H ↑ • S⁻¹ ↑) • S ↑ • H  • S • CZ • H ↑ • CZ ≈⟨ general-powers0 100 auto ⟩
    CZ • S • H  • H ↑ • CZ • S⁻¹ ↑ • H ↑ • H  • S • CZ • H ↑ • CZ ≈⟨ general-comm auto ⟩
    (CZ • H ↑ • S⁻¹ ↑) • (S • H • CZ • H • H ↑ • CZ) • S • H ↑ • CZ ≈⟨ (cright (cleft lemma-eqn16)) ⟩
    (CZ • H ↑ • S⁻¹ ↑) • (H • CZ • H • H ↑ • CZ • S⁻¹ ↑ • H ↑ • S⁻¹ ↑) • S • H ↑ • CZ ≈⟨ general-comm auto ⟩
    (CZ • H ↑ • H • CZ) • (H • S⁻¹ ↑ • H ↑ • CZ) • (S⁻¹ ↑ • H ↑ • S⁻¹ ↑ • H ↑) • S • CZ ≈⟨ (cright (cright (cleft lemma-cong↑ _ _ lemma-SSHSSH))) ⟩
    (CZ • H ↑ • H • CZ) • (H • S⁻¹ ↑ • H ↑ • CZ) • (H ↑ • S ↑) • S • CZ ≈⟨ general-comm auto ⟩
    (CZ • H ↑ • H • CZ • H) • (S⁻¹ ↑ • H ↑ • CZ • H ↑) • S ↑ • S • CZ ≈⟨ (cright (cleft lemma-S↑²H↑CZ↑H)) ⟩
    (CZ • H ↑ • H • CZ • H) • (H ↑ • CZ • H ↑ • CZ ^ 2 • S⁻¹ ↓ • S⁻¹ ↑) • S ↑ • S • CZ ≈⟨ general-powers0 100 auto ⟩
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
    (H ↑ • CZ • H) • S • (S⁻¹ ↑) • H ↑ • CZ  • H ↑  • S ↑ • CZ • H • CZ ≈⟨ ((cright general-comm auto)) ⟩
    (H ↑ • CZ • H) • (S⁻¹ ↑) • H ↑ • CZ • S • H ↑  • S ↑ • CZ • H • CZ ≈⟨ by-assoc auto ⟩
    (H ↑ • CZ • H • S⁻¹ ↑ • H ↑ • CZ) • S • H ↑  • S ↑ • CZ • H • CZ ≈⟨ general-comm auto ⟩
    (H ↑ • CZ • S⁻¹ ↑ • H ↑ • H • CZ) • S • H ↑  • S ↑ • CZ • H • CZ ≈⟨ (cleft lemma-eqn17) ⟩
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
    (H ↑ • CZ • H) • S • (S⁻¹ ↑) • H ↑ • CZ  • H ↑  • S ↑ • CZ • H • CZ ≈⟨ ((cright general-comm auto)) ⟩
    (H ↑ • CZ • H) • (S⁻¹ ↑) • H ↑ • CZ • S • H ↑  • S ↑ • CZ • H • CZ ≈⟨ by-assoc auto ⟩
    (H ↑ • CZ • H • S⁻¹ ↑ • H ↑ • CZ) • S • H ↑  • S ↑ • CZ • H • CZ ≈⟨ general-comm auto ⟩
    (H ↑ • CZ • S⁻¹ ↑ • H ↑ • H • CZ) • S • H ↑  • S ↑ • CZ • H • CZ ≈⟨ (cleft lemma-eqn17) ⟩
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



-}



