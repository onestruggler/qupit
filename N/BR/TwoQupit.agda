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



module N.BR.TwoQupit (p-2 : ℕ) (p-prime : Prime (2+ p-2)) where

n : ℕ
n = 0
    
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
open import N.Lemmas-2Qupit-Sym p-2 p-prime
open import N.NF2-Sym p-2 p-prime
--open Lemmas-2Q 2

open import N.NF1 p-2 p-prime
open import N.Ex-Sym p-2 p-prime
open import N.Ex-Sym1 p-2 p-prime
open import N.Ex-Sym2 p-2 p-prime
open import N.Ex-Sym3 p-2 p-prime
open import N.Ex-Sym4 p-2 p-prime
--open import N.Ex-Sym5 p-2 p-prime hiding (module L0)
open import N.Ex-Sym2n p-2 p-prime
open import N.Ex-Sym3n p-2 p-prime

open import N.Lemma-Comm-n p-2 p-prime 0
open import N.Completeness1-Sym p-2 p-prime renaming (module Completeness to Cp1)
open Lemmas0a
open Lemmas0a1
open Lemmas0b
open Lemmas0c
open Lemmas-Sym
open Duality

open import N.Completeness1-Sym p-2 p-prime renaming (module Completeness to CP1) using ()
--open import N.Coset2-Update-Sym p-2 p-prime renaming (module Completeness to CP2) using ()
open import N.Lemmas4-Sym p-2 p-prime
open import N.Lemmas-3Q p-2 p-prime
open import N.Pushing.DH p-2 p-prime
open import N.Duality p-2 p-prime
open import N.BR.Calculations p-2 p-prime


open PB ((₂₊ n) QRel,_===_)
open PP ((₂₊ n) QRel,_===_)
open SR word-setoid
open Pattern-Assoc
open Lemmas0 n
open Lemmas-2Q n
open Sym0-Rewriting (₁₊ n)

{-
fig-27-1 : ∀ (b*@(b , nzb) : ℤ* ₚ) ->
  let
  b⁻¹ = (b* ⁻¹) .proj₁
  nz = aux-b≠0⇒ab≠0 ₀ b nzb
  in
  
  [ (₀ , b) , nz ]ᵃ ↑ • CZ ≈ CZ^ b⁻¹ • [ (₀ , b) , nz ]ᵃ ↑

fig-27-1 b*@(b , nzb) = begin
  [ (₀ , b) , nz ]ᵃ ↑ • CZ ≈⟨ cleft lemma-cong↑ _ _ (aux-abox-nzb b nzb) ⟩
  ⟦ (b , nzb) ⁻¹ ⟧ₘ ↑ • CZ ≈⟨ axiom (semi-M↑CZ ((b , nzb) ⁻¹)) ⟩
  CZ^ b⁻¹ • ⟦ (b , nzb) ⁻¹ ⟧ₘ ↑ ≈⟨ cright sym (lemma-cong↑ _ _ (aux-abox-nzb b nzb)) ⟩
  CZ^ b⁻¹ • [ (₀ , b) , nz ]ᵃ ↑ ∎
  where
  b⁻¹ = (b* ⁻¹) .proj₁
  nz = aux-b≠0⇒ab≠0 ₀ b nzb


fig-27-1-dual : ∀ (b*@(b , nzb) : ℤ* ₚ) ->
  let
  b⁻¹ = (b* ⁻¹) .proj₁
  nz = aux-b≠0⇒ab≠0 ₀ b nzb
  in
  
  [ (₀ , b) , nz ]ᵃ  • CZ ≈ CZ^ b⁻¹ • [ (₀ , b) , nz ]ᵃ 

fig-27-1-dual b*@(b , nzb) = begin
  [ (₀ , b) , nz ]ᵃ  • CZ ≈⟨ cleft (aux-abox-nzb b nzb) ⟩
  ⟦ (b , nzb) ⁻¹ ⟧ₘ  • CZ ≈⟨ axiom (semi-M↓CZ ((b , nzb) ⁻¹)) ⟩
  CZ^ b⁻¹ • ⟦ (b , nzb) ⁻¹ ⟧ₘ  ≈⟨ cright sym ((aux-abox-nzb b nzb)) ⟩
  CZ^ b⁻¹ • [ (₀ , b) , nz ]ᵃ  ∎
  where
  b⁻¹ = (b* ⁻¹) .proj₁
  nz = aux-b≠0⇒ab≠0 ₀ b nzb


{-
fig-27-2 : ∀ (a*@(a , nza) : ℤ* ₚ) (b : ℤ ₚ) ->
  let
  a⁻¹ = (a* ⁻¹) .proj₁
  -b/a = - b * a⁻¹
  nz : (a , b) ≢ (₀ , ₀)
  nz = aux-a≠0⇒ab≠0 a b nza
  nz' : (₀ , - a) ≢ (₀ , ₀)
  nz' = aux-b≠0⇒ab≠0 ₀ (- a) ((-' a*) .proj₂)
  in
  
  [ (a , b) , nz ]ᵃ ↑ • CZ ≈ CZ^ a⁻¹ • [ a , b ]ᵇ • [ (₀ , - a) , nz' ]ᵃ

fig-27-2 a*@(a , nza) b = begin
  [ (a , b) , nz ]ᵃ ↑ • CZ ≈⟨ cleft lemma-cong↑ _ _ (aux-abox-nza a b nza) ⟩
  ⟦ (a , nza) ⁻¹ , HS^ -b/a ⟧ₘ₊ ↑ • CZ ≈⟨ refl ⟩
  ⟦ (a , nza) ⁻¹ , HS^ -b/a ⟧ₘ₊ ↑ • CZ ≈⟨ {!!} ⟩
  CZ^ a⁻¹ • (Ex • CX • [ (a , b) , nz ]ᵃ ↑) • ⟦ (- a , (-' a*) .proj₂) ⁻¹ ⟧ₘ ≈⟨ cright cong (sym (aux-bbox-nza a b nza)) (sym (aux-abox-nzb (- a) ((-' a*) .proj₂))) ⟩
  CZ^ a⁻¹ • [ a , b ]ᵇ • [ (₀ , - a) , nz' ]ᵃ ∎
  where
  a⁻¹ = (a* ⁻¹) .proj₁
  -b/a = - b * a⁻¹
  nz : (a , b) ≢ (₀ , ₀)
  nz = aux-a≠0⇒ab≠0 a b nza
  nz' : (₀ , - a) ≢ (₀ , ₀)
  nz' = aux-b≠0⇒ab≠0 ₀ (- a) ((-' a*) .proj₂)

-}

fig-28-1 : ∀ (b*@(b , nzb) : ℤ* ₚ) ->
  let
  b⁻¹ = (b* ⁻¹) .proj₁
  nz = aux-b≠0⇒ab≠0 ₀ b nzb
  in
  
  [ ₀ , ₀ ]ᵇ • [ (₀ , b) , nz ]ᵃ • CZ ≈ CZ^ b⁻¹ • [ ₀ , ₀ ]ᵇ • [ (₀ , b) , nz ]ᵃ

fig-28-1 b*@(b , nzb) = begin
  [ ₀ , ₀ ]ᵇ • [ (₀ , b) , nz ]ᵃ  • CZ ≈⟨ cright fig-27-1-dual b* ⟩
  [ ₀ , ₀ ]ᵇ • CZ^ b⁻¹ • [ (₀ , b) , nz ]ᵃ  ≈⟨ sym assoc ⟩  
  ([ ₀ , ₀ ]ᵇ • CZ^ b⁻¹) • [ (₀ , b) , nz ]ᵃ  ≈⟨ cleft word-comm 1 (toℕ b⁻¹) (sym {!!}) ⟩  
  (CZ^ b⁻¹ • [ ₀ , ₀ ]ᵇ) • [ (₀ , b) , nz ]ᵃ  ≈⟨ assoc ⟩  
  CZ^ b⁻¹ • [ ₀ , ₀ ]ᵇ • [ (₀ , b) , nz ]ᵃ  ∎
  where
  b⁻¹ = (b* ⁻¹) .proj₁
  nz = aux-b≠0⇒ab≠0 ₀ b nzb



fig-28-2 : ∀ (b*@(b , nzb) d*@(d , nzd) : ℤ* ₚ) ->
  let
  b⁻¹ = (b* ⁻¹) .proj₁
  d⁻¹ = (d* ⁻¹) .proj₁
  [bd]⁻¹ = b⁻¹ * d⁻¹
  -2[bd]⁻¹ = - [bd]⁻¹ + - [bd]⁻¹
  nz = aux-b≠0⇒ab≠0 ₀ b nzb
  in
  
  [ ₀ , d ]ᵇ • [ (₀ , b) , nz ]ᵃ • CZ ≈ (S^ -2[bd]⁻¹ • CZ^ [bd]⁻¹) • [ ₀ , d ]ᵇ • [ (₀ , b) , nz ]ᵃ

fig-28-2 b*@(b , nzb) d*@(d , nzd) = begin
  [ ₀ , d ]ᵇ • [ (₀ , b) , nz ]ᵃ  • CZ ≈⟨ cright fig-27-1-dual b* ⟩
  [ ₀ , d ]ᵇ • CZ^ b⁻¹ • [ (₀ , b) , nz ]ᵃ  ≈⟨ sym assoc ⟩  
  ([ ₀ , d ]ᵇ • CZ^ b⁻¹) • [ (₀ , b) , nz ]ᵃ  ≈⟨ cleft cleft {!!} d nzd ⟩
  ((Ex • CX • ⟦ (d , nzd) ⁻¹ ⟧ₘ ↑) • CZ^ b⁻¹) • [ (₀ , b) , nz ]ᵃ  ≈⟨ special-assoc ((□ ^ 3 • □) • □) (□ ^ 2 • □ ^ 2 • □) auto ⟩
  (Ex • CX) • (⟦ (d , nzd) ⁻¹ ⟧ₘ ↑ • CZ^ b⁻¹) • [ (₀ , b) , nz ]ᵃ  ≈⟨ cright cleft lemma-M↑CZ^k d⁻¹ b⁻¹ (((d , nzd) ⁻¹) .proj₂) ⟩
  (Ex • CX) • (CZ^ (b⁻¹ * d⁻¹) • ⟦ (d , nzd) ⁻¹ ⟧ₘ ↑) • [ (₀ , b) , nz ]ᵃ  ≈⟨ special-assoc (□ ^ 2 • □ ^ 2 • □) (□ • □ ^ 2 • □ ^ 2) auto ⟩
  Ex • (CX • CZ^ (b⁻¹ * d⁻¹)) • ⟦ (d , nzd) ⁻¹ ⟧ₘ ↑ • [ (₀ , b) , nz ]ᵃ  ≈⟨ cright cleft lemma-semi-CXCZ^k k* ⟩
  Ex • (S^ -2k ↑ • CZ^ k • CX) • ⟦ (d , nzd) ⁻¹ ⟧ₘ ↑ • [ (₀ , b) , nz ]ᵃ  ≈⟨ special-assoc (□ • □ ^ 3 • □) (□ ^ 2 • □ ^ 3) auto ⟩
  (Ex • S^ -2k ↑) • CZ^ k • CX • ⟦ (d , nzd) ⁻¹ ⟧ₘ ↑ • [ (₀ , b) , nz ]ᵃ  ≈⟨ cleft cright sym (refl' (lemma-^-↑ S (toℕ -2k))) ⟩
  (Ex • S ↑ ^ toℕ -2k) • CZ^ k • CX • ⟦ (d , nzd) ⁻¹ ⟧ₘ ↑ • [ (₀ , b) , nz ]ᵃ  ≈⟨ cleft lemma-Induction lemma-Ex-S↑-n (toℕ -2k) ⟩
  (S^ -2k • Ex) • CZ^ k • CX • ⟦ (d , nzd) ⁻¹ ⟧ₘ ↑ • [ (₀ , b) , nz ]ᵃ  ≈⟨ special-assoc (□ ^ 2 • □ ^ 2) (□ • □ ^ 2 • □) auto ⟩
  S^ -2k • (Ex • CZ^ k) • CX • ⟦ (d , nzd) ⁻¹ ⟧ₘ ↑ • [ (₀ , b) , nz ]ᵃ  ≈⟨ cright cleft word-comm 1 (toℕ k) (sym lemma-comm-Ex-CZ-n) ⟩
  S^ -2k • (CZ^ k • Ex) • CX • ⟦ (d , nzd) ⁻¹ ⟧ₘ ↑ • [ (₀ , b) , nz ]ᵃ  ≈⟨ special-assoc (□ • □ ^ 2 • □ ^ 3) (□ ^ 2 • □ ^ 3 • □) auto ⟩
  (S^ -2k • CZ^ k) • (Ex • CX • ⟦ (d , nzd) ⁻¹ ⟧ₘ ↑) • [ (₀ , b) , nz ]ᵃ  ≈⟨ cright cleft sym ({!!} d nzd) ⟩
  (S^ -2k • CZ^ k) • [ ₀ , d ]ᵇ • [ (₀ , b) , nz ]ᵃ  ≈⟨ refl ⟩
  (S^ -2[bd]⁻¹ • CZ^ [bd]⁻¹) • [ ₀ , d ]ᵇ • [ (₀ , b) , nz ]ᵃ  ∎
  where
  b⁻¹ = (b* ⁻¹) .proj₁
  d⁻¹ = (d* ⁻¹) .proj₁
  nz = aux-b≠0⇒ab≠0 ₀ b nzb
  k* : ℤ* ₚ
  k* = (b* ⁻¹ *' d* ⁻¹)
  
  k : ℤ ₚ
  k = k* .proj₁
  -k : ℤ ₚ
  -k = - k
  k⁻¹ : ℤ ₚ
  k⁻¹ = ((k* ⁻¹) .proj₁)
  -k⁻¹ : ℤ ₚ
  -k⁻¹ = - k⁻¹
  -2k = -k + -k
  [bd]⁻¹ = b⁻¹ * d⁻¹
  -2[bd]⁻¹ = - [bd]⁻¹ + - [bd]⁻¹


aux-HH↑-CZ⁻¹ : H ↑ ^ 2 • CZ⁻¹ ≈ CZ • H ↑ ^ 2
aux-HH↑-CZ⁻¹ = begin
  H ↑ ^ 2 • CZ⁻¹ ≈⟨ lemma-semi-HH↑-CZ^k′ p-1 ⟩
  (CZ^ ₋₁) ^ p-1 • H ↑ ^ 2 ≈⟨ cleft lemma-^-cong _ _ p-1 (refl' (Eq.cong (CZ ^_) lemma-toℕ₋₁)) ⟩
  (CZ ^ p-1) ^ p-1 • H ↑ ^ 2 ≈⟨ cleft aux-CZ⁻¹⁻¹ ⟩
  CZ • H ↑ ^ 2 ∎


fig-28-3 : ∀ (b*@(b , nzb) : ℤ* ₚ) (d : ℤ ₚ) ->
  let
  b⁻¹ = (b* ⁻¹) .proj₁
  nz : (₀ , b) ≢ (₀ , ₀)
  nz = aux-b≠0⇒ab≠0 ₀ b nzb
  nz' : (b , d) ≢ (₀ , ₀)
  nz' = aux-a≠0⇒ab≠0 b d nzb
  in
  
  [ b , d ]ᵇ • [ (₀ , b) , nz ]ᵃ • CZ ≈ (H ^ 3 • CZ • H ^ 3 • ZM (b* ⁻¹)) • [ (b , d) , nz' ]ᵃ ↑

fig-28-3 b*@(b , nzb) d = begin
  [ b , d ]ᵇ • [ (₀ , b) , nz ]ᵃ • CZ ≈⟨ cright cleft aux-abox-nzb b nzb ⟩
  [ b , d ]ᵇ • ⟦ (b , nzb) ⁻¹ ⟧ₘ • CZ ≈⟨ cright axiom (semi-M↓CZ ((b , nzb) ⁻¹)) ⟩
  [ b , d ]ᵇ • CZ^ b⁻¹ • ⟦ (b , nzb) ⁻¹ ⟧ₘ ≈⟨ cleft {!!} b d nzb ⟩
  (Ex • CX • ⟦ (b , nzb) ⁻¹ , HS^ -d/b ⟧ₘ₊ ↑) • CZ^ b⁻¹ • ⟦ (b , nzb) ⁻¹ ⟧ₘ ≈⟨ special-assoc (□ ^ 5 • □ ^ 2) (□ ^ 4 • □ ^ 2 • □) auto ⟩
  (Ex • CX • ⟦ (b , nzb) ⁻¹ ⟧ₘ ↑ • H ↑) • (S^ -d/b ↑ • CZ^ b⁻¹) • ⟦ (b , nzb) ⁻¹ ⟧ₘ ≈⟨ cright cleft sym (word-comm (toℕ b⁻¹) 1 (aux-comm-CZ-S^k↑ (-d/b))) ⟩
  (Ex • CX • ⟦ (b , nzb) ⁻¹ ⟧ₘ ↑ • H ↑) • (CZ^ b⁻¹ • S^ -d/b ↑) • ⟦ (b , nzb) ⁻¹ ⟧ₘ ≈⟨ sym (cleft cright cright lemma-cong↑ _ _ (semi-HM (b , nzb))) ⟩
  (Ex • CX • H ↑ • ⟦ (b , nzb) ⟧ₘ ↑) • (CZ^ b⁻¹ • S^ -d/b ↑) • ⟦ (b , nzb) ⁻¹ ⟧ₘ ≈⟨ special-assoc (□ ^ 4 • □ ^ 2 • □) (□ ^ 3 • □ ^ 2 • □ ^ 2) auto ⟩
  (Ex • CX • H ↑) • (⟦ (b , nzb) ⟧ₘ ↑ • CZ^ b⁻¹) • S^ -d/b ↑ • ⟦ (b , nzb) ⁻¹ ⟧ₘ ≈⟨ cright cleft lemma-M↑CZ^k b b⁻¹ nzb ⟩
  (Ex • CX • H ↑) • (CZ^ (b⁻¹ * b) • ⟦ (b , nzb) ⟧ₘ ↑) • S^ -d/b ↑ • ⟦ (b , nzb) ⁻¹ ⟧ₘ ≈⟨ cright cleft cleft refl' (Eq.cong CZ^ (lemma-⁻¹ˡ b {{nztoℕ {y = b} {neq0 = nzb}}})) ⟩
  (Ex • CX • H ↑) • (CZ • ⟦ (b , nzb) ⟧ₘ ↑) • S^ -d/b ↑ • ⟦ (b , nzb) ⁻¹ ⟧ₘ ≈⟨ special-assoc ((□ • □ ^ 3 • □) • □ ^ 2 • □) (□ ^ 6 • □ ^ 2) auto ⟩
  (Ex • H ^ 3 • CZ • H • H ↑ • CZ) • ⟦ (b , nzb) ⟧ₘ ↑ • S^ -d/b ↑ • ⟦ (b , nzb) ⁻¹ ⟧ₘ ≈⟨ cleft cright cright aux-hEx' ⟩
  (Ex • H ^ 3 • H ↑ ^ 3 • H ^ 3 • CZ⁻¹ • H ↑ ^ 3 • H ^ 3 • Ex) • ⟦ (b , nzb) ⟧ₘ ↑ • S^ -d/b ↑ • ⟦ (b , nzb) ⁻¹ ⟧ₘ ≈⟨ cleft special-assoc (□ ^ 8) (□ • □ ^ 6 • □) auto ⟩
  (Ex • (H ^ 3 • H ↑ ^ 3 • H ^ 3 • CZ⁻¹ • H ↑ ^ 3 • H ^ 3) • Ex) • ⟦ (b , nzb) ⟧ₘ ↑ • S^ -d/b ↑ • ⟦ (b , nzb) ⁻¹ ⟧ₘ ≈⟨ cleft sym (lemma-Ex-dual ((H ^ 3 • H ↑ ^ 3 • H ^ 3 • CZ⁻¹ • H ↑ ^ 3 • H ^ 3))) ⟩
  ((H ↑ ^ 3 • H ^ 3 • H ↑ ^ 3 • dual CZ⁻¹ • H ^ 3 • H ↑ ^ 3)) • ⟦ (b , nzb) ⟧ₘ ↑ • S^ -d/b ↑ • ⟦ (b , nzb) ⁻¹ ⟧ₘ ≈⟨ cleft special-assoc (□ ^ 4 ) (□ ^ 3 • □) auto ⟩
  ((H ↑ ^ 3 • H ^ 3 • H ↑ ^ 3) • dual CZ⁻¹ • H ^ 3 • H ↑ ^ 3) • ⟦ (b , nzb) ⟧ₘ ↑ • S^ -d/b ↑ • ⟦ (b , nzb) ⁻¹ ⟧ₘ ≈⟨ cleft cong (rewrite-sym0 100 auto) (cleft refl' (aux-dual-CZ^k p-1)) ⟩
  ((H ^ 3 • H ↑ ^ 2) • CZ⁻¹ • H ^ 3 • H ↑ ^ 3) • ⟦ (b , nzb) ⟧ₘ ↑ • S^ -d/b ↑ • ⟦ (b , nzb) ⁻¹ ⟧ₘ ≈⟨ cleft special-assoc (□ ^ 2 • □ ^ 3) (□ • □ ^ 2 • □ ^ 2) auto ⟩
  (H ^ 3 • (H ↑ ^ 2 • CZ⁻¹) • H ^ 3 • H ↑ ^ 3) • ⟦ (b , nzb) ⟧ₘ ↑ • S^ -d/b ↑ • ⟦ (b , nzb) ⁻¹ ⟧ₘ ≈⟨ cleft cright cleft aux-HH↑-CZ⁻¹ ⟩
  (H ^ 3 • (CZ • H ↑ ^ 2) • H ^ 3 • H ↑ ^ 3) • ⟦ (b , nzb) ⟧ₘ ↑ • S^ -d/b ↑ • ⟦ (b , nzb) ⁻¹ ⟧ₘ ≈⟨ cleft cright assoc ⟩
  (H ^ 3 • CZ • H ↑ ^ 2 • H ^ 3 • H ↑ ^ 3) • ⟦ (b , nzb) ⟧ₘ ↑ • S^ -d/b ↑ • ⟦ (b , nzb) ⁻¹ ⟧ₘ ≈⟨ cleft rewrite-sym0 100 auto ⟩
  (H ^ 3 • CZ • H ^ 3 • H ↑) • ⟦ (b , nzb) ⟧ₘ ↑ • S^ -d/b ↑ • ⟦ (b , nzb) ⁻¹ ⟧ₘ ≈⟨ special-assoc (□ ^ 4 • □ ^ 3) (□ ^ 3 • □ ^ 2 • □ ^ 2) auto ⟩
  (H ^ 3 • CZ • H ^ 3) • (H ↑ • ⟦ (b , nzb) ⟧ₘ ↑) • S^ -d/b ↑ • ⟦ (b , nzb) ⁻¹ ⟧ₘ ≈⟨ cright cleft lemma-cong↑ _ _ (semi-HM (b , nzb)) ⟩
  (H ^ 3 • CZ • H ^ 3) • (⟦ (b , nzb) ⁻¹ ⟧ₘ ↑ • H ↑) • S^ -d/b ↑ • ⟦ (b , nzb) ⁻¹ ⟧ₘ ≈⟨ cright special-assoc (□ ^ 2 • □ ^ 2) (□ ^ 3 • □) auto ⟩
  (H ^ 3 • CZ • H ^ 3) • (⟦ (b , nzb) ⁻¹ ⟧ₘ ↑ • H ↑ • S^ -d/b ↑) • ⟦ (b , nzb) ⁻¹ ⟧ₘ ≈⟨ cright sym (aux-comm-MMC ((b , nzb) ⁻¹) ((b , nzb) ⁻¹) (HS^ -d/b)) ⟩
  (H ^ 3 • CZ • H ^ 3) • ⟦ (b , nzb) ⁻¹ ⟧ₘ • (⟦ (b , nzb) ⁻¹ ⟧ₘ ↑ • H ↑ • S^ -d/b ↑) ≈⟨ special-assoc (□ ^ 3 • □ ^ 2) (□ ^ 4 • □) auto ⟩
  (H ^ 3 • CZ • H ^ 3 • ⟦ (b , nzb) ⁻¹ ⟧ₘ) • (⟦ (b , nzb) ⁻¹ ⟧ₘ ↑ • H ↑ • S^ -d/b ↑) ≈⟨ refl ⟩
  (H ^ 3 • CZ • H ^ 3 • ZM (b* ⁻¹)) • (⟦ (b , nzb) ⁻¹ ⟧ₘ ↑ • H ↑ • S^ -d/b ↑)  ≈⟨ cright sym (lemma-cong↑ _ _ (aux-abox-nza b d nzb) ) ⟩
  (H ^ 3 • CZ • H ^ 3 • ZM (b* ⁻¹)) • [ (b , d) , nz' ]ᵃ ↑ ∎
  where
  b⁻¹ = (b* ⁻¹) .proj₁
  nz : (₀ , b) ≢ (₀ , ₀)
  nz = aux-b≠0⇒ab≠0 ₀ b nzb
  nz' : (b , d) ≢ (₀ , ₀)
  nz' = aux-a≠0⇒ab≠0 b d nzb
  -d/b = - d * b⁻¹


-}
