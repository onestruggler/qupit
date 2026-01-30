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



module N.Pushing.DS (p-2 : ℕ) (p-prime : Prime (2+ p-2))  where

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
open import N.Lemmas-2Qupit-Sym p-2 p-prime
open import N.NF2-Sym p-2 p-prime
--open Lemmas-2Q 2

open import N.NF1 p-2 p-prime
open import N.Ex-Sym p-2 p-prime
open import N.Ex-Sym1 p-2 p-prime
open import N.Ex-Sym2 p-2 p-prime
open import N.Ex-Sym3 p-2 p-prime
open import N.Ex-Sym4 p-2 p-prime
open import N.Ex-Sym5 p-2 p-prime hiding (module L0)
open import N.Ex-Sym2n p-2 p-prime
open import N.Ex-Sym3n p-2 p-prime

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
open import N.Lemmas4-Sym p-2 p-prime
open import N.Pushing.DH p-2 p-prime
open import N.Pushing.AS p-2 p-prime



dir-of-DS : D -> Word (Gen (₁₊ n))
dir-of-DS (₀ , b) = S
dir-of-DS (₁₊ _ , _) = ε

d-of-DS : D -> D
d-of-DS (₀ , b) = ₀ , b
d-of-DS (a@(₁₊ _) , b) = a , b + - a

aux-DS : let open PB ((₂₊ n) QRel,_===_) in

  ∀ d ->
  let
  d' = d-of-DS d
  w = dir-of-DS d
  in
  [ d ]ᵈ • S ≈ w ↑ • [ d' ]ᵈ

aux-DS {n} d@(a@₀ , b) = claim
  where
  open PB ((₂₊ n) QRel,_===_)  
  open PP ((₂₊ n) QRel,_===_)
  open SR word-setoid

  claim : [ d ]ᵈ • S ≈ S ↑ • [ d ]ᵈ
  claim = begin
    ([ d ]ᵈ • S) ≈⟨ assoc ⟩
    (Ex • CZ^ (- b) • S) ≈⟨ (cright word-comm (toℕ (- b)) 1 (axiom comm-CZ-S↓)) ⟩
    Ex • S • CZ^ (- b) ≈⟨ sym assoc ⟩
    (Ex • S) • CZ^ (- b) ≈⟨ (cleft lemma-Ex-S) ⟩
    (S ↑ • Ex) • CZ^ (- b) ≈⟨ assoc ⟩
    S ↑ • [ d ]ᵈ ∎
    

aux-DS {n} d@(a@(₁₊ _) , b) = claim
  where
  a⁻¹ = ((a , λ ()) ⁻¹) .proj₁
  -b/a = - b * a⁻¹
  aux : -b/a + ₁ ≡ - (b + - a) * a⁻¹
  aux = Eq.sym ( begin
    - (b + - a) * a⁻¹ ≡⟨ Eq.cong (_* a⁻¹) (Eq.sym (-‿+-comm b (- a))) ⟩
    (- b + - - a) * a⁻¹ ≡⟨ Eq.cong (\ xx -> (- b + xx) * a⁻¹) (-‿involutive a) ⟩
    (- b + a) * a⁻¹ ≡⟨ *-distribʳ-+ a⁻¹ (- b) a ⟩
    - b * a⁻¹ + a * a⁻¹ ≡⟨ Eq.cong (- b * a⁻¹ +_) (lemma-⁻¹ʳ a {{nztoℕ {y = a} {neq0 = λ ()}}}) ⟩
    - b * a⁻¹ + ₁ ≡⟨ auto ⟩
    -b/a + ₁ ∎
    )
    where
    open ≡-Reasoning

  
  open PB ((₂₊ n) QRel,_===_)  
  open PP ((₂₊ n) QRel,_===_)
  open SR word-setoid
  open Lemmas0 (₁₊ n)
  open Pattern-Assoc

  w = S
  d' = (a , b + - a)
  
  claim : [ d ]ᵈ • S ≈ (ε ↑) • [ d' ]ᵈ
  claim = begin
    ((Ex • CZ^ (- a) • H • S^ -b/a) • S) ≈⟨ special-assoc (□ ^ 4 • □) (□ ^ 5) auto ⟩
    Ex • CZ^ (- a) • H • S^ -b/a • S ≈⟨ (cright cright cright lemma-S^k+l -b/a ₁) ⟩
    Ex • CZ^ (- a) • H • S^ (-b/a + ₁) ≈⟨ (cright cright cright refl' (Eq.cong S^ aux)) ⟩
    Ex • CZ^ (- a) • H • S^ (- (b + - a) * a⁻¹) ≈⟨ refl ⟩
    ([ (a , (b + - a)) ]ᵈ) ≈⟨ sym left-unit ⟩
    ε • ([ (a , (b + - a)) ]ᵈ)  ∎



aux-DS↑ : let open PB ((₂₊ n) QRel,_===_) in

  ∀ d -> [ d ]ᵈ • S ↑ ≈ S • [ d ]ᵈ

aux-DS↑ {n} d@(a@₀ , b) = begin
  ([ d ]ᵈ • S ↑) ≈⟨ assoc ⟩
  (Ex • CZ^ (- b) • S ↑) ≈⟨ (cright word-comm (toℕ (- b)) 1 (axiom comm-CZ-S↑)) ⟩
  Ex • S ↑ • CZ^ (- b) ≈⟨ sym assoc ⟩
  (Ex • S ↑) • CZ^ (- b) ≈⟨ (cleft lemma-Ex-S↑-n) ⟩
  (S • Ex) • CZ^ (- b) ≈⟨ assoc ⟩
  S • [ d ]ᵈ ∎
  where
  
  open PB ((₂₊ n) QRel,_===_)  
  open PP ((₂₊ n) QRel,_===_)
  open SR word-setoid
  open Lemmas0 (₁₊ n)
  open Pattern-Assoc
  
aux-DS↑ {n} d@(a@(₁₊ _) , b) = begin
  [ d ]ᵈ • S ↑ ≈⟨ refl ⟩
  (Ex • CZ^ (- a) • H • S^ -b/a) • S ↑ ≈⟨ special-assoc (□ ^ 3 • □) (□ ^ 2 • □ ^ 2) auto ⟩
  (Ex • CZ^ (- a)) • (H • S^ -b/a) • S ↑ ≈⟨ (cright comm-hs-w↑ -b/a S) ⟩
  (Ex • CZ^ (- a)) • S ↑ • H • S^ -b/a ≈⟨ special-assoc (□ ^ 2 • □ ^ 2) (□ • □ ^ 2 • □) auto ⟩
  Ex • (CZ^ (- a) • S ↑) • H • S^ -b/a ≈⟨ (cright cleft word-comm (toℕ (- a)) 1 (axiom comm-CZ-S↑)) ⟩
  Ex • (S ↑ • CZ^ (- a)) • H • S^ -b/a ≈⟨ sym (special-assoc (□ ^ 2 • □ ^ 2) (□ • □ ^ 2 • □) auto ) ⟩
  (Ex • S ↑) • CZ^ (- a) • H • S^ -b/a ≈⟨ (cleft lemma-Ex-Sᵏ↑ 1) ⟩
  (S • Ex) • CZ^ (- a) • H • S^ -b/a ≈⟨ assoc ⟩
  S • [ d ]ᵈ ∎
  where
  
  open PB ((₂₊ n) QRel,_===_)  
  open PP ((₂₊ n) QRel,_===_)
  open SR word-setoid
  open Lemmas0 (₁₊ n)
  open Pattern-Assoc
  
  a⁻¹ = ((a , λ ()) ⁻¹) .proj₁
  -b/a = - b * a⁻¹
