{-# OPTIONS --safe #-}
-- Pushing a gate through the M-box, for the flat LM structure.
-- M←S : [ m ]ᵐ • S ≈ w↑ • [ m' ]ᵐ  (residue w is LIFTED — no wire-0 leftover).
open import Data.Nat hiding (_^_ ; _+_ ; _*_)
open import Data.Nat.Primality

module N.PushM (p-2 : ℕ) (p-prime : Prime (2+ p-2)) where

open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂ ; ∃)
open import Data.Vec using (Vec ; _∷_ ; [])
open import Data.Fin using (toℕ)

import Presentation.Base as PB
import Presentation.Properties as PP
import Relation.Binary.Reasoning.Setoid as SR

open import Word.Base as WB
open import Zp.ModularArithmetic
open PrimeModulus p-2 p-prime

open import N.Symplectic p-2 p-prime
open Symplectic renaming (M to ZM)
open Lemmas-Sym
open import N.LM-Sym p-2 p-prime
open import N.Pushing.DS p-2 p-prime using (aux-DS ; dir-of-DS ; d-of-DS)
import N.BR.One.E p-2 p-prime 0 as OE

pattern ₀ = zero
pattern ₁₊ ⱼ = suc ⱼ
pattern ₂₊ ⱼ = suc (suc ⱼ)

M←S : ∀ {n} (m : M (₁₊ n)) → let open PB ((₁₊ n) QRel,_===_) in
  ∃ λ m' → ∃ λ w → [ m ]ᵐ • S ≈ w ↑ • [ m' ]ᵐ

-- M 1 = E : S merges into the E-box (E←S), residue ε.
M←S {0} e = (e + - ₁) , ε , claim
  where
  open PB (1 QRel,_===_)
  open PP (1 QRel,_===_)
  open SR word-setoid
  claim : [ e ]ᵉ • S ≈ ε ↑ • [ e + - ₁ ]ᵉ
  claim = begin
    [ e ]ᵉ • S          ≈⟨ OE.lemma-single-qupit-br-E e ⟩
    [ e + - ₁ ]ᵉ        ≈⟨ sym left-unit ⟩
    ε ↑ • [ e + - ₁ ]ᵉ  ∎

-- M (₂₊ n) = E × Vec D : S enters the first D-box (aux-DS gives a LIFTED
-- residue), commuting past the rest of the ladder and the E-box.
M←S {₁₊ n} (e , d₀ ∷ rest) = (e , d-of-DS d₀ ∷ rest) , dir-of-DS d₀ , claim
  where
  open PB ((₂₊ n) QRel,_===_)
  open PP ((₂₊ n) QRel,_===_)
  open SR word-setoid
  w₀  = dir-of-DS d₀
  d₀' = d-of-DS d₀
  claim : [ e , d₀ ∷ rest ]ᵐ • S ≈ w₀ ↑ • [ e , d₀' ∷ rest ]ᵐ
  claim = begin
    (S^ (- e) • ([ d₀ ]ᵈ • [ rest ]ᵛᵈ ↑)) • S     ≈⟨ assoc ⟩
    S^ (- e) • (([ d₀ ]ᵈ • [ rest ]ᵛᵈ ↑) • S)     ≈⟨ cright assoc ⟩
    S^ (- e) • ([ d₀ ]ᵈ • ([ rest ]ᵛᵈ ↑ • S))     ≈⟨ cright (cright (sym (lemma-comm-S-w↑ [ rest ]ᵛᵈ))) ⟩
    S^ (- e) • ([ d₀ ]ᵈ • (S • [ rest ]ᵛᵈ ↑))     ≈⟨ cright (sym assoc) ⟩
    S^ (- e) • (([ d₀ ]ᵈ • S) • [ rest ]ᵛᵈ ↑)     ≈⟨ cright (cleft (aux-DS d₀)) ⟩
    S^ (- e) • ((w₀ ↑ • [ d₀' ]ᵈ) • [ rest ]ᵛᵈ ↑) ≈⟨ cright assoc ⟩
    S^ (- e) • (w₀ ↑ • ([ d₀' ]ᵈ • [ rest ]ᵛᵈ ↑)) ≈⟨ sym assoc ⟩
    (S^ (- e) • w₀ ↑) • ([ d₀' ]ᵈ • [ rest ]ᵛᵈ ↑) ≈⟨ cleft (lemma-comm-Sᵏ-w↑ (toℕ (- e)) w₀) ⟩
    (w₀ ↑ • S^ (- e)) • ([ d₀' ]ᵈ • [ rest ]ᵛᵈ ↑) ≈⟨ assoc ⟩
    w₀ ↑ • (S^ (- e) • ([ d₀' ]ᵈ • [ rest ]ᵛᵈ ↑)) ∎

