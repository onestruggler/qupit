{-# OPTIONS --safe #-}
-- Wire-0 S-power absorption for the NEW uniform LM structure
--   LM (₂₊ n) = (M (₂₊ n) × L (₂₊ n)) × LM (₁₊ n)
--   [ ((m , l) , lm) ]ˡᵐ = [ m ]ᵐ • [ l ]ˡ • [ lm ]ˡᵐ ↑
-- Every LM box leads with an M-box, which leads with S^(-e); so a wire-0
-- S^k merges straight into that E-component -- no recursion, no residue.
open import Data.Nat hiding (_^_ ; _+_ ; _*_)
open import Data.Nat.Primality

module N.AbsorbS (p-2 : ℕ) (p-prime : Prime (2+ p-2)) where

open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂ ; ∃)
open import Data.Vec using (Vec)

import Presentation.Base as PB
import Presentation.Properties as PP
import Relation.Binary.Reasoning.Setoid as SR
import Relation.Binary.PropositionalEquality as Eq
open import Word.Base as WB

open import Zp.ModularArithmetic
open PrimeModulus p-2 p-prime

open import N.Symplectic p-2 p-prime
open Symplectic renaming (M to ZM)
open Lemmas-Sym
open import N.LM-Sym p-2 p-prime
open import N.NF1-Sym p-2 p-prime using (⟦_⟧₁ ; ⟦_⟧ₘ ; ⟦_⟧ₕₛ)
open import Algebra.Properties.Ring (+-*-ring p-2)

pattern ₀ = zero
pattern ₁₊ ⱼ = suc ⱼ
pattern ₂₊ ⱼ = suc (suc ⱼ)

------------------------------------------------------------------------
-- absorb-S : push a wire-0 S-power from the LEFT through an LM box.
-- The residual is always the empty word ε (i.e. ε ↑), because S^k is
-- entirely absorbed into the leading E-component.
------------------------------------------------------------------------
absorb-S : ∀ {n} (k : ℤ ₚ) (lm : LM (₁₊ n)) → let open PB ((₁₊ n) QRel,_===_) in
  ∃ λ lm' → ∃ λ w → S^ k • [ lm ]ˡᵐ ≈ w ↑ • [ lm' ]ˡᵐ

-- LM 1 = NF1 : ⟦(s,m,c)⟧₁ = S^s • …  →  merge into the leading S-power.
absorb-S {0} k (s , m , c) = (k + s , m , c) , ε , claim
  where
  open PB (1 QRel,_===_)
  open PP (1 QRel,_===_)
  open SR word-setoid
  open Lemmas0 0
  claim : S^ k • ⟦ (s , m , c) ⟧₁ ≈ ε ↑ • ⟦ (k + s , m , c) ⟧₁
  claim = begin
    S^ k • (S^ s • ⟦ m ⟧ₘ • ⟦ c ⟧ₕₛ)        ≈⟨ sym assoc ⟩
    (S^ k • S^ s) • (⟦ m ⟧ₘ • ⟦ c ⟧ₕₛ)      ≈⟨ cleft lemma-S^k+l k s ⟩
    S^ (k + s) • (⟦ m ⟧ₘ • ⟦ c ⟧ₕₛ)         ≈⟨ sym left-unit ⟩
    ε ↑ • (S^ (k + s) • (⟦ m ⟧ₘ • ⟦ c ⟧ₕₛ)) ∎

-- LM (₂₊ n) = (M , L) : [(m,l)]ˡᵐ = (S^(-e) • [vd]) • [l]
--   →  merge S^k into the E-component e; everything else is untouched.
absorb-S {₁₊ n} k ((e , vd) , l) = ((e' , vd) , l) , ε , claim
  where
  open PB ((₂₊ n) QRel,_===_)
  open PP ((₂₊ n) QRel,_===_)
  open SR word-setoid
  open Lemmas0 (₁₊ n)
  e' = - (k + - e)
  claim : S^ k • [ (e , vd) , l ]ˡᵐ ≈ ε ↑ • [ (e' , vd) , l ]ˡᵐ
  claim = begin
    S^ k • (([ e ]ᵉ • [ vd ]ᵛᵈ) • [ l ]ˡ)  ≈⟨ sym assoc ⟩
    (S^ k • ([ e ]ᵉ • [ vd ]ᵛᵈ)) • [ l ]ˡ  ≈⟨ cleft sym assoc ⟩
    ((S^ k • [ e ]ᵉ) • [ vd ]ᵛᵈ) • [ l ]ˡ  ≈⟨ cleft (cleft (lemma-S^k+l k (- e))) ⟩
    ((S^ (k + - e) • [ vd ]ᵛᵈ) • [ l ]ˡ)   ≈⟨ cleft (cleft (refl' (Eq.cong (λ z → S^ z) (Eq.sym (-‿involutive (k + - e)))))) ⟩
    (([ e' ]ᵉ • [ vd ]ᵛᵈ) • [ l ]ˡ)        ≈⟨ sym left-unit ⟩
    ε ↑ • (([ e' ]ᵉ • [ vd ]ᵛᵈ) • [ l ]ˡ)  ∎
