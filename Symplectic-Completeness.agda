------------------------------------------------------------------------
-- Symplectic-Completeness.agda
--
-- A pure-symplectic analogue of Theorem 4.4 of doc/qudit-quantum-June12.pdf.
--
-- Everything here lives at the level of the symplectic rewrite relation
-- of N.Symplectic (i.e. ≈ for the presentation (n QRel,_===_)); there is
-- NO Clifford / Pauli component.  In `BoxRelations.agda` it is shown, from
-- the N.Symplectic relations, how to push a single generator through each
-- normal box (A, E, L, B, D, BB, B↑, DD).
--
-- This file does the two remaining structural steps the paper describes:
--
--   (1) chain those box relations into a single rule for pushing a gate
--       through an *LM box*  (`coset-update`), and
--
--   (2) by induction over the normal-form structure, merge a gate -- and
--       hence any circuit -- into a normal form  (`merge-gate`,
--       `merge-word`, `completeness`).
--
-- This is the normalisation/completeness mechanism (Prop. 4.3 / Lemma 4.2,
-- underlying Thm. 4.4) for the *pure-symplectic* case.
--
-- The per-box LM step `coset-update` is taken as input: its constituent
-- box relations are proven in `BoxRelations.agda`, and its full
-- constructor-by-constructor chaining is the (in-progress)
-- `N.Completeness.lemma-coset-update`.  Given that one step, the
-- normalisation induction below is complete.
------------------------------------------------------------------------

{-# OPTIONS --termination-depth=4 #-}

open import Data.Nat hiding (_^_ ; _+_ ; _*_)
open import Data.Nat.Primality

module Symplectic-Completeness (p-2 : ℕ) (p-prime : Prime (2+ p-2)) where

open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂ ; ∃)
open import Data.Unit using (⊤ ; tt)

import Presentation.Base as PB
import Presentation.Properties as PP
import Relation.Binary.Reasoning.Setoid as SR

open import Word.Base as WB

open import Zp.ModularArithmetic
open PrimeModulus p-2 p-prime

open import N.Symplectic p-2 p-prime
open Symplectic renaming (M to ZM)
open Lemmas-Sym using (lemma-cong↑)

open import N.LM-Sym p-2 p-prime

pattern ₀ = zero
pattern ₁₊ ⱼ = suc ⱼ

------------------------------------------------------------------------
-- (1) Pushing a gate through an LM box.
--
-- This is the box-relation chaining: its per-box constituents are the
-- relations A←H/S, E←S, L←CZ, B←H↑/S↑/S, D←H/S↑/S/CZ, BB←CZ↑, B↑←CZ,
-- DD←CZ proven in BoxRelations.agda from the N.Symplectic relations.
------------------------------------------------------------------------
postulate
  coset-update : ∀ {n} (lm : LM (₁₊ n)) (g : Gen (₁₊ n)) →
    let open PB ((₁₊ n) QRel,_===_) in
    ∃ λ lm' → ∃ λ w → [ lm ]ˡᵐ • [ g ]ʷ ≈ w ↑ • [ lm' ]ˡᵐ

------------------------------------------------------------------------
-- (2) Merging a gate, and then any circuit, into a normal form.
--
-- A normal form is  [ (nf , lm) ] = [ nf ] ↑ • [ lm ]ˡᵐ , so pushing a
-- gate g in from the right uses coset-update on the outer LM box to get a
-- residual word w one level up, which is then merged into the inner normal
-- form nf by the induction hypothesis.
------------------------------------------------------------------------

merge-gate : ∀ {n} (nf : NF (₁₊ n)) (g : Gen (₁₊ n)) →
  let open PB ((₁₊ n) QRel,_===_) in
  ∃ λ nf' → [ nf ] • [ g ]ʷ ≈ [ nf' ]

merge-word : ∀ {n} (nf : NF n) (w : Word (Gen n)) →
  let open PB (n QRel,_===_) in
  ∃ λ nf' → [ nf ] • w ≈ [ nf' ]

merge-gate {n} (nf₀ , lm) g = (nf₀' , lm') , proof
  where
  open PB ((₁₊ n) QRel,_===_)
  open PP ((₁₊ n) QRel,_===_)
  open SR word-setoid
  cu  = coset-update lm g
  lm' = cu .proj₁
  w   = cu .proj₂ .proj₁
  e   = cu .proj₂ .proj₂          -- [ lm ]ˡᵐ • [ g ]ʷ ≈ w ↑ • [ lm' ]ˡᵐ
  mw  = merge-word {n} nf₀ w
  nf₀' = mw .proj₁
  e₀  = mw .proj₂                  -- [ nf₀ ] • w ≈ [ nf₀' ]
  proof : [ nf₀ , lm ] • [ g ]ʷ ≈ [ nf₀' , lm' ]
  proof = begin
    [ nf₀ , lm ] • [ g ]ʷ            ≈⟨ assoc ⟩
    [ nf₀ ] ↑ • ([ lm ]ˡᵐ • [ g ]ʷ)  ≈⟨ cright e ⟩
    [ nf₀ ] ↑ • (w ↑ • [ lm' ]ˡᵐ)    ≈⟨ sym assoc ⟩
    ([ nf₀ ] ↑ • w ↑) • [ lm' ]ˡᵐ    ≈⟨ cleft (lemma-cong↑ ([ nf₀ ] • w) [ nf₀' ] e₀) ⟩
    [ nf₀' ] ↑ • [ lm' ]ˡᵐ           ∎

merge-word {n}      nf ε         = nf , right-unit
  where open PB (n QRel,_===_)
merge-word {₀}      nf [ () ]ʷ
merge-word {₁₊ n}   nf [ g ]ʷ    = merge-gate {n} nf g
merge-word {n}      nf (w₁ • w₂) = nf₂ , proof
  where
  open PB (n QRel,_===_)
  open PP (n QRel,_===_)
  open SR word-setoid
  m1  = merge-word {n} nf  w₁
  nf₁ = m1 .proj₁
  e₁  = m1 .proj₂                  -- [ nf ] • w₁ ≈ [ nf₁ ]
  m2  = merge-word {n} nf₁ w₂
  nf₂ = m2 .proj₁
  e₂  = m2 .proj₂                  -- [ nf₁ ] • w₂ ≈ [ nf₂ ]
  proof : [ nf ] • (w₁ • w₂) ≈ [ nf₂ ]
  proof = begin
    [ nf ] • (w₁ • w₂)  ≈⟨ sym assoc ⟩
    ([ nf ] • w₁) • w₂  ≈⟨ cleft e₁ ⟩
    [ nf₁ ] • w₂        ≈⟨ e₂ ⟩
    [ nf₂ ]             ∎

------------------------------------------------------------------------
-- Completeness (pure-symplectic analogue of Theorem 4.4):
--
-- any circuit `w`, appended on the right of a normal form, rewrites by the
-- N.Symplectic relations to a normal form.  Starting from the normal form
-- of the identity, this normalises an arbitrary symplectic circuit.
------------------------------------------------------------------------
completeness : ∀ {n} (nf : NF n) (w : Word (Gen n)) →
  let open PB (n QRel,_===_) in
  ∃ λ nf' → [ nf ] • w ≈ [ nf' ]
completeness = merge-word
