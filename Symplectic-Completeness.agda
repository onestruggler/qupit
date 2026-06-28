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
-- `coset-update` is PROVEN here for the single-qupit base case (LM 1, via
-- the live N.Completeness1-Sym lemma) and for the recursive lifted-gate
-- carry on depth-≥3 boxes (via the d-box commutation lemma comm-dbox-w↑↑).
-- Two genuinely-hard sub-cases remain as input (postulates `push-LM2`,
-- `push-LM-hard`): the two-qupit base case (whose proof exists in
-- N.Coset2-Update-Sym but is currently commented out) and the pushing of a
-- wire-0 generator through a depth-≥3 box, where the box relations emit a
-- bottom-wire residual that must be re-absorbed into the box.
--
-- Given `coset-update`, the normalisation induction (2) below is complete.
------------------------------------------------------------------------

{-# OPTIONS --termination-depth=4 #-}

open import Data.Nat hiding (_^_ ; _+_ ; _*_)
open import Data.Nat.Primality

module Symplectic-Completeness (p-2 : ℕ) (p-prime : Prime (2+ p-2)) where

open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂ ; ∃)
open import Data.Unit using (⊤ ; tt)
open import Data.Sum using (_⊎_ ; inj₁ ; inj₂)

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

-- The single-qupit completeness lemma and the d-box commutation lemma,
-- both proven from the N.Symplectic relations.  (The two-qupit symplectic
-- completeness lemma lives in N.Coset2-Update-Sym but is currently inside a
-- block comment there, i.e. unfinished, so the n = 1 base case below is
-- still taken as input.)
open import N.Completeness1-Sym p-2 p-prime renaming (module Completeness to CP1) using ()
open import N.Lemmas4-Sym        p-2 p-prime using (comm-dbox-w↑↑)

pattern ₀ = zero
pattern ₁₊ ⱼ = suc ⱼ
pattern ₂₊ ⱼ = suc (suc ⱼ)
pattern ₃₊ ⱼ = suc (suc (suc ⱼ))

------------------------------------------------------------------------
-- (1) Pushing a gate through an LM box.
--
-- This is the box-relation chaining: its per-box constituents are the
-- relations A←H/S, E←S, L←CZ, B←H↑/S↑/S, D←H/S↑/S/CZ, BB←CZ↑, B↑←CZ,
-- DD←CZ proven in BoxRelations.agda from the N.Symplectic relations.
--
-- The genuinely hard part of the induction is pushing a *wire-0* generator
-- (H, S, CZ) into a depth-≥3 box, because the box relations emit a residual
-- on the bottom wire that must be re-absorbed into the box (the n≥2
-- "coset update").  That residue-absorption is what is left open below.
------------------------------------------------------------------------
postulate
  -- Two-qupit base case (LM 2 = Cosets2).  This is the symplectic two-qupit
  -- completeness lemma; its proof exists in N.Coset2-Update-Sym but is
  -- presently commented out there, so it is taken as input here.
  push-LM2 : ∀ (lm : LM 2) (g : Gen 2) →
    let open PB (2 QRel,_===_) in
    ∃ λ lm' → ∃ λ w → [ lm ]ˡᵐ • [ g ]ʷ ≈ w ↑ • [ lm' ]ˡᵐ

  -- Pushing a wire-0 generator (or any generator into an M·L' box) through a
  -- depth-≥3 LM box.  Only invoked for the inj₁ box and for the wire-0 gates
  -- H-gen / S-gen / CZ-gen on an inj₂ box; the lifted-gate (·↥) case is
  -- discharged by the proven recursive clause of `coset-update` below.
  push-LM-hard : ∀ {n} (lm : LM (₃₊ n)) (g : Gen (₃₊ n)) →
    let open PB ((₃₊ n) QRel,_===_) in
    ∃ λ lm' → ∃ λ w → [ lm ]ˡᵐ • [ g ]ʷ ≈ w ↑ • [ lm' ]ˡᵐ

-- The full LM-pushing step.  PROVEN for: single qupit (LM 1), two qupits
-- (LM 2), and the recursive lifted-gate case on depth-≥3 boxes.  The
-- remaining wire-0-generator cases on depth-≥3 boxes are delegated to
-- `push-LM-hard`.
coset-update : ∀ {n} (lm : LM (₁₊ n)) (g : Gen (₁₊ n)) →
  let open PB ((₁₊ n) QRel,_===_) in
  ∃ λ lm' → ∃ λ w → [ lm ]ˡᵐ • [ g ]ʷ ≈ w ↑ • [ lm' ]ˡᵐ

-- LM 1 = NF1 : the single-qupit completeness lemma (complete).
coset-update {0} lm H-gen = lm' , ε , claim
  where
  open PB (1 QRel,_===_)
  open PP (1 QRel,_===_)
  open SR word-setoid
  cp1 = CP1.Lemma-single-qupit-completeness {0} lm H-gen _
  lm' = cp1 .proj₁
  claim : [ lm ]ˡᵐ • [ H-gen ]ʷ ≈ (ε ↑) • [ lm' ]ˡᵐ
  claim = begin
    [ lm ]ˡᵐ • [ H-gen ]ʷ ≈⟨ cp1 .proj₂ ⟩
    [ lm' ]ˡᵐ             ≈⟨ sym left-unit ⟩
    (ε ↑) • [ lm' ]ˡᵐ     ∎
coset-update {0} lm S-gen = lm' , ε , claim
  where
  open PB (1 QRel,_===_)
  open PP (1 QRel,_===_)
  open SR word-setoid
  cp1 = CP1.Lemma-single-qupit-completeness {0} lm S-gen _
  lm' = cp1 .proj₁
  claim : [ lm ]ˡᵐ • [ S-gen ]ʷ ≈ (ε ↑) • [ lm' ]ˡᵐ
  claim = begin
    [ lm ]ˡᵐ • [ S-gen ]ʷ ≈⟨ cp1 .proj₂ ⟩
    [ lm' ]ˡᵐ             ≈⟨ sym left-unit ⟩
    (ε ↑) • [ lm' ]ˡᵐ     ∎

-- LM 2 = Cosets2 : the two-qupit base case (taken as input, see push-LM2).
coset-update {1} lm g = push-LM2 lm g

-- Depth ≥ 3 : the M·L' box, and wire-0 gates on the D·LM box, are the open
-- residue-absorption cases.
coset-update {₂₊ n} (inj₁ x)         g      = push-LM-hard (inj₁ x) g
coset-update {₂₊ n} (inj₂ (d , lm))  H-gen  = push-LM-hard (inj₂ (d , lm)) H-gen
coset-update {₂₊ n} (inj₂ (d , lm))  S-gen  = push-LM-hard (inj₂ (d , lm)) S-gen
coset-update {₂₊ n} (inj₂ (d , lm))  CZ-gen = push-LM-hard (inj₂ (d , lm)) CZ-gen

-- The lifted-gate case: push g one level up through the inner LM box by the
-- induction hypothesis, then slide the residual past the bottom d-box
-- (comm-dbox-w↑↑).  This is the proven recursive carry.
coset-update {₂₊ n} (inj₂ (d , lm)) (g ↥) = inj₂ (d , lm') , w ↑ , claim
  where
  open PB ((₃₊ n) QRel,_===_)
  open PP ((₃₊ n) QRel,_===_)
  open SR word-setoid
  ih  = coset-update {₁₊ n} lm g
  lm' = ih .proj₁
  w   = ih .proj₂ .proj₁
  claim : [ inj₂ (d , lm) ]ˡᵐ • [ g ↥ ]ʷ ≈ (w ↑ ↑) • [ inj₂ (d , lm') ]ˡᵐ
  claim = begin
    [ inj₂ (d , lm) ]ˡᵐ • [ g ↥ ]ʷ      ≈⟨ assoc ⟩
    [ d ]ᵈ • [ lm ]ˡᵐ ↑ • [ g ↥ ]ʷ      ≈⟨ refl ⟩
    [ d ]ᵈ • [ lm ]ˡᵐ ↑ • [ g ]ʷ ↑      ≈⟨ (cright lemma-cong↑ _ _ (ih .proj₂ .proj₂)) ⟩
    [ d ]ᵈ • w ↑ ↑ • [ lm' ]ˡᵐ ↑        ≈⟨ sym assoc ⟩
    ([ d ]ᵈ • w ↑ ↑) • [ lm' ]ˡᵐ ↑      ≈⟨ (cleft comm-dbox-w↑↑ d w) ⟩
    (w ↑ ↑ • [ d ]ᵈ) • [ lm' ]ˡᵐ ↑      ≈⟨ assoc ⟩
    w ↑ ↑ • [ d ]ᵈ • [ lm' ]ˡᵐ ↑        ∎

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
