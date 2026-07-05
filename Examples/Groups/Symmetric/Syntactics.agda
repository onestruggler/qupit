------------------------------------------------------------------------
-- Presentations of groups
--
-- Symmetric groups Sₙ: gate type, circuit generators, and the
-- group-specific relations (order and yang-baxter).
-- Syntactic framework only; no coset enumeration or normal form.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}

open import Data.Nat using (ℕ)
open import Data.Product using (_,_)
import Relation.Binary.Reasoning.Setoid as SR

open import Word.Base
open import Notations
open import Presentation.GroupLike
import Presentation.Vertical-Syntactics
import Presentation.Horizontal-Syntactics as PB
import Presentation.Properties as PP

module Examples.Groups.Symmetric.Syntactics where

private variable
  n :  ℕ
  
------------------------------------------------------------------------
-- Gate type

data Gate : ℕ → Set where
  σ-gate : Gate 2

------------------------------------------------------------------------
-- Syntactics framework

private module SC = Presentation.Vertical-Syntactics Gate
open SC using (Gen ; gate₁ ; gate₂ ; _↥ ; _↑ ; _↓ ; _↥ᵏ_ ; _↑ᵏ_; Circuit) public

pattern σ-gen = gate₂ σ-gate

σ : Word (Gen (₂₊ n))
σ = [ σ-gen ]ʷ

------------------------------------------------------------------------
-- Group-specific relation: order and braid only; no structural rules

infix 4 _SRel,_===_
data _SRel,_===_ : (n : ℕ) → WRel (Gen n) where
  order       : (₂₊ n) SRel, σ • σ === ε
  yang-baxter : (₃₊ n) SRel, σ • σ ↑ • σ === σ ↑ • σ • σ ↑

------------------------------------------------------------------------
-- Full relation via Lift-Relation (adds structure rules cong↑, comm₁,
-- comm₂)

private module LR = SC.Lift-Relation _SRel,_===_
open LR public using (srel ; cong↑ ; comm₁ ; comm₂ ; lemma-cong↑ ; _VRel,_===_)

------------------------------------------------------------------------
-- Grouplike (each generator has a two-sided inverse)

grouplike : Grouplike (_VRel,_===_ n)
grouplike {₂₊ k} (gate₂ σ-gate) = σ , PB.axiom (srel order)
grouplike {₁₊ n} (g ↥) with grouplike {n} g
... | ig , prf = ig ↑ , lemma-cong↑ (ig • [ g ]ʷ) ε prf

------------------------------------------------------------------------
-- lemma-comm : w ↑ ↑ • [σ]ʷ ≈ [σ]ʷ • w ↑ ↑   (at _VRel,_===_ (₂₊ n))

lemma-comm : let open PB ( (₂₊ n) VRel,_===_ ) in

  ∀ (w : Circuit n) → w ↑ ↑ • σ ≈ σ • w ↑ ↑
  
lemma-comm {n} ε = PB._≈_.trans PB._≈_.left-unit (PB._≈_.sym PB._≈_.right-unit)
  where P = _VRel,_===_ (₂₊ n) ; open PB P
lemma-comm {n} [ g ]ʷ = PB._≈_.axiom (comm₂ σ-gate g)
  where P = _VRel,_===_ (₂₊ n) ; open PB P
lemma-comm {n} (w • v) = begin
  (w • v) ↑ ↑ • σ ≡⟨ auto ⟩
  (w ↑ ↑ • v ↑ ↑) • σ ≈⟨ _≈_.assoc ⟩
  w ↑ ↑ • v ↑ ↑ • σ ≈⟨ cong refl (lemma-comm v) ⟩
  w ↑ ↑ • σ • v ↑ ↑ ≈⟨ _≈_.sym _≈_.assoc ⟩
  (w ↑ ↑ • σ) • v ↑ ↑ ≈⟨ cong (lemma-comm w) refl ⟩
  (σ • w ↑ ↑) • v ↑ ↑ ≈⟨ _≈_.assoc ⟩
  σ • (w • v) ↑ ↑ ∎
  where
  P = _VRel,_===_ (₂₊ n)
  open PB P
  open PP P
  open SR word-setoid
