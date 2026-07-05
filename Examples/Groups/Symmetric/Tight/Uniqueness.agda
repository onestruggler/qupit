------------------------------------------------------------------------
-- Presentations of groups
--
-- Unique normal form for the tight (Permutation′) semantics of Sₙ,
-- derived from the loose uniqueness via a pointwise agreement lemma.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}

open import Data.Nat using (ℕ ; zero ; suc)
open import Data.Fin using (Fin ; zero ; suc)
import Data.Fin as F
open import Data.Fin.Permutation
  using ( Permutation′ ; _⟨$⟩ʳ_ ; _∘ₚ_ )
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_ ; refl)
import Presentation.Properties as PP
open import Algebra.Bundles using (Group)
import Presentation.Normalization hiding (NormalForm)
import Examples.Groups.Symmetric.Tight.Semantics as TightSem
open TightSem using (Permutation′-group)

open import Word.Base
open import Notations

module Examples.Groups.Symmetric.Tight.Uniqueness where

open import Examples.Groups.Symmetric.Syntactics
open import Examples.Groups.Symmetric.NormalForm
open import Examples.Groups.Symmetric.Normalization using (nf-of)
open import Examples.Groups.Symmetric.Loose.Semantics
open import Examples.Groups.Symmetric.Loose.Uniqueness using (unique-nf)

private variable n : ℕ

------------------------------------------------------------------------
-- Agreement between tight and loose denotations

private

  ⟦⟧ᵍ-agree : ∀ {n} (g : Gen n) (k : Fin n)
             → TightSem.⟦ g ⟧ᵍ ⟨$⟩ʳ k ≡ ⟦ g ⟧ᵍ k
  ⟦⟧ᵍ-agree (gate₁ ()) _
  ⟦⟧ᵍ-agree (gate₂ σ-gate) zero      = refl
  ⟦⟧ᵍ-agree (gate₂ σ-gate) (₁₊ zero) = refl
  ⟦⟧ᵍ-agree (gate₂ σ-gate) (₂₊ _)    = refl
  ⟦⟧ᵍ-agree (g ↥) zero    = refl
  ⟦⟧ᵍ-agree (g ↥) (suc j) = Eq.cong F.suc (⟦⟧ᵍ-agree g j)

  ⟦⟧-agree : ∀ {n} (w : Circuit n) (k : Fin n)
            → TightSem.⟦ w ⟧ ⟨$⟩ʳ k ≡ ⟦ w ⟧ k
  ⟦⟧-agree ε       _ = refl
  ⟦⟧-agree [ g ]ʷ  k = ⟦⟧ᵍ-agree g k
  ⟦⟧-agree (w • v) k = Eq.trans (Eq.cong (TightSem.⟦ v ⟧ ⟨$⟩ʳ_) (⟦⟧-agree w k))
                                 (⟦⟧-agree v _)

------------------------------------------------------------------------
-- Unique normal form for the tight semantics

unique-nf-tight : let open PP (n VRel,_===_) in
  Presentation.Normalization.UniqueNormalForm
    word-setoid (NF n) (nf-of {n}) (inv-nf {n})
    (Group.setoid (Permutation′-group n)) (TightSem.⟦_⟧ {n})
unique-nf-tight {n = n} = record
  { nf     = Presentation.Normalization.UniqueNormalForm.nf (unique-nf n)
  ; unique = λ {u} {v} eq →
      Presentation.Normalization.UniqueNormalForm.unique (unique-nf n)
        (λ k → Eq.trans (Eq.sym (⟦⟧-agree (inv-nf {n} u) k))
               (Eq.trans (eq k) (⟦⟧-agree (inv-nf {n} v) k)))
  }
