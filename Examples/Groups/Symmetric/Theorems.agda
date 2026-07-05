------------------------------------------------------------------------
-- Presentations of groups
--
-- This file collects main theorems for convenience.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}

open import Level
open import Data.Nat using (ℕ ; zero ; suc)
open import Data.Fin using (Fin ; zero ; suc)
open import Data.Vec.Functional.Relation.Binary.Permutation
open import Data.Vec.Functional.Relation.Binary.Permutation.Properties
open import Algebra.Bundles using (Group)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_ ; refl)
open import Function using (_∘_ ; id)

open import Word.Base
import Presentation.Horizontal-Syntactics as PB
import Presentation.Properties as PP
open import Presentation.Definitions
open import Presentation.Normalization hiding (NF)
open import Notations

module Examples.Groups.Symmetric.Theorems where

open import Examples.Groups.Symmetric.Syntactics

open import Examples.Groups.Symmetric.Normalization as SN hiding (unique-nf)

open Relative

private variable
  n : ℕ

-- ----------------------------------------------------------------------
-- * Unique normal form, soundness, completeness and presentation

module Semantics-Loose where

  open import Examples.Groups.Symmetric.Semantics

  unique-nf : let open PP (n VRel,_===_) in
    UniqueNF word-setoid (NF n) (nf-of {n}) (inv-f n) (Perm-setoid n) (⟦_⟧ {n})
  unique-nf {n = n} = SN.unique-nf n

  soundness : let open PP (n VRel,_===_) in
    Soundness word-setoid (Perm-setoid n) ⟦_⟧
  soundness = sound

  completeness : let open PP (n VRel,_===_) in
    Completeness word-setoid (Perm-setoid n) ⟦_⟧
  completeness {n} = by-normalization unique-nf soundness
    where
    open PP (n VRel,_===_)
    open Completeness word-setoid (NF n) (nf-of {n}) (inv-f n) {0ℓ} {0ℓ} (Perm-setoid n) (⟦_⟧ {n})


module Semantics-Tight where

  open import Examples.Groups.Symmetric.Semantics-Tight
  open import Examples.Groups.Symmetric.Permutation-Properties
  import Examples.Groups.Symmetric.Semantics as LooseSem
  open import Data.Fin.Permutation
    using ( Permutation′ ; _⟨$⟩ʳ_ ; _⟨$⟩ˡ_ ; _∘ₚ_ ; flip
          ; inverseˡ ; inverseʳ ; lift₀ ; lift₀-cong ; remove ; lift₀-remove)
  open import Data.Product using (∃ ; _,_ ; proj₁ ; proj₂)
  import Data.Fin as F
  import Examples.Groups.Symmetric.Presentation as P

  private

    ⟦⟧ᵍ-agree : ∀ {n} (g : Gen n) (k : Fin n)
               → ⟦ g ⟧ᵍ ⟨$⟩ʳ k ≡ LooseSem.⟦ g ⟧ᵍ k
    ⟦⟧ᵍ-agree (gate₁ ()) _
    ⟦⟧ᵍ-agree (gate₂ σ-gate) zero      = refl
    ⟦⟧ᵍ-agree (gate₂ σ-gate) (₁₊ zero) = refl
    ⟦⟧ᵍ-agree (gate₂ σ-gate) (₂₊ _)    = refl
    ⟦⟧ᵍ-agree (g ↥) zero    = refl
    ⟦⟧ᵍ-agree (g ↥) (suc j) = Eq.cong F.suc (⟦⟧ᵍ-agree g j)

    ⟦⟧-agree : ∀ {n} (w : Circuit n) (k : Fin n)
              → ⟦ w ⟧ ⟨$⟩ʳ k ≡ LooseSem.⟦ w ⟧ k
    ⟦⟧-agree ε       _ = refl
    ⟦⟧-agree [ g ]ʷ  k = ⟦⟧ᵍ-agree g k
    ⟦⟧-agree (w • v) k = Eq.trans (Eq.cong (⟦ v ⟧ ⟨$⟩ʳ_) (⟦⟧-agree w k))
                                   (⟦⟧-agree v _)

  unique-nf : let open PP (n VRel,_===_) in
    UniqueNF word-setoid (NF n) (nf-of {n}) (inv-f n) (Group.setoid (Permutation′-group n)) (⟦_⟧ {n})
  unique-nf {n = n} = record
    { nf     = UniqueNF.nf (SN.unique-nf n)
    ; unique = λ {u} {v} eq →
        UniqueNF.unique (SN.unique-nf n)
          (λ k → Eq.trans (Eq.sym (⟦⟧-agree (inv-f n u) k))
                 (Eq.trans (eq k) (⟦⟧-agree (inv-f n v) k)))
    }

  soundness : let open PP (n VRel,_===_) in
    Soundness word-setoid (Group.setoid (Permutation′-group n)) ⟦_⟧
  soundness = sound

  completeness : let open PP (n VRel,_===_) in
    Completeness word-setoid (Group.setoid (Permutation′-group n)) ⟦_⟧
  completeness {n} = by-normalization unique-nf soundness
    where
    open PP (n VRel,_===_)
    open Completeness word-setoid (NF n) (nf-of {n}) (inv-f n) {0ℓ} {0ℓ} (Group.setoid (Permutation′-group n)) (⟦_⟧ {n})


  presentation : let open PP (n VRel,_===_) in
    (n VRel,_===_) IsPresentationOf (Permutation′-group n)
  presentation {n = n} = record
    { gl  = grouplike
    ; ⟦_⟧ = ⟦_⟧
    ; iso = record
        { isGroupMonomorphism = record
            { isGroupHomomorphism = P.⟦⟧-isGroupHom n
            ; injective           = completeness
            }
        ; surjective = λ π →
            let w , ih = go n π
            in w , λ {z} z≈w k → Eq.trans (soundness z≈w k) (ih k)
        }
    }
    where

    fin-to-C : ∀ {m} → Fin (₁₊ m) → SN.C m
    fin-to-C           F.zero    = SN.ε
    fin-to-C {₁₊ m} (F.suc j) = SN.σ• (fin-to-C j)

    depth : ∀ {m} → SN.C m → Fin (₁₊ m)
    depth SN.ε      = F.zero
    depth (SN.σ• c) = F.suc (depth c)

    depth-fin-to-C : ∀ {m} (j : Fin (₁₊ m)) → depth (fin-to-C j) ≡ j
    depth-fin-to-C           F.zero    = refl
    depth-fin-to-C {₁₊ m} (F.suc j) = Eq.cong F.suc (depth-fin-to-C j)

    ⟦[r]ᶜ⟧-zero : ∀ {m} (r : SN.C m) → ⟦ SN.[ r ]ᶜ ⟧ ⟨$⟩ʳ F.zero ≡ depth r
    ⟦[r]ᶜ⟧-zero SN.ε      = refl
    ⟦[r]ᶜ⟧-zero (SN.σ• c) =
      Eq.trans (⟦↑⟧ (SN.[ c ]ᶜ) (F.suc F.zero))
               (Eq.cong F.suc (⟦[r]ᶜ⟧-zero c))

    go : ∀ m (π : Permutation′ m) → ∃ λ w → ∀ k → ⟦ w ⟧ ⟨$⟩ʳ k ≡ π ⟨$⟩ʳ k
    go 0       π = ε , λ ()
    go (suc m) π = w' ↑ • SN.[ r ]ᶜ , correct
      where
      j      = π ⟨$⟩ʳ F.zero
      r      = fin-to-C j
      ρ_r    = ⟦ SN.[ r ]ᶜ ⟧
      χ      = π ∘ₚ flip ρ_r
      ρ_r-eq : ρ_r ⟨$⟩ʳ F.zero ≡ j
      ρ_r-eq = Eq.trans (⟦[r]ᶜ⟧-zero r) (depth-fin-to-C j)
      χ₀     : χ ⟨$⟩ʳ F.zero ≡ F.zero
      χ₀     = Eq.subst (λ x → ρ_r ⟨$⟩ˡ x ≡ F.zero) ρ_r-eq (inverseˡ ρ_r)
      ρ'     = remove F.zero χ
      rec    = go m ρ'
      w'     = rec .proj₁
      ih     = rec .proj₂
      correct : ∀ k → ⟦ w' ↑ • SN.[ r ]ᶜ ⟧ ⟨$⟩ʳ k ≡ π ⟨$⟩ʳ k
      correct k =
        Eq.trans
          (Eq.cong (ρ_r ⟨$⟩ʳ_)
            (Eq.trans (⟦↑⟧ w' k)
            (Eq.trans (lift₀-cong ⟦ w' ⟧ ρ' ih k)
                      (lift₀-remove χ χ₀ k))))
          (inverseʳ ρ_r)

