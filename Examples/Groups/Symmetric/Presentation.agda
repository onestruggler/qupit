------------------------------------------------------------------------
-- Presentations of groups
--
-- Group homomorphism from the free-group presentation (Word (Gen n) / ≈)
-- to the permutation group Permutation′ n, via the tight semantics.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}

module Examples.Groups.Symmetric.Presentation where

open import Data.Nat using (ℕ)
open import Data.Fin.Permutation using (_⟨$⟩ˡ_ ; _⟨$⟩ʳ_ ; inverseˡ)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (sym ; trans ; cong)

open import Algebra.Bundles using (Group)
open import Algebra.Morphism.Bundles using (GroupHomomorphism)
open import Algebra.Morphism.Structures using (module GroupMorphisms)

open import Presentation.GroupLike

open import Examples.Groups.Symmetric.Syntactics
import Examples.Groups.Symmetric.Semantics-Tight as ST
open import Examples.Groups.Symmetric.Permutation-Properties

module _ (n : ℕ) where

  private
    module GL = Group-Lemmas (Gen n) (_VRel,_===_ n) (grouplike {n})

  open GroupMorphisms (Group.rawGroup GL.•-ε-group) (Group.rawGroup (Permutation′-group n))

  ⟦⟧-isGroupHom : IsGroupHomomorphism (ST.⟦_⟧ {n})
  ⟦⟧-isGroupHom = record
    { isMonoidHomomorphism = record
      { isMagmaHomomorphism = record
        { isRelHomomorphism = record { cong = ST.sound }
        ; homo = λ _ _ _ → Eq.refl
        }
      ; ε-homo = λ _ → Eq.refl
      }
    ; ⁻¹-homo = λ w k →
        trans (sym (inverseˡ (ST.⟦ w ⟧)))
              (cong (ST.⟦ w ⟧ ⟨$⟩ˡ_) (ST.sound (GL.lemma-left-inverse {g = w}) k))
    }

  ⟦⟧-groupHom : GroupHomomorphism (Group.rawGroup GL.•-ε-group) (Group.rawGroup (Permutation′-group n))
  ⟦⟧-groupHom = record
    { ⟦_⟧ = ST.⟦_⟧
    ; isGroupHomomorphism = ⟦⟧-isGroupHom
    }
