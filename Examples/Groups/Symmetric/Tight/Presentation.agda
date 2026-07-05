------------------------------------------------------------------------
-- Presentations of groups
--
-- Group homomorphism from the free-group presentation (Word (Gen n) / ≈)
-- to the permutation group Permutation′ n, via the tight semantics.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}

module Examples.Groups.Symmetric.Tight.Presentation where

open import Data.Nat using (ℕ)
open import Data.Fin.Permutation using (_⟨$⟩ˡ_ ; _⟨$⟩ʳ_ ; inverseˡ)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (sym ; trans ; cong)

open import Algebra.Bundles using (Group)
open import Algebra.Morphism.Bundles using (GroupHomomorphism)
open import Algebra.Morphism.Structures using (module GroupMorphisms)

open import Presentation.GroupLike

open import Examples.Groups.Symmetric.Syntactics
import Examples.Groups.Symmetric.Tight.Semantics as ST
import Examples.Groups.Symmetric.Tight.Soundness as STS
open ST using (Permutation′-group)
open import Notations
open import Word.Base


module _ (n : ℕ) where

  private
    module GL = Group-Lemmas (Gen n) (_VRel,_===_ n) (grouplike {n})

  open GroupMorphisms (Group.rawGroup GL.•-ε-group) (Group.rawGroup (Permutation′-group n))

  ⟦⟧-isGroupHom : IsGroupHomomorphism (ST.⟦_⟧ {n})
  ⟦⟧-isGroupHom = record
    { isMonoidHomomorphism = record
      { isMagmaHomomorphism = record
        { isRelHomomorphism = record { cong = STS.sound }
        ; homo = λ _ _ _ → Eq.refl
        }
      ; ε-homo = λ _ → Eq.refl
      }
    ; ⁻¹-homo = λ w k →
        trans (sym (inverseˡ (ST.⟦ w ⟧)))
              (cong (ST.⟦ w ⟧ ⟨$⟩ˡ_) (STS.sound (GL.lemma-left-inverse {g = w}) k))
    }

  ⟦⟧-groupHom : GroupHomomorphism (Group.rawGroup GL.•-ε-group) (Group.rawGroup (Permutation′-group n))
  ⟦⟧-groupHom = record
    { ⟦_⟧ = ST.⟦_⟧
    ; isGroupHomomorphism = ⟦⟧-isGroupHom
    }

  import Presentation.Properties as PP
  open import Presentation.Definitions

  open import Examples.Groups.Symmetric.Tight.Semantics
  open import Examples.Groups.Symmetric.Tight.Soundness
  import Examples.Groups.Symmetric.Loose.Semantics as LooseSem
  open import Data.Fin.Permutation
    using ( Permutation′ ; _⟨$⟩ʳ_ ; _⟨$⟩ˡ_ ; _∘ₚ_ ; flip
          ; inverseˡ ; inverseʳ ; lift₀ ; lift₀-cong ; remove ; lift₀-remove)
  open import Data.Product using (∃ ; _,_ ; proj₁ ; proj₂)
  import Data.Fin as F

  open import Data.Nat using (ℕ ; zero ; suc)
  open import Data.Fin using (Fin ; zero ; suc)
  open import Examples.Groups.Symmetric.NormalForm
  import Examples.Groups.Symmetric.Tight.Completeness as TC

  import Relation.Binary.PropositionalEquality as Eq
  open Eq using (_≡_ ; refl)

  presentation : let open PP (n VRel,_===_) in
    (n VRel,_===_) IsPresentationOf (Permutation′-group n)
  presentation  = record
    { gl  = grouplike
    ; ⟦_⟧ = ⟦_⟧
    ; iso = record
        { isGroupMonomorphism = record
            { isGroupHomomorphism = ⟦⟧-isGroupHom
            ; injective           = TC.completeness
            }
        ; surjective = λ π →
            let w , ih = go n π
            in w , λ {z} z≈w k → Eq.trans (sound z≈w k) (ih k)
        }
    }
    where

    fin-to-C : ∀ {m} → Fin (₁₊ m) → C m
    fin-to-C           F.zero    = ε
    fin-to-C {₁₊ m} (F.suc j) = σ• (fin-to-C j)

    depth : ∀ {m} → C m → Fin (₁₊ m)
    depth ε      = F.zero
    depth (σ• c) = F.suc (depth c)

    depth-fin-to-C : ∀ {m} (j : Fin (₁₊ m)) → depth (fin-to-C j) ≡ j
    depth-fin-to-C           F.zero    = refl
    depth-fin-to-C {₁₊ m} (F.suc j) = Eq.cong F.suc (depth-fin-to-C j)

    ⟦[r]ᶜ⟧-zero : ∀ {m} (r : C m) → ⟦ [ r ]ᶜ ⟧ ⟨$⟩ʳ F.zero ≡ depth r
    ⟦[r]ᶜ⟧-zero ε      = refl
    ⟦[r]ᶜ⟧-zero (σ• c) =
      Eq.trans (⟦↑⟧ ([ c ]ᶜ) (F.suc F.zero))
               (Eq.cong F.suc (⟦[r]ᶜ⟧-zero c))

    go : ∀ m (π : Permutation′ m) → ∃ λ w → ∀ k → ⟦ w ⟧ ⟨$⟩ʳ k ≡ π ⟨$⟩ʳ k
    go 0       π = ε , λ ()
    go (suc m) π = w' ↑ • [ r ]ᶜ , correct
      where
      j      = π ⟨$⟩ʳ F.zero
      r      = fin-to-C j
      ρ_r    = ⟦ [ r ]ᶜ ⟧
      χ      = π ∘ₚ flip ρ_r
      ρ_r-eq : ρ_r ⟨$⟩ʳ F.zero ≡ j
      ρ_r-eq = Eq.trans (⟦[r]ᶜ⟧-zero r) (depth-fin-to-C j)
      χ₀     : χ ⟨$⟩ʳ F.zero ≡ F.zero
      χ₀     = Eq.subst (λ x → ρ_r ⟨$⟩ˡ x ≡ F.zero) ρ_r-eq (inverseˡ ρ_r)
      ρ'     = remove F.zero χ
      rec    = go m ρ'
      w'     = rec .proj₁
      ih     = rec .proj₂
      correct : ∀ k → ⟦ (w' ↑) • [ r ]ᶜ ⟧ ⟨$⟩ʳ k ≡ π ⟨$⟩ʳ k
      correct k =
        Eq.trans
          (Eq.cong (ρ_r ⟨$⟩ʳ_)
            (Eq.trans (⟦↑⟧ w' k)
            (Eq.trans (lift₀-cong ⟦ w' ⟧ ρ' ih k)
                      (lift₀-remove χ χ₀ k))))
          (inverseʳ ρ_r)
