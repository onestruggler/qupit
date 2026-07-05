------------------------------------------------------------------------
-- Presentations of groups
--
-- The notion of "Γ presents G" and other related notions. Sometimes,
-- there are diffculties in formalizing the semantic side, so we use
-- different levels of presentation (completeness) defintions.
--
-- 1) Standard presentation (_IsPresentationOf_):
--    _====_ is a presentation of G iff G is isomorphic (as a group) to the
--    free group on generators X quotiented by the congruence closure
--    of _===_.
--
-- 2) Monoid presentation, a monoid version.
--
-- 3) Everything rewrites to its unique normal form.

------------------------------------------------------------------------

{-# OPTIONS --safe #-}

module Presentation.Definitions where

open import Data.Nat using (ℕ)
open import Level using (Level ; _⊔_)

open import Relation.Binary using (Setoid)
open import Algebra.Bundles using (Group ; Monoid)
open import Algebra.Morphism.Bundles using (GroupHomomorphism)
open import Algebra.Morphism.Structures using (module GroupMorphisms ; module MonoidMorphisms)

open import Word.Base

open import Presentation.GroupLike
import Presentation.Base as HS
import Presentation.Properties as PP
import Presentation.Vertical-Syntactics as VS

private variable
  a b ℓ ℓ' : Level
  X : Set


------------------------------------------------------------------------
-- _===_ : WRel X is a presentation of G iff there is a group
-- isomorphism ⟦_⟧ : Word X / _≈_ ≅ G, where _≈_ is the congruence
-- closure of _===_.  The source group GL.•-ε-group is (Word X, _•_,
-- ε, _⁻¹) modulo _≈_, constructed in Presentation.GroupLike from a
-- grouplike structure gl on _===_ (which gives every generator a left
-- inverse in ≈_Γ).

infix 4 _IsPresentationOf_
record _IsPresentationOf_ (_===_ : WRel X) (G : Group a ℓ) : Set (a ⊔ ℓ) where
  field
    gl : Grouplike _===_
  module GL = Group-Lemmas X _===_ gl
  open GroupMorphisms (Group.rawGroup GL.•-ε-group) (Group.rawGroup G)
  field
    ⟦_⟧ : Word X → Group.Carrier G
    iso  : IsGroupIsomorphism ⟦_⟧

infix 4 _IsMonoidPresentationOf_
record _IsMonoidPresentationOf_ (_===_ : WRel X) (M : Monoid a ℓ) : Set (a ⊔ ℓ) where
  open MonoidMorphisms (Monoid.rawMonoid (PP.•-ε-monoid _===_)) (Monoid.rawMonoid M)
  field
    ⟦_⟧ : Word X → Monoid.Carrier M
    iso  : IsMonoidIsomorphism ⟦_⟧

module Relative {a b ℓ₁ ℓ₂}
  (Syn : Setoid a ℓ₁)
  (Sem : Setoid b ℓ₂)
  where

  open Setoid Syn using () renaming (Carrier to A; _≈_ to _≈₁_)
  open Setoid Sem using () renaming (Carrier to B; _≈_ to _≈₂_)

  Soundness : (⟦_⟧ : A → B) → Set (a ⊔ ℓ₁ ⊔ ℓ₂)
  Soundness ⟦_⟧ = ∀ {x y : A} → x ≈₁ y → ⟦ x ⟧ ≈₂ ⟦ y ⟧

  Completeness : (⟦_⟧ : A → B) → Set (a ⊔ ℓ₁ ⊔ ℓ₂)
  Completeness ⟦_⟧ = ∀ {x y : A} → ⟦ x ⟧ ≈₂ ⟦ y ⟧ → x ≈₁ y
