------------------------------------------------------------------------
-- Presentations of groups
--
-- Monoid and group homomorphism / monomorphism / isomorphism builders
-- for the extension functor (f *)
------------------------------------------------------------------------

{-# OPTIONS --safe #-}

open import Data.Product using (proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_)
import Relation.Binary.PropositionalEquality as Eq
import Relation.Binary.Reasoning.Setoid as SR

open import Algebra.Morphism.Structures
  using (module MonoidMorphisms ; module GroupMorphisms)
open import Function.Definitions using (Surjective)
open import Algebra.Bundles using (Monoid ; Group)
open import Algebra.Bundles.Raw using (RawGroup)

open import Word.Base
open import Word.Properties
import Presentation.Base as PB
import Presentation.Properties as PP
open import Presentation.Reidemeister-Schreier hiding (module Star-Congruence)

module Presentation.Morphism {A B : Set} (Γ : WRel A) (Δ : WRel B) where

open PB Γ renaming
  (_===_ to _===₁_ ; _≈_ to _≈₁_ ; refl to refl₁ ; cong to cong₁ ; sym to sym₁)
open PP Γ renaming (•-ε-monoid to m₁)
open PB Δ renaming
  (_===_ to _===₂_ ; _≈_ to _≈₂_ ; refl to refl₂ ; cong to cong₂ ; sym to sym₂)
open PP Δ renaming (•-ε-monoid to m₂ ; word-setoid to ws₂)
open PB

------------------------------------------------------------------------
-- Congruence: (f *) and wmap f preserve _≈_

module Star-Congruence
  (f : A → Word B)
  (f-well-defined : ∀ {w v} → w ===₁ v → (f *) w ≈₂ (f *) v)
  where

  lemma-f*-cong : ∀ {w v : Word A} → w ≈₁ v → (f *) w ≈₂ (f *) v
  lemma-f*-cong _≈₁_.refl        = _≈₂_.refl
  lemma-f*-cong (sym h)           = _≈₂_.sym (lemma-f*-cong h)
  lemma-f*-cong (trans h h₁)     = _≈₂_.trans (lemma-f*-cong h) (lemma-f*-cong h₁)
  lemma-f*-cong (cong h h₁)      = _≈₂_.cong (lemma-f*-cong h) (lemma-f*-cong h₁)
  lemma-f*-cong assoc             = _≈₂_.assoc
  lemma-f*-cong left-unit         = _≈₂_.left-unit
  lemma-f*-cong right-unit        = _≈₂_.right-unit
  lemma-f*-cong (axiom a)         = f-well-defined a

module Congruence
  (f : A → B)
  (f-well-defined : let f* = wmap f in ∀ {w v} → w ===₁ v → (f*) w ≈₂ (f*) v)
  where

  f* = wmap f

  lemma-f*-cong : ∀ {w v : Word A} → w ≈₁ v → (f*) w ≈₂ (f*) v
  lemma-f*-cong _≈₁_.refl        = _≈₂_.refl
  lemma-f*-cong (sym h)           = _≈₂_.sym (lemma-f*-cong h)
  lemma-f*-cong (trans h h₁)     = _≈₂_.trans (lemma-f*-cong h) (lemma-f*-cong h₁)
  lemma-f*-cong (cong h h₁)      = _≈₂_.cong (lemma-f*-cong h) (lemma-f*-cong h₁)
  lemma-f*-cong assoc             = _≈₂_.assoc
  lemma-f*-cong left-unit         = _≈₂_.left-unit
  lemma-f*-cong right-unit        = _≈₂_.right-unit
  lemma-f*-cong (axiom a)         = f-well-defined a

------------------------------------------------------------------------
-- Monoid morphisms

open MonoidMorphisms (Monoid.rawMonoid m₁) (Monoid.rawMonoid m₂)

-- Epimorphisms are not in the standard library.
record IsMonoidEpimorphism (f : Word A → Word B) : Set where
  field
    isMonoidHomomorphism : IsMonoidHomomorphism f
    surjective           : Surjective _≈₁_ _≈₂_ f

  open IsMonoidHomomorphism isMonoidHomomorphism public

-- Build a monoid homomorphism from (f *).
module StarHomomorphism
  (f : A → Word B)
  (f-well-defined : ∀ {w v} → w ===₁ v → (f *) w ≈₂ (f *) v)
  where

  isMonoidHomomorphism : IsMonoidHomomorphism (f *)
  isMonoidHomomorphism = record
    { isMagmaHomomorphism = record
      { isRelHomomorphism = record { cong = lemma-f*-cong f f-well-defined }
      ; homo = λ x y → _≈₂_.refl
      }
    ; ε-homo = _≈₂_.refl
    }
    where open Star-Congruence

-- Build a monoid homomorphism from wmap f.
module GenHomomorphism
  (f : A → B)
  (f-well-defined : let f* = wmap f in ∀ {w v} → w ===₁ v → (f*) w ≈₂ (f*) v)
  where

  f* = wmap f

  isMonoidHomomorphism : IsMonoidHomomorphism (f*)
  isMonoidHomomorphism = record
    { isMagmaHomomorphism = record
      { isRelHomomorphism = record { cong = lemma-f*-cong f f-well-defined }
      ; homo = λ x y → _≈₂_.refl
      }
    ; ε-homo = _≈₂_.refl
    }
    where open Congruence

-- Build a monoid monomorphism from (f *), using Reidemeister-Schreier.
module StarMonomorphism
  (f : A → Word B)
  (g : B → Word A)
  (f-well-defined : ∀ {w v} → w ===₁ v → (f *) w ≈₂ (f *) v)
  (g-well-defined : ∀ {u t : Word B} → u ===₂ t → (g *) u ≈₁ (g *) t)
  (g-left-inv-gen : ∀ (x : A) → [ x ]ʷ ≈₁ (g *) (f x))
  where

  open StarHomomorphism f f-well-defined
  open Star-Injective-Simplified Γ Δ
  open Reidemeister-Schreier-Simplified f g g-well-defined g-left-inv-gen

  isMonoidMonomorphism : IsMonoidMonomorphism (f *)
  isMonoidMonomorphism = record
    { isMonoidHomomorphism = isMonoidHomomorphism
    ; injective = f*-inj
    }

-- Build a monoid isomorphism from (f *).
module StarIsomorphism
  (f : A → Word B)
  (g : B → Word A)
  (f-well-defined  : ∀ {w v} → w ===₁ v → (f *) w ≈₂ (f *) v)
  (f-left-inv-gen  : ∀ (x : B) → [ x ]ʷ ≈₂ (f *) (g x))
  (g-well-defined  : ∀ {u t : Word B} → u ===₂ t → (g *) u ≈₁ (g *) t)
  (g-left-inv-gen  : ∀ (x : A) → [ x ]ʷ ≈₁ (g *) (f x))
  where

  open StarMonomorphism f g f-well-defined g-well-defined g-left-inv-gen
  open Star-Injective-Simplified Δ Γ
  open Reidemeister-Schreier-Simplified g f f-well-defined f-left-inv-gen
    renaming (g*-surj to f*-surj)

  isMonoidIsomorphism : IsMonoidIsomorphism (f *)
  isMonoidIsomorphism = record
    { isMonoidMonomorphism = isMonoidMonomorphism
    ; surjective = f*-surj
    }

-- Transfer a normal-form witness along a generator bijection.
module HomomorphismANF
  (f : A → B)
  (g : B → A)
  (fg=id : ∀ x → f (g x) ≡ x)
  (f-well-defined : let f* = wmap f in ∀ {w v} → w ===₁ v → (f*) w ≈₂ (f*) v)
  where

  open import Function using (_∘_)
  open Congruence f f-well-defined

  homo-anf : PP.NFProperty Γ → PP.AlmostNFProperty Δ
  homo-anf gp = record { ANF = NF ; anf = anf ; anf-injective = inj }
    where
    open PP.NFProperty gp
    anf = nf ∘ wmap g
    import Relation.Binary.Reasoning.Setoid as SR
    open SR ws₂
    g* = wmap g

    lemma-f*g* : ∀ w → f* (g* w) ≡ w
    lemma-f*g* [ x ]ʷ    rewrite fg=id x = Eq.refl
    lemma-f*g* ε           = Eq.refl
    lemma-f*g* (w • w₁)   rewrite lemma-f*g* w | lemma-f*g* w₁ = Eq.refl

    inj : {w v : Word B} → nf (wmap g w) ≡ nf (wmap g v) → w ≈₂ v
    inj {w} {v} eq =
      begin w          ≡⟨ Eq.sym (lemma-f*g* w) ⟩
        f* (g* w)      ≈⟨ lemma-f*-cong (nf-injective eq) ⟩
        f* (g* v)      ≡⟨ lemma-f*g* v ⟩
        v ∎

open import Presentation.GroupLike

------------------------------------------------------------------------
-- Group morphisms

module GroupMorphs
  (group-like₁ : Grouplike _===₁_)
  (group-like₂ : Grouplike _===₂_)
  where

  open Group-Lemmas A _===₁_ group-like₁
    renaming (•-ε-group to •-ε-group₁)
  open Group-Lemmas B _===₂_ group-like₂
    renaming ( •-ε-group              to •-ε-group₂
             ; lemma-left-inverse-unique to lemma-left-inverse-unique₂
             ; lemma-cong-inv          to lemma-cong-inv₂
             )

  open GroupMorphisms (Group.rawGroup •-ε-group₁) (Group.rawGroup •-ε-group₂)

  module StarGroupHomomorphism
    (f : A → Word B)
    (f-well-defined : ∀ {w v} → w ===₁ v → (f *) w ≈₂ (f *) v)
    where

    open Star-Congruence f f-well-defined
    open StarHomomorphism f f-well-defined
    open RawGroup (Group.rawGroup •-ε-group₁) renaming (_⁻¹ to _⁻¹₁)
    open RawGroup (Group.rawGroup •-ε-group₂) renaming (_⁻¹ to _⁻¹₂)

    inv-homo : ∀ x → (f *) (x ⁻¹₁) ≈₂ ((f *) x) ⁻¹₂
    inv-homo [ x ]ʷ =
      begin (f *) ([ x ]ʷ ⁻¹₁)
          ≈⟨ lemma-left-inverse-unique₂ {g = (f *) [ x ]ʷ} {h = (f *) ([ x ]ʷ ⁻¹₁)}
               (lemma-f*-cong (group-like₁ x .proj₂)) ⟩
        (f *) [ x ]ʷ ⁻¹₂ ∎
      where open SR ws₂
    inv-homo ε = refl₂
    inv-homo (x • y) =
      begin (f *) ((x • y) ⁻¹₁)           ≈⟨ lemma-f*-cong {(x • y) ⁻¹₁} {y ⁻¹₁ • x ⁻¹₁} refl₁ ⟩
        (f *) (y ⁻¹₁ • x ⁻¹₁)             ≈⟨ refl₂ ⟩
        (f *) (y ⁻¹₁) • (f *) (x ⁻¹₁)    ≈⟨ cong₂ (inv-homo y) (inv-homo x) ⟩
        ((f *) y) ⁻¹₂ • ((f *) x) ⁻¹₂    ≈⟨ refl₂ ⟩
        (f *) (x • y) ⁻¹₂ ∎
      where open SR ws₂

    isGroupHomomorphism : IsGroupHomomorphism (f *)
    isGroupHomomorphism = record
      { isMonoidHomomorphism = isMonoidHomomorphism
      ; ⁻¹-homo = inv-homo
      }

  module GenGroupHomomorphism
    (f : A → B)
    (f-well-defined : let f* = wmap f in ∀ {w v} → w ===₁ v → (f*) w ≈₂ (f*) v)
    where

    open Congruence f f-well-defined
    open GenHomomorphism f f-well-defined hiding (f*)
    open RawGroup (Group.rawGroup •-ε-group₁) renaming (_⁻¹ to _⁻¹₁)
    open RawGroup (Group.rawGroup •-ε-group₂) renaming (_⁻¹ to _⁻¹₂)

    inv-homo : ∀ x → (f*) (x ⁻¹₁) ≈₂ ((f*) x) ⁻¹₂
    inv-homo [ x ]ʷ =
      begin (f*) ([ x ]ʷ ⁻¹₁)
          ≈⟨ lemma-left-inverse-unique₂ {g = (f*) [ x ]ʷ} {h = (f*) ([ x ]ʷ ⁻¹₁)}
               (lemma-f*-cong (group-like₁ x .proj₂)) ⟩
        (f*) [ x ]ʷ ⁻¹₂ ∎
      where open SR ws₂
    inv-homo ε = refl₂
    inv-homo (x • y) =
      begin (f*) ((x • y) ⁻¹₁)           ≈⟨ lemma-f*-cong {(x • y) ⁻¹₁} {y ⁻¹₁ • x ⁻¹₁} refl₁ ⟩
        (f*) (y ⁻¹₁ • x ⁻¹₁)             ≈⟨ refl₂ ⟩
        (f*) (y ⁻¹₁) • (f*) (x ⁻¹₁)     ≈⟨ cong₂ (inv-homo y) (inv-homo x) ⟩
        ((f*) y) ⁻¹₂ • ((f*) x) ⁻¹₂     ≈⟨ refl₂ ⟩
        (f*) (x • y) ⁻¹₂ ∎
      where open SR ws₂

    isGroupHomomorphism : IsGroupHomomorphism (f*)
    isGroupHomomorphism = record
      { isMonoidHomomorphism = isMonoidHomomorphism
      ; ⁻¹-homo = inv-homo
      }

  module StarGroupMonomorphism
    (f : A → Word B)
    (g : B → Word A)
    (f-well-defined : ∀ {w v} → w ===₁ v → (f *) w ≈₂ (f *) v)
    (g-well-defined : ∀ {u t : Word B} → u ===₂ t → (g *) u ≈₁ (g *) t)
    (g-left-inv-gen : ∀ (x : A) → [ x ]ʷ ≈₁ (g *) (f x))
    where

    open StarGroupHomomorphism f f-well-defined
    open Star-Injective-Simplified Γ Δ
    open Reidemeister-Schreier-Simplified f g g-well-defined g-left-inv-gen

    isGroupMonomorphism : IsGroupMonomorphism (f *)
    isGroupMonomorphism = record
      { isGroupHomomorphism = isGroupHomomorphism
      ; injective = f*-inj
      }

  module StarGroupIsomorphism
    (f : A → Word B)
    (g : B → Word A)
    (f-well-defined  : ∀ {w v} → w ===₁ v → (f *) w ≈₂ (f *) v)
    (f-left-inv-gen  : ∀ (x : B) → [ x ]ʷ ≈₂ (f *) (g x))
    (g-well-defined  : ∀ {u t : Word B} → u ===₂ t → (g *) u ≈₁ (g *) t)
    (g-left-inv-gen  : ∀ (x : A) → [ x ]ʷ ≈₁ (g *) (f x))
    where

    open StarGroupMonomorphism f g f-well-defined g-well-defined g-left-inv-gen
    open Star-Injective-Simplified Δ Γ
    open Reidemeister-Schreier-Simplified g f f-well-defined f-left-inv-gen
      renaming (g*-surj to f*-surj)

    isGroupIsomorphism : IsGroupIsomorphism (f *)
    isGroupIsomorphism = record
      { isGroupMonomorphism = isGroupMonomorphism
      ; surjective = f*-surj
      }
