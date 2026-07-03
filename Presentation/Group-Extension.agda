{-# OPTIONS --safe #-}

------------------------------------------------------------------------
-- Presentations of group extensions.
--
-- This module formalizes the relation-building part of the standard
-- recipe:
--
--   if N has presentation < Y | S > and G/N has presentation
--   < Xbar | Rbar >, choose lifts X of Xbar in G.  A presentation of
--   G is obtained on generators Y ∪ X by:
--
--     * the kernel relations S;
--     * one corrected lift of every quotient relation;
--     * conjugation relations saying that each lift of X normalizes N.
--
-- Since Word has no built-in formal inverses, quotient relators are
-- encoded in the binary-relation style already used by Presentation:
-- if a quotient relation says u = v, its lift is recorded as
--
--     lift(u) = correction(u=v) · lift(v).
--
-- This is the same information as lift(u) lift(v)^-1 ∈ N.
------------------------------------------------------------------------

open import Level using (0ℓ)
open import Relation.Binary using (REL)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)
open import Data.Product using (∃)
open import Data.Sum using (_⊎_ ; inj₁ ; inj₂)

open import Word.Base
import Presentation.Horizontal-Syntactics as PB
open import Presentation.Construct.Base using ([_]ₗ ; [_]ᵣ)

module Presentation.Group-Extension where

WREL : Set -> Set -> Set₁
WREL X Y = REL (Word X) (Word Y) 0ℓ

------------------------------------------------------------------------
-- Data for the extension recipe.
------------------------------------------------------------------------

record ExtensionData {Y X : Set}
                     (S : WRel Y)
                     (R : WRel X) : Set₁ where
  field
    -- For each quotient relation u = v, choose the kernel word w_r
    -- such that the lifted relation is u = w_r · v.
    quotient-correction : ∀ {u v : Word X} -> R u v -> Word Y

    -- For each lifted quotient generator x and kernel generator y,
    -- choose the kernel word w_xy describing conjugation by x.
    --
    -- The orientation below is x · y = w_xy · x, i.e. x y x^-1 = w_xy
    -- in ordinary group notation.
    conjugation-correction : X -> Y -> Word Y


------------------------------------------------------------------------
-- The extension relation on the disjoint union of generators.
------------------------------------------------------------------------

data ExtensionRel
  {Y X : Set}
  (S : WRel Y)
  (R : WRel X)
  (ext : ExtensionData S R)
  : WRel (Y ⊎ X) where

  -- The relations of the normal subgroup N.
  kernel :
    ∀ {u v : Word Y} ->
    S u v ->
    ExtensionRel S R ext [ u ]ₗ [ v ]ₗ

  -- Corrected lifts of quotient relations.  Notice that the raw
  -- quotient relation [ u ]ᵣ = [ v ]ᵣ is not imposed directly.
  quotient :
    ∀ {u v : Word X} ->
    (ρ : R u v) ->
    ExtensionRel S R ext
      [ u ]ᵣ
      ([ ExtensionData.quotient-correction ext ρ ]ₗ • [ v ]ᵣ)

  -- Normality/conjugation relations for moving a lifted quotient
  -- generator past a kernel generator.
  conjugation :
    ∀ (x : X) (y : Y) ->
    ExtensionRel S R ext
      ([ [ x ]ʷ ]ᵣ • [ [ y ]ʷ ]ₗ)
      ([ ExtensionData.conjugation-correction ext x y ]ₗ • [ [ x ]ʷ ]ᵣ)


------------------------------------------------------------------------
-- A direct, parameterized variant.
------------------------------------------------------------------------

data ExtensionRel'
  {Y X : Set}
  (S : WRel Y)
  (R : WRel X)
  (quotient-correction : ∀ {u v : Word X} -> R u v -> Word Y)
  (conjugation-correction : X -> Y -> Word Y)
  : WRel (Y ⊎ X) where

  kernel :
    ∀ {u v : Word Y} ->
    S u v ->
    ExtensionRel' S R quotient-correction conjugation-correction
      [ u ]ₗ
      [ v ]ₗ

  quotient :
    ∀ {u v : Word X} ->
    (ρ : R u v) ->
    ExtensionRel' S R quotient-correction conjugation-correction
      [ u ]ᵣ
      ([ quotient-correction ρ ]ₗ • [ v ]ᵣ)

  conjugation :
    ∀ (x : X) (y : Y) ->
    ExtensionRel' S R quotient-correction conjugation-correction
      ([ [ x ]ʷ ]ᵣ • [ [ y ]ʷ ]ₗ)
      ([ conjugation-correction x y ]ₗ • [ [ x ]ʷ ]ᵣ)


------------------------------------------------------------------------
-- The split case recovers the usual semidirect-product style relation:
-- quotient relators lift without correction.
------------------------------------------------------------------------

split-extension-data :
  ∀ {Y X : Set} {S : WRel Y} {R : WRel X} ->
  (conjugation-correction : X -> Y -> Word Y) ->
  ExtensionData S R
split-extension-data conjugation-correction = record
  { quotient-correction = λ _ -> ε
  ; conjugation-correction = conjugation-correction
  }

SplitExtensionRel :
  ∀ {Y X : Set} ->
  (S : WRel Y) ->
  (R : WRel X) ->
  (conjugation-correction : X -> Y -> Word Y) ->
  WRel (Y ⊎ X)
SplitExtensionRel S R conjugation-correction =
  ExtensionRel S R (split-extension-data conjugation-correction)


------------------------------------------------------------------------
-- Formal proof infrastructure.
--
-- The paper proof uses two evident maps:
--
--   1. include the normal subgroup presentation into the extension
--      presentation;
--   2. project the extension presentation to the quotient presentation
--      by killing kernel generators.
--
-- The lemmas below formalize that both maps respect the defining
-- relations.  This is the Agda version of the proof's first step:
-- the presented extension maps onto the intended quotient, and the
-- presented kernel maps into the subgroup generated by Y.
------------------------------------------------------------------------

module Proof
  {Y X : Set}
  (S : WRel Y)
  (R : WRel X)
  (ext : ExtensionData S R)
  where

  Γ : WRel (Y ⊎ X)
  Γ = ExtensionRel S R ext

  open PB S renaming (_≈_ to _≈S_)
    using ()
  open PB R renaming (_≈_ to _≈R_ ; refl to reflR ; sym to symR ;
                      trans to transR ; cong to congR ; axiom to axiomR ;
                      left-unit to left-unitR ; right-unit to right-unitR)
    using ()
  open PB Γ renaming (_≈_ to _≈Γ_ ; axiom to axiomΓ)
    using ()

  ----------------------------------------------------------------------
  -- Kernel inclusion.
  ----------------------------------------------------------------------

  include-kernel : Y -> Word (Y ⊎ X)
  include-kernel y = [ inj₁ y ]ʷ

  include-kernel* : Word Y -> Word (Y ⊎ X)
  include-kernel* = include-kernel *

  include-kernel*≡left : ∀ (w : Word Y) -> include-kernel* w ≡ [ w ]ₗ
  include-kernel*≡left [ y ]ʷ = refl
  include-kernel*≡left ε = refl
  include-kernel*≡left (u • v) rewrite include-kernel*≡left u | include-kernel*≡left v = refl

  include-kernel-well-defined :
    ∀ {u v : Word Y} ->
    S u v ->
    include-kernel* u ≈Γ include-kernel* v
  include-kernel-well-defined {u} {v} rel
    rewrite include-kernel*≡left u | include-kernel*≡left v =
    axiomΓ (kernel rel)

  ----------------------------------------------------------------------
  -- Projection to the quotient presentation.
  ----------------------------------------------------------------------

  to-quotient : Y ⊎ X -> Word X
  to-quotient (inj₁ _) = ε
  to-quotient (inj₂ x) = [ x ]ʷ

  to-quotient* : Word (Y ⊎ X) -> Word X
  to-quotient* = to-quotient *

  left-killed :
    ∀ (w : Word Y) ->
    to-quotient* [ w ]ₗ ≈R ε
  left-killed [ y ]ʷ = reflR
  left-killed ε = reflR
  left-killed (u • v) =
    transR (congR (left-killed u) (left-killed v)) left-unitR

  right-preserved :
    ∀ (w : Word X) ->
    to-quotient* [ w ]ᵣ ≈R w
  right-preserved [ x ]ʷ = reflR
  right-preserved ε = reflR
  right-preserved (u • v) =
    congR (right-preserved u) (right-preserved v)

  quotient-tail :
    ∀ (wy : Word Y) (wx : Word X) ->
    to-quotient* ([ wy ]ₗ • [ wx ]ᵣ) ≈R wx
  quotient-tail wy wx =
    transR (congR (left-killed wy) (right-preserved wx)) left-unitR

  quotient-head :
    ∀ (x : X) (wy : Word Y) ->
    to-quotient* ([ [ x ]ʷ ]ᵣ • [ wy ]ₗ) ≈R [ x ]ʷ
  quotient-head x wy =
    transR (congR reflR (left-killed wy)) right-unitR

  to-quotient-well-defined :
    ∀ {u v : Word (Y ⊎ X)} ->
    Γ u v ->
    to-quotient* u ≈R to-quotient* v
  to-quotient-well-defined (kernel {u} {v} _) =
    transR (left-killed u) (symR (left-killed v))
  to-quotient-well-defined (quotient {u} {v} ρ) =
    transR (right-preserved u)
      (transR (axiomR ρ)
        (symR (quotient-tail
          (ExtensionData.quotient-correction ext ρ)
          v)))
  to-quotient-well-defined (conjugation x y) =
    transR (quotient-head x [ y ]ʷ)
      (symR (quotient-tail
        (ExtensionData.conjugation-correction ext x y)
        [ x ]ʷ))

  to-quotient-preimage : Word X -> Word (Y ⊎ X)
  to-quotient-preimage = [_]ᵣ

  to-quotient-preimage-correct :
    ∀ (w : Word X) ->
    to-quotient* (to-quotient-preimage w) ≈R w
  to-quotient-preimage-correct = right-preserved

  ----------------------------------------------------------------------
  -- The exactness statement used by the full extension theorem.
  --
  -- In the paper proof this is the point where one proves that the
  -- subgroup K generated by the Y-generators is normal and is exactly
  -- the kernel of the quotient map F -> G/N.  In this syntactic
  -- presentation setting, the corresponding statement is:
  --
  --   if a word has trivial quotient projection, then it is equal in
  --   the extension presentation to a pure kernel word.
  --
  -- This cannot be derived from arbitrary correction functions alone;
  -- it is the compatibility/semantic hypothesis that the chosen
  -- corrections really come from a group extension.
  ----------------------------------------------------------------------

  record ExtensionExact : Set₁ where
    field
      kernel-complete :
        ∀ (w : Word (Y ⊎ X)) ->
        to-quotient* w ≈R ε ->
        ∃ λ (wy : Word Y) -> w ≈Γ [ wy ]ₗ

      kernel-sound :
        ∀ (wy : Word Y) ->
        to-quotient* [ wy ]ₗ ≈R ε

    kernel-sound-default :
      ∀ (wy : Word Y) ->
      to-quotient* [ wy ]ₗ ≈R ε
    kernel-sound-default = left-killed
