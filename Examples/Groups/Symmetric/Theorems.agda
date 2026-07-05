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
import Presentation.Base as PB
import Presentation.Properties as PP
open import Presentation.Definitions
open import Presentation.Normalization hiding (NormalForm)
open import Relation.Binary.Bundles using (Setoid)
open Setoid using (Carrier)

open import Notations

module Examples.Groups.Symmetric.Theorems where

open import Examples.Groups.Symmetric.Syntactics

import Examples.Groups.Symmetric.Loose.Uniqueness as LU
import Examples.Groups.Symmetric.Tight.Uniqueness as TU
open import Examples.Groups.Symmetric.NormalForm
open import Examples.Groups.Symmetric.Normalization using (nf-of)

open Relative

private variable
  n : ℕ

-- ----------------------------------------------------------------------
-- * Unique normal form, soundness, completeness and presentation

module Semantics-Loose where

  open import Examples.Groups.Symmetric.Loose.Semantics as SS
  open import Examples.Groups.Symmetric.Loose.Soundness

  unique-nf : ∀ n ->
    let
    module PPV = PP (n VRel,_===_)
    Syn        = PPV.word-setoid
    A          = Syn .Carrier
    B          = NF n
    Sem        = Endo-setoid n
    section    : A -> B
    section    = nf-of
    retraction : B -> A
    retraction = inv-nf
    in
    
    UniqueNormalForm Syn B section retraction Sem ⟦_⟧
    
  unique-nf = LU.unique-nf

  soundness : ∀ n ->
    let
    module PPV = PP (n VRel,_===_)
    Syn        = PPV.word-setoid
    Sem        = Endo-setoid n
    in
    
    Soundness Syn Sem ⟦_⟧
    
  soundness n = sound

  completeness : ∀ n ->
    let
    module PPV = PP (n VRel,_===_)
    Syn        = PPV.word-setoid
    Sem        = Endo-setoid n
    in
    
    Completeness Syn Sem ⟦_⟧
    
  completeness n = by-normalization (unique-nf n) (soundness n)
    where
    open PP (n VRel,_===_)
    open Completeness word-setoid (NF n) (nf-of {n}) (inv-nf {n}) (Endo-setoid n) (⟦_⟧ {n})


module Semantics-Tight where

  open import Examples.Groups.Symmetric.Tight.Semantics
  open import Examples.Groups.Symmetric.Tight.Soundness
  import Examples.Groups.Symmetric.Loose.Semantics as LooseSem
  open import Data.Fin.Permutation
    using ( Permutation′ ; _⟨$⟩ʳ_ ; _⟨$⟩ˡ_ ; _∘ₚ_ ; flip
          ; inverseˡ ; inverseʳ ; lift₀ ; lift₀-cong ; remove ; lift₀-remove)
  open import Data.Product using (∃ ; _,_ ; proj₁ ; proj₂)
  import Data.Fin as F
  import Examples.Groups.Symmetric.Tight.Presentation as P

  unique-nf : let open PP (n VRel,_===_) in
    UniqueNormalForm word-setoid (NF n) (nf-of {n}) (inv-nf {n}) (Group.setoid (Permutation′-group n)) (⟦_⟧ {n})
  unique-nf {n = n} = TU.unique-nf-tight
  
  soundness : let open PP (n VRel,_===_) in
    Soundness word-setoid (Group.setoid (Permutation′-group n)) ⟦_⟧
  soundness = sound

  completeness : let open PP (n VRel,_===_) in
    Completeness word-setoid (Group.setoid (Permutation′-group n)) ⟦_⟧
  completeness {n} = by-normalization unique-nf soundness
    where
    open PP (n VRel,_===_)
    open Completeness word-setoid (NF n) (nf-of {n}) (inv-nf {n}) {0ℓ} {0ℓ} (Group.setoid (Permutation′-group n)) (⟦_⟧ {n})


  presentation : let open PP (n VRel,_===_) in
    (n VRel,_===_) IsPresentationOf (Permutation′-group n)
  presentation {n = n} = P.presentation n
