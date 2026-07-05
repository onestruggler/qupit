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
open import Examples.Groups.Symmetric.NormalForm
open import Examples.Groups.Symmetric.Normalization using (nf-of)

open Relative

private variable
  n : ℕ

-- ----------------------------------------------------------------------
-- * Unique normal form, soundness, completeness and presentation

module Loose where

  open import Examples.Groups.Symmetric.Loose.Semantics as SS
  import Examples.Groups.Symmetric.Loose.Soundness as LS
  import Examples.Groups.Symmetric.Loose.Completeness as LC
  import Examples.Groups.Symmetric.Loose.Uniqueness as LU

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
    
  soundness n = LS.sound

  completeness : ∀ n ->
    let
    module PPV = PP (n VRel,_===_)
    Syn        = PPV.word-setoid
    Sem        = Endo-setoid n
    in
    
    Completeness Syn Sem ⟦_⟧
    
  completeness = LC.completeness


module Semantics-Tight where

  open import Examples.Groups.Symmetric.Tight.Semantics as SS
  import Examples.Groups.Symmetric.Tight.Soundness as TS
  import Examples.Groups.Symmetric.Tight.Completeness as TC
  import Examples.Groups.Symmetric.Tight.Uniqueness as TU
  import Examples.Groups.Symmetric.Tight.Presentation as TP

  unique-nf : ∀ n ->
    let
    module PPV = PP (n VRel,_===_)
    Syn        = PPV.word-setoid
    A          = Syn .Carrier
    B          = NF n
    Sem        = Group.setoid (Permutation′-group n)
    section    : A -> B
    section    = nf-of
    retraction : B -> A
    retraction = inv-nf
    in
    
    UniqueNormalForm Syn B section retraction Sem ⟦_⟧
    
  unique-nf n = TU.unique-nf-tight {n}

  soundness : ∀ n ->
    let
    module PPV = PP (n VRel,_===_)
    Syn        = PPV.word-setoid
    Sem        = Group.setoid (Permutation′-group n)
    in
    
    Soundness Syn Sem ⟦_⟧
    
  soundness n = TS.sound

  completeness : ∀ n ->
    let
    module PPV = PP (n VRel,_===_)
    Syn        = PPV.word-setoid
    Sem        = Group.setoid (Permutation′-group n)
    in
    
    Completeness Syn Sem ⟦_⟧
    
  completeness n = TC.completeness {n} 


  presentation : ∀ n -> (n VRel,_===_) IsPresentationOf (Permutation′-group n)
  presentation = TP.presentation
