{-# OPTIONS --safe #-}

open import Data.Nat using (ℕ)
open import Algebra.Bundles using (Group)
import Presentation.Properties as PP
open import Presentation.Definitions
open import Presentation.Normalization hiding (NormalForm)

module Examples.Groups.Symmetric.Tight.Completeness where

open import Examples.Groups.Symmetric.Syntactics
open import Examples.Groups.Symmetric.NormalForm
open import Examples.Groups.Symmetric.Normalization using (nf-of)
open import Examples.Groups.Symmetric.Tight.Semantics
open import Examples.Groups.Symmetric.Tight.Soundness
import Examples.Groups.Symmetric.Tight.Uniqueness as TU
import Examples.Groups.Symmetric.Tight.Semantics as ST

open ST using (Permutation′-group)
open Relative

private variable n : ℕ

completeness : let open PP (n VRel,_===_) in
  Completeness word-setoid (Group.setoid (Permutation′-group n)) ⟦_⟧
completeness {n} = by-normalization TU.unique-nf-tight (sound {n})
  where
  open PP (n VRel,_===_)
  open Completeness word-setoid (NF n) (nf-of {n}) (inv-nf {n}) (Group.setoid (Permutation′-group n)) (⟦_⟧ {n})
