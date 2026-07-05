{-# OPTIONS --safe #-}

open import Data.Nat using (ℕ)
import Presentation.Properties as PP
open import Presentation.Definitions
open import Presentation.Normalization hiding (NormalForm)

module Examples.Groups.Symmetric.Loose.Completeness where

open import Examples.Groups.Symmetric.Syntactics
open import Examples.Groups.Symmetric.NormalForm
open import Examples.Groups.Symmetric.Normalization using (nf-of)
open import Examples.Groups.Symmetric.Loose.Semantics
open import Examples.Groups.Symmetric.Loose.Soundness
import Examples.Groups.Symmetric.Loose.Uniqueness as LU
open Relative

completeness : ∀ n →
  let
  module PPV = PP (n VRel,_===_)
  Syn        = PPV.word-setoid
  Sem        = Endo-setoid n
  in
  Completeness Syn Sem ⟦_⟧
completeness n = by-normalization (LU.unique-nf n) sound
  where
  open PP (n VRel,_===_)
  open Completeness word-setoid (NF n) (nf-of {n}) (inv-nf {n}) (Endo-setoid n) (⟦_⟧ {n})
