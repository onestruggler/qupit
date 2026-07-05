{-# OPTIONS  --safe #-}
{-# OPTIONS  --call-by-name #-}
--{-# OPTIONS --termination-depth=2 #-}
open import Level using (0ℓ)

open import Relation.Binary using (Rel)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Binary.Morphism.Definitions using (Homomorphic₂)
open import Relation.Binary.PropositionalEquality using (_≡_ ; _≢_ ; inspect ; setoid ; module ≡-Reasoning ; _≗_) renaming ([_] to [_]')
import Relation.Binary.Reasoning.Setoid as SR
import Relation.Binary.PropositionalEquality as Eq
open import Relation.Nullary.Decidable using (yes ; no)


open import Function using (_∘_ ; id)
open import Function.Definitions using (Injective)

open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂ ; map₁ ; ∃ ; Σ ; Σ-syntax)
open import Data.Product.Relation.Binary.Pointwise.NonDependent as PW using (≡×≡⇒≡ ; Pointwise ; ≡⇒≡×≡)
open import Data.Nat hiding (_^_ ; _+_ ; _*_ ;  _≟_)
open import Agda.Builtin.Nat using (_-_)
import Data.Nat as Nat
open import Data.Bool hiding (_<_ ; _≤_ ; _≟_)
open import Data.List hiding ([_] ; _++_ ; last ; head ; tail ; _∷ʳ_)
open import Data.Vec hiding ([_])
import Data.Vec as Vec
open import Data.Fin hiding (_+_ ; _-_)

open import Data.Maybe
open import Data.Sum using (_⊎_ ; inj₁ ; inj₂ ; [_,_] ; [_,_]′)
open import Data.Unit using (⊤ ; tt)
open import Data.Empty using (⊥ ; ⊥-elim)

open import Word.Base as WB hiding (wfoldl ; _*)
open import Word.Properties
import Presentation.Base as PB
import Presentation.Properties as PP
open PP using (NFProperty ; NFProperty')
import Presentation.CosetNF as CA
import Presentation.Reidemeister-Schreier as RS
module RSF = RS.Star-Injective-Full.Reidemeister-Schreier-Full

open import Presentation.Construct.Base hiding (_*_ ; _⊕_)
import Presentation.Construct.Properties.SemiDirectProduct2 as SDP2
import Presentation.Construct.Properties.DirectProduct as DP
import Presentation.Groups.Cyclic as Cyclic


open import Data.Fin using (Fin ; toℕ ; suc ; zero ; fromℕ)
open import Data.Fin.Properties using (suc-injective ; toℕ-inject₁ ; toℕ-fromℕ)
import Data.Nat.Properties as NP
open import Presentation.GroupLike
open import Presentation.Tactics hiding ([_] ; inspect)
open import Data.Nat.Primality
import Data.Fin.Properties as FP



module N.Coset3-Update-Sym (p-2 : ℕ) (p-prime : Prime (2+ p-2))  where

open import Zp.ModularArithmetic
open PrimeModulus p-2 p-prime
open import N.Symplectic p-2 p-prime
open import N.Lemmas-2Qupit p-2 p-prime
open import N.NF2-Sym p-2 p-prime
--open Lemmas-2Q 2
open Symplectic
open Lemmas-Sym
open import N.NF1-Sym p-2 p-prime
open import N.Ex-Sym p-2 p-prime
open import N.Ex-Sym1 p-2 p-prime
open import N.Ex-Sym2 p-2 p-prime
open import N.Ex-Sym3 p-2 p-prime
open import N.Ex-Sym4 p-2 p-prime
open import N.Ex-Sym5 p-2 p-prime hiding (module L0)
open import N.Cosets p-2 p-prime

open import N.Lemma-Comm p-2 p-prime 0
open import N.Completeness1-Sym p-2 p-prime renaming (module Completeness to Cp1)
open import N.Coset2-Update-Sym p-2 p-prime renaming (module Completeness to Cp2)
open Lemmas0a
open Lemmas0a1
open Lemmas0b
open Lemmas0c

open LM2
open import N.Completeness1-Sym p-2 p-prime renaming (module Completeness to CP1) using ()


module Completeness where

  open PB (3 QRel,_===_)
  open PP (3 QRel,_===_)
  open SR word-setoid
  open Pattern-Assoc
  open Sym0-Rewriting 1

  open import N.Proofs.P1 p-2 p-prime
  open import N.Proofs.P2 p-2 p-prime
  open import N.Proofs.P3 p-2 p-prime
  open import N.Proofs.P4 p-2 p-prime
  open import N.Proofs.P5 p-2 p-prime
  open import N.Proofs.P6 p-2 p-prime
  open import N.Proofs.P7 p-2 p-prime hiding (module L0)
  open import N.Proofs.P8 p-2 p-prime
  open import N.Lemmas-2Qupit-Sym p-2 p-prime as TQ
  open import N.Lemma-Postfix p-2 p-prime
  open import N.Derived p-2 p-prime
  open import N.Derived2 p-2 p-prime
--  open import N.NF1-Sym p-2 p-prime as NF1
--  open NF1.Normal-Form1 using ()
  
  open TQ.Lemmas-2Q 0
  open Duality
  import N.Duality p-2 p-prime as ND
  open Lemmas0 1
  module L0 = Lemmas0 0
  open import Algebra.Properties.Ring (+-*-ring p-2)
  open import Zp.Mod-Lemmas p-2 p-prime

  Lemma-three-qupit-completeness :

    ∀ (lm : Cosets3) (g :(Gen 3)) ->
    -----------------------------------------------------
    ∃ \ lm' -> ∃ \ w -> ⟦ lm ⟧₃ • [ g ]ʷ ≈ w ↑ • ⟦ lm' ⟧₃

  Lemma-three-qupit-completeness (case-I x x₁ x₂) H-gen = {!!}
  Lemma-three-qupit-completeness (case-I x x₁ x₂) S-gen = {!!}
  Lemma-three-qupit-completeness (case-I x x₁ x₂) CZ-gen = {!!}
  Lemma-three-qupit-completeness (case-I x x₁ x₂) (g ↥) = {!!}
  Lemma-three-qupit-completeness (case-II x x₁ x₂ x₃ x₄) H-gen = {!!}
  Lemma-three-qupit-completeness (case-II x x₁ x₂ x₃ x₄) S-gen = {!!}
  Lemma-three-qupit-completeness (case-II x x₁ x₂ x₃ x₄) CZ-gen = {!!}
  Lemma-three-qupit-completeness (case-II x x₁ x₂ x₃ x₄) (g ↥) = {!!}
