{-# OPTIONS  --safe #-}
open import Level using (0ℓ)
open import Relation.Binary using (IsEquivalence ; Setoid ; Rel)
open import Data.Product using (_,_)
open import Relation.Binary.Morphism.Definitions using (Homomorphic₂)
open import Relation.Binary.PropositionalEquality using (_≡_)
import Relation.Binary.PropositionalEquality as Eq

open import Word.Base
module Presentation.Base {X : Set} (Γ : WRel X) where

open import Relation.Binary.Definitions using (DecidableEquality ; Decidable)
open import Relation.Binary.Morphism.Structures using (IsRelMonomorphism)
open import Relation.Binary.PropositionalEquality using (_≡_ ; setoid)
import Relation.Binary.PropositionalEquality as Eq
open import Relation.Nullary.Decidable using (via-injection)
open import Function.Definitions using (Injective)
open import Function.Bundles using (Injection)
open import Function using (_∘_)

private
  variable
    w v u w' v' u' : Word X

infix 4 _===_
_===_ = Γ

infix 4 _≈_
data _≈_ : WRel X where
  -- ≈ is a congruence.
  refl : w ≈ w
  sym : w ≈ v -> v ≈ w
  trans : w ≈ v -> v ≈ u -> w ≈ u
  cong : w ≈ w' -> v ≈ v' -> w • v ≈ w' • v'

  -- The monoid axioms: asociativity and the left and right unit laws.
  assoc : (w • v) • u ≈ w • (v • u)
  left-unit : ε • w ≈ w
  right-unit : w • ε ≈ w

  -- Axioms.
  axiom : Γ w v -> w ≈ v

refl' : w ≡ v -> w ≈ v
refl' Eq.refl = refl

Alphabet = X

infixl 4 _reversed
infixl 3 cleft_
infixl 3 cright_

_reversed : {w v : Word X} -> w ≈ v -> v ≈ w
_reversed = sym

cleft_ : {w v u : Word X} -> w ≈ v -> w • u ≈ v • u
cleft_ E = cong E refl

cright_ : {w v u : Word X} -> w ≈ v -> u • w ≈ u • v
cright_ E = cong refl E
