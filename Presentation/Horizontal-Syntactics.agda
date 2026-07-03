------------------------------------------------------------------------
-- Presentations of groups
--
-- Congruence closure of a word relation (the presented monoid)
------------------------------------------------------------------------

{-# OPTIONS --safe #-}

open import Word.Base using (WRel ; Word ; [_]ʷ ; ε ; _•_)

module Presentation.Horizontal-Syntactics {X : Set} (Γ : WRel X) where

open import Relation.Binary.PropositionalEquality as Eq using (_≡_)

private
  variable
    w v u w' v' u' : Word X

------------------------------------------------------------------------
-- Syntax of a presented monoid

-- Raw axioms: exactly the generating relations.
infix 4 _===_
_===_ = Γ

-- Congruence closure of the generating relations together with the
-- free-monoid laws.  This is the word problem for the presented monoid.
infix 4 _≈_
data _≈_ : WRel X where
  refl  : w ≈ w
  sym   : w ≈ v → v ≈ w
  trans : w ≈ v → v ≈ u → w ≈ u
  cong  : w ≈ w' → v ≈ v' → w • v ≈ w' • v'
  assoc      : (w • v) • u ≈ w • (v • u)
  left-unit  : ε • w ≈ w
  right-unit : w • ε ≈ w
  axiom      : Γ w v → w ≈ v

-- Lift propositional equality into the congruence.
refl' : w ≡ v → w ≈ v
refl' Eq.refl = refl

Alphabet = X

------------------------------------------------------------------------
-- Congruence combinators

infixl 4 _reversed
infixl 3 cleft_
infixl 3 cright_

_reversed : w ≈ v → v ≈ w
_reversed = sym

cleft_ : w ≈ v → w • u ≈ v • u
cleft_ E = cong E refl

cright_ : w ≈ v → u • w ≈ u • v
cright_ E = cong refl E
