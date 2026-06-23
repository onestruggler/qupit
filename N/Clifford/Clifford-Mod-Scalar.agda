{-# OPTIONS --safe #-}
{-# OPTIONS --termination-depth=20 #-}

------------------------------------------------------------------------
-- Qudit Clifford group mod scalars.
--
-- This module is an aggregator: the development was split across three
-- files in the `Clifford-Mod-Scalar/` folder (to keep each under ~1000
-- LOC).  It re-exports all of them publicly, so every existing importer
-- (`open import N.Clifford.Clifford-Mod-Scalar …`) sees exactly the same
-- names as before the split:
--
--   Part1 : shared preamble (patterns, 𝑠/1/2, Symplectic), Clifford-Relations, Lemmas-Clifford
--   Part2 : Lemmas1
--   Part3 : Clifford-GroupLike, CommData-Sim, Commuting-Symplectic-Sim,
--           Rewriting-Sim, Sim-Rewriting, Lemmas1b
--
-- Each part imports its predecessor with `public`, so re-exporting Part3
-- alone transitively re-exports the whole module.
--
-- The previous abandoned WIP tail (incomplete proofs with `{!!}` holes,
-- formerly block-commented) lives in archive/Clifford-Mod-Scalar-tail.agda.txt
-- and is not part of the build.
------------------------------------------------------------------------

open import Relation.Binary.PropositionalEquality using (_≡_ ; _≢_)
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂ ; ∃)
open import Data.Nat hiding (_^_ ; _+_ ; _*_ ; _%_ ; _/_)
open import Data.Fin hiding (_+_ ; _-_)
open import Data.Nat.Primality
open import Zp.ModularArithmetic
open import Zp.Fermats-little-theorem

module N.Clifford.Clifford-Mod-Scalar
  (p-3 : ℕ)
  (let p-2 = suc p-3)
  (p-prime : Prime (suc (suc p-2)))
  (let open PrimeModulus' p-2 p-prime)
  (g*@(g , g≠0) : ℤ* ₚ)
  (g-gen : ∀ ((x , _) : ℤ* ₚ) -> ∃ \ (k : ℤ ₚ-₁) -> x ≡ g ^′ toℕ k )
  where

-- Part1 carries the shared preamble (patterns, 1/2, Symplectic, …) and the
-- first modules; re-export it in full.  From Part2/Part3 re-export only their
-- own modules (their preambles are copies of Part1's — taking them again would
-- be a duplicate definition).
open import N.Clifford.Clifford-Mod-Scalar.Part1 p-3 p-prime g* g-gen public
open import N.Clifford.Clifford-Mod-Scalar.Part2 p-3 p-prime g* g-gen public
  using (module Lemmas1)
open import N.Clifford.Clifford-Mod-Scalar.Part3 p-3 p-prime g* g-gen public
  using ( module Clifford-GroupLike ; module CommData-Sim ; module Commuting-Symplectic-Sim
        ; module Rewriting-Sim ; module Sim-Rewriting ; module Lemmas1b )
