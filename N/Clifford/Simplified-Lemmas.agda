{-# OPTIONS --termination-depth=20 #-}
{-# OPTIONS --inversion-max-depth=1000 #-}

------------------------------------------------------------------------
-- Re-derivation of the Clifford conjugation base-lemma subtree for the
-- *Simplified* presentation (route (B): fully machine-checked).
--
-- This module is an aggregator: the development was split across four
-- files in the `Simplified-Lemmas/` folder (to keep each under ~1000
-- LOC).  It re-exports all of them publicly, so existing importers see
-- exactly the same names as before the split:
--
--   Part1 : Lemmas1-S
--   Part2 : Lemmas-Clifford-S, Simplified-GroupLike-S, Lemmas1b-S
--   Part3 : the standalone 𝑠/Z/CZ conjugation lemmas (CL, CLb glue)
--   Part4 : the tail-c10/c11 cascade, C10/C11, Completeness-S
--
-- Each part imports its predecessor with `public`, so re-exporting
-- Part4 alone transitively re-exports the whole subtree.
------------------------------------------------------------------------

open import Level using (0ℓ)
open import Relation.Binary.PropositionalEquality using (_≡_ ; _≢_)
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂ ; ∃)
open import Data.Nat hiding (_^_ ; _+_ ; _*_ ; _%_ ; _/_)
open import Data.Fin hiding (_+_ ; _-_)
open import Data.Nat.Primality
open import Zp.ModularArithmetic
open import Zp.Fermats-little-theorem

module N.Clifford.Simplified-Lemmas
  (p-3 : ℕ)
  (let p-2 = suc p-3)
  (p-prime : Prime (suc (suc p-2)))
  (let open PrimeModulus' p-2 p-prime)
  (g*@(g , g≠0) : ℤ* ₚ)
  (g-gen : ∀ ((x , _) : ℤ* ₚ) -> ∃ \ (k : ℤ ₚ-₁) -> x ≡ g ^′ toℕ k )
  where

open import N.Clifford.Simplified-Lemmas.Part4 p-3 p-prime g* g-gen public
