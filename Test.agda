{-# OPTIONS --safe #-}
open import Data.Nat
import Presentation.Vertical-Syntactics
open import Notations
data G : ℕ → Set where G1 : G 1 ; G2 : G 2
open Presentation.Vertical-Syntactics G using (Gen ; gate ; _↥)

-- Test: abstract ₂₊ n target
f : {n : ℕ} → Gen (₂₊ n) → ℕ
f {n} g with g
f {n} _ | gate 1 G1 = 1
f {n} _ | gate 2 G2 = 2
f {n} _ | h ↥ = 3
