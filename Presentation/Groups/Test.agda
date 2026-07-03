open import Notations
module Presentation.Groups.Test where

open import Data.Fin hiding (_+_)
open import Data.Nat
open import Data.Product
open import Relation.Binary.PropositionalEquality using (_≡_ ; inspect ; setoid ; module ≡-Reasoning) renaming ([_] to [_]ₑ)


f : {n : ℕ} -> (a : Fin (₁₊ n)) -> (b : Fin′ a) -> ℕ
f {n} zero ()
f {n} (₁₊ a) zero = 1
f {n} (₁₊ zero) (suc ())
f {n} (₂₊ a) (₁₊ zero) = 1
f {n} (₂₊ a) (₂₊ b) with f (₁₊ a) (₁₊ b)
... | ih = ih + 1


lemma-f : ∀ {n} a b -> f {n} a b ≡ toℕ a
lemma-f zero ()
lemma-f (₁₊ a) zero = {!!}
lemma-f (₁₊ zero) (suc ())
lemma-f (₂₊ a) (₁₊ zero) = {!!}
lemma-f (₂₊ a) (₂₊ b) = {!!}
