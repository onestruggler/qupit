module Presentation.Groups.Test where

open import Data.Fin hiding (_+_)
open import Data.Nat
open import Data.Product
open import Relation.Binary.PropositionalEquality using (_≡_ ; inspect ; setoid ; module ≡-Reasoning) renaming ([_] to [_]ₑ)


f : {n : ℕ} -> (a : Fin (suc n)) -> (b : Fin′ a) -> ℕ
f {n} zero ()
f {n} (suc a) zero = 1
f {n} (suc zero) (suc ())
f {n} (suc (suc a)) (suc zero) = 1
f {n} (suc (suc a)) (suc (suc b)) with f (suc a) (suc b)
... | ih = ih + 1


lemma-f : ∀ {n} a b -> f {n} a b ≡ toℕ a
lemma-f zero ()
lemma-f (suc a) zero = {!!}
lemma-f (suc zero) (suc ())
lemma-f (suc (suc a)) (suc zero) = {!!}
lemma-f (suc (suc a)) (suc (suc b)) = {!!}
