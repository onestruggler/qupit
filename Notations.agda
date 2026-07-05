------------------------------------------------------------------------
-- The Agda standard library
--
-- Aliases
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (zero ; suc)
open import Data.Fin using (zero ; suc)

import Relation.Binary.PropositionalEquality as Eq

module Notations where

Property = Set

pattern auto = Eq.refl

pattern ₀ = zero
pattern ₁ = suc ₀
pattern ₂ = suc ₁
pattern ₃ = suc ₂
pattern ₄ = suc ₃
pattern ₅ = suc ₄
pattern ₆ = suc ₅
pattern ₇ = suc ₆
pattern ₈ = suc ₇
pattern ₉ = suc ₈
pattern ₁₀ = suc ₉
pattern ₁₁ = suc ₁₀
pattern ₁₂ = suc ₁₁
pattern ₁₃ = suc ₁₂
pattern ₁₄ = suc ₁₃
pattern ₁₅ = suc ₁₄

pattern ₁₊ ⱼ = suc ⱼ
pattern ₂₊ ⱼ = suc (suc ⱼ)
pattern ₃₊ ⱼ = suc (suc (suc ⱼ))
pattern ₄₊ ⱼ = suc (suc (suc (suc ⱼ)))
