{-# OPTIONS --cubical-compatible --safe #-}
module Word.Base where

open import Level using (0ℓ)
open import Relation.Binary using (Rel)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Data.Product using (_×_ ; _,_)
open import Data.Nat using (ℕ ; suc ; zero)
open import Function using (_∘_)

private
  variable
    A B C X Y H N : Set

-- ----------------------------------------------------------------------
-- * Precedence of various operators

infix 8 _^_ _^'_
infixr 7 _•_
infixl 9 _* _** _**' _⋆⋆
infixl 9 _ʰ
infixl 9 _ⁿ

-- ----------------------------------------------------------------------
-- * Words

-- Words in the language of monoids, over a set of generators X. A
-- word is either a generator, the empty word, or a product of two
-- words.
data Word (X : Set) : Set where
  [_]ʷ : X -> Word X
  ε : Word X
  _•_ : Word X -> Word X -> Word X

-- For convenience, we define powers of words.
_^_ : Word X -> ℕ -> Word X
w ^ zero = ε
w ^ (suc zero) = w
w ^ suc (suc n) = w • (w ^ (suc n))

-- Left-associative powers of words.
_^'_ : Word X -> ℕ -> Word X
w ^' zero = ε
w ^' (suc zero) = w
w ^' suc (suc n) = (w ^' (suc n)) • w

-- ----------------------------------------------------------------------
-- * Auxiliary operations

-- Map for word.
wmap : (f : A -> B) -> Word A -> Word B
wmap f [ x ]ʷ = [ f x ]ʷ
wmap f ε = ε
wmap f (wa • wa₁) = wmap f wa • wmap f wa₁

-- Concatenation for word.
wconcat : Word (Word A) -> Word A
wconcat [ ws ]ʷ = ws
wconcat ε = ε
wconcat (ws • ws₁) = wconcat ws • wconcat ws₁

wconcatmap : (f : A -> Word B) -> Word A -> Word B
wconcatmap f = wconcat ∘ wmap f

-- word foldr.
wfoldr : (A -> B -> B) -> Word A -> B -> B
wfoldr _⊕_ [ x ]ʷ b = x ⊕ b
wfoldr _⊕_ ε b = b
wfoldr _⊕_ (wa • wa₁) b = let _⊕'_ = wfoldr _⊕_ in
  wa ⊕' (wa₁ ⊕' b)

-- word foldl.
wfoldl : (B -> A -> B) -> B -> Word A -> B
wfoldl _⊕_ b [ x ]ʷ = b ⊕ x
wfoldl _⊕_ b ε = b
wfoldl _⊕_ b (wa • wa₁) = let _⊕'_ = wfoldl _⊕_ in
  (b ⊕' wa) ⊕' wa₁

hext : (C -> Y -> Word X × C) -> Word X × C -> Y -> Word X × C
hext t (w , c) y with t c y
hext t (w , c) y | (v , c') = w • v , c'

-- a version of word foldl, the same as _**.
_⋆⋆ : (C -> Y -> Word X × C) -> (C -> Word Y -> Word X × C)
_⋆⋆ h = wfoldl (hext h) ∘ emb
  where
    emb : C -> Word X × C
    emb c = (ε , c)

hext' : (Y -> C -> C × Word X) -> Y -> C × Word X -> C × Word X
hext' t y (c , w) with t y c
hext' t y (c , w) | (c' , v) = c' ,  w • v

-- a version of word foldr, the same as _**'.
_⋆⋆' : (Y -> C -> C × Word X) -> (Word Y -> C -> C × Word X)
_⋆⋆' h wy = wfoldr (hext' h) wy ∘ emb
  where
    emb : C -> C × Word X
    emb c = (c , ε)

-- useful operations for dealing with conjugation.
_ʰ : (H -> N -> N) -> Word H -> N -> N
_ʰ = wfoldr

_ⁿ : (H -> N -> N) -> H -> Word N -> Word N
_ⁿ = wmap ∘_

-- useful operations for dealing with conjugation.
_ⁿ' : (H -> N -> Word N) -> H -> Word N -> Word N
(conj ⁿ') h [ x ]ʷ = conj h x
(conj ⁿ') h ε = ε
(conj ⁿ') h (ns • ns₁) = (conj ⁿ') h ns • (conj ⁿ') h ns₁

_ʰ' : (H -> N -> Word N) -> Word H -> Word N -> Word N
(conj ʰ') [ x ]ʷ ns = (conj ⁿ') x ns
(conj ʰ') ε ns = ns
(conj ʰ') (hs • hs₁) ns = (conj ʰ') hs ((conj ʰ') hs₁ ns)


-- Relation on words.
WRel : Set -> Set₁
WRel X = Rel (Word X) 0ℓ

------------------------------------------------------------------------
-- DEPRECATED
------------------------------------------------------------------------
-- Please use the new names as continuing support for the old names is
-- not guaranteed.

-- Extend a function from generators to words.
_* : (X -> Word Y) -> (Word X -> Word Y)
_* g = wconcat ∘ wmap g

-- a version of word foldl.
_** : (C -> Y -> Word X × C) -> (C -> Word Y -> Word X × C)
_** h c [ y ]ʷ = h c y
_** h c ε = (ε , c)
_** h c (w • u) with (h **) c w
_** h c (w • u) | (w' , c') with (h **) c' u
_** h c (w • u) | (w' , c') | (u' , c'') = (w' • u' , c'')


-- a version of word foldr.
_**' : (Y -> C -> C × Word X) -> (Word Y -> C -> C × Word X)
_**' h [ y ]ʷ c = h y c
_**' h ε c = (c , ε)
_**' h (w • u) c with (h **') u c
_**' h (w • u) c | (c' , u') with (h **') w c'
_**' h (w • u) c | (c' , u') | (c'' , w') = (c'' , w' • u')

