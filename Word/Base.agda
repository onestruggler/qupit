------------------------------------------------------------------------
-- Presentations of groups
--
-- Free monoids (words) over a set of generators
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Notations
module Word.Base where

open import Level using (0ℓ)
open import Relation.Binary using (Rel)
open import Data.Product using (_×_ ; _,_)
open import Data.Nat using (ℕ ; suc ; zero)
open import Function using (_∘_)

private
  variable
    A B C X Y H N : Set

------------------------------------------------------------------------
-- Fixity declarations

infix  8 _^_ _^'_
infixr 7 _•_
infixl 9 _* _** _**' _⋆⋆
infixl 9 _ʰ
infixl 9 _ⁿ

------------------------------------------------------------------------
-- Words

-- Words in the language of monoids over a set of generators X.  A
-- word is either a singleton generator, the empty word, or a
-- concatenation of two words.
data Word (X : Set) : Set where
  [_]ʷ : X → Word X
  ε    : Word X
  _•_  : Word X → Word X → Word X

-- Right-associative power: w ^ n = w • w • … • w (n times).
_^_ : Word X → ℕ → Word X
w ^ zero        = ε
w ^ ₁₊ zero    = w
w ^ ₂₊ n = w • (w ^ ₁₊ n)

-- Left-associative power: w ^' n = w • … • w • w (n times).
_^'_ : Word X → ℕ → Word X
w ^' zero        = ε
w ^' ₁₊ zero    = w
w ^' ₂₊ n = (w ^' ₁₊ n) • w

------------------------------------------------------------------------
-- Functorial operations

-- Functorial map.
wmap : (f : A → B) → Word A → Word B
wmap f [ x ]ʷ      = [ f x ]ʷ
wmap f ε            = ε
wmap f (wa • wa₁)  = wmap f wa • wmap f wa₁

-- Flatten a word of words.
wconcat : Word (Word A) → Word A
wconcat [ ws ]ʷ     = ws
wconcat ε           = ε
wconcat (ws • ws₁)  = wconcat ws • wconcat ws₁

-- Monadic bind: extend f : A → Word B to Word A → Word B.
wconcatmap : (f : A → Word B) → Word A → Word B
wconcatmap f = wconcat ∘ wmap f

------------------------------------------------------------------------
-- Fold operations

-- Right fold over a word.
wfoldr : (A → B → B) → Word A → B → B
wfoldr _⊕_ [ x ]ʷ      b = x ⊕ b
wfoldr _⊕_ ε           b = b
wfoldr _⊕_ (wa • wa₁)  b = wfoldr _⊕_ wa (wfoldr _⊕_ wa₁ b)

-- Left fold over a word.
wfoldl : (B → A → B) → B → Word A → B
wfoldl _⊕_ b [ x ]ʷ     = b ⊕ x
wfoldl _⊕_ b ε          = b
wfoldl _⊕_ b (wa • wa₁) = wfoldl _⊕_ (wfoldl _⊕_ b wa) wa₁

------------------------------------------------------------------------
-- Stateful traversals (coset enumeration helpers)

-- hext lifts a single-step coset action to a step over a state
-- paired with an accumulated output word.
hext : (C → Y → Word X × C) → Word X × C → Y → Word X × C
hext t (w , c) y with t c y
... | (v , c') = w • v , c'

-- Left-to-right stateful traversal (_** is the deprecated form).
_⋆⋆ : (C → Y → Word X × C) → (C → Word Y → Word X × C)
_⋆⋆ h = wfoldl (hext h) ∘ emb
  where
  emb : C → Word X × C
  emb c = ε , c

hext' : (Y → C → C × Word X) → Y → C × Word X → C × Word X
hext' t y (c , w) with t y c
... | (c' , v) = c' , w • v

-- Right-to-left stateful traversal (_**' is the deprecated form).
_⋆⋆' : (Y → C → C × Word X) → (Word Y → C → C × Word X)
_⋆⋆' h wy = wfoldr (hext' h) wy ∘ emb
  where
  emb : C → C × Word X
  emb c = c , ε

------------------------------------------------------------------------
-- Conjugation helpers

-- wfoldr specialised to conjugation: apply a list of group elements.
_ʰ : (H → N → N) → Word H → N → N
_ʰ = wfoldr

-- Lift a conjugation action pointwise over a word of normals.
_ⁿ : (H → N → N) → H → Word N → Word N
_ⁿ = wmap ∘_

-- Conjugation with a word-valued action (one normal at a time).
_ⁿ' : (H → N → Word N) → H → Word N → Word N
(conj ⁿ') h [ x ]ʷ      = conj h x
(conj ⁿ') h ε            = ε
(conj ⁿ') h (ns • ns₁)  = (conj ⁿ') h ns • (conj ⁿ') h ns₁

-- Conjugation with a word-valued action (a word of group elements).
_ʰ' : (H → N → Word N) → Word H → Word N → Word N
(conj ʰ') [ x ]ʷ    ns = (conj ⁿ') x ns
(conj ʰ') ε          ns = ns
(conj ʰ') (hs • hs₁) ns = (conj ʰ') hs ((conj ʰ') hs₁ ns)

------------------------------------------------------------------------
-- Relations on words

-- A relation on Word X (used to specify presentation axioms).
WRel : Set → Set₁
WRel X = Rel (Word X) 0ℓ

------------------------------------------------------------------------
-- Deprecated
------------------------------------------------------------------------
-- The following names are kept for backwards compatibility.
-- They may be removed in a future version.

-- Compatibility alias for wconcatmap.
_* : (X → Word Y) → (Word X → Word Y)
_* = wconcatmap

-- Compatibility alias for _⋆⋆.
_** : (C → Y → Word X × C) → (C → Word Y → Word X × C)
_** h c [ y ]ʷ = h c y
_** h c ε      = ε , c
_** h c (w • u) with (_** h) c w
_** h c (w • u) | (w' , c') with (_** h) c' u
_** h c (w • u) | (w' , c') | (u' , c'') = w' • u' , c''

-- Compatibility alias for _⋆⋆'.
_**' : (Y → C → C × Word X) → (Word Y → C → C × Word X)
_**' h [ y ]ʷ c = h y c
_**' h ε      c = c , ε
_**' h (w • u) c with (_**' h) u c
_**' h (w • u) c | (c' , u') with (_**' h) w c'
_**' h (w • u) c | (c' , u') | (c'' , w') = c'' , w' • u'
