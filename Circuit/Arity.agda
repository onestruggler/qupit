{-# OPTIONS --safe #-}

------------------------------------------------------------------------
-- Deeper layer: arity-annotated generators and a single generic
-- "disjoint support ⇒ commute" axiom scheme.
--
-- The shallow layer (Circuit.Structure) still required each group to
-- state its own one-generator commutation axioms (comm-H, comm-S,
-- comm-CZ).  This layer removes that last piece of per-gate boilerplate.
--
-- A group additionally declares:
--   * `Bottom`         : an index set of its named "bottom" gates;
--   * `arity  b`       : how many bottom wires gate b occupies;
--   * `embed  b`       : the gate as a generator on `arity b + n` wires.
--
-- From this we generate ONE axiom scheme
--
--     disj : [ b ] • [ g shifted past b ]  ===  [ g shifted past b ] • [ b ]
--
-- valid for every bottom gate b and every generator g whose support is
-- disjoint from b's (i.e. g lifted `arity b` times).  Combined with a
-- group's own relations it yields, with NO further per-group input, the
-- whole-word and power commutation lemmas.
------------------------------------------------------------------------

open import Data.Nat using (ℕ ; suc ; zero ; _+_)
open import Data.Sum using (_⊎_ ; inj₁ ; inj₂)
open import Word.Base
import Presentation.Base as PB

module Circuit.Arity
  {Gen : ℕ → Set}
  (_↥ : ∀ {n} → Gen n → Gen (suc n))
  (Bottom : Set)
  (arity  : Bottom → ℕ)
  (embed  : (b : Bottom) → ∀ {n} → Gen (arity b + n))
  where

-- Reuse the whole shallow engine: _↑, Lifted, lemma-lift, comm-along, …
open import Circuit.Structure {Gen} _↥ public

-- Shift a generator up by k wires (support moves from {…} to {…}+k).
liftⁿ : ∀ k {n} → Gen n → Gen (k + n)
liftⁿ zero    g = g
liftⁿ (suc k) g = liftⁿ k g ↥

------------------------------------------------------------------------
-- The generic disjoint-commutation axiom scheme, as a relation family.

data Disj : (n : ℕ) → WRel (Gen n) where
  disj : ∀ (b : Bottom) {n} (g : Gen n) →
         Disj (arity b + n)
              ([ embed b ]ʷ • [ liftⁿ (arity b) g ]ʷ)
              ([ liftⁿ (arity b) g ]ʷ • [ embed b ]ʷ)

-- Combine a group's own relations with the generic disjoint scheme.
infixl 5 _+Disj
_+Disj : (R : ∀ n → WRel (Gen n)) → (∀ n → WRel (Gen n))
(R +Disj) n w v = R n w v ⊎ Disj n w v

------------------------------------------------------------------------
-- Consequences, fully generic (a group supplies NO commutation input).

module _ (R : ∀ n → WRel (Gen n)) where

  -- The presentation reasoned in: group relations + disjoint scheme,
  -- then closed under lifting.
  Pres : (n : ℕ) → WRel (Gen n)
  Pres = Lifted (R +Disj)

  -- A bottom gate commutes with an ARBITRARY subcircuit `w` sitting on
  -- the wires above its support.  Derived once, for every group.
  gate-comm-word : ∀ (b : Bottom) {n} (w : Word (Gen n)) →
    let open PB (Pres (arity b + n)) using (_≈_) in
    [ embed b ]ʷ • wmap (liftⁿ (arity b)) w ≈ wmap (liftⁿ (arity b)) w • [ embed b ]ʷ
  gate-comm-word b {n} w =
    comm-along (liftⁿ (arity b) {n}) (Pres (arity b + n)) [ embed b ]ʷ
               (λ g → PB.axiom (base (inj₂ (disj b g)))) w

  -- …and so does every power of a bottom gate.
  gate-comm-word-^ : ∀ (b : Bottom) {n} (k : ℕ) (w : Word (Gen n)) →
    let open PB (Pres (arity b + n)) using (_≈_) in
    ([ embed b ]ʷ ^ k) • wmap (liftⁿ (arity b)) w
      ≈ wmap (liftⁿ (arity b)) w • ([ embed b ]ʷ ^ k)
  gate-comm-word-^ b {n} k w =
    comm-along-^ (liftⁿ (arity b) {n}) (Pres (arity b + n)) [ embed b ]ʷ
                 (λ g → PB.axiom (base (inj₂ (disj b g)))) k w
