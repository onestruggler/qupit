{-# OPTIONS --safe #-}

------------------------------------------------------------------------
-- Generic structural rules for wire-indexed circuit presentations.
--
-- A "wire-indexed circuit family" is a generator family
--
--     Gen : ℕ → Set
--
-- together with a shift  _↥ : Gen n → Gen (suc n)  that moves a gate
-- onto a later wire (freeing wire 0).  Clifford circuits
-- (N/Symplectic.agda) are one instance; the symmetric group Sₙ
-- (Circuit/Example/Sn.agda) is another.
--
-- Every such family shares the SAME structural rules, independently of
-- the group-specific relations:
--
--   (1) lifting  : a relation valid on n wires is valid on n+1 wires
--                  (the `cong↑` rule of N/Symplectic.agda);
--   (2) disjoint : a gate commutes with any subcircuit living on wires
--                  disjoint from its support (the `comm-H/S/CZ` rules
--                  and their `lemma-comm-*-w↑` consequences).
--
-- This module provides both, ONCE, so a new circuit family only has to
-- declare its own group-specific relations and then apply this module.
------------------------------------------------------------------------

open import Data.Nat using (ℕ ; suc ; zero)
open import Word.Base
import Presentation.Base as PB

module Circuit.Structure
  {Gen : ℕ → Set}
  (_↥ : ∀ {n} → Gen n → Gen (suc n))
  where

infixl 10 _↑

-- Lifting a whole word onto a later wire: the monoid homomorphism
-- induced by the generator shift.  Note that `_↑` distributes over `•`
-- and fixes `ε` *definitionally* (it is `wmap`), which is what makes the
-- generic proofs below go through with only `refl` at the joints.
_↑ : ∀ {n} → Word (Gen n) → Word (Gen (suc n))
_↑ = wmap _↥

------------------------------------------------------------------------
-- (1) The lifting structure rule.
--
-- A group supplies a family of group-specific relations
--
--     R : ∀ n → WRel (Gen n).
--
-- The actual presentation used for reasoning is `Lifted R`, which is R
-- closed under the single structural constructor `lift↑`.  This replaces
-- the ad-hoc `cong↑` constructor that used to sit *inside* every group's
-- relation type.
------------------------------------------------------------------------

data Lifted (R : ∀ n → WRel (Gen n)) : (n : ℕ) → WRel (Gen n) where
  base  : ∀ {n w v} → R n w v → Lifted R n w v
  lift↑ : ∀ {n w v} → Lifted R n w v → Lifted R (suc n) (w ↑) (v ↑)

-- The lifting rule is *admissible on the whole congruence closure*, for
-- ANY relation family `Γ` that is stable under lifting at the axiom level
-- (i.e. that provides a `cong↑`-style rule).  This is the generic form of
-- `lemma-cong↑`; it applies equally to `Lifted R` (via `lift↑`) and to a
-- bespoke relation datatype such as N/Symplectic's `_QRel,_===_` (via its
-- own `cong↑` constructor).
module _ (Γ : ∀ n → WRel (Gen n))
         (cong↑ : ∀ {n} {w v : Word (Gen n)} → Γ n w v → Γ (suc n) (w ↑) (v ↑))
         where
  lift-closure : ∀ {n} (w v : Word (Gen n)) →
    let open PB (Γ n)       using (_≈_)                    in
    let open PB (Γ (suc n)) using () renaming (_≈_ to _≈↑_) in
    w ≈ v → w ↑ ≈↑ v ↑
  lift-closure w v PB.refl         = PB.refl
  lift-closure w v (PB.sym e)      = PB.sym (lift-closure v w e)
  lift-closure w v (PB.trans e e₁) = PB.trans (lift-closure _ _ e) (lift-closure _ _ e₁)
  lift-closure w v (PB.cong e e₁)  = PB.cong (lift-closure _ _ e) (lift-closure _ _ e₁)
  lift-closure w v PB.assoc        = PB.assoc
  lift-closure w v PB.left-unit    = PB.left-unit
  lift-closure w v PB.right-unit   = PB.right-unit
  lift-closure w v (PB.axiom x)    = PB.axiom (cong↑ x)

module _ (R : ∀ n → WRel (Gen n)) where

  -- The `Lifted R` instance of `lift-closure` (used by the examples).
  lemma-lift : ∀ {n} (w v : Word (Gen n)) →
    let open PB (Lifted R n)       using (_≈_)              in
    let open PB (Lifted R (suc n)) using () renaming (_≈_ to _≈↑_) in
    w ≈ v → w ↑ ≈↑ v ↑
  lemma-lift = lift-closure (Lifted R) lift↑

------------------------------------------------------------------------
-- (2) The disjoint-commutation structure rule.
--
-- Let `e : Gen j → Gen m` be an embedding of "far" generators (typically
-- an iterated shift `_↥`), and let Γ be any relation on `Gen m`.  If a
-- fixed gate `c` commutes with every embedded *generator* `[ e g ]ʷ`,
-- then it commutes with every embedded *word* `wmap e w`, and with every
-- power `c ^ k` as well.
--
-- The induction on the word / on the power is IDENTICAL for H, S, CZ and
-- for the gates of any other group; only the one-generator base fact is
-- group-specific.  So a group supplies just that base fact (its
-- `comm-H`/`comm-S`/`comm-CZ` axioms) and gets the word- and
-- power-level `lemma-comm-*-w↑` lemmas for free.
------------------------------------------------------------------------

module _ {j m} (e : Gen j → Gen m) (Γ : WRel (Gen m)) where

  open PB Γ

  comm-along : (c : Word (Gen m)) →
               (∀ g → c • [ e g ]ʷ ≈ [ e g ]ʷ • c) →
               ∀ w → c • wmap e w ≈ wmap e w • c
  comm-along c h [ x ]ʷ    = h x
  comm-along c h ε         = trans right-unit (sym left-unit)
  comm-along c h (w • w₁)  =
    trans (sym assoc)
    (trans (cong (comm-along c h w) refl)
    (trans assoc
    (trans (cong refl (comm-along c h w₁))
           (sym assoc))))

  comm-along-^ : (c : Word (Gen m)) →
                 (∀ g → c • [ e g ]ʷ ≈ [ e g ]ʷ • c) →
                 ∀ k w → (c ^ k) • wmap e w ≈ wmap e w • (c ^ k)
  comm-along-^ c h zero          w = trans left-unit (sym right-unit)
  comm-along-^ c h (suc zero)    w = comm-along c h w
  comm-along-^ c h (suc (suc k)) w =
    trans assoc
    (trans (cong refl (comm-along-^ c h (suc k) w))
    (trans (sym assoc)
    (trans (cong (comm-along c h w) refl)
           assoc)))
