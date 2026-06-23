{-# OPTIONS --safe #-}
{-# OPTIONS --termination-depth=20 #-}

------------------------------------------------------------------------
-- A *simplified* relation set for the qudit Clifford group mod scalars,
-- an analogue of `N.Symplectic-Simplified` for `N.Clifford.Clifford-Mod-Scalar`.
--
-- Simplification strategy (applied per relation):
--   (1) push the X and Z (Pauli) parts of both sides to the right-most
--       position and cancel them as far as possible;
--   (2) use only the basic gates S, H, CZ as much as possible
--       (in particular, prefer S over 𝑠 = S · Z^½);
--   (3) keep the original structure as much as possible.
--
-- The generators and all the derived words (X, Z, 𝑠, M, Mg, …) are
-- inherited unchanged from `Clifford-Mod-Scalar`; only the *relation
-- set* `_QRel,_===_` is redefined.
--
-- NOTE: this file states the proposed simplified presentation only.
-- Proving it equivalent to `Clifford-Relations._QRel,_===_` (an
-- isomorphism `id`, in the style of `Iso3`) is the next step.
------------------------------------------------------------------------

open import Level using (0ℓ)

open import Relation.Binary using (Rel)
open import Relation.Binary.PropositionalEquality using (_≡_ ; _≢_)

open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂ ; ∃)
open import Data.Nat hiding (_^_ ; _+_ ; _*_ ; _%_ ; _/_)
import Data.Nat as Nat
open import Data.Fin hiding (_+_ ; _-_)
open import Data.Sum using (_⊎_ ; inj₁ ; inj₂)

open import Word.Base as WB hiding (wfoldl ; _* ; _^'_)
import Presentation.Base as PB

open import Presentation.Construct.Base hiding (_*_)
open import Presentation.GroupLike
open import Data.Nat.Primality

open import Zp.ModularArithmetic
open import Zp.Fermats-little-theorem


module N.Clifford.Clifford-Mod-Scalars-Simplified
  (p-3 : ℕ)
  (let p-2 = suc p-3)
  (p-prime : Prime (suc (suc p-2)))
  (let open PrimeModulus' p-2 p-prime)
  (g*@(g , g≠0) : ℤ* ₚ)
  (g-gen : ∀ ((x , _) : ℤ* ₚ) -> ∃ \ (k : ℤ ₚ-₁) -> x ≡ g ^′ toℕ k )
  where

pattern ₀ = zero
pattern ₁ = suc ₀
pattern ₂ = suc ₁
pattern ₁₊ n = suc n
pattern ₂₊ n = suc (suc n)
pattern ₃₊ n = suc (₂₊ n)

open Primitive-Root-Modp' g* g-gen

-- Inherit the generators (S, H, CZ, ↥) and every derived word
-- (X, Z, X⁻¹, Z⁻¹, S⁻¹, Z^, X^, 𝑠, 𝑠^, M, M₋₁, Mg, Mg^, ⊤⊥, ⊥⊤, …)
-- from the original Clifford presentation.
open import N.Clifford.Clifford-Mod-Scalar p-3 p-prime g* g-gen
open Clifford-Relations hiding (_QRel,_===_)


module Simplified-Relations where

  -- The bare S,H multiplier of Mg = M g′ and the leftover Pauli exponent
  -- ½(g-1), used only to state the simplified semi-M𝑠 relation.  Kept
  -- `private` so they don't collide with the local copies in Mg-Simplify /
  -- Mg-Simplify-S (they are definitionally equal to those, so the iso still
  -- lines up).
  private
    Wg : ∀ {n} -> Word (Gen (₁₊ n))
    Wg = S ^ toℕ (g* .proj₁) • H • S ^ toℕ ((g* ⁻¹) .proj₁) • H • S ^ toℕ (g* .proj₁) • H

    zX : ℕ
    zX = toℕ ((g* .proj₁ + (- 1ₚ)) * 1/2)

  infix 4 _QRel,_===_
  data _QRel,_===_ : (n : ℕ) → WRel (Gen n) where

    ----------------------------------------------------------------
    -- (A) Single-qudit symplectic layer — already in basic S, H.
    --     No X/Z present: kept verbatim.
    ----------------------------------------------------------------
    order-S :       ∀ {n} → (₁₊ n) QRel,  S ^ p === ε
    order-SH :      ∀ {n} → (₁₊ n) QRel,  (S • H) ^ 3 === ε
    comm-HHSHHS :   ∀ {n} → (₁₊ n) QRel,  H • H • S • H • H • S === S • H • H • S • H • H

    ----------------------------------------------------------------
    -- (B) Metaplectic layer.
    --     order-H / M-power pin down the "diagonal" subgroup; kept verbatim.
    --
    --     semi-M𝑠 is stated in its *simplified* form: the metaplectic
    --     Mg = M g′ is replaced by its bare S,H multiplier
    --     Wg = S^g·H·S^(g⁻¹)·H·S^g·H, with Mg's own Pauli pushed out and
    --     cancelled, leaving a single Z^zX correction (zX = ½(g-1)):
    --
    --        semi-M𝑠 :  Wg · 𝑠 = 𝑠^(g²) · Wg · Z^(½(g-1))
    --
    --     This is the `simplified-semi-M𝑠` theorem of N.Clifford.Mg-Simplify
    --     (soundness, in the original Clifford presentation); the original
    --     Mg-form is recovered as `completeness-semi-M𝑠` in N.Clifford.Mg-Simplify-S.
    --
    --     semi-M↑CZ / semi-M↓CZ are kept in their *original* Mg-form.  They
    --     cannot be simplified the same way: the simplified statement's
    --     completeness proof would need Z↔CZ commutation, which (unlike the
    --     single-qudit 𝑠 case) is NOT a consequence of the selinger + Pauli
    --     relations — it genuinely requires the metaplectic relations
    --     themselves, so demoting them is circular.  Kept verbatim.
    ----------------------------------------------------------------
    order-H :       ∀ {n} → (₁₊ n) QRel,  H ^ 2 === M₋₁
    M-power : ∀ {n} (k : ℤ ₚ) → (₁₊ n) QRel,  Mg^ k === M (g^ k)
    semi-M𝑠 :       ∀ {n} → (₁₊ n) QRel,  Wg • 𝑠 === 𝑠^ (g * g) • Wg • Z ^ zX
    semi-M↑CZ :     ∀ {n} → (₂₊ n) QRel,  Mg ↑ • CZ === CZ^ g • Mg ↑
    semi-M↓CZ :     ∀ {n} → (₂₊ n) QRel,  Mg ↓ • CZ === CZ^ g • Mg ↓

    ----------------------------------------------------------------
    -- (C) Pauli layer — the canonical transport rules for X, Z.
    --     X and Z are already at the right-most positions, nothing
    --     to cancel: these *define* the Pauli action, kept verbatim.
    ----------------------------------------------------------------
    comm-X-Z :      ∀ {n} → (₁₊ n) QRel,  X • Z === Z • X
    rel-X↑-CZ :     ∀ {n} → (₂₊ n) QRel,  CZ • X ↑ === X ↑ • Z ↓ • CZ
    rel-X↓-CZ :     ∀ {n} → (₂₊ n) QRel,  CZ • X ↓ === X ↓ • Z ↑ • CZ

    ----------------------------------------------------------------
    -- (D) CZ layer (no X/Z): kept verbatim.
    ----------------------------------------------------------------
    order-CZ :      ∀ {n} → (₂₊ n) QRel,  CZ ^ p === ε
    comm-CZ-S↓ :    ∀ {n} → (₂₊ n) QRel,  CZ • S ↓ === S ↓ • CZ
    comm-CZ-S↑ :    ∀ {n} → (₂₊ n) QRel,  CZ • S ↑ === S ↑ • CZ

    ----------------------------------------------------------------
    -- (E) The two "selinger" CZ–H–CZ relations: this is where the
    --     strategy actually changes something.
    --
    --     Original (Clifford-Relations), using 𝑠 = S · Z^½ :
    --        CZ • H↑ • CZ
    --          === 𝑠↑⁻¹ • H↑ • 𝑠↑⁻¹ • CZ • H↑ • 𝑠↑⁻¹ • 𝑠↓⁻¹
    --
    --     Replace every 𝑠⁻¹ by the basic S⁻¹ (= 𝑠⁻¹ · Z^½), push the
    --     resulting Z-halves to the right and cancel.  The symplectic
    --     part is exactly the `N.Symplectic-Simplified` relation; the
    --     leftover Pauli collapses to a single tail X↑ · Z↑ (the Z↓
    --     halves cancel).  Result (basic gates, Pauli right-most):
    --
    --        CZ • H↑ • CZ • X↑ • Z↑
    --          === S⁻¹↑ • H↑ • S⁻¹↑ • CZ • H↑ • S⁻¹↑ • S⁻¹↓
    --
    --     (and ↑↔↓ for c11, with tail X↓ · Z↓).
    --
    --     [proposed; the Pauli tail still needs to be verified.]
    ----------------------------------------------------------------
    selinger-c10 :  ∀ {n} → (₂₊ n) QRel,
      CZ • H ↑ • CZ • X ↑ • Z ↑ === S ↑ ^ p-1 • H ↑ • S ↑ ^ p-1 • CZ • H ↑ • S ↑ ^ p-1 • S ↓ ^ p-1
    selinger-c11 :  ∀ {n} → (₂₊ n) QRel,
      CZ • H ↓ • CZ • X ↓ • Z ↓ === S ↓ ^ p-1 • H ↓ • S ↓ ^ p-1 • CZ • H ↓ • S ↓ ^ p-1 • S ↑ ^ p-1

    ----------------------------------------------------------------
    -- (F) Three-qudit selinger relations (no X/Z): kept verbatim.
    ----------------------------------------------------------------
    selinger-c12 :  ∀ {n} → (₃₊ n) QRel,  CZ ↑ • CZ === CZ • CZ ↑
    selinger-c13 :  ∀ {n} → (₃₊ n) QRel,  ⊤⊥ ↑ • CZ ↓ • ⊥⊤ ↑ === ⊥⊤ ↓ • CZ ↑ • ⊤⊥ ↓
    selinger-c14 :  ∀ {n} → (₃₊ n) QRel,  (⊤⊥ ↑ • CZ ↓) ^ 3 === ε
    selinger-c15 :  ∀ {n} → (₃₊ n) QRel,  (⊥⊤ ↓ • CZ ↑) ^ 3 === ε

    ----------------------------------------------------------------
    -- (G) Structural relations: kept verbatim.
    ----------------------------------------------------------------
    comm-H :     ∀ {n}{x} → (₂₊ n) QRel,  [ x ↥ ]ʷ • H === H • [ x ↥ ]ʷ
    comm-S :     ∀ {n}{x} → (₂₊ n) QRel,  [ x ↥ ]ʷ • S === S • [ x ↥ ]ʷ
    comm-CZ :    ∀ {n}{x} → (₃₊ n) QRel,  [ x ↥ ↥ ]ʷ • CZ === CZ • [ x ↥ ↥ ]ʷ

    cong↑ :      ∀ {n w v} →     n QRel,  w === v →
                              -------------------------
                              (₁₊ n) QRel,  w ↑ === v ↑
