------------------------------------------------------------------------
-- Presentations of groups
--
-- Semantics of the symmetric group: bijections on Fin n via
-- Data.Fin.Permutation.Permutation′.
-- Also provides the group structure on Permutation′ n.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}

open import Data.Nat using (ℕ ; zero ; suc)
open import Data.Fin using (Fin ; zero ; suc)
open import Data.Fin.Permutation
  using ( Permutation′ ; permutation ; _⟨$⟩ʳ_ ; _⟨$⟩ˡ_ ; _∘ₚ_ ; flip
        ; lift₀ ; lift₀-id ; lift₀-comp
        ; inverseˡ ; inverseʳ )
  renaming (id to idP)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_ ; refl ; cong ; sym ; trans)

open import Data.Product.Base using (_,_ ; proj₁ ; proj₂)
open import Algebra.Structures using (IsMagma ; IsSemigroup ; IsMonoid ; IsGroup)
open import Algebra.Bundles using (Group)
open import Relation.Binary.Structures using (IsEquivalence)
import Function.Endo.Propositional as Endo

open import Word.Base
open import Notations

module Examples.Groups.Symmetric.Tight.Semantics where

open import Examples.Groups.Symmetric.Syntactics

------------------------------------------------------------------------
-- Permutation type

Perm : ℕ → Set
Perm n = Permutation′ n

------------------------------------------------------------------------
-- Semantic building blocks

-- The underlying function for swap01 (used to build the Permutation′).
private
  swap01-fun : ∀ {n} → Fin (₂₊ n) → Fin (₂₊ n)
  swap01-fun zero      = ₁₊ zero
  swap01-fun (₁₊ zero) = zero
  swap01-fun (₂₊ k)    = ₂₊ k

-- Swap positions 0 and 1: the denotation of σ-gate.
swap01 : ∀ {n} → Perm (₂₊ n)
swap01 = permutation swap01-fun swap01-fun
  (λ { zero → refl ; (₁₊ zero) → refl ; (₂₊ _) → refl })
  (λ { zero → refl ; (₁₊ zero) → refl ; (₂₊ _) → refl })

-- Shift a permutation up by one wire: the action of _↥.
shift : ∀ {n} → Perm n → Perm (₁₊ n)
shift = lift₀

------------------------------------------------------------------------
-- Denotation of generators and words

⟦_⟧ᵍ : ∀ {n} → Gen n → Perm n
⟦ gate₁ () ⟧ᵍ
⟦ gate₂ σ-gate ⟧ᵍ = swap01
⟦ g ↥ ⟧ᵍ          = shift ⟦ g ⟧ᵍ

-- Words are read left-to-right: w • v applies w first, then v.
⟦_⟧ : ∀ {n} → Word (Gen n) → Perm n
⟦ ε ⟧      = idP
⟦ [ g ]ʷ ⟧ = ⟦ g ⟧ᵍ
⟦ w • v ⟧  = ⟦ w ⟧ ∘ₚ ⟦ v ⟧

------------------------------------------------------------------------
-- Lemmas about shift (= lift₀)

-- ⟦ w ↑ ⟧ agrees with shift ⟦ w ⟧ pointwise.
⟦↑⟧ : ∀ {n} (w : Word (Gen n)) (k : Fin (₁₊ n))
     → ⟦ w ↑ ⟧ ⟨$⟩ʳ k ≡ shift ⟦ w ⟧ ⟨$⟩ʳ k
⟦↑⟧ ε       k = Eq.sym (lift₀-id k)
⟦↑⟧ [ g ]ʷ  k = refl
⟦↑⟧ (w • v) k =
  Eq.trans (Eq.cong (⟦ v ↑ ⟧ ⟨$⟩ʳ_) (⟦↑⟧ w k))
  (Eq.trans (⟦↑⟧ v _) (lift₀-comp ⟦ w ⟧ ⟦ v ⟧ k))

------------------------------------------------------------------------
-- Group structure on Permutation′ n

Permutation′-group : ∀ (n : ℕ) → Group _ _
Permutation′-group n = record
  { Carrier = Permutation′ n
  ; _≈_     = _≈_
  ; _∙_     = _∘ₚ_
  ; ε       = idP
  ; _⁻¹     = flip
  ; isGroup = perm-isGroup
  }
  where
  open import Data.Fin.Permutation using (_≈_)
  -- Pull the endomorphism-monoid laws for Fin n → Fin n (all proved by refl).
  open IsMonoid (Endo.∘-id-isMonoid (Fin n))
    using (assoc ; identity)

  -- _≈_ is an equivalence relation (pointwise _≡_)
  ≈-isEquiv : IsEquivalence (_≈_ {m = n} {n = n})
  ≈-isEquiv = record
    { refl  = λ _   → refl
    ; sym   = λ h i → sym (h i)
    ; trans = λ p q i → trans (p i) (q i)
    }

  -- _∘ₚ_ is congruent: if π₁ ≈ π₂ and ρ₁ ≈ ρ₂ then π₁ ∘ₚ ρ₁ ≈ π₂ ∘ₚ ρ₂.
  ∘ₚ-cong : ∀ {π₁ π₂ ρ₁ ρ₂ : Permutation′ n}
           → π₁ ≈ π₂ → ρ₁ ≈ ρ₂ → π₁ ∘ₚ ρ₁ ≈ π₂ ∘ₚ ρ₂
  ∘ₚ-cong {ρ₁ = ρ₁} h₁ h₂ i = trans (cong (ρ₁ ⟨$⟩ʳ_) (h₁ i)) (h₂ _)

  -- Associativity of _∘ₚ_ is pointwise associativity of _∘_.
  ∘ₚ-assoc : ∀ (π ρ σ : Permutation′ n) → (π ∘ₚ ρ) ∘ₚ σ ≈ π ∘ₚ (ρ ∘ₚ σ)
  ∘ₚ-assoc π ρ σ i =
    cong (λ f → f i) (assoc (σ ⟨$⟩ʳ_) (ρ ⟨$⟩ʳ_) (π ⟨$⟩ʳ_))

  ∘ₚ-identityˡ : ∀ (π : Permutation′ n) → idP ∘ₚ π ≈ π
  ∘ₚ-identityˡ π i =
    cong (λ f → f i) (proj₂ identity (π ⟨$⟩ʳ_))

  ∘ₚ-identityʳ : ∀ (π : Permutation′ n) → π ∘ₚ idP ≈ π
  ∘ₚ-identityʳ π i =
    cong (λ f → f i) (proj₁ identity (π ⟨$⟩ʳ_))

  flip-invˡ : ∀ (π : Permutation′ n) → flip π ∘ₚ π ≈ idP
  flip-invˡ π _ = inverseʳ π

  flip-invʳ : ∀ (π : Permutation′ n) → π ∘ₚ flip π ≈ idP
  flip-invʳ π _ = inverseˡ π

  flip-cong : ∀ {π ρ : Permutation′ n} → π ≈ ρ → flip π ≈ flip ρ
  flip-cong {π = π} {ρ = ρ} h i =
    ρ-inj (trans (trans (sym (h (π ⟨$⟩ˡ i))) (inverseʳ π)) (sym (inverseʳ ρ)))
    where
    ρ-inj : ∀ {a b} → ρ ⟨$⟩ʳ a ≡ ρ ⟨$⟩ʳ b → a ≡ b
    ρ-inj eq =
      trans (sym (inverseˡ ρ)) (trans (cong (ρ ⟨$⟩ˡ_) eq) (inverseˡ ρ))

  perm-isGroup : IsGroup _≈_ _∘ₚ_ idP flip
  perm-isGroup = record
    { isMonoid = record
      { isSemigroup = record
        { isMagma = record
          { isEquivalence = ≈-isEquiv
          ; ∙-cong        = λ {π₁} {π₂} {ρ₁} {ρ₂} h₁ h₂ → ∘ₚ-cong {π₁ = π₁} {π₂ = π₂} {ρ₁ = ρ₁} {ρ₂ = ρ₂} h₁ h₂
          }
        ; assoc = ∘ₚ-assoc
        }
      ; identity = ∘ₚ-identityˡ , ∘ₚ-identityʳ
      }
    ; inverse = flip-invˡ , flip-invʳ
    ; ⁻¹-cong = λ {π} {ρ} h → flip-cong {π = π} {ρ = ρ} h
    }
