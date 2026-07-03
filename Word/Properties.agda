------------------------------------------------------------------------
-- Presentations of groups
--
-- Properties of the free-monoid functor (wmap, wconcat, _*)
------------------------------------------------------------------------

{-# OPTIONS --safe #-}

open import Notations
module Word.Properties where

open import Relation.Binary.PropositionalEquality as Eq
  using (_≡_ ; _≗_)

open import Data.Nat using (ℕ ; suc ; zero)
open import Function using (_∘_ ; id)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Nullary using (yes ; no)

open import Word.Base

private
  variable
    A B C X Y Z : Set

------------------------------------------------------------------------
-- wmap / wconcat fusion laws

-- wmap distributes over composition.
wmap-∘ : {g : B → C} {f : A → B} → wmap (g ∘ f) ≗ wmap g ∘ wmap f
wmap-∘ {g = g} {f = f} [ x ]ʷ     = Eq.refl
wmap-∘ {g = g} {f = f} ε           = Eq.refl
wmap-∘ {g = g} {f = f} (w • w₁)   = Eq.cong₂ _•_ (wmap-∘ w) (wmap-∘ w₁)

-- wconcat ∘ wmap [_]ʷ is the identity.
wconcatmap-[-]ʷ : (wconcat {A = A} ∘ wmap [_]ʷ) ≗ id
wconcatmap-[-]ʷ [ x ]ʷ   = Eq.refl
wconcatmap-[-]ʷ ε         = Eq.refl
wconcatmap-[-]ʷ (w • w₁) rewrite wconcatmap-[-]ʷ w | wconcatmap-[-]ʷ w₁ = Eq.refl

-- wconcatmap with a singleton-wrapped function equals wmap.
wconcatmap-[f]ʷ : {f : A → B} → (wconcat ∘ wmap ([_]ʷ ∘ f)) ≗ wmap f
wconcatmap-[f]ʷ {f = f} [ x ]ʷ    = Eq.refl
wconcatmap-[f]ʷ {f = f} ε          = Eq.refl
wconcatmap-[f]ʷ {f = f} (ws • ws₁) = Eq.cong₂ _•_ (wconcatmap-[f]ʷ ws) (wconcatmap-[f]ʷ ws₁)

-- wconcat commutes with wmap of wmap.
wconcat-wmap : {f : A → B} → wconcat ∘ (wmap (wmap f)) ≗ wmap f ∘ wconcat
wconcat-wmap {f = f} [ ws ]ʷ    = Eq.refl
wconcat-wmap {f = f} ε           = Eq.refl
wconcat-wmap {f = f} (ws • ws₁) = Eq.cong₂ _•_ (wconcat-wmap ws) (wconcat-wmap ws₁)

-- _* distributes over word powers.
lemma-f*-w^n : {f : A → Word B} {w : Word A} (n : ℕ) →
               wconcatmap f (w ^ n) ≡ wconcatmap f w ^ n
lemma-f*-w^n {f = f} {w = w} zero        = Eq.refl
lemma-f*-w^n {f = f} {w = w} (₁₊ zero)  = Eq.refl
lemma-f*-w^n {f = f} {w = w} (₂₊ n) =
  Eq.cong₂ _•_ Eq.refl (lemma-f*-w^n (₁₊ n))

------------------------------------------------------------------------
-- Decidable equality

-- If B has decidable equality, so does Word B.
≡-dec : DecidableEquality B → DecidableEquality (Word B)
≡-dec deceqB [ x ]ʷ [ x₁ ]ʷ with deceqB x x₁
... | yes p = yes (Eq.cong [_]ʷ p)
... | no np = no (λ { Eq.refl → np Eq.refl })
≡-dec deceqB [ x ]ʷ ε             = no (λ { () })
≡-dec deceqB [ x ]ʷ (y • y₁)     = no (λ { () })
≡-dec deceqB ε      [ x ]ʷ       = no (λ { () })
≡-dec deceqB ε      ε             = yes Eq.refl
≡-dec deceqB ε      (y • y₁)     = no (λ { () })
≡-dec deceqB (x • x₁) [ x₂ ]ʷ  = no (λ { () })
≡-dec deceqB (x • x₁) ε          = no (λ { () })
≡-dec deceqB (x • x₁) (y • y₁)
  with ≡-dec deceqB x y | ≡-dec deceqB x₁ y₁
... | yes p  | yes p' = yes (Eq.cong₂ _•_ p p')
... | yes p  | no np' = no (λ { Eq.refl → np' Eq.refl })
... | no np  | _      = no (λ { Eq.refl → np  Eq.refl })

------------------------------------------------------------------------
-- Compatibility aliases

-- Alias for wconcatmap-[f]ʷ.
lemma-* : {f : A → B} → (w : Word A) → wconcatmap ([_]ʷ ∘ f) w ≡ wmap f w
lemma-* = wconcatmap-[f]ʷ

lemma-*-∘ : (f : A → Word B) → (g : B → C) → (w : Word A) →
            wconcatmap (wmap g ∘ f) w ≡ (wmap g ∘ wconcatmap f) w
lemma-*-∘ f g [ x ]ʷ    = Eq.refl
lemma-*-∘ f g ε           = Eq.refl
lemma-*-∘ f g (w • w₁)  = Eq.cong₂ _•_ (lemma-*-∘ f g w) (lemma-*-∘ f g w₁)

lemma-*-∘-∘ : (g : Z → A) → (h : Y → Z) → (w : Word Y) →
              wconcatmap ([_]ʷ ∘ g ∘ h) w ≡ wmap g (wconcatmap ([_]ʷ ∘ h) w)
lemma-*-∘-∘ g h w =
  Eq.trans (wconcatmap-[f]ʷ w)
    (Eq.trans (wmap-∘ w)
      (Eq.cong (wmap g) (Eq.sym (wconcatmap-[f]ʷ w))))
