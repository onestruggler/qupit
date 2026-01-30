{-# OPTIONS  --safe #-}
open import Relation.Binary using (Rel ; REL)

open import Level using (0ℓ)
open import Data.Product using (_,_ ; _×_ ; map ; proj₁ ; proj₂ ; Σ ; ∃ ; ∃-syntax)
import Data.Product.Relation.Binary.Pointwise.NonDependent as PW
open import Data.Sum using (_⊎_ ; inj₁ ; inj₂)
open import Data.Nat using (ℕ ; zero ; suc)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤ ; tt)
open import Function using (_∘_ ; _∘₂_)
open import Relation.Binary.PropositionalEquality using (_≡_ ; inspect ; setoid ; module ≡-Reasoning) renaming ([_] to [_]')
import Relation.Binary.PropositionalEquality as Eq

import Relation.Binary.Reasoning.Setoid as SR

open import Word.Base
open import Word.Properties
open import Presentation.Base
open import Presentation.Reidemeister-Schreier

import Presentation.Base as PB
import Presentation.Properties as PP


module Presentation.Construct.Base where

WREL : Set -> Set -> Set₁
WREL X Y = REL (Word X) (Word Y) 0ℓ

[_]ₗ : ∀ {A B} -> Word A -> Word (A ⊎ B)
[_]ₗ {A} {B} = wmap inj₁

[_]ᵣ : ∀ {A B} -> Word B -> Word (A ⊎ B)
[_]ᵣ {A} {B} = wmap inj₂


infix 5 _⸲_⸲_
infixr 5 _∪_

data _⸲_⸲_ {A B} (Γ₁ : WRel A) (Γ₂ : WRel B) (Γ₃ : WRel (A ⊎ B)) : WRel (A ⊎ B) where
 left : ∀ {u v} -> Γ₁ u v -> (Γ₁ ⸲ Γ₂ ⸲ Γ₃) [ u ]ₗ [ v ]ₗ
 right : ∀ {u v} -> Γ₂ u v -> (Γ₁ ⸲ Γ₂ ⸲ Γ₃) [ u ]ᵣ [ v ]ᵣ
 mid : ∀ {u v} -> Γ₃ u v -> (Γ₁ ⸲ Γ₂ ⸲ Γ₃) u v

data _∪_ {A} (Γ₁ Γ₂ : WRel A) : WRel A where
 left : ∀ {u v} -> Γ₁ u v -> (Γ₁ ∪ Γ₂) u v
 right : ∀ {u v} -> Γ₂ u v -> (Γ₁ ∪ Γ₂) u v


-- Empty rel.
data Γₑ {A} : WRel A where 

-- Coarsest rel.
data Γᵤ {A} : WRel A where
  alleq : ∀ {w} -> Γᵤ {A} w ε

-- Comm rel
data Γₓ {A B} : WRel (A ⊎ B) where
  comm : (a : A) (b : B) -> Γₓ ([ [ a ]ʷ ]ₗ • [ [ b ]ʷ ]ᵣ) ([ [ b ]ʷ ]ᵣ • [ [ a ]ʷ ]ₗ)

-- Semi comm rel.
data Γⱼ {N H} (conj : H -> N -> N) : WRel (N ⊎ H) where
  comm : (n : N) (h : H) -> Γⱼ conj ([ [ h ]ʷ ]ᵣ • [ [ n ]ʷ ]ₗ) ([ [ conj h n ]ʷ ]ₗ • [ [ h ]ʷ ]ᵣ)

-- Semi comm rel.
data Γⱼ' {N H} (conj : H -> N -> Word N) : WRel (N ⊎ H) where
  comm : (n : N) (h : H) -> Γⱼ' conj ([ [ h ]ʷ ]ᵣ • [ [ n ]ʷ ]ₗ) ([ conj h n ]ₗ • [ [ h ]ʷ ]ᵣ)

-- Amalgamation rel.
data Γₐ {M A B : Set} (f₁ : M -> Word A) (f₂ : M -> Word B) : WRel (A ⊎ B) where
  amal : ∀ {m} -> Γₐ f₁ f₂ [ (f₁ m) ]ₗ [ (f₂ m) ]ᵣ

-- Sugar relation. The new added generating set M desuars to Word A.
data Γₛ {M A} (f : M -> Word A) : WRel (M ⊎ A) where
  desugar : ∀ {m} -> Γₛ f [ inj₁ m ]ʷ [ f m ]ᵣ 

-- Free product.
infix 4 _*_
_*_ : {A B : Set} -> WRel A -> WRel B -> WRel (A ⊎ B)
_*_  Γ Δ = Γ ⸲ Δ ⸲ Γₑ

-- Direct product.
infix 4 _⊕_
_⊕_ : {A B : Set} -> WRel A -> WRel B -> WRel (A ⊎ B)
_⊕_  Γ Δ = Γ ⸲ Δ ⸲ Γₓ

-- n time union
infix 4 _⊎^_
_⊎^_ : Set -> ℕ -> Set
_⊎^_ A zero = ⊥
_⊎^_ A (suc zero) = A
_⊎^_ A (suc (suc n)) = A ⊎ (A ⊎^ (suc n))

-- n time direct product.
infix 4 _⊕^_
_⊕^_ : {A : Set} -> WRel A -> (n : ℕ) -> WRel (A ⊎^ n)
_⊕^_ {A} Γ zero = Γₑ
_⊕^_ {A} Γ (suc zero) = Γ
_⊕^_ {A} Γ (suc (suc n)) = Γ ⸲ Γ ⊕^ (suc n) ⸲ Γₓ 


-- Semi-direct product.
infix 4 _⋊_⋆_
_⋊_⋆_ : {N H : Set} -> WRel N -> WRel H -> (conj : H -> N -> N) -> WRel (N ⊎ H)
_⋊_⋆_  Γ Δ conj = Γ ⸲ Δ ⸲ Γⱼ conj

-- Amalgamated product.
infix 4 _*_⋆_⋆_
_*_⋆_⋆_ : {M A B : Set} -> WRel A -> WRel B -> (f₁ : M -> Word A) -> (f₂ : M -> Word B) -> WRel (A ⊎ B)
_*_⋆_⋆_  Γ Δ f₁ f₂ = Γ ⸲ Δ ⸲ Γₐ f₁ f₂


module LeftRightCongruence
  {A B : Set}
  (Γ : WRel A)
  (Δ : WRel B)
  (Λ : WRel (A ⊎ B))
  where

  open PB Γ renaming (_===_ to _===₁_ ; _≈_ to _≈₁_)
  open PB Δ renaming (_===_ to _===₂_ ; _≈_ to _≈₂_)
  open PB {A ⊎ B} (Γ ⸲ Δ ⸲ Λ) renaming (_===_ to _===₃_ ; _≈_ to _≈₃_)

  lefts :  ∀ {u v} -> u ≈₁ v -> [ u ]ₗ ≈₃ [ v ]ₗ
  lefts {u} {v} refl = _≈₃_.refl
  lefts {u} {v} (sym h) = _≈₃_.sym (lefts h)
  lefts {u} {v} (trans h h₁) = _≈₃_.trans (lefts h) (lefts h₁)
  lefts {u} {v} (cong h h₁) = _≈₃_.cong (lefts h) (lefts h₁)
  lefts {u} {v} assoc = _≈₃_.assoc
  lefts {u} {v} left-unit = _≈₃_.left-unit
  lefts {u} {v} right-unit = _≈₃_.right-unit
  lefts {u} {v} (axiom x) = _≈₃_.axiom (left x)

  rights :  ∀ {u v} -> u ≈₂ v -> [ u ]ᵣ ≈₃ [ v ]ᵣ
  rights {u} {v} refl = _≈₃_.refl
  rights {u} {v} (sym h) = _≈₃_.sym (rights h)
  rights {u} {v} (trans h h₁) = _≈₃_.trans (rights h) (rights h₁)
  rights {u} {v} (cong h h₁) = _≈₃_.cong (rights h) (rights h₁)
  rights {u} {v} assoc = _≈₃_.assoc
  rights {u} {v} left-unit = _≈₃_.left-unit
  rights {u} {v} right-unit = _≈₃_.right-unit
  rights {u} {v} (axiom x) = _≈₃_.axiom (right x)



module LeftRightCongruence-∪
  {A : Set}
  (Γ : WRel A)
  (Δ : WRel A)
  where

  open PB Γ renaming (_===_ to _===₁_ ; _≈_ to _≈₁_)
  open PB Δ renaming (_===_ to _===₂_ ; _≈_ to _≈₂_)
  open PB (Γ ∪ Δ) renaming (_===_ to _===₃_ ; _≈_ to _≈₃_)

  lefts :  ∀ {u v} -> u ≈₁ v -> u ≈₃ v
  lefts {u} {v} refl = _≈₃_.refl
  lefts {u} {v} (sym h) = _≈₃_.sym (lefts h)
  lefts {u} {v} (trans h h₁) = _≈₃_.trans (lefts h) (lefts h₁)
  lefts {u} {v} (cong h h₁) = _≈₃_.cong (lefts h) (lefts h₁)
  lefts {u} {v} assoc = _≈₃_.assoc
  lefts {u} {v} left-unit = _≈₃_.left-unit
  lefts {u} {v} right-unit = _≈₃_.right-unit
  lefts {u} {v} (axiom x) = _≈₃_.axiom (left x)

  rights :  ∀ {u v} -> u ≈₂ v -> u ≈₃ v
  rights {u} {v} refl = _≈₃_.refl
  rights {u} {v} (sym h) = _≈₃_.sym (rights h)
  rights {u} {v} (trans h h₁) = _≈₃_.trans (rights h) (rights h₁)
  rights {u} {v} (cong h h₁) = _≈₃_.cong (rights h) (rights h₁)
  rights {u} {v} assoc = _≈₃_.assoc
  rights {u} {v} left-unit = _≈₃_.left-unit
  rights {u} {v} right-unit = _≈₃_.right-unit
  rights {u} {v} (axiom x) = _≈₃_.axiom (right x)


anfpₗ : ∀ {A} {Γ Δ : WRel A} -> PP.NFProperty Γ -> PP.AlmostNFProperty (Γ ∪ Δ)
anfpₗ {A} {Γ} {Δ} nfp = record { ANF = NF ; anf = nf ; anf-injective = λ x → lefts (nf-injective x) }
  where
  open PP.NFProperty nfp
  open LeftRightCongruence-∪ Γ Δ

anfpₗ' : ∀ {A} {Γ Δ : WRel A} -> PP.AlmostNFProperty Γ -> PP.AlmostNFProperty (Γ ∪ Δ)
anfpₗ' {A} {Γ} {Δ} anfp = record { ANF = ANF ; anf = anf ; anf-injective = λ x → lefts (anf-injective x) }
  where
  open PP.AlmostNFProperty anfp
  open LeftRightCongruence-∪ Γ Δ

anfpᵣ : ∀ {A} {Γ Δ : WRel A} -> PP.NFProperty Δ -> PP.AlmostNFProperty (Γ ∪ Δ)
anfpᵣ {A} {Γ} {Δ} nfp = record { ANF = NF ; anf = nf ; anf-injective = λ x → rights (nf-injective x) }
  where
  open PP.NFProperty nfp
  open LeftRightCongruence-∪ Γ Δ

anfpᵣ' : ∀ {A} {Γ Δ : WRel A} -> PP.AlmostNFProperty Δ -> PP.AlmostNFProperty (Γ ∪ Δ)
anfpᵣ' {A} {Γ} {Δ} anfp = record { ANF = ANF ; anf = anf ; anf-injective = λ x → rights (anf-injective x) }
  where
  open PP.AlmostNFProperty anfp
  open LeftRightCongruence-∪ Γ Δ

open import Algebra.Morphism.Structures using (module MonoidMorphisms)
open import Algebra.Bundles using (Monoid)

mono-anfp : ∀ {A B} {Γ : WRel A} {Δ : WRel B} -> PP.AlmostNFProperty Δ -> (f : Word A -> Word B) ->
  let open PP Γ renaming (•-ε-monoid to m₁) in
  let open PP Δ renaming (•-ε-monoid to m₂) in
  MonoidMorphisms.IsMonoidMonomorphism (Monoid.rawMonoid m₁) ((Monoid.rawMonoid m₂)) f -> PP.AlmostNFProperty (Γ)
mono-anfp {A} {B} {Γ} {Δ} anfp f mono = record { ANF = ANF ; anf = anf ∘ f ; anf-injective = inj }
  where
  open PB Γ renaming (_≈_ to _≈₁_)
  open PB Δ renaming (_≈_ to _≈₂_)
  open PP.AlmostNFProperty anfp
  open MonoidMorphisms.IsMonoidMonomorphism mono renaming (injective to f-inj)
  inj : {w v : Word A} → anf (f w) ≡ anf (f v) → w ≈₁ v
  inj {w} {v} eq = f-inj (anf-injective eq)


mono-nfp : ∀ {A B} {Γ : WRel A} {Δ : WRel B} -> PP.NFProperty Δ -> (f : Word A -> Word B) ->
  let open PP Γ renaming (•-ε-monoid to m₁) in
  let open PP Δ renaming (•-ε-monoid to m₂) in
  MonoidMorphisms.IsMonoidMonomorphism (Monoid.rawMonoid m₁) ((Monoid.rawMonoid m₂)) f -> PP.NFProperty (Γ)
mono-nfp {A} {B} {Γ} {Δ} nfp f mono = record { NF = NF ; nf = nf ∘ f ; nf-cong = mycong ; nf-injective = inj }
  where
  open PB Γ renaming (_≈_ to _≈₁_)
  open PB Δ renaming (_≈_ to _≈₂_)
  open PP.NFProperty nfp
  open MonoidMorphisms.IsMonoidMonomorphism mono renaming (injective to f-inj)
  inj : {w v : Word A} → nf (f w) ≡ nf (f v) → w ≈₁ v
  inj {w} {v} eq = f-inj (nf-injective eq)

  mycong : {w v : Word A} → w ≈₁ v → nf (f w) ≡ nf (f v)
  mycong {w} {v} eq = nf-cong (⟦⟧-cong eq)

iso-nfp' : ∀ {A B} {Γ : WRel A} {Δ : WRel B} -> PP.NFProperty' Δ -> (f : Word A -> Word B) ->
  let open PP Γ renaming (•-ε-monoid to m₁) in
  let open PP Δ renaming (•-ε-monoid to m₂) in
  MonoidMorphisms.IsMonoidIsomorphism (Monoid.rawMonoid m₁) ((Monoid.rawMonoid m₂)) f -> PP.NFProperty' (Γ)
iso-nfp' {A} {B} {Γ} {Δ} nfp f iso = record
                                        { NF = NF ; nf = nf ∘ f ; nf-cong = mycong ; inv-nf = inv-f ∘ inv-nf ; inv-nf∘nf=id = =id }
  where
  open PB Γ renaming (_≈_ to _≈₁_ ; refl to refl₁)
  open PB Δ renaming (_≈_ to _≈₂_ ; trans to trans₂)
  open PP.NFProperty' nfp
  open MonoidMorphisms.IsMonoidIsomorphism iso renaming (injective to f-inj ; surjective to f-surj)
  inj : {w v : Word A} → nf (f w) ≡ nf (f v) → w ≈₁ v
  inj {w} {v} eq = f-inj (nf-injective eq)

  mycong : {w v : Word A} → w ≈₁ v → nf (f w) ≡ nf (f v)
  mycong {w} {v} eq = nf-cong (⟦⟧-cong eq)

  inv-f : Word B → Word A
  inv-f x with f-surj x
  ... | (y , _) = y

  lemma-f∘inv-f : ∀ {x} -> f (inv-f x) ≈₂ x
  lemma-f∘inv-f {x} with f-surj x
  ... | (y , p) = p refl₁
  
  =id : {w : Word A} → inv-f (inv-nf (nf (f w))) ≈₁ w
  =id {w} with f-surj (f w)
  ... | (y , p) = f-inj (trans₂ lemma-f∘inv-f inv-nf∘nf=id)
    where
    claim : inv-nf (nf (f w)) ≈₂ f w
    claim = inv-nf∘nf=id
