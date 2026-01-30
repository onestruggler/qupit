open import Level using (0ℓ)

open import Relation.Binary using (IsEquivalence ; Setoid ; Rel)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Binary.PropositionalEquality using (_≡_)
import Relation.Binary.PropositionalEquality as Eq
open import Relation.Nullary.Decidable using (yes ; no)

open import Data.Product using (Σ ; _×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤ ; tt)


open import Word.Base
open import Word.Properties
import Presentation.Base as PB
import Presentation.Properties as PP
open PP using (NFProperty ; NFProperty')
open import Presentation.Construct.Base

module Presentation.Groups.Trivial where

module P1 where
  A = ⊥
  
  pres : WRel A
  pres = Γₑ

  open PB pres using (_≈_)
  open PP pres using (•-ε-monoid ; word-setoid)
  
  f : Word A -> ⊤
  f _ = tt

  f-cong : ∀ {a b} -> a ≈ b -> f a ≡ f b
  f-cong {a} {b} eq = Eq.refl

  open _≈_
  singleton : ∀ {a} -> a ≈ ε
  singleton {ε} = refl
  singleton {a • a₁} with singleton {a} | singleton {a₁}
  ... | ih1 | ih2 = trans (cong ih1 ih2) left-unit

  open import Relation.Binary.Reasoning.Setoid word-setoid

  f-inj :  ∀ {a b} -> f a ≡ f b -> a ≈ b
  f-inj {a} {b} eq = begin
    a ≈⟨ singleton ⟩
    ε ≈⟨ sym singleton ⟩
    b ∎
  
  nfp : NFProperty Γₑ
  nfp = record { NF = ⊤ ; nf = f ; nf-cong = λ {w} {v} z → Eq.refl ; nf-injective = f-inj }
 
  nfp' : NFProperty' Γₑ
  nfp' = record
           { NF = ⊤ ; nf = f ; nf-cong = λ {w} {v} z → Eq.refl ; inv-nf = λ z → ε ; inv-nf∘nf=id = λ {w} → sym singleton }


module P2 (A : Set) where

  pres : WRel A
  pres = Γᵤ

  open PB pres using (_≈_)
  open PP pres using (•-ε-monoid ; word-setoid)
  
  f : Word A -> ⊤
  f _ = tt

  f-cong : ∀ {a b} -> a ≈ b -> f a ≡ f b
  f-cong {a} {b} eq = Eq.refl

  open _≈_
  singleton : ∀ {a} -> a ≈ ε
  singleton {ε} = refl
  singleton {[ x ]ʷ} = axiom alleq
  singleton {a • a₁} with singleton {a} | singleton {a₁}
  ... | ih1 | ih2 = trans (cong ih1 ih2) left-unit

  open import Relation.Binary.Reasoning.Setoid word-setoid

  f-inj :  ∀ {a b} -> f a ≡ f b -> a ≈ b
  f-inj {a} {b} eq = begin
    a ≈⟨ singleton ⟩
    ε ≈⟨ sym singleton ⟩
    b ∎

  nfp : NFProperty Γᵤ
  nfp = record { NF = ⊤ ; nf = f ; nf-cong = λ {w} {v} z → Eq.refl ; nf-injective = f-inj }

  nfp' : NFProperty' Γᵤ
  nfp' = record
           { NF = ⊤ ; nf = f ; nf-cong = λ {w} {v} z → Eq.refl ; inv-nf = λ z → ε ; inv-nf∘nf=id = λ {w} → sym singleton }



module P1IsoP2 (B : Set) where
  open import Algebra.Bundles using (Monoid)
  open import Presentation.Morphism
  open import Algebra.Morphism.Structures using (module MonoidMorphisms)

  A = ⊥

  open PB (Γₑ {A}) renaming (_===_ to _===₁_ ; _≈_ to _≈₁_) using ()
  open PB (Γᵤ {B}) renaming (_===_ to _===₂_ ; _≈_ to _≈₂_) using ()
  open PP (Γₑ {A}) renaming (•-ε-monoid to m₁)
  open PP (Γᵤ {B}) renaming (•-ε-monoid to m₂)

  f : A -> Word B
  f ()

  g : B -> Word A
  g _ = ε

  f-well-defined : ∀ {w v} -> w ===₁ v -> (f *) w ≈₂ (f *) v
  f-well-defined {w} {v} eq = _≈₂_.trans (_≈₂_.axiom alleq) (_≈₂_.sym (_≈₂_.axiom alleq))
  
  f-left-inv-gen : ∀ (x : B) -> [ x ]ʷ ≈₂ (f *) (g x)
  f-left-inv-gen x = _≈₂_.axiom alleq
  
  g-well-defined : ∀ {u t : Word B} -> u ===₂ t -> (g *) u ≈₁ (g *) t
  g-well-defined {[ x ]ʷ} {t} alleq = _≈₁_.refl
  g-well-defined {ε} {t} alleq = _≈₁_.refl
  g-well-defined {u • u₁} {t} alleq = _≈₁_.trans (_≈₁_.cong (g-well-defined {u = u} alleq) (g-well-defined {u = u₁} alleq)) _≈₁_.left-unit
  
  g-left-inv-gen : ∀ (x : A) -> [ x ]ʷ ≈₁ (g *) (f x)
  g-left-inv-gen ()
  
  module Iso = StarIsomorphism (Γₑ {A}) (Γᵤ {B}) f g f-well-defined f-left-inv-gen g-well-defined g-left-inv-gen

  iso : MonoidMorphisms.IsMonoidIsomorphism (Monoid.rawMonoid m₁) (Monoid.rawMonoid m₂) (f *)
  iso = Iso.isMonoidIsomorphism
