{-# OPTIONS  --safe #-}
open import Level using (0ℓ)
open import Relation.Binary using (IsEquivalence ; Setoid ; Rel)
open import Data.Product using (_,_)
open import Relation.Binary.Morphism.Definitions using (Homomorphic₂)
open import Relation.Binary.PropositionalEquality using (_≡_)
import Relation.Binary.PropositionalEquality as Eq
import Relation.Binary.Reasoning.Setoid as SR

open import Word.Base

module Presentation.GroupLike where

import Presentation.Base as PB
import Presentation.Properties as PP

open import Relation.Binary.Definitions using (DecidableEquality ; Decidable)
open import Relation.Binary.Morphism.Structures using (IsRelMonomorphism)
open import Relation.Binary.PropositionalEquality using (_≡_ ; setoid)
import Relation.Binary.PropositionalEquality as Eq
open import Relation.Nullary.Decidable using (via-injection)
open import Function.Definitions using (Injective)
open import Function.Bundles using (Injection)
open import Function using (_∘_)
open import Data.Nat using (ℕ ; zero ; suc)
import Relation.Binary.Reasoning.Setoid as Eqv
open import Data.Product.Relation.Binary.Pointwise.NonDependent as PW

open import Data.Product using (_×_ ; proj₁ ; proj₂ ; ∃)
open import Data.List using (_++_ ; [] ; _∷_ ; List)

open import Algebra.Bundles using (Monoid ; Group)
open import Algebra.Morphism.Structures using (module MonoidMorphisms ; module GroupMorphisms)

-- ----------------------------------------------------------------------
-- ** Basic lemmas about groups

-- A context is group-like if it provides a left inverse to every
-- generator.
Grouplike : {Y : Set} -> (Γ : WRel Y) -> Set
Grouplike {Y} Γ = ∀ (x : Y) -> ∃ λ (x' : Word Y) -> let open PB Γ renaming (_≈_ to _≈₁_) in x' • [ x ]ʷ ≈₁ ε

-- We take Y and Γ to be fixed throughout the following lemmas, and we
-- assume Γ is group-like.
module Group-Lemmas
       (Y : Set)
       (Γ : WRel Y)
       (group-like : Grouplike Γ)
  where

  infix 8 _⁻¹

  open PP Γ
  open PB Γ
  open SR word-setoid


  -- The inverse of a word.
  _⁻¹ : Word Y -> Word Y
  [ x ]ʷ ⁻¹ = proj₁ (group-like x)
  ε ⁻¹ = ε
  (u • v) ⁻¹ = v ⁻¹ • u ⁻¹

  -- g ⁻¹ is a left inverse.
  lemma-left-inverse : {g : Word Y} -> g ⁻¹ • g ≈ ε
  lemma-left-inverse {[ x ]ʷ} = proj₂ (group-like x)
  lemma-left-inverse {ε} = left-unit
  lemma-left-inverse {u • v} =
         begin (v ⁻¹ • u ⁻¹) • (u • v)
                 ≈⟨ assoc ⟩
              v ⁻¹ • (u ⁻¹ • (u • v))
                 ≈⟨ cright assoc reversed ⟩
              v ⁻¹ • ((u ⁻¹ • u) • v)
                 ≈⟨ cright cleft lemma-left-inverse ⟩
              v ⁻¹ • ε • v
                 ≈⟨ cright left-unit ⟩
              v ⁻¹ • v
                 ≈⟨ lemma-left-inverse ⟩
              ε ∎

  -- g ⁻¹ is a right inverse.
  lemma-right-inverse : {g : Word Y} -> g • g ⁻¹ ≈ ε
  lemma-right-inverse {g} = 
    begin g • (g ⁻¹)
            ≈⟨ left-unit reversed ⟩
         ε • (g • (g ⁻¹))
            ≈⟨ cleft lemma-left-inverse reversed ⟩
         ((g ⁻¹) ⁻¹ • g ⁻¹) • (g • (g ⁻¹))
            ≈⟨ assoc ⟩
         (g ⁻¹) ⁻¹ • (g ⁻¹ • (g • (g ⁻¹)))
            ≈⟨ cright assoc reversed ⟩
         (g ⁻¹) ⁻¹ • ((g ⁻¹ • g) • g ⁻¹)
            ≈⟨ cright cleft lemma-left-inverse ⟩
         (g ⁻¹) ⁻¹ • (ε • g ⁻¹)
            ≈⟨ cright left-unit ⟩
         (g ⁻¹) ⁻¹ • g ⁻¹
            ≈⟨ lemma-left-inverse ⟩
         ε ∎
  
  -- Left cancellation.
  lemma-left-cancel : {g h h' : Word Y} -> g • h ≈ g • h' -> h ≈ h'
  lemma-left-cancel {g} {h} {h'} p = 
    begin h
               ≈⟨ left-unit reversed ⟩
         ε • h
               ≈⟨ cleft lemma-left-inverse reversed ⟩
         (g ⁻¹ • g) • h
               ≈⟨ assoc ⟩
         g ⁻¹ • (g • h)
               ≈⟨ cright p ⟩
         g ⁻¹ • (g • h')
               ≈⟨ assoc reversed ⟩
         (g ⁻¹ • g) • h'
               ≈⟨ cleft lemma-left-inverse ⟩
         ε • h'
               ≈⟨ left-unit ⟩
         h' ∎
  
  -- Right cancellation.
  lemma-right-cancel : {g g' h : Word Y} -> g • h ≈ g' • h -> g ≈ g'
  lemma-right-cancel {g} {g'} {h} p = 
    begin g
               ≈⟨ right-unit reversed ⟩
         g • ε
               ≈⟨ cright lemma-right-inverse reversed ⟩
         g • (h • h ⁻¹)
               ≈⟨ assoc reversed ⟩
         (g • h) • h ⁻¹
               ≈⟨ cleft p ⟩
         (g' • h) • h ⁻¹
               ≈⟨ assoc ⟩
         g' • (h • h ⁻¹)
               ≈⟨ cright lemma-right-inverse ⟩
         g' • ε
               ≈⟨ right-unit ⟩
         g' ∎
  
  -- Left inverses are unique.
  lemma-left-inverse-unique : {g h : Word Y} -> h • g ≈ ε -> h ≈ g ⁻¹
  lemma-left-inverse-unique {g} {h} p = 
    begin h
               ≈⟨ right-unit reversed ⟩
         h • ε
               ≈⟨ cright lemma-right-inverse reversed ⟩
         h • (g • g ⁻¹)
               ≈⟨ assoc reversed ⟩
         (h • g) • g ⁻¹
               ≈⟨ cleft p ⟩
         ε • g ⁻¹
               ≈⟨ left-unit ⟩
         g ⁻¹ ∎
  
  -- Right inverses are unique.
  lemma-right-inverse-unique : {g h : Word Y} -> g • h ≈ ε -> h ≈ g ⁻¹
  lemma-right-inverse-unique {g} {h} p = 
    begin h
               ≈⟨ left-unit reversed ⟩
         ε • h
               ≈⟨ cleft lemma-left-inverse reversed ⟩
         (g ⁻¹ • g) • h
               ≈⟨ assoc ⟩
         g ⁻¹ • (g • h)
               ≈⟨ cright p ⟩
         g ⁻¹ • ε
               ≈⟨ right-unit ⟩
         g ⁻¹ ∎

  -- Congruence for inverses.
  lemma-cong-inv : {g h : Word Y} -> g ≈ h -> g ⁻¹ ≈ h ⁻¹
  lemma-cong-inv {g} {h} p = lemma-right-inverse-unique claim
     where
       claim : h • g ⁻¹ ≈ ε
       claim = begin h • g ⁻¹
                       ≈⟨ cleft p reversed ⟩
                    g • g ⁻¹
                       ≈⟨ lemma-right-inverse ⟩
                    ε ∎

  -- The inverse is involutive.
  lemma-inverse-involutive : {g : Word Y} -> (g ⁻¹) ⁻¹ ≈ g
  lemma-inverse-involutive {g} = lemma-right-inverse-unique lemma-left-inverse reversed
  
  -- The inverse of ε.
  lemma-unit-inverse : ε ⁻¹ ≈ ε
  lemma-unit-inverse = refl
  
  -- The inverse of a product.
  lemma-product-inverse : ∀ {g h : Word Y} -> (g • h) ⁻¹ ≈ h ⁻¹ • g ⁻¹
  lemma-product-inverse = refl

  -- To show two words are equal, it is sufficient to show their
  -- inverses are equal.
  lemma-rule-inverse : ∀ {u v : Word Y} -> u ⁻¹ ≈ v ⁻¹ -> u ≈ v
  lemma-rule-inverse {u} {v} hyp =
         begin u
                 ≈⟨ right-unit reversed ⟩
              u • ε
                 ≈⟨ cright (lemma-left-inverse reversed) ⟩
              u • (v ⁻¹ • v)
                 ≈⟨ assoc reversed ⟩
              (u • v ⁻¹) • v
                 ≈⟨ cleft (cright (hyp reversed)) ⟩
              (u • u ⁻¹) • v
                 ≈⟨ cleft lemma-right-inverse ⟩
              ε • v
                 ≈⟨ left-unit ⟩
              v ∎

  -- Commutativity of inverses. (Note: commutativity is the special
  -- case where v = v' and w = w')
  lemma-comm-inv : ∀ {v v' w w'} -> v • w ≈ w' • v' -> v' • w ⁻¹ ≈ w' ⁻¹ • v
  lemma-comm-inv {v} {v'} {w} {w'} hyp =
      begin v' • w ⁻¹
              ≈⟨ left-unit reversed ⟩
           ε • (v' • w ⁻¹)
              ≈⟨ cleft lemma-left-inverse reversed ⟩
           (w' ⁻¹ • w') • (v' • w ⁻¹)
              ≈⟨ assoc ⟩
           w' ⁻¹ • (w' • (v' • w ⁻¹))
              ≈⟨ cright assoc reversed ⟩
           w' ⁻¹ • (w' • v') • w ⁻¹
              ≈⟨ cright cleft hyp reversed ⟩
           w' ⁻¹ • (v • w) • w ⁻¹
              ≈⟨ cright assoc ⟩
           w' ⁻¹ • v • (w • w ⁻¹)
              ≈⟨ assoc reversed ⟩
           (w' ⁻¹ • v) • (w • w ⁻¹)
              ≈⟨ cright lemma-right-inverse ⟩
           (w' ⁻¹ • v) • ε
              ≈⟨ right-unit ⟩
           w' ⁻¹ • v ∎

  -- Any equation can be reduced to a one-sided equation.
  lemma-one-sided : ∀ {w u} -> w • u ⁻¹ ≈ ε -> w ≈ u
  lemma-one-sided {w} {u} hyp =
      begin w
              ≈⟨ right-unit reversed ⟩
           w • ε
              ≈⟨ cright lemma-left-inverse reversed ⟩
           w • (u ⁻¹ • u)
              ≈⟨ assoc reversed ⟩
           (w • u ⁻¹) • u
              ≈⟨ cleft hyp ⟩
           ε • u
              ≈⟨ left-unit ⟩
           u ∎
          
  •-ε-group : Group 0ℓ 0ℓ
  •-ε-group = record
               { Carrier = Word Y ; _≈_ = _≈_ ; _∙_ = _•_ ; ε = ε ; _⁻¹ = _⁻¹ ;
               isGroup = record { isMonoid = •-ε-isMonoid ;
               inverse = (λ x → lemma-left-inverse) , (λ x → lemma-right-inverse) ; ⁻¹-cong = lemma-cong-inv } }

module Basis-Change
       (Y : Set)
       (Γ : WRel Y)
       (group-like : Grouplike Γ)
  where

  open PB Γ
  open PP Γ
  
  open Group-Lemmas Y Γ group-like
  open SR word-setoid
  
  by-basis-change : ∀ {u v} b c d e -> d • b ≈ ε -> c • e ≈ ε -> b • u • c ≈ b • v • c -> u ≈ v
  by-basis-change {u} {v} b c d e h1 h2 eq = begin
    u ≈⟨ sym (trans left-unit right-unit) ⟩
    ε • u • ε ≈⟨ cong (sym h1) (cong refl (sym h2)) ⟩
    (d • b) • u • (c • e) ≈⟨ special-assoc (□ ^ 2 • □ • □ ^ 2) (□ • □ ^ 3 • □) Eq.refl ⟩
    d • (b • u • c) • e ≈⟨ cong refl (cong eq refl) ⟩
    d • (b • v • c) • e ≈⟨ special-assoc  (□ • □ ^ 3 • □) (□ ^ 2 • □ • □ ^ 2) Eq.refl ⟩
    (d • b) • v • (c • e) ≈⟨ cong h1 (cong refl h2) ⟩
    ε • v • ε ≈⟨ trans left-unit right-unit ⟩
    v ∎
    where

    open Pattern-Assoc

  bbc : ∀ {u v} b c -> b • u • c ≈ b • v • c -> u ≈ v
  bbc {u} {v} b c eq = by-basis-change b c (b ⁻¹) (c ⁻¹) lemma-left-inverse lemma-right-inverse eq

  bbc-and : ∀ {u v x y} b c -> b • u • c ≈ x ->  b • v • c ≈ y -> u ≈ v -> x ≈ y
  bbc-and {u} {v} {x} {y} b c equ eqv uv = begin
    x ≈⟨ sym equ ⟩
    b • u • c ≈⟨ cong refl (cong uv refl) ⟩
    b • v • c ≈⟨ eqv ⟩
    y ∎
    
    

word-act : ∀ {C Y : Set} (act1 : Y -> C -> C) -> Word Y -> C -> C
word-act {C} {Y} act1 [ x ]ʷ c = act1 x c
word-act {C} {Y} act1 ε c = c
word-act {C} {Y} act1 (w • w₁) c = word-act act1 w (word-act act1 w₁ c)

module Group-Action
       (C Y : Set)
       (Γ : WRel Y)
       (group-like : Grouplike Γ)
       (act1 : Y -> C -> C)
       (let act = word-act act1)
       (let open PB Γ)
       (hyp : ∀ {w v} -> Γ w v -> ∀ c -> act w c ≡ act v c )
  where

  open PP Γ
  
  open Group-Lemmas Y Γ group-like
  open SR word-setoid

  act-cong : ∀ w v c -> w ≈ v -> act w c ≡ act v c
  act-cong w v c PB.refl = Eq.refl
  act-cong w v c (PB.sym eq) = Eq.sym (act-cong v w c eq)
  act-cong w v c (PB.trans eq eq₁) = Eq.trans (act-cong _ _ c eq) (act-cong _ _ c eq₁)
  act-cong w v c (PB.cong {w'} {w''} {v'} {v''} eq eq₁) rewrite act-cong _ _ c eq₁ = act-cong _ _ (word-act act1 v'' c) eq
  act-cong w v c PB.assoc = Eq.refl
  act-cong w v c PB.left-unit = Eq.refl
  act-cong w v c PB.right-unit = Eq.refl
  act-cong w v c (PB.axiom x) = hyp x c
