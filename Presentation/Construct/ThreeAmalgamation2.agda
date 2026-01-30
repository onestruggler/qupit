open import Relation.Binary using (Rel ; REL)

open import Level using (0ℓ)
open import Data.Product using (_,_ ; _×_ ; map ; proj₁ ; proj₂ ; Σ ; ∃ ; ∃-syntax)
import Data.Product.Relation.Binary.Pointwise.NonDependent as PW
open import Data.Sum using (_⊎_ ; inj₁ ; inj₂ ; assocʳ ; assocˡ)
open import Data.Nat using (ℕ ; zero ; suc)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤ ; tt)
open import Function using (_∘_ ; _∘₂_ ; id)
open import Relation.Binary.PropositionalEquality using (_≡_ ; inspect ; setoid ; module ≡-Reasoning) renaming ([_] to [_]')
import Relation.Binary.PropositionalEquality as Eq

import Relation.Binary.Reasoning.Setoid as SR

open import Word.Base
open import Word.Properties
open import Presentation.Base
open import Presentation.Reidemeister-Schreier

open import Presentation.Construct.Base
open import Presentation.Construct.Properties.Amalgamation
open import Presentation.Morphism as Morphism
open import Presentation.MorphismId as MorphismId

import Presentation.Base as PB
import Presentation.Properties as PP

open import Algebra.Morphism.Structures using (module MonoidMorphisms)
open import Algebra.Bundles using (Monoid)


import Presentation.Construct.ThreeAmalgamation as TA
module Presentation.Construct.ThreeAmalgamation2
  {X Y Z : Set}
  (Γ₁ : WRel (X ⊎ Y))
  (Γ₂ : WRel (X ⊎ Z))
  (Γ₃ : WRel (Y ⊎ Z))
  where
open TA Γ₁ Γ₂ Γ₃


open import Presentation.CosetNF

module ANFP₁
  (rz : WRel Z)
  (nfp-rz : PP.NFProperty rz)
  (C₁ : Set)
  (h₁ : C₁ ⊎ ⊤ → X ⊎ Z → Word Z × (C₁ ⊎ ⊤))
  ([_]ₒ₁ : C₁ → Word (X ⊎ Z))
  (hcme₁ : (c : C₁) (m : Z) → ∃ (λ w → ∃ (λ c' → h₁ (inj₁ c) (inj₂ m) ≡ (w , inj₁ c'))))
  (htme₁ : (m : Z) → h₁ (inj₂ tt) (inj₂ m) ≡ ([ m ]ʷ , inj₂ tt))
  (htme~₁ : (m : Z) → PW.Pointwise (_≈_ rz) _≡_ ([ m ]ʷ , inj₂ tt)  (h₁ (inj₂ tt) (inj₂ m)))
  (hcme~₁ : (c : C₁) (m : Z) → (Γ₂ ≈ [ c ]ₒ₁ • [ inj₂ m ]ʷ) (((λ x → [ inj₂ x ]ʷ) *) (proj₁ (hcme₁ c m)) • [ proj₁ (proj₂ (hcme₁ c m)) ]ₒ₁))
  (h-wd-ax₁ : (c : C₁ ⊎ ⊤) {u t : Word (X ⊎ Z)} → (Γ₂ === u) t →  PW.Pointwise (_≈_ rz) _≡_ ((h₁ **) c u) ((h₁ **) c t))
  (f-wd-ax₁ : {w v : Word Z} → (rz === w) v → (Γ₂ ≈ ((λ x → [ inj₂ x ]ʷ) *) w) (((λ x → [ inj₂ x ]ʷ) *) v))
  (h=ract₁ : (c : C₁ ⊎ ⊤) (y : X ⊎ Z) → (Γ₂ ≈ Data.Sum.[ [_]ₒ₁ , (λ v → ε) ] c • [ y ]ʷ) (((λ x → [ inj₂ x ]ʷ) *) (proj₁ (h₁ c y)) • Data.Sum.[ [_]ₒ₁ , (λ v → ε) ] (proj₂ (h₁ c y))))
  (C₂ : Set)
  (h₂ : C₂ ⊎ ⊤ → Y ⊎ Z → Word Z × (C₂ ⊎ ⊤))
  ([_]ₒ₂ : C₂ → Word (Y ⊎ Z))
  (hcme₂ : (c : C₂) (m : Z) → ∃ (λ w → ∃ (λ c' → h₂ (inj₁ c) (inj₂ m) ≡ (w , inj₁ c'))))
  (htme₂ : (m : Z) → h₂ (inj₂ tt) (inj₂ m) ≡ ([ m ]ʷ , inj₂ tt))
  (htme~₂ : (m : Z) → PW.Pointwise (_≈_ rz) _≡_ ([ m ]ʷ , inj₂ tt)  (h₂ (inj₂ tt) (inj₂ m)))
  (hcme~₂ : (c : C₂) (m : Z) → (Γ₃ ≈ [ c ]ₒ₂ • [ inj₂ m ]ʷ) (((λ x → [ inj₂ x ]ʷ) *) (proj₁ (hcme₂ c m)) • [ proj₁ (proj₂ (hcme₂ c m)) ]ₒ₂))
  (h-wd-ax₂ : (c : C₂ ⊎ ⊤) {u t : Word (Y ⊎ Z)} → (Γ₃ === u) t →  PW.Pointwise (_≈_ rz) _≡_ ((h₂ **) c u) ((h₂ **) c t))
  (f-wd-ax₂ : {w v : Word Z} → (rz === w) v → (Γ₃ ≈ ((λ x → [ inj₂ x ]ʷ) *) w) (((λ x → [ inj₂ x ]ʷ) *) v))
  (h=ract₂ : (c : C₂ ⊎ ⊤) (y : Y ⊎ Z) → (Γ₃ ≈ Data.Sum.[ [_]ₒ₂ , (λ v → ε) ] c • [ y ]ʷ) (((λ x → [ inj₂ x ]ʷ) *) (proj₁ (h₂ c y)) • Data.Sum.[ [_]ₒ₂ , (λ v → ε) ] (proj₂ (h₂ c y))))
  where
  
  anfp : PP.AlmostNFProperty (Γ₁'' ∪ Γ₂'' ∪ Γ₃'')
  anfp = anfpᵣ (nfp-iso.nfp' (nfp nfp-rz) (gg) (iso-iso.iso← (Γ₂'' ∪ Γ₃'') amal23 (([_]ʷ ∘ fz)*) isoz))
    where
    open iso-iso (Γ₂'' ∪ Γ₃'') amal23 (([_]ʷ ∘ fz)*) isoz using (gg)

    anfd : AmalDataNF Z Γ₂ Γ₃
    anfd = record {
      P₀ = rz ;
      CA₁ = record
             { C = C₁
             ; f = [_]ʷ ∘ inj₂
             ; h = h₁
             ; [_]ₒ = [_]ₒ₁
             ; hcme = hcme₁
             ; htme = htme₁
             ; htme~ = htme~₁
             ; hcme~ = hcme~₁
             ; h-wd-ax = h-wd-ax₁
             ; f-wd-ax = f-wd-ax₁
             ; h=ract = h=ract₁
             } ;
      CA₂ = record
             { C = C₂
             ; f = [_]ʷ ∘ inj₂
             ; h = h₂
             ; [_]ₒ = [_]ₒ₂
             ; hcme = hcme₂
             ; htme = htme₂
             ; htme~ = htme~₂
             ; hcme~ = hcme~₂
             ; h-wd-ax = h-wd-ax₂
             ; f-wd-ax = f-wd-ax₂
             ; h=ract = h=ract₂
             } }

    open ANF Γ₂ Γ₃ anfd



module ANFP₂
  (rx : WRel X)
  (nfp-rx : PP.NFProperty rx)
  (C₁ : Set)
  (h₁ : C₁ ⊎ ⊤ → X ⊎ Y → Word X × (C₁ ⊎ ⊤))
  ([_]ₒ₁ : C₁ → Word (X ⊎ Y))
  (hcme₁ : (c : C₁) (m : X) → ∃ (λ w → ∃ (λ c' → h₁ (inj₁ c) (inj₁ m) ≡ (w , inj₁ c'))))
  (htme₁ : (m : X) → h₁ (inj₂ tt) (inj₁ m) ≡ ([ m ]ʷ , inj₂ tt))
  (htme~₁ : (m : X) → PW.Pointwise (_≈_ rx) _≡_ ([ m ]ʷ , inj₂ tt)  (h₁ (inj₂ tt) (inj₁ m)))
  (hcme~₁ : (c : C₁) (m : X) → (Γ₁ ≈ [ c ]ₒ₁ • [ inj₁ m ]ʷ) (((λ x → [ inj₁ x ]ʷ) *) (proj₁ (hcme₁ c m)) • [ proj₁ (proj₂ (hcme₁ c m)) ]ₒ₁))
  (h-wd-ax₁ : (c : C₁ ⊎ ⊤) {u t : Word (X ⊎ Y)} → (Γ₁ === u) t →  PW.Pointwise (_≈_ rx) _≡_ ((h₁ **) c u) ((h₁ **) c t))
  (f-wd-ax₁ : {w v : Word X} → (rx === w) v → (Γ₁ ≈ ((λ x → [ inj₁ x ]ʷ) *) w) (((λ x → [ inj₁ x ]ʷ) *) v))
  (h=ract₁ : (c : C₁ ⊎ ⊤) (y : X ⊎ Y) → (Γ₁ ≈ Data.Sum.[ [_]ₒ₁ , (λ v → ε) ] c • [ y ]ʷ) (((λ x → [ inj₁ x ]ʷ) *) (proj₁ (h₁ c y)) • Data.Sum.[ [_]ₒ₁ , (λ v → ε) ] (proj₂ (h₁ c y))))
  (C₂ : Set)
  (h₂ : C₂ ⊎ ⊤ → X ⊎ Z → Word X × (C₂ ⊎ ⊤))
  ([_]ₒ₂ : C₂ → Word (X ⊎ Z))
  (hcme₂ : (c : C₂) (m : X) → ∃ (λ w → ∃ (λ c' → h₂ (inj₁ c) (inj₁ m) ≡ (w , inj₁ c'))))
  (htme₂ : (m : X) → h₂ (inj₂ tt) (inj₁ m) ≡ ([ m ]ʷ , inj₂ tt))
  (htme~₂ : (m : X) → PW.Pointwise (_≈_ rx) _≡_ ([ m ]ʷ , inj₂ tt)  (h₂ (inj₂ tt) (inj₁ m)))
  (hcme~₂ : (c : C₂) (m : X) → (Γ₂ ≈ [ c ]ₒ₂ • [ inj₁ m ]ʷ) (((λ x → [ inj₁ x ]ʷ) *) (proj₁ (hcme₂ c m)) • [ proj₁ (proj₂ (hcme₂ c m)) ]ₒ₂))
  (h-wd-ax₂ : (c : C₂ ⊎ ⊤) {u t : Word (X ⊎ Z)} → (Γ₂ === u) t →  PW.Pointwise (_≈_ rx) _≡_ ((h₂ **) c u) ((h₂ **) c t))
  (f-wd-ax₂ : {w v : Word X} → (rx === w) v → (Γ₂ ≈ ((λ x → [ inj₁ x ]ʷ) *) w) (((λ x → [ inj₁ x ]ʷ) *) v))
  (h=ract₂ : (c : C₂ ⊎ ⊤) (y : X ⊎ Z) → (Γ₂ ≈ Data.Sum.[ [_]ₒ₂ , (λ v → ε) ] c • [ y ]ʷ) (((λ x → [ inj₁ x ]ʷ) *) (proj₁ (h₂ c y)) • Data.Sum.[ [_]ₒ₂ , (λ v → ε) ] (proj₂ (h₂ c y))))
  where
  
  anfp : PP.AlmostNFProperty (Γ₁'' ∪ Γ₁'' ∪ Γ₂'')
  anfp = anfpᵣ (nfp-iso.nfp' (nfp nfp-rx) (gg) (iso-iso.iso← (Γ₁'' ∪ Γ₂'') amal12 (([_]ʷ ∘ fx)*) isox))
    where
    open iso-iso (Γ₁'' ∪ Γ₂'') amal12 (([_]ʷ ∘ fx)*) isox using (gg)

    anfd : AmalDataNF X Γ₁ Γ₂
    anfd = record {
      P₀ = rx ;
      CA₁ = record
             { C = C₁
             ; f = [_]ʷ ∘ inj₁
             ; h = h₁
             ; [_]ₒ = [_]ₒ₁
             ; hcme = hcme₁
             ; htme = htme₁
             ; htme~ = htme~₁
             ; hcme~ = hcme~₁
             ; h-wd-ax = h-wd-ax₁
             ; f-wd-ax = f-wd-ax₁
             ; h=ract = h=ract₁
             } ;
      CA₂ = record
             { C = C₂
             ; f = [_]ʷ ∘ inj₁
             ; h = h₂
             ; [_]ₒ = [_]ₒ₂
             ; hcme = hcme₂
             ; htme = htme₂
             ; htme~ = htme~₂
             ; hcme~ = hcme~₂
             ; h-wd-ax = h-wd-ax₂
             ; f-wd-ax = f-wd-ax₂
             ; h=ract = h=ract₂
             } }

    open ANF Γ₁ Γ₂ anfd


module ANFP₃
  (ry : WRel Y)
  (nfp-ry : PP.NFProperty ry)
  (C₁ : Set)
  (h₁ : C₁ ⊎ ⊤ → X ⊎ Y → Word Y × (C₁ ⊎ ⊤))
  ([_]ₒ₁ : C₁ → Word (X ⊎ Y))
  (hcme₁ : (c : C₁) (m : Y) → ∃ (λ w → ∃ (λ c' → h₁ (inj₁ c) (inj₂ m) ≡ (w , inj₁ c'))))
  (htme₁ : (m : Y) → h₁ (inj₂ tt) (inj₂ m) ≡ ([ m ]ʷ , inj₂ tt))
  (htme~₁ : (m : Y) → PW.Pointwise (_≈_ ry) _≡_ ([ m ]ʷ , inj₂ tt)  (h₁ (inj₂ tt) (inj₂ m)))
  (hcme~₁ : (c : C₁) (m : Y) → (Γ₁ ≈ [ c ]ₒ₁ • [ inj₂ m ]ʷ) (((λ x → [ inj₂ x ]ʷ) *) (proj₁ (hcme₁ c m)) • [ proj₁ (proj₂ (hcme₁ c m)) ]ₒ₁))
  (h-wd-ax₁ : (c : C₁ ⊎ ⊤) {u t : Word (X ⊎ Y)} → (Γ₁ === u) t →  PW.Pointwise (_≈_ ry) _≡_ ((h₁ **) c u) ((h₁ **) c t))
  (f-wd-ax₁ : {w v : Word Y} → (ry === w) v → (Γ₁ ≈ ((λ x → [ inj₂ x ]ʷ) *) w) (((λ x → [ inj₂ x ]ʷ) *) v))
  (h=ract₁ : (c : C₁ ⊎ ⊤) (y : X ⊎ Y) → (Γ₁ ≈ Data.Sum.[ [_]ₒ₁ , (λ v → ε) ] c • [ y ]ʷ) (((λ x → [ inj₂ x ]ʷ) *) (proj₁ (h₁ c y)) • Data.Sum.[ [_]ₒ₁ , (λ v → ε) ] (proj₂ (h₁ c y))))
  (C₂ : Set)
  (h₂ : C₂ ⊎ ⊤ → Y ⊎ Z → Word Y × (C₂ ⊎ ⊤))
  ([_]ₒ₂ : C₂ → Word (Y ⊎ Z))
  (hcme₂ : (c : C₂) (m : Y) → ∃ (λ w → ∃ (λ c' → h₂ (inj₁ c) (inj₁ m) ≡ (w , inj₁ c'))))
  (htme₂ : (m : Y) → h₂ (inj₂ tt) (inj₁ m) ≡ ([ m ]ʷ , inj₂ tt))
  (htme~₂ : (m : Y) → PW.Pointwise (_≈_ ry) _≡_ ([ m ]ʷ , inj₂ tt)  (h₂ (inj₂ tt) (inj₁ m)))
  (hcme~₂ : (c : C₂) (m : Y) → (Γ₃ ≈ [ c ]ₒ₂ • [ inj₁ m ]ʷ) (((λ x → [ inj₁ x ]ʷ) *) (proj₁ (hcme₂ c m)) • [ proj₁ (proj₂ (hcme₂ c m)) ]ₒ₂))
  (h-wd-ax₂ : (c : C₂ ⊎ ⊤) {u t : Word (Y ⊎ Z)} → (Γ₃ === u) t →  PW.Pointwise (_≈_ ry) _≡_ ((h₂ **) c u) ((h₂ **) c t))
  (f-wd-ax₂ : {w v : Word Y} → (ry === w) v → (Γ₃ ≈ ((λ x → [ inj₁ x ]ʷ) *) w) (((λ x → [ inj₁ x ]ʷ) *) v))
  (h=ract₂ : (c : C₂ ⊎ ⊤) (y : Y ⊎ Z) → (Γ₃ ≈ Data.Sum.[ [_]ₒ₂ , (λ v → ε) ] c • [ y ]ʷ) (((λ x → [ inj₁ x ]ʷ) *) (proj₁ (h₂ c y)) • Data.Sum.[ [_]ₒ₂ , (λ v → ε) ] (proj₂ (h₂ c y))))
  where
  
  anfp : PP.AlmostNFProperty (Γ₁'' ∪ Γ₁'' ∪ Γ₃'')
  anfp = anfpᵣ (nfp-iso.nfp' (nfp nfp-ry) (gg) (iso-iso.iso← (Γ₁'' ∪ Γ₃'') amal13 (([_]ʷ ∘ fy)*) isoy))
    where
    open iso-iso (Γ₁'' ∪ Γ₃'') amal13 (([_]ʷ ∘ fy)*) isoy using (gg)

    anfd : AmalDataNF Y Γ₁ Γ₃
    anfd = record {
      P₀ = ry ;
      CA₁ = record
             { C = C₁
             ; f = [_]ʷ ∘ inj₂
             ; h = h₁
             ; [_]ₒ = [_]ₒ₁
             ; hcme = hcme₁
             ; htme = htme₁
             ; htme~ = htme~₁
             ; hcme~ = hcme~₁
             ; h-wd-ax = h-wd-ax₁
             ; f-wd-ax = f-wd-ax₁
             ; h=ract = h=ract₁
             } ;
      CA₂ = record
             { C = C₂
             ; f = [_]ʷ ∘ inj₁
             ; h = h₂
             ; [_]ₒ = [_]ₒ₂
             ; hcme = hcme₂
             ; htme = htme₂
             ; htme~ = htme~₂
             ; hcme~ = hcme~₂
             ; h-wd-ax = h-wd-ax₂
             ; f-wd-ax = f-wd-ax₂
             ; h=ract = h=ract₂
             } }

    open ANF Γ₁ Γ₃ anfd
