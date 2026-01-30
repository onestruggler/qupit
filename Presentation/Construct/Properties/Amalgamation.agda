open import Level using (0ℓ)

open import Relation.Binary.PropositionalEquality as Eq renaming ([_] to [_]') using ( _≡_ ; inspect)
open import Relation.Binary using (IsEquivalence ; Setoid ; Rel)
open import Data.Product.Relation.Binary.Pointwise.NonDependent as PW
open import Function.Definitions using (Injective ; Surjective)
open import Data.Product using (_,_ ; _×_ ; proj₁ ; proj₂)
open import Data.Sum.Properties using (inj₁-injective ; inj₂-injective)

import Relation.Binary.Reasoning.Setoid as SR


open import Word.Base
open import Word.Properties
import Presentation.Base as PB
import Presentation.Properties as PP
open import Presentation.CosetNF

open import Presentation.Reidemeister-Schreier

open import Presentation.Construct.Base


module Presentation.Construct.Properties.Amalgamation where

open import Relation.Binary.Definitions using (DecidableEquality ; Decidable)
open import Relation.Binary.Morphism.Structures using (IsRelMonomorphism)
open import Relation.Binary.PropositionalEquality using (_≡_ ; setoid)
import Relation.Binary.PropositionalEquality as Eq
open import Relation.Nullary.Decidable using (via-injection)
open import Function.Definitions using (Injective)
open import Function.Bundles using (Injection)
open import Function using (_∘_ ; _∋_)
open import Relation.Binary.Morphism.Definitions using (Homomorphic₂)
open import Data.Sum using (_⊎_ ; inj₁ ; inj₂)
open import Data.Unit using (⊤ ; tt)
open import Data.List hiding ([_])



lemma-**-act3 :
  {Y X D : Set}
  (py : WRel Y) (_⊕_ : D -> X -> Word X × D) ([_] : D -> Word Y) (f : X -> Word Y) ->
  let
      open PB py using (_≈_)
  in
  (hyp : (c : D) (x : X) -> ([ c ] • f x) ≈ (f *) ((c ⊕ x) .proj₁) • [ (c ⊕ x) .proj₂ ])
  -> -- -------------------------------------------------------------------------------------
  ∀ (c : D) (w : Word X) -> let _⊕'_ = _⊕_ ** in [ c ] • (f *) w ≈ (f *) ((c ⊕' w) .proj₁) • [ (c ⊕' w) .proj₂ ]
lemma-**-act3 {Y} {X} {D} py _⊕_ [_] f hyp c [ x ]ʷ = hyp c x
lemma-**-act3 {Y} {X} {D} py _⊕_ [_] f hyp c ε = _≈_.trans _≈_.right-unit (_≈_.sym _≈_.left-unit)
  where
    open PB py
lemma-**-act3 {Y} {X} {D} py _⊕_ [_] f hyp c (w • v)  with (_⊕_ **) c w | inspect (((_⊕_) **) c) w
... | (w' , c') | [ Eq.refl ]' with (_⊕_ **) c' v | inspect ((_⊕_ **) c') v
... | (v' , c'') | [ Eq.refl ]' = claim
  where
    open PB py
    open PP py renaming (word-setoid to ws) using ()

    -- eval : Word X × D -> Word X
    -- eval wc = (wc .proj₁) • [ wc .proj₂ ]
    infix 4 _⊕'_ 
    _⊕'_ = _⊕_ **

    [_]ₓ' = f *

    open SR ws

    claim : [ c ] • [ w • v ]ₓ' ≈ [ w' • v' ]ₓ' • [ c'' ]
    claim = begin
      [ c ] • [ w • v ]ₓ' ≈⟨ _≈_.sym _≈_.assoc ⟩
      ([ c ] • [ w ]ₓ') • [ v ]ₓ' ≈⟨ _≈_.cong (lemma-**-act3 py _⊕_ [_] f hyp c w) _≈_.refl ⟩
      ([ w' ]ₓ' • [ c' ]) • [ v ]ₓ' ≈⟨ _≈_.assoc ⟩
      [ w' ]ₓ' • [ c' ] • [ v ]ₓ' ≈⟨ _≈_.cong _≈_.refl (lemma-**-act3 py _⊕_ [_] f hyp c' v) ⟩
      [ w' ]ₓ' • [ v' ]ₓ' • [ c'' ] ≈⟨ _≈_.sym _≈_.assoc ⟩
      [ w' • v' ]ₓ' • [ c'' ] ∎



-- C (D) is the set of non-trivial coset representatives.
amalNFC : (C D : Set) -> Set
amalNFC C D = (D ⊎ ⊤) × List (C × D) × (C ⊎ ⊤)

record AmalDataNF {A B : Set} (M : Set) (P1 : WRel A) (P2 : WRel B) : Set₁ where
  field
    P₀ : WRel M
    CA₁ : CosetNF-CT-Assumptions-And-Theorems-Packed P₀ P1
    CA₂ : CosetNF-CT-Assumptions-And-Theorems-Packed P₀ P2

-- Amalgamation product with NF property.
module ANF {M A B : Set} (P₁ : WRel A) (P₂ : WRel B) (anf : AmalDataNF M P₁ P₂) where
  open PB P₁ renaming ( _===_ to _===₁_ ; _≈_ to _≈₁_ ; refl' to refl'₁) using () public
  open PP P₁ renaming ( word-setoid to word-setoid₁) using () public
  open PB P₂ renaming ( _===_ to _===₂_ ; _≈_ to _≈₂_) using () public
  open PP P₂ renaming ( •-ε-monoid to m₂) using () public
  open AmalDataNF anf using (CA₁ ; CA₂ ; P₀) using () public
  open PB P₀ renaming ( _===_ to _===₀_ ; _≈_ to _≈₀_ ; refl' to refl'₀) using () public
  open PP P₀ renaming (word-setoid to ws₀) using () public
  open CosetNF-CT-Assumptions-And-Theorems-Packed CA₁ renaming ([_]ₒ to [_]ₒ₁ ; [_]ₓ to [_]ₓ₁ ; [_] to [_]₁ ; f to f₁ ; f-wd-ax to f-wd-ax₁ ; f*-injective to f*-injective₁ ; [I]≡ε to [I]≡ε₁
    ; h to h₁ ; nfx to nfx₁ ; h=ract to h₁-hyp ; _~_ to _~₁_ ; I to I₁) using (C ; hcm ; hcm' ; hcmw ; hca ; hcmw-hyp ; hcmw'-hyp ; hcm-hyp ; hcm'-hyp ; hca-hyp) public
  open CosetNF-CT-Assumptions-And-Theorems-Packed CA₂ renaming (h to h₂ ; [_]ₒ to [_]ₒ₂ ; [_]ₓ to [_]ₓ₂ ; [_] to [_]₂ ; f to f₂ ; f-wd-ax to f-wd-ax₂ ; f*-injective to f*-injective₂ ; [I]≡ε to [I]≡ε₂
    ; nfx to nfx₂ ; h=ract to h₂-hyp ; _~_ to _~₂_ ; I to I₂ ; hcm to hdm ; hca to hdb ; hcmw-hyp to hdmw-hyp ; hcmw'-hyp to hdmw'-hyp ; hcm'-hyp to hdm'-hyp ; hcm-hyp to hdm-hyp ; hca-hyp to hdb-hyp ; hcm' to hdm' ; hcmw to hdmw ; hcmw' to hdmw' ; C to D) using () public


  CD : Set
  CD = amalNFC C D

  mypres = ( P₁ * P₂ ⋆ f₁ ⋆ f₂)
  open PP mypres renaming (word-setoid to ws₃ ; by-assoc to by-assoc₃) using () public
  open PB mypres renaming (Alphabet to Y ; _===_ to _===₃_ ; _≈_ to _≈₃_ ; refl' to refl'₃) using () public

  open _≈₃_
  
  P1 = P₁
  P2 = P₂

  f : M -> Word Y
  f = [_]ₗ ∘ f₁

  f' : M -> Word Y
  f' = [_]ᵣ ∘ f₂

  [_]ₓ = f *

  [_]ₓ' = f' *

  lemma-amal : ∀ w -> [ w ]ₓ ≈₃ [ w ]ₓ'
  lemma-amal [ x ]ʷ = axiom (mid amal)
  lemma-amal ε = refl
  lemma-amal (w • w₁) = cong (lemma-amal w) (lemma-amal w₁)

  [_]ᵢ : (C × D) → Word (A ⊎ B)
  [_]ᵢ (c , d) = [ [ c ]ₒ₁ ]ₗ • [ [ d ]ₒ₂ ]ᵣ

  eval-cd = [_]ᵢ
  
  semcds : List (C × D) -> Word (A ⊎ B)
  semcds [] = ε
  semcds ((c , d) ∷ xs) = semcds xs • [ (c , d) ]ᵢ

  [_]ₓₛ : List (C × D) → Word (A ⊎ B)
  [_]ₓₛ = semcds
  
  
  [_] : CD → Word (A ⊎ B)
  [ l , m , r ] = [ [ l ]₂ ]ᵣ • semcds m • [ [ r ]₁ ]ₗ

  I : CD
  I = inj₂ tt , [] , inj₂ tt

  [I]≈ε : [ (inj₂ tt , [] , inj₂ tt) ] ≈₃ ε
  [I]≈ε rewrite [I]≡ε₁ | [I]≡ε₂ = _≈₃_.trans _≈₃_.left-unit _≈₃_.left-unit


  hcd : C × D -> M -> Word M × (C × D)
  hcd (c , d) m with hdm d m
  ... | (wm , d') with hcmw c wm
  ... | (wm' , c') = wm' , c' , d'

  hcdw : C × D -> Word M -> Word M × (C × D)
  hcdw = hcd **

  hcdws : List (C × D) -> Word M -> Word M × List (C × D)
  hcdws [] wm = wm , []
  hcdws (x ∷ cds) wm with hcdw x wm
  ... | (wm' , x') with hcdws cds wm'
  ... | (wm'' , cds') = wm'' , (x' ∷ cds')


  hcdb : C × D -> B -> (Word M × (C × D)) ⊎ (Word M × C)
  hcdb (c , d) b with hdb d b
  hcdb (c , d) b | wm , inj₁ d' with hcmw c wm
  ... | (wm' , c') = inj₁ (wm' , c' , d')
  hcdb (c , d) b | wm , inj₂ tt with hcmw c wm
  ... | (wm' , c') = inj₂ (wm' , c')
  
  hcdbs : List (C × D) -> ∀ (c : C) (d : D) -> B -> (((Word M × List (C × D))) ⊎ ((Word M × List (C × D) × C)))
  hcdbs cds c d b with hcdb (c , d) b
  hcdbs cds c d b | inj₁ (wm , c' , d') with hcdws cds wm
  ... | (wm' , cds') = inj₁ (wm' , cds' ++ (c' , d') ∷ [])
  hcdbs cds c d b | inj₂ (wm , c') with hcdws cds wm
  ... | (wm' , cds') = inj₂ (wm' , cds' , c')


  hma : CD -> A -> Word M × CD
  hma (d , cds , c) (x) with h₁ c x
  ... | (wm , c') with hcdws cds wm
  ... | (wm' , cds') with hdmw' d wm'
  ... | (wm'' , d') = wm'' , d' , cds' , c'

  hmaw = hma **

  infix 4 _~_
  _~_ = PW.Pointwise _≈₀_ (_≡_ {A = CD})

  mcdₛ : Setoid _ _
  mcdₛ = PW.×-setoid ws₀ (setoid CD)

  open Setoid mcdₛ renaming (refl to reflₛ ; sym to symₛ ; trans to transₛ)
  
 
  module AB = LeftRightCongruence P1 P2 (Γₐ f₁ f₂)

 
  aux-f₁ : ∀ wm -> [ (f₁ *) wm ]ₗ ≡ (f *) wm
  aux-f₁ wm = begin
    [ (f₁ *) wm ]ₗ ≡⟨ Eq.sym (lemma-*-∘ f₁ inj₁ wm) ⟩
    (f *) wm ∎
    where open Eq.≡-Reasoning

  aux-f₁' : ∀ wm -> [ (f₁ *) wm ]ₗ ≈₃ (f *) wm
  aux-f₁' wm rewrite aux-f₁ wm = refl


  aux-f₂ : ∀ wm -> [ (f₂ *) wm ]ᵣ ≈₃ (f *) wm
  aux-f₂ wm = begin
    [ (f₂ *) wm ]ᵣ ≡⟨ Eq.sym (lemma-*-∘ f₂ inj₂ wm) ⟩
    [ wm ]ₓ' ≈⟨ sym (lemma-amal wm) ⟩
    (f *) wm ∎
    where open SR ws₃

  lemma-amal' : ∀ w -> [ [ w ]ₓ₁ ]ₗ ≈₃ [ [ w ]ₓ₂ ]ᵣ
  lemma-amal' w = begin
    [ [ w ]ₓ₁ ]ₗ ≈⟨ refl'₃ (aux-f₁ w) ⟩
    [ w ]ₓ ≈⟨ sym (aux-f₂ w) ⟩
    [ [ w ]ₓ₂ ]ᵣ ∎
    where
    open SR ws₃

  f-wd-ax : ∀ {w v} -> w ===₀ v -> (f *) w ≈₃ (f *) v
  f-wd-ax {w} {v} eqx = begin
    (f *) w ≡⟨ Eq.sym (aux-f₁ w) ⟩
    [ ((f₁)*) w ]ₗ ≈⟨ AB.lefts (f-wd-ax₁ eqx) ⟩
    [ ((f₁)*) v ]ₗ ≡⟨ aux-f₁ v ⟩
    (f *) v ∎
    where open SR ws₃



  aux-hh1 : ∀ d cds c -> [ (d , cds , c) ] ≈₃ [ (d , cds , inj₂ tt) ] • [ [ c ]₁ ]ₗ
  aux-hh1 d cds c  = _≈₃_.sym (begin
    [ (d , cds , inj₂ tt) ] • [ [ c ]₁ ]ₗ ≈⟨ _≈₃_.refl ⟩
    ([ [ d ]₂ ]ᵣ • [ cds ]ₓₛ • [ [ inj₂ tt ]₁ ]ₗ ) • [ [ c ]₁ ]ₗ ≈⟨ _≈₃_.trans _≈₃_.assoc (_≈₃_.cong _≈₃_.refl _≈₃_.assoc) ⟩
    [ [ d ]₂ ]ᵣ • [ cds ]ₓₛ • [ [ inj₂ tt ]₁ ]ₗ • [ [ c ]₁ ]ₗ ≈⟨ _≈₃_.refl ⟩
    [ [ d ]₂ ]ᵣ • [ cds ]ₓₛ • [ [ inj₂ tt ]₁ • [ c ]₁ ]ₗ ≈⟨ _≈₃_.cong _≈₃_.refl (_≈₃_.cong _≈₃_.refl (refl'₃ (Eq.cong₂ _•_ ( Eq.cong [_]ₗ [I]≡ε₁) Eq.refl))) ⟩
    [ [ d ]₂ ]ᵣ • [ cds ]ₓₛ • [ ε • [ c ]₁ ]ₗ ≈⟨ _≈₃_.cong _≈₃_.refl (_≈₃_.cong _≈₃_.refl _≈₃_.left-unit) ⟩
    [ [ d ]₂ ]ᵣ • [ cds ]ₓₛ • [ [ c ]₁ ]ₗ ≈⟨ _≈₃_.refl ⟩
    [ (d , cds ,  c) ]  ∎)
    where open SR ws₃


  aux-hh2 : ∀ d cds -> [ (d , cds , inj₂ tt) ] ≈₃ [ (d , [] , inj₂ tt) ] • [ cds ]ₓₛ
  aux-hh2 d cds = _≈₃_.sym (begin
    [ (d , [] , inj₂ tt) ] • [ cds ]ₓₛ ≈⟨ _≈₃_.refl ⟩
    ([ [ d ]₂ ]ᵣ • [ [] ]ₓₛ • [ [ inj₂ tt ]₁ ]ₗ ) • [ cds ]ₓₛ ≈⟨ _≈₃_.trans _≈₃_.assoc (_≈₃_.cong _≈₃_.refl _≈₃_.assoc) ⟩
    [ [ d ]₂ ]ᵣ • [ [] ]ₓₛ • [ [ inj₂ tt ]₁ ]ₗ • [ cds ]ₓₛ ≈⟨ _≈₃_.refl ⟩
    [ [ d ]₂ ]ᵣ • ε • [ [ inj₂ tt ]₁ ]ₗ • [ cds ]ₓₛ ≈⟨ _≈₃_.cong _≈₃_.refl _≈₃_.left-unit ⟩
    [ [ d ]₂ ]ᵣ • [ [ inj₂ tt ]₁ ]ₗ • [ cds ]ₓₛ ≡⟨ Eq.cong (λ xx → [ [ d ]₂ ]ᵣ • [ xx ]ₗ • [ cds ]ₓₛ) [I]≡ε₁ ⟩
    [ [ d ]₂ ]ᵣ • ε • [ cds ]ₓₛ ≈⟨ _≈₃_.cong _≈₃_.refl _≈₃_.left-unit ⟩
    [ [ d ]₂ ]ᵣ • [ cds ]ₓₛ ≈⟨ _≈₃_.sym (_≈₃_.cong _≈₃_.refl _≈₃_.right-unit) ⟩
    [ [ d ]₂ ]ᵣ • [ cds ]ₓₛ • ε ≡⟨ Eq.sym (Eq.cong (λ xx → [ [ d ]₂ ]ᵣ • [ cds ]ₓₛ  • [ xx ]ₗ) [I]≡ε₁) ⟩
    [ [ d ]₂ ]ᵣ • [ cds ]ₓₛ • [ [ inj₂ tt ]₁ ]ₗ ≈⟨ _≈₃_.refl ⟩
    [ (d , cds , inj₂ tt) ]  ∎)
    where open SR ws₃


  aux-hhd : ∀ d  -> [ (d , [] , inj₂ tt) ] ≈₃ [ (inj₂ tt , [] , inj₂ tt) ] • [ [ d ]₂ ]ᵣ
  aux-hhd d  = sym (begin
    [ (inj₂ tt , [] , inj₂ tt) ] • [ [ d ]₂ ]ᵣ ≈⟨ cong (trans left-unit left-unit) refl ⟩
    ε • [ [ d ]₂ ]ᵣ ≈⟨ left-unit ⟩
    [ [ d ]₂ ]ᵣ ≈⟨ sym right-unit ⟩
    [ [ d ]₂ ]ᵣ • ε ≈⟨ sym (cong refl left-unit) ⟩
    [ [ d ]₂ ]ᵣ • ε • ε ≈⟨ refl ⟩
    [ (d , [] , inj₂ tt) ] ∎)
    where open SR ws₃


  aux-hdm : ∀ m d -> let (wm' , d') = hdm d m in [ [ inj₁ d ]₂ ]ᵣ • [ f₂ m ]ᵣ ≈₃ [ wm' ]ₓ' • [ [ inj₁ d' ]₂ ]ᵣ
  aux-hdm m d =
    let (wm' , d') = hdm d m in
    begin
    [ [ inj₁ d ]₂ ]ᵣ • [ f₂ m ]ᵣ ≈⟨ refl ⟩
    [ [ inj₁ d ]₂ • f₂ m ]ᵣ ≈⟨ AB.rights (hdm-hyp d m) ⟩
    [ [ wm' ]ₓ₂ • [ inj₁ d' ]₂ ]ᵣ ≈⟨ refl ⟩
    [ [ wm' ]ₓ₂ ]ᵣ • [ [ inj₁ d' ]₂ ]ᵣ ≈⟨ cong (aux-f₂ wm') refl ⟩
    [ wm' ]ₓ • [ [ inj₁ d' ]₂ ]ᵣ ≈⟨ cong (lemma-amal wm') refl ⟩
    [ wm' ]ₓ' • [ [ inj₁ d' ]₂ ]ᵣ ∎
    where open SR ws₃


  aux-hh3' : ∀ cd m -> let (m' , cd') = hcd cd m in
    [ cd ]ᵢ • f m  ≈₃ [ m' ]ₓ • [ cd' ]ᵢ
  aux-hh3' cd@(c , d) m =
    let (m' , cd'@(c' ,  d')) = hcd (c , d) m in
    let (m1 , d1) = hdm d m in
    let (m2 , c2) = hcmw c m1 in
    begin
    [ cd ]ᵢ • f m ≈⟨ assoc ⟩
    [ [ inj₁ c ]₁ ]ₗ • [ [ inj₁ d ]₂ ]ᵣ • f m ≈⟨ refl ⟩
    [ [ inj₁ c ]₁ ]ₗ • [ [ inj₁ d ]₂ ]ᵣ • [ f₁ m ]ₗ ≈⟨ cong refl (cong refl (axiom (mid amal))) ⟩
    [ [ inj₁ c ]₁ ]ₗ • [ [ inj₁ d ]₂ ]ᵣ • [ f₂ m ]ᵣ ≈⟨ cong refl (aux-hdm m d) ⟩
    [ [ inj₁ c ]₁ ]ₗ • [ m1 ]ₓ' • [ [ inj₁ d' ]₂ ]ᵣ ≈⟨ cong refl (cong (sym (lemma-amal m1)) refl) ⟩
    [ [ inj₁ c ]₁ ]ₗ • [ m1 ]ₓ • [ [ inj₁ d' ]₂ ]ᵣ ≈⟨ cong refl (cong (sym (refl'₃ (aux-f₁ m1))) refl ) ⟩
    [ [ inj₁ c ]₁ ]ₗ • [ [ m1 ]ₓ₁ ]ₗ • [ [ inj₁ d' ]₂ ]ᵣ ≈⟨ sym assoc ⟩
    [ [ inj₁ c ]₁ • [ m1 ]ₓ₁ ]ₗ • [ [ inj₁ d' ]₂ ]ᵣ ≈⟨ cong (AB.lefts (hcmw-hyp c m1)) refl ⟩
    [ [ m2 ]ₓ₁ • [ inj₁ c2 ]₁ ]ₗ • [ [ inj₁ d' ]₂ ]ᵣ ≈⟨ assoc ⟩
    [ [ m2 ]ₓ₁ ]ₗ • [ [ inj₁ c2 ]₁ ]ₗ • [ [ inj₁ d' ]₂ ]ᵣ ≈⟨ cong (refl'₃ (aux-f₁ m')) refl ⟩
    [ m' ]ₓ • [ cd' ]ᵢ ∎
    where open SR ws₃




  lemma-hcdw : ∀ cd wm -> let (wm' , cd') = hcdw cd wm in [ cd ]ᵢ • [ wm ]ₓ ≈₃ [ wm' ]ₓ • [ cd' ]ᵢ
  lemma-hcdw cd wm = lemma-**-act3 _===₃_ hcd [_]ᵢ ([_]ₗ ∘ f₁) aux-hh3' cd wm
  

  lemma-hcdws : ∀ cds wm -> let (wm' , cds') = hcdws cds wm in semcds cds • [ wm ]ₓ ≈₃ [ wm' ]ₓ • semcds cds'
  lemma-hcdws [] wm = _≈₃_.trans _≈₃_.left-unit (_≈₃_.sym _≈₃_.right-unit)
  lemma-hcdws (x ∷ cds) wm with hcdw x wm | inspect (hcdw x) wm
  ... | (wm1 , x1) | [ Eq.refl ]' with lemma-hcdw x wm1
  ... | hyp =
    let (wm' , cds') = hcdws cds wm1 in
    let (wm2 , cds2) = hcdws (x ∷ cds) wm in begin
    semcds (x ∷ cds) • [ wm ]ₓ ≈⟨ _≈₃_.assoc ⟩
    semcds cds • [ x ]ᵢ • [ wm ]ₓ ≈⟨ _≈₃_.cong _≈₃_.refl  (lemma-hcdw x wm) ⟩
    semcds cds • [ wm1 ]ₓ • [ x1 ]ᵢ ≈⟨ _≈₃_.sym _≈₃_.assoc ⟩
    (semcds cds • [ wm1 ]ₓ) • [ x1 ]ᵢ ≈⟨ _≈₃_.cong (lemma-hcdws cds wm1) _≈₃_.refl ⟩
    ([ wm' ]ₓ • semcds cds') • [ x1 ]ᵢ ≈⟨ _≈₃_.assoc ⟩
    [ wm2 ]ₓ • semcds cds2 ∎
    where open SR ws₃

  lemma-hdmw'1 : ∀ d wm -> let (wm' , d') = hdmw' d wm in [ [ d ]₂ ]ᵣ • (f *) wm ≈₃ (f *) wm' • [ [ d' ]₂ ]ᵣ 
  lemma-hdmw'1 d wm = let (wm' , d') = hdmw' d wm in begin
    [ [ d ]₂ ]ᵣ • (f *) wm ≈⟨ _≈₃_.cong _≈₃_.refl ( _≈₃_.sym (aux-f₂ wm)) ⟩
    [ [ d ]₂  • (f₂ *) wm ]ᵣ ≈⟨ AB.rights (hdmw'-hyp d wm) ⟩
    [ (f₂ *) wm' • [ d' ]₂ ]ᵣ  ≈⟨ cong (aux-f₂ wm') refl ⟩
    (f *) wm' • [ [ d' ]₂ ]ᵣ ∎
    where open SR ws₃



  lemma-hdmw1 : ∀ d wm -> let (wm' , d') = hdmw d wm in [ [ d ]ₒ₂ ]ᵣ • (f *) wm ≈₃ (f *) wm' • [ [ d' ]ₒ₂ ]ᵣ 
  lemma-hdmw1 d wm = let (wm' , d') = hdmw d wm in begin
    [ [ d ]ₒ₂ ]ᵣ • (f *) wm ≈⟨ _≈₃_.cong _≈₃_.refl ( _≈₃_.sym (aux-f₂ wm)) ⟩
    [ [ d ]ₒ₂  • (f₂ *) wm ]ᵣ ≈⟨ AB.rights (hdmw-hyp d wm) ⟩
    [ (f₂ *) wm' • [ d' ]ₒ₂ ]ᵣ  ≈⟨ cong (aux-f₂ wm') refl ⟩
    (f *) wm' • [ [ d' ]ₒ₂ ]ᵣ ∎
    where open SR ws₃


  lemma-hcmw1 : ∀ d wm -> let (wm' , d') = hcmw d wm in [ [ d ]ₒ₁ ]ₗ • (f *) wm ≈₃ (f *) wm' • [ [ d' ]ₒ₁ ]ₗ 
  lemma-hcmw1 d wm = let (wm' , d') = hcmw d wm in begin
    [ [ d ]ₒ₁ ]ₗ • (f *) wm ≈⟨ _≈₃_.cong _≈₃_.refl ( _≈₃_.sym (refl'₃ (aux-f₁ wm))) ⟩
    [ [ d ]ₒ₁  • (f₁ *) wm ]ₗ ≈⟨ AB.lefts (hcmw-hyp d wm) ⟩
    [ (f₁ *) wm' • [ d' ]ₒ₁ ]ₗ  ≈⟨ cong (refl'₃ (aux-f₁ wm')) refl ⟩
    (f *) wm' • [ [ d' ]ₒ₁ ]ₗ ∎
    where open SR ws₃

  lemma-cdε-m : ∀ m -> [ (inj₂ tt , [] , inj₂ tt) ] • [ [ m ]ₓ₁ ]ₗ ≈₃ [ [ m ]ₓ₁ ]ₗ • [ (inj₂ tt , [] , inj₂ tt) ]
  lemma-cdε-m m = begin
    [ (inj₂ tt , [] , inj₂ tt) ] • [ [ m ]ₓ₁ ]ₗ ≈⟨ cong (trans left-unit left-unit) refl ⟩
    ε • [ [ m ]ₓ₁ ]ₗ ≈⟨ trans left-unit (sym right-unit) ⟩
    [ [ m ]ₓ₁ ]ₗ • ε ≈⟨ cong refl (sym (trans left-unit left-unit)) ⟩
    [ [ m ]ₓ₁ ]ₗ • [ (inj₂ tt , [] , inj₂ tt) ] ∎
    where open SR ws₃


  hcdm : CD -> M -> Word M × CD
  hcdm (d , cds , c) m with hcm' c m
  ... | (wm , c') with hcdws cds wm
  ... | (wm' , cds') with hdmw' d wm'
  ... | (wm'' , d') = wm'' , d' , cds' , c'

  hcdmw = hcdm **

  lemma-hcdm : ∀ d cds m -> let (wm' , d' , cds' , c') = hcdm (d , cds , inj₂ tt) m
    in c' ≡ inj₂ tt
  lemma-hcdm d cds m = Eq.refl

  lemma-hcdmw : ∀ d cds c -> c ≡ inj₂ tt -> ∀ wm -> let (wm' , d' , cds' , c') = (hcdm **) (d , cds , inj₂ tt) wm
    in c' ≡ inj₂ tt
  lemma-hcdmw d cds c eq [ x ]ʷ = Eq.refl
  lemma-hcdmw d cds c eq ε = Eq.refl
  lemma-hcdmw d cds c eq (wm • wm₁) with (hcdm **) (d , cds , inj₂ tt) wm | inspect ((hcdm **) (d , cds , inj₂ tt)) wm
  ... | (wm' , (d' , cds' , c')) | [ Eq.refl ]' with lemma-hcdmw d cds c eq wm | lemma-hcdmw d' cds' c' (lemma-hcdmw d cds c eq wm) wm₁
  ... | ih1 | ih2 rewrite ih1 =
    let cd : CD
        cd = (d , cds , inj₂ tt)
    in
    let (wm' , d' , cds' , c') = (hcdm **) (d , cds , inj₂ tt) (wm • wm₁) in
    let (wm1 , d1 , cds1 , c1) = (hcdm **) (d , cds , inj₂ tt) wm in
    let cd'  = (d' , cds' , c') in
    begin
    c' ≡⟨ Eq.refl ⟩
    (hcdm **) cd (wm • wm₁) .proj₂ .proj₂ .proj₂ ≡⟨ Eq.refl ⟩
    (hcdm **) ((hcdm **) cd wm .proj₂) wm₁ .proj₂ .proj₂ .proj₂ ≡⟨ Eq.refl ⟩
    (hcdm **) (d1 , cds1 , c1) wm₁ .proj₂ .proj₂ .proj₂ ≡⟨ Eq.cong (\xx -> (hcdm **) (d1 , cds1 , xx) wm₁ .proj₂ .proj₂ .proj₂) (lemma-hcdmw d cds c eq wm) ⟩
    (hcdm **) (d1 , cds1 , inj₂ tt) wm₁ .proj₂ .proj₂ .proj₂ ≡⟨ lemma-hcdmw d1 cds1 (inj₂ tt) (Eq.refl) wm₁ ⟩
    inj₂ tt ∎
    where open Eq.≡-Reasoning

  lemma-cd-m : ∀ cd m -> let (x' , c') = hcdm cd m in
    [ cd ] • f m ≈₃ [ x' ]ₓ • [ c' ]
  lemma-cd-m cd@(d , cds , c) m =
    let (wm1 , c1) = hcm' c m in
    let (wm2 , cds') = hcdws cds wm1 in
    let (wm3 , d3) = hdmw' d wm2 in
    let (x' , c') = hcdm cd m in
    begin
    [ d , cds , c ] • f m ≈⟨ _≈₃_.cong (aux-hh1 d cds c)  _≈₃_.refl ⟩
    ([ d , cds , inj₂ tt ] • [ [ c ]₁ ]ₗ) • f m ≈⟨ assoc ⟩
    [ d , cds , inj₂ tt ] • [ [ c ]₁ ]ₗ • f m ≈⟨ refl ⟩
    [ (d , cds , inj₂ tt) ] • [ [ c ]₁ • f₁ m ]ₗ ≈⟨ _≈₃_.cong _≈₃_.refl (AB.lefts (hcm'-hyp c m)) ⟩
    [ (d , cds , inj₂ tt) ] • [ [ wm1 ]ₓ₁ • [ c1 ]₁ ]ₗ ≈⟨ sym assoc ⟩
    ([ (d , cds , inj₂ tt) ] • [ [ wm1 ]ₓ₁ ]ₗ) • [ [ c1 ]₁ ]ₗ ≈⟨ cong (cong (aux-hh2 d cds) refl) refl ⟩
    (([ (d , [] , inj₂ tt) ] • semcds cds) • [ [ wm1 ]ₓ₁ ]ₗ) • [ [ c1 ]₁ ]ₗ ≈⟨ cong assoc refl ⟩
    ([ (d , [] , inj₂ tt) ] • (semcds cds • [ [ wm1 ]ₓ₁ ]ₗ)) • [ [ c1 ]₁ ]ₗ ≈⟨ cong (cong refl (cong refl (refl'₃ (aux-f₁ wm1)))) refl ⟩
    ([ (d , [] , inj₂ tt) ] • (semcds cds • [ wm1 ]ₓ)) • [ [ c1 ]₁ ]ₗ ≈⟨ cong (cong refl (lemma-hcdws cds (wm1))) refl ⟩
    ([ (d , [] , inj₂ tt) ] • ([ wm2 ]ₓ • semcds cds')) • [ [ c1 ]₁ ]ₗ ≈⟨ cong (cong refl (cong (refl'₃ (Eq.sym (aux-f₁ wm2))) refl )) refl ⟩
    ([ (d , [] , inj₂ tt) ] • ([ [ wm2 ]ₓ₁ ]ₗ • semcds cds')) • [ [ c1 ]₁ ]ₗ ≈⟨ cong (sym assoc) refl ⟩
    (([ (d , [] , inj₂ tt) ] • [ [ wm2 ]ₓ₁ ]ₗ) • semcds cds') • [ [ c1 ]₁ ]ₗ ≈⟨ cong (cong (cong (aux-hhd d) refl) refl) refl ⟩
    ((([ (inj₂ tt , [] , inj₂ tt) ] • [ [ d ]₂ ]ᵣ) • [ [ wm2 ]ₓ₁ ]ₗ) • semcds cds') • [ [ c1 ]₁ ]ₗ ≈⟨ cong (cong assoc refl) refl ⟩
    (([ (inj₂ tt , [] , inj₂ tt) ] • [ [ d ]₂ ]ᵣ • [ [ wm2 ]ₓ₁ ]ₗ) • semcds cds') • [ [ c1 ]₁ ]ₗ ≈⟨ cong (cong (cong refl (cong refl (refl'₃ (aux-f₁ wm2)))) refl) refl ⟩
    (([ (inj₂ tt , [] , inj₂ tt) ] • [ [ d ]₂ ]ᵣ • (f *) wm2 ) • semcds cds') • [ [ c1 ]₁ ]ₗ ≈⟨ cong (cong (cong refl (lemma-hdmw'1 d wm2)) refl) refl ⟩
    (([ (inj₂ tt , [] , inj₂ tt) ] • (f *) wm3 • [ [  d3 ]₂ ]ᵣ) • semcds cds') • [ [ c1 ]₁ ]ₗ ≈⟨ cong (cong (cong refl (cong (sym (refl'₃ (aux-f₁ wm3))) refl)) refl) refl ⟩
    (([ (inj₂ tt , [] , inj₂ tt) ] • [ [ wm3 ]ₓ₁ ]ₗ • [ [  d3 ]₂ ]ᵣ) • semcds cds') • [ [ c1 ]₁ ]ₗ ≈⟨ cong (cong (sym assoc) refl) refl ⟩
    ((([ (inj₂ tt , [] , inj₂ tt) ] • [ [ wm3 ]ₓ₁ ]ₗ) • [ [ d3 ]₂ ]ᵣ) • semcds cds') • [ [ c1 ]₁ ]ₗ ≈⟨ cong (cong (cong (lemma-cdε-m wm3) refl) refl) refl ⟩
    ((([ [ wm3 ]ₓ₁ ]ₗ • [ (inj₂ tt , [] , inj₂ tt) ]) • [ [  d3 ]₂ ]ᵣ) • semcds cds') • [ [ c1 ]₁ ]ₗ ≈⟨ cong (cong assoc refl) refl ⟩
    (([ [ wm3 ]ₓ₁ ]ₗ • [ (inj₂ tt , [] , inj₂ tt) ] • [ [  d3 ]₂ ]ᵣ) • semcds cds') • [ [ c1 ]₁ ]ₗ ≈⟨ cong (cong (cong refl (sym (aux-hhd (d3)))) refl) refl ⟩
    (([ [ wm3 ]ₓ₁ ]ₗ • [ (d3 , [] , inj₂ tt) ]) • semcds cds') • [ [ c1 ]₁ ]ₗ ≈⟨ cong assoc refl ⟩
    ([ [ wm3 ]ₓ₁ ]ₗ • [ (d3 , [] , inj₂ tt) ] • semcds cds') • [ [ c1 ]₁ ]ₗ ≈⟨ cong (sym (cong refl (aux-hh2 (d3) cds'))) refl ⟩
    ([ [ wm3 ]ₓ₁ ]ₗ • [ (d3 , cds' , inj₂ tt) ]) • [ [ c1 ]₁ ]ₗ ≈⟨ assoc ⟩
    [ [ wm3 ]ₓ₁ ]ₗ • [ (d3 , cds' , inj₂ tt) ] • [ [ c1 ]₁ ]ₗ ≈⟨ cong refl (sym (aux-hh1 (d3) cds' c1)) ⟩
    [ [ wm3 ]ₓ₁ ]ₗ • [ (d3 , cds' , c1) ] ≈⟨ cong ( refl'₃ (aux-f₁ wm3)) refl ⟩
    (f *) wm3 • [ (d3 , cds' , c1) ] ≈⟨ refl ⟩
    [ x' ]ₓ • [ c' ] ∎
    where
    open SR ws₃

  lemma-cd-wm : ∀ cd m -> let (x' , c') = (hcdm **) cd m in
    [ cd ] • [ m ]ₓ ≈₃ [ x' ]ₓ • [ c' ]
  lemma-cd-wm cd [ x ]ʷ = lemma-cd-m cd x
  lemma-cd-wm cd ε = trans right-unit (sym left-unit)
  lemma-cd-wm cd m@(w • v) =
    let (m' , cd') = (hcdm **) cd m  in
    let (w' , cdw) = (hcdm **) cd w  in
    let (v' , cdv) = (hcdm **) cdw v in
    begin
    [ cd ] • [ w • v ]ₓ ≈⟨ refl ⟩
    [ cd ] • [ w ]ₓ • [ v ]ₓ ≈⟨ sym assoc ⟩
    ([ cd ] • [ w ]ₓ) • [ v ]ₓ ≈⟨ cong (lemma-cd-wm cd w) refl ⟩
    ([ w' ]ₓ • [ cdw ]) • [ v ]ₓ ≈⟨ assoc ⟩
    [ w' ]ₓ • [ cdw ] • [ v ]ₓ ≈⟨ cong refl (lemma-cd-wm cdw v) ⟩
    [ w' ]ₓ • [ v' ]ₓ • [ cdv ] ≈⟨ sym assoc ⟩
    [ m' ]ₓ • [ cd' ] ∎
    where
    open SR ws₃


  hh-cd-b' : C × D -> B -> Word M × C × (D ⊎ ⊤)
  hh-cd-b' (c , d) b with hdb d b
  hh-cd-b' (c , d) b | wm , dt with hcmw c wm
  hh-cd-b' (c , d) b | wm , dt | (wm' , c') = (wm' , c' , dt)

  eval-cdb' : Word M × C × (D ⊎ ⊤) -> Word Y
  eval-cdb' ((wm , c , dt)) = [ wm ]ₓ • [ [ inj₁ c ]₁ ]ₗ • [ [ dt ]₂ ]ᵣ

  lemma-hh-cd-b' : ∀ c d b -> eval-cdb' (hh-cd-b' (c , d) b) ≈₃ eval-cd (c , d) • [ [ b ]ʷ ]ᵣ
  lemma-hh-cd-b' c d b =
    let (wm , d') = hdb d b in
    let (wm' , c') = hcmw c wm in
    begin
    eval-cdb' ( (wm' , c' , d')) ≈⟨ sym assoc ⟩
    ([ wm' ]ₓ • [ [ c' ]ₒ₁ ]ₗ) • [ [ d' ]₂ ]ᵣ ≈⟨ cong (cong (refl'₃ (Eq.sym (aux-f₁ wm'))) refl) refl ⟩
    ([ [ wm' ]ₓ₁ • [ c' ]ₒ₁ ]ₗ) • [ [ d' ]₂ ]ᵣ ≈⟨ cong (sym (AB.lefts (hcmw-hyp c wm))) refl ⟩
    ([ [ c ]ₒ₁ • [ wm ]ₓ₁ ]ₗ) • [ [ d' ]₂ ]ᵣ ≈⟨ cong (cong refl (refl'₃ (Eq.cong [_]ₗ (Eq.refl)))) refl ⟩
    ([ [ c ]ₒ₁ • [ wm ]ₓ₁ ]ₗ) • [ [ d' ]₂ ]ᵣ ≈⟨ assoc ⟩
    [ [ c ]ₒ₁ ]ₗ • [ [ wm ]ₓ₁ ]ₗ • [ [ d' ]₂ ]ᵣ ≈⟨ cong refl (cong (lemma-amal' wm) refl) ⟩
    [ [ c ]ₒ₁ ]ₗ • [ (f₂ *) wm • [ d' ]₂ ]ᵣ ≈⟨ cong refl (sym (AB.rights (hdb-hyp d b))) ⟩
    [ [ c ]ₒ₁ ]ₗ • [ [ d ]ₒ₂ ]ᵣ • [ [ b ]ʷ ]ᵣ  ≈⟨ sym assoc ⟩
    ([ [ c ]ₒ₁ ]ₗ • [ [ d ]ₒ₂ ]ᵣ) • [ [ b ]ʷ ]ᵣ ∎
    where
    open SR ws₃


  aux-hh9 : ∀ d cds c0 d0 -> [ d , cds , inj₂ tt ] • [ c0 , d0 ]ᵢ ≈₃ [ d , (c0 , d0) ∷ cds , inj₂ tt ]
  aux-hh9 d cds c0 d0 = begin
    [ d , cds , inj₂ tt ] • [ c0 , d0 ]ᵢ ≈⟨ cong (aux-hh2 d cds) refl ⟩
    ([ d , [] , inj₂ tt ] • semcds cds) • [ c0 , d0 ]ᵢ ≈⟨ assoc ⟩
    [ d , [] , inj₂ tt ] • semcds cds • [ c0 , d0 ]ᵢ ≈⟨ cong refl refl ⟩
    [ d , [] , inj₂ tt ] • semcds ((c0 , d0) ∷ cds) ≈⟨ sym (aux-hh2 d ((c0 , d0) ∷ cds)) ⟩
    [ d , (c0 , d0) ∷ cds , inj₂ tt ] ∎
    where
    open SR ws₃


  hh : CD -> A ⊎ B -> Word M × CD
  hh (d , cds , c) (inj₁ a) with h₁ c a
  hh (d , cds , c) (inj₁ a) | (wm , c') with hcdws cds wm
  hh (d , cds , c) (inj₁ a) | (wm , c') | (wm' , cds') with hdmw' d wm'
  hh (d , cds , c) (inj₁ a) | (wm , c') | (wm' , cds') | (wm'' , d') = wm'' , d' , cds' , c'
  
  hh (d , cds , inj₁ c) (inj₂ b) with h₂ (inj₂ tt) b
  hh (d , cds , inj₁ c) (inj₂ b) | (wm1 , inj₁ d1) with hcmw c wm1
  hh (d , cds , inj₁ c) (inj₂ b) | (wm1 , inj₁ d1) | (wm2 , c2) with hcdmw (d , cds , inj₂ tt) wm2
  hh (d , cds , inj₁ c) (inj₂ b) | (wm1 , inj₁ d1) | (wm2 , c2) | (wm3 , d3 , cds3 , c3) = wm3 , d3 , ((c2 , d1) ∷ cds3) , inj₂ tt
  hh (d , cds , inj₁ c) (inj₂ b) | (wm1 , inj₂ tt) with hcmw c wm1
  hh (d , cds , inj₁ c) (inj₂ b) | (wm1 , inj₂ tt) | (wm2 , c2) with hcdmw (d , cds , inj₂ tt) wm2
  hh (d , cds , inj₁ c) (inj₂ b) | (wm1 , inj₂ tt) | (wm2 , c2) | (wm3 , d3 , cds3 , c3) = wm3 , d3 , cds3 , inj₁ c2
  
  hh (d , [] , inj₂ tt) (inj₂ b) with h₂ d b
  hh (d , [] , inj₂ tt) (inj₂ b) | (wm1 , d1) = wm1 , d1 , [] , inj₂ tt

  hh (d , ((c0 , d0) ∷ tail) , inj₂ tt) (inj₂ b) with hdb d0 b
  hh (d , ((c0 , d0) ∷ tail) , inj₂ tt) (inj₂ b) | (wm , inj₁ d1) with hcmw c0 wm
  hh (d , ((c0 , d0) ∷ tail) , inj₂ tt) (inj₂ b) | (wm , inj₁ d1) | (wm1 , c1) with (hcdm **) (d , tail , inj₂ tt) wm1
  hh (d , ((c0 , d0) ∷ tail) , inj₂ tt) (inj₂ b) | (wm , inj₁ d1) | (wm1 , c1) | (wm3 , d3 , tail3 , c3) = wm3 ,  d3 , (c1 , d1) ∷ tail3 , inj₂ tt
  hh (d , ((c0 , d0) ∷ tail) , inj₂ tt) (inj₂ b) | (wm , inj₂ tt) with hcmw c0 wm
  hh (d , ((c0 , d0) ∷ tail) , inj₂ tt) (inj₂ b) | (wm , inj₂ tt) | (wm1 , c1) with (hcdm **) (d , tail , inj₂ tt) wm1
  hh (d , ((c0 , d0) ∷ tail) , inj₂ tt) (inj₂ b) | (wm , inj₂ tt) | (wm1 , c1) | (wm3 , d3 , tail3 , c3) = wm3 ,  d3 , tail3 , inj₁ c1



  hh-hyp :  ∀ cd y -> let (x' , c') = hh cd y in
    [ cd ] • [ y ]ʷ ≈₃ [ x' ]ₓ • [ c' ]

  hh-hyp (d , cds , c) (inj₁ a) with h₁ c a | inspect (h₁ c) a
  hh-hyp (d , cds , c) (inj₁ a) | (wm , c') | [ eq1 ]' with hcdws cds wm | inspect (hcdws cds) wm
  hh-hyp (d , cds , c) (inj₁ a) | (wm , c') | [ eq1 ]' | (wm' , cds') | [ eq2 ]' with hdmw' d wm' | inspect (hdmw' d) wm'
  hh-hyp (d , cds , c) (inj₁ a) | (wm , c') | [ eq1 ]' | (wm' , cds') | [ eq2 ]' | (wm'' , d') | [ eq3 ]' rewrite eq3 = begin
    [ d , cds , c ] • [ inj₁ a ]ʷ ≈⟨ refl ⟩
    ([ [ d ]₂ ]ᵣ • semcds cds • [ [ c ]₁ ]ₗ) • [ inj₁ a ]ʷ ≈⟨ cong (sym assoc) refl ⟩
    (([ [ d ]₂ ]ᵣ • semcds cds) • [ [ c ]₁ ]ₗ) • [ inj₁ a ]ʷ ≈⟨ assoc ⟩
    ([ [ d ]₂ ]ᵣ • semcds cds) • [ [ c ]₁ ]ₗ • [ inj₁ a ]ʷ ≈⟨ refl ⟩
    ([ [ d ]₂ ]ᵣ • semcds cds) • [ [ c ]₁ • [ a ]ʷ ]ₗ ≈⟨ cong refl (AB.lefts (h₁-hyp c a)) ⟩
    ([ [ d ]₂ ]ᵣ • semcds cds) • [ [ h₁ c a .proj₁ ]ₓ₁ • [ h₁ c a .proj₂ ]₁ ]ₗ ≡⟨ Eq.cong₂ (λ xx yy → ([ [ d ]₂ ]ᵣ • semcds cds) • [ [ xx ]ₓ₁ • [ yy ]₁ ]ₗ) (Eq.cong proj₁ eq1) (Eq.cong proj₂ eq1) ⟩
    ([ [ d ]₂ ]ᵣ • semcds cds) • [ [ wm ]ₓ₁ • [ c' ]₁ ]ₗ ≈⟨ sym assoc ⟩
    (([ [ d ]₂ ]ᵣ • semcds cds) • [ [ wm ]ₓ₁ ]ₗ) • [ [ c' ]₁ ]ₗ ≈⟨ cong (cong refl (refl'₃ (aux-f₁ wm))) refl ⟩
    (([ [ d ]₂ ]ᵣ • semcds cds) • [ wm ]ₓ) • [ [ c' ]₁ ]ₗ ≈⟨ cong assoc refl ⟩
    ([ [ d ]₂ ]ᵣ • semcds cds • [ wm ]ₓ) • [ [ c' ]₁ ]ₗ ≈⟨ cong (cong refl (lemma-hcdws cds wm)) refl ⟩
    ([ [ d ]₂ ]ᵣ • [ hcdws cds wm .proj₁ ]ₓ • semcds (hcdws cds wm .proj₂)) • [ [ c' ]₁ ]ₗ ≡⟨ Eq.cong₂ (λ xx yy → ([ [ d ]₂ ]ᵣ • [ xx ]ₓ • semcds yy) • [ [ c' ]₁ ]ₗ) (Eq.cong proj₁ eq2) (Eq.cong proj₂ eq2) ⟩
    ([ [ d ]₂ ]ᵣ • [ wm' ]ₓ • semcds cds') • [ [ c' ]₁ ]ₗ ≈⟨ cong (sym assoc) refl ⟩
    (([ [ d ]₂ ]ᵣ • [ wm' ]ₓ) • semcds cds') • [ [ c' ]₁ ]ₗ ≈⟨ cong (cong (cong refl (sym (aux-f₂ wm'))) refl) refl ⟩
    (([ [ d ]₂ • [ wm' ]ₓ₂ ]ᵣ) • semcds cds') • [ [ c' ]₁ ]ₗ ≈⟨ cong (cong (AB.rights (hdmw'-hyp d wm')) refl) refl ⟩
    (([ [ hdmw' d wm' .proj₁ ]ₓ₂ • [ hdmw' d wm' .proj₂ ]₂ ]ᵣ) • semcds cds') • [ [ c' ]₁ ]ₗ ≡⟨ Eq.cong₂  (λ xx yy → ([ [ xx ]ₓ₂ • [ yy ]₂ ]ᵣ • semcds cds') • [ [ c' ]₁ ]ₗ) (Eq.cong proj₁ eq3) (Eq.cong proj₂ eq3) ⟩
    (([ [ wm'' ]ₓ₂ • [ d' ]₂ ]ᵣ) • semcds cds') • [ [ c' ]₁ ]ₗ ≈⟨ refl ⟩
    ([ [ wm'' ]ₓ₂ • [ d' ]₂ ]ᵣ • semcds cds') • [ [ c' ]₁ ]ₗ ≈⟨ assoc ⟩
    ([ [ wm'' ]ₓ₂ ]ᵣ • [ [ d' ]₂ ]ᵣ) • semcds cds' • [ [ c' ]₁ ]ₗ ≈⟨ cong (cong (aux-f₂ wm'') refl) refl ⟩
    ([ wm'' ]ₓ • [ [ d' ]₂ ]ᵣ) • semcds cds' • [ [ c' ]₁ ]ₗ ≈⟨ assoc ⟩
    [ wm'' ]ₓ • [ d' , cds' , c' ] ∎
    where
      open SR ws₃


  hh-hyp (d , cds , inj₁ c) (inj₂ b) with h₂ I₂ b | inspect (h₂ I₂) b
  hh-hyp (d , cds , inj₁ c) (inj₂ b) | (wm1 , inj₁ d1) | [ eq1 ]' with hcmw c wm1 | inspect (hcmw c) wm1
  hh-hyp (d , cds , inj₁ c) (inj₂ b) | (wm1 , inj₁ d1) | [ eq1 ]' | (wm2 , c2) | [ eq2 ]' with hcdmw (d , cds , inj₂ tt) wm2 | inspect (hcdmw (d , cds , inj₂ tt)) wm2
  hh-hyp (d , cds , inj₁ c) (inj₂ b) | (wm1 , inj₁ d1) | [ eq1 ]' | (wm2 , c2) | [ eq2 ]' | (wm3 , d3 , cds3 , c3) | [ eq3 ]' = begin
    [ d , cds , inj₁ c ] • [ inj₂ b ]ʷ ≈⟨ cong refl (sym left-unit) ⟩
    [ d , cds , inj₁ c ] • ε • [ inj₂ b ]ʷ ≈⟨ refl ⟩
    [ d , cds , inj₁ c ] • [ ε • [ b ]ʷ ]ᵣ ≈⟨ cong refl (AB.rights (h₂-hyp I₂ b)) ⟩
    [ d , cds , inj₁ c ] • [ [ h₂ I₂ b .proj₁ ]ₓ₂ • [ h₂ I₂ b .proj₂ ]₂ ]ᵣ ≡⟨ Eq.cong₂ (\xx yy -> [ d , cds , inj₁ c ] • [ [ xx ]ₓ₂ • [ yy ]₂ ]ᵣ) (Eq.cong proj₁ eq1) (Eq.cong proj₂ eq1)  ⟩
    [ d , cds , inj₁ c ] • [ [ wm1 ]ₓ₂ • [ inj₁ d1 ]₂ ]ᵣ ≈⟨ refl ⟩
    [ d , cds , inj₁ c ] • [ [ wm1 ]ₓ₂ ]ᵣ • [ [ inj₁ d1 ]₂ ]ᵣ ≈⟨ cong refl (cong (aux-f₂ wm1) refl) ⟩
    [ d , cds , inj₁ c ] • [ wm1 ]ₓ • [ [ inj₁ d1 ]₂ ]ᵣ ≈⟨ sym assoc ⟩
    ([ d , cds , inj₁ c ] • [ wm1 ]ₓ) • [ [ inj₁ d1 ]₂ ]ᵣ ≈⟨ cong (cong (aux-hh1 d cds (inj₁ c)) refl) refl ⟩
    (([ d , cds , inj₂ tt ] • [ [ c ]ₒ₁ ]ₗ) • [ wm1 ]ₓ) • [ [ inj₁ d1 ]₂ ]ᵣ ≈⟨ cong assoc refl ⟩
    ([ d , cds , inj₂ tt ] • [ [ c ]ₒ₁ ]ₗ • [ wm1 ]ₓ) • [ [ inj₁ d1 ]₂ ]ᵣ ≈⟨ cong (cong refl (cong refl (sym (aux-f₁' wm1)))) refl ⟩
    ([ d , cds , inj₂ tt ] • [ [ c ]ₒ₁ • [ wm1 ]ₓ₁ ]ₗ) • [ [ inj₁ d1 ]₂ ]ᵣ ≈⟨ cong (cong refl (AB.lefts (hcmw-hyp c wm1))) refl ⟩
    ([ d , cds , inj₂ tt ] • [ [ hcmw c wm1 .proj₁ ]ₓ₁ • [ hcmw c wm1 .proj₂ ]ₒ₁ ]ₗ) • [ [ inj₁ d1 ]₂ ]ᵣ ≡⟨ Eq.cong₂ (\ xx yy -> ([ d , cds , inj₂ tt ] • [ [ xx ]ₓ₁ • [ yy ]ₒ₁ ]ₗ) • [ [ inj₁ d1 ]₂ ]ᵣ) (Eq.cong proj₁ eq2) (Eq.cong proj₂ eq2) ⟩
    ([ d , cds , inj₂ tt ] • [ [ wm2 ]ₓ₁ • [ c2 ]ₒ₁ ]ₗ) • [ [ inj₁ d1 ]₂ ]ᵣ ≈⟨ cong (sym assoc) refl ⟩
    (([ d , cds , inj₂ tt ] • [ [ wm2 ]ₓ₁ ]ₗ) • [ [ c2 ]ₒ₁ ]ₗ) • [ [ inj₁ d1 ]₂ ]ᵣ ≈⟨ cong (cong (cong refl (aux-f₁' wm2)) refl) refl ⟩
    (([ d , cds , inj₂ tt ] • [ wm2 ]ₓ) • [ [ c2 ]ₒ₁ ]ₗ) • [ [ inj₁ d1 ]₂ ]ᵣ ≈⟨ cong (cong (lemma-cd-wm (d , cds , inj₂ tt) wm2) refl) refl ⟩
    (([ hcdmw (d , cds , inj₂ tt) wm2 .proj₁ ]ₓ • [ hcdmw (d , cds , inj₂ tt) wm2 .proj₂ ]) • [ [ c2 ]ₒ₁ ]ₗ) • [ [ inj₁ d1 ]₂ ]ᵣ ≈⟨ assoc ⟩
    ([ hcdmw (d , cds , inj₂ tt) wm2 .proj₁ ]ₓ • [ hcdmw (d , cds , inj₂ tt) wm2 .proj₂ ]) • [ [ c2 ]ₒ₁ ]ₗ • [ [ inj₁ d1 ]₂ ]ᵣ ≈⟨ refl ⟩
    ([ hcdmw (d , cds , inj₂ tt) wm2 .proj₁ ]ₓ • [ hcdmw (d , cds , inj₂ tt) wm2 .proj₂ ]) • [ c2 , d1 ]ᵢ ≡⟨ Eq.cong₂ (λ xx yy → ([ xx ]ₓ • [ yy ]) • [ c2 , d1 ]ᵢ) (Eq.cong proj₁ eq3) (Eq.cong proj₂ eq3) ⟩
    ([ wm3 ]ₓ • [ d3 , cds3 , c3 ]) • [ c2 , d1 ]ᵢ ≡⟨ Eq.cong (λ xx → ([ wm3 ]ₓ • [ d3 , cds3 , xx ]) • [ c2 , d1 ]ᵢ) claim ⟩
    ([ wm3 ]ₓ • [ d3 , cds3 , inj₂ tt ]) • [ c2 , d1 ]ᵢ ≈⟨ assoc ⟩
    [ wm3 ]ₓ • [ d3 , cds3 , inj₂ tt ] • [ c2 , d1 ]ᵢ ≈⟨ cong refl (aux-hh9 d3 cds3 c2 d1) ⟩
    [ wm3 ]ₓ • [ d3 , (c2 , d1) ∷ cds3 , inj₂ tt ] ∎
    where
      claim : c3 ≡ inj₂ tt
      claim = Eq.trans (Eq.sym ((Eq.cong (proj₂ ∘ proj₂ ∘ proj₂) eq3))) (lemma-hcdmw d cds (inj₂ tt) Eq.refl wm2)
      open SR ws₃

  hh-hyp (d , cds , inj₁ c) (inj₂ b) | (wm1 , inj₂ tt) | [ eq1 ]' with hcmw c wm1 | inspect (hcmw c) wm1
  hh-hyp (d , cds , inj₁ c) (inj₂ b) | (wm1 , inj₂ tt) | [ eq1 ]' | (wm2 , c2) | [ eq2 ]' with hcdmw (d , cds , inj₂ tt) wm2 | inspect (hcdmw (d , cds , inj₂ tt)) wm2
  hh-hyp (d , cds , inj₁ c) (inj₂ b) | (wm1 , inj₂ tt) | [ eq1 ]' | (wm2 , c2) | [ eq2 ]' | (wm3 , d3 , cds3 , c3) | [ eq3 ]' = begin
    [ d , cds , inj₁ c ] • [ inj₂ b ]ʷ ≈⟨ cong refl (sym left-unit) ⟩
    [ d , cds , inj₁ c ] • ε • [ inj₂ b ]ʷ ≈⟨ refl ⟩
    [ d , cds , inj₁ c ] • [ ε • [ b ]ʷ ]ᵣ ≈⟨ cong refl (AB.rights (h₂-hyp I₂ b)) ⟩
    [ d , cds , inj₁ c ] • [ [ h₂ I₂ b .proj₁ ]ₓ₂ • [ h₂ I₂ b .proj₂ ]₂ ]ᵣ ≡⟨ Eq.cong₂ (\xx yy -> [ d , cds , inj₁ c ] • [ [ xx ]ₓ₂ • [ yy ]₂ ]ᵣ) (Eq.cong proj₁ eq1) (Eq.cong proj₂ eq1)  ⟩
    [ d , cds , inj₁ c ] • [ [ wm1 ]ₓ₂ • [ inj₂ tt ]₂ ]ᵣ ≈⟨ refl ⟩
    [ d , cds , inj₁ c ] • [ [ wm1 ]ₓ₂ ]ᵣ • [ [ inj₂ tt ]₂ ]ᵣ ≈⟨ cong refl (cong (aux-f₂ wm1) refl) ⟩
    [ d , cds , inj₁ c ] • [ wm1 ]ₓ • [ [ inj₂ tt ]₂ ]ᵣ ≈⟨ sym assoc ⟩
    ([ d , cds , inj₁ c ] • [ wm1 ]ₓ) • [ [ inj₂ tt ]₂ ]ᵣ ≈⟨ cong (cong (aux-hh1 d cds (inj₁ c)) refl) refl ⟩
    (([ d , cds , inj₂ tt ] • [ [ c ]ₒ₁ ]ₗ) • [ wm1 ]ₓ) • [ [ inj₂ tt ]₂ ]ᵣ ≈⟨ cong assoc refl ⟩
    ([ d , cds , inj₂ tt ] • [ [ c ]ₒ₁ ]ₗ • [ wm1 ]ₓ) • [ [ inj₂ tt ]₂ ]ᵣ ≈⟨ cong (cong refl (cong refl (sym (aux-f₁' wm1)))) refl ⟩
    ([ d , cds , inj₂ tt ] • [ [ c ]ₒ₁ • [ wm1 ]ₓ₁ ]ₗ) • [ [ inj₂ tt ]₂ ]ᵣ ≈⟨ cong (cong refl (AB.lefts (hcmw-hyp c wm1))) refl ⟩
    ([ d , cds , inj₂ tt ] • [ [ hcmw c wm1 .proj₁ ]ₓ₁ • [ hcmw c wm1 .proj₂ ]ₒ₁ ]ₗ) • [ [ inj₂ tt ]₂ ]ᵣ ≡⟨ Eq.cong₂ (\ xx yy -> ([ d , cds , inj₂ tt ] • [ [ xx ]ₓ₁ • [ yy ]ₒ₁ ]ₗ) • [ [ inj₂ tt ]₂ ]ᵣ) (Eq.cong proj₁ eq2) (Eq.cong proj₂ eq2) ⟩
    ([ d , cds , inj₂ tt ] • [ [ wm2 ]ₓ₁ • [ c2 ]ₒ₁ ]ₗ) • [ [ inj₂ tt ]₂ ]ᵣ ≈⟨ cong (sym assoc) refl ⟩
    (([ d , cds , inj₂ tt ] • [ [ wm2 ]ₓ₁ ]ₗ) • [ [ c2 ]ₒ₁ ]ₗ) • [ [ inj₂ tt ]₂ ]ᵣ ≈⟨ cong (cong (cong refl (aux-f₁' wm2)) refl) refl ⟩
    (([ d , cds , inj₂ tt ] • [ wm2 ]ₓ) • [ [ c2 ]ₒ₁ ]ₗ) • [ [ inj₂ tt ]₂ ]ᵣ ≈⟨ cong (cong (lemma-cd-wm (d , cds , inj₂ tt) wm2) refl) refl ⟩
    (([ hcdmw (d , cds , inj₂ tt) wm2 .proj₁ ]ₓ • [ hcdmw (d , cds , inj₂ tt) wm2 .proj₂ ]) • [ [ c2 ]ₒ₁ ]ₗ) • [ [ inj₂ tt ]₂ ]ᵣ ≈⟨ assoc ⟩
    ([ hcdmw (d , cds , inj₂ tt) wm2 .proj₁ ]ₓ • [ hcdmw (d , cds , inj₂ tt) wm2 .proj₂ ]) • [ [ c2 ]ₒ₁ ]ₗ • [ [ inj₂ tt ]₂ ]ᵣ ≈⟨ cong refl right-unit ⟩
    ([ hcdmw (d , cds , inj₂ tt) wm2 .proj₁ ]ₓ • [ hcdmw (d , cds , inj₂ tt) wm2 .proj₂ ]) • [ [ c2 ]ₒ₁ ]ₗ ≡⟨ Eq.cong₂ (λ xx yy → ([ xx ]ₓ • [ yy ]) • [ [ c2 ]ₒ₁ ]ₗ) (Eq.cong proj₁ eq3) (Eq.cong proj₂ eq3) ⟩ 
     ([ wm3 ]ₓ • [ d3 , cds3 , c3 ]) • [ [ c2 ]ₒ₁ ]ₗ ≡⟨ Eq.cong (λ xx → ([ wm3 ]ₓ • [ d3 , cds3 , xx ]) • [ [ c2 ]ₒ₁ ]ₗ) claim ⟩
    ([ wm3 ]ₓ • [ d3 , cds3 , inj₂ tt ]) • [ [ c2 ]ₒ₁ ]ₗ ≈⟨ assoc ⟩
    [ wm3 ]ₓ • [ d3 , cds3 , inj₂ tt ] • [ [ c2 ]ₒ₁ ]ₗ ≈⟨ cong refl (sym (aux-hh1 d3 cds3 (inj₁ c2))) ⟩
    [ wm3 ]ₓ • [ d3 , cds3 , inj₁ c2 ] ∎
    where
      open SR ws₃
      claim : c3 ≡ inj₂ tt
      claim = Eq.trans (Eq.sym ((Eq.cong (proj₂ ∘ proj₂ ∘ proj₂) eq3))) (lemma-hcdmw d cds (inj₂ tt) Eq.refl wm2)

  hh-hyp (d , [] , inj₂ tt) (inj₂ b) with h₂ d b | inspect (h₂ d) b
  hh-hyp (d , [] , inj₂ tt) (inj₂ b) | (wm1 , d1) | [ Eq.refl ]' = begin
    [ d , [] , inj₂ tt ] • [ inj₂ b ]ʷ ≈⟨ refl ⟩
    ([ [ d ]₂ ]ᵣ • ε • ε) • [ inj₂ b ]ʷ ≈⟨ cong (trans (cong refl left-unit) right-unit) refl ⟩
    ([ [ d ]₂ ]ᵣ) • [ inj₂ b ]ʷ ≈⟨ refl ⟩
    [ [ d ]₂ • [ b ]ʷ ]ᵣ ≈⟨ AB.rights (h₂-hyp d b) ⟩
    [ [ wm1 ]ₓ₂ • [ d1 ]₂ ]ᵣ ≈⟨ cong (aux-f₂ wm1) (sym (trans right-unit right-unit)) ⟩
    [ wm1 ]ₓ • ([ [ d1 ]₂ ]ᵣ • ε) • ε ≈⟨ cong refl assoc ⟩
    [ wm1 ]ₓ • [ d1 , [] , inj₂ tt ] ∎
    where
      open SR ws₃


  hh-hyp (d , ((c0 , d0) ∷ tail) , inj₂ tt) (inj₂ b) with hdb d0 b | inspect (hdb d0) b
  hh-hyp (d , ((c0 , d0) ∷ tail) , inj₂ tt) (inj₂ b) | (wm , inj₁ d1) | [ eq1 ]' with hcmw c0 wm | inspect (hcmw c0) wm
  hh-hyp (d , ((c0 , d0) ∷ tail) , inj₂ tt) (inj₂ b) | (wm , inj₁ d1) | [ eq1 ]' | (wm1 , c1) | [ Eq.refl ]' with (hcdm **) (d , tail , inj₂ tt) wm1 | inspect ((hcdm **) (d , tail , inj₂ tt)) wm1
  hh-hyp (d , ((c0 , d0) ∷ tail) , inj₂ tt) (inj₂ b) | (wm , inj₁ d1) | [ eq1 ]' | (wm1 , c1) | [ Eq.refl ]' | (wm3 , d3 , tail3 , c3) | [ Eq.refl ]' = begin
    [ d , (c0 , d0) ∷ tail , inj₂ tt ] • [ inj₂ b ]ʷ ≈⟨ refl ⟩
    ([ [ d ]₂ ]ᵣ • semcds ((c0 , d0) ∷ tail) • ε) • [ inj₂ b ]ʷ ≈⟨ cong (cong refl right-unit) refl ⟩
    ([ [ d ]₂ ]ᵣ • semcds ((c0 , d0) ∷ tail)) • [ inj₂ b ]ʷ ≈⟨ refl ⟩
    ([ [ d ]₂ ]ᵣ • semcds (tail) • [ (c0 , d0) ]ᵢ) • [ inj₂ b ]ʷ ≈⟨ assoc ⟩
    [ [ d ]₂ ]ᵣ • (semcds (tail) • [ (c0 , d0) ]ᵢ) • [ inj₂ b ]ʷ ≈⟨ cong refl assoc ⟩
    [ [ d ]₂ ]ᵣ • semcds (tail) • [ (c0 , d0) ]ᵢ • [ inj₂ b ]ʷ ≈⟨ cong refl (cong refl assoc) ⟩
    [ [ d ]₂ ]ᵣ • semcds (tail) • [ [ c0 ]ₒ₁ ]ₗ • [ [ d0 ]ₒ₂ ]ᵣ • [ inj₂ b ]ʷ ≈⟨ refl ⟩
    [ [ d ]₂ ]ᵣ • semcds (tail) • [ [ c0 ]ₒ₁ ]ₗ • [ [ d0 ]ₒ₂ • [ b ]ʷ ]ᵣ ≈⟨ cong refl (cong refl (cong refl (AB.rights (hdb-hyp d0 b)))) ⟩
    [ [ d ]₂ ]ᵣ • semcds (tail) • [ [ c0 ]ₒ₁ ]ₗ • [ [ hdb d0 b .proj₁ ]ₓ₂ • [ hdb d0 b .proj₂ ]₂ ]ᵣ ≡⟨ Eq.cong₂ (\xx yy -> [ [ d ]₂ ]ᵣ • semcds (tail) • [ [ c0 ]ₒ₁ ]ₗ • [ [ xx ]ₓ₂ • [ yy ]₂ ]ᵣ) (Eq.cong proj₁ eq1) (Eq.cong proj₂ eq1) ⟩
    [ [ d ]₂ ]ᵣ • semcds (tail) • [ [ c0 ]ₒ₁ ]ₗ • [ [ wm ]ₓ₂ • [ inj₁ d1 ]₂ ]ᵣ ≈⟨ cong refl (sym (cong refl assoc)) ⟩
    [ [ d ]₂ ]ᵣ • semcds (tail) • ([ [ c0 ]ₒ₁ ]ₗ • [ [ wm ]ₓ₂ ]ᵣ) • [ [ inj₁ d1 ]₂ ]ᵣ ≈⟨ cong refl (cong refl (cong (cong refl (sym (lemma-amal' wm))) refl )) ⟩
    [ [ d ]₂ ]ᵣ • semcds (tail) • ([ [ c0 ]ₒ₁ ]ₗ • [ [ wm ]ₓ₁ ]ₗ) • [ [ inj₁ d1 ]₂ ]ᵣ ≈⟨ cong refl (cong refl (cong (AB.lefts (hcmw-hyp c0 wm)) refl)) ⟩
    [ [ d ]₂ ]ᵣ • semcds (tail) • ([ [ wm1 ]ₓ₁ • [ c1 ]ₒ₁ ]ₗ) • [ [ inj₁ d1 ]₂ ]ᵣ ≈⟨ cong refl (cong refl (sym left-unit)) ⟩
    [ [ d ]₂ ]ᵣ • semcds (tail) • ε • ([ [ wm1 ]ₓ₁ • [ c1 ]ₒ₁ ]ₗ) • [ [ inj₁ d1 ]₂ ]ᵣ ≈⟨ sym (cong refl assoc) ⟩
    [ [ d ]₂ ]ᵣ • (semcds (tail) • ε) • ([ [ wm1 ]ₓ₁ • [ c1 ]ₒ₁ ]ₗ) • [ [ inj₁ d1 ]₂ ]ᵣ ≈⟨ sym assoc ⟩
    ([ [ d ]₂ ]ᵣ • semcds (tail) • ε) • ([ [ wm1 ]ₓ₁ • [ c1 ]ₒ₁ ]ₗ) • [ [ inj₁ d1 ]₂ ]ᵣ ≈⟨ refl ⟩
    [ d , tail , inj₂ tt ] • ([ [ wm1 ]ₓ₁ • [ c1 ]ₒ₁ ]ₗ) • [ [ inj₁ d1 ]₂ ]ᵣ ≈⟨ cong refl assoc ⟩
    [ d , tail , inj₂ tt ] • [ [ wm1 ]ₓ₁ ]ₗ • [ [ c1 ]ₒ₁ ]ₗ • [ [ inj₁ d1 ]₂ ]ᵣ ≈⟨ sym assoc ⟩
    ([ d , tail , inj₂ tt ] • [ [ wm1 ]ₓ₁ ]ₗ) • [ [ c1 ]ₒ₁ ]ₗ • [ [ inj₁ d1 ]₂ ]ᵣ ≈⟨ cong (cong refl (aux-f₁' wm1)) refl  ⟩
    ([ d , tail , inj₂ tt ] • [ wm1 ]ₓ) • [ [ c1 ]ₒ₁ ]ₗ • [ [ inj₁ d1 ]₂ ]ᵣ ≈⟨ cong (lemma-cd-wm (d , tail , inj₂ tt) wm1) refl ⟩
    ([ wm3 ]ₓ • [ d3 , tail3 , c3 ]) • [ [ c1 ]ₒ₁ ]ₗ • [ [ inj₁ d1 ]₂ ]ᵣ ≡⟨ Eq.cong (\xx -> ([ wm3 ]ₓ • [ d3 , tail3 , xx ]) • [ [ c1 ]ₒ₁ ]ₗ • [ [ inj₁ d1 ]₂ ]ᵣ) claim ⟩
    ([ wm3 ]ₓ • [ d3 , tail3 , inj₂ tt ]) • [ [ c1 ]ₒ₁ ]ₗ • [ [ inj₁ d1 ]₂ ]ᵣ ≈⟨ refl ⟩
    ([ wm3 ]ₓ • [ d3 , tail3 , inj₂ tt ]) • [ c1 , d1 ]ᵢ ≈⟨ assoc ⟩
    [ wm3 ]ₓ • [ d3 , tail3 , inj₂ tt ] • [ c1 , d1 ]ᵢ ≈⟨ cong refl (aux-hh9 d3 tail3 c1 d1) ⟩
    [ wm3 ]ₓ • [ d3 , (c1 , d1) ∷ tail3 , inj₂ tt ] ∎
    where
      open SR ws₃
      claim : c3 ≡ inj₂ tt
      claim = lemma-hcdmw d tail (inj₂ tt) Eq.refl wm1

  hh-hyp (d , ((c0 , d0) ∷ tail) , inj₂ tt) (inj₂ b) | (wm , inj₂ tt) | [ eq1 ]' with hcmw c0 wm | inspect (hcmw c0) wm
  hh-hyp (d , ((c0 , d0) ∷ tail) , inj₂ tt) (inj₂ b) | (wm , inj₂ tt) | [ eq1 ]' | (wm1 , c1) | [ Eq.refl ]' with (hcdm **) (d , tail , inj₂ tt) wm1 | inspect ((hcdm **) (d , tail , inj₂ tt)) wm1
  hh-hyp (d , ((c0 , d0) ∷ tail) , inj₂ tt) (inj₂ b) | (wm , inj₂ tt) | [ eq1 ]' | (wm1 , c1) | [ Eq.refl ]' | (wm3 , d3 , tail3 , c3) | [ Eq.refl ]' = begin
    [ d , (c0 , d0) ∷ tail , inj₂ tt ] • [ inj₂ b ]ʷ ≈⟨ refl ⟩
    ([ [ d ]₂ ]ᵣ • semcds ((c0 , d0) ∷ tail) • ε) • [ inj₂ b ]ʷ ≈⟨ cong (cong refl right-unit) refl ⟩
    ([ [ d ]₂ ]ᵣ • semcds ((c0 , d0) ∷ tail)) • [ inj₂ b ]ʷ ≈⟨ refl ⟩
    ([ [ d ]₂ ]ᵣ • semcds (tail) • [ (c0 , d0) ]ᵢ) • [ inj₂ b ]ʷ ≈⟨ assoc ⟩
    [ [ d ]₂ ]ᵣ • (semcds (tail) • [ (c0 , d0) ]ᵢ) • [ inj₂ b ]ʷ ≈⟨ cong refl assoc ⟩
    [ [ d ]₂ ]ᵣ • semcds (tail) • [ (c0 , d0) ]ᵢ • [ inj₂ b ]ʷ ≈⟨ cong refl (cong refl assoc) ⟩
    [ [ d ]₂ ]ᵣ • semcds (tail) • [ [ c0 ]ₒ₁ ]ₗ • [ [ d0 ]ₒ₂ ]ᵣ • [ inj₂ b ]ʷ ≈⟨ refl ⟩
    [ [ d ]₂ ]ᵣ • semcds (tail) • [ [ c0 ]ₒ₁ ]ₗ • [ [ d0 ]ₒ₂ • [ b ]ʷ ]ᵣ ≈⟨ cong refl (cong refl (cong refl (AB.rights (hdb-hyp d0 b)))) ⟩
    [ [ d ]₂ ]ᵣ • semcds (tail) • [ [ c0 ]ₒ₁ ]ₗ • [ [ hdb d0 b .proj₁ ]ₓ₂ • [ hdb d0 b .proj₂ ]₂ ]ᵣ ≡⟨ Eq.cong₂ (\xx yy -> [ [ d ]₂ ]ᵣ • semcds (tail) • [ [ c0 ]ₒ₁ ]ₗ • [ [ xx ]ₓ₂ • [ yy ]₂ ]ᵣ) (Eq.cong proj₁ eq1) (Eq.cong proj₂ eq1) ⟩
    [ [ d ]₂ ]ᵣ • semcds (tail) • [ [ c0 ]ₒ₁ ]ₗ • [ [ wm ]ₓ₂ • [ inj₂ tt ]₂ ]ᵣ ≈⟨ cong refl (sym (cong refl assoc)) ⟩
    [ [ d ]₂ ]ᵣ • semcds (tail) • ([ [ c0 ]ₒ₁ ]ₗ • [ [ wm ]ₓ₂ ]ᵣ) • [ [ inj₂ tt ]₂ ]ᵣ ≈⟨ cong refl (cong refl (cong (cong refl (sym (lemma-amal' wm))) refl )) ⟩
    [ [ d ]₂ ]ᵣ • semcds (tail) • ([ [ c0 ]ₒ₁ ]ₗ • [ [ wm ]ₓ₁ ]ₗ) • [ [ inj₂ tt ]₂ ]ᵣ ≈⟨ cong refl (cong refl (cong (AB.lefts (hcmw-hyp c0 wm)) refl)) ⟩
    [ [ d ]₂ ]ᵣ • semcds (tail) • ([ [ wm1 ]ₓ₁ • [ c1 ]ₒ₁ ]ₗ) • [ [ inj₂ tt ]₂ ]ᵣ ≈⟨ cong refl (cong refl (sym left-unit)) ⟩
    [ [ d ]₂ ]ᵣ • semcds (tail) • ε • ([ [ wm1 ]ₓ₁ • [ c1 ]ₒ₁ ]ₗ) • [ [ inj₂ tt ]₂ ]ᵣ ≈⟨ sym (cong refl assoc) ⟩
    [ [ d ]₂ ]ᵣ • (semcds (tail) • ε) • ([ [ wm1 ]ₓ₁ • [ c1 ]ₒ₁ ]ₗ) • [ [ inj₂ tt ]₂ ]ᵣ ≈⟨ sym assoc ⟩
    ([ [ d ]₂ ]ᵣ • semcds (tail) • ε) • ([ [ wm1 ]ₓ₁ • [ c1 ]ₒ₁ ]ₗ) • [ [ inj₂ tt ]₂ ]ᵣ ≈⟨ refl ⟩
    [ d , tail , inj₂ tt ] • ([ [ wm1 ]ₓ₁ • [ c1 ]ₒ₁ ]ₗ) • [ [ inj₂ tt ]₂ ]ᵣ ≈⟨ cong refl assoc ⟩
    [ d , tail , inj₂ tt ] • [ [ wm1 ]ₓ₁ ]ₗ • [ [ c1 ]ₒ₁ ]ₗ • [ [ inj₂ tt ]₂ ]ᵣ ≈⟨ sym assoc ⟩
    ([ d , tail , inj₂ tt ] • [ [ wm1 ]ₓ₁ ]ₗ) • [ [ c1 ]ₒ₁ ]ₗ • [ [ inj₂ tt ]₂ ]ᵣ ≈⟨ cong (cong refl (aux-f₁' wm1)) refl  ⟩
    ([ d , tail , inj₂ tt ] • [ wm1 ]ₓ) • [ [ c1 ]ₒ₁ ]ₗ • [ [ inj₂ tt ]₂ ]ᵣ ≈⟨ cong (lemma-cd-wm (d , tail , inj₂ tt) wm1) refl ⟩
    ([ wm3 ]ₓ • [ d3 , tail3 , c3 ]) • [ [ c1 ]ₒ₁ ]ₗ • [ [ inj₂ tt ]₂ ]ᵣ ≡⟨ Eq.cong (\xx -> ([ wm3 ]ₓ • [ d3 , tail3 , xx ]) • [ [ c1 ]ₒ₁ ]ₗ • [ [ inj₂ tt ]₂ ]ᵣ) claim ⟩
    ([ wm3 ]ₓ • [ d3 , tail3 , inj₂ tt ]) • [ [ c1 ]ₒ₁ ]ₗ • [ [ inj₂ tt ]₂ ]ᵣ ≈⟨ cong refl right-unit ⟩
    ([ wm3 ]ₓ • [ d3 , tail3 , inj₂ tt ]) • [ [ c1 ]ₒ₁ ]ₗ ≈⟨ assoc ⟩
    [ wm3 ]ₓ • [ d3 , tail3 , inj₂ tt ] • [ [ c1 ]ₒ₁ ]ₗ ≈⟨ cong refl (sym (aux-hh1 d3 tail3 (inj₁ c1))) ⟩
    [ wm3 ]ₓ • [ d3 , tail3 , inj₁ c1 ] ∎
    where
      open SR ws₃
      claim : c3 ≡ inj₂ tt
      claim = lemma-hcdmw d tail (inj₂ tt) Eq.refl wm1




  hh-hyp-w :  ∀ cd y -> let (x' , c') = (hh **) cd y in
    [ cd ] • y ≈₃ [ x' ]ₓ • [ c' ]
  hh-hyp-w cd [ x ]ʷ = hh-hyp cd x
  hh-hyp-w cd ε = _≈₃_.trans _≈₃_.right-unit (_≈₃_.sym _≈₃_.left-unit)
  hh-hyp-w cd (y • y₁) with (hh **) cd y | inspect ((hh **) cd) y | hh-hyp-w cd y
  ... | (wm , cd') | [ Eq.refl ]' | ih with  (hh **) cd' y₁ | inspect ((hh **) cd') y₁ | hh-hyp-w cd' y₁
  ... | (wm2 , cd2) | [ Eq.refl ]' | ih2 =
    begin
    [ cd ] • (y • y₁) ≈⟨ _≈₃_.sym _≈₃_.assoc ⟩
    ([ cd ] • y) • y₁ ≈⟨ cong ih refl ⟩
    ([ wm ]ₓ • [ cd' ]) • y₁ ≈⟨ _≈₃_.assoc ⟩
    [ wm ]ₓ • [ cd' ] • y₁ ≈⟨ _≈₃_.cong _≈₃_.refl ih2 ⟩
    [ wm ]ₓ • [ wm2 ]ₓ • [ cd2 ] ≈⟨ _≈₃_.sym _≈₃_.assoc ⟩
    [ wm • wm2 ]ₓ • [ cd2 ] ∎
    where
      open SR ws₃


  open CosetNF-CT-Assumptions-And-Theorems-Packed CA₁ renaming (h-wd-ax to h-wd-ax₁ ; h-wd to h-wd₁ ; f-wd to f-wd₁ ; h-wd-m to h-wd-m₁) using (hcmw' ; lemma-h**=hcmw' ; lemma-h**=hcmw ; hcmw-cong ; hcmw-cong2 ; hcmw-cong' ; hcmw-cong'2 ; htme ; hcme) public
  open CosetNF-CT-Assumptions-And-Theorems-Packed CA₂ renaming (h-wd-ax to h-wd-ax₂ ; h-wd to h-wd₂ ; f-wd to f-wd₂ ; h-wd-m to h-wd-m₂ ; hcmw-cong to hdmw-cong ; hcmw-cong2 to hdmw-cong2 ; hcmw-cong' to hdmw-cong' ; hcmw-cong'2 to hdmw-cong'2 ; lemma-h**=hcmw' to lemma-h**=hdmw' ; htme to htme₂ ; hcme to hdme) using () public



  hcxd1-m : (C × D) -> Word M -> Word M × (C × D)
  hcxd1-m (c , d) wm with hdmw d wm
  hcxd1-m (c , d) wm | (wm1 , d1) with hcmw c wm1
  hcxd1-m (c , d) wm | (wm1 , d1) | (wm2 , c2) = (wm2 , c2 , d1)

  hcxds-m : List (C × D) -> Word M -> Word M × List (C × D)
  hcxds-m [] wm = wm , []
  hcxds-m (h ∷ t) wm with hcxd1-m h wm
  hcxds-m (h ∷ t) wm | (wm1 , cd1) with hcxds-m t wm1
  hcxds-m (h ∷ t) wm | (wm1 , cd1) | (wm2 , cds2) = wm2 , cd1 ∷ cds2

  hcd-m : CD -> Word M -> Word M × CD
  hcd-m cd@(d , cds , c) wm with hcmw' c wm
  hcd-m cd@(d , cds , c) wm | (wm1 , c1) with hcxds-m cds wm1
  hcd-m cd@(d , cds , c) wm | (wm1 , c1) | wm2 , cds2 with hdmw' d wm2
  hcd-m cd@(d , cds , c) wm | (wm1 , c1) | wm2 , cds2 | (wm3 , d3) = wm3 , d3 , cds2 , c1


  hcd-ma : CD -> Word A -> Word M × CD
  hcd-ma (d , cds , c) w with (h₁ **) c w
  hcd-ma (d , cds , c) w | (wm1 , c1) with hcxds-m cds wm1
  hcd-ma (d , cds , c) w | (wm1 , c1) | (wm2 , cds2) with hdmw' d wm2
  hcd-ma (d , cds , c) w | (wm1 , c1) | (wm2 , cds2) | (wm3 , d3) = (wm3 , d3 , cds2 , c1)


  hcxd1-mb : C × D -> Word B -> Word M × C × D ⊎ Word M × C
  hcxd1-mb (c , d) w with (h₂ **) (inj₁ d) w
  hcxd1-mb (c , d) w | wm1 , inj₁ d' with hcmw c wm1
  hcxd1-mb (c , d) w | wm1 , inj₁ d' | (wm2 , c2) = inj₁ (wm2 , c2 , d')
  hcxd1-mb (c , d) w | wm1 , inj₂ tt with hcmw c wm1
  hcxd1-mb (c , d) w | wm1 , inj₂ tt | (wm2 , c2) = inj₂ (wm2 , c2)

  hcxd1-mb' : C × D -> Word B -> Word M × (C × (D ⊎ ⊤))
  hcxd1-mb' (c , d) w with (h₂ **) (inj₁ d) w
  hcxd1-mb' (c , d) w | wm1 , dt1 with hcmw c wm1
  hcxd1-mb' (c , d) w | wm1 , dt1 | (wm2 , c2) = wm2 , c2 , dt1


  aux-hcm'=h₁**2 : ∀ c m -> hcm' c m ≡ hcmw' c [ m ]ʷ
  aux-hcm'=h₁**2 (inj₁ x) m = Eq.refl
  aux-hcm'=h₁**2 (inj₂ y) m = Eq.refl

  aux-hdm=h₂**2 : ∀ d b -> (h₂ **) (inj₁ d) [ b ]ʷ ≡ hdb d b
  aux-hdm=h₂**2 d b = Eq.refl


  aux-h₁=h₁** : ∀ c a -> h₁ c a ≡ (h₁ **) c [ a ]ʷ
  aux-h₁=h₁** (inj₁ x) a = Eq.refl
  aux-h₁=h₁** (inj₂ y) a = Eq.refl


  aux-hcdw=hcxd1-m : ∀ cd wm -> hcdw cd wm ≡ hcxd1-m cd wm
  aux-hcdw=hcxd1-m cd [ x ]ʷ = Eq.refl
  aux-hcdw=hcxd1-m cd ε = Eq.refl
  aux-hcdw=hcxd1-m cd (wm • wm₁) rewrite aux-hcdw=hcxd1-m cd wm | aux-hcdw=hcxd1-m (hcdw cd wm .proj₂) wm₁ | aux-hcdw=hcxd1-m (hcxd1-m cd wm .proj₂) wm₁ = Eq.refl

  aux-hcdws=hcxds-m : ∀ cds wm -> hcdws cds wm ≡ hcxds-m cds wm
  aux-hcdws=hcxds-m [] wm = Eq.refl
  aux-hcdws=hcxds-m (x ∷ cds) wm with aux-hcdw=hcxd1-m x wm | aux-hcdws=hcxds-m cds (hcdw x wm .proj₁)
  ... | ih1 | ih2 rewrite ih1 | ih2 = Eq.refl

  hcxds-m-hdmw' : ∀ d cds wm -> Word M × CD
  hcxds-m-hdmw' d cds wm =
    let (wm2 , cds2) = hcxds-m cds wm in
    let (wm3 , d3) = hdmw' d wm2 in
    (wm3 , d3 , cds2 , inj₂ tt)
  

  hcd-mb : CD -> Word B -> Word M × CD
  hcd-mb (d , cds , inj₁ c) w with (h₂ **) (inj₂ tt) w
  hcd-mb (d , cds , inj₁ c) w | wm1 , inj₁ d1 with hcmw c wm1
  hcd-mb (d , cds , inj₁ c) w | wm1 , inj₁ d1 | (wm1' , c1') with hcxds-m-hdmw' d cds wm1'
  hcd-mb (d , cds , inj₁ c) w | wm1 , inj₁ d1 | (wm1' , c1') | (wm2 , d2 , cds2 , _) = wm2 , d2 , (c1' , d1) ∷ cds2 , inj₂ tt
  
  hcd-mb (d , cds , inj₁ c) w | wm1 , inj₂ tt with hcmw c wm1
  hcd-mb (d , cds , inj₁ c) w | wm1 , inj₂ tt | (wm1' , c1') with hcxds-m-hdmw' d cds wm1'
  hcd-mb (d , cds , inj₁ c) w | wm1 , inj₂ tt | (wm1' , c1') | (wm2 , d2 , cds2 , _) = wm2 , d2 , cds2 , inj₁ c1'
  
  hcd-mb (d , [] , inj₂ tt) w with (h₂ **) d w
  hcd-mb (d , [] , inj₂ tt) w | (wm1 , d1) = wm1 , d1 , [] , inj₂ tt
  
  hcd-mb (d , (c0 , d0) ∷ cds , inj₂ tt) w with (h₂ **) (inj₁ d0) w
  hcd-mb (d , (c0 , d0) ∷ cds , inj₂ tt) w | (wm1 , inj₁ d1) with hcmw c0 wm1
  hcd-mb (d , (c0 , d0) ∷ cds , inj₂ tt) w | (wm1 , inj₁ d1) | wm1' , c1' with hcxds-m-hdmw' d cds wm1'
  hcd-mb (d , (c0 , d0) ∷ cds , inj₂ tt) w | (wm1 , inj₁ d1) | wm1' , c1' | (wm2 , d2 , cds2 , _) =  wm2 , d2 , (c1' , d1) ∷ cds2 , inj₂ tt
  
  hcd-mb (d , (c0 , d0) ∷ cds , inj₂ tt) w | (wm1 , inj₂ tt) with hcmw c0 wm1
  hcd-mb (d , (c0 , d0) ∷ cds , inj₂ tt) w | (wm1 , inj₂ tt) | wm1' , c1' with hcxds-m-hdmw' d cds wm1'
  hcd-mb (d , (c0 , d0) ∷ cds , inj₂ tt) w | (wm1 , inj₂ tt) | wm1' , c1' | (wm2 , d2 , cds2 , _) =  wm2 , d2 , cds2 , inj₁ c1'

  aux-hcdws-ε : ∀ cds -> hcdws cds ε ≡ (ε , cds)
  aux-hcdws-ε [] = Eq.refl
  aux-hcdws-ε (x ∷ cds) rewrite aux-hcdws-ε cds = Eq.refl

  aux-hcdws-• : ∀ cds w v -> let (w' , cds') = hcdws cds w in let (v' , cds'') = hcdws cds' v in
    hcdws cds (w • v) .proj₁ ≡ w' • v'
  aux-hcdws-• [] w v = Eq.refl
  aux-hcdws-• (x ∷ cds) w v = aux-hcdws-• cds ((hcd **) x w .proj₁)
                                ((hcd **) ((hcd **) x w .proj₂) v .proj₁)

  aux-hcdws-•2 : ∀ cds w v -> let (w' , cds') = hcdws cds w in let (v' , cds'') = hcdws cds' v in
    hcdws cds (w • v) .proj₂ ≡ cds''
  aux-hcdws-•2 [] w v = Eq.refl
  aux-hcdws-•2 (x ∷ cds) w v rewrite aux-hcdws-•2 cds ((hcd **) x w .proj₁) ((hcd **) ((hcd **) x w .proj₂) v .proj₁) = Eq.refl

  
  hcdws-m-hdmw' : ∀ d cds wm -> Word M × CD
  hcdws-m-hdmw' d cds wm =
    let (wm2 , cds2) = hcdws cds wm in
    let (wm3 , d3) = hdmw' d wm2 in
    (wm3 , d3 , cds2 , inj₂ tt)


  aux-hcdws-hdmw-• : ∀ d cds w v ->
    let (w1 , d1 , cds1 , c1) = hcdws-m-hdmw' d cds w in
    let (v2 , d2 , cds2 , c2) = hcdws-m-hdmw' d1 cds1 v in
    hcdws-m-hdmw' d cds (w • v) ≡ (w1 • v2 , d2 , cds2 , inj₂ tt)
  aux-hcdws-hdmw-• d cds w v with aux-hcdws-• cds w v
  aux-hcdws-hdmw-• d cds w v | fact =
    let (w1 , d1 , cds1 , c1) = hcdws-m-hdmw' d cds w in
    let (v2 , d2 , cds2 , c2) = hcdws-m-hdmw' d1 cds1 v in
    let (wm6 , cds6) = hcdws cds (w • v) in
    let (wm3 , d3) = hdmw' d wm6 in
    let (wm7 , cds7) = hcdws cds w in
    let (wm8 , cds8) = hcdws cds7 v in
    let (wm3' , d3') = hdmw' d (wm7 • wm8) in
    let (wm3'a , d3'a) = hdmw' d wm7 in
    let (wm4'a , d4'a) = hdmw' d3'a wm8 in
    begin
    hcdws-m-hdmw' d cds (w • v) ≡⟨ Eq.refl ⟩
    (wm3 , d3 , cds6 , inj₂ tt) ≡⟨ Eq.cong₂ (\xx yy -> (xx , yy , cds6 , inj₂ tt))
      (Eq.cong proj₁ (Eq.cong (hdmw' d) (aux-hcdws-• cds w  v)))
      ((Eq.cong proj₂ (Eq.cong (hdmw' d) (aux-hcdws-• cds w  v)))) ⟩
    (wm3' , d3' , cds6 , inj₂ tt) ≡⟨ Eq.cong (\xx -> wm3' , d3' , xx , inj₂ tt) (aux-hcdws-•2 cds w v) ⟩
    (wm3'a • wm4'a , d4'a , cds8 , inj₂ tt) ≡⟨ Eq.refl ⟩
    (w1 • v2 , d2 , cds2 , inj₂ tt) ∎
    where
      open Eq.≡-Reasoning

  lemma-hcm'2 : ∀ m -> hcm' (inj₂ tt) m ≡ ([ m ]ʷ , inj₂ tt)
  lemma-hcm'2 m = Eq.refl

  lemma-hcdmw-q2 : ∀ d cds wm -> 
    hcdmw (d , cds , inj₂ tt) wm ≡ hcdws-m-hdmw' d cds wm
  lemma-hcdmw-q2 d cds [ x ]ʷ = Eq.refl
  lemma-hcdmw-q2 d cds ε rewrite aux-hcdws-ε cds = Eq.refl
  lemma-hcdmw-q2 d cds (w • v) with lemma-hcdmw-q2 d cds w
  lemma-hcdmw-q2 d cds (w • v) | ih =
    let (wm1 , cd1@(dd1 , cdss1 , cc1)) = hcdmw (d , cds , inj₂ tt) w in
    let (wm2 , cd2) = hcdmw cd1 v in
    let (wm2' , cd2'@(d5 , cds5 , c5)) = hcdmw (dd1 , cdss1 , inj₂ tt) v in
    let (w1 , d1 , cds1 , c1) = hcdws-m-hdmw' d cds w in
    let (v2 , d2 , cds2 , c2) = hcdws-m-hdmw' d1 cds1 v in
    let (wm6 , cd6@(d6 , cds6 , c6)) = hcdmw (d1 , cds1 , inj₂ tt) v in
    begin
    hcdmw (d , cds , inj₂ tt) (w • v) ≡⟨ Eq.refl ⟩
    wm1 • wm2 , cd2 ≡⟨ Eq.cong₂ (\ xx yy -> wm1 • xx , yy)
      (Eq.cong proj₁ (Eq.cong (\ zz -> hcdmw zz v) (Eq.cong (\ttt -> (dd1 , cdss1 , ttt)) (lemma-hcdmw d cds (inj₂ tt) Eq.refl w))))
      ((Eq.cong proj₂ (Eq.cong (\ zz -> hcdmw zz v) (Eq.cong (\ttt -> (dd1 , cdss1 , ttt)) (lemma-hcdmw d cds (inj₂ tt) Eq.refl w))))) ⟩
    wm1 • wm2' , d5 , cds5 , c5 ≡⟨ Eq.cong₂ (\ xx yy -> wm1 • xx , yy) (Eq.cong proj₁ (Eq.cong₂ (\ aa bb -> hcdmw (aa , bb , inj₂ tt) v)
      (Eq.cong (proj₁ ∘ proj₂) ih) (Eq.cong (proj₁ ∘ proj₂ ∘ proj₂) ih)))
      (Eq.cong proj₂ (Eq.cong₂ (\ aa bb -> hcdmw (aa , bb , inj₂ tt) v) (Eq.cong (proj₁ ∘ proj₂) ih) (Eq.cong (proj₁ ∘ proj₂ ∘ proj₂) ih))) ⟩
    -- wm1 • wm2' , d5 , cds5 , c5 ≡⟨ Eq.cong (\xx -> wm1 • wm2' , d5 , cds5 , xx) (lemma-hcdmw dd1 cdss1 (inj₂ tt) Eq.refl v) ⟩
    -- wm1 • wm2' , d5 , cds5 , inj₂ tt ≡⟨ Eq.cong (\xx -> xx • wm2' , d5 , cds5 , inj₂ tt) (Eq.cong proj₁ ih) ⟩
    -- w1 • wm2' , d5 , cds5 , inj₂ tt ≡⟨ {!Eq.cong!} ⟩
    wm1 • wm6 , d6 , cds6 , c6 ≡⟨ Eq.cong (λ xx → xx • wm6 , d6 , cds6 , c6) (Eq.cong proj₁ ih) ⟩
    w1 • wm6 , d6 , cds6 , c6 ≡⟨ Eq.cong₂ (\ xx yy -> w1 • xx , yy) (Eq.cong proj₁ (lemma-hcdmw-q2 d1 cds1 v))  ((Eq.cong proj₂ (lemma-hcdmw-q2 d1 cds1 v))) ⟩
    w1 • v2 , d2 , cds2 , inj₂ tt ≡⟨ Eq.sym (aux-hcdws-hdmw-• d cds w v) ⟩
    hcdws-m-hdmw' d cds (w • v) ∎
    where
      open Eq.≡-Reasoning


  aux104 : ∀ d cds wm -> hcdws-m-hdmw' d cds wm ≡ hcxds-m-hdmw' d cds wm
  aux104 d cds wm rewrite aux-hcdws=hcxds-m cds wm = Eq.refl

  aux-hcdmw=hcxds-m-hdmw'2 : ∀ d cds wm ->
    hcdmw (d , cds , inj₂ tt) wm ≡ hcxds-m-hdmw' d cds wm
  aux-hcdmw=hcxds-m-hdmw'2 d cds wm = Eq.trans (lemma-hcdmw-q2 d cds wm) ( (aux104 d cds wm))

  lemma-100 : ∀ cd -> hcxd1-m cd ε ≡ (ε , cd)
  lemma-100 cd = Eq.refl

  lemma-101 : ∀ cds -> hcxds-m cds ε ≡ (ε , cds) 
  lemma-101 [] = Eq.refl
  lemma-101 (x ∷ cds) rewrite lemma-100 x | lemma-101 cds = Eq.refl

  lemma-hcd-ma-ε : ∀ d cds c -> hcd-ma (d , cds , c) ε ≡ (ε , d , cds , c)
  lemma-hcd-ma-ε d cds c rewrite lemma-h**=hcmw' c ε | lemma-101 cds = Eq.refl

  lemma-hcxd1-m-ε : ∀ cd -> hcxd1-m cd ε ≡ (ε , cd)
  lemma-hcxd1-m-ε cd = Eq.refl

  lemma-hcxds-m-ε : ∀ cds -> hcxds-m cds ε ≡ (ε , cds)
  lemma-hcxds-m-ε [] = Eq.refl
  lemma-hcxds-m-ε (x ∷ cds) rewrite lemma-hcxd1-m-ε x | lemma-hcxds-m-ε cds = Eq.refl

  lemma-hcd-mb-ε : ∀ d cds c -> hcd-mb (d , cds , c) ε ≡ (ε , d , cds , c)
  lemma-hcd-mb-ε d cds c@(inj₁ c') rewrite lemma-101 cds  = Eq.refl
  lemma-hcd-mb-ε d [] (inj₂ tt) = Eq.refl
  lemma-hcd-mb-ε d cds@(x ∷ cds') c@(inj₂ tt) rewrite  lemma-101 cds  | lemma-hcxds-m-ε cds'  = Eq.refl

  aux-hcxds-hdmw'-• : ∀ d cds w v ->
    let (w1 , d1 , cds1 , c1) = hcxds-m-hdmw' d cds w in
    let (v2 , d2 , cds2 , c2) = hcxds-m-hdmw' d1 cds1 v in
    hcxds-m-hdmw' d cds (w • v) ≡ (w1 • v2 , d2 , cds2 , inj₂ tt)
  aux-hcxds-hdmw'-• d cds w v = 
    let (w1 , d1 , cds1 , c1) = hcxds-m-hdmw' d cds w in
    let (v2 , d2 , cds2 , c2) = hcxds-m-hdmw' d1 cds1 v in
    let (w1' , d1' , cds1' , c1') = hcdws-m-hdmw' d cds w in
    let (v2' , d2' , cds2' , c2') = hcdws-m-hdmw' d1' cds1' v in
    let (v2'' , d2'' , cds2'' , c2'') = hcxds-m-hdmw' d1' cds1' v in
    let (v2''a , d2''a , cds2''a , c2''a) = hcxds-m-hdmw' d1 cds1' v in
    let (v2''b , d2''b , cds2''b , c2''b) = hcxds-m-hdmw' d1 cds1 v in
    begin
    hcxds-m-hdmw' d cds (w • v) ≡⟨ Eq.sym (aux104 d cds (w • v)) ⟩
    hcdws-m-hdmw' d cds (w • v) ≡⟨ aux-hcdws-hdmw-• d cds w v ⟩
    (w1' • v2' , d2' , cds2' , inj₂ tt) ≡⟨
      Eq.cong₂ (λ xx yy → xx • yy , d2' , cds2' , inj₂ tt)
      (Eq.cong proj₁ (aux104 d cds w))
      (Eq.cong proj₁ (aux104 d1' cds1' v)) ⟩
    (w1 • v2'' , d2' , cds2' , inj₂ tt) ≡⟨
      Eq.cong₂ (λ xx yy → w1 • v2'' , xx , yy , inj₂ tt)
      (Eq.cong (proj₁ ∘ proj₂) (aux104 d1' cds1' v))
      (Eq.cong (proj₁ ∘ proj₂ ∘ proj₂) (aux104 d1' cds1' v)) ⟩
    (w1 • v2'' , d2'' , cds2'' , inj₂ tt) ≡⟨
      Eq.cong₂ (λ xx yy → w1 • v2'' , xx , yy , inj₂ tt)
      (Eq.cong (proj₁ ∘ proj₂) (Eq.cong (\zz -> hcxds-m-hdmw' zz cds1' v) (Eq.cong (proj₁ ∘ proj₂) ( aux104 d cds w))))
      (Eq.cong (proj₁ ∘ proj₂ ∘ proj₂) (Eq.cong (\zz -> hcxds-m-hdmw' zz cds1' v) ((Eq.cong (proj₁ ∘ proj₂) ( aux104 d cds w))))) ⟩
    (w1 • v2'' , d2''a , cds2''a , inj₂ tt) ≡⟨
      Eq.cong (λ xx → w1 • xx , d2''a , cds2''a , inj₂ tt)
      (Eq.cong (proj₁) (Eq.cong (\zz -> hcxds-m-hdmw' zz cds1' v) (Eq.cong (proj₁ ∘ proj₂) ( aux104 d cds w)))) ⟩
    (w1 • v2''a , d2''a , cds2''a , inj₂ tt) ≡⟨
      Eq.cong₂ (λ xx yy → w1 • v2''a , xx , yy , inj₂ tt)
      (Eq.cong (proj₁ ∘ proj₂) (Eq.cong (\zz -> hcxds-m-hdmw' d1 zz v) (Eq.cong (proj₁ ∘ proj₂ ∘ proj₂) ( aux104 d cds w))))
      (Eq.cong (proj₁ ∘ proj₂ ∘ proj₂) (Eq.cong (\zz -> hcxds-m-hdmw' d1 zz v) ((Eq.cong (proj₁ ∘ proj₂ ∘ proj₂) ( aux104 d cds w))))) ⟩
    (w1 • v2''a , d2''b , cds2''b , inj₂ tt) ≡⟨
      Eq.cong (λ xx → w1 • xx , d2''b , cds2''b , inj₂ tt)
      (Eq.cong (proj₁) (Eq.cong (\zz -> hcxds-m-hdmw' d1 zz v) (Eq.cong (proj₁ ∘ proj₂ ∘ proj₂) ( aux104 d cds w)))) ⟩
    (w1 • v2''b , d2''b , cds2''b , inj₂ tt) ≡⟨ Eq.refl ⟩
    (w1 • v2 , d2 , cds2 , inj₂ tt) ∎
    where open Eq.≡-Reasoning


  lemma-hcd-ma-• : ∀ cd w v ->
    let (wm1 , cd1) = hcd-ma cd w in 
    let (wm2 , cd2) = hcd-ma cd1 v in 
    hcd-ma cd (w • v) ≡ (wm1 • wm2 , cd2)
  lemma-hcd-ma-• cd@(d , cds , c) w v = 
    let (wm1 , cd1) = hcd-ma cd w in 
    let (wm2 , cd2) = hcd-ma cd1 v in
    
    let (wm3 , c3) = (h₁ **) c (w • v) in
    let (wm4 , d4 , cds4 , c4) = hcxds-m-hdmw' d cds wm3 in
    let (wm3a , c3a) = (h₁ **) c w in
    let (wm3b , c3b) = (h₁ **) c3a v in
    let (wm4' , d4' , cds4' , c4') = hcxds-m-hdmw' d cds (wm3a • wm3b) in

    let (w1` , d1` , cds1` , c1`) = hcxds-m-hdmw' d cds wm3a in
    let (v2` , d2` , cds2` , c2`) = hcxds-m-hdmw' d1` cds1` wm3b in

    begin
    hcd-ma cd (w • v) ≡⟨ Eq.refl ⟩
    wm4 , d4 , cds4 , c3 ≡⟨ Eq.refl ⟩
    wm4' , d4' , cds4' , c3 ≡⟨ Eq.cong (\ xx -> wm4' , d4' , xx , c3) (((Eq.cong (proj₁ ∘ proj₂ ∘ proj₂) (aux-hcxds-hdmw'-• d cds wm3a wm3b)))) ⟩
    wm4' , d4' , cds2` , c3 ≡⟨ Eq.cong₂ (\ xx yy -> xx , yy , cds2` , c3)
      (Eq.cong proj₁ (aux-hcxds-hdmw'-• d cds wm3a wm3b))
      ((Eq.cong (proj₁ ∘ proj₂) (aux-hcxds-hdmw'-• d cds wm3a wm3b))) ⟩
    w1` • v2` , d2` , cds2` , c3 ≡⟨ Eq.refl ⟩
    (wm1 • wm2 , cd2) ∎
    where open Eq.≡-Reasoning

  lemma-hcxd1-mb'4 : ∀ c d w v ->
    let (w' , c' , d') = hcxd1-mb' (c , d) w in
    let (v' , d'') = (h₂ **) d' v in
    let (v'' , c'') = hcmw c' v' in
    hcxd1-mb' (c , d) (w • v) ≡ (w' • v'' , c'' , d'' )
  lemma-hcxd1-mb'4 c d w v = Eq.refl


  lemma-hcxd1-m : ∀ cd w v ->
    let (w' , cd') = hcxd1-m cd w in
    let (v' , cd'') = hcxd1-m cd' v in
    hcxd1-m cd (w • v) ≡ (w' • v' , cd'')
  lemma-hcxd1-m cd w v = Eq.refl


  lemma-hcxds-m : ∀ cds w v ->
    let (w' , cds') = hcxds-m cds w in
    let (v' , cds'') = hcxds-m cds' v in
    hcxds-m cds (w • v) ≡ (w' • v' , cds'')
  lemma-hcxds-m [] w v = Eq.refl
  lemma-hcxds-m (x ∷ cds) w v with lemma-hcxd1-m x w v | hcxd1-m x w | inspect (hcxd1-m x) w
  lemma-hcxds-m (x ∷ cds) w v | hx | (w' , cd') | [ Eq.refl ]' with hcxd1-m cd' v | inspect (hcxd1-m cd') v
  lemma-hcxds-m (x ∷ cds) w v | hx | (w' , cd') | [ Eq.refl ]' | (v' , cd'') | [ Eq.refl ]' rewrite hx | lemma-hcxds-m cds w' v' = Eq.refl

  lemma-hcd-mb-• : ∀ cd w v ->
    let (wm1 , cd1) = hcd-mb cd w in 
    let (wm2 , cd2) = hcd-mb cd1 v in 
    hcd-mb cd (w • v) ≡ (wm1 • wm2 , cd2)
  lemma-hcd-mb-• cd@(d , cds@[] , c@(inj₂ tt)) w v = Eq.refl

  lemma-hcd-mb-• cd@(d , (c0 , d0) ∷ cds , c@(inj₂ tt)) w v with (h₂ **) (inj₁ d0) (w • v) | inspect ((h₂ **) (inj₁ d0)) (w • v) | (h₂ **) (inj₁ d0) w | inspect ((h₂ **) (inj₁ d0)) w
  lemma-hcd-mb-• cd@(d , (c0 , d0) ∷ cds , c@(inj₂ tt)) w v | (wv1 , inj₁ d1) | [ eq1 ]' | (w1 , inj₁ d1w) | [ eqw ]' with hcmw c0 wv1 | inspect (hcmw c0) wv1 | hcmw c0 w1 | inspect (hcmw c0) w1 
  lemma-hcd-mb-• cd@(d , (c0 , d0) ∷ cds , c@(inj₂ tt)) w v | (wv1 , inj₁ d1) | [ eq1 ]' | (w1 , inj₁ d1w) | [ eqw ]' | (wv2 , c2) | [ Eq.refl ]' | (w2 , c2w) | [ Eq.refl ]' with hcxds-m-hdmw' d cds wv1 | inspect (hcxds-m-hdmw' d cds) wv1 | hcxds-m-hdmw' d cds w2 | inspect (hcxds-m-hdmw' d cds) w2
  lemma-hcd-mb-• cd@(d , (c0 , d0) ∷ cds , c@(inj₂ tt)) w v | (wv1 , inj₁ d1) | [ eq1 ]' | (w1 , inj₁ d1w) | [ eqw ]' | (wv2 , c2) | [ Eq.refl ]' | (w2 , c2w) | [ Eq.refl ]' | (wv3 , d3 , cds3 , inj₂ tt) | [ Eq.refl ]' | (w3 , d3w , cds3w , inj₂ tt) | [ Eq.refl ]' with (h₂ **) (inj₁ d1w) v | inspect ((h₂ **) (inj₁ d1w)) v
  lemma-hcd-mb-• cd@(d , (c0 , d0) ∷ cds , c@(inj₂ tt)) w v | (wv1 , inj₁ d1) | [ eq1 ]' | (w1 , inj₁ d1w) | [ eqw ]' | (wv2 , c2) | [ Eq.refl ]' | (w2 , c2w) | [ Eq.refl ]' | (wv3 , d3 , cds3 , inj₂ tt) | [ Eq.refl ]' | (w3 , d3w , cds3w , inj₂ tt) | [ Eq.refl ]' | (v1 , inj₁ d1v) | [ eqv ]' with hcmw c2w v1 | inspect (hcmw c2w) v1
  lemma-hcd-mb-• cd@(d , (c0 , d0) ∷ cds , c@(inj₂ tt)) w v | (wv1 , inj₁ d1) | [ eq1 ]' | (w1 , inj₁ d1w) | [ eqw ]' | (wv2 , c2) | [ Eq.refl ]' | (w2 , c2w) | [ Eq.refl ]' | (wv3 , d3 , cds3 , inj₂ tt) | [ Eq.refl ]' | (w3 , d3w , cds3w , inj₂ tt) | [ Eq.refl ]' | (v1 , inj₁ d1v) | [ eqv ]' | (v2 , c2v) | [ Eq.refl ]' with hcxds-m-hdmw' d cds3w v2 | inspect (hcxds-m-hdmw' d cds3w) v2
  lemma-hcd-mb-• cd@(d , (c0 , d0) ∷ cds , c@(inj₂ tt)) w v | (wv1 , inj₁ d1) | [ eq1 ]' | (w1 , inj₁ d1w) | [ eqw ]' | (wv2 , c2) | [ Eq.refl ]' | (w2 , c2w) | [ Eq.refl ]' | (wv3 , d3 , cds3 , inj₂ tt) | [ Eq.refl ]' | (w3 , d3w , cds3w , inj₂ tt) | [ Eq.refl ]' | (v1 , inj₁ d1v) | [ eqv ]' | (v2 , c2v) | [ Eq.refl ]' | (v3 , d3v , cds3v , inj₂ tt) | [ Eq.refl ]' rewrite lemma-hcxds-m cds w2 v2 = Eq.refl
  lemma-hcd-mb-• cd@(d , (c0 , d0) ∷ cds , c@(inj₂ tt)) w v | (wv1 , inj₁ d1) | [ eq1 ]' | (w1 , inj₁ d1w) | [ eqw ]' | (wv2 , c2) | [ Eq.refl ]' | (w2 , c2w) | [ Eq.refl ]' | (wv3 , d3 , cds3 , inj₂ tt) | [ Eq.refl ]' | (w3 , d3w , cds3w , inj₂ tt) | [ Eq.refl ]' | (v1 , inj₂ tt) | [ eqv ]' with hcmw c2w v1 | inspect (hcmw c2w) v1
  lemma-hcd-mb-• cd@(d , (c0 , d0) ∷ cds , c@(inj₂ tt)) w v | (wv1 , inj₁ d1) | [ eq1 ]' | (w1 , inj₁ d1w) | [ eqw ]' | (wv2 , c2) | [ Eq.refl ]' | (w2 , c2w) | [ Eq.refl ]' | (wv3 , d3 , cds3 , inj₂ tt) | [ Eq.refl ]' | (w3 , d3w , cds3w , inj₂ tt) | [ Eq.refl ]' | (v1 , inj₂ tt) | [ eqv ]'  | (v2 , c2v) | [ Eq.refl ]' with hcxds-m-hdmw' d cds3w v2 | inspect (hcxds-m-hdmw' d cds3w) v2
  lemma-hcd-mb-• cd@(d , (c0 , d0) ∷ cds , c@(inj₂ tt)) w v | (wv1 , inj₁ d1) | [ eq1 ]' | (w1 , inj₁ d1w) | [ eqw ]' | (wv2 , c2) | [ Eq.refl ]' | (w2 , c2w) | [ Eq.refl ]' | (wv3 , d3 , cds3 , inj₂ tt) | [ Eq.refl ]' | (w3 , d3w , cds3w , inj₂ tt) | [ Eq.refl ]' | (v1 , inj₂ tt) | [ eqv ]'  | (v2 , c2v) | [ Eq.refl ]' | (v3 , d3v , cds3v , inj₂ tt) | [ Eq.refl ]' rewrite lemma-hcxds-m cds w2 v2 = Eq.refl

  lemma-hcd-mb-• cd@(d , (c0 , d0) ∷ cds , c@(inj₂ tt)) w v | (wv1 , inj₂ tt) | [ eq1 ]' | (w1 , inj₁ d1w) | [ eqw ]' with hcmw c0 wv1 | inspect (hcmw c0) wv1 | hcmw c0 w1 | inspect (hcmw c0) w1 
  lemma-hcd-mb-• cd@(d , (c0 , d0) ∷ cds , c@(inj₂ tt)) w v | (wv1 , inj₂ tt) | [ eq1 ]' | (w1 , inj₁ d1w) | [ eqw ]' | (wv2 , c2) | [ Eq.refl ]' | (w2 , c2w) | [ Eq.refl ]' with hcxds-m-hdmw' d cds wv1 | inspect (hcxds-m-hdmw' d cds) wv1 | hcxds-m-hdmw' d cds w2 | inspect (hcxds-m-hdmw' d cds) w2
  lemma-hcd-mb-• cd@(d , (c0 , d0) ∷ cds , c@(inj₂ tt)) w v | (wv1 , inj₂ tt) | [ eq1 ]' | (w1 , inj₁ d1w) | [ eqw ]' | (wv2 , c2) | [ Eq.refl ]' | (w2 , c2w) | [ Eq.refl ]' | (wv3 , d3 , cds3 , inj₂ tt) | [ Eq.refl ]' | (w3 , d3w , cds3w , inj₂ tt) | [ Eq.refl ]' with (h₂ **) (inj₁ d1w) v | inspect ((h₂ **) (inj₁ d1w)) v
  lemma-hcd-mb-• cd@(d , (c0 , d0) ∷ cds , c@(inj₂ tt)) w v | (wv1 , inj₂ tt) | [ eq1 ]' | (w1 , inj₁ d1w) | [ eqw ]' | (wv2 , c2) | [ Eq.refl ]' | (w2 , c2w) | [ Eq.refl ]' | (wv3 , d3 , cds3 , inj₂ tt) | [ Eq.refl ]' | (w3 , d3w , cds3w , inj₂ tt) | [ Eq.refl ]' | (v1 , inj₁ d1v) | [ eqv ]' with hcmw c2w v1 | inspect (hcmw c2w) v1
  lemma-hcd-mb-• cd@(d , (c0 , d0) ∷ cds , c@(inj₂ tt)) w v | (wv1 , inj₂ tt) | [ eq1 ]' | (w1 , inj₁ d1w) | [ eqw ]' | (wv2 , c2) | [ Eq.refl ]' | (w2 , c2w) | [ Eq.refl ]' | (wv3 , d3 , cds3 , inj₂ tt) | [ Eq.refl ]' | (w3 , d3w , cds3w , inj₂ tt) | [ Eq.refl ]' | (v1 , inj₁ d1v) | [ eqv ]' | (v2 , c2v) | [ Eq.refl ]' with hcxds-m-hdmw' d cds3w v2 | inspect (hcxds-m-hdmw' d cds3w) v2
  lemma-hcd-mb-• cd@(d , (c0 , d0) ∷ cds , c@(inj₂ tt)) w v | (wv1 , inj₂ tt) | [ eq1 ]' | (w1 , inj₁ d1w) | [ eqw ]' | (wv2 , c2) | [ Eq.refl ]' | (w2 , c2w) | [ Eq.refl ]' | (wv3 , d3 , cds3 , inj₂ tt) | [ Eq.refl ]' | (w3 , d3w , cds3w , inj₂ tt) | [ Eq.refl ]' | (v1 , inj₁ d1v) | [ eqv ]' | (v2 , c2v) | [ Eq.refl ]' | (v3 , d3v , cds3v , inj₂ tt) | [ Eq.refl ]' rewrite lemma-hcxds-m cds w2 v2 = Eq.refl
  lemma-hcd-mb-• cd@(d , (c0 , d0) ∷ cds , c@(inj₂ tt)) w v | (wv1 , inj₂ tt) | [ eq1 ]' | (w1 , inj₁ d1w) | [ eqw ]' | (wv2 , c2) | [ Eq.refl ]' | (w2 , c2w) | [ Eq.refl ]' | (wv3 , d3 , cds3 , inj₂ tt) | [ Eq.refl ]' | (w3 , d3w , cds3w , inj₂ tt) | [ Eq.refl ]' | (v1 , inj₂ tt) | [ eqv ]' with hcmw c2w v1 | inspect (hcmw c2w) v1
  lemma-hcd-mb-• cd@(d , (c0 , d0) ∷ cds , c@(inj₂ tt)) w v | (wv1 , inj₂ tt) | [ eq1 ]' | (w1 , inj₁ d1w) | [ eqw ]' | (wv2 , c2) | [ Eq.refl ]' | (w2 , c2w) | [ Eq.refl ]' | (wv3 , d3 , cds3 , inj₂ tt) | [ Eq.refl ]' | (w3 , d3w , cds3w , inj₂ tt) | [ Eq.refl ]' | (v1 , inj₂ tt) | [ eqv ]'  | (v2 , c2v) | [ Eq.refl ]' with hcxds-m-hdmw' d cds3w v2 | inspect (hcxds-m-hdmw' d cds3w) v2
  lemma-hcd-mb-• cd@(d , (c0 , d0) ∷ cds , c@(inj₂ tt)) w v | (wv1 , inj₂ tt) | [ eq1 ]' | (w1 , inj₁ d1w) | [ eqw ]' | (wv2 , c2) | [ Eq.refl ]' | (w2 , c2w) | [ Eq.refl ]' | (wv3 , d3 , cds3 , inj₂ tt) | [ Eq.refl ]' | (w3 , d3w , cds3w , inj₂ tt) | [ Eq.refl ]' | (v1 , inj₂ tt) | [ eqv ]'  | (v2 , c2v) | [ Eq.refl ]' | (v3 , d3v , cds3v , inj₂ tt) | [ Eq.refl ]' rewrite lemma-hcxds-m cds w2 v2 = Eq.refl

  lemma-hcd-mb-• cd@(d , (c0 , d0) ∷ cds , c@(inj₂ tt)) w v | (wv1 , inj₂ tt) | [ eq1 ]' | (w1 , inj₂ tt) | [ eqw ]' with hcmw c0 wv1 | inspect (hcmw c0) wv1 | hcmw c0 w1 | inspect (hcmw c0) w1 
  lemma-hcd-mb-• cd@(d , (c0 , d0) ∷ cds , c@(inj₂ tt)) w v | (wv1 , inj₂ tt) | [ eq1 ]' | (w1 , inj₂ tt) | [ eqw ]' | (wv2 , c2) | [ Eq.refl ]' | (w2 , c2w) | [ Eq.refl ]' with hcxds-m-hdmw' d cds wv1 | inspect (hcxds-m-hdmw' d cds) wv1 | hcxds-m-hdmw' d cds w2 | inspect (hcxds-m-hdmw' d cds) w2
  lemma-hcd-mb-• cd@(d , (c0 , d0) ∷ cds , c@(inj₂ tt)) w v | (wv1 , inj₂ tt) | [ eq1 ]' | (w1 , inj₂ tt) | [ eqw ]' | (wv2 , c2) | [ Eq.refl ]' | (w2 , c2w) | [ Eq.refl ]' | (wv3 , d3 , cds3 , inj₂ tt) | [ Eq.refl ]' | (w3 , d3w , cds3w , inj₂ tt) | [ Eq.refl ]' with (h₂ **) (inj₂ tt) v | inspect ((h₂ **) (inj₂ tt)) v
  lemma-hcd-mb-• cd@(d , (c0 , d0) ∷ cds , c@(inj₂ tt)) w v | (wv1 , inj₂ tt) | [ eq1 ]' | (w1 , inj₂ tt) | [ eqw ]' | (wv2 , c2) | [ Eq.refl ]' | (w2 , c2w) | [ Eq.refl ]' | (wv3 , d3 , cds3 , inj₂ tt) | [ Eq.refl ]' | (w3 , d3w , cds3w , inj₂ tt) | [ Eq.refl ]' | (v1 , inj₁ d1v) | [ eqv ]' with hcmw c2w v1 | inspect (hcmw c2w) v1
  lemma-hcd-mb-• cd@(d , (c0 , d0) ∷ cds , c@(inj₂ tt)) w v | (wv1 , inj₂ tt) | [ eq1 ]' | (w1 , inj₂ tt) | [ eqw ]' | (wv2 , c2) | [ Eq.refl ]' | (w2 , c2w) | [ Eq.refl ]' | (wv3 , d3 , cds3 , inj₂ tt) | [ Eq.refl ]' | (w3 , d3w , cds3w , inj₂ tt) | [ Eq.refl ]' | (v1 , inj₁ d1v) | [ eqv ]' | (v2 , c2v) | [ Eq.refl ]' with hcxds-m-hdmw' d cds3w v2 | inspect (hcxds-m-hdmw' d cds3w) v2
  lemma-hcd-mb-• cd@(d , (c0 , d0) ∷ cds , c@(inj₂ tt)) w v | (wv1 , inj₂ tt) | [ eq1 ]' | (w1 , inj₂ tt) | [ eqw ]' | (wv2 , c2) | [ Eq.refl ]' | (w2 , c2w) | [ Eq.refl ]' | (wv3 , d3 , cds3 , inj₂ tt) | [ Eq.refl ]' | (w3 , d3w , cds3w , inj₂ tt) | [ Eq.refl ]' | (v1 , inj₁ d1v) | [ eqv ]' | (v2 , c2v) | [ Eq.refl ]' | (v3 , d3v , cds3v , inj₂ tt) | [ Eq.refl ]' rewrite lemma-hcxds-m cds w2 v2 = Eq.refl
  lemma-hcd-mb-• cd@(d , (c0 , d0) ∷ cds , c@(inj₂ tt)) w v | (wv1 , inj₂ tt) | [ eq1 ]' | (w1 , inj₂ tt) | [ eqw ]' | (wv2 , c2) | [ Eq.refl ]' | (w2 , c2w) | [ Eq.refl ]' | (wv3 , d3 , cds3 , inj₂ tt) | [ Eq.refl ]' | (w3 , d3w , cds3w , inj₂ tt) | [ Eq.refl ]' | (v1 , inj₂ tt) | [ eqv ]' with hcmw c2w v1 | inspect (hcmw c2w) v1
  lemma-hcd-mb-• cd@(d , (c0 , d0) ∷ cds , c@(inj₂ tt)) w v | (wv1 , inj₂ tt) | [ eq1 ]' | (w1 , inj₂ tt) | [ eqw ]' | (wv2 , c2) | [ Eq.refl ]' | (w2 , c2w) | [ Eq.refl ]' | (wv3 , d3 , cds3 , inj₂ tt) | [ Eq.refl ]' | (w3 , d3w , cds3w , inj₂ tt) | [ Eq.refl ]' | (v1 , inj₂ tt) | [ eqv ]'  | (v2 , c2v) | [ Eq.refl ]' with hcxds-m-hdmw' d cds3w v2 | inspect (hcxds-m-hdmw' d cds3w) v2
  lemma-hcd-mb-• cd@(d , (c0 , d0) ∷ cds , c@(inj₂ tt)) w v | (wv1 , inj₂ tt) | [ eq1 ]' | (w1 , inj₂ tt) | [ eqw ]' | (wv2 , c2) | [ Eq.refl ]' | (w2 , c2w) | [ Eq.refl ]' | (wv3 , d3 , cds3 , inj₂ tt) | [ Eq.refl ]' | (w3 , d3w , cds3w , inj₂ tt) | [ Eq.refl ]' | (v1 , inj₂ tt) | [ eqv ]'  | (v2 , c2v) | [ Eq.refl ]' | (v3 , d3v , cds3v , inj₂ tt) | [ Eq.refl ]' rewrite lemma-hcxds-m cds w2 v2 = Eq.refl

  lemma-hcd-mb-• cd@(d , (c0 , d0) ∷ cds , c@(inj₂ tt)) w v | (wv1 , inj₁ d1) | [ eq1 ]' | (w1 , inj₂ tt) | [ eqw ]' with hcmw c0 wv1 | inspect (hcmw c0) wv1 | hcmw c0 w1 | inspect (hcmw c0) w1 
  lemma-hcd-mb-• cd@(d , (c0 , d0) ∷ cds , c@(inj₂ tt)) w v | (wv1 , inj₁ d1) | [ eq1 ]' | (w1 , inj₂ tt) | [ eqw ]' | (wv2 , c2) | [ Eq.refl ]' | (w2 , c2w) | [ Eq.refl ]' with hcxds-m-hdmw' d cds wv1 | inspect (hcxds-m-hdmw' d cds) wv1 | hcxds-m-hdmw' d cds w2 | inspect (hcxds-m-hdmw' d cds) w2
  lemma-hcd-mb-• cd@(d , (c0 , d0) ∷ cds , c@(inj₂ tt)) w v | (wv1 , inj₁ d1) | [ eq1 ]' | (w1 , inj₂ tt) | [ eqw ]' | (wv2 , c2) | [ Eq.refl ]' | (w2 , c2w) | [ Eq.refl ]' | (wv3 , d3 , cds3 , inj₂ tt) | [ Eq.refl ]' | (w3 , d3w , cds3w , inj₂ tt) | [ Eq.refl ]' with (h₂ **) (inj₂ tt) v | inspect ((h₂ **) (inj₂ tt)) v
  lemma-hcd-mb-• cd@(d , (c0 , d0) ∷ cds , c@(inj₂ tt)) w v | (wv1 , inj₁ d1) | [ eq1 ]' | (w1 , inj₂ tt) | [ eqw ]' | (wv2 , c2) | [ Eq.refl ]' | (w2 , c2w) | [ Eq.refl ]' | (wv3 , d3 , cds3 , inj₂ tt) | [ Eq.refl ]' | (w3 , d3w , cds3w , inj₂ tt) | [ Eq.refl ]' | (v1 , inj₁ d1v) | [ eqv ]' with hcmw c2w v1 | inspect (hcmw c2w) v1
  lemma-hcd-mb-• cd@(d , (c0 , d0) ∷ cds , c@(inj₂ tt)) w v | (wv1 , inj₁ d1) | [ eq1 ]' | (w1 , inj₂ tt) | [ eqw ]' | (wv2 , c2) | [ Eq.refl ]' | (w2 , c2w) | [ Eq.refl ]' | (wv3 , d3 , cds3 , inj₂ tt) | [ Eq.refl ]' | (w3 , d3w , cds3w , inj₂ tt) | [ Eq.refl ]' | (v1 , inj₁ d1v) | [ eqv ]' | (v2 , c2v) | [ Eq.refl ]' with hcxds-m-hdmw' d cds3w v2 | inspect (hcxds-m-hdmw' d cds3w) v2
  lemma-hcd-mb-• cd@(d , (c0 , d0) ∷ cds , c@(inj₂ tt)) w v | (wv1 , inj₁ d1) | [ eq1 ]' | (w1 , inj₂ tt) | [ eqw ]' | (wv2 , c2) | [ Eq.refl ]' | (w2 , c2w) | [ Eq.refl ]' | (wv3 , d3 , cds3 , inj₂ tt) | [ Eq.refl ]' | (w3 , d3w , cds3w , inj₂ tt) | [ Eq.refl ]' | (v1 , inj₁ d1v) | [ eqv ]' | (v2 , c2v) | [ Eq.refl ]' | (v3 , d3v , cds3v , inj₂ tt) | [ Eq.refl ]' rewrite lemma-hcxds-m cds w2 v2 = Eq.refl
  lemma-hcd-mb-• cd@(d , (c0 , d0) ∷ cds , c@(inj₂ tt)) w v | (wv1 , inj₁ d1) | [ eq1 ]' | (w1 , inj₂ tt) | [ eqw ]' | (wv2 , c2) | [ Eq.refl ]' | (w2 , c2w) | [ Eq.refl ]' | (wv3 , d3 , cds3 , inj₂ tt) | [ Eq.refl ]' | (w3 , d3w , cds3w , inj₂ tt) | [ Eq.refl ]' | (v1 , inj₂ tt) | [ eqv ]' with hcmw c2w v1 | inspect (hcmw c2w) v1
  lemma-hcd-mb-• cd@(d , (c0 , d0) ∷ cds , c@(inj₂ tt)) w v | (wv1 , inj₁ d1) | [ eq1 ]' | (w1 , inj₂ tt) | [ eqw ]' | (wv2 , c2) | [ Eq.refl ]' | (w2 , c2w) | [ Eq.refl ]' | (wv3 , d3 , cds3 , inj₂ tt) | [ Eq.refl ]' | (w3 , d3w , cds3w , inj₂ tt) | [ Eq.refl ]' | (v1 , inj₂ tt) | [ eqv ]'  | (v2 , c2v) | [ Eq.refl ]' with hcxds-m-hdmw' d cds3w v2 | inspect (hcxds-m-hdmw' d cds3w) v2
  lemma-hcd-mb-• cd@(d , (c0 , d0) ∷ cds , c@(inj₂ tt)) w v | (wv1 , inj₁ d1) | [ eq1 ]' | (w1 , inj₂ tt) | [ eqw ]' | (wv2 , c2) | [ Eq.refl ]' | (w2 , c2w) | [ Eq.refl ]' | (wv3 , d3 , cds3 , inj₂ tt) | [ Eq.refl ]' | (w3 , d3w , cds3w , inj₂ tt) | [ Eq.refl ]' | (v1 , inj₂ tt) | [ eqv ]'  | (v2 , c2v) | [ Eq.refl ]' | (v3 , d3v , cds3v , inj₂ tt) | [ Eq.refl ]' rewrite lemma-hcxds-m cds w2 v2 = Eq.refl

  lemma-hcd-mb-• cd@(d , cds , c@(inj₁ c0)) w v with (h₂ **) (inj₂ tt) (w • v) | inspect ((h₂ **) (inj₂ tt)) (w • v) | (h₂ **) (inj₂ tt) w | inspect ((h₂ **) (inj₂ tt)) w
  lemma-hcd-mb-• cd@(d , cds , c@(inj₁ c0)) w v | (wv1 , inj₁ d1) | [ eq1 ]' | (w1 , inj₁ d1w) | [ eqw ]' with hcmw c0 wv1 | inspect (hcmw c0) wv1 | hcmw c0 w1 | inspect (hcmw c0) w1 
  lemma-hcd-mb-• cd@(d , cds , c@(inj₁ c0)) w v | (wv1 , inj₁ d1) | [ eq1 ]' | (w1 , inj₁ d1w) | [ eqw ]' | (wv2 , c2) | [ Eq.refl ]' | (w2 , c2w) | [ Eq.refl ]' with hcxds-m-hdmw' d cds wv1 | inspect (hcxds-m-hdmw' d cds) wv1 | hcxds-m-hdmw' d cds w2 | inspect (hcxds-m-hdmw' d cds) w2
  lemma-hcd-mb-• cd@(d , cds , c@(inj₁ c0)) w v | (wv1 , inj₁ d1) | [ eq1 ]' | (w1 , inj₁ d1w) | [ eqw ]' | (wv2 , c2) | [ Eq.refl ]' | (w2 , c2w) | [ Eq.refl ]' | (wv3 , d3 , cds3 , inj₂ tt) | [ Eq.refl ]' | (w3 , d3w , cds3w , inj₂ tt) | [ Eq.refl ]' with (h₂ **) (inj₁ d1w) v | inspect ((h₂ **) (inj₁ d1w)) v
  lemma-hcd-mb-• cd@(d , cds , c@(inj₁ c0)) w v | (wv1 , inj₁ d1) | [ eq1 ]' | (w1 , inj₁ d1w) | [ eqw ]' | (wv2 , c2) | [ Eq.refl ]' | (w2 , c2w) | [ Eq.refl ]' | (wv3 , d3 , cds3 , inj₂ tt) | [ Eq.refl ]' | (w3 , d3w , cds3w , inj₂ tt) | [ Eq.refl ]' | (v1 , inj₁ d1v) | [ eqv ]' with hcmw c2w v1 | inspect (hcmw c2w) v1
  lemma-hcd-mb-• cd@(d , cds , c@(inj₁ c0)) w v | (wv1 , inj₁ d1) | [ eq1 ]' | (w1 , inj₁ d1w) | [ eqw ]' | (wv2 , c2) | [ Eq.refl ]' | (w2 , c2w) | [ Eq.refl ]' | (wv3 , d3 , cds3 , inj₂ tt) | [ Eq.refl ]' | (w3 , d3w , cds3w , inj₂ tt) | [ Eq.refl ]' | (v1 , inj₁ d1v) | [ eqv ]' | (v2 , c2v) | [ Eq.refl ]' with hcxds-m-hdmw' d cds3w v2 | inspect (hcxds-m-hdmw' d cds3w) v2
  lemma-hcd-mb-• cd@(d , cds , c@(inj₁ c0)) w v | (wv1 , inj₁ d1) | [ eq1 ]' | (w1 , inj₁ d1w) | [ eqw ]' | (wv2 , c2) | [ Eq.refl ]' | (w2 , c2w) | [ Eq.refl ]' | (wv3 , d3 , cds3 , inj₂ tt) | [ Eq.refl ]' | (w3 , d3w , cds3w , inj₂ tt) | [ Eq.refl ]' | (v1 , inj₁ d1v) | [ eqv ]' | (v2 , c2v) | [ Eq.refl ]' | (v3 , d3v , cds3v , inj₂ tt) | [ Eq.refl ]' rewrite lemma-hcxds-m cds w2 v2 = Eq.refl
  lemma-hcd-mb-• cd@(d , cds , c@(inj₁ c0)) w v | (wv1 , inj₁ d1) | [ eq1 ]' | (w1 , inj₁ d1w) | [ eqw ]' | (wv2 , c2) | [ Eq.refl ]' | (w2 , c2w) | [ Eq.refl ]' | (wv3 , d3 , cds3 , inj₂ tt) | [ Eq.refl ]' | (w3 , d3w , cds3w , inj₂ tt) | [ Eq.refl ]' | (v1 , inj₂ tt) | [ eqv ]' with hcmw c2w v1 | inspect (hcmw c2w) v1
  lemma-hcd-mb-• cd@(d , cds , c@(inj₁ c0)) w v | (wv1 , inj₁ d1) | [ eq1 ]' | (w1 , inj₁ d1w) | [ eqw ]' | (wv2 , c2) | [ Eq.refl ]' | (w2 , c2w) | [ Eq.refl ]' | (wv3 , d3 , cds3 , inj₂ tt) | [ Eq.refl ]' | (w3 , d3w , cds3w , inj₂ tt) | [ Eq.refl ]' | (v1 , inj₂ tt) | [ eqv ]'  | (v2 , c2v) | [ Eq.refl ]' with hcxds-m-hdmw' d cds3w v2 | inspect (hcxds-m-hdmw' d cds3w) v2
  lemma-hcd-mb-• cd@(d , cds , c@(inj₁ c0)) w v | (wv1 , inj₁ d1) | [ eq1 ]' | (w1 , inj₁ d1w) | [ eqw ]' | (wv2 , c2) | [ Eq.refl ]' | (w2 , c2w) | [ Eq.refl ]' | (wv3 , d3 , cds3 , inj₂ tt) | [ Eq.refl ]' | (w3 , d3w , cds3w , inj₂ tt) | [ Eq.refl ]' | (v1 , inj₂ tt) | [ eqv ]'  | (v2 , c2v) | [ Eq.refl ]' | (v3 , d3v , cds3v , inj₂ tt) | [ Eq.refl ]' rewrite lemma-hcxds-m cds w2 v2 = Eq.refl

  lemma-hcd-mb-• cd@(d , cds , c@(inj₁ c0)) w v | (wv1 , inj₂ tt) | [ eq1 ]' | (w1 , inj₂ tt) | [ eqw ]' with hcmw c0 wv1 | inspect (hcmw c0) wv1 | hcmw c0 w1 | inspect (hcmw c0) w1 
  lemma-hcd-mb-• cd@(d , cds , c@(inj₁ c0)) w v | (wv1 , inj₂ tt) | [ eq1 ]' | (w1 , inj₂ tt) | [ eqw ]' | (wv2 , c2) | [ Eq.refl ]' | (w2 , c2w) | [ Eq.refl ]' with hcxds-m-hdmw' d cds wv1 | inspect (hcxds-m-hdmw' d cds) wv1 | hcxds-m-hdmw' d cds w2 | inspect (hcxds-m-hdmw' d cds) w2
  lemma-hcd-mb-• cd@(d , cds , c@(inj₁ c0)) w v | (wv1 , inj₂ tt) | [ eq1 ]' | (w1 , inj₂ tt) | [ eqw ]' | (wv2 , c2) | [ Eq.refl ]' | (w2 , c2w) | [ Eq.refl ]' | (wv3 , d3 , cds3 , inj₂ tt) | [ Eq.refl ]' | (w3 , d3w , cds3w , inj₂ tt) | [ Eq.refl ]' with (h₂ **) (inj₂ tt) v | inspect ((h₂ **) (inj₂ tt)) v
  lemma-hcd-mb-• cd@(d , cds , c@(inj₁ c0)) w v | (wv1 , inj₂ tt) | [ eq1 ]' | (w1 , inj₂ tt) | [ eqw ]' | (wv2 , c2) | [ Eq.refl ]' | (w2 , c2w) | [ Eq.refl ]' | (wv3 , d3 , cds3 , inj₂ tt) | [ Eq.refl ]' | (w3 , d3w , cds3w , inj₂ tt) | [ Eq.refl ]' | (v1 , inj₁ d1v) | [ eqv ]' with hcmw c2w v1 | inspect (hcmw c2w) v1
  lemma-hcd-mb-• cd@(d , cds , c@(inj₁ c0)) w v | (wv1 , inj₂ tt) | [ eq1 ]' | (w1 , inj₂ tt) | [ eqw ]' | (wv2 , c2) | [ Eq.refl ]' | (w2 , c2w) | [ Eq.refl ]' | (wv3 , d3 , cds3 , inj₂ tt) | [ Eq.refl ]' | (w3 , d3w , cds3w , inj₂ tt) | [ Eq.refl ]' | (v1 , inj₁ d1v) | [ eqv ]' | (v2 , c2v) | [ Eq.refl ]' with hcxds-m-hdmw' d cds3w v2 | inspect (hcxds-m-hdmw' d cds3w) v2
  lemma-hcd-mb-• cd@(d , cds , c@(inj₁ c0)) w v | (wv1 , inj₂ tt) | [ eq1 ]' | (w1 , inj₂ tt) | [ eqw ]' | (wv2 , c2) | [ Eq.refl ]' | (w2 , c2w) | [ Eq.refl ]' | (wv3 , d3 , cds3 , inj₂ tt) | [ Eq.refl ]' | (w3 , d3w , cds3w , inj₂ tt) | [ Eq.refl ]' | (v1 , inj₁ d1v) | [ eqv ]' | (v2 , c2v) | [ Eq.refl ]' | (v3 , d3v , cds3v , inj₂ tt) | [ Eq.refl ]' rewrite lemma-hcxds-m cds w2 v2 = Eq.refl
  lemma-hcd-mb-• cd@(d , cds , c@(inj₁ c0)) w v | (wv1 , inj₂ tt) | [ eq1 ]' | (w1 , inj₂ tt) | [ eqw ]' | (wv2 , c2) | [ Eq.refl ]' | (w2 , c2w) | [ Eq.refl ]' | (wv3 , d3 , cds3 , inj₂ tt) | [ Eq.refl ]' | (w3 , d3w , cds3w , inj₂ tt) | [ Eq.refl ]' | (v1 , inj₂ tt) | [ eqv ]' with hcmw c2w v1 | inspect (hcmw c2w) v1
  lemma-hcd-mb-• cd@(d , cds , c@(inj₁ c0)) w v | (wv1 , inj₂ tt) | [ eq1 ]' | (w1 , inj₂ tt) | [ eqw ]' | (wv2 , c2) | [ Eq.refl ]' | (w2 , c2w) | [ Eq.refl ]' | (wv3 , d3 , cds3 , inj₂ tt) | [ Eq.refl ]' | (w3 , d3w , cds3w , inj₂ tt) | [ Eq.refl ]' | (v1 , inj₂ tt) | [ eqv ]'  | (v2 , c2v) | [ Eq.refl ]' with hcxds-m-hdmw' d cds3w v2 | inspect (hcxds-m-hdmw' d cds3w) v2
  lemma-hcd-mb-• cd@(d , cds , c@(inj₁ c0)) w v | (wv1 , inj₂ tt) | [ eq1 ]' | (w1 , inj₂ tt) | [ eqw ]' | (wv2 , c2) | [ Eq.refl ]' | (w2 , c2w) | [ Eq.refl ]' | (wv3 , d3 , cds3 , inj₂ tt) | [ Eq.refl ]' | (w3 , d3w , cds3w , inj₂ tt) | [ Eq.refl ]' | (v1 , inj₂ tt) | [ eqv ]'  | (v2 , c2v) | [ Eq.refl ]' | (v3 , d3v , cds3v , inj₂ tt) | [ Eq.refl ]' rewrite lemma-hcxds-m cds w2 v2 = Eq.refl

  lemma-hcd-mb-• cd@(d , cds , c@(inj₁ c0)) w v | (wv1 , inj₁ d1) | [ eq1 ]' | (w1 , inj₂ tt) | [ eqw ]' with hcmw c0 wv1 | inspect (hcmw c0) wv1 | hcmw c0 w1 | inspect (hcmw c0) w1 
  lemma-hcd-mb-• cd@(d , cds , c@(inj₁ c0)) w v | (wv1 , inj₁ d1) | [ eq1 ]' | (w1 , inj₂ tt) | [ eqw ]' | (wv2 , c2) | [ Eq.refl ]' | (w2 , c2w) | [ Eq.refl ]' with hcxds-m-hdmw' d cds wv1 | inspect (hcxds-m-hdmw' d cds) wv1 | hcxds-m-hdmw' d cds w2 | inspect (hcxds-m-hdmw' d cds) w2
  lemma-hcd-mb-• cd@(d , cds , c@(inj₁ c0)) w v | (wv1 , inj₁ d1) | [ eq1 ]' | (w1 , inj₂ tt) | [ eqw ]' | (wv2 , c2) | [ Eq.refl ]' | (w2 , c2w) | [ Eq.refl ]' | (wv3 , d3 , cds3 , inj₂ tt) | [ Eq.refl ]' | (w3 , d3w , cds3w , inj₂ tt) | [ Eq.refl ]' with (h₂ **) (inj₂ tt) v | inspect ((h₂ **) (inj₂ tt)) v
  lemma-hcd-mb-• cd@(d , cds , c@(inj₁ c0)) w v | (wv1 , inj₁ d1) | [ eq1 ]' | (w1 , inj₂ tt) | [ eqw ]' | (wv2 , c2) | [ Eq.refl ]' | (w2 , c2w) | [ Eq.refl ]' | (wv3 , d3 , cds3 , inj₂ tt) | [ Eq.refl ]' | (w3 , d3w , cds3w , inj₂ tt) | [ Eq.refl ]' | (v1 , inj₁ d1v) | [ eqv ]' with hcmw c2w v1 | inspect (hcmw c2w) v1
  lemma-hcd-mb-• cd@(d , cds , c@(inj₁ c0)) w v | (wv1 , inj₁ d1) | [ eq1 ]' | (w1 , inj₂ tt) | [ eqw ]' | (wv2 , c2) | [ Eq.refl ]' | (w2 , c2w) | [ Eq.refl ]' | (wv3 , d3 , cds3 , inj₂ tt) | [ Eq.refl ]' | (w3 , d3w , cds3w , inj₂ tt) | [ Eq.refl ]' | (v1 , inj₁ d1v) | [ eqv ]' | (v2 , c2v) | [ Eq.refl ]' with hcxds-m-hdmw' d cds3w v2 | inspect (hcxds-m-hdmw' d cds3w) v2
  lemma-hcd-mb-• cd@(d , cds , c@(inj₁ c0)) w v | (wv1 , inj₁ d1) | [ eq1 ]' | (w1 , inj₂ tt) | [ eqw ]' | (wv2 , c2) | [ Eq.refl ]' | (w2 , c2w) | [ Eq.refl ]' | (wv3 , d3 , cds3 , inj₂ tt) | [ Eq.refl ]' | (w3 , d3w , cds3w , inj₂ tt) | [ Eq.refl ]' | (v1 , inj₁ d1v) | [ eqv ]' | (v2 , c2v) | [ Eq.refl ]' | (v3 , d3v , cds3v , inj₂ tt) | [ Eq.refl ]' rewrite lemma-hcxds-m cds w2 v2 = Eq.refl
  lemma-hcd-mb-• cd@(d , cds , c@(inj₁ c0)) w v | (wv1 , inj₁ d1) | [ eq1 ]' | (w1 , inj₂ tt) | [ eqw ]' | (wv2 , c2) | [ Eq.refl ]' | (w2 , c2w) | [ Eq.refl ]' | (wv3 , d3 , cds3 , inj₂ tt) | [ Eq.refl ]' | (w3 , d3w , cds3w , inj₂ tt) | [ Eq.refl ]' | (v1 , inj₂ tt) | [ eqv ]' with hcmw c2w v1 | inspect (hcmw c2w) v1
  lemma-hcd-mb-• cd@(d , cds , c@(inj₁ c0)) w v | (wv1 , inj₁ d1) | [ eq1 ]' | (w1 , inj₂ tt) | [ eqw ]' | (wv2 , c2) | [ Eq.refl ]' | (w2 , c2w) | [ Eq.refl ]' | (wv3 , d3 , cds3 , inj₂ tt) | [ Eq.refl ]' | (w3 , d3w , cds3w , inj₂ tt) | [ Eq.refl ]' | (v1 , inj₂ tt) | [ eqv ]'  | (v2 , c2v) | [ Eq.refl ]' with hcxds-m-hdmw' d cds3w v2 | inspect (hcxds-m-hdmw' d cds3w) v2
  lemma-hcd-mb-• cd@(d , cds , c@(inj₁ c0)) w v | (wv1 , inj₁ d1) | [ eq1 ]' | (w1 , inj₂ tt) | [ eqw ]' | (wv2 , c2) | [ Eq.refl ]' | (w2 , c2w) | [ Eq.refl ]' | (wv3 , d3 , cds3 , inj₂ tt) | [ Eq.refl ]' | (w3 , d3w , cds3w , inj₂ tt) | [ Eq.refl ]' | (v1 , inj₂ tt) | [ eqv ]'  | (v2 , c2v) | [ Eq.refl ]' | (v3 , d3v , cds3v , inj₂ tt) | [ Eq.refl ]' rewrite lemma-hcxds-m cds w2 v2 = Eq.refl


  lemma-hcd-mb-• cd@(d , cds , c@(inj₁ c0)) w v | (wv1 , inj₂ tt) | [ eq1 ]' | (w1 , inj₁ d1w) | [ eqw ]' with hcmw c0 wv1 | inspect (hcmw c0) wv1 | hcmw c0 w1 | inspect (hcmw c0) w1 
  lemma-hcd-mb-• cd@(d , cds , c@(inj₁ c0)) w v | (wv1 , inj₂ tt) | [ eq1 ]' | (w1 , inj₁ d1w) | [ eqw ]' | (wv2 , c2) | [ Eq.refl ]' | (w2 , c2w) | [ Eq.refl ]' with hcxds-m-hdmw' d cds wv1 | inspect (hcxds-m-hdmw' d cds) wv1 | hcxds-m-hdmw' d cds w2 | inspect (hcxds-m-hdmw' d cds) w2
  lemma-hcd-mb-• cd@(d , cds , c@(inj₁ c0)) w v | (wv1 , inj₂ tt) | [ eq1 ]' | (w1 , inj₁ d1w) | [ eqw ]' | (wv2 , c2) | [ Eq.refl ]' | (w2 , c2w) | [ Eq.refl ]' | (wv3 , d3 , cds3 , inj₂ tt) | [ Eq.refl ]' | (w3 , d3w , cds3w , inj₂ tt) | [ Eq.refl ]' with (h₂ **) (inj₁ d1w) v | inspect ((h₂ **) (inj₁ d1w)) v
  lemma-hcd-mb-• cd@(d , cds , c@(inj₁ c0)) w v | (wv1 , inj₂ tt) | [ eq1 ]' | (w1 , inj₁ d1w) | [ eqw ]' | (wv2 , c2) | [ Eq.refl ]' | (w2 , c2w) | [ Eq.refl ]' | (wv3 , d3 , cds3 , inj₂ tt) | [ Eq.refl ]' | (w3 , d3w , cds3w , inj₂ tt) | [ Eq.refl ]' | (v1 , inj₁ d1v) | [ eqv ]' with hcmw c2w v1 | inspect (hcmw c2w) v1
  lemma-hcd-mb-• cd@(d , cds , c@(inj₁ c0)) w v | (wv1 , inj₂ tt) | [ eq1 ]' | (w1 , inj₁ d1w) | [ eqw ]' | (wv2 , c2) | [ Eq.refl ]' | (w2 , c2w) | [ Eq.refl ]' | (wv3 , d3 , cds3 , inj₂ tt) | [ Eq.refl ]' | (w3 , d3w , cds3w , inj₂ tt) | [ Eq.refl ]' | (v1 , inj₁ d1v) | [ eqv ]' | (v2 , c2v) | [ Eq.refl ]' with hcxds-m-hdmw' d cds3w v2 | inspect (hcxds-m-hdmw' d cds3w) v2
  lemma-hcd-mb-• cd@(d , cds , c@(inj₁ c0)) w v | (wv1 , inj₂ tt) | [ eq1 ]' | (w1 , inj₁ d1w) | [ eqw ]' | (wv2 , c2) | [ Eq.refl ]' | (w2 , c2w) | [ Eq.refl ]' | (wv3 , d3 , cds3 , inj₂ tt) | [ Eq.refl ]' | (w3 , d3w , cds3w , inj₂ tt) | [ Eq.refl ]' | (v1 , inj₁ d1v) | [ eqv ]' | (v2 , c2v) | [ Eq.refl ]' | (v3 , d3v , cds3v , inj₂ tt) | [ Eq.refl ]' rewrite lemma-hcxds-m cds w2 v2 = Eq.refl
  lemma-hcd-mb-• cd@(d , cds , c@(inj₁ c0)) w v | (wv1 , inj₂ tt) | [ eq1 ]' | (w1 , inj₁ d1w) | [ eqw ]' | (wv2 , c2) | [ Eq.refl ]' | (w2 , c2w) | [ Eq.refl ]' | (wv3 , d3 , cds3 , inj₂ tt) | [ Eq.refl ]' | (w3 , d3w , cds3w , inj₂ tt) | [ Eq.refl ]' | (v1 , inj₂ tt) | [ eqv ]' with hcmw c2w v1 | inspect (hcmw c2w) v1
  lemma-hcd-mb-• cd@(d , cds , c@(inj₁ c0)) w v | (wv1 , inj₂ tt) | [ eq1 ]' | (w1 , inj₁ d1w) | [ eqw ]' | (wv2 , c2) | [ Eq.refl ]' | (w2 , c2w) | [ Eq.refl ]' | (wv3 , d3 , cds3 , inj₂ tt) | [ Eq.refl ]' | (w3 , d3w , cds3w , inj₂ tt) | [ Eq.refl ]' | (v1 , inj₂ tt) | [ eqv ]'  | (v2 , c2v) | [ Eq.refl ]' with hcxds-m-hdmw' d cds3w v2 | inspect (hcxds-m-hdmw' d cds3w) v2
  lemma-hcd-mb-• cd@(d , cds , c@(inj₁ c0)) w v | (wv1 , inj₂ tt) | [ eq1 ]' | (w1 , inj₁ d1w) | [ eqw ]' | (wv2 , c2) | [ Eq.refl ]' | (w2 , c2w) | [ Eq.refl ]' | (wv3 , d3 , cds3 , inj₂ tt) | [ Eq.refl ]' | (w3 , d3w , cds3w , inj₂ tt) | [ Eq.refl ]' | (v1 , inj₂ tt) | [ eqv ]'  | (v2 , c2v) | [ Eq.refl ]' | (v3 , d3v , cds3v , inj₂ tt) | [ Eq.refl ]' rewrite lemma-hcxds-m cds w2 v2 = Eq.refl


  lemma-hh=hcd-ma : ∀ cd wa -> (hh **) cd [ wa ]ₗ ≡ hcd-ma cd wa
  lemma-hh=hcd-ma cd@(d , cds , c) [ a ]ʷ with h₁ c a | (h₁ **) c [ a ]ʷ | inspect (h₁ c) a | inspect ((h₁ **) c) [ a ]ʷ 
  lemma-hh=hcd-ma cd@(d , cds , c) [ a ]ʷ | (wm , c') | (wm1 , c1) | [ Eq.refl ]' | [ Eq.refl ]' with hcdws cds wm | hcxds-m cds wm1 | inspect (hcdws cds) wm | inspect (hcxds-m cds) wm1
  lemma-hh=hcd-ma cd@(d , cds , c) [ a ]ʷ | (wm , c') | (wm1 , c1) | [ Eq.refl ]' | [ Eq.refl ]' | (wm' , cds') | (wm2 , cds2) | [ Eq.refl ]' | [ Eq.refl ]' with hdmw' d wm' | hdmw' d wm2 | inspect (hdmw' d) wm' | inspect (hdmw' d) wm2
  lemma-hh=hcd-ma cd@(d , cds , c) [ a ]ʷ | (wm , c') | (wm1 , c1) | [ Eq.refl ]' | [ Eq.refl ]' | (wm' , cds') | (wm2 , cds2) | [ Eq.refl ]' | [ Eq.refl ]' | (wm'' , d') | (wm3 , d3) | [ Eq.refl ]' | [ Eq.refl ]'
    rewrite aux-hcdws=hcxds-m cds wm | aux-hcdws=hcxds-m cds wm1
    = Eq.refl
    
  lemma-hh=hcd-ma cd@(d , cds , c) ε = begin
    (ε , d , cds , c) ≡⟨ Eq.sym (lemma-hcd-ma-ε d cds c) ⟩
    hcd-ma (d , cds , c) ε ∎
    where open Eq.≡-Reasoning

  lemma-hh=hcd-ma cd@(d , cds , c) (wa • wa₁) with lemma-hh=hcd-ma cd wa | (hh **) cd [ wa ]ₗ | inspect ((hh **) cd) [ wa ]ₗ  
  lemma-hh=hcd-ma cd@(d , cds , c) (wa • wa₁) | ih | (wm1 , cd1) | [ Eq.refl ]' with lemma-hh=hcd-ma cd1 wa₁ | (hh **) cd1 [ wa₁ ]ₗ | inspect ((hh **) cd1) [ wa₁ ]ₗ  
  lemma-hh=hcd-ma cd@(d , cds , c) (wa • wa₁) | ih | (wm1 , cd1) | [ Eq.refl ]' | ih2 | (wm2 , cd2) | [ Eq.refl ]'
    =
    let (wm1` , cd1`) = hcd-ma cd wa in 
    let (wm2` , cd2`) = hcd-ma cd1` wa₁ in 
    let (wm2`a , cd2`a) = hcd-ma cd1 wa₁ in 
    
    begin
    (hh **) cd [ wa • wa₁ ]ₗ ≡⟨ Eq.refl ⟩
    wm1 • wm2 , cd2 ≡⟨ Eq.cong (λ xx → xx • wm2 , cd2) (Eq.cong proj₁ ih) ⟩
    wm1` • wm2 , cd2 ≡⟨ Eq.cong₂ (\ xx yy -> wm1` • xx , yy) (Eq.cong proj₁ ih2) (Eq.cong proj₂ ih2) ⟩
    wm1` • wm2`a , cd2`a ≡⟨ Eq.cong₂ (\ xx yy -> wm1` • xx , yy)
      (Eq.cong proj₁ (Eq.cong ((\ xx -> hcd-ma xx wa₁) ) (Eq.cong proj₂ ih)))
      (Eq.cong proj₂ (Eq.cong ((\ xx -> hcd-ma xx wa₁) ) (Eq.cong proj₂ ih))) ⟩
    wm1` • wm2` , cd2` ≡⟨ Eq.refl ⟩
    (wm1` • wm2` , cd2`) ≡⟨ Eq.sym (lemma-hcd-ma-• cd wa wa₁) ⟩
    hcd-ma cd (wa • wa₁) ∎
    where open Eq.≡-Reasoning

  h₁-wd-h : ∀ c u t -> u ===₁ t -> ((h₁ **) c u) ~₁ ((h₁ **) c t)
  h₁-wd-h c u t eq =  begin
    ((h₁ **) c u) ≈⟨ h-wd-ax₁ c eq ⟩
    ((h₁ **) c t) ∎
    where open SR (PW.×-setoid ws₀ (setoid (C ⊎ ⊤)))

  h₂-wd-h : ∀ c u t -> u ===₂ t -> ((h₂ **) c u) ~₂ ((h₂ **) c t)
  h₂-wd-h c u t eq =  begin
    ((h₂ **) c u) ≈⟨ h-wd-ax₂ c eq ⟩
    ((h₂ **) c t) ∎
    where open SR (PW.×-setoid ws₀ (setoid (D ⊎ ⊤)))

  hcxd1-m-congl : ∀ cd w v -> w ≈₀ v -> hcxd1-m cd w .proj₁ ≈₀ hcxd1-m cd v .proj₁
  hcxd1-m-congl cd@(c , d) w v eq with hdmw d w | hdmw d v | inspect (hdmw d) w | inspect (hdmw d) v
  hcxd1-m-congl cd@(c , d) w v eq | (wm1 , d1) | (wm1' , d1') | [ Eq.refl ]' | [ Eq.refl ]' with hcmw c wm1 | hcmw c wm1' | inspect (hcmw c) wm1 | inspect (hcmw c) wm1'
  hcxd1-m-congl cd@(c , d) w v eq | (wm1 , d1) | (wm1' , d1') | [ Eq.refl ]' | [ Eq.refl ]' | (wm2 , d2) | (wm2' , d2') | [ Eq.refl ]' | [ Eq.refl ]' = claim2
    where
    claim1 : wm1 ≈₀ wm1'
    claim1 = hdmw-cong d w v eq

    claim2 : wm2 ≈₀ wm2'
    claim2 = hcmw-cong c wm1 wm1' claim1

  hcxd1-m-congr : ∀ cd w v -> w ≈₀ v -> hcxd1-m cd w .proj₂ ≡ hcxd1-m cd v .proj₂
  hcxd1-m-congr cd@(c , d) w v eq with hdmw d w | hdmw d v | inspect (hdmw d) w | inspect (hdmw d) v
  hcxd1-m-congr cd@(c , d) w v eq | (wm1 , d1) | (wm1' , d1') | [ Eq.refl ]' | [ Eq.refl ]' with hcmw c wm1 | hcmw c wm1' | inspect (hcmw c) wm1 | inspect (hcmw c) wm1'
  hcxd1-m-congr cd@(c , d) w v eq | (wm1 , d1) | (wm1' , d1') | [ Eq.refl ]' | [ Eq.refl ]' | (wm2 , d2) | (wm2' , d2') | [ Eq.refl ]' | [ Eq.refl ]' = claim3
    where
    claim1 : wm1 ≈₀ wm1'
    claim1 = hdmw-cong d w v eq

    claim1r : d1 ≡ d1'
    claim1r = hdmw-cong2 d w v eq

    claim2 : wm2 ≈₀ wm2'
    claim2 = hcmw-cong c wm1 wm1' claim1

    claim2r : d2 ≡ d2'
    claim2r = hcmw-cong2 c wm1 wm1' claim1

    claim3 : (d2 , d1) ≡ (d2' , d1')
    claim3 = ≡×≡⇒≡ (claim2r , claim1r)

  hcxds-m-congl : ∀ cds w v -> w ≈₀ v -> hcxds-m cds w .proj₁ ≈₀ hcxds-m cds v .proj₁
  hcxds-m-congl [] w v eq = eq
  hcxds-m-congl (x ∷ cds) w v eq with hcxd1-m x w .proj₁ | hcxd1-m x v .proj₁ | inspect (\ xx -> proj₁ (hcxd1-m x xx)) w | inspect (\ xx -> proj₁ (hcxd1-m x xx)) v
  hcxds-m-congl (x ∷ cds) w v eq | w' | v' | [ Eq.refl ]' | [ Eq.refl ]' with hcxd1-m-congl x w v eq | hcxds-m-congl cds w' v' (hcxd1-m-congl x w v eq)
  hcxds-m-congl (x ∷ cds) w v eq | w' | v' | [ Eq.refl ]' | [ Eq.refl ]' | eqh | eqt = eqt

  hcxds-m-congr : ∀ cds w v -> w ≈₀ v -> hcxds-m cds w .proj₂ ≡ hcxds-m cds v .proj₂
  hcxds-m-congr [] w v eq = Eq.refl
  hcxds-m-congr (x ∷ cds) w v eq rewrite hcxd1-m-congr x w v eq | hcxds-m-congr cds (hcxd1-m x w .proj₁) (hcxd1-m x v .proj₁) (hcxd1-m-congl x w v eq) = Eq.refl

  lemma-hb : ∀ d b -> h₂ d b ≡ (h₂ **) d [ b ]ʷ
  lemma-hb (inj₁ x) b = Eq.refl
  lemma-hb (inj₂ y) b = Eq.refl

  lemma-hdb : ∀ d b -> hdb d b ≡ (h₂ **) (inj₁ d) [ b ]ʷ
  lemma-hdb d b = Eq.refl

  htb : ⊤ -> B -> Word M × (D ⊎ ⊤)
  htb tt b = h₂ (inj₂ tt) b

  lemma-htb : ∀ b -> htb tt b .proj₁ ≡ (h₂ **) (inj₂ tt) [ b ]ʷ .proj₁
  lemma-htb b = Eq.refl


  lemma-hh=hcdmb1 : ∀ cd b -> hh cd (inj₂ b) ≡ hcd-mb cd [ b ]ʷ
  lemma-hh=hcdmb1 (d , cds , inj₁ c) b with h₂ I₂ b
  lemma-hh=hcdmb1 (d , cds , inj₁ c) b | (wm1 , inj₁ d1) rewrite aux-hcdmw=hcxds-m-hdmw'2 d cds (hcmw c wm1 .proj₁) = Eq.refl
  lemma-hh=hcdmb1 (d , cds , inj₁ c) b | (wm1 , inj₂ tt) rewrite aux-hcdmw=hcxds-m-hdmw'2 d cds (hcmw c wm1 .proj₁) = Eq.refl
  lemma-hh=hcdmb1 (d , [] , inj₂ tt) b = Eq.refl
  lemma-hh=hcdmb1 (d , (c0 , d0) ∷ cds , inj₂ tt) b with hdb d0 b
  lemma-hh=hcdmb1 (d , (c0 , d0) ∷ cds , inj₂ tt) b | (wm , inj₁ d1) rewrite aux-hcdmw=hcxds-m-hdmw'2 d cds (hcmw c0 wm .proj₁) = Eq.refl
  lemma-hh=hcdmb1 (d , (c0 , d0) ∷ cds , inj₂ tt) b | (wm , inj₂ tt) rewrite aux-hcdmw=hcxds-m-hdmw'2 d cds (hcmw c0 wm .proj₁) = Eq.refl

  lemma-hh=hcd-mb : ∀ cd wb -> (hh **) cd [ wb ]ᵣ ≡ hcd-mb cd wb
  lemma-hh=hcd-mb (d , cds , c) [ x ]ʷ = lemma-hh=hcdmb1 (d , cds , c) x
  lemma-hh=hcd-mb (d , cds , c) ε rewrite lemma-hcd-mb-ε d cds c = Eq.refl
  
  lemma-hh=hcd-mb cd@(d , cds , c) (w • v) with lemma-hh=hcd-mb cd w | (hh **) cd [ w ]ᵣ | inspect ((hh **) cd) [ w ]ᵣ  
  lemma-hh=hcd-mb cd@(d , cds , c) (w • v) | ih | (wm1 , cd1) | [ Eq.refl ]' with lemma-hh=hcd-mb cd1 v | (hh **) cd1 [ v ]ᵣ | inspect ((hh **) cd1) [ v ]ᵣ  
  lemma-hh=hcd-mb cd@(d , cds , c) (w • v) | ih | (wm1 , cd1) | [ Eq.refl ]' | ih2 | (wm2 , cd2) | [ Eq.refl ]' =
    let (wm1b , cd1b) = hcd-mb cd w in 
    let (wm2b , cd2b) = hcd-mb cd1b v in 
    let (wm3b , cd3b) = hcd-mb cd1 v in 
    begin
    (hh **) cd [ w • v ]ᵣ ≡⟨ Eq.refl ⟩
    (wm1 • wm2 , cd2) ≡⟨ Eq.cong (\xx -> xx • wm2 , cd2) (Eq.cong proj₁ (lemma-hh=hcd-mb cd w)) ⟩
    (wm1b • wm2 , cd2) ≡⟨ Eq.cong₂ (\xx yy -> wm1b • xx , yy) (Eq.cong proj₁ ih2) (Eq.cong proj₂ ih2) ⟩
    (wm1b • wm3b , cd3b) ≡⟨ Eq.cong₂ (\xx yy -> wm1b • xx , yy)
      (Eq.cong proj₁ (Eq.cong ((\ xx -> hcd-mb xx v) ) (Eq.cong proj₂ ih)))
      (Eq.cong proj₂ (Eq.cong ((\ xx -> hcd-mb xx v) ) (Eq.cong proj₂ ih))) ⟩
    (wm1b • wm2b , cd2b) ≡⟨ Eq.sym (lemma-hcd-mb-• cd w v) ⟩
    hcd-mb cd (w • v) ∎
    where open Eq.≡-Reasoning

  claim-s : ∀ d w v -> w ===₂ v -> hcd-mb (d , [] , inj₂ tt) w ~ hcd-mb (d , [] , inj₂ tt) v
  claim-s d w v x with (h₂ **) d w | (h₂ **) d v | inspect ((h₂ **) d) w | inspect ((h₂ **) d) v | h₂-wd-h d w v x
  claim-s d w v x | (w1 , inj₁ d1) | (v1 , inj₂ tt) | [ eqw ]' | [ eqv ]' | (ee1 , eq1) rewrite eqw | eqv with eq1
  ... | () 
  claim-s d w v x | (w1 , inj₂ tt) | (v1 , inj₁ d1') | [ eqw ]' | [ eqv ]' | (ee1 , eq1) rewrite eqw | eqv with eq1
  ... | () 
  claim-s d w v x | (w1 , inj₂ tt) | (v1 , inj₂ tt) | [ eqw ]' | [ eqv ]' | (ee1 , eq1) rewrite eqw | eqv
    = begin
    w1 , inj₂ tt , [] , inj₂ tt ≈⟨ claim1 , ≡×≡⇒≡ (eq1 , Eq.refl) ⟩
    v1 , inj₂ tt , [] , inj₂ tt ∎
    where
    open SR mcdₛ
    claim1 : w1 ≈₀ v1
    claim1 rewrite eqv | eqw = ee1

  claim-s d w v x | (w1 , inj₁ d1) | (v1 , inj₁ d1') | [ eqw ]' | [ eqv ]' | (ee1 , eq1)
    = begin
    w1 , inj₁ d1 , [] , inj₂ tt ≈⟨ claim1 , ≡×≡⇒≡ (claim2 , Eq.refl) ⟩
    v1 , inj₁ d1' , [] , inj₂ tt ∎
    where
    open SR mcdₛ
    claim1 : w1 ≈₀ v1
    claim1 rewrite eqv | eqw = ee1

    claim2 : ((D ⊎ ⊤) ∋ (inj₁ d1)) ≡ inj₁ d1'
    claim2 rewrite eqv | eqw = eq1

  hcxds-m-hdmw'-cong : ∀ d cds w v -> w ≈₀ v -> hcxds-m-hdmw' d cds w .proj₁ ≈₀ hcxds-m-hdmw' d cds v .proj₁ 
  hcxds-m-hdmw'-cong d cds w v eq with hcxds-m-congl cds w v eq
  hcxds-m-hdmw'-cong d cds w v eq | h1 with hdmw-cong' d (hcxds-m cds w .proj₁) (hcxds-m cds v .proj₁) h1
  hcxds-m-hdmw'-cong d cds w v eq | h1 | h2 = h2

  hcxds-m-hdmw'-cong2 : ∀ d cds w v -> w ≈₀ v -> hcxds-m-hdmw' d cds w .proj₂ .proj₁ ≡ hcxds-m-hdmw' d cds v .proj₂ .proj₁ 
  hcxds-m-hdmw'-cong2 d cds w v eq with hcxds-m-congl cds w v eq
  hcxds-m-hdmw'-cong2 d cds w v eq | h1 with hdmw-cong'2 d (hcxds-m cds w .proj₁) (hcxds-m cds v .proj₁) h1
  hcxds-m-hdmw'-cong2 d cds w v eq | h1 | h2 = h2


  hcxds-m-hdmw'-cong3 : ∀ d cds w v -> w ≈₀ v -> hcxds-m-hdmw' d cds w .proj₂ .proj₂ .proj₁ ≡ hcxds-m-hdmw' d cds v .proj₂ .proj₂ .proj₁ 
  hcxds-m-hdmw'-cong3 d cds w v eq with hcxds-m-congl cds w v eq
  hcxds-m-hdmw'-cong3 d cds w v eq | h1 with hdmw-cong'2 d (hcxds-m cds w .proj₁) (hcxds-m cds v .proj₁) h1
  hcxds-m-hdmw'-cong3 d cds w v eq | h1 | h2 = hcxds-m-congr cds w v eq


  lemma-hcm'=h₁ : ∀ c m -> hcm' c m ≡ (h₁ **) c (f₁ m)
  lemma-hcm'=h₁ (inj₁ x) m with hcme x m
  lemma-hcm'=h₁ (inj₁ x) m | (w , c' , hyp) = Eq.sym hyp
  lemma-hcm'=h₁ (inj₂ tt) m rewrite htme m = Eq.refl

  lemma-hdm'=h₂ : ∀ c m -> hdm' c m ≡ (h₂ **) c (f₂ m)
  lemma-hdm'=h₂ (inj₁ x) m with hdme x m
  lemma-hdm'=h₂ (inj₁ x) m | (w , c' , hyp) = Eq.sym hyp
  lemma-hdm'=h₂ (inj₂ tt) m rewrite htme₂ m = Eq.refl

  lemma-hcd-ma=hcdm : ∀ cd m -> hcd-ma cd (f₁ m) ≡ hcdm cd m
  lemma-hcd-ma=hcdm (d , cds , c) m rewrite lemma-hcm'=h₁ c m | aux-hcdws=hcxds-m cds ((h₁ **) c (f₁ m) .proj₁) | aux104 d cds ((h₁ **) c (f₁ m) .proj₁) = Eq.refl
    where
    open Eq.≡-Reasoning

  lemma-hcd-mb=hcdm : ∀ cd m -> hcd-mb cd (f₂ m) ≡ hcdm cd m
  lemma-hcd-mb=hcdm cd@(d , cds , inj₁ c) m rewrite htme₂ m | aux-hcdws=hcxds-m cds ((hcm c m) .proj₁) = Eq.refl
  lemma-hcd-mb=hcdm (d , [] , inj₂ tt) m rewrite htme₂ m | lemma-hdm'=h₂ d m = Eq.refl
  lemma-hcd-mb=hcdm (d , x@(c0 , d0) ∷ cds , inj₂ tt) m rewrite htme₂ m | Eq.sym (lemma-hdm'=h₂ (inj₁ d0) m) | hdme d0 m .proj₂ .proj₂ | aux-hcdws=hcxds-m cds ((hcmw c0 (hdme d0 m .proj₁)) .proj₁) = Eq.refl
    where
    open Eq.≡-Reasoning


  hhh-wd-ax : ∀ (c : CD){u t : Word Y} -> u ===₃ t -> ((hh **) c u) ~ ((hh **) c t)
  hhh-wd-ax cd@(d , cds , c) {u} {t} (left {u₁} {v} x) = claim2
    where
    claim : hcd-ma cd u₁ ~ hcd-ma cd v
    claim with (h₁ **) c u₁ | (h₁ **) c v | inspect ((h₁ **) c) u₁ | inspect ((h₁ **) c) v
    claim | (wm1 , c1) | (wm1' , c1') | [ Eq.refl ]' | [ Eq.refl ]' with hcxds-m cds wm1 | hcxds-m cds wm1' | inspect (hcxds-m cds) wm1 | inspect (hcxds-m cds) wm1'
    claim | (wm1 , c1) | (wm1' , c1') | [ Eq.refl ]' | [ Eq.refl ]' | (wm2 , cds2) | (wm2' , cds2') | [ Eq.refl ]' | [ Eq.refl ]' with hdmw' d wm2 | hdmw' d wm2' | inspect (hdmw' d) wm2 | inspect (hdmw' d) wm2'
    claim | (wm1 , c1) | (wm1' , c1') | [ Eq.refl ]' | [ Eq.refl ]' | (wm2 , cds2) | (wm2' , cds2') | [ Eq.refl ]' | [ Eq.refl ]' | (wm3 , d3) | (wm3' , d3') | [ Eq.refl ]' | [ Eq.refl ]'
      with h₁-wd-h c u₁ v x
    ... | (eqv1 , eq1 )  = claim4 , claim5 where

      claim2 : wm1 ≈₀ wm1'
      claim2 = eqv1

      claim3 : wm2 ≈₀ wm2'
      claim3 = hcxds-m-congl cds wm1 wm1' claim2

      claim4 : wm3 ≈₀ wm3'
      claim4 = hdmw-cong' d wm2 wm2' claim3

      claim2' : c1 ≡ c1'
      claim2' = eq1
      
      claim3' : cds2 ≡ cds2'
      claim3' = hcxds-m-congr cds wm1 wm1' claim2
      
      claim4' : d3 ≡ d3'
      claim4' = hdmw-cong'2 d wm2 wm2' claim3

      claim5 : (d3 , cds2 , c1) ≡ (d3' , cds2' , c1')
      claim5 = ≡×≡⇒≡ (claim4' , (≡×≡⇒≡ (claim3' , eq1)))

    claim2 : ((hh **) cd u) ~ ((hh **) cd t)
    claim2 = begin
      ((hh **) cd u) ≡⟨ lemma-hh=hcd-ma (d , cds , c) u₁ ⟩
      hcd-ma cd u₁ ≈⟨ claim ⟩
      hcd-ma cd v ≡⟨ Eq.sym (lemma-hh=hcd-ma (d , cds , c) v) ⟩
      ((hh **) cd t) ∎
      where
      open SR mcdₛ

  hhh-wd-ax cd@(d , [] , c@(inj₂ tt)) {u} {t} (right {u₁} {v} x) = claim2
    where 
    open SR mcdₛ
    claim1 : hcd-mb (d , [] , inj₂ tt) u₁ ~ hcd-mb (d , [] , inj₂ tt) v
    claim1 = claim-s d u₁ v x

    claim2 : (hh **) (d , [] , inj₂ tt) [ u₁ ]ᵣ ~ (hh **) (d , [] , inj₂ tt) [ v ]ᵣ
    claim2 = begin
      (hh **) (d , [] , inj₂ tt) [ u₁ ]ᵣ ≡⟨ lemma-hh=hcd-mb (d , [] , inj₂ tt) u₁ ⟩
      (hcd-mb) (d , [] , inj₂ tt) u₁ ≈⟨ claim1 ⟩
      (hcd-mb) (d , [] , inj₂ tt) v ≡⟨ Eq.sym (lemma-hh=hcd-mb (d , [] , inj₂ tt) v) ⟩
      (hh **) (d , [] , inj₂ tt) [ v ]ᵣ ∎
     
    
  hhh-wd-ax cd@(d , cds@(he@(c0 , d0) ∷ ta) , c@(inj₂ tt)) {u} {t} (right {u₁} {v} px) = claim2ok
    where
    claim : hcd-mb cd u₁ ~ hcd-mb cd v
    claim with (h₂ **) (inj₁ d0) u₁ | (h₂ **) (inj₁ d0) v | inspect ((h₂ **) (inj₁ d0)) u₁ | inspect ((h₂ **) (inj₁ d0)) v
    
    claim | wm1 , inj₂ y | wm1' , inj₁ d0' | [ eq1 ]' | [ eq2 ]' rewrite eq1 | eq2  with hcmw c0 wm1 | inspect (hcmw c0) wm1 | hcmw c0 wm1' | inspect (hcmw c0) wm1'
    claim | wm1 , inj₂ y | wm1' , inj₁ d0' | [ eq1 ]' | [ eq2 ]' | (wm2 , c2) | [ Eq.refl ]' | (wm2' , c2') | [ Eq.refl ]' with hcxds-m-hdmw' d ta wm2 | inspect (hcxds-m-hdmw' d ta) wm2 | hcxds-m-hdmw' d ta wm2' | inspect (hcxds-m-hdmw' d ta) wm2'
    claim | wm1 , inj₂ y | wm1' , inj₁ d0' | [ eq1 ]' | [ eq2 ]' | (wm2 , c2) | [ Eq.refl ]' | (wm2' , c2') | [ Eq.refl ]' | (wm3 , d3 , cds3 , c3) | [ Eq.refl ]' | (wm3' , d3' , cds3' , c3') | [ Eq.refl ]' rewrite eq1 | eq2 with h₂-wd-h (inj₁ d0) u₁ v px
    ... | (eqv1 , eq1a ) rewrite eq1 | eq2 | eq1a with eq1a
    ... | ()

    claim | wm1 , inj₁ d0' | wm1' , inj₂ y' | [ eq1 ]' | [ eq2 ]' rewrite eq1 | eq2  with hcmw c0 wm1 | inspect (hcmw c0) wm1 | hcmw c0 wm1' | inspect (hcmw c0) wm1'
    claim | wm1 , inj₁ d0' | wm1' , inj₂ y' | [ eq1 ]' | [ eq2 ]' | (wm2 , c2) | [ Eq.refl ]' | (wm2' , c2') | [ Eq.refl ]' with hcxds-m-hdmw' d ta wm2 | inspect (hcxds-m-hdmw' d ta) wm2 | hcxds-m-hdmw' d ta wm2' | inspect (hcxds-m-hdmw' d ta) wm2'
    claim | wm1 , inj₁ d0' | wm1' , inj₂ y' | [ eq1 ]' | [ eq2 ]' | (wm2 , c2) | [ Eq.refl ]' | (wm2' , c2') | [ Eq.refl ]' | (wm3 , d3 , cds3 , c3) | [ Eq.refl ]' | (wm3' , d3' , cds3' , c3') | [ Eq.refl ]' rewrite eq1 | eq2 with h₂-wd-h (inj₁ d0) u₁ v px
    ... | (eqv1 , eq1a ) rewrite eq1 | eq2 | eq1a with eq1a
    ... | ()

    claim | wm1 , inj₂ y | wm1' , inj₂ y₁ | [ eq1 ]' | [ eq2 ]' rewrite eq1 | eq2  with hcmw c0 wm1 | inspect (hcmw c0) wm1 | hcmw c0 wm1' | inspect (hcmw c0) wm1'
    claim | wm1 , inj₂ y | wm1' , inj₂ y₁ | [ eq1 ]' | [ eq2 ]' | (wm2 , c2) | [ Eq.refl ]' | (wm2' , c2') | [ Eq.refl ]' with hcxds-m-hdmw' d ta wm2 | inspect (hcxds-m-hdmw' d ta) wm2 | hcxds-m-hdmw' d ta wm2' | inspect (hcxds-m-hdmw' d ta) wm2'
    claim | wm1 , inj₂ y | wm1' , inj₂ y₁ | [ eq1 ]' | [ eq2 ]' | (wm2 , c2) | [ Eq.refl ]' | (wm2' , c2') | [ Eq.refl ]' | (wm3 , d3 , cds3 , c3) | [ Eq.refl ]' | (wm3' , d3' , cds3' , c3') | [ Eq.refl ]' rewrite eq1 | eq2 with h₂-wd-h (inj₁ d0) u₁ v px
    ... | (eqv1 , eq1a ) = claim5
      where
      claim5 =
        begin
        wm3 , d3 , cds3 , inj₁ c2 ≡⟨ Eq.cong₂ (λ xx yy → wm3 , d3 , xx , yy) claim6a (Eq.cong inj₁ claim7a) ⟩
        wm3 , d3 , cds3' , inj₁ c2' ≈⟨ claim4 , Eq.cong (λ xx → xx , cds3' , inj₁ c2') claim5a  ⟩
        wm3' , d3' , cds3' , inj₁ c2' ∎

        where
        open SR mcdₛ

        c1 : wm1 ≈₀ wm1'
        c1 rewrite Eq.cong proj₁ (eq1) | Eq.cong proj₁ (eq2) = eqv1

        claim3 : wm2 ≈₀ wm2'
        claim3 = hcmw-cong c0 wm1 wm1' c1

        claim4 : wm3 ≈₀ wm3'
        claim4 = hcxds-m-hdmw'-cong d ta wm2 wm2' claim3

        claim5a : d3 ≡ d3'
        claim5a = hcxds-m-hdmw'-cong2 d ta wm2 wm2' claim3

        claim6a : cds3 ≡ cds3'
        claim6a = hcxds-m-hdmw'-cong3 d ta wm2 wm2' claim3

        claim7a : c2 ≡ c2'
        claim7a = hcmw-cong2 c0 wm1 wm1' c1

    claim | wm1 , inj₁ d0' | wm1' , inj₁ d0'₁ | [ eq1 ]' | [ eq2 ]' rewrite eq1 | eq2  with hcmw c0 wm1 | inspect (hcmw c0) wm1 | hcmw c0 wm1' | inspect (hcmw c0) wm1'
    claim | wm1 , inj₁ d0' | wm1' , inj₁ d0'₁ | [ eq1 ]' | [ eq2 ]' | (wm2 , c2) | [ Eq.refl ]' | (wm2' , c2') | [ Eq.refl ]' with hcxds-m-hdmw' d ta wm2 | inspect (hcxds-m-hdmw' d ta) wm2 | hcxds-m-hdmw' d ta wm2' | inspect (hcxds-m-hdmw' d ta) wm2'
    claim | wm1 , inj₁ d0' | wm1' , inj₁ d0'₁ | [ eq1 ]' | [ eq2 ]' | (wm2 , c2) | [ Eq.refl ]' | (wm2' , c2') | [ Eq.refl ]' | (wm3 , d3 , cds3 , c3) | [ Eq.refl ]' | (wm3' , d3' , cds3' , c3') | [ Eq.refl ]' rewrite eq1 | eq2 with h₂-wd-h (inj₁ d0) u₁ v px
    ... | (eqv1 , eq1a ) = claim5
      where
      claim5 =
        begin
        wm3 , d3 , (c2 , d0') ∷ cds3 , inj₂ tt ≡⟨ Eq.cong₂ (λ xx yy → wm3 , d3 , (c2 , d0') ∷ xx , yy) claim6a Eq.refl ⟩
        wm3 , d3 , (c2 , d0') ∷ cds3' , inj₂ tt ≈⟨ claim4 , Eq.cong₂ (\ xx yy -> xx , yy ∷ cds3' , inj₂ tt) claim5a (≡×≡⇒≡ (claim7a , c2a)) ⟩ 
        wm3' , d3' , (c2' , d0'₁) ∷ cds3' , inj₂ tt ∎

        where
        open SR mcdₛ

        c1 : wm1 ≈₀ wm1'
        c1 rewrite Eq.cong proj₁ (eq1) | Eq.cong proj₁ (eq2) = eqv1

        claim3 : wm2 ≈₀ wm2'
        claim3 = hcmw-cong c0 wm1 wm1' c1

        claim4 : wm3 ≈₀ wm3'
        claim4 = hcxds-m-hdmw'-cong d ta wm2 wm2' claim3

        claim5a : d3 ≡ d3'
        claim5a = hcxds-m-hdmw'-cong2 d ta wm2 wm2' claim3

        claim6a : cds3 ≡ cds3'
        claim6a = hcxds-m-hdmw'-cong3 d ta wm2 wm2' claim3

        claim7a : c2 ≡ c2'
        claim7a = hcmw-cong2 c0 wm1 wm1' c1


        cl2 : inj₁ d0' ≡ inj₁ d0'₁
        cl2 rewrite Eq.cong proj₂ (Eq.sym eq1) | Eq.cong proj₂ (eq2) = eq1a

        c2a : d0' ≡ d0'₁
        c2a = inj₁-injective cl2

    claim2ok : ((hh **) cd u) ~ ((hh **) cd t)
    claim2ok = begin
      ((hh **) cd u) ≡⟨ lemma-hh=hcd-mb (d , cds , c) u₁ ⟩
      hcd-mb cd u₁ ≈⟨ claim ⟩
      hcd-mb cd v ≡⟨ Eq.sym (lemma-hh=hcd-mb (d , cds , c) v) ⟩
      ((hh **) cd t) ∎
      where
      open SR mcdₛ
    
  hhh-wd-ax cd@(d , cds , c@(inj₁ c0)) {u} {t} (right {u₁} {v} px) = claim2ok
    where
    claim : hcd-mb cd u₁ ~ hcd-mb cd v
    claim with (h₂ **) (inj₂ tt) u₁ | (h₂ **) (inj₂ tt) v | inspect ((h₂ **) (inj₂ tt)) u₁ | inspect ((h₂ **) (inj₂ tt)) v
    
    claim | wm1 , inj₂ y | wm1' , inj₁ d0' | [ eq1 ]' | [ eq2 ]' rewrite eq1 | eq2  with hcmw c0 wm1 | inspect (hcmw c0) wm1 | hcmw c0 wm1' | inspect (hcmw c0) wm1'
    claim | wm1 , inj₂ y | wm1' , inj₁ d0' | [ eq1 ]' | [ eq2 ]' | (wm2 , c2) | [ Eq.refl ]' | (wm2' , c2') | [ Eq.refl ]' with hcxds-m-hdmw' d cds wm2 | inspect (hcxds-m-hdmw' d cds) wm2 | hcxds-m-hdmw' d cds wm2' | inspect (hcxds-m-hdmw' d cds) wm2'
    claim | wm1 , inj₂ y | wm1' , inj₁ d0' | [ eq1 ]' | [ eq2 ]' | (wm2 , c2) | [ Eq.refl ]' | (wm2' , c2') | [ Eq.refl ]' | (wm3 , d3 , cds3 , c3) | [ Eq.refl ]' | (wm3' , d3' , cds3' , c3') | [ Eq.refl ]' rewrite eq1 | eq2 with h₂-wd-h (inj₂ tt) u₁ v px
    ... | (eqv1 , eq1a ) rewrite eq1 | eq2 | eq1a with eq1a
    ... | ()

    claim | wm1 , inj₁ d0' | wm1' , inj₂ y' | [ eq1 ]' | [ eq2 ]' rewrite eq1 | eq2  with hcmw c0 wm1 | inspect (hcmw c0) wm1 | hcmw c0 wm1' | inspect (hcmw c0) wm1'
    claim | wm1 , inj₁ d0' | wm1' , inj₂ y' | [ eq1 ]' | [ eq2 ]' | (wm2 , c2) | [ Eq.refl ]' | (wm2' , c2') | [ Eq.refl ]' with hcxds-m-hdmw' d cds wm2 | inspect (hcxds-m-hdmw' d cds) wm2 | hcxds-m-hdmw' d cds wm2' | inspect (hcxds-m-hdmw' d cds) wm2'
    claim | wm1 , inj₁ d0' | wm1' , inj₂ y' | [ eq1 ]' | [ eq2 ]' | (wm2 , c2) | [ Eq.refl ]' | (wm2' , c2') | [ Eq.refl ]' | (wm3 , d3 , cds3 , c3) | [ Eq.refl ]' | (wm3' , d3' , cds3' , c3') | [ Eq.refl ]' rewrite eq1 | eq2 with h₂-wd-h (inj₂ tt) u₁ v px
    ... | (eqv1 , eq1a ) rewrite eq1 | eq2 | eq1a with eq1a
    ... | ()

    claim | wm1 , inj₁ d0' | wm1' , inj₁ d0'₁ | [ eq1 ]' | [ eq2 ]' rewrite eq1 | eq2  with hcmw c0 wm1 | inspect (hcmw c0) wm1 | hcmw c0 wm1' | inspect (hcmw c0) wm1'
    claim | wm1 , inj₁ d0' | wm1' , inj₁ d0'₁ | [ eq1 ]' | [ eq2 ]' | (wm2 , c2) | [ Eq.refl ]' | (wm2' , c2') | [ Eq.refl ]' with hcxds-m-hdmw' d cds wm2 | inspect (hcxds-m-hdmw' d cds) wm2 | hcxds-m-hdmw' d cds wm2' | inspect (hcxds-m-hdmw' d cds) wm2'
    claim | wm1 , inj₁ d0' | wm1' , inj₁ d0'₁ | [ eq1 ]' | [ eq2 ]' | (wm2 , c2) | [ Eq.refl ]' | (wm2' , c2') | [ Eq.refl ]' | (wm3 , d3 , cds3 , c3) | [ Eq.refl ]' | (wm3' , d3' , cds3' , c3') | [ Eq.refl ]' rewrite eq1 | eq2 with h₂-wd-h (inj₂ tt) u₁ v px
    ... | (eqv1 , eq1a )  = claim5
      where
      claim5 =
        begin
        wm3 , d3 , (c2 , d0') ∷ cds3 , inj₂ tt ≡⟨ Eq.cong₂ (λ xx yy → wm3 , d3 , (c2 , d0') ∷ xx , yy) claim6a Eq.refl ⟩
        wm3 , d3 , (c2 , d0') ∷ cds3' , inj₂ tt ≈⟨ claim4 , Eq.cong₂ (\ xx yy -> xx , yy ∷ cds3' , inj₂ tt) claim5a (≡×≡⇒≡ (claim7a , c2a)) ⟩ 
        wm3' , d3' , (c2' , d0'₁) ∷ cds3' , inj₂ tt ∎

        where
        open SR mcdₛ

        c1 : wm1 ≈₀ wm1'
        c1 rewrite Eq.cong proj₁ (eq1) | Eq.cong proj₁ (eq2) = eqv1

        claim3 : wm2 ≈₀ wm2'
        claim3 = hcmw-cong c0 wm1 wm1' c1

        claim4 : wm3 ≈₀ wm3'
        claim4 = hcxds-m-hdmw'-cong d cds wm2 wm2' claim3

        claim5a : d3 ≡ d3'
        claim5a = hcxds-m-hdmw'-cong2 d cds wm2 wm2' claim3

        claim6a : cds3 ≡ cds3'
        claim6a = hcxds-m-hdmw'-cong3 d cds wm2 wm2' claim3

        claim7a : c2 ≡ c2'
        claim7a = hcmw-cong2 c0 wm1 wm1' c1


        cl2 : inj₁ d0' ≡ inj₁ d0'₁
        cl2 rewrite Eq.cong proj₂ (Eq.sym eq1) | Eq.cong proj₂ (eq2) = eq1a

        c2a : d0' ≡ d0'₁
        c2a = inj₁-injective cl2


    claim | wm1 , inj₂ y | wm1' , inj₂ y₁ | [ eq1 ]' | [ eq2 ]' rewrite eq1 | eq2  with hcmw c0 wm1 | inspect (hcmw c0) wm1 | hcmw c0 wm1' | inspect (hcmw c0) wm1'
    claim | wm1 , inj₂ y | wm1' , inj₂ y₁ | [ eq1 ]' | [ eq2 ]' | (wm2 , c2) | [ Eq.refl ]' | (wm2' , c2') | [ Eq.refl ]' with hcxds-m-hdmw' d cds wm2 | inspect (hcxds-m-hdmw' d cds) wm2 | hcxds-m-hdmw' d cds wm2' | inspect (hcxds-m-hdmw' d cds) wm2'
    claim | wm1 , inj₂ y | wm1' , inj₂ y₁ | [ eq1 ]' | [ eq2 ]' | (wm2 , c2) | [ Eq.refl ]' | (wm2' , c2') | [ Eq.refl ]' | (wm3 , d3 , cds3 , c3) | [ Eq.refl ]' | (wm3' , d3' , cds3' , c3') | [ Eq.refl ]' rewrite eq1 | eq2 with h₂-wd-h (inj₂ tt) u₁ v px
    ... | (eqv1 , eq1a )  = claim5
      where
      claim5 =
        begin
        wm3 , d3 , cds3 , inj₁ c2 ≡⟨ Eq.cong₂ (λ xx yy → wm3 , d3 , xx , yy) claim6a (Eq.cong inj₁ claim7a) ⟩
        wm3 , d3 , cds3' , inj₁ c2' ≈⟨ claim4 , Eq.cong (λ xx → xx , cds3' , inj₁ c2') claim5a  ⟩
        wm3' , d3' , cds3' , inj₁ c2' ∎

        where
        open SR mcdₛ

        c1 : wm1 ≈₀ wm1'
        c1 rewrite Eq.cong proj₁ (eq1) | Eq.cong proj₁ (eq2) = eqv1

        claim3 : wm2 ≈₀ wm2'
        claim3 = hcmw-cong c0 wm1 wm1' c1

        claim4 : wm3 ≈₀ wm3'
        claim4 = hcxds-m-hdmw'-cong d cds wm2 wm2' claim3

        claim5a : d3 ≡ d3'
        claim5a = hcxds-m-hdmw'-cong2 d cds wm2 wm2' claim3

        claim6a : cds3 ≡ cds3'
        claim6a = hcxds-m-hdmw'-cong3 d cds wm2 wm2' claim3

        claim7a : c2 ≡ c2'
        claim7a = hcmw-cong2 c0 wm1 wm1' c1

    claim2ok : ((hh **) cd u) ~ ((hh **) cd t)
    claim2ok = begin
      ((hh **) cd u) ≡⟨ lemma-hh=hcd-mb (d , cds , c) u₁ ⟩
      hcd-mb cd u₁ ≈⟨ claim ⟩
      hcd-mb cd v ≡⟨ Eq.sym (lemma-hh=hcd-mb (d , cds , c) v) ⟩
      ((hh **) cd t) ∎
      where
      open SR mcdₛ



  hhh-wd-ax cd@(d , cds , c) {u} {t} (mid (amal {m})) = claim
    where
    claim : (hh **) (d , cds , c) [ f₁ m ]ₗ ~ (hh **) (d , cds , c) [ f₂ m ]ᵣ
    claim = begin
      (hh **) (d , cds , c) [ f₁ m ]ₗ ≡⟨ lemma-hh=hcd-ma (d , cds , c) (f₁ m) ⟩
      hcd-ma (d , cds , c) (f₁ m) ≡⟨ lemma-hcd-ma=hcdm (d , cds , c) m ⟩
      hcdm (d , cds , c) m ≡⟨ Eq.sym (lemma-hcd-mb=hcdm (d , cds , c) m) ⟩
      hcd-mb (d , cds , c) (f₂ m) ≡⟨ Eq.sym (lemma-hh=hcd-mb (d , cds , c) (f₂ m)) ⟩
      (hh **) (d , cds , c) [ f₂ m ]ᵣ ∎
      where
      open SR mcdₛ

  h=⁻¹f-gen : ∀ (x : M) -> ([ x ]ʷ , I) ~ (hh **) I (f x)
  h=⁻¹f-gen x = symₛ (begin
    (hh **) I (f x) ≡⟨ lemma-hh=hcd-ma I (f₁ x) ⟩
    hcd-ma I (f₁ x) ≡⟨ lemma-hcd-ma=hcdm I x ⟩
    hcdm I x ≡⟨ Eq.refl ⟩
    ([ x ]ʷ , I) ∎)
    where open SR mcdₛ

  module myData3 = Data P₀ mypres CD I f hh [_]
  open myData3.Assumptions-And-Theorems h=⁻¹f-gen hhh-wd-ax f-wd-ax (trans left-unit left-unit) hh-hyp hiding ([_]ₓ) public
