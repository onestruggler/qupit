
import Relation.Binary.Reasoning.Setoid as SR

import Presentation.Groups.Cyclic as Cyclic
open import Presentation.Construct.Base
import Presentation.Construct.Properties.SugarProduct as SP
open import Data.Unit using (⊤ ; tt)
open import Data.Sum using (_⊎_ ; inj₁ ; inj₂ ; [_,_])
open import Relation.Binary.PropositionalEquality as Eq renaming ([_] to [_]') using ( _≡_ ; inspect)
open import Data.Nat using (ℕ ; suc ; zero)
open import Data.Product using (_,_ ; _×_ ; proj₁ ; proj₂ ; map ; ∃)
open import Data.Product.Relation.Binary.Pointwise.NonDependent as PW
open import Function using (_∘_)

open import Word.Base
import Presentation.Properties as PP
import Presentation.Base as PB

import Presentation.Construct.Properties.DirectProduct as DP
import Presentation.Construct.Properties.NDirectProduct as NDP
import Presentation.Reidemeister-Schreier as RS

open import Presentation.Groups.SnD

import Presentation.Groups.Sn as Sn

open import CliffordCCS.Index

-- ----------------------------------------------------------------------
-- * Generators and relations for U₈(ℤ[1/2, i])


module U33Di where


module TwoLevel-Simplified-Amal where

  module Simplified where
    -- The new set of generators.
    data Gen : Set where
      i₀-gen : Gen
      K₀₁-gen : Gen
      X₀₁-gen : Gen
      X₁₂-gen : Gen

    open import Data.Nat using (ℕ ; suc ; zero)

    gen : Gen -> Word Gen
    gen = [_]ʷ

    X₀₁ : Word Gen
    X₀₁ = gen X₀₁-gen

    X₁₂ : Word Gen
    X₁₂ = gen X₁₂-gen

    X₀₂ : Word Gen
    X₀₂ = X₁₂ • X₀₁ • X₁₂

    i₀ : Word Gen
    i₀ = gen i₀-gen
    
    i₁ : Word Gen
    i₁ = X₀₁ • i₀ • X₀₁
    
    i₂ : Word Gen
    i₂ = X₁₂ • i₁ • X₁₂

    K₀₁ : Word Gen
    K₀₁ = gen K₀₁-gen

    K₀₂ : Word Gen
    K₀₂ = X₁₂ • K₀₁ • X₁₂

    K₁₂ : Word Gen
    K₁₂ = X₀₁ • K₀₂ • X₀₁


    infix 4 _===_
    -- The new set of relations.
    data _===_ : WRel Gen where
    -- PD
      [S1] : i₀ ^ 4 === ε
      [S3a] : X₀₁ ^ 2 === ε
      [S3b] : X₁₂ ^ 2 === ε
      [S4a] : i₁ • i₀ === i₀ • i₁
      [S5a] : i₀ • X₁₂ === X₁₂ • i₀
      [S9a] : X₁₂ • X₀₁ • X₁₂ === X₀₁ • X₁₂ • X₀₁

    -- Ki, generators: K₀₁, i₀ , i₁, i₂
      [S10] : K₀₁ • i₁ ^ 2 === X₀₁ • K₀₁
      [S11] : i₁ • K₀₁ • i₁ • K₀₁ === K₀₁ • i₁ ^ 3
      [S12] : K₀₁ • i₀ • i₁ === i₀ • i₁ • K₀₁
      [S14] : K₀₁ ^ 2 • i₀ • i₁ === ε
      [S4b] : i₂ • K₀₁ === K₀₁ • i₂

    open PB _===_ hiding (_===_)
    open PP _===_

    open PB (Cyclic.pres 4 ⊕^ 3) renaming (_≈_ to _≈₀_ ; _===_ to _===₀_ ; Alphabet to M) using ()

    g : M -> Word Gen
    g (inj₁ tt) = i₀
    g (inj₂ (inj₁ tt)) = i₁
    g (inj₂ (inj₂ tt)) = i₂

    g-wd-ax : ∀ {w v} -> w ===₀ v -> (g *) w ≈ (g *) v
    g-wd-ax {w} {v} (left Cyclic.order) = trans (trans assoc assoc) (axiom [S1])
    g-wd-ax {w} {v} (right (left Cyclic.order)) = claim
      where
      claim : (i₁ ^' 4) ≈ ε
      claim = begin
        (i₁ ^' 4) ≈⟨ by-assoc Eq.refl ⟩
        X₀₁ • i₀ • (X₀₁ • X₀₁) • i₀ • (X₀₁ • X₀₁) • i₀ • (X₀₁ • X₀₁) • i₀ • X₀₁ ≈⟨ cong refl (cong refl (cong (axiom [S3a]) (cong refl (cong (axiom [S3a]) (cong refl (cong (axiom [S3a]) refl)))))) ⟩
        X₀₁ • i₀ • (ε) • i₀ • (ε) • i₀ • (ε) • i₀ • X₀₁ ≈⟨ by-assoc Eq.refl ⟩
        X₀₁ • (i₀ ^ 4) • X₀₁ ≈⟨ cong refl (cong (axiom [S1]) refl) ⟩
        X₀₁ • (ε) • X₀₁ ≈⟨ cong refl left-unit ⟩
        X₀₁ • X₀₁ ≈⟨ axiom [S3a] ⟩
        ε ∎
        where open SR word-setoid
    
    g-wd-ax {w} {v} (right (right Cyclic.order)) = claim
      where
      claim : (i₂ ^' 4) ≈ ε
      claim = begin
        (i₂ ^' 4) ≈⟨ by-assoc Eq.refl ⟩
        (X₁₂ • X₀₁ • i₀ • X₀₁) • (X₁₂ • X₁₂) • (X₀₁ • i₀ • X₀₁) • (X₁₂ • X₁₂) • (X₀₁ • i₀ • X₀₁) • (X₁₂ • X₁₂) • X₀₁ • i₀ • X₀₁ • X₁₂ ≈⟨ cong refl (cong (axiom [S3b]) (cong refl (cong (axiom [S3b]) (cong refl (cong (axiom [S3b]) refl))))) ⟩
        (X₁₂ • X₀₁ • i₀ • X₀₁) • ε • (X₀₁ • i₀ • X₀₁) • ε • (X₀₁ • i₀ • X₀₁) • ε • X₀₁ • i₀ • X₀₁ • X₁₂ ≈⟨ by-assoc Eq.refl ⟩
        X₁₂ • (i₁ ^' 4) • X₁₂ ≈⟨ cong refl (cong (g-wd-ax (right (left Cyclic.order))) refl) ⟩
        X₁₂ • ε • X₁₂ ≈⟨ by-assoc Eq.refl ⟩
        X₁₂ • X₁₂ ≈⟨ axiom [S3b] ⟩
        ε ∎
        where open SR word-setoid
    
    g-wd-ax {w} {v} (right (mid (comm tt tt))) = claim
      where
      claim : (i₁ • i₂) ≈ (i₂ • i₁)
      claim = begin
        (i₁ • i₂) ≈⟨ by-assoc Eq.refl ⟩
        X₀₁ • i₀ • (X₀₁ • X₁₂ • X₀₁) • i₀ • X₀₁ • X₁₂ ≈⟨ cong refl (cong refl (cong (sym (axiom [S9a])) refl)) ⟩
        X₀₁ • i₀ • (X₁₂ • X₀₁ • X₁₂) • i₀ • X₀₁ • X₁₂ ≈⟨ cong refl (by-assoc Eq.refl) ⟩
        X₀₁ • (i₀ • X₁₂) • X₀₁ • X₁₂ • i₀ • X₀₁ • X₁₂ ≈⟨ cong refl (cong (axiom [S5a]) refl) ⟩
        X₀₁ • (X₁₂ • i₀) • X₀₁ • X₁₂ • i₀ • X₀₁ • X₁₂ ≈⟨ by-assoc Eq.refl ⟩
        (X₀₁ • X₁₂ • i₀ • X₀₁) • (X₁₂ • i₀) • X₀₁ • X₁₂ ≈⟨ cong refl (sym (cong (axiom [S5a]) refl)) ⟩
        (X₀₁ • X₁₂ • i₀ • X₀₁) • (i₀ • X₁₂) • X₀₁ • X₁₂ ≈⟨ trans (sym left-unit) (cong (sym (axiom [S3b])) refl) ⟩
        (X₁₂ • X₁₂) • (X₀₁ • X₁₂ • i₀ • X₀₁) • (i₀ • X₁₂) • X₀₁ • X₁₂ ≈⟨ by-assoc Eq.refl ⟩
        X₁₂ • (X₁₂ • X₀₁ • X₁₂) • (i₀ • X₀₁) • (i₀ • X₁₂) • X₀₁ • X₁₂ ≈⟨ cong refl (cong (axiom [S9a]) refl) ⟩
        X₁₂ • (X₀₁ • X₁₂ • X₀₁) • (i₀ • X₀₁) • (i₀ • X₁₂) • X₀₁ • X₁₂ ≈⟨ by-assoc Eq.refl ⟩
        (X₁₂ • X₀₁ • X₁₂) • ((X₀₁ • i₀ • X₀₁) • i₀) • X₁₂ • X₀₁ • X₁₂ ≈⟨ cong refl (cong (axiom [S4a]) refl) ⟩
        (X₁₂ • X₀₁ • X₁₂) • (i₀ • (X₀₁ • i₀ • X₀₁)) • X₁₂ • X₀₁ • X₁₂ ≈⟨ by-assoc Eq.refl ⟩
        (X₁₂ • X₀₁) • (X₁₂ • i₀) • (X₀₁ • i₀ • X₀₁) • X₁₂ • X₀₁ • X₁₂ ≈⟨ cong refl (sym (cong (axiom [S5a]) refl)) ⟩
        (X₁₂ • X₀₁) • (i₀ • X₁₂) • (X₀₁ • i₀ • X₀₁) • X₁₂ • X₀₁ • X₁₂ ≈⟨ by-assoc Eq.refl ⟩
        (X₁₂ • X₀₁ • i₀ • X₁₂ • X₀₁ • i₀) • (X₀₁ • X₁₂ • X₀₁) • X₁₂ ≈⟨ cong refl (sym (cong (axiom [S9a]) refl)) ⟩
        (X₁₂ • X₀₁ • i₀ • X₁₂ • X₀₁ • i₀) • (X₁₂ • X₀₁ • X₁₂) • X₁₂ ≈⟨ by-assoc Eq.refl ⟩
        (X₁₂ • X₀₁ • i₀ • X₁₂ • X₀₁) • (i₀ • X₁₂) • X₀₁ • (X₁₂ • X₁₂) ≈⟨ cong refl (cong (axiom [S5a]) (cong refl (axiom [S3b]))) ⟩
        (X₁₂ • X₀₁ • i₀ • X₁₂ • X₀₁) • (X₁₂ • i₀) • X₀₁ • ε ≈⟨ by-assoc Eq.refl ⟩
        (X₁₂ • X₀₁ • i₀) • (X₁₂ • X₀₁ • X₁₂) • i₀ • X₀₁ ≈⟨ cong refl (cong (axiom [S9a]) refl) ⟩
        (X₁₂ • X₀₁ • i₀) • (X₀₁ • X₁₂ • X₀₁) • i₀ • X₀₁ ≈⟨ by-assoc Eq.refl ⟩
        X₁₂ • X₀₁ • i₀ • X₀₁ • X₁₂ • X₀₁ • i₀ • X₀₁ ≈⟨ by-assoc Eq.refl ⟩
        (i₂ • i₁) ∎
        where open SR word-setoid
    
    g-wd-ax {w} {v} (mid (comm tt (inj₁ tt))) = _≈_.sym (_≈_.axiom [S4a])
    g-wd-ax {w} {v} (mid (comm tt (inj₂ tt))) = claim
      where
      claim : (i₀ • i₂) ≈ (i₂ • i₀)
      claim = begin
        (i₀ • i₂) ≈⟨ by-assoc Eq.refl ⟩
        (i₀ • X₁₂) • X₀₁ • i₀ • X₀₁ • X₁₂ ≈⟨ cong (axiom [S5a]) refl ⟩
        (X₁₂ • i₀) • X₀₁ • i₀ • X₀₁ • X₁₂ ≈⟨ by-assoc Eq.refl ⟩
        X₁₂ • (i₀ • X₀₁ • i₀ • X₀₁) • X₁₂ ≈⟨ cong refl (cong (sym (axiom [S4a])) refl) ⟩
        X₁₂ • ((X₀₁ • i₀ • X₀₁) • i₀) • X₁₂ ≈⟨ by-assoc Eq.refl ⟩
        (X₁₂ • X₀₁ • i₀ • X₀₁) • i₀ • X₁₂ ≈⟨ cong refl (axiom [S5a]) ⟩
        (X₁₂ • X₀₁ • i₀ • X₀₁) • X₁₂ • i₀ ≈⟨ by-assoc Eq.refl ⟩
        (i₂ • i₀) ∎
        where open SR word-setoid
    
    by-sub-nf : ∀ {w v} -> w ≈₀ v -> (g *) w ≈ (g *) v
    by-sub-nf {w} {v} eq = RS.Star-Congruence.lemma-f*-cong _===₀_ _===_ g g-wd-ax eq

    sub-nfp : PP.NFProperty _===₀_
    sub-nfp = NDP.nfp (Cyclic.pres 4) 3 (Cyclic.nfp 4)

    open PP.NFProperty sub-nfp public

    i₀' : Word M
    i₀' = [ inj₁ tt ]ʷ

    i₁' : Word M
    i₁' = [ inj₂ (inj₁ tt) ]ʷ

    i₂' : Word M
    i₂' = [ inj₂ (inj₂ tt) ]ʷ


  module Ki where

    data Gen : Set where
      K₀₁-gen : Gen
      i₀-gen : Gen
      i₁-gen : Gen

    K₀₁ : Word Gen
    K₀₁ = [ K₀₁-gen ]ʷ

    i₀ : Word Gen
    i₀ = [ i₀-gen ]ʷ

    i₁ : Word Gen
    i₁ = [ i₁-gen ]ʷ

    X₀₁ : Word Gen
    X₀₁ = K₀₁ • i₁ • i₁ • K₀₁ • i₀ • i₁

    infix 4 _===_
    data _===_ : WRel Gen where
      [S2a] : i₀ ^ 4 === ε
      [S2b] : i₁ ^ 4 === ε
      [S4a] : i₁ • i₀ === i₀ • i₁
      [S10] : K₀₁ • i₀ • i₀ • K₀₁ • i₁ === i₀ • K₀₁ • i₀ • i₀ • K₀₁
      [S10b] : K₀₁ • i₀ • i₀ • K₀₁ • i₀ === i₁ • K₀₁ • i₀ • i₀ • K₀₁
      [S11] : i₁ • K₀₁ • i₁ • K₀₁ === K₀₁ • i₁ ^ 3
      [S12] : K₀₁ • i₀ • i₁ === i₀ • i₁ • K₀₁
      [S14] : K₀₁ ^ 2 • i₀ • i₁ === ε


    pres-D = C^n 2
    pres-D-nfp = NDP.nfp (Cyclic.pres 4) (2) (Cyclic.nfp 4)

    data C : Set where
      I : C
      K01 : C
      K01I0 : C
      K01III : C
      K01I0I0 : C
      KIIK : C
      
    X = Cyclic.X ⊎ Cyclic.X

    i₀' : Word X
    i₀' = [ inj₁ tt ]ʷ

    i₁' : Word X
    i₁' = [ inj₂ tt ]ʷ

    Y = Gen
    
    f : X -> Word Y
    f (inj₁ tt) = [ i₀-gen ]ʷ
    f (inj₂ tt) = [ i₁-gen ]ʷ 

    ract : C -> Gen -> Word X × C
    ract I i₀-gen = i₀' , I
    ract K01 i₀-gen = ε , K01I0
    ract K01I0 i₀-gen = ε , K01I0I0
    ract K01III i₀-gen = ε , K01
    ract K01I0I0 i₀-gen = ε , K01III
    ract KIIK i₀-gen = i₁' , KIIK
    ract I K₀₁-gen = ε , K01
    ract K01 K₀₁-gen = i₀' • i₀' • i₀' • i₁' • i₁' • i₁' , I
    ract K01I0 K₀₁-gen = i₀' • i₁' • i₁' , K01III
    ract K01III K₀₁-gen = i₀' • i₀' • i₁' , K01I0
    ract K01I0I0 K₀₁-gen = ε , KIIK
    ract KIIK K₀₁-gen = i₀' • i₀' • i₀' • i₁' • i₁' • i₁' , K01I0I0
    ract I i₁-gen = i₁' , I
    ract K01 i₁-gen = i₀' • i₁' , K01III
    ract K01I0 i₁-gen = i₀' • i₁' , K01
    ract K01III i₁-gen = i₀' • i₁' , K01I0I0
    ract K01I0I0 i₁-gen = i₀' • i₁' , K01I0
    ract KIIK i₁-gen = i₀' , KIIK

    h = ract

    [_] : C -> Word Y
    [ I ] = ε
    [ K01 ] = K₀₁
    [ K01I0 ] = K₀₁ • i₀
    [ K01III ] = K₀₁ • i₀ • i₀ • i₀
    [ K01I0I0 ] = K₀₁ • i₀ • i₀
    [ KIIK ] = K₀₁ • i₀ • i₀ • K₀₁

    import Presentation.CosetNF as CNF
    pres-KD = (_===_)
    
    module DD = CNF.Data pres-D pres-KD C I f ract [_]
    open DD using (_~_)
    open PP.NFProperty (pres-D-nfp) renaming (by-equal-nf to bef) using ()
    open PB pres-KD renaming (_===_ to _===₂_ ; _≈_ to _≈₂_ ; refl' to refl'₂) using ()
    open PB pres-D renaming (_===_ to _===₁_ ; _≈_ to _≈₁_) using ()
    open PP pres-KD renaming (word-setoid to ws₂ ; by-assoc to by-assoc₂) using ()
    open PP pres-D renaming (word-setoid to ws₁) using ()
    open PB

    h=⁻¹f-gen : ∀ (x : X) -> ([ x ]ʷ , I) ~ ((h **) I (f x))
    h=⁻¹f-gen (inj₁ x) = bef Eq.refl , Eq.refl
    h=⁻¹f-gen (inj₂ y) = bef Eq.refl , Eq.refl

    h-wd-ax : ∀ (c : C){u t : Word Y} -> u ===₂ t -> ((h **) c u) ~ ((h **) c t)
    h-wd-ax I {.(i₀ ^ 4)} {.ε} [S2a] = bef Eq.refl , Eq.refl
    h-wd-ax I {.(i₁ ^ 4)} {.ε} [S2b] = bef Eq.refl , Eq.refl
    h-wd-ax I {.(i₁ • i₀)} {.(i₀ • i₁)} [S4a] = bef Eq.refl , Eq.refl
    h-wd-ax I {.(i₁ • K₀₁ • i₁ • K₀₁)} {.(K₀₁ • i₁ ^ 3)} [S11] = bef Eq.refl , Eq.refl
    h-wd-ax I {.(K₀₁ • i₀ • i₁)} {.(i₀ • i₁ • K₀₁)} [S12] = bef Eq.refl , Eq.refl
    h-wd-ax I {.(K₀₁ ^ 2 • i₀ • i₁)} {.ε} [S14] = bef Eq.refl , Eq.refl
    h-wd-ax K01 {.(i₀ ^ 4)} {.ε} [S2a] = bef Eq.refl , Eq.refl
    h-wd-ax K01 {.(i₁ ^ 4)} {.ε} [S2b] = bef Eq.refl , Eq.refl
    h-wd-ax K01 {.(i₁ • i₀)} {.(i₀ • i₁)} [S4a] = bef Eq.refl , Eq.refl
    h-wd-ax K01 {.(i₁ • K₀₁ • i₁ • K₀₁)} {.(K₀₁ • i₁ ^ 3)} [S11] = bef Eq.refl , Eq.refl
    h-wd-ax K01 {.(K₀₁ • i₀ • i₁)} {.(i₀ • i₁ • K₀₁)} [S12] = bef Eq.refl , Eq.refl
    h-wd-ax K01 {.(K₀₁ ^ 2 • i₀ • i₁)} {.ε} [S14] = bef Eq.refl , Eq.refl
    h-wd-ax K01I0 {.(i₀ ^ 4)} {.ε} [S2a] = bef Eq.refl , Eq.refl
    h-wd-ax K01I0 {.(i₁ ^ 4)} {.ε} [S2b] = bef Eq.refl , Eq.refl
    h-wd-ax K01I0 {.(i₁ • i₀)} {.(i₀ • i₁)} [S4a] = bef Eq.refl , Eq.refl
    h-wd-ax K01I0 {.(i₁ • K₀₁ • i₁ • K₀₁)} {.(K₀₁ • i₁ ^ 3)} [S11] = bef Eq.refl , Eq.refl
    h-wd-ax K01I0 {.(K₀₁ • i₀ • i₁)} {.(i₀ • i₁ • K₀₁)} [S12] = bef Eq.refl , Eq.refl
    h-wd-ax K01I0 {.(K₀₁ ^ 2 • i₀ • i₁)} {.ε} [S14] = bef Eq.refl , Eq.refl
    h-wd-ax K01III {.(i₀ ^ 4)} {.ε} [S2a] = bef Eq.refl , Eq.refl
    h-wd-ax K01III {.(i₁ ^ 4)} {.ε} [S2b] = bef Eq.refl , Eq.refl
    h-wd-ax K01III {.(i₁ • i₀)} {.(i₀ • i₁)} [S4a] = bef Eq.refl , Eq.refl
    h-wd-ax K01III {.(i₁ • K₀₁ • i₁ • K₀₁)} {.(K₀₁ • i₁ ^ 3)} [S11] = bef Eq.refl , Eq.refl
    h-wd-ax K01III {.(K₀₁ • i₀ • i₁)} {.(i₀ • i₁ • K₀₁)} [S12] = bef Eq.refl , Eq.refl
    h-wd-ax K01III {.(K₀₁ ^ 2 • i₀ • i₁)} {.ε} [S14] = bef Eq.refl , Eq.refl
    h-wd-ax K01I0I0 {.(i₀ ^ 4)} {.ε} [S2a] = bef Eq.refl , Eq.refl
    h-wd-ax K01I0I0 {.(i₁ ^ 4)} {.ε} [S2b] = bef Eq.refl , Eq.refl
    h-wd-ax K01I0I0 {.(i₁ • i₀)} {.(i₀ • i₁)} [S4a] = bef Eq.refl , Eq.refl
    h-wd-ax K01I0I0 {.(i₁ • K₀₁ • i₁ • K₀₁)} {.(K₀₁ • i₁ ^ 3)} [S11] = bef Eq.refl , Eq.refl
    h-wd-ax K01I0I0 {.(K₀₁ • i₀ • i₁)} {.(i₀ • i₁ • K₀₁)} [S12] = bef Eq.refl , Eq.refl
    h-wd-ax K01I0I0 {.(K₀₁ ^ 2 • i₀ • i₁)} {.ε} [S14] = bef Eq.refl , Eq.refl
    h-wd-ax KIIK {.(i₀ ^ 4)} {.ε} [S2a] = bef Eq.refl , Eq.refl
    h-wd-ax KIIK {.(i₁ ^ 4)} {.ε} [S2b] = bef Eq.refl , Eq.refl
    h-wd-ax KIIK {.(i₁ • i₀)} {.(i₀ • i₁)} [S4a] = bef Eq.refl , Eq.refl
    h-wd-ax KIIK {.(i₁ • K₀₁ • i₁ • K₀₁)} {.(K₀₁ • i₁ ^ 3)} [S11] = bef Eq.refl , Eq.refl
    h-wd-ax KIIK {.(K₀₁ • i₀ • i₁)} {.(i₀ • i₁ • K₀₁)} [S12] = bef Eq.refl , Eq.refl
    h-wd-ax KIIK {.(K₀₁ ^ 2 • i₀ • i₁)} {.ε} [S14] = bef Eq.refl , Eq.refl
    h-wd-ax I [S10b] = bef Eq.refl , Eq.refl
    h-wd-ax K01 [S10b] = bef Eq.refl , Eq.refl
    h-wd-ax K01I0 [S10b] = bef Eq.refl , Eq.refl
    h-wd-ax K01III [S10b] = bef Eq.refl , Eq.refl
    h-wd-ax K01I0I0 [S10b] = bef Eq.refl , Eq.refl
    h-wd-ax KIIK [S10b] = bef Eq.refl , Eq.refl
    h-wd-ax I [S10] = bef Eq.refl , Eq.refl
    h-wd-ax K01 [S10] = bef Eq.refl , Eq.refl
    h-wd-ax K01I0 [S10] = bef Eq.refl , Eq.refl
    h-wd-ax K01III [S10] = bef Eq.refl , Eq.refl
    h-wd-ax K01I0I0 [S10] = bef Eq.refl , Eq.refl
    h-wd-ax KIIK [S10] = bef Eq.refl , Eq.refl
  
    f-wd-ax : ∀ {w v} -> w ===₁ v -> (f *) w ≈₂ (f *) v
    f-wd-ax {.([ Cyclic.T ^' 4 ]ₗ)} {.([ ε ]ₗ)} (left Cyclic.order) = begin
      i₀ ^' 4 ≈⟨ by-assoc₂ Eq.refl ⟩
      i₀ ^ 4 ≈⟨ _≈₂_.axiom [S2a] ⟩
      ε ∎
      where
      open SR ws₂
    f-wd-ax {.([ Cyclic.T ^' 4 ]ᵣ)} {.([ ε ]ᵣ)} (right Cyclic.order) = begin
      i₁ ^' 4 ≈⟨ by-assoc₂ Eq.refl ⟩
      i₁ ^ 4 ≈⟨ _≈₂_.axiom [S2b] ⟩
      ε ∎
      where
      open SR ws₂
    f-wd-ax {.([ [ tt ]ʷ ]ₗ • [ [ tt ]ʷ ]ᵣ)} {.([ [ tt ]ʷ ]ᵣ • [ [ tt ]ʷ ]ₗ)} (mid (comm tt tt)) = begin
      i₀ • i₁ ≈⟨ sym (axiom [S4a]) ⟩
      i₁ • i₀ ∎
      where
      open SR ws₂

    open SR ws₂

    by-sub-nf : ∀ {w v} -> w ≈₁ v -> (f *) w ≈₂ (f *) v
    by-sub-nf {w} {v} eq = RS.Star-Congruence.lemma-f*-cong _===₁_ _===₂_ f f-wd-ax eq 


    lemma-K01^2 : K₀₁ ^ 2 ≈₂ i₀ ^ 3 • i₁ ^ 3
    lemma-K01^2 = begin
      K₀₁ • [ K₀₁-gen ]ʷ ≈⟨ by-assoc₂ Eq.refl ⟩
      (K₀₁ • [ K₀₁-gen ]ʷ) • ε • ε ≈⟨ cong refl (cong (sym (axiom [S2a])) (sym (axiom [S2b]))) ⟩
      (K₀₁ • [ K₀₁-gen ]ʷ) • i₀ ^ 4 • i₁ ^ 4 ≈⟨ cong refl (by-sub-nf {i₀' ^ 4 • i₁' ^ 4} {i₀' • i₁' • i₀' ^ 3 • i₁' ^ 3} (bef Eq.refl)) ⟩
      (K₀₁ • [ K₀₁-gen ]ʷ) • i₀ • i₁ • i₀ ^ 3 • i₁ ^ 3 ≈⟨ by-assoc₂ Eq.refl ⟩
      (K₀₁ ^ 2 • i₀ • i₁) • i₀ ^ 3 • i₁ ^ 3 ≈⟨ cong (axiom [S14]) refl ⟩
      ε • i₀ ^ 3 • i₁ ^ 3 ≈⟨ by-assoc₂ Eq.refl ⟩
      i₀ ^ 3 • i₁ ^ 3 ∎

    lemma-KI : (k : ℕ) -> K₀₁ • (i₀ • i₁) ^ k ≈₂ (i₀ • i₁) ^ k • K₀₁
    lemma-KI zero = trans (right-unit) (sym left-unit)
    lemma-KI (suc zero) = trans (axiom [S12]) (sym assoc)
    lemma-KI (suc (suc k)) = begin
      K₀₁ • (i₀ • i₁) • (i₀ • i₁) ^ suc k ≈⟨ by-assoc₂ Eq.refl ⟩
      (K₀₁ • i₀ • i₁) • (i₀ • i₁) ^ suc k ≈⟨ cong (axiom [S12]) refl ⟩
      (i₀ • i₁ • K₀₁) • (i₀ • i₁) ^ suc k ≈⟨ by-assoc₂ Eq.refl ⟩
      (i₀ • i₁) • K₀₁ • (i₀ • i₁) ^ suc k ≈⟨ cong refl (lemma-KI (suc k)) ⟩
      (i₀ • i₁) • (i₀ • i₁) ^ suc k • K₀₁ ≈⟨ by-assoc₂ Eq.refl ⟩
      ((i₀ • i₁) • (i₀ • i₁) ^ suc k) • K₀₁ ∎

    lemma-KiiiK : K₀₁ • i₁ ^ 3 • K₀₁ • i₀ • i₁ ≈₂ i₁ • K₀₁ • i₁
    lemma-KiiiK = begin
      K₀₁ • i₁ ^ 3 • K₀₁ • i₀ • i₁ ≈⟨ by-assoc₂ Eq.refl ⟩
      (K₀₁ • i₁ ^ 3) • K₀₁ • i₀ • i₁ ≈⟨ cong (sym (axiom [S11])) refl ⟩
      (i₁ • K₀₁ • i₁ • K₀₁) • K₀₁ • i₀ • i₁ ≈⟨ by-assoc₂ Eq.refl ⟩
      (i₁ • K₀₁ • i₁) • K₀₁ ^ 2 • i₀ • i₁ ≈⟨ trans (cong refl (axiom [S14])) right-unit ⟩
      i₁ • K₀₁ • i₁ ∎


    lemma-KI0K : K₀₁ • i₀ • K₀₁ ≈₂ i₁ • K₀₁ • i₁
    lemma-KI0K = begin
      K₀₁ • i₀ • K₀₁ ≈⟨ cong refl (cong (by-sub-nf {i₀'} {i₁' ^ 3 • i₀' • i₁'} (bef Eq.refl)) refl ) ⟩
      K₀₁ • (i₁ ^ 3 • i₀ • i₁) • K₀₁ ≈⟨ by-assoc₂ Eq.refl ⟩
      K₀₁ • i₁ ^ 3 • i₀ • i₁ • K₀₁ ≈⟨ cong refl (cong refl (sym (axiom [S12]))) ⟩
      K₀₁ • i₁ ^ 3 • K₀₁ • i₀ • i₁ ≈⟨ lemma-KiiiK ⟩
      i₁ • K₀₁ • i₁ ∎

    lemma-XI1 : K₀₁ • i₀ • i₀ • K₀₁ • i₁ ≈₂ i₀ • K₀₁ • i₀ • i₀ • K₀₁
    lemma-XI1 = begin
      K₀₁ • i₀ • i₀ • K₀₁ • i₁ ≈⟨ axiom [S10] ⟩
      i₀ • K₀₁ • i₀ • i₀ • K₀₁ ∎

    lemma-XI0 : K₀₁ • i₀ • i₀ • K₀₁ • i₀ ≈₂ i₁ • K₀₁ • i₀ • i₀ • K₀₁
    lemma-XI0 = begin
      K₀₁ • i₀ • i₀ • K₀₁ • i₀ ≈⟨ axiom [S10b] ⟩
      i₁ • K₀₁ • i₀ • i₀ • K₀₁ ∎

    h=ract :  ∀ c b -> let (b' , c') = h c b in let [_]ₓ = f * in
      [ c ] • [ b ]ʷ ≈₂ [ b' ]ₓ • [ c' ]
    h=ract I K₀₁-gen = by-assoc₂ Eq.refl
    h=ract I i₀-gen = by-assoc₂ Eq.refl
    h=ract I i₁-gen = by-assoc₂ Eq.refl
    h=ract K01 K₀₁-gen = trans lemma-K01^2 (by-assoc₂ Eq.refl)
    h=ract K01 i₀-gen = by-assoc₂ Eq.refl
    h=ract K01 i₁-gen = begin
      K₀₁ • [ i₁-gen ]ʷ ≈⟨ cong refl (by-sub-nf {i₁'} {i₀' • i₁' • i₀' • i₀' • i₀'} (bef Eq.refl)) ⟩
      K₀₁ • i₀ • i₁ • i₀ • i₀ • i₀ ≈⟨ by-assoc₂ Eq.refl ⟩
      (K₀₁ • i₀ • i₁) • i₀ • i₀ • i₀ ≈⟨ cong (axiom [S12]) refl ⟩
      (i₀ • i₁ • K₀₁) • i₀ • i₀ • i₀ ≈⟨ by-assoc₂ Eq.refl ⟩
      (i₀ • i₁) • K₀₁ • i₀ • i₀ • i₀ ∎
    h=ract K01I0 K₀₁-gen = begin
      (K₀₁ • i₀) • [ K₀₁-gen ]ʷ ≈⟨ by-assoc₂ Eq.refl ⟩
      K₀₁ • i₀ • [ K₀₁-gen ]ʷ ≈⟨ lemma-KI0K ⟩
      i₁ • K₀₁ • i₁ ≈⟨ by-assoc₂ Eq.refl ⟩
      (i₁ • K₀₁) • i₁ ≈⟨ cong refl (by-sub-nf {i₁'} {i₀' • i₁' • i₀' ^ 3} (bef Eq.refl)) ⟩
      (i₁ • K₀₁) • i₀ • i₁ • i₀ ^ 3 ≈⟨ by-assoc₂ Eq.refl ⟩
      i₁ • (K₀₁ • i₀ • i₁) • i₀ • i₀ • i₀ ≈⟨ cong refl (cong (axiom [S12]) refl) ⟩
      i₁ • (i₀ • i₁ • K₀₁) • i₀ • i₀ • i₀ ≈⟨ by-assoc₂ Eq.refl ⟩
      (i₁ • i₀) • i₁ • K₀₁ • i₀ • i₀ • i₀ ≈⟨ cong (axiom [S4a]) refl ⟩
      (i₀ • i₁) • i₁ • K₀₁ • i₀ • i₀ • i₀ ≈⟨ by-assoc₂ Eq.refl ⟩
      (i₀ • i₁ • i₁) • K₀₁ • i₀ • i₀ • i₀ ∎
    h=ract K01I0 i₀-gen = by-assoc₂ Eq.refl
    h=ract K01I0 i₁-gen = begin
      (K₀₁ • i₀) • [ i₁-gen ]ʷ ≈⟨ assoc ⟩
      K₀₁ • i₀ • [ i₁-gen ]ʷ ≈⟨ axiom [S12] ⟩
      i₀ • [ i₁-gen ]ʷ • K₀₁ ≈⟨ sym assoc ⟩
      (i₀ • i₁) • K₀₁ ∎
    h=ract K01III K₀₁-gen = begin
      (K₀₁ • i₀ • i₀ • i₀) • [ K₀₁-gen ]ʷ ≈⟨ by-assoc₂ Eq.refl ⟩
      (K₀₁ • i₀ • i₀) • i₀ • K₀₁ ≈⟨ cong refl (trans (sym left-unit) (cong (sym (axiom [S14])) refl)) ⟩
      (K₀₁ • i₀ • i₀) • (K₀₁ ^ 2 • i₀ • i₁) • i₀ • K₀₁ ≈⟨ by-assoc₂ Eq.refl ⟩
      (K₀₁ • i₀ • i₀ • K₀₁ • K₀₁ • i₀) • (i₁ • i₀) • K₀₁ ≈⟨ cong refl (cong (axiom [S4a]) refl) ⟩
      (K₀₁ • i₀ • i₀ • K₀₁ • K₀₁ • i₀) • (i₀ • i₁) • K₀₁ ≈⟨ cong refl assoc  ⟩
      (K₀₁ • i₀ • i₀ • K₀₁ • K₀₁ • i₀) • i₀ • i₁ • K₀₁ ≈⟨ cong refl (sym (axiom [S12])) ⟩
      (K₀₁ • i₀ • i₀ • K₀₁ • K₀₁ • i₀) • K₀₁ • i₀ • i₁ ≈⟨ by-assoc₂ Eq.refl ⟩
      (K₀₁ • i₀ • i₀ • K₀₁) • (K₀₁ • i₀ • K₀₁) • i₀ • i₁ ≈⟨ cong refl (cong lemma-KI0K refl) ⟩
      (K₀₁ • i₀ • i₀ • K₀₁) • (i₁ • K₀₁ • i₁) • i₀ • i₁ ≈⟨ by-assoc₂ Eq.refl ⟩
      (K₀₁ • i₀ • i₀ • K₀₁ • i₁) • (K₀₁ • i₁) • i₀ • i₁ ≈⟨ cong lemma-XI1 refl ⟩
      (i₀ • K₀₁ • i₀ • i₀ • K₀₁) • (K₀₁ • i₁) • i₀ • i₁ ≈⟨ by-assoc₂ Eq.refl ⟩
      (i₀ • K₀₁ • i₀ • i₀) • (K₀₁ • K₀₁) • i₁ • i₀ • i₁ ≈⟨ cong refl (cong lemma-K01^2 refl) ⟩
      (i₀ • K₀₁ • i₀ • i₀) • (i₀ ^ 3 • i₁ ^ 3) • i₁ • i₀ • i₁ ≈⟨ by-assoc₂ Eq.refl ⟩
      (i₀ • K₀₁) • i₀ • i₀ • (i₀ ^ 3 • i₁ ^ 3) • i₁ • i₀ • i₁ ≈⟨ cong refl (by-sub-nf {i₀' • i₀' • (i₀' ^ 3 • i₁' ^ 3) • i₁' • i₀' • i₁'} {i₀' • i₁' • i₀'} (bef Eq.refl))  ⟩
      (i₀ • K₀₁) • i₀ • i₁ • i₀ ≈⟨ by-assoc₂ Eq.refl ⟩
      i₀ • (K₀₁ • i₀ • i₁) • i₀ ≈⟨ cong refl (cong (axiom [S12]) refl) ⟩
      i₀ • (i₀ • i₁ • K₀₁) • i₀ ≈⟨ by-assoc₂ Eq.refl ⟩
      (i₀ • i₀ • i₁) • K₀₁ • i₀ ∎
    h=ract K01III i₀-gen = begin
      (K₀₁ • i₀ • i₀ • i₀) • [ i₀-gen ]ʷ ≈⟨ by-assoc₂ Eq.refl ⟩
      K₀₁ • i₀ • i₀ • i₀ • [ i₀-gen ]ʷ ≈⟨ trans (cong refl (axiom [S2a])) (trans right-unit (sym left-unit)) ⟩
      (ε) • K₀₁ ∎
    h=ract K01III i₁-gen = begin
      (K₀₁ • i₀ • i₀ • i₀) • [ i₁-gen ]ʷ ≈⟨ by-assoc₂ Eq.refl ⟩
      K₀₁ • i₀ • i₀ • i₀ • i₁ ≈⟨ cong refl (by-sub-nf {i₀' • i₀' • i₀' • i₁'} {i₀' • i₁' • i₀' ^ 2} (bef Eq.refl)) ⟩
      K₀₁ • i₀ • i₁ • i₀ ^ 2 ≈⟨ by-assoc₂ Eq.refl ⟩
      (K₀₁ • i₀ • i₁) • i₀ ^ 2 ≈⟨ cong (axiom [S12]) refl ⟩
      (i₀ • i₁ • K₀₁) • i₀ ^ 2 ≈⟨ by-assoc₂ Eq.refl ⟩
      (i₀ • i₁) • K₀₁ • i₀ • i₀ ∎
    h=ract K01I0I0 K₀₁-gen = by-assoc₂ Eq.refl
    h=ract K01I0I0 i₀-gen = by-assoc₂ Eq.refl
    h=ract K01I0I0 i₁-gen = begin
      (K₀₁ • i₀ • i₀) • [ i₁-gen ]ʷ ≈⟨ by-assoc₂ Eq.refl ⟩
      K₀₁ • i₀ • i₀ • i₁ ≈⟨ cong refl (by-sub-nf {i₀' • i₀' • i₁'} {i₀' • i₁' • i₀'} (bef Eq.refl)) ⟩
      K₀₁ • i₀ • i₁ • i₀ ≈⟨ by-assoc₂ Eq.refl ⟩
      (K₀₁ • i₀ • i₁) • i₀ ≈⟨ cong (axiom [S12]) refl ⟩
      (i₀ • i₁ • K₀₁) • i₀ ≈⟨ by-assoc₂ Eq.refl ⟩
      (i₀ • i₁) • K₀₁ • i₀ ∎
    h=ract KIIK K₀₁-gen = begin
      (K₀₁ • i₀ • i₀ • K₀₁) • [ K₀₁-gen ]ʷ ≈⟨ by-assoc₂ Eq.refl ⟩
      (K₀₁ • i₀ • i₀) • K₀₁ ^ 2 ≈⟨ cong refl lemma-K01^2 ⟩
      (K₀₁ • i₀ • i₀) • i₀ ^ 3 • i₁ ^ 3 ≈⟨ by-assoc₂ Eq.refl ⟩
      K₀₁ • i₀ • i₀ • i₀ ^ 3 • i₁ ^ 3 ≈⟨ cong refl (by-sub-nf {i₀' • i₀' • i₀' ^ 3 • i₁' ^ 3} {(i₀' • i₁') ^ 3 • i₀' ^ 2} (bef Eq.refl)) ⟩
      K₀₁ • (i₀ • i₁) ^ 3 • i₀ ^ 2 ≈⟨ by-assoc₂ Eq.refl ⟩
      (K₀₁ • (i₀ • i₁) ^ 3) • i₀ ^ 2 ≈⟨ cong (lemma-KI 3) refl ⟩
      ((i₀ • i₁) ^ 3 • K₀₁) • i₀ ^ 2 ≈⟨ by-assoc₂ Eq.refl ⟩
      (i₀ • i₁) ^ 3 • K₀₁ • i₀ ^ 2 ≈⟨ cong (by-sub-nf {(i₀' • i₁') ^ 3} {i₀' ^ 3 • i₁' ^ 3} (bef Eq.refl)) refl ⟩
      (i₀ ^ 3 • i₁ ^ 3) • K₀₁ • i₀ ^ 2 ≈⟨ by-assoc₂ Eq.refl ⟩
      (i₀ • i₀ • i₀ • i₁ • i₁ • i₁) • K₀₁ • i₀ • i₀ ∎
    h=ract KIIK i₀-gen = begin
      (K₀₁ • i₀ • i₀ • K₀₁) • [ i₀-gen ]ʷ ≈⟨ by-assoc₂ Eq.refl ⟩
      K₀₁ • i₀ • i₀ • K₀₁ • [ i₀-gen ]ʷ ≈⟨ lemma-XI0 ⟩
      i₁ • K₀₁ • i₀ • i₀ • K₀₁ ∎
    h=ract KIIK i₁-gen = begin
      (K₀₁ • i₀ • i₀ • K₀₁) • [ i₁-gen ]ʷ ≈⟨ by-assoc₂ Eq.refl ⟩
      K₀₁ • i₀ • i₀ • K₀₁ • [ i₁-gen ]ʷ ≈⟨ lemma-XI1 ⟩
      i₀ • K₀₁ • i₀ • i₀ • K₀₁ ∎


    module AAT = DD.Assumptions-And-Theorems h=⁻¹f-gen h-wd-ax f-wd-ax (refl'₂ Eq.refl) h=ract

    -- pres-KD works on indices ₀ and ₁, the next component is i₂.
    pres-KI = pres-KD ⊕ (Cyclic.pres 4)
    pres-KI-nfp : PP.NFProperty pres-KI
    pres-KI-nfp = DP.NFP.nfp pres-KD (Cyclic.pres 4) (AAT.nfp pres-D-nfp) (Cyclic.nfp 4)

    open PB pres-KI renaming (Alphabet to B ; _===_ to _===₂_ ; _≈_ to _≈₃_) using ()
    open PB (Cyclic.pres 2) renaming (Alphabet to S ; _===_ to _===₀_) using ()
    open PP.NFProperty pres-KI-nfp renaming (by-equal-nf to bef') using ()

    fs : ⊤ -> Word B
    fs tt = [ X₀₁ ]ₗ

    pres' = (Cyclic.pres 2 ⸲ pres-KI ⸲ Γₛ fs)

    fs-wd-ax : {w v : Word Cyclic.X} → w ===₀ v → (fs *) w ≈₃ (fs *) v
    fs-wd-ax {.(Cyclic.T ^' 2)} {.ε} Cyclic.order = bef' Eq.refl
    
    nfp-a : PP.NFProperty pres'
    nfp-a = SP.nfp (Cyclic.pres 2) pres-KI fs fs-wd-ax pres-KI-nfp

    -- finally, we got all generators: K₀₁, i₀ -- i₂, and X₀₁.
    open PB pres' renaming (Alphabet to FGen) using () public
    fK₀₁ : Word FGen
    fK₀₁ = [ [ [ K₀₁-gen ]ʷ ]ₗ ]ᵣ

    fi₀ : Word FGen
    fi₀ = [ [ [ i₀-gen ]ʷ ]ₗ ]ᵣ

    fi₁ : Word FGen
    fi₁ = [ [ [ i₀-gen ]ʷ ]ₗ ]ᵣ
    
    fi₂ : Word FGen
    fi₂ = [ [ [ tt ]ʷ ]ᵣ ]ᵣ

    fX₀₁ : Word FGen
    fX₀₁ = [ [ tt ]ʷ ]ₗ

  module PD where
    pres = pres-SnD 2
    pres-nfp = nfp 2
    
    open PB pres renaming (Alphabet to Gen) public
    
    X₀₁ : Word Gen
    X₀₁ = [ [ Sn.swap ]ʷ ]ᵣ

    X₁₂ : Word Gen
    X₁₂ = [ [ Sn.swap Sn.ₛ ]ʷ ]ᵣ
    
    i₀ : Word Gen
    i₀ = [ [ [ tt ]ʷ ]ₗ ]ₗ
    
  open import Presentation.Construct.Properties.Amalgamation

  module M where
    pres-M = pres-SnD 1 ⊕ Cyclic.pres 4
    pres-M-nfp = DP.NFP.nfp (pres-SnD 1) (Cyclic.pres 4) (nfp 1) (Cyclic.nfp 4)
    
  module Amal where
    open PB M.pres-M renaming (_≈_ to _≈₀_ ; _===_ to _===₀_ ; Alphabet to M) using ()
    open PB PD.pres renaming (_≈_ to _≈₁_ ; _===_ to _===₁_ ; Alphabet to A) using ()
    open PB Ki.pres' renaming (_≈_ to _≈₂_ ; _===_ to _===₂_ ; Alphabet to B) using ()


    module CA1 where
      data C : Set where
        X12 : C
        X12X01 : C

      i₀ : Word ((⊤ ⊎ ⊤ ⊎ ⊤) ⊎ Sn.X 2)
      i₀ = [ inj₁ (inj₁ tt) ]ʷ

      i₁ : Word ((⊤ ⊎ ⊤ ⊎ ⊤) ⊎ Sn.X 2)
      i₁ = [ inj₁ (inj₂ (inj₁ tt)) ]ʷ

      i₂ : Word ((⊤ ⊎ ⊤ ⊎ ⊤) ⊎ Sn.X 2)
      i₂ = [ inj₁ (inj₂ (inj₂ tt)) ]ʷ

      swap₀₁ : Word ((⊤ ⊎ ⊤ ⊎ ⊤) ⊎ Sn.X 2)
      swap₀₁ = [ inj₂ Sn.swap ]ʷ

      X₀₁ = swap₀₁

      X₁₂ : Word ((⊤ ⊎ ⊤ ⊎ ⊤) ⊎ Sn.X 2)
      X₁₂ = [ inj₂ (Sn.swap Sn.ₛ) ]ʷ


      i₀' : Word (((⊤ ⊎ ⊤) ⊎ Sn.X 1) ⊎ ⊤)
      i₀' = [ inj₁ (inj₁ (inj₁ tt)) ]ʷ
      i₁' : Word (((⊤ ⊎ ⊤) ⊎ Sn.X 1) ⊎ ⊤)
      i₁' = [ inj₁ (inj₁ (inj₂ tt)) ]ʷ
      i₂' : Word (((⊤ ⊎ ⊤) ⊎ Sn.X 1) ⊎ ⊤)
      i₂' = [ inj₂ tt ]ʷ

      X₀₁' : Word (((⊤ ⊎ ⊤) ⊎ Sn.X 1) ⊎ ⊤)
      X₀₁' = [ inj₁ (inj₂ Sn.swap) ]ʷ

      f : ((⊤ ⊎ ⊤) ⊎ Sn.X 1) ⊎ ⊤ → Word ((⊤ ⊎ ⊤ ⊎ ⊤) ⊎ Sn.X 2)
      f (inj₁ (inj₁ (inj₁ tt))) = i₀
      f (inj₁ (inj₁ (inj₂ tt))) = i₁
      f (inj₁ (inj₂ Sn.swap)) = swap₀₁
      f (inj₂ tt) = i₂

      ract : C ⊎ ⊤ → (⊤ ⊎ ⊤ ⊎ ⊤) ⊎ Sn.X 2 → Word (((⊤ ⊎ ⊤) ⊎ Sn.X 1) ⊎ ⊤) × (C ⊎ ⊤)
      ract (inj₁ X12) (inj₁ (inj₁ tt)) = i₀' , (inj₁ X12)
      ract (inj₁ X12X01) (inj₁ (inj₁ tt)) = i₂' , (inj₁ X12X01)
      ract (inj₁ X12) (inj₁ (inj₂ (inj₁ tt))) = i₂' , (inj₁ X12)
      ract (inj₁ X12X01) (inj₁ (inj₂ (inj₁ tt))) = i₀' , (inj₁ X12X01)
      ract (inj₁ X12) (inj₁ (inj₂ (inj₂ tt))) = i₁' , (inj₁ X12)
      ract (inj₁ X12X01) (inj₁ (inj₂ (inj₂ tt))) = i₁' , (inj₁ X12X01)
      ract (inj₁ X12) (inj₂ (Sn.swap Sn.ₛ)) = ε , (inj₂ tt)
      ract (inj₁ X12X01) (inj₂ (Sn.swap Sn.ₛ)) = X₀₁' , (inj₁ X12X01)
      ract (inj₁ X12) (inj₂ Sn.swap) = ε , (inj₁ X12X01)
      ract (inj₁ X12X01) (inj₂ Sn.swap) = ε , (inj₁ X12)
      
      ract (inj₂ tt) (inj₁ (inj₁ tt)) = i₀' , (inj₂ tt)
      ract (inj₂ tt) (inj₁ (inj₂ (inj₁ tt))) = i₁' , (inj₂ tt)
      ract (inj₂ tt) (inj₁ (inj₂ (inj₂ tt))) = i₂' , (inj₂ tt)
      ract (inj₂ tt) (inj₂ (Sn.swap Sn.ₛ)) = ε , (inj₁ X12)
      ract (inj₂ tt) (inj₂ Sn.swap) = X₀₁' , (inj₂ tt)

      [_]ₒ : C → Word ((⊤ ⊎ ⊤ ⊎ ⊤) ⊎ Sn.X 2)
      [ X12 ]ₒ = X₁₂
      [ X12X01 ]ₒ = X₁₂ • X₀₁

      hcme : (c : C) (m : ((⊤ ⊎ ⊤) ⊎ Sn.X 1) ⊎ ⊤) → ∃ (λ w → ∃ (λ c' → (ract **) (inj₁ c) (f m) ≡ (w , inj₁ c')))
      hcme X12 (inj₁ (inj₁ (inj₁ tt))) = i₀' , (X12 , Eq.refl)
      hcme X12 (inj₁ (inj₁ (inj₂ tt))) = i₂' , (X12 , Eq.refl)
      hcme X12 (inj₁ (inj₂ Sn.swap)) = ε , (X12X01 , Eq.refl)
      hcme X12 (inj₂ tt) = i₁' , (X12 , Eq.refl)
      hcme X12X01 (inj₁ (inj₁ (inj₁ tt))) = i₂' , (X12X01 , Eq.refl)
      hcme X12X01 (inj₁ (inj₁ (inj₂ tt))) = i₀' , (X12X01 , Eq.refl)
      hcme X12X01 (inj₁ (inj₂ Sn.swap)) = ε , (X12 , Eq.refl)
      hcme X12X01 (inj₂ tt) = i₁' , (X12X01 , Eq.refl)

      htme : (m : ((⊤ ⊎ ⊤) ⊎ Sn.X 1) ⊎ ⊤) → (ract **) (inj₂ tt) (f m) ≡ ([ m ]ʷ , inj₂ tt)
      htme (inj₁ (inj₁ (inj₁ tt))) = Eq.refl
      htme (inj₁ (inj₁ (inj₂ tt))) = Eq.refl
      htme (inj₁ (inj₂ Sn.swap)) = Eq.refl
      htme (inj₂ tt) = Eq.refl

      infix 4 _~_
      _~_ = PW.Pointwise _≈₀_ (_≡_ {A = C ⊎ ⊤})

      htme~ : (m : ((⊤ ⊎ ⊤) ⊎ Sn.X 1) ⊎ ⊤) → ([ m ]ʷ , inj₂ tt) ~ ((ract **) (inj₂ tt) (f m))
      htme~ (inj₁ (inj₁ (inj₁ tt))) = _≈₀_.refl , Eq.refl
      htme~ (inj₁ (inj₁ (inj₂ tt))) = _≈₀_.refl , Eq.refl
      htme~ (inj₁ (inj₂ Sn.swap)) = _≈₀_.refl , Eq.refl
      htme~ (inj₂ tt) = _≈₀_.refl , Eq.refl

      open PB
      open PP.NFProperty (PD.pres-nfp) using (by-equal-nf)
      open PP.NFProperty (M.pres-M-nfp) renaming (by-equal-nf to bef) using ()
      
      hcme~ : (c : C) (m : ((⊤ ⊎ ⊤) ⊎ Sn.X 1) ⊎ ⊤) → [ c ]ₒ • f m ≈₁ ((f *) (proj₁ (hcme c m)) • [ proj₁ (proj₂ (hcme c m)) ]ₒ)
      hcme~ X12 (inj₁ (inj₁ (inj₁ tt))) = by-equal-nf Eq.refl
      hcme~ X12 (inj₁ (inj₁ (inj₂ tt))) = by-equal-nf Eq.refl
      hcme~ X12 (inj₁ (inj₂ Sn.swap)) = _≈₁_.sym _≈₁_.left-unit
      hcme~ X12 (inj₂ tt) = by-equal-nf Eq.refl
      hcme~ X12X01 (inj₁ (inj₁ (inj₁ tt))) = by-equal-nf Eq.refl
      hcme~ X12X01 (inj₁ (inj₁ (inj₂ tt))) = by-equal-nf Eq.refl
      hcme~ X12X01 (inj₁ (inj₂ Sn.swap)) = by-equal-nf Eq.refl
      hcme~ X12X01 (inj₂ tt) = by-equal-nf Eq.refl


      h-wd-ax : (c : C ⊎ ⊤) {u t : Word ((⊤ ⊎ ⊤ ⊎ ⊤) ⊎ Sn.X 2)} → u ===₁ t → (ract **) c u ~ ((ract **) c t)
      h-wd-ax (inj₂ tt) {.([ [ Cyclic.T ^' N ]ₗ ]ₗ)} {.([ [ ε ]ₗ ]ₗ)} (left (left Cyclic.order)) = bef Eq.refl , Eq.refl
      h-wd-ax (inj₂ tt) {.([ [ [ Cyclic.T ^' N ]ₗ ]ᵣ ]ₗ)} {.([ [ [ ε ]ₗ ]ᵣ ]ₗ)} (left (right (left Cyclic.order))) = (bef Eq.refl) , Eq.refl
      h-wd-ax (inj₂ tt) {.([ [ [ Cyclic.T ^' N ]ᵣ ]ᵣ ]ₗ)} {.([ [ [ ε ]ᵣ ]ᵣ ]ₗ)} (left (right (right Cyclic.order))) = bef Eq.refl , Eq.refl
      h-wd-ax (inj₂ tt) {.([ [ [ [ tt ]ʷ ]ₗ • [ [ tt ]ʷ ]ᵣ ]ᵣ ]ₗ)} {.([ [ [ [ tt ]ʷ ]ᵣ • [ [ tt ]ʷ ]ₗ ]ᵣ ]ₗ)} (left (right (mid (comm tt tt)))) = bef Eq.refl , Eq.refl
      h-wd-ax (inj₂ tt) {.([ [ [ tt ]ʷ ]ₗ • [ [ inj₁ tt ]ʷ ]ᵣ ]ₗ)} {.([ [ [ inj₁ tt ]ʷ ]ᵣ • [ [ tt ]ʷ ]ₗ ]ₗ)} (left (mid (comm tt (inj₁ tt)))) = bef Eq.refl , Eq.refl
      h-wd-ax (inj₂ tt) {.([ [ [ tt ]ʷ ]ₗ • [ [ inj₂ tt ]ʷ ]ᵣ ]ₗ)} {.([ [ [ inj₂ tt ]ʷ ]ᵣ • [ [ tt ]ʷ ]ₗ ]ₗ)} (left (mid (comm tt (inj₂ tt)))) = bef Eq.refl , Eq.refl
      h-wd-ax (inj₂ tt) {.([ [ Sn.swap ]ʷ • [ Sn.swap ]ʷ ]ᵣ)} {.([ ε ]ᵣ)} (right Sn.order) = bef Eq.refl , Eq.refl
      h-wd-ax (inj₂ tt) {.([ [ Sn.swap ]ʷ • [ Sn.swap Sn.ₛ ]ʷ • [ Sn.swap ]ʷ ]ᵣ)} {.([ [ Sn.swap Sn.ₛ ]ʷ • [ Sn.swap ]ʷ • [ Sn.swap Sn.ₛ ]ʷ ]ᵣ)} (right Sn.yang-baxter) = bef Eq.refl , Eq.refl
      h-wd-ax (inj₂ tt) {.([ Sn.[ [ Sn.swap ]ʷ • [ Sn.swap ]ʷ ⇑] ]ᵣ)} {.([ Sn.[ ε ⇑] ]ᵣ)} (right (Sn.congₛ Sn.order)) = bef Eq.refl , Eq.refl
      h-wd-ax (inj₂ tt) {.([ [ Sn.swap ]ʷ ]ᵣ • [ [ inj₁ tt ]ʷ ]ₗ)} {.([ [ conj 2 Sn.swap (inj₁ tt) ]ʷ ]ₗ • [ [ Sn.swap ]ʷ ]ᵣ)} (mid (comm (inj₁ tt) Sn.swap)) = bef Eq.refl , Eq.refl
      h-wd-ax (inj₂ tt) {.([ [ Sn.swap Sn.ₛ ]ʷ ]ᵣ • [ [ inj₁ tt ]ʷ ]ₗ)} {.([ [ conj 2 (Sn.swap Sn.ₛ) (inj₁ tt) ]ʷ ]ₗ • [ [ Sn.swap Sn.ₛ ]ʷ ]ᵣ)} (mid (comm (inj₁ tt) (Sn.swap Sn.ₛ))) = bef Eq.refl , Eq.refl
      h-wd-ax (inj₂ tt) {.([ [ Sn.swap ]ʷ ]ᵣ • [ [ inj₂ (inj₁ tt) ]ʷ ]ₗ)} {.([ [ conj 2 Sn.swap (inj₂ (inj₁ tt)) ]ʷ ]ₗ • [ [ Sn.swap ]ʷ ]ᵣ)} (mid (comm (inj₂ (inj₁ tt)) Sn.swap)) = bef Eq.refl , Eq.refl
      h-wd-ax (inj₂ tt) {.([ [ Sn.swap ]ʷ ]ᵣ • [ [ inj₂ (inj₂ tt) ]ʷ ]ₗ)} {.([ [ conj 2 Sn.swap (inj₂ (inj₂ tt)) ]ʷ ]ₗ • [ [ Sn.swap ]ʷ ]ᵣ)} (mid (comm (inj₂ (inj₂ tt)) Sn.swap)) = bef Eq.refl , Eq.refl
      h-wd-ax (inj₂ tt) {.([ [ Sn.swap Sn.ₛ ]ʷ ]ᵣ • [ [ inj₂ (inj₁ x) ]ʷ ]ₗ)} {.([ [ conj 2 (Sn.swap Sn.ₛ) (inj₂ (inj₁ x)) ]ʷ ]ₗ • [ [ Sn.swap Sn.ₛ ]ʷ ]ᵣ)} (mid (comm (inj₂ (inj₁ x)) (Sn.swap Sn.ₛ))) = bef Eq.refl , Eq.refl
      h-wd-ax (inj₂ tt) {.([ [ Sn.swap Sn.ₛ ]ʷ ]ᵣ • [ [ inj₂ (inj₂ y) ]ʷ ]ₗ)} {.([ [ conj 2 (Sn.swap Sn.ₛ) (inj₂ (inj₂ y)) ]ʷ ]ₗ • [ [ Sn.swap Sn.ₛ ]ʷ ]ᵣ)} (mid (comm (inj₂ (inj₂ y)) (Sn.swap Sn.ₛ))) = bef Eq.refl , Eq.refl

      h-wd-ax (inj₁ X12) {.([ [ Cyclic.T ^' N ]ₗ ]ₗ)} {.([ [ ε ]ₗ ]ₗ)} (left (left Cyclic.order)) = bef Eq.refl , Eq.refl
      h-wd-ax (inj₁ X12) {.([ [ [ Cyclic.T ^' N ]ₗ ]ᵣ ]ₗ)} {.([ [ [ ε ]ₗ ]ᵣ ]ₗ)} (left (right (left Cyclic.order))) = bef Eq.refl , Eq.refl
      h-wd-ax (inj₁ X12) {.([ [ [ Cyclic.T ^' N ]ᵣ ]ᵣ ]ₗ)} {.([ [ [ ε ]ᵣ ]ᵣ ]ₗ)} (left (right (right Cyclic.order))) = bef Eq.refl , Eq.refl
      h-wd-ax (inj₁ X12) {.([ [ [ [ tt ]ʷ ]ₗ • [ [ tt ]ʷ ]ᵣ ]ᵣ ]ₗ)} {.([ [ [ [ tt ]ʷ ]ᵣ • [ [ tt ]ʷ ]ₗ ]ᵣ ]ₗ)} (left (right (mid (comm tt tt)))) = bef Eq.refl , Eq.refl
      h-wd-ax (inj₁ X12) {.([ [ [ tt ]ʷ ]ₗ • [ [ inj₁ tt ]ʷ ]ᵣ ]ₗ)} {.([ [ [ inj₁ tt ]ʷ ]ᵣ • [ [ tt ]ʷ ]ₗ ]ₗ)} (left (mid (comm tt (inj₁ tt)))) = bef Eq.refl , Eq.refl
      h-wd-ax (inj₁ X12) {.([ [ [ tt ]ʷ ]ₗ • [ [ inj₂ tt ]ʷ ]ᵣ ]ₗ)} {.([ [ [ inj₂ tt ]ʷ ]ᵣ • [ [ tt ]ʷ ]ₗ ]ₗ)} (left (mid (comm tt (inj₂ tt)))) = bef Eq.refl , Eq.refl
      h-wd-ax (inj₁ X12) {.([ [ Sn.swap ]ʷ • [ Sn.swap ]ʷ ]ᵣ)} {.([ ε ]ᵣ)} (right Sn.order) = bef Eq.refl , Eq.refl
      h-wd-ax (inj₁ X12) {.([ [ Sn.swap ]ʷ • [ Sn.swap Sn.ₛ ]ʷ • [ Sn.swap ]ʷ ]ᵣ)} {.([ [ Sn.swap Sn.ₛ ]ʷ • [ Sn.swap ]ʷ • [ Sn.swap Sn.ₛ ]ʷ ]ᵣ)} (right Sn.yang-baxter) = bef Eq.refl , Eq.refl
      h-wd-ax (inj₁ X12) {.([ Sn.[ [ Sn.swap ]ʷ • [ Sn.swap ]ʷ ⇑] ]ᵣ)} {.([ Sn.[ ε ⇑] ]ᵣ)} (right (Sn.congₛ Sn.order)) = bef Eq.refl , Eq.refl
      h-wd-ax (inj₁ X12) {.([ [ Sn.swap ]ʷ ]ᵣ • [ [ inj₁ tt ]ʷ ]ₗ)} {.([ [ conj 2 Sn.swap (inj₁ tt) ]ʷ ]ₗ • [ [ Sn.swap ]ʷ ]ᵣ)} (mid (comm (inj₁ tt) Sn.swap)) = bef Eq.refl , Eq.refl
      h-wd-ax (inj₁ X12) {.([ [ Sn.swap Sn.ₛ ]ʷ ]ᵣ • [ [ inj₁ tt ]ʷ ]ₗ)} {.([ [ conj 2 (Sn.swap Sn.ₛ) (inj₁ tt) ]ʷ ]ₗ • [ [ Sn.swap Sn.ₛ ]ʷ ]ᵣ)} (mid (comm (inj₁ tt) (Sn.swap Sn.ₛ))) = bef Eq.refl , Eq.refl
      h-wd-ax (inj₁ X12) {.([ [ Sn.swap ]ʷ ]ᵣ • [ [ inj₂ (inj₁ tt) ]ʷ ]ₗ)} {.([ [ conj 2 Sn.swap (inj₂ (inj₁ tt)) ]ʷ ]ₗ • [ [ Sn.swap ]ʷ ]ᵣ)} (mid (comm (inj₂ (inj₁ tt)) Sn.swap)) = bef Eq.refl , Eq.refl
      h-wd-ax (inj₁ X12) {.([ [ Sn.swap ]ʷ ]ᵣ • [ [ inj₂ (inj₂ tt) ]ʷ ]ₗ)} {.([ [ conj 2 Sn.swap (inj₂ (inj₂ tt)) ]ʷ ]ₗ • [ [ Sn.swap ]ʷ ]ᵣ)} (mid (comm (inj₂ (inj₂ tt)) Sn.swap)) = bef Eq.refl , Eq.refl
      h-wd-ax (inj₁ X12) {.([ [ Sn.swap Sn.ₛ ]ʷ ]ᵣ • [ [ inj₂ (inj₁ x) ]ʷ ]ₗ)} {.([ [ conj 2 (Sn.swap Sn.ₛ) (inj₂ (inj₁ x)) ]ʷ ]ₗ • [ [ Sn.swap Sn.ₛ ]ʷ ]ᵣ)} (mid (comm (inj₂ (inj₁ x)) (Sn.swap Sn.ₛ))) = bef Eq.refl , Eq.refl 
      h-wd-ax (inj₁ X12) {.([ [ Sn.swap Sn.ₛ ]ʷ ]ᵣ • [ [ inj₂ (inj₂ y) ]ʷ ]ₗ)} {.([ [ conj 2 (Sn.swap Sn.ₛ) (inj₂ (inj₂ y)) ]ʷ ]ₗ • [ [ Sn.swap Sn.ₛ ]ʷ ]ᵣ)} (mid (comm (inj₂ (inj₂ y)) (Sn.swap Sn.ₛ))) = bef Eq.refl , Eq.refl


      h-wd-ax (inj₁ X12X01) {.([ [ Cyclic.T ^' N ]ₗ ]ₗ)} {.([ [ ε ]ₗ ]ₗ)} (left (left Cyclic.order)) = bef Eq.refl , Eq.refl
      h-wd-ax (inj₁ X12X01) {.([ [ [ Cyclic.T ^' N ]ₗ ]ᵣ ]ₗ)} {.([ [ [ ε ]ₗ ]ᵣ ]ₗ)} (left (right (left Cyclic.order))) = (bef Eq.refl) , Eq.refl
      h-wd-ax (inj₁ X12X01) {.([ [ [ Cyclic.T ^' N ]ᵣ ]ᵣ ]ₗ)} {.([ [ [ ε ]ᵣ ]ᵣ ]ₗ)} (left (right (right Cyclic.order))) = bef Eq.refl , Eq.refl
      h-wd-ax (inj₁ X12X01) {.([ [ [ [ tt ]ʷ ]ₗ • [ [ tt ]ʷ ]ᵣ ]ᵣ ]ₗ)} {.([ [ [ [ tt ]ʷ ]ᵣ • [ [ tt ]ʷ ]ₗ ]ᵣ ]ₗ)} (left (right (mid (comm tt tt)))) = bef Eq.refl , Eq.refl
      h-wd-ax (inj₁ X12X01) {.([ [ [ tt ]ʷ ]ₗ • [ [ inj₁ x ]ʷ ]ᵣ ]ₗ)} {.([ [ [ inj₁ x ]ʷ ]ᵣ • [ [ tt ]ʷ ]ₗ ]ₗ)} (left (mid (comm tt (inj₁ x)))) = bef Eq.refl , Eq.refl
      h-wd-ax (inj₁ X12X01) {.([ [ [ tt ]ʷ ]ₗ • [ [ inj₂ y ]ʷ ]ᵣ ]ₗ)} {.([ [ [ inj₂ y ]ʷ ]ᵣ • [ [ tt ]ʷ ]ₗ ]ₗ)} (left (mid (comm tt (inj₂ y)))) = bef Eq.refl , Eq.refl
      h-wd-ax (inj₁ X12X01) {.([ [ Sn.swap ]ʷ • [ Sn.swap ]ʷ ]ᵣ)} {.([ ε ]ᵣ)} (right Sn.order) = bef Eq.refl , Eq.refl
      h-wd-ax (inj₁ X12X01) {.([ [ Sn.swap ]ʷ • [ Sn.swap Sn.ₛ ]ʷ • [ Sn.swap ]ʷ ]ᵣ)} {.([ [ Sn.swap Sn.ₛ ]ʷ • [ Sn.swap ]ʷ • [ Sn.swap Sn.ₛ ]ʷ ]ᵣ)} (right Sn.yang-baxter) = bef Eq.refl , Eq.refl
      h-wd-ax (inj₁ X12X01) {.([ Sn.[ [ Sn.swap ]ʷ • [ Sn.swap ]ʷ ⇑] ]ᵣ)} {.([ Sn.[ ε ⇑] ]ᵣ)} (right (Sn.congₛ Sn.order)) = bef Eq.refl , Eq.refl
      h-wd-ax (inj₁ X12X01) {.([ [ Sn.swap ]ʷ ]ᵣ • [ [ inj₁ tt ]ʷ ]ₗ)} {.([ [ conj 2 Sn.swap (inj₁ tt) ]ʷ ]ₗ • [ [ Sn.swap ]ʷ ]ᵣ)} (mid (comm (inj₁ tt) Sn.swap)) = bef Eq.refl , Eq.refl
      h-wd-ax (inj₁ X12X01) {.([ [ Sn.swap Sn.ₛ ]ʷ ]ᵣ • [ [ inj₁ tt ]ʷ ]ₗ)} {.([ [ conj 2 (Sn.swap Sn.ₛ) (inj₁ tt) ]ʷ ]ₗ • [ [ Sn.swap Sn.ₛ ]ʷ ]ᵣ)} (mid (comm (inj₁ tt) (Sn.swap Sn.ₛ))) = bef Eq.refl , Eq.refl
      h-wd-ax (inj₁ X12X01) {.([ [ Sn.swap ]ʷ ]ᵣ • [ [ inj₂ (inj₁ tt) ]ʷ ]ₗ)} {.([ [ conj 2 Sn.swap (inj₂ (inj₁ tt)) ]ʷ ]ₗ • [ [ Sn.swap ]ʷ ]ᵣ)} (mid (comm (inj₂ (inj₁ tt)) Sn.swap)) = bef Eq.refl , Eq.refl
      h-wd-ax (inj₁ X12X01) {.([ [ Sn.swap ]ʷ ]ᵣ • [ [ inj₂ (inj₂ tt) ]ʷ ]ₗ)} {.([ [ conj 2 Sn.swap (inj₂ (inj₂ tt)) ]ʷ ]ₗ • [ [ Sn.swap ]ʷ ]ᵣ)} (mid (comm (inj₂ (inj₂ tt)) Sn.swap)) = bef Eq.refl , Eq.refl
      h-wd-ax (inj₁ X12X01) {.([ [ Sn.swap Sn.ₛ ]ʷ ]ᵣ • [ [ inj₂ (inj₁ x) ]ʷ ]ₗ)} {.([ [ conj 2 (Sn.swap Sn.ₛ) (inj₂ (inj₁ x)) ]ʷ ]ₗ • [ [ Sn.swap Sn.ₛ ]ʷ ]ᵣ)} (mid (comm (inj₂ (inj₁ x)) (Sn.swap Sn.ₛ))) = bef Eq.refl , Eq.refl
      h-wd-ax (inj₁ X12X01) {.([ [ Sn.swap Sn.ₛ ]ʷ ]ᵣ • [ [ inj₂ (inj₂ y) ]ʷ ]ₗ)} {.([ [ conj 2 (Sn.swap Sn.ₛ) (inj₂ (inj₂ y)) ]ʷ ]ₗ • [ [ Sn.swap Sn.ₛ ]ʷ ]ᵣ)} (mid (comm (inj₂ (inj₂ y)) (Sn.swap Sn.ₛ))) = bef Eq.refl , Eq.refl

      f-wd-ax : {w v : Word (((⊤ ⊎ ⊤) ⊎ Sn.X 1) ⊎ ⊤)} → w ===₀ v → (f *) w ≈₁ (f *) v
      f-wd-ax {.([ [ [ Cyclic.T ^' N ]ₗ ]ₗ ]ₗ)} {.([ [ [ ε ]ₗ ]ₗ ]ₗ)} (left (left (left Cyclic.order))) = by-equal-nf Eq.refl
      f-wd-ax {.([ [ [ Cyclic.T ^' N ]ᵣ ]ₗ ]ₗ)} {.([ [ [ ε ]ᵣ ]ₗ ]ₗ)} (left (left (right Cyclic.order))) = by-equal-nf Eq.refl
      f-wd-ax {.([ [ [ [ tt ]ʷ ]ₗ • [ [ tt ]ʷ ]ᵣ ]ₗ ]ₗ)} {.([ [ [ [ tt ]ʷ ]ᵣ • [ [ tt ]ʷ ]ₗ ]ₗ ]ₗ)} (left (left (mid (comm tt tt)))) = by-equal-nf Eq.refl
      f-wd-ax {.([ [ [ Sn.swap ]ʷ • [ Sn.swap ]ʷ ]ᵣ ]ₗ)} {.([ [ ε ]ᵣ ]ₗ)} (left (right Sn.order)) = by-equal-nf Eq.refl
      f-wd-ax {.([ [ [ Sn.swap ]ʷ ]ᵣ • [ [ inj₁ x ]ʷ ]ₗ ]ₗ)} {.([ [ [ conj 1 Sn.swap (inj₁ x) ]ʷ ]ₗ • [ [ Sn.swap ]ʷ ]ᵣ ]ₗ)} (left (mid (comm (inj₁ x) Sn.swap))) = by-equal-nf Eq.refl
      f-wd-ax {.([ [ [ Sn.swap ]ʷ ]ᵣ • [ [ inj₂ y ]ʷ ]ₗ ]ₗ)} {.([ [ [ conj 1 Sn.swap (inj₂ y) ]ʷ ]ₗ • [ [ Sn.swap ]ʷ ]ᵣ ]ₗ)} (left (mid (comm (inj₂ y) Sn.swap))) = by-equal-nf Eq.refl
      f-wd-ax {.([ Cyclic.T ^' 4 ]ᵣ)} {.([ ε ]ᵣ)} (right Cyclic.order) = by-equal-nf Eq.refl
      f-wd-ax {.([ [ inj₁ (inj₁ tt) ]ʷ ]ₗ • [ [ tt ]ʷ ]ᵣ)} {.([ [ tt ]ʷ ]ᵣ • [ [ inj₁ (inj₁ tt) ]ʷ ]ₗ)} (mid (comm (inj₁ (inj₁ tt)) tt)) = by-equal-nf Eq.refl
      f-wd-ax {.([ [ inj₁ (inj₂ tt) ]ʷ ]ₗ • [ [ tt ]ʷ ]ᵣ)} {.([ [ tt ]ʷ ]ᵣ • [ [ inj₁ (inj₂ tt) ]ʷ ]ₗ)} (mid (comm (inj₁ (inj₂ tt)) tt)) = by-equal-nf Eq.refl
      f-wd-ax {.([ [ inj₂ Sn.swap ]ʷ ]ₗ • [ [ tt ]ʷ ]ᵣ)} {.([ [ tt ]ʷ ]ᵣ • [ [ inj₂ Sn.swap ]ʷ ]ₗ)} (mid (comm (inj₂ Sn.swap) tt)) = by-equal-nf Eq.refl

      [_] : C ⊎ ⊤ -> Word ((⊤ ⊎ ⊤ ⊎ ⊤) ⊎ Sn.X 2)
      [_] = [_,_] [_]ₒ (λ v → ε)

      h=ract :  ∀ c y -> let (m' , c') = ract c y in let [_]ₓ  = (f *) in [ c ] • [ y ]ʷ ≈₁ [ m' ]ₓ • [ c' ]
      h=ract (inj₁ X12) (inj₁ (inj₁ tt)) = by-equal-nf Eq.refl
      h=ract (inj₁ X12) (inj₁ (inj₂ (inj₁ tt))) = by-equal-nf Eq.refl
      h=ract (inj₁ X12) (inj₁ (inj₂ (inj₂ tt))) = by-equal-nf Eq.refl
      h=ract (inj₁ X12) (inj₂ Sn.swap) = by-equal-nf Eq.refl
      h=ract (inj₁ X12) (inj₂ (Sn.swap Sn.ₛ)) = by-equal-nf Eq.refl

      h=ract (inj₂ tt) (inj₁ (inj₁ tt)) = by-equal-nf Eq.refl
      h=ract (inj₂ tt) (inj₁ (inj₂ (inj₁ tt))) = by-equal-nf Eq.refl
      h=ract (inj₂ tt) (inj₁ (inj₂ (inj₂ tt))) = by-equal-nf Eq.refl
      h=ract (inj₂ tt) (inj₂ Sn.swap) = by-equal-nf Eq.refl
      h=ract (inj₂ tt) (inj₂ (Sn.swap Sn.ₛ)) = by-equal-nf Eq.refl

      h=ract (inj₁ X12X01) (inj₁ (inj₁ tt)) = by-equal-nf Eq.refl
      h=ract (inj₁ X12X01) (inj₁ (inj₂ (inj₁ tt))) = by-equal-nf Eq.refl
      h=ract (inj₁ X12X01) (inj₁ (inj₂ (inj₂ tt))) = by-equal-nf Eq.refl
      h=ract (inj₁ X12X01) (inj₂ Sn.swap) = by-equal-nf Eq.refl
      h=ract (inj₁ X12X01) (inj₂ (Sn.swap Sn.ₛ)) = by-equal-nf Eq.refl

    module CA2 where
      data C : Set where
        K01 : C
        K01I0 : C
      

      i₀ : Word B
      i₀ = [ [ Ki.i₀ ]ₗ ]ᵣ

      i₁ : Word B
      i₁ = [ [ Ki.i₁ ]ₗ ]ᵣ

      i₂ : Word B
      i₂ = [ [ inj₂ tt ]ʷ ]ᵣ

      swap₀₁ : Word B
      swap₀₁ = [ inj₁ tt ]ʷ

      K₀₁ : Word B
      K₀₁ = [ [ Ki.K₀₁ ]ₗ ]ᵣ

      X₀₁ = swap₀₁

      i₀' : Word (((⊤ ⊎ ⊤) ⊎ Sn.X 1) ⊎ ⊤)
      i₀' = [ inj₁ (inj₁ (inj₁ tt)) ]ʷ
      i₁' : Word (((⊤ ⊎ ⊤) ⊎ Sn.X 1) ⊎ ⊤)
      i₁' = [ inj₁ (inj₁ (inj₂ tt)) ]ʷ
      i₂' : Word (((⊤ ⊎ ⊤) ⊎ Sn.X 1) ⊎ ⊤)
      i₂' = [ inj₂ tt ]ʷ

      X₀₁' : Word (((⊤ ⊎ ⊤) ⊎ Sn.X 1) ⊎ ⊤)
      X₀₁' = [ inj₁ (inj₂ Sn.swap) ]ʷ

      f : M → Word B
      f (inj₁ (inj₁ (inj₁ tt))) = i₀
      f (inj₁ (inj₁ (inj₂ tt))) = i₁
      f (inj₁ (inj₂ Sn.swap)) = swap₀₁
      f (inj₂ tt) = i₂

      pattern I = inj₂ tt

      ract : C ⊎ ⊤ → B → Word M × (C ⊎ ⊤)

      ract I (inj₂ (inj₁ Ki.i₀-gen)) = i₀' , I
      ract (inj₁ K01) (inj₂ (inj₁ Ki.i₀-gen)) = ε , (inj₁ K01I0)
      ract (inj₁ K01I0) (inj₂ (inj₁ Ki.i₀-gen)) = X₀₁' • i₀' • i₀' • i₁' • i₁' , inj₁ K01
      ract (inj₂ tt) (inj₂ (inj₁ Ki.K₀₁-gen)) = ε , inj₁ K01
      ract (inj₁ K01) (inj₂ (inj₁ Ki.K₀₁-gen)) = i₀' • i₀' • i₀' • i₁' • i₁' • i₁' , I
      ract (inj₁ K01I0) (inj₂ (inj₁ Ki.K₀₁-gen)) = X₀₁' • i₁' • i₁' • i₁' , (inj₁ K01I0)
      ract I (inj₂ (inj₁ Ki.i₁-gen)) = i₁' , I
      ract (inj₁ K01) (inj₂ (inj₁ Ki.i₁-gen)) = X₀₁' • i₀' • i₀' • i₀' • i₁' • i₁' • i₁' , (inj₁ K01I0)
      ract (inj₁ K01I0) (inj₂ (inj₁ Ki.i₁-gen)) = i₀' • i₁' , inj₁ K01
      ract I (inj₁ tt) = X₀₁' , I
      ract (inj₁ K01) (inj₁ tt) = i₁' • i₁' , inj₁ K01
      ract (inj₁ K01I0) (inj₁ tt) = X₀₁' • i₀' • i₁' • i₁' • i₁' , (inj₁ K01I0)
      ract I (inj₂ (inj₂ tt)) = i₂' , I
      ract (inj₁ K01) (inj₂ (inj₂ tt)) = i₂' , inj₁ K01
      ract (inj₁ K01I0) (inj₂ (inj₂ tt)) = i₂' , (inj₁ K01I0)
     
      [_]ₒ : C → Word B
      [ K01 ]ₒ = K₀₁
      [ K01I0 ]ₒ = K₀₁ • i₀


      hcme : (c : C) (m : M) → ∃ (λ w → ∃ (λ c' → (ract **) (inj₁ c) (f m) ≡ (w , inj₁ c')))
      hcme (K01) (inj₁ (inj₁ (inj₁ tt))) = ε , (K01I0 , Eq.refl)
      hcme (K01) (inj₁ (inj₁ (inj₂ tt))) = [ inj₁ (inj₂ Sn.swap) ]ʷ •
                                            [ inj₁ (inj₁ (inj₁ tt)) ]ʷ •
                                            [ inj₁ (inj₁ (inj₁ tt)) ]ʷ •
                                            [ inj₁ (inj₁ (inj₁ tt)) ]ʷ •
                                            [ inj₁ (inj₁ (inj₂ tt)) ]ʷ •
                                            [ inj₁ (inj₁ (inj₂ tt)) ]ʷ • [ inj₁ (inj₁ (inj₂ tt)) ]ʷ , (K01I0 , Eq.refl) 
      hcme (K01) (inj₁ (inj₂ Sn.swap)) = [ inj₁ (inj₁ (inj₂ tt)) ]ʷ • [ inj₁ (inj₁ (inj₂ tt)) ]ʷ , (K01 , Eq.refl)
      hcme (K01) (inj₂ tt) = [ inj₂ tt ]ʷ , (K01 , Eq.refl)

      hcme K01I0 (inj₁ (inj₁ (inj₁ tt))) = [ inj₁ (inj₂ Sn.swap) ]ʷ •
                                            [ inj₁ (inj₁ (inj₁ tt)) ]ʷ •
                                            [ inj₁ (inj₁ (inj₁ tt)) ]ʷ •
                                            [ inj₁ (inj₁ (inj₂ tt)) ]ʷ • [ inj₁ (inj₁ (inj₂ tt)) ]ʷ , (K01 , Eq.refl)
      hcme K01I0 (inj₁ (inj₁ I)) = [ inj₁ (inj₁ (inj₁ tt)) ]ʷ • [ inj₁ (inj₁ (inj₂ tt)) ]ʷ , (K01 , Eq.refl)
      hcme K01I0 (inj₁ (inj₂ Sn.swap)) = [ inj₁ (inj₂ Sn.swap) ]ʷ •
                                          [ inj₁ (inj₁ (inj₁ tt)) ]ʷ •
                                          [ inj₁ (inj₁ (inj₂ tt)) ]ʷ •
                                          [ inj₁ (inj₁ (inj₂ tt)) ]ʷ • [ inj₁ (inj₁ (inj₂ tt)) ]ʷ , (K01I0 , Eq.refl)
      hcme K01I0 I = [ inj₂ tt ]ʷ , (K01I0 , Eq.refl)

      htme : (m : M) → (ract **) (inj₂ tt) (f m) ≡ ([ m ]ʷ , inj₂ tt)
      htme (inj₁ (inj₁ (inj₁ tt))) = Eq.refl
      htme (inj₁ (inj₁ (inj₂ tt))) = Eq.refl
      htme (inj₁ (inj₂ Sn.swap)) = Eq.refl
      htme (inj₂ tt) = Eq.refl


      infix 4 _~_
      _~_ = PW.Pointwise _≈₀_ (_≡_ {A = C ⊎ ⊤})

      htme~ : (m : M) → ([ m ]ʷ , inj₂ tt) ~ ((ract **) (inj₂ tt) (f m))
      htme~ (inj₁ (inj₁ (inj₁ tt))) = _≈₀_.refl , Eq.refl
      htme~ (inj₁ (inj₁ (inj₂ tt))) = _≈₀_.refl , Eq.refl
      htme~ (inj₁ (inj₂ Sn.swap)) = _≈₀_.refl , Eq.refl
      htme~ (inj₂ tt) = _≈₀_.refl , Eq.refl

      open PB
      open PP.NFProperty (Ki.nfp-a) using (by-equal-nf)
      open PP.NFProperty (M.pres-M-nfp) renaming (by-equal-nf to bef) using ()
      
      hcme~ : (c : C) (m : M) → [ c ]ₒ • f m ≈₂ ((f *) (proj₁ (hcme c m)) • [ proj₁ (proj₂ (hcme c m)) ]ₒ)
      hcme~ K01 (inj₁ (inj₁ (inj₁ tt))) = by-equal-nf Eq.refl
      hcme~ K01 (inj₁ (inj₁ (inj₂ tt))) = by-equal-nf Eq.refl
      hcme~ K01 (inj₁ (inj₂ Sn.swap)) = by-equal-nf Eq.refl
      hcme~ K01 (inj₂ tt) = by-equal-nf Eq.refl
      hcme~ K01I0 (inj₁ (inj₁ (inj₁ tt))) = by-equal-nf Eq.refl
      hcme~ K01I0 (inj₁ (inj₁ (inj₂ tt))) = by-equal-nf Eq.refl
      hcme~ K01I0 (inj₁ (inj₂ Sn.swap)) = by-equal-nf Eq.refl
      hcme~ K01I0 (inj₂ tt) = by-equal-nf Eq.refl
      

      h-wd-ax : (c : C ⊎ ⊤) {u t : Word B} → u ===₂ t → (ract **) c u ~ ((ract **) c t)
      
      h-wd-ax (inj₁ K01I0) {.([ Cyclic.T ^' 2 ]ₗ)} {.([ ε ]ₗ)} (left Cyclic.order) = (bef Eq.refl) , Eq.refl
      h-wd-ax (inj₁ K01I0) {.([ [ Ki.i₀ ^ 4 ]ₗ ]ᵣ)} {.([ [ ε ]ₗ ]ᵣ)} (right (left Ki.[S2a])) = (bef Eq.refl) , Eq.refl
      h-wd-ax (inj₁ K01I0) {.([ [ Ki.i₁ ^ 4 ]ₗ ]ᵣ)} {.([ [ ε ]ₗ ]ᵣ)} (right (left Ki.[S2b])) = (bef Eq.refl) , Eq.refl
      h-wd-ax (inj₁ K01I0) {.([ [ Ki.i₁ • Ki.i₀ ]ₗ ]ᵣ)} {.([ [ Ki.i₀ • Ki.i₁ ]ₗ ]ᵣ)} (right (left Ki.[S4a])) = (bef Eq.refl) , Eq.refl
      h-wd-ax (inj₁ K01I0) {.([ [ Ki.K₀₁ • Ki.i₀ • Ki.i₀ • Ki.K₀₁ • Ki.i₁ ]ₗ ]ᵣ)} {.([ [ Ki.i₀ • Ki.K₀₁ • Ki.i₀ • Ki.i₀ • Ki.K₀₁ ]ₗ ]ᵣ)} (right (left Ki.[S10])) = (bef Eq.refl) , Eq.refl
      h-wd-ax (inj₁ K01I0) {.([ [ Ki.K₀₁ • Ki.i₀ • Ki.i₀ • Ki.K₀₁ • Ki.i₀ ]ₗ ]ᵣ)} {.([ [ Ki.i₁ • Ki.K₀₁ • Ki.i₀ • Ki.i₀ • Ki.K₀₁ ]ₗ ]ᵣ)} (right (left Ki.[S10b])) = (bef Eq.refl) , Eq.refl
      h-wd-ax (inj₁ K01I0) {.([ [ Ki.i₁ • Ki.K₀₁ • Ki.i₁ • Ki.K₀₁ ]ₗ ]ᵣ)} {.([ [ Ki.K₀₁ • Ki.i₁ ^ 3 ]ₗ ]ᵣ)} (right (left Ki.[S11])) = (bef Eq.refl) , Eq.refl
      h-wd-ax (inj₁ K01I0) {.([ [ Ki.K₀₁ • Ki.i₀ • Ki.i₁ ]ₗ ]ᵣ)} {.([ [ Ki.i₀ • Ki.i₁ • Ki.K₀₁ ]ₗ ]ᵣ)} (right (left Ki.[S12])) = (bef Eq.refl) , Eq.refl
      h-wd-ax (inj₁ K01I0) {.([ [ Ki.K₀₁ ^ 2 • Ki.i₀ • Ki.i₁ ]ₗ ]ᵣ)} {.([ [ ε ]ₗ ]ᵣ)} (right (left Ki.[S14])) = (bef Eq.refl) , Eq.refl
      h-wd-ax (inj₁ K01I0) {.([ [ Cyclic.T ^' 4 ]ᵣ ]ᵣ)} {.([ [ ε ]ᵣ ]ᵣ)} (right (right Cyclic.order)) = (bef Eq.refl) , Eq.refl
      h-wd-ax (inj₁ K01I0) {.([ [ [ Ki.K₀₁-gen ]ʷ ]ₗ • [ [ tt ]ʷ ]ᵣ ]ᵣ)} {.([ [ [ tt ]ʷ ]ᵣ • [ [ Ki.K₀₁-gen ]ʷ ]ₗ ]ᵣ)} (right (mid (comm Ki.K₀₁-gen tt))) = (bef Eq.refl) , Eq.refl
      h-wd-ax (inj₁ K01I0) {.([ [ [ Ki.i₀-gen ]ʷ ]ₗ • [ [ tt ]ʷ ]ᵣ ]ᵣ)} {.([ [ [ tt ]ʷ ]ᵣ • [ [ Ki.i₀-gen ]ʷ ]ₗ ]ᵣ)} (right (mid (comm Ki.i₀-gen tt))) = (bef Eq.refl) , Eq.refl
      h-wd-ax (inj₁ K01I0) {.([ [ [ Ki.i₁-gen ]ʷ ]ₗ • [ [ tt ]ʷ ]ᵣ ]ᵣ)} {.([ [ [ tt ]ʷ ]ᵣ • [ [ Ki.i₁-gen ]ʷ ]ₗ ]ᵣ)} (right (mid (comm Ki.i₁-gen tt))) = (bef Eq.refl) , Eq.refl
      h-wd-ax (inj₁ K01I0) {.([ inj₁ _ ]ʷ)} {.([ Ki.fs _ ]ᵣ)} (mid desugar) = (bef Eq.refl) , Eq.refl
            
      h-wd-ax (inj₁ K01) {.([ Cyclic.T ^' 2 ]ₗ)} {.([ ε ]ₗ)} (left Cyclic.order) = (bef Eq.refl) , Eq.refl
      h-wd-ax (inj₁ K01) {.([ [ Ki.i₀ ^ 4 ]ₗ ]ᵣ)} {.([ [ ε ]ₗ ]ᵣ)} (right (left Ki.[S2a])) = (bef Eq.refl) , Eq.refl
      h-wd-ax (inj₁ K01) {.([ [ Ki.i₁ ^ 4 ]ₗ ]ᵣ)} {.([ [ ε ]ₗ ]ᵣ)} (right (left Ki.[S2b])) = (bef Eq.refl) , Eq.refl
      h-wd-ax (inj₁ K01) {.([ [ Ki.i₁ • Ki.i₀ ]ₗ ]ᵣ)} {.([ [ Ki.i₀ • Ki.i₁ ]ₗ ]ᵣ)} (right (left Ki.[S4a])) = (bef Eq.refl) , Eq.refl
      h-wd-ax (inj₁ K01) {.([ [ Ki.K₀₁ • Ki.i₀ • Ki.i₀ • Ki.K₀₁ • Ki.i₁ ]ₗ ]ᵣ)} {.([ [ Ki.i₀ • Ki.K₀₁ • Ki.i₀ • Ki.i₀ • Ki.K₀₁ ]ₗ ]ᵣ)} (right (left Ki.[S10])) = (bef Eq.refl) , Eq.refl
      h-wd-ax (inj₁ K01) {.([ [ Ki.K₀₁ • Ki.i₀ • Ki.i₀ • Ki.K₀₁ • Ki.i₀ ]ₗ ]ᵣ)} {.([ [ Ki.i₁ • Ki.K₀₁ • Ki.i₀ • Ki.i₀ • Ki.K₀₁ ]ₗ ]ᵣ)} (right (left Ki.[S10b])) = (bef Eq.refl) , Eq.refl
      h-wd-ax (inj₁ K01) {.([ [ Ki.i₁ • Ki.K₀₁ • Ki.i₁ • Ki.K₀₁ ]ₗ ]ᵣ)} {.([ [ Ki.K₀₁ • Ki.i₁ ^ 3 ]ₗ ]ᵣ)} (right (left Ki.[S11])) = (bef Eq.refl) , Eq.refl
      h-wd-ax (inj₁ K01) {.([ [ Ki.K₀₁ • Ki.i₀ • Ki.i₁ ]ₗ ]ᵣ)} {.([ [ Ki.i₀ • Ki.i₁ • Ki.K₀₁ ]ₗ ]ᵣ)} (right (left Ki.[S12])) = (bef Eq.refl) , Eq.refl
      h-wd-ax (inj₁ K01) {.([ [ Ki.K₀₁ ^ 2 • Ki.i₀ • Ki.i₁ ]ₗ ]ᵣ)} {.([ [ ε ]ₗ ]ᵣ)} (right (left Ki.[S14])) = (bef Eq.refl) , Eq.refl
      h-wd-ax (inj₁ K01) {.([ [ Cyclic.T ^' 4 ]ᵣ ]ᵣ)} {.([ [ ε ]ᵣ ]ᵣ)} (right (right Cyclic.order)) = (bef Eq.refl) , Eq.refl
      h-wd-ax (inj₁ K01) {.([ [ [ Ki.K₀₁-gen ]ʷ ]ₗ • [ [ tt ]ʷ ]ᵣ ]ᵣ)} {.([ [ [ tt ]ʷ ]ᵣ • [ [ Ki.K₀₁-gen ]ʷ ]ₗ ]ᵣ)} (right (mid (comm Ki.K₀₁-gen tt))) = (bef Eq.refl) , Eq.refl
      h-wd-ax (inj₁ K01) {.([ [ [ Ki.i₀-gen ]ʷ ]ₗ • [ [ tt ]ʷ ]ᵣ ]ᵣ)} {.([ [ [ tt ]ʷ ]ᵣ • [ [ Ki.i₀-gen ]ʷ ]ₗ ]ᵣ)} (right (mid (comm Ki.i₀-gen tt))) = (bef Eq.refl) , Eq.refl
      h-wd-ax (inj₁ K01) {.([ [ [ Ki.i₁-gen ]ʷ ]ₗ • [ [ tt ]ʷ ]ᵣ ]ᵣ)} {.([ [ [ tt ]ʷ ]ᵣ • [ [ Ki.i₁-gen ]ʷ ]ₗ ]ᵣ)} (right (mid (comm Ki.i₁-gen tt))) = (bef Eq.refl) , Eq.refl
      h-wd-ax (inj₁ K01) {.([ inj₁ _ ]ʷ)} {.([ Ki.fs _ ]ᵣ)} (mid desugar) = (bef Eq.refl) , Eq.refl

      h-wd-ax (inj₂ tt) {.([ Cyclic.T ^' 2 ]ₗ)} {.([ ε ]ₗ)} (left Cyclic.order) = (bef Eq.refl) , Eq.refl
      h-wd-ax (inj₂ tt) {.([ [ Ki.i₀ ^ 4 ]ₗ ]ᵣ)} {.([ [ ε ]ₗ ]ᵣ)} (right (left Ki.[S2a])) = (bef Eq.refl) , Eq.refl
      h-wd-ax (inj₂ tt) {.([ [ Ki.i₁ ^ 4 ]ₗ ]ᵣ)} {.([ [ ε ]ₗ ]ᵣ)} (right (left Ki.[S2b])) = (bef Eq.refl) , Eq.refl
      h-wd-ax (inj₂ tt) {.([ [ Ki.i₁ • Ki.i₀ ]ₗ ]ᵣ)} {.([ [ Ki.i₀ • Ki.i₁ ]ₗ ]ᵣ)} (right (left Ki.[S4a])) = (bef Eq.refl) , Eq.refl
      h-wd-ax (inj₂ tt) {.([ [ Ki.K₀₁ • Ki.i₀ • Ki.i₀ • Ki.K₀₁ • Ki.i₁ ]ₗ ]ᵣ)} {.([ [ Ki.i₀ • Ki.K₀₁ • Ki.i₀ • Ki.i₀ • Ki.K₀₁ ]ₗ ]ᵣ)} (right (left Ki.[S10])) = (bef Eq.refl) , Eq.refl
      h-wd-ax (inj₂ tt) {.([ [ Ki.K₀₁ • Ki.i₀ • Ki.i₀ • Ki.K₀₁ • Ki.i₀ ]ₗ ]ᵣ)} {.([ [ Ki.i₁ • Ki.K₀₁ • Ki.i₀ • Ki.i₀ • Ki.K₀₁ ]ₗ ]ᵣ)} (right (left Ki.[S10b])) = (bef Eq.refl) , Eq.refl
      h-wd-ax (inj₂ tt) {.([ [ Ki.i₁ • Ki.K₀₁ • Ki.i₁ • Ki.K₀₁ ]ₗ ]ᵣ)} {.([ [ Ki.K₀₁ • Ki.i₁ ^ 3 ]ₗ ]ᵣ)} (right (left Ki.[S11])) = (bef Eq.refl) , Eq.refl
      h-wd-ax (inj₂ tt) {.([ [ Ki.K₀₁ • Ki.i₀ • Ki.i₁ ]ₗ ]ᵣ)} {.([ [ Ki.i₀ • Ki.i₁ • Ki.K₀₁ ]ₗ ]ᵣ)} (right (left Ki.[S12])) = (bef Eq.refl) , Eq.refl
      h-wd-ax (inj₂ tt) {.([ [ Ki.K₀₁ ^ 2 • Ki.i₀ • Ki.i₁ ]ₗ ]ᵣ)} {.([ [ ε ]ₗ ]ᵣ)} (right (left Ki.[S14])) = (bef Eq.refl) , Eq.refl
      h-wd-ax (inj₂ tt) {.([ [ Cyclic.T ^' 4 ]ᵣ ]ᵣ)} {.([ [ ε ]ᵣ ]ᵣ)} (right (right Cyclic.order)) = (bef Eq.refl) , Eq.refl
      h-wd-ax (inj₂ tt) {.([ [ [ Ki.K₀₁-gen ]ʷ ]ₗ • [ [ tt ]ʷ ]ᵣ ]ᵣ)} {.([ [ [ tt ]ʷ ]ᵣ • [ [ Ki.K₀₁-gen ]ʷ ]ₗ ]ᵣ)} (right (mid (comm Ki.K₀₁-gen tt))) = (bef Eq.refl) , Eq.refl
      h-wd-ax (inj₂ tt) {.([ [ [ Ki.i₀-gen ]ʷ ]ₗ • [ [ tt ]ʷ ]ᵣ ]ᵣ)} {.([ [ [ tt ]ʷ ]ᵣ • [ [ Ki.i₀-gen ]ʷ ]ₗ ]ᵣ)} (right (mid (comm Ki.i₀-gen tt))) = (bef Eq.refl) , Eq.refl
      h-wd-ax (inj₂ tt) {.([ [ [ Ki.i₁-gen ]ʷ ]ₗ • [ [ tt ]ʷ ]ᵣ ]ᵣ)} {.([ [ [ tt ]ʷ ]ᵣ • [ [ Ki.i₁-gen ]ʷ ]ₗ ]ᵣ)} (right (mid (comm Ki.i₁-gen tt))) = (bef Eq.refl) , Eq.refl
      h-wd-ax (inj₂ tt) {.([ inj₁ _ ]ʷ)} {.([ Ki.fs _ ]ᵣ)} (mid desugar) = (bef Eq.refl) , Eq.refl
      
      f-wd-ax : {w v : Word M} → w ===₀ v → (f *) w ≈₂ (f *) v
      f-wd-ax {.([ [ [ Cyclic.T ^' N ]ₗ ]ₗ ]ₗ)} {.([ [ [ ε ]ₗ ]ₗ ]ₗ)} (left (left (left Cyclic.order))) = by-equal-nf Eq.refl
      f-wd-ax {.([ [ [ Cyclic.T ^' N ]ᵣ ]ₗ ]ₗ)} {.([ [ [ ε ]ᵣ ]ₗ ]ₗ)} (left (left (right Cyclic.order))) = by-equal-nf Eq.refl
      f-wd-ax {.([ [ [ [ tt ]ʷ ]ₗ • [ [ tt ]ʷ ]ᵣ ]ₗ ]ₗ)} {.([ [ [ [ tt ]ʷ ]ᵣ • [ [ tt ]ʷ ]ₗ ]ₗ ]ₗ)} (left (left (mid (comm tt tt)))) = by-equal-nf Eq.refl
      f-wd-ax {.([ [ [ Sn.swap ]ʷ • [ Sn.swap ]ʷ ]ᵣ ]ₗ)} {.([ [ ε ]ᵣ ]ₗ)} (left (right Sn.order)) = by-equal-nf Eq.refl
      f-wd-ax {.([ [ [ Sn.swap ]ʷ ]ᵣ • [ [ inj₁ x ]ʷ ]ₗ ]ₗ)} {.([ [ [ conj 1 Sn.swap (inj₁ x) ]ʷ ]ₗ • [ [ Sn.swap ]ʷ ]ᵣ ]ₗ)} (left (mid (comm (inj₁ x) Sn.swap))) = by-equal-nf Eq.refl
      f-wd-ax {.([ [ [ Sn.swap ]ʷ ]ᵣ • [ [ inj₂ y ]ʷ ]ₗ ]ₗ)} {.([ [ [ conj 1 Sn.swap (inj₂ y) ]ʷ ]ₗ • [ [ Sn.swap ]ʷ ]ᵣ ]ₗ)} (left (mid (comm (inj₂ y) Sn.swap))) = by-equal-nf Eq.refl
      f-wd-ax {.([ Cyclic.T ^' 4 ]ᵣ)} {.([ ε ]ᵣ)} (right Cyclic.order) = by-equal-nf Eq.refl
      f-wd-ax {.([ [ inj₁ (inj₁ tt) ]ʷ ]ₗ • [ [ tt ]ʷ ]ᵣ)} {.([ [ tt ]ʷ ]ᵣ • [ [ inj₁ (inj₁ tt) ]ʷ ]ₗ)} (mid (comm (inj₁ (inj₁ tt)) tt)) = by-equal-nf Eq.refl
      f-wd-ax {.([ [ inj₁ I ]ʷ ]ₗ • [ [ tt ]ʷ ]ᵣ)} {.([ [ tt ]ʷ ]ᵣ • [ [ inj₁ I ]ʷ ]ₗ)} (mid (comm (inj₁ I) tt)) = by-equal-nf Eq.refl
      f-wd-ax {.([ [ inj₂ Sn.swap ]ʷ ]ₗ • [ [ tt ]ʷ ]ᵣ)} {.([ [ tt ]ʷ ]ᵣ • [ [ inj₂ Sn.swap ]ʷ ]ₗ)} (mid (comm (inj₂ Sn.swap) tt)) = by-equal-nf Eq.refl
      
      [_] : C ⊎ ⊤ -> Word B
      [_] = [_,_] [_]ₒ (λ v → ε)

      h=ract :  ∀ c y -> let (m' , c') = ract c y in let [_]ₓ  = (f *) in [ c ] • [ y ]ʷ ≈₂ [ m' ]ₓ • [ c' ]
      h=ract (inj₂ tt) (inj₁ tt) = by-equal-nf Eq.refl
      h=ract (inj₂ tt) (inj₂ (inj₁ Ki.K₀₁-gen)) = by-equal-nf Eq.refl
      h=ract (inj₂ tt) (inj₂ (inj₁ Ki.i₀-gen)) = by-equal-nf Eq.refl
      h=ract (inj₂ tt) (inj₂ (inj₁ Ki.i₁-gen)) = by-equal-nf Eq.refl
      h=ract (inj₂ tt) (inj₂ I) = by-equal-nf Eq.refl
      h=ract (inj₁ K01) (inj₁ tt) = by-equal-nf Eq.refl
      h=ract (inj₁ K01) (inj₂ (inj₁ Ki.K₀₁-gen)) = by-equal-nf Eq.refl
      h=ract (inj₁ K01) (inj₂ (inj₁ Ki.i₀-gen)) = by-equal-nf Eq.refl
      h=ract (inj₁ K01) (inj₂ (inj₁ Ki.i₁-gen)) = by-equal-nf Eq.refl
      h=ract (inj₁ K01) (inj₂ I) = by-equal-nf Eq.refl
      h=ract (inj₁ K01I0) (inj₁ tt) = by-equal-nf Eq.refl
      h=ract (inj₁ K01I0) (inj₂ (inj₁ Ki.K₀₁-gen)) = by-equal-nf Eq.refl
      h=ract (inj₁ K01I0) (inj₂ (inj₁ Ki.i₀-gen)) = by-equal-nf Eq.refl
      h=ract (inj₁ K01I0) (inj₂ (inj₁ Ki.i₁-gen)) = by-equal-nf Eq.refl
      h=ract (inj₁ K01I0) (inj₂ I) = by-equal-nf Eq.refl
      

    ad : AmalDataNF ((⊤ ⊎^ 2 ⊎ Sn.X 1) ⊎ ⊤) PD.pres Ki.pres'
    ad = record {
      P₀ = M.pres-M ;
      CA₁ = record
             { C = CA1.C
             ; f = CA1.f
             ; h = CA1.ract
             ; [_]ₒ = CA1.[_]ₒ
             ; hcme = CA1.hcme
             ; htme = CA1.htme
             ; htme~ = CA1.htme~
             ; hcme~ = CA1.hcme~
             ; h-wd-ax = CA1.h-wd-ax
             ; f-wd-ax = CA1.f-wd-ax
             ; h=ract = CA1.h=ract
             } ;
      CA₂ = record
             { C = CA2.C
             ; f = CA2.f
             ; h = CA2.ract
             ; [_]ₒ = CA2.[_]ₒ
             ; hcme = CA2.hcme
             ; htme = CA2.htme
             ; htme~ = CA2.htme~
             ; hcme~ = CA2.hcme~
             ; h-wd-ax = CA2.h-wd-ax
             ; f-wd-ax = CA2.f-wd-ax
             ; h=ract = CA2.h=ract
             } }
    
    module myANF = ANF PD.pres Ki.pres' ad

    nf = myANF.inv-nf ∘ myANF.nf

--    t : {!myANF!}
--    t = {!nf (K₀₁ • i₂ • X₁₂ • K₀₁ • i₂ • X₁₂ • K₀₁ • i₂ • X₁₂ • K₀₁)!}

  module Iso where
--    open Simplified
    open Amal

    open myANF using (nfp ; nfp') public

    pattern K₀₁ = [ inj₂ ( inj₂ (inj₁ Ki.K₀₁-gen)) ]ʷ
    pattern X₀₁ = [ inj₂ ( inj₁ tt) ]ʷ
    pattern i₀ = [ inj₂ ( inj₂ (inj₁ Ki.i₀-gen)) ]ʷ
    pattern i₁ = [ inj₂ ( inj₂ (inj₁ Ki.i₁-gen)) ]ʷ
    pattern i₂ = [ inj₂ ( inj₂ (inj₂ tt)) ]ʷ

    pattern X₀₁' = [  ( inj₁ (inj₂ Sn.swap)) ]ʷ
    pattern X₁₂ = [  ( inj₁ (inj₂ (Sn.swap Sn.ₛ))) ]ʷ
    pattern i₀' = [ inj₁ ( inj₁ ((inj₁ tt))) ]ʷ
    pattern i₁' = [ inj₁ ( inj₁ (inj₂ (inj₁ tt))) ]ʷ
    pattern i₂' = [ inj₁ ( inj₁ (inj₂ (inj₂ tt))) ]ʷ


    pattern K₀₁-gen = inj₂ ( inj₂ (inj₁ Ki.K₀₁-gen)) 
    pattern X₀₁-gen = inj₂ ( inj₁ tt) 
    pattern i₀-gen = inj₂ ( inj₂ (inj₁ Ki.i₀-gen)) 
    pattern i₁-gen = inj₂ ( inj₂ (inj₁ Ki.i₁-gen)) 
    pattern i₂-gen = inj₂ ( inj₂ (inj₂ tt)) 

    pattern X₀₁'-gen =  ( inj₁ (inj₂ Sn.swap)) 
    pattern X₁₂-gen =  ( inj₁ (inj₂ (Sn.swap Sn.ₛ))) 
    pattern i₀'-gen = inj₁ ( inj₁ ((inj₁ tt))) 
    pattern i₁'-gen = inj₁ ( inj₁ (inj₂ (inj₁ tt))) 
    pattern i₂'-gen = inj₁ ( inj₁ (inj₂ (inj₂ tt))) 


    f : Simplified.Gen -> Word (PD.Gen ⊎ Ki.FGen)
    f Simplified.i₀-gen =  [ PD.i₀ ]ₗ
    f Simplified.K₀₁-gen = [ Ki.fK₀₁ ]ᵣ
    f Simplified.X₀₁-gen = [ PD.X₀₁ ]ₗ
    f Simplified.X₁₂-gen = [ PD.X₁₂ ]ₗ

    module Sim = Simplified

    g : (PD.Gen ⊎ Ki.FGen) -> Word Simplified.Gen
    g K₀₁-gen = Sim.K₀₁
    g X₀₁-gen = Sim.X₀₁
    g i₀-gen = Sim.i₀
    g i₁-gen = Sim.i₁
    g i₂-gen = Sim.i₂

    g X₀₁'-gen = Sim.X₀₁
    g X₁₂-gen = Sim.X₁₂
    g i₀'-gen = Sim.i₀
    g i₁'-gen = Sim.i₁
    g i₂'-gen = Sim.i₂



    open myANF using (mypres)

    open PB mypres renaming (_===_ to _===₂_ ; _≈_ to _≈₂_) using ()
    
    open PB Sim._===_ renaming (_===_ to _===₁_ ; _≈_ to _≈₁_)
    open PP Sim._===_ renaming (by-assoc to by-assoc₁) using ()


    open import Algebra.Bundles using (Monoid)
    open import Algebra.Morphism.Structures using (module MonoidMorphisms)
    open PP Sim._===_ renaming (•-ε-monoid to m₁ ; word-setoid to ws₁)
    open PP mypres renaming (•-ε-monoid to m₂)

    open PP.NFProperty (myANF.nfp M.pres-M-nfp) using (by-equal-nf)
    
    open import Presentation.Morphism

    f-well-defined : ∀ {w v} -> w ===₁ v -> (f *) w ≈₂ (f *) v
    f-well-defined {w} {v} Simplified.[S1] = by-equal-nf Eq.refl
    f-well-defined {w} {v} Simplified.[S3a] = by-equal-nf Eq.refl
    f-well-defined {w} {v} Simplified.[S3b] = by-equal-nf Eq.refl
    f-well-defined {w} {v} Simplified.[S4a] = by-equal-nf Eq.refl
    f-well-defined {w} {v} Simplified.[S5a] = by-equal-nf Eq.refl
    f-well-defined {w} {v} Simplified.[S9a] = by-equal-nf Eq.refl
    f-well-defined {w} {v} Simplified.[S10] = by-equal-nf Eq.refl
    f-well-defined {w} {v} Simplified.[S11] = by-equal-nf Eq.refl
    f-well-defined {w} {v} Simplified.[S12] = by-equal-nf Eq.refl
    f-well-defined {w} {v} Simplified.[S14] = by-equal-nf Eq.refl
    f-well-defined {w} {v} Simplified.[S4b] = by-equal-nf Eq.refl
    

    g-well-defined : ∀ {w v} -> w ===₂ v -> (g *) w ≈₁ (g *) v
    g-well-defined {w} {v} (left (left (left Cyclic.order))) = _≈₁_.trans (_≈₁_.trans _≈₁_.assoc _≈₁_.assoc) (_≈₁_.axiom Sim.[S1])
    g-well-defined {w} {v} (left (left (right (left Cyclic.order)))) = claim
      where
      claim : (g *) (i₁ ^' 4) ≈₁ ε
      claim = begin
        (g *) (i₁ ^' 4) ≈⟨ by-assoc₁ Eq.refl ⟩
        Sim.X₀₁ • Sim.i₀ • (Sim.X₀₁ • Sim.X₀₁) • Sim.i₀ • (Sim.X₀₁ • Sim.X₀₁) • Sim.i₀ • (Sim.X₀₁ • Sim.X₀₁) • Sim.i₀ • Sim.X₀₁ ≈⟨ cong refl (cong refl (cong (axiom Sim.[S3a]) (cong refl (cong (axiom Sim.[S3a]) (cong refl (cong (axiom Sim.[S3a]) refl)))))) ⟩
        Sim.X₀₁ • Sim.i₀ • (ε) • Sim.i₀ • (ε) • Sim.i₀ • (ε) • Sim.i₀ • Sim.X₀₁ ≈⟨ by-assoc₁ Eq.refl ⟩
        Sim.X₀₁ • (Sim.i₀ ^ 4) • Sim.X₀₁ ≈⟨ cong refl (cong (axiom Sim.[S1]) refl) ⟩
        Sim.X₀₁ • (ε) • Sim.X₀₁ ≈⟨ cong refl left-unit ⟩
        Sim.X₀₁ • Sim.X₀₁ ≈⟨ axiom Sim.[S3a] ⟩
        ε ∎
        where open SR ws₁
        
    g-well-defined {w} {v} (left (left (right (right Cyclic.order)))) = claim
      where
      claim : (g *) (i₂ ^' 4) ≈₁ ε
      claim = begin
        (g *) (i₂ ^' 4) ≈⟨ by-assoc₁ Eq.refl ⟩
        (Sim.X₁₂ • Sim.X₀₁ • Sim.i₀ • Sim.X₀₁) • (Sim.X₁₂ • Sim.X₁₂) • (Sim.X₀₁ • Sim.i₀ • Sim.X₀₁) • (Sim.X₁₂ • Sim.X₁₂) • (Sim.X₀₁ • Sim.i₀ • Sim.X₀₁) • (Sim.X₁₂ • Sim.X₁₂) • Sim.X₀₁ • Sim.i₀ • Sim.X₀₁ • Sim.X₁₂ ≈⟨ cong refl (cong (axiom Sim.[S3b]) (cong refl (cong (axiom Sim.[S3b]) (cong refl (cong (axiom Sim.[S3b]) refl))))) ⟩
        (Sim.X₁₂ • Sim.X₀₁ • Sim.i₀ • Sim.X₀₁) • ε • (Sim.X₀₁ • Sim.i₀ • Sim.X₀₁) • ε • (Sim.X₀₁ • Sim.i₀ • Sim.X₀₁) • ε • Sim.X₀₁ • Sim.i₀ • Sim.X₀₁ • Sim.X₁₂ ≈⟨ by-assoc₁ Eq.refl ⟩
        Sim.X₁₂ • (g *) (i₁ ^' 4) • Sim.X₁₂ ≈⟨ cong refl (cong (g-well-defined (left (left (right (left Cyclic.order))))) refl) ⟩
        Sim.X₁₂ • ε • Sim.X₁₂ ≈⟨ by-assoc₁ Eq.refl ⟩
        Sim.X₁₂ • Sim.X₁₂ ≈⟨ axiom Sim.[S3b] ⟩
        ε ∎
        where open SR ws₁
    
    g-well-defined {w} {v} (left (left (right (mid (comm tt tt))))) = claim
      where
      claim : (g *) (i₁ • i₂) ≈₁ (g *) (i₂ • i₁)
      claim = begin
        (g *) (i₁ • i₂) ≈⟨ by-assoc₁ Eq.refl ⟩
        Sim.X₀₁ • Sim.i₀ • (Sim.X₀₁ • Sim.X₁₂ • Sim.X₀₁) • Sim.i₀ • Sim.X₀₁ • Sim.X₁₂ ≈⟨ cong refl (cong refl (cong (sym (axiom Sim.[S9a])) refl)) ⟩
        Sim.X₀₁ • Sim.i₀ • (Sim.X₁₂ • Sim.X₀₁ • Sim.X₁₂) • Sim.i₀ • Sim.X₀₁ • Sim.X₁₂ ≈⟨ cong refl (by-assoc₁ Eq.refl) ⟩
        Sim.X₀₁ • (Sim.i₀ • Sim.X₁₂) • Sim.X₀₁ • Sim.X₁₂ • Sim.i₀ • Sim.X₀₁ • Sim.X₁₂ ≈⟨ cong refl (cong (axiom Sim.[S5a]) refl) ⟩
        Sim.X₀₁ • (Sim.X₁₂ • Sim.i₀) • Sim.X₀₁ • Sim.X₁₂ • Sim.i₀ • Sim.X₀₁ • Sim.X₁₂ ≈⟨ by-assoc₁ Eq.refl ⟩
        (Sim.X₀₁ • Sim.X₁₂ • Sim.i₀ • Sim.X₀₁) • (Sim.X₁₂ • Sim.i₀) • Sim.X₀₁ • Sim.X₁₂ ≈⟨ cong refl (sym (cong (axiom Sim.[S5a]) refl)) ⟩
        (Sim.X₀₁ • Sim.X₁₂ • Sim.i₀ • Sim.X₀₁) • (Sim.i₀ • Sim.X₁₂) • Sim.X₀₁ • Sim.X₁₂ ≈⟨ trans (sym left-unit) (cong (sym (axiom Sim.[S3b])) refl) ⟩
        (Sim.X₁₂ • Sim.X₁₂) • (Sim.X₀₁ • Sim.X₁₂ • Sim.i₀ • Sim.X₀₁) • (Sim.i₀ • Sim.X₁₂) • Sim.X₀₁ • Sim.X₁₂ ≈⟨ by-assoc₁ Eq.refl ⟩
        Sim.X₁₂ • (Sim.X₁₂ • Sim.X₀₁ • Sim.X₁₂) • (Sim.i₀ • Sim.X₀₁) • (Sim.i₀ • Sim.X₁₂) • Sim.X₀₁ • Sim.X₁₂ ≈⟨ cong refl (cong (axiom Sim.[S9a]) refl) ⟩
        Sim.X₁₂ • (Sim.X₀₁ • Sim.X₁₂ • Sim.X₀₁) • (Sim.i₀ • Sim.X₀₁) • (Sim.i₀ • Sim.X₁₂) • Sim.X₀₁ • Sim.X₁₂ ≈⟨ by-assoc₁ Eq.refl ⟩
        (Sim.X₁₂ • Sim.X₀₁ • Sim.X₁₂) • ((Sim.X₀₁ • Sim.i₀ • Sim.X₀₁) • Sim.i₀) • Sim.X₁₂ • Sim.X₀₁ • Sim.X₁₂ ≈⟨ cong refl (cong (axiom Sim.[S4a]) refl) ⟩
        (Sim.X₁₂ • Sim.X₀₁ • Sim.X₁₂) • (Sim.i₀ • (Sim.X₀₁ • Sim.i₀ • Sim.X₀₁)) • Sim.X₁₂ • Sim.X₀₁ • Sim.X₁₂ ≈⟨ by-assoc₁ Eq.refl ⟩
        (Sim.X₁₂ • Sim.X₀₁) • (Sim.X₁₂ • Sim.i₀) • (Sim.X₀₁ • Sim.i₀ • Sim.X₀₁) • Sim.X₁₂ • Sim.X₀₁ • Sim.X₁₂ ≈⟨ cong refl (sym (cong (axiom Sim.[S5a]) refl)) ⟩
        (Sim.X₁₂ • Sim.X₀₁) • (Sim.i₀ • Sim.X₁₂) • (Sim.X₀₁ • Sim.i₀ • Sim.X₀₁) • Sim.X₁₂ • Sim.X₀₁ • Sim.X₁₂ ≈⟨ by-assoc₁ Eq.refl ⟩
        (Sim.X₁₂ • Sim.X₀₁ • Sim.i₀ • Sim.X₁₂ • Sim.X₀₁ • Sim.i₀) • (Sim.X₀₁ • Sim.X₁₂ • Sim.X₀₁) • Sim.X₁₂ ≈⟨ cong refl (sym (cong (axiom Sim.[S9a]) refl)) ⟩
        (Sim.X₁₂ • Sim.X₀₁ • Sim.i₀ • Sim.X₁₂ • Sim.X₀₁ • Sim.i₀) • (Sim.X₁₂ • Sim.X₀₁ • Sim.X₁₂) • Sim.X₁₂ ≈⟨ by-assoc₁ Eq.refl ⟩
        (Sim.X₁₂ • Sim.X₀₁ • Sim.i₀ • Sim.X₁₂ • Sim.X₀₁) • (Sim.i₀ • Sim.X₁₂) • Sim.X₀₁ • (Sim.X₁₂ • Sim.X₁₂) ≈⟨ cong refl (cong (axiom Sim.[S5a]) (cong refl (axiom Sim.[S3b]))) ⟩
        (Sim.X₁₂ • Sim.X₀₁ • Sim.i₀ • Sim.X₁₂ • Sim.X₀₁) • (Sim.X₁₂ • Sim.i₀) • Sim.X₀₁ • ε ≈⟨ by-assoc₁ Eq.refl ⟩
        (Sim.X₁₂ • Sim.X₀₁ • Sim.i₀) • (Sim.X₁₂ • Sim.X₀₁ • Sim.X₁₂) • Sim.i₀ • Sim.X₀₁ ≈⟨ cong refl (cong (axiom Sim.[S9a]) refl) ⟩
        (Sim.X₁₂ • Sim.X₀₁ • Sim.i₀) • (Sim.X₀₁ • Sim.X₁₂ • Sim.X₀₁) • Sim.i₀ • Sim.X₀₁ ≈⟨ by-assoc₁ Eq.refl ⟩
        Sim.X₁₂ • Sim.X₀₁ • Sim.i₀ • Sim.X₀₁ • Sim.X₁₂ • Sim.X₀₁ • Sim.i₀ • Sim.X₀₁ ≈⟨ by-assoc₁ Eq.refl ⟩
        (g *) (i₂ • i₁) ∎
        where open SR ws₁
        
    g-well-defined {w} {v} (left (left (mid (comm tt (inj₁ tt))))) = _≈₁_.sym (_≈₁_.axiom Sim.[S4a])
    g-well-defined {w} {v} (left (left (mid (comm tt (inj₂ tt))))) = claim
      where
      claim : (g *) (i₀ • i₂) ≈₁ (g *) (i₂ • i₀)
      claim = begin
        (g *) (i₀ • i₂) ≈⟨ by-assoc₁ Eq.refl ⟩
        (Sim.i₀ • Sim.X₁₂) • Sim.X₀₁ • Sim.i₀ • Sim.X₀₁ • Sim.X₁₂ ≈⟨ cong (axiom Sim.[S5a]) refl ⟩
        (Sim.X₁₂ • Sim.i₀) • Sim.X₀₁ • Sim.i₀ • Sim.X₀₁ • Sim.X₁₂ ≈⟨ by-assoc₁ Eq.refl ⟩
        Sim.X₁₂ • (Sim.i₀ • Sim.X₀₁ • Sim.i₀ • Sim.X₀₁) • Sim.X₁₂ ≈⟨ cong refl (cong (sym (axiom Sim.[S4a])) refl) ⟩
        Sim.X₁₂ • ((Sim.X₀₁ • Sim.i₀ • Sim.X₀₁) • Sim.i₀) • Sim.X₁₂ ≈⟨ by-assoc₁ Eq.refl ⟩
        (Sim.X₁₂ • Sim.X₀₁ • Sim.i₀ • Sim.X₀₁) • Sim.i₀ • Sim.X₁₂ ≈⟨ cong refl (axiom Sim.[S5a]) ⟩
        (Sim.X₁₂ • Sim.X₀₁ • Sim.i₀ • Sim.X₀₁) • Sim.X₁₂ • Sim.i₀ ≈⟨ by-assoc₁ Eq.refl ⟩
        (g *) (i₂ • i₀) ∎
        where open SR ws₁
        
    g-well-defined {w} {v} (left (right Sn.order)) = _≈₁_.axiom Sim.[S3a]
    g-well-defined {w} {v} (left (right Sn.yang-baxter)) = _≈₁_.sym (_≈₁_.axiom Sim.[S9a])
    g-well-defined {w} {v} (left (right (Sn.congₛ Sn.order))) = _≈₁_.axiom Sim.[S3b]
    g-well-defined {w} {v} (left (mid (comm (inj₁ tt) Sn.swap))) = trans (sym right-unit) (trans (cong refl (sym (axiom Sim.[S3a]))) (by-assoc₁ Eq.refl))
    g-well-defined {w} {v} (left (mid (comm (inj₁ tt) (Sn.swap Sn.ₛ)))) = _≈₁_.sym (_≈₁_.axiom Sim.[S5a])
    g-well-defined {w} {v} (left (mid (comm (inj₂ (inj₁ tt)) Sn.swap))) = claim
      where
      claim : (g *) [ [ inj₂ Sn.swap ]ʷ • [ inj₁ (inj₂ ( inj₁ tt)) ]ʷ ]ₗ ≈₁ (g *) [ [ [ inj₁ tt ]ʷ ]ₗ • [ inj₂ Sn.swap ]ʷ ]ₗ
      claim = begin
        (g *) [ [ inj₂ Sn.swap ]ʷ • [ inj₁ (inj₂ ( inj₁ tt)) ]ʷ ]ₗ ≈⟨ sym assoc ⟩
        (Sim.X₀₁ • Sim.X₀₁) • Sim.i₀ • Sim.X₀₁ ≈⟨ cong (axiom Sim.[S3a]) refl ⟩
        ε • Sim.i₀ • Sim.X₀₁ ≈⟨ left-unit ⟩
        (g *) [ [ [ inj₁ tt ]ʷ ]ₗ • [ inj₂ Sn.swap ]ʷ ]ₗ ∎
        where open SR ws₁
    
    g-well-defined {w} {v} (left (mid (comm (inj₂ (inj₂ tt)) Sn.swap))) = claim
      where
      claim : (g *) [ [ inj₂ Sn.swap ]ʷ • [ inj₁ (inj₂ (inj₂ tt)) ]ʷ ]ₗ ≈₁ (g *) [ [ [ inj₂ (inj₂ tt) ]ʷ ]ₗ • [ inj₂ Sn.swap ]ʷ ]ₗ
      claim = begin
        (g *) [ [ inj₂ Sn.swap ]ʷ • [ inj₁ (inj₂ (inj₂ tt)) ]ʷ ]ₗ ≈⟨ by-assoc₁ Eq.refl ⟩
        (Sim.X₀₁ • Sim.X₁₂ • Sim.X₀₁) • Sim.i₀ • Sim.X₀₁ • Sim.X₁₂ ≈⟨ cong (sym (axiom Sim.[S9a])) refl ⟩
        (Sim.X₁₂ • Sim.X₀₁ • Sim.X₁₂) • Sim.i₀ • Sim.X₀₁ • Sim.X₁₂ ≈⟨ by-assoc₁ Eq.refl ⟩
        (Sim.X₁₂ • Sim.X₀₁) • (Sim.X₁₂ • Sim.i₀) • Sim.X₀₁ • Sim.X₁₂ ≈⟨ cong refl (sym (cong (axiom Sim.[S5a]) refl)) ⟩
        (Sim.X₁₂ • Sim.X₀₁) • (Sim.i₀ • Sim.X₁₂) • Sim.X₀₁ • Sim.X₁₂ ≈⟨ by-assoc₁ Eq.refl ⟩
        (Sim.X₁₂ • Sim.X₀₁ • Sim.i₀) • Sim.X₁₂ • Sim.X₀₁ • Sim.X₁₂ ≈⟨ cong refl (axiom Sim.[S9a]) ⟩
        (Sim.X₁₂ • Sim.X₀₁ • Sim.i₀) • Sim.X₀₁ • Sim.X₁₂ • Sim.X₀₁ ≈⟨ by-assoc₁ Eq.refl ⟩
        Sim.X₁₂ • Sim.X₀₁ • Sim.i₀ • Sim.X₀₁ • Sim.X₁₂ • Sim.X₀₁ ≈⟨ by-assoc₁ Eq.refl ⟩
        (g *) [ [ [ inj₂ (inj₂ tt) ]ʷ ]ₗ • [ inj₂ Sn.swap ]ʷ ]ₗ ∎
        where open SR ws₁
        
    
    g-well-defined {w} {v} (left (mid (comm X₀₁-gen (Sn.swap Sn.ₛ)))) = claim
      where
      claim : (g *) [ [ inj₂ (Sn.swap Sn.ₛ) ]ʷ • [ inj₁ X₀₁-gen ]ʷ ]ₗ ≈₁ (g *) [ [ [ inj₂ (inj₂ tt) ]ʷ ]ₗ • [ inj₂ (Sn.swap Sn.ₛ) ]ʷ ]ₗ
      claim = begin
        (g *) [ [ inj₂ (Sn.swap Sn.ₛ) ]ʷ • [ inj₁ X₀₁-gen ]ʷ ]ₗ ≈⟨ by-assoc₁ Eq.refl ⟩
        (Sim.X₁₂ • Sim.X₀₁ • Sim.i₀ • Sim.X₀₁) • ε  ≈⟨ cong refl (sym (axiom Sim.[S3b])) ⟩
        (Sim.X₁₂ • Sim.X₀₁ • Sim.i₀ • Sim.X₀₁) • Sim.X₁₂ • Sim.X₁₂  ≈⟨ by-assoc₁ Eq.refl ⟩
        (g *) [ [ [ inj₂ (inj₂ tt) ]ʷ ]ₗ • [ inj₂ (Sn.swap Sn.ₛ) ]ʷ ]ₗ ∎
        where open SR ws₁
        
    g-well-defined {w} {v} (left (mid (comm (inj₂ (inj₂ tt)) (Sn.swap Sn.ₛ)))) = claim
      where
      claim : (g *) [ [ inj₂ (Sn.swap Sn.ₛ) ]ʷ • [ inj₁ (inj₂ (inj₂ tt)) ]ʷ ]ₗ ≈₁ (g *) [ [ X₀₁ ]ₗ • [ inj₂ (Sn.swap Sn.ₛ) ]ʷ ]ₗ
      claim = begin
        (g *) [ [ inj₂ (Sn.swap Sn.ₛ) ]ʷ • [ inj₁ (inj₂ (inj₂ tt)) ]ʷ ]ₗ ≈⟨ by-assoc₁ Eq.refl ⟩
        (Sim.X₁₂ • Sim.X₁₂) • Sim.X₀₁ • Sim.i₀ • Sim.X₀₁ • Sim.X₁₂  ≈⟨ cong (axiom Sim.[S3b]) refl ⟩
        ε • Sim.X₀₁ • Sim.i₀ • Sim.X₀₁ • Sim.X₁₂  ≈⟨ by-assoc₁ Eq.refl ⟩
        (g *) [ [ X₀₁ ]ₗ • [ inj₂ (Sn.swap Sn.ₛ) ]ʷ ]ₗ ∎
        where open SR ws₁
        
    g-well-defined {w} {v} (right (left Cyclic.order)) = _≈₁_.axiom Sim.[S3a]
    g-well-defined {w} {v} (right (right (left Ki.[S2a]))) = _≈₁_.axiom Sim.[S1]
    g-well-defined {w} {v} (right (right (left Ki.[S2b]))) = trans (by-assoc₁ Eq.refl) (g-well-defined (left (left (right (left Cyclic.order)))))
    g-well-defined {w} {v} (right (right (left Ki.[S4a]))) = _≈₁_.axiom Sim.[S4a]
    g-well-defined {w} {v} (right (right (left Ki.[S10]))) = claim0
      where
      open SR ws₁
      claim : Sim.X₀₁ ≈₁ (Sim.K₀₁ • Sim.i₁ • Sim.i₁) • Sim.K₀₁ • Sim.i₀ • Sim.i₁
      claim = begin
        Sim.X₀₁ ≈⟨ sym right-unit ⟩
        Sim.X₀₁ • ε ≈⟨ cong refl (sym (axiom Sim.[S14])) ⟩
        Sim.X₀₁ • Sim.K₀₁ ^ 2 • Sim.i₀ • Sim.i₁ ≈⟨ by-assoc₁ Eq.refl ⟩
        (Sim.X₀₁ • Sim.K₀₁) • Sim.K₀₁ • Sim.i₀ • Sim.i₁ ≈⟨ cong (sym (axiom Sim.[S10])) refl ⟩
        (Sim.K₀₁ • Sim.i₁ • Sim.i₁) • Sim.K₀₁ • Sim.i₀ • Sim.i₁ ∎


      claim2 : Sim.K₀₁ • Sim.i₀ • Sim.i₀ • Sim.K₀₁ • (Sim.i₀ • Sim.i₁) ^ 3 ≈₁ Sim.X₀₁ 
      claim2 = begin
        Sim.K₀₁ • Sim.i₀ • Sim.i₀ • Sim.K₀₁ • (Sim.i₀ • Sim.i₁) ^ 3 ≈⟨ by-assoc₁ Eq.refl ⟩
        (Sim.K₀₁ • Sim.i₀ • Sim.i₀) • (Sim.K₀₁ • Sim.i₀ • Sim.i₁) • (Sim.i₀ • Sim.i₁) ^ 2 ≈⟨ cong refl (cong (axiom Sim.[S12]) refl) ⟩
        (Sim.K₀₁ • Sim.i₀ • Sim.i₀) • (Sim.i₀ • Sim.i₁ • Sim.K₀₁) • (Sim.i₀ • Sim.i₁) ^ 2 ≈⟨ by-assoc₁ Eq.refl ⟩
        (Sim.K₀₁ • Sim.i₀ • Sim.i₀ • Sim.i₀ • Sim.i₁) • (Sim.K₀₁ • Sim.i₀ • Sim.i₁) • Sim.i₀ • Sim.i₁ ≈⟨ cong refl (cong (axiom Sim.[S12]) refl) ⟩
        (Sim.K₀₁ • Sim.i₀ • Sim.i₀ • Sim.i₀ • Sim.i₁) • (Sim.i₀ • Sim.i₁ • Sim.K₀₁) • Sim.i₀ • Sim.i₁ ≈⟨ by-assoc₁ Eq.refl ⟩
        (Sim.K₀₁ • Sim.i₀ • Sim.i₀ • Sim.i₀) • (Sim.i₁ • Sim.i₀) • Sim.i₁ • Sim.K₀₁ • Sim.i₀ • Sim.i₁ ≈⟨ cong refl (cong (axiom Sim.[S4a]) refl) ⟩
        (Sim.K₀₁ • Sim.i₀ • Sim.i₀ • Sim.i₀) • (Sim.i₀ • Sim.i₁) • Sim.i₁ • Sim.K₀₁ • Sim.i₀ • Sim.i₁ ≈⟨ by-assoc₁ Eq.refl ⟩
        Sim.K₀₁ • Sim.i₀ ^ 4 • Sim.i₁ • Sim.i₁ • Sim.K₀₁ • Sim.i₀ • Sim.i₁ ≈⟨ cong refl (cong (axiom Sim.[S1]) refl) ⟩
        Sim.K₀₁ • ε • Sim.i₁ • Sim.i₁ • Sim.K₀₁ • Sim.i₀ • Sim.i₁ ≈⟨ by-assoc₁ Eq.refl ⟩
        (Sim.K₀₁ • Sim.i₁ • Sim.i₁) • Sim.K₀₁ • Sim.i₀ • Sim.i₁ ≈⟨ sym claim ⟩
        Sim.X₀₁ ∎

      c1 : (Sim.i₀ • Sim.i₁) ^ 4 ≈₁ ε
      c1 = Sim.by-sub-nf {(Sim.i₀' • Sim.i₁') ^ 4} {ε} (Sim.by-equal-nf Eq.refl)
      
      comm-aux : ∀ {a b} -> a • b ≈₁ b • a -> (n : ℕ) -> a • b ^ n ≈₁ b ^ n • a
      comm-aux {a} {b} eq zero = trans right-unit (sym left-unit)
      comm-aux {a} {b} eq (suc zero) = eq
      comm-aux {a} {b} eq (suc (suc n)) = begin
        a • b • b ^ suc n ≈⟨ sym assoc ⟩
        (a • b) • b ^ suc n ≈⟨ cong eq refl ⟩
        (b • a) • b ^ suc n ≈⟨ assoc ⟩
        b • a • b ^ suc n ≈⟨ cong refl (comm-aux eq (suc n)) ⟩
        b • b ^ suc n • a ≈⟨ sym assoc ⟩
        (b • b ^ suc n) • a ∎

      claim0 : (g *) [ [ [ Ki.K₀₁ • Ki.i₀ • Ki.i₀ • Ki.K₀₁ • Ki.i₁ ]ₗ ]ᵣ ]ᵣ ≈₁ (g *) [ [ [ Ki.i₀ • Ki.K₀₁ • Ki.i₀ • Ki.i₀ • Ki.K₀₁ ]ₗ ]ᵣ ]ᵣ
      claim0 = begin
        (g *) [ [ [ Ki.K₀₁ • Ki.i₀ • Ki.i₀ • Ki.K₀₁ • Ki.i₁ ]ₗ ]ᵣ ]ᵣ ≈⟨ trans (sym right-unit) (cong refl (sym c1)) ⟩
        (Sim.K₀₁ • Sim.i₀ • Sim.i₀ • Sim.K₀₁ • Sim.i₁) • (Sim.i₀ • Sim.i₁) ^ 4 ≈⟨ by-assoc₁ Eq.refl ⟩
        (Sim.K₀₁ • Sim.i₀ • Sim.i₀ • Sim.K₀₁) • Sim.i₁ • (Sim.i₀ • Sim.i₁) ^ 4 ≈⟨ cong refl (Sim.by-sub-nf {Sim.i₁' • (Sim.i₀' • Sim.i₁') ^ 4} {(Sim.i₀' • Sim.i₁') ^ 3 • Sim.i₀' • Sim.i₁' • Sim.i₁'} (Sim.by-equal-nf Eq.refl)) ⟩
        (Sim.K₀₁ • Sim.i₀ • Sim.i₀ • Sim.K₀₁) • (Sim.i₀ • Sim.i₁) ^ 3 • Sim.i₀ • Sim.i₁ • Sim.i₁ ≈⟨ by-assoc₁ Eq.refl ⟩
        (Sim.K₀₁ • Sim.i₀ • Sim.i₀ • Sim.K₀₁ • (Sim.i₀ • Sim.i₁) ^ 3) • Sim.i₀ • Sim.i₁ • Sim.i₁ ≈⟨ cong claim2 refl ⟩
        Sim.X₀₁ • Sim.i₀ • Sim.i₁ • Sim.i₁ ≈⟨ by-assoc₁ Eq.refl ⟩
        Sim.X₀₁ • (Sim.i₀ • Sim.i₁) • Sim.i₁ ≈⟨ cong refl (cong (sym (axiom Sim.[S4a])) refl) ⟩
        Sim.X₀₁ • (Sim.i₁ • Sim.i₀) • Sim.i₁ ≈⟨ by-assoc₁ Eq.refl ⟩
        (Sim.X₀₁ • Sim.i₁) • Sim.i₀ • Sim.i₁ ≈⟨ cong (trans (sym assoc) (trans (cong (axiom Sim.[S3a]) refl) (left-unit))) refl ⟩
        (Sim.i₀ • Sim.X₀₁) • Sim.i₀ • Sim.i₁ ≈⟨ cong (cong refl (sym claim2)) refl ⟩
        (Sim.i₀ • (Sim.K₀₁ • Sim.i₀ • Sim.i₀ • Sim.K₀₁ • (Sim.i₀ • Sim.i₁) ^ 3)) • Sim.i₀ • Sim.i₁ ≈⟨ by-assoc₁ Eq.refl ⟩
        (Sim.i₀ • Sim.K₀₁ • Sim.i₀ • Sim.i₀ • Sim.K₀₁) • (Sim.i₀ • Sim.i₁) ^ 4 ≈⟨ cong refl c1 ⟩
        (Sim.i₀ • Sim.K₀₁ • Sim.i₀ • Sim.i₀ • Sim.K₀₁) • ε ≈⟨ by-assoc₁ Eq.refl ⟩


        (g *) [ [ [ Ki.i₀ • Ki.K₀₁ • Ki.i₀ • Ki.i₀ • Ki.K₀₁ ]ₗ ]ᵣ ]ᵣ ∎

    g-well-defined {w} {v} (right (right (left Ki.[S10b]))) = claim0
      where
      open SR ws₁
      claim : Sim.X₀₁ ≈₁ (Sim.K₀₁ • Sim.i₁ • Sim.i₁) • Sim.K₀₁ • Sim.i₀ • Sim.i₁
      claim = begin
        Sim.X₀₁ ≈⟨ sym right-unit ⟩
        Sim.X₀₁ • ε ≈⟨ cong refl (sym (axiom Sim.[S14])) ⟩
        Sim.X₀₁ • Sim.K₀₁ ^ 2 • Sim.i₀ • Sim.i₁ ≈⟨ by-assoc₁ Eq.refl ⟩
        (Sim.X₀₁ • Sim.K₀₁) • Sim.K₀₁ • Sim.i₀ • Sim.i₁ ≈⟨ cong (sym (axiom Sim.[S10])) refl ⟩
        (Sim.K₀₁ • Sim.i₁ • Sim.i₁) • Sim.K₀₁ • Sim.i₀ • Sim.i₁ ∎


      claim2 : Sim.K₀₁ • Sim.i₀ • Sim.i₀ • Sim.K₀₁ • (Sim.i₀ • Sim.i₁) ^ 3 ≈₁ Sim.X₀₁ 
      claim2 = begin
        Sim.K₀₁ • Sim.i₀ • Sim.i₀ • Sim.K₀₁ • (Sim.i₀ • Sim.i₁) ^ 3 ≈⟨ by-assoc₁ Eq.refl ⟩
        (Sim.K₀₁ • Sim.i₀ • Sim.i₀) • (Sim.K₀₁ • Sim.i₀ • Sim.i₁) • (Sim.i₀ • Sim.i₁) ^ 2 ≈⟨ cong refl (cong (axiom Sim.[S12]) refl) ⟩
        (Sim.K₀₁ • Sim.i₀ • Sim.i₀) • (Sim.i₀ • Sim.i₁ • Sim.K₀₁) • (Sim.i₀ • Sim.i₁) ^ 2 ≈⟨ by-assoc₁ Eq.refl ⟩
        (Sim.K₀₁ • Sim.i₀ • Sim.i₀ • Sim.i₀ • Sim.i₁) • (Sim.K₀₁ • Sim.i₀ • Sim.i₁) • Sim.i₀ • Sim.i₁ ≈⟨ cong refl (cong (axiom Sim.[S12]) refl) ⟩
        (Sim.K₀₁ • Sim.i₀ • Sim.i₀ • Sim.i₀ • Sim.i₁) • (Sim.i₀ • Sim.i₁ • Sim.K₀₁) • Sim.i₀ • Sim.i₁ ≈⟨ by-assoc₁ Eq.refl ⟩
        (Sim.K₀₁ • Sim.i₀ • Sim.i₀ • Sim.i₀) • (Sim.i₁ • Sim.i₀) • Sim.i₁ • Sim.K₀₁ • Sim.i₀ • Sim.i₁ ≈⟨ cong refl (cong (axiom Sim.[S4a]) refl) ⟩
        (Sim.K₀₁ • Sim.i₀ • Sim.i₀ • Sim.i₀) • (Sim.i₀ • Sim.i₁) • Sim.i₁ • Sim.K₀₁ • Sim.i₀ • Sim.i₁ ≈⟨ by-assoc₁ Eq.refl ⟩
        Sim.K₀₁ • Sim.i₀ ^ 4 • Sim.i₁ • Sim.i₁ • Sim.K₀₁ • Sim.i₀ • Sim.i₁ ≈⟨ cong refl (cong (axiom Sim.[S1]) refl) ⟩
        Sim.K₀₁ • ε • Sim.i₁ • Sim.i₁ • Sim.K₀₁ • Sim.i₀ • Sim.i₁ ≈⟨ by-assoc₁ Eq.refl ⟩
        (Sim.K₀₁ • Sim.i₁ • Sim.i₁) • Sim.K₀₁ • Sim.i₀ • Sim.i₁ ≈⟨ sym claim ⟩
        Sim.X₀₁ ∎

      c1 : (Sim.i₀ • Sim.i₁) ^ 4 ≈₁ ε
      c1 = Sim.by-sub-nf {(Sim.i₀' • Sim.i₁') ^ 4} {ε} (Sim.by-equal-nf Eq.refl)
      
      comm-aux : ∀ {a b} -> a • b ≈₁ b • a -> (n : ℕ) -> a • b ^ n ≈₁ b ^ n • a
      comm-aux {a} {b} eq zero = trans right-unit (sym left-unit)
      comm-aux {a} {b} eq (suc zero) = eq
      comm-aux {a} {b} eq (suc (suc n)) = begin
        a • b • b ^ suc n ≈⟨ sym assoc ⟩
        (a • b) • b ^ suc n ≈⟨ cong eq refl ⟩
        (b • a) • b ^ suc n ≈⟨ assoc ⟩
        b • a • b ^ suc n ≈⟨ cong refl (comm-aux eq (suc n)) ⟩
        b • b ^ suc n • a ≈⟨ sym assoc ⟩
        (b • b ^ suc n) • a ∎

      claim0 : (g *) [ [ [ Ki.K₀₁ • Ki.i₀ • Ki.i₀ • Ki.K₀₁ • Ki.i₀ ]ₗ ]ᵣ ]ᵣ ≈₁ (g *) [ [ [ Ki.i₁ • Ki.K₀₁ • Ki.i₀ • Ki.i₀ • Ki.K₀₁ ]ₗ ]ᵣ ]ᵣ
      claim0 = begin
        (g *) [ [ [ Ki.K₀₁ • Ki.i₀ • Ki.i₀ • Ki.K₀₁ • Ki.i₀ ]ₗ ]ᵣ ]ᵣ ≈⟨ trans (sym right-unit) (cong refl (sym c1)) ⟩
        (Sim.K₀₁ • Sim.i₀ • Sim.i₀ • Sim.K₀₁ • Sim.i₀) • (Sim.i₀ • Sim.i₁) ^ 4 ≈⟨ by-assoc₁ Eq.refl ⟩
        (Sim.K₀₁ • Sim.i₀ • Sim.i₀ • Sim.K₀₁) • Sim.i₀ • (Sim.i₀ • Sim.i₁) ^ 4 ≈⟨ cong refl (Sim.by-sub-nf {Sim.i₀' • (Sim.i₀' • Sim.i₁') ^ 4} {(Sim.i₀' • Sim.i₁') ^ 3 • Sim.i₀' • Sim.i₀' • Sim.i₁'} (Sim.by-equal-nf Eq.refl)) ⟩
        (Sim.K₀₁ • Sim.i₀ • Sim.i₀ • Sim.K₀₁) • (Sim.i₀ • Sim.i₁) ^ 3 • Sim.i₀ • Sim.i₀ • Sim.i₁ ≈⟨ by-assoc₁ Eq.refl ⟩
        (Sim.K₀₁ • Sim.i₀ • Sim.i₀ • Sim.K₀₁ • (Sim.i₀ • Sim.i₁) ^ 3) • Sim.i₀ • Sim.i₀ • Sim.i₁ ≈⟨ cong claim2 refl ⟩
        Sim.X₀₁ • Sim.i₀ • Sim.i₀ • Sim.i₁ ≈⟨ by-assoc₁ Eq.refl ⟩
        (Sim.X₀₁ • Sim.i₀) • Sim.i₀ • Sim.i₁ ≈⟨ cong (sym (trans (trans (trans (cong (sym assoc) refl) assoc) (cong refl (axiom Sim.[S3a]))) right-unit)) refl ⟩
        (Sim.i₁ • Sim.X₀₁) • Sim.i₀ • Sim.i₁ ≈⟨ cong (cong refl (sym claim2)) refl ⟩
        (Sim.i₁ • (Sim.K₀₁ • Sim.i₀ • Sim.i₀ • Sim.K₀₁ • (Sim.i₀ • Sim.i₁) ^ 3)) • Sim.i₀ • Sim.i₁ ≈⟨ by-assoc₁ Eq.refl ⟩
        (Sim.i₁ • Sim.K₀₁ • Sim.i₀ • Sim.i₀ • Sim.K₀₁) • (Sim.i₀ • Sim.i₁) ^ 4 ≈⟨ cong refl c1 ⟩
        (Sim.i₁ • Sim.K₀₁ • Sim.i₀ • Sim.i₀ • Sim.K₀₁) • ε ≈⟨ by-assoc₁ Eq.refl ⟩
        (g *) [ [ [ Ki.i₁ • Ki.K₀₁ • Ki.i₀ • Ki.i₀ • Ki.K₀₁ ]ₗ ]ᵣ ]ᵣ ∎
        
    g-well-defined {w} {v} (right (right (left Ki.[S11]))) = _≈₁_.axiom Sim.[S11]
    g-well-defined {w} {v} (right (right (left Ki.[S12]))) = _≈₁_.axiom Sim.[S12]
    g-well-defined {w} {v} (right (right (left Ki.[S14]))) = _≈₁_.axiom Sim.[S14]
    g-well-defined {w} {v} (right (right (right Cyclic.order))) = trans (by-assoc₁ Eq.refl) claim
      where
      claim : (g *) (i₂ ^' 4) ≈₁ ε
      claim = begin
        (g *) (i₂ ^' 4) ≈⟨ by-assoc₁ Eq.refl ⟩
        (Sim.X₁₂ • Sim.X₀₁ • Sim.i₀ • Sim.X₀₁) • (Sim.X₁₂ • Sim.X₁₂) • (Sim.X₀₁ • Sim.i₀ • Sim.X₀₁) • (Sim.X₁₂ • Sim.X₁₂) • (Sim.X₀₁ • Sim.i₀ • Sim.X₀₁) • (Sim.X₁₂ • Sim.X₁₂) • Sim.X₀₁ • Sim.i₀ • Sim.X₀₁ • Sim.X₁₂ ≈⟨ cong refl (cong (axiom Sim.[S3b]) (cong refl (cong (axiom Sim.[S3b]) (cong refl (cong (axiom Sim.[S3b]) refl))))) ⟩
        (Sim.X₁₂ • Sim.X₀₁ • Sim.i₀ • Sim.X₀₁) • ε • (Sim.X₀₁ • Sim.i₀ • Sim.X₀₁) • ε • (Sim.X₀₁ • Sim.i₀ • Sim.X₀₁) • ε • Sim.X₀₁ • Sim.i₀ • Sim.X₀₁ • Sim.X₁₂ ≈⟨ by-assoc₁ Eq.refl ⟩
        Sim.X₁₂ • (g *) (i₁ ^' 4) • Sim.X₁₂ ≈⟨ cong refl (cong (g-well-defined (left (left (right (left Cyclic.order))))) refl) ⟩
        Sim.X₁₂ • ε • Sim.X₁₂ ≈⟨ by-assoc₁ Eq.refl ⟩
        Sim.X₁₂ • Sim.X₁₂ ≈⟨ axiom Sim.[S3b] ⟩
        ε ∎
        where open SR ws₁
    
    g-well-defined {w} {v} (right (right (mid (comm Ki.K₀₁-gen tt)))) = _≈₁_.sym (_≈₁_.axiom Sim.[S4b])
    g-well-defined {w} {v} (right (right (mid (comm Ki.i₀-gen tt)))) = g-well-defined (left (left (mid (comm tt (inj₂ tt)))))
    g-well-defined {w} {v} (right (right (mid (comm Ki.i₁-gen tt)))) = g-well-defined (left (left (right (mid (comm tt tt)))))
    g-well-defined {w} {v} (right (mid (desugar {tt}))) = claim
      where
      claim : (g *) [ [ inj₁ tt ]ʷ ]ᵣ ≈₁ (g *) [ [ Ki.fs tt ]ᵣ ]ᵣ
      claim = begin
        Sim.X₀₁ ≈⟨ sym right-unit ⟩
        Sim.X₀₁ • ε ≈⟨ cong refl (sym (axiom Sim.[S14])) ⟩
        Sim.X₀₁ • Sim.K₀₁ ^ 2 • Sim.i₀ • Sim.i₁ ≈⟨ by-assoc₁ Eq.refl ⟩
        (Sim.X₀₁ • Sim.K₀₁) • Sim.K₀₁ • Sim.i₀ • Sim.i₁ ≈⟨ cong (sym (axiom Sim.[S10])) refl ⟩
        (Sim.K₀₁ • Sim.i₁ • Sim.i₁) • Sim.K₀₁ • Sim.i₀ • Sim.i₁ ≈⟨ by-assoc₁ Eq.refl ⟩
        (g *) [ [ Ki.fs tt ]ᵣ ]ᵣ ∎
        where open SR ws₁
        
    g-well-defined {w} {v} (mid (amal {i₀'-gen})) = _≈₁_.refl
    g-well-defined {w} {v} (mid (amal {inj₁ (inj₁ (inj₂ tt))})) = _≈₁_.refl
    g-well-defined {w} {v} (mid (amal {X₀₁'-gen})) = _≈₁_.refl
    g-well-defined {w} {v} (mid (amal {inj₂ tt})) = _≈₁_.refl


    f-left-inv-gen : ∀ x -> [ x ]ʷ ≈₂ (f *) (g x)
    f-left-inv-gen K₀₁-gen = _≈₂_.refl
    f-left-inv-gen X₀₁-gen = by-equal-nf Eq.refl
    f-left-inv-gen i₀-gen = by-equal-nf Eq.refl
    f-left-inv-gen i₁-gen = by-equal-nf Eq.refl
    f-left-inv-gen i₂-gen = by-equal-nf Eq.refl

    f-left-inv-gen X₀₁'-gen = _≈₂_.refl
    f-left-inv-gen X₁₂-gen = _≈₂_.refl
    f-left-inv-gen i₀'-gen = _≈₂_.refl
    f-left-inv-gen i₁'-gen = by-equal-nf Eq.refl
    f-left-inv-gen i₂'-gen = by-equal-nf Eq.refl

    g-left-inv-gen : ∀ x -> [ x ]ʷ ≈₁ (g *) (f x)
    g-left-inv-gen Simplified.i₀-gen = refl
    g-left-inv-gen Simplified.K₀₁-gen = refl
    g-left-inv-gen Simplified.X₀₁-gen = refl
    g-left-inv-gen Simplified.X₁₂-gen = refl

    open MonoidMorphisms 

    Theorem-U33Di-iso-B*A⋆⋆ : IsMonoidIsomorphism (Monoid.rawMonoid m₂) (Monoid.rawMonoid m₁) (g *)
    Theorem-U33Di-iso-B*A⋆⋆ = StarIsomorphism.isMonoidIsomorphism mypres _===₁_ g f g-well-defined g-left-inv-gen f-well-defined f-left-inv-gen


