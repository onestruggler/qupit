{-# OPTIONS --allow-unsolved-metas #-}
-- {-# OPTIONS  --safe #-}
{-# OPTIONS --termination-depth=4 #-}
open import Level using (0ℓ)

open import Relation.Binary using (Rel)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Binary.Morphism.Definitions using (Homomorphic₂)
open import Relation.Binary.PropositionalEquality using (_≡_ ; _≢_ ; inspect ; setoid ; module ≡-Reasoning) renaming ([_] to [_]')
import Relation.Binary.Reasoning.Setoid as SR
import Relation.Binary.PropositionalEquality as Eq
open import Relation.Nullary.Decidable using (yes ; no)


open import Function using (_∘_ ; id)
open import Function.Definitions using (Injective)

open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂ ; map₁ ; ∃ ; Σ ; Σ-syntax)

open import Data.Product.Relation.Binary.Pointwise.NonDependent as PW using (≡×≡⇒≡ ; Pointwise ; ≡⇒≡×≡)
open import Data.Nat hiding (_^_ ; _*_ ; _+_)
open import Agda.Builtin.Nat using (_-_)
import Data.Nat as Nat
open import Data.Fin hiding (_+_ ; _≤_)
open import Data.Bool hiding (_≤_)
open import Data.List hiding ([_])

open import Data.Maybe
open import Data.Sum using (_⊎_ ; inj₁ ; inj₂ ; [_,_])
open import Data.Unit using (⊤ ; tt)
open import Data.Empty using (⊥ ; ⊥-elim)

open import Word.Base as WB hiding (wfoldl)
open import Word.Properties
import Presentation.Base as PB
import Presentation.Properties as PP
open PP using (NFProperty ; NFProperty')
import Presentation.CosetNF as CA
import Presentation.Reidemeister-Schreier as RS
module RSF = RS.Star-Injective-Full.Reidemeister-Schreier-Full

open import Presentation.Construct.Base hiding (_*_)
import Presentation.Construct.Properties.SemiDirectProduct2 as SDP2
import Presentation.Construct.Properties.DirectProduct as DP
import Presentation.Groups.Cyclic as Cyclic
open import Presentation.Tactics hiding ([_])

open import Data.Fin.Properties using (suc-injective ; toℕ-inject₁ ; toℕ-fromℕ)
import Data.Nat.Properties as NP
open import Presentation.GroupLike
import N.Symplectic as NS
open import Data.Nat.Primality

open import Zp.ModularArithmetic
open import Zp.Fermats-little-theorem


module N.Clifford.Iso
  (p-3 : ℕ)
  (let p-2 = suc p-3)
  (p-prime : Prime (suc (suc p-2)))
  (let open PrimeModulus' p-2 p-prime)
  (g*@(g , g≠0) : ℤ* ₚ)
  (g-gen : ∀ ((x , _) : ℤ* ₚ) -> ∃ \ (k : ℤ ₚ-₁) -> x ≡ g ^′ toℕ k )
  where


open import N.Clifford.SDProduct p-3 p-prime g* g-gen
open import N.Clifford.Clifford-Lemmas p-3 p-prime g* g-gen hiding (module CL ; module CLb)
pattern ₀ = zero
pattern ₁ = suc ₀
pattern ₂ = suc ₁

pattern ₁₊ ⱼ = suc ⱼ
pattern ₂₊ ⱼ = suc (suc ⱼ)
pattern ₃₊ ⱼ = suc (suc (suc ⱼ))

import N.Symplectic p-2 p-prime as NSym
import N.Symplectic-Simplified p-2 p-prime g* g-gen as NSim
--module Sym = NSym.Symplectic
--module Sim = NSim.Simplified-Relations
import N.XZ p-2 p-prime as XZ


{-  

{-
  open PB Sim._===_ renaming (_===_ to _===₂_ ; _≈_ to _≈₂_) using ()
  open PP Sim._===_ renaming (•-ε-monoid to m₂ ; word-setoid to ws₂) using ()
  
  open PB XZ._===_ renaming (_===_ to _===₁_ ; _≈_ to _≈₁_) using ()
  open PP XZ._===_ renaming (•-ε-monoid to m₁ ; word-setoid to ws₁ ; by-assoc-and to by-assoc-and₁ ; by-assoc to by-assoc₁) using ()
-}

  open PB hiding (_===_)


  hyph :
    let
    open PB (Sim._QRel,_===_ n) renaming (_===_ to _===₂_ ; _≈_ to _≈₂_) using ()
    open PB (XZ._QRel,_===_ n) renaming (_===_ to _===₁_ ; _≈_ to _≈₁_) using ()
    in
    
    ∀ {c d} n -> c ===₂ d -> (conj ʰ') c n ≈₁ (conj ʰ') d n

  hyph {c} {d} [ XZ.X-gen ]ʷ Sim.order-S = {!!}
  hyph {c} {d} [ XZ.Z-gen ]ʷ Sim.order-S = {!!}
  hyph {c} {d} [ (x XZ.↥) ]ʷ Sim.order-S = {!!}
  hyph {c} {d} [ x ]ʷ Sim.order-H = {!!}
  hyph {c} {d} [ x ]ʷ (Sim.M-power k) = {!!}
  hyph {c} {d} [ x ]ʷ Sim.semi-MS = {!!}
  hyph {c} {d} [ x ]ʷ Sim.semi-M↑CZ = {!!}
  hyph {c} {d} [ x ]ʷ Sim.semi-M↓CZ = {!!}
  hyph {c} {d} [ x ]ʷ Sim.order-CZ = {!!}
  hyph {c} {d} [ x ]ʷ Sim.comm-CZ-S↓ = {!!}
  hyph {c} {d} [ x ]ʷ Sim.comm-CZ-S↑ = {!!}
  hyph {c} {d} [ x ]ʷ Sim.selinger-c10 = {!!}
  hyph {c} {d} [ x ]ʷ Sim.selinger-c11 = {!!}
  hyph {c} {d} [ x ]ʷ Sim.selinger-c12 = {!!}
  hyph {c} {d} [ x ]ʷ Sim.selinger-c13 = {!!}
  hyph {c} {d} [ x ]ʷ Sim.selinger-c14 = {!!}
  hyph {c} {d} [ x ]ʷ Sim.selinger-c15 = {!!}
  hyph {c} {d} [ x ]ʷ Sim.comm-H = {!!}
  hyph {c} {d} [ x ]ʷ Sim.comm-S = {!!}
  hyph {c} {d} [ x ]ʷ Sim.comm-CZ = {!!}
  hyph {c} {d} [ x ]ʷ (Sim.cong↑ ax) = {!!}
  hyph {c} {d} ε ax = {!!}
  hyph {c} {d} (n • n₁) ax = {!!}


  hypn :
    let
    open PB (Sim._QRel,_===_ n) renaming (_===_ to _===₂_ ; _≈_ to _≈₂_) using ()
    open PB (XZ._QRel,_===_ n) renaming (_===_ to _===₁_ ; _≈_ to _≈₁_) using ()
    in
  
    ∀ c {w v} -> w ===₁ v -> (conj ⁿ') c w ≈₁ (conj ⁿ') c v
  hypn Sym.H-gen XZ.order-X = {!!}
  hypn Sym.H-gen XZ.order-Z = {!!}
  hypn Sym.H-gen XZ.comm-Z-X = {!!}
  hypn Sym.H-gen XZ.comm-X = {!!}
  hypn Sym.H-gen XZ.comm-Z = {!!}
  hypn Sym.H-gen (XZ.cong↑ ax) = {!!}
  hypn Sym.S-gen XZ.order-X = {!!}
  hypn Sym.S-gen XZ.order-Z = {!!}
  hypn Sym.S-gen XZ.comm-Z-X = {!!}
  hypn Sym.S-gen XZ.comm-X = {!!}
  hypn Sym.S-gen XZ.comm-Z = {!!}
  hypn Sym.S-gen (XZ.cong↑ ax) = {!!}
  hypn Sym.CZ-gen XZ.order-X = {!!}
  hypn Sym.CZ-gen XZ.order-Z = {!!}
  hypn Sym.CZ-gen XZ.comm-Z-X = {!!}
  hypn Sym.CZ-gen XZ.comm-X = {!!}
  hypn Sym.CZ-gen XZ.comm-Z = {!!}
  hypn Sym.CZ-gen (XZ.cong↑ ax) = {!!}
  hypn (c Sym.↥) XZ.order-X = {!!}
  hypn (c Sym.↥) XZ.order-Z = {!!}
  hypn (c Sym.↥) XZ.comm-Z-X = {!!}
  hypn (c Sym.↥) XZ.comm-X = {!!}
  hypn (c Sym.↥) XZ.comm-Z = {!!}
  hypn (c Sym.↥) (XZ.cong↑ ax) = {!!}


  nfp' : (n : ℕ) -> NFProperty' (n QRel,_===_)
  nfp' n = SDP2.NFP'.nfp' (XZ._QRel,_===_  n) (Sim._QRel,_===_ n) (conj {n}) (hyph {n}) (hypn {n}) {!!} {!!}


-}

module Iso (n : ℕ) where

  open import N.Clifford.Clifford-Mod-Scalar p-3 p-prime g* g-gen as Cli

  module Clifford = Clifford-Relations
--  open Clifford-Lemmas

--  open import Presentation.Morphism SemiDirect._===_ Clifford-Relations._===_
--  open GroupMorphs SemiDirect.grouplike Clifford-GroupLike.grouplike


  f : ∀ {n} -> SemiDirect.Gen n -> Word (Gen n)
  f SemiDirect.X-gen = Clifford.X
  f SemiDirect.Z-gen = Clifford.Z
  f SemiDirect.H-gen = Cli.H
  f SemiDirect.S-gen = Clifford.𝑠
  f SemiDirect.CZ-gen = Cli.CZ
  f {₁₊ n} (inj₁ (x XZ.↥)) = f (inj₁ x) ↑
  f {₁₊ n} (inj₂ (y NS.Symplectic.↥)) = f (inj₂ y) ↑

  h : ∀ {n} -> Cli.Gen n -> Word (SemiDirect.Gen n)
  h Cli.H-gen = SemiDirect.H
  h Cli.S-gen = SemiDirect.Z^ -1/2 • SemiDirect.S
  h Cli.CZ-gen = SemiDirect.CZ
  h (x Cli.↥) = (h x) SemiDirect.↑

{-

  
  

  open Clifford-Powers renaming (general-powers to general-powers₂)
  open Commuting-Clifford

  open PP SemiDirect._===_ renaming (by-assoc-and to by-assoc-and₁)
  open PP Clifford._===_ renaming (by-assoc-and to by-assoc-and₂ ; word-setoid to ws₂ ; by-assoc to by-assoc₂)

  open PB hiding (_===_)
  open Clifford


  import One.Clifford-Mod-Scalar as OC
  import Two.Clifford-Mod-Scalar as TC
  module O = OC.Clifford
  module OL = OC.Clifford-Lemmas
  open Clifford-Powers
  open Clifford-Rewriting
  open TC.Clifford-Duality
  open OC.Clifford-Lemmas2
  open Clifford-Lemmas2a
  open OC.Clifford-Lemmas
--  open PP.NFProperty' Clifford-NFP'.nfp' renaming (by-equal-nf to by-equal-nf₂)
-}


  module SD = SemiDirect
  module CL = Lemmas1
  module CLb = Lemmas1b
  open import Presentation.Construct.Properties


  f-M : ∀ {n} x -> (f *) (SD.M {n = n} x) ≡ Clifford.M x
  f-M {n} x' = begin
    (f *) (SD.S^ x • SD.H • SD.S^ x⁻¹ • SD.H • SD.S^ x • SD.H) ≡⟨ Eq.cong₂ _•_ (lemma-f*-w^n (toℕ x)) (Eq.cong₂ _•_ auto (Eq.cong₂ _•_ (lemma-f*-w^n (toℕ x⁻¹)) (Eq.cong₂ _•_ auto (Eq.cong₂ _•_ (lemma-f*-w^n (toℕ x)) auto)))) ⟩
    Clifford.𝑠^ x • Cli.H • Clifford.𝑠^ x⁻¹ • Cli.H • Clifford.𝑠^ x • Cli.H ≡⟨ auto ⟩
    Clifford.M x' ∎
    where
    open ≡-Reasoning
    x = x' .proj₁
    x⁻¹ = ((x' ⁻¹) .proj₁ )


  f-M' : ∀ {n} x -> (f *) [  Sym.M {n = n} x ]ᵣ ≡ Clifford.M x
  f-M' {n} x' = begin
    (f *) [ Sym.M x' ]ᵣ ≡⟨ Eq.cong (\ z -> (f *) (z • [ Sym.H • Sym.S^ x⁻¹ • Sym.H • Sym.S^ x • Sym.H ]ᵣ)) (lemma-[w^n]ᵣ=[w]ᵣ^n Sym.S (toℕ x)) ⟩
    (f *) (SD.S^ x • [ Sym.H • Sym.S^ x⁻¹ • Sym.H • Sym.S^ x • Sym.H ]ᵣ) ≡⟨  auto ⟩
    (f *) (SD.S^ x • SD.H • [ Sym.S^ x⁻¹ • Sym.H • Sym.S^ x • Sym.H ]ᵣ) ≡⟨ Eq.cong
                                                                            (λ z → (f *) (SD.S^ x • SD.H • z • [ Sym.H • Sym.S^ x • Sym.H ]ᵣ))
                                                                            (lemma-[w^n]ᵣ=[w]ᵣ^n Sym.S (toℕ x⁻¹)) ⟩
    (f *) (SD.S^ x • SD.H • SD.S^ x⁻¹ • [ Sym.H • Sym.S^ x • Sym.H ]ᵣ) ≡⟨ Eq.cong (\ z -> (f *) (SD.S^ x • SD.H • SD.S^ x⁻¹ • SD.H • z • SD.H)) (lemma-[w^n]ᵣ=[w]ᵣ^n Sym.S (toℕ x)) ⟩
    (f *) (SD.S^ x • SD.H • SD.S^ x⁻¹ • SD.H • SD.S^ x • SD.H) ≡⟨ f-M x' ⟩
    Clifford.M x' ∎
    where
    open ≡-Reasoning
    x = x' .proj₁
    x⁻¹ = ((x' ⁻¹) .proj₁ )


  lemma-f*-[w]ᵣ : ∀ {n} {w : Word (Sym.Gen n)} -> (f *) [ w Sym.↑ ]ᵣ ≡ (f *) [ w ]ᵣ ↑
  lemma-f*-[w]ᵣ {n} {[ x ]ʷ} = auto
  lemma-f*-[w]ᵣ {n} {ε} = auto
  lemma-f*-[w]ᵣ {n} {w • w₁} rewrite lemma-f*-[w]ᵣ {w = w} | lemma-f*-[w]ᵣ {w = w₁} = auto

  lemma-[]ₗ-↑' : ∀ {n} (w : Word (XZ.Gen n)) -> SD._↑ {n} ([_]ₗ {B = Sym.Gen n} w) ≡ [_]ₗ {B = Sym.Gen (suc n)} (w XZ.↑)
  lemma-[]ₗ-↑' {n} [ x ]ʷ = auto
  lemma-[]ₗ-↑' {n} ε = auto
  lemma-[]ₗ-↑' {n} (w • w₁) rewrite lemma-[]ₗ-↑' w | lemma-[]ₗ-↑' w₁ = auto

  lemma-f*-SD↑ : ∀ {n} (w : Word (SemiDirect.Gen n)) -> (f *) (SD._↑ {n} w) ≡ ((f *) w) ↑
  lemma-f*-SD↑ {n} [ inj₁ x ]ʷ = auto
  lemma-f*-SD↑ {n} [ inj₂ y ]ʷ = auto
  lemma-f*-SD↑ {n} ε = auto
  lemma-f*-SD↑ {n} (w • w₁) rewrite lemma-f*-SD↑ w | lemma-f*-SD↑ w₁ = auto

  lemma-f*-^ᵣ : ∀ {n} (w : Word (Sym.Gen n)) k -> (f *) ([ w ^ k ]ᵣ) ≡ ((f *) [ w ]ᵣ) ^ k
  lemma-f*-^ᵣ w k = Eq.trans (Eq.cong (f *) (lemma-[w^n]ᵣ=[w]ᵣ^n w k)) (lemma-f*-w^n k)

  lemma-f*-^ₗ : ∀ {n} (w : Word (XZ.Gen n)) k -> (f *) ([ w ^ k ]ₗ) ≡ ((f *) [ w ]ₗ) ^ k
  lemma-f*-^ₗ w k = Eq.trans (Eq.cong (f *) (lemma-[w^n]ₗ=[w]ₗ^n w k)) (lemma-f*-w^n k)


  lemma-f*-S⁻¹↑ : ∀ {n} -> (f *) ([ (S {n} ^ p-1) Sym.↑ ]ᵣ) ≡ Clifford.𝑠 ↑ ^ p-1
  lemma-f*-S⁻¹↑ {n} = begin
    (f *) ([ (S ^ p-1) Sym.↑ ]ᵣ) ≡⟨ lemma-f*-[w]ᵣ {w = S ^ p-1} ⟩
    (f *) ([ S ^ p-1 ]ᵣ) ↑ ≡⟨ Eq.cong _↑ (lemma-f*-^ᵣ S p-1) ⟩
    (Clifford.𝑠 ^ p-1) ↑ ≡⟨ Lemmas-Clifford.lemma-↑^ p-1 Clifford.𝑠 ⟩
    Clifford.𝑠 ↑ ^ p-1 ∎
    where open ≡-Reasoning


  f-well-defined : ∀ {n w v} ->
    let
      open PB (n SemiDirect.QRel,_===_) renaming (_===_ to _===₁_ ; _≈_ to _≈₁_) using ()
      open PB (n Clifford.QRel,_===_) renaming (_===_ to _===₂_ ; _≈_ to _≈₂_ ; cleft_ to cleft₂_ ; cright_ to cright₂_) using ()
    in
    w ===₁ v -> (f *) w ≈₂ (f *) v

  f-well-defined {n@(suc n')} (SD.order-X) = begin
    (f *) ([ XZ.X ^ p ]ₗ) ≡⟨ Eq.cong (f *) (lemma-[w^n]ₗ=[w]ₗ^n XZ.X p) ⟩
    (f *) ([ XZ.X ]ₗ ^ p) ≡⟨ lemma-f*-w^n p ⟩
    ((f *) [ XZ.X ]ₗ) ^ p ≈⟨ CL.lemma-order-X n' ⟩
    ε ∎
    where
    open PB (n Clifford.QRel,_===_) renaming (_===_ to _===₂_ ; _≈_ to _≈₂_ ; cleft_ to cleft₂_ ; cright_ to cright₂_) using (refl')
    open PP (n Clifford.QRel,_===_)
    open SR word-setoid

  f-well-defined {n@(suc n')} (SD.order-Z) = begin
    (f *) ([ XZ.Z ^ p ]ₗ) ≡⟨ Eq.cong (f *) (lemma-[w^n]ₗ=[w]ₗ^n XZ.Z p) ⟩
    (f *) ([ XZ.Z ]ₗ ^ p) ≡⟨ lemma-f*-w^n p ⟩
    ((f *) [ XZ.Z ]ₗ) ^ p ≈⟨ CL.lemma-order-Z n' ⟩
    ε ∎
    where
    open PB (n Clifford.QRel,_===_) renaming (_===_ to _===₂_ ; _≈_ to _≈₂_ ; cleft_ to cleft₂_ ; cright_ to cright₂_) using (refl')
    open PP (n Clifford.QRel,_===_)
    open SR word-setoid
  f-well-defined (SD.comm-Z-X) = PB.sym (PB.axiom Clifford._QRel,_===_.comm-X-Z)
  f-well-defined {n@(suc n')} (left (XZ.comm-X {g = g})) = begin
    (f *) ([ [ g XZ.↥ ]ʷ • XZ.X ]ₗ) ≡⟨ auto ⟩
    (f *) ([ [ g XZ.↥ ]ʷ ]ₗ) • (f *) ([ XZ.X ]ₗ) ≡⟨ auto ⟩
    (f *) ([ [ g XZ.↥ ]ʷ ]ₗ) • Clifford.X ≈⟨ sym₂ (Lemmas-Clifford.lemma-comm-X-w↑ (f (inj₁ g))) ⟩
    Clifford.X • (f *) ([ [ g XZ.↥ ]ʷ ]ₗ) ≡⟨ auto ⟩
    (f *) ([ XZ.X • [ g XZ.↥ ]ʷ ]ₗ) ∎
    where
    open PB (n Clifford.QRel,_===_) renaming (_===_ to _===₂_ ; _≈_ to _≈₂_ ; cleft_ to cleft₂_ ; cright_ to cright₂_ ; sym to sym₂) using (refl')
    open PP (n Clifford.QRel,_===_)
    open SR word-setoid
  f-well-defined {n@(suc n')} (left (XZ.comm-Z {g = g})) = begin
    (f *) ([ [ g XZ.↥ ]ʷ • XZ.Z ]ₗ) ≡⟨ auto ⟩
    (f *) ([ [ g XZ.↥ ]ʷ ]ₗ) • (f *) ([ XZ.Z ]ₗ) ≡⟨ auto ⟩
    (f *) ([ [ g XZ.↥ ]ʷ ]ₗ) • Clifford.Z ≈⟨ sym₂ (Lemmas-Clifford.lemma-comm-Z-w↑ (f (inj₁ g))) ⟩
    Clifford.Z • (f *) ([ [ g XZ.↥ ]ʷ ]ₗ) ≡⟨ auto ⟩
    (f *) ([ XZ.Z • [ g XZ.↥ ]ʷ ]ₗ) ∎
    where
    open PB (n Clifford.QRel,_===_) renaming (_===_ to _===₂_ ; _≈_ to _≈₂_ ; cleft_ to cleft₂_ ; cright_ to cright₂_ ; sym to sym₂) using (refl')
    open PP (n Clifford.QRel,_===_)
    open SR word-setoid
  f-well-defined {n@(suc (n'@(suc n'')))} (left (XZ.cong↑ {w = w} {v} x)) = begin
    (f *) ([ w XZ.↑ ]ₗ) ≡⟨ lemma-f*-[w]ₗ {w = w} ⟩
    (f *) ([ w ]ₗ) ↑ ≈⟨ Lemmas-Clifford.lemma-cong↑ ((f *) ([ w ]ₗ)) ((f *) ([ v ]ₗ)) (f-well-defined (left x)) ⟩
    (f *) ([ v ]ₗ) ↑ ≡⟨ Eq.sym (lemma-f*-[w]ₗ {w = v}) ⟩
    (f *) ([ v XZ.↑ ]ₗ) ∎
    where
    open PB (n Clifford.QRel,_===_) renaming (_===_ to _===₂_ ; _≈_ to _≈₂_ ; cleft_ to cleft₂_ ; cright_ to cright₂_ ; sym to sym₂) using (refl')
    open PP (n Clifford.QRel,_===_)
    open SR word-setoid

    lemma-f*-[w]ₗ : ∀ {n} {w : Word (XZ.Gen (n))} -> (f *) [ w XZ.↑ ]ₗ ≡ (f *) [ w ]ₗ ↑
    lemma-f*-[w]ₗ {n} {[ x ]ʷ} = auto
    lemma-f*-[w]ₗ {n} {ε} = auto
    lemma-f*-[w]ₗ {n} {w • w₁} rewrite lemma-f*-[w]ₗ {w = w} | lemma-f*-[w]ₗ {w = w₁} = auto

  f-well-defined {n@(suc n')} (right Sim.order-S) = begin
    (f *) ([ S ^ p ]ᵣ) ≡⟨ Eq.cong (f *) (lemma-[w^n]ᵣ=[w]ᵣ^n S p) ⟩
    (f *) ([ S ]ᵣ ^ p) ≡⟨ lemma-f*-w^n p ⟩
    ((f *) [ S ]ᵣ) ^ p ≈⟨ CL.lemma-order-𝑠 n' ⟩
    ε ∎
    where
    open PB (n Clifford.QRel,_===_) renaming (_===_ to _===₂_ ; _≈_ to _≈₂_ ; cleft_ to cleft₂_ ; cright_ to cright₂_) using (refl')
    open PP (n Clifford.QRel,_===_)
    open SR word-setoid
  
  f-well-defined {n@(suc n')} (right Sim.order-H) = begin
    (f *) ([ H ^ 2 ]ᵣ) ≡⟨ auto ⟩
    Cli.H ^ 2 ≈⟨ _≈₂_.axiom Clifford._QRel,_===_.order-H ⟩
    Clifford.M₋₁ ≡⟨ Eq.sym (f-M' -'₁) ⟩
    (f *) [ Sim.M₋₁ ]ᵣ ∎
    where
    open PB (n Clifford.QRel,_===_) renaming (_===_ to _===₂_ ; _≈_ to _≈₂_ ; cleft_ to cleft₂_ ; cright_ to cright₂_) using (refl')
    open PP (n Clifford.QRel,_===_)
    open SR word-setoid
 
  f-well-defined {n@(suc n')} (right (Sim.M-power k)) =  begin
    (f *) ([ Sim.Mg^ k ]ᵣ) ≡⟨ Eq.cong (f *) (lemma-[w^n]ᵣ=[w]ᵣ^n Sim.Mg (toℕ k)) ⟩
    (f *) ([ Sim.Mg ]ᵣ ^ toℕ k) ≡⟨ lemma-f*-w^n (toℕ k) ⟩
    (f *) [ Sim.Mg ]ᵣ ^ toℕ k ≡⟨ Eq.cong (_^ toℕ k) (f-M' g*) ⟩
    Clifford.M g* ^ toℕ k ≈⟨ _≈₂_.axiom (Clifford._QRel,_===_.M-power k) ⟩
    Clifford.M (g^ k) ≡⟨ Eq.sym (f-M' (g^ k)) ⟩
    (f *) [ Sym.M (g^ k) ]ᵣ ∎
    where
    open PB (n Clifford.QRel,_===_) renaming (_===_ to _===₂_ ; _≈_ to _≈₂_ ; cleft_ to cleft₂_ ; cright_ to cright₂_) using (refl')
    open PP (n Clifford.QRel,_===_)
    open SR word-setoid
    open Primitive-Root-Modp' g* g-gen
    
  f-well-defined {n@(suc n')} (right Sim.semi-MS) = begin
    (f *) ([ Sim.Mg • S ]ᵣ) ≡⟨ auto ⟩
    (f *) [ Sim.Mg ]ᵣ • (f *) [ S ]ᵣ ≡⟨ Eq.cong (_• (f *) [ S ]ᵣ) (f-M' g*) ⟩
    Clifford.M g* • (f *) [ S ]ᵣ ≈⟨ _≈₂_.axiom Clifford._QRel,_===_.semi-M𝑠 ⟩
    Clifford.𝑠^ (g * g) • Clifford.M g* ≡⟨ Eq.cong (Clifford.𝑠^ (g * g) •_) (Eq.sym (f-M' g*)) ⟩
    Clifford.𝑠^ (g * g) • (f *) [ Sim.Mg ]ᵣ ≡⟨ Eq.cong (_• (f *) [ Sim.Mg ]ᵣ) (Eq.sym (lemma-f*-^ᵣ S (toℕ (g * g)))) ⟩
    (f *) ([ S ^ toℕ (g * g) ]ᵣ) • (f *) [ Sim.Mg ]ᵣ ≡⟨ auto ⟩
    (f *) ([ S^ (g * g) • Sim.Mg ]ᵣ) ∎
    where
    open PB (n Clifford.QRel,_===_) renaming (_===_ to _===₂_ ; _≈_ to _≈₂_ ; cleft_ to cleft₂_ ; cright_ to cright₂_) using (refl')
    open PP (n Clifford.QRel,_===_)
    open SR word-setoid

  f-well-defined {n@(suc (n'@(suc n'')))} (right Sim.semi-M↑CZ) = begin
    (f *) ([ Sim.Mg ↑ • CZ ]ᵣ) ≡⟨ auto ⟩
    (f *) [ Sim.Mg ↑ ]ᵣ • Cli.CZ ≡⟨ Eq.cong (_• Cli.CZ) (lemma-f*-[w]ᵣ {w = Sim.Mg}) ⟩
    (f *) [ Sim.Mg ]ᵣ ↑ • Cli.CZ ≡⟨ Eq.cong (\ x -> x ↑ • Cli.CZ) (f-M' g*) ⟩
    Clifford.M g* ↑ • Cli.CZ ≈⟨ _≈₂_.axiom Clifford._QRel,_===_.semi-M↑CZ ⟩
    CZ^ g • Clifford.M g* ↑ ≡⟨ Eq.cong (\ x -> CZ^ g • x ↑) (Eq.sym (f-M' g*)) ⟩
    CZ^ g • (f *) [ Sim.Mg ]ᵣ ↑ ≡⟨ Eq.cong (CZ^ g •_) (Eq.sym (lemma-f*-[w]ᵣ {w = Sim.Mg})) ⟩
    CZ^ g • (f *) [ Sim.Mg ↑ ]ᵣ ≡⟨ Eq.cong (_• (f *) [ Sim.Mg ↑ ]ᵣ) (Eq.sym (lemma-f*-^ᵣ CZ (toℕ g))) ⟩
    (f *) ([ CZ ^ toℕ g ]ᵣ) • (f *) [ Sim.Mg ↑ ]ᵣ ≡⟨ auto ⟩
    (f *) ([ CZ^ g • Sim.Mg ↑ ]ᵣ) ∎
    where
    open PB (n Clifford.QRel,_===_) renaming (_===_ to _===₂_ ; _≈_ to _≈₂_ ; cleft_ to cleft₂_ ; cright_ to cright₂_) using (refl')
    open PP (n Clifford.QRel,_===_)
    open SR word-setoid

  f-well-defined {n@(suc (n'@(suc n'')))} (right Sim.semi-M↓CZ) = begin
    (f *) ([ Sim.Mg • CZ ]ᵣ) ≡⟨ auto ⟩
    (f *) [ Sim.Mg ]ᵣ • Cli.CZ ≡⟨ Eq.cong (_• Cli.CZ) (f-M' g*) ⟩
    Clifford.M g* • Cli.CZ ≈⟨ _≈₂_.axiom Clifford._QRel,_===_.semi-M↓CZ ⟩
    CZ^ g • Clifford.M g* ≡⟨ Eq.cong (CZ^ g •_) (Eq.sym (f-M' g*)) ⟩
    CZ^ g • (f *) [ Sim.Mg ]ᵣ ≡⟨ Eq.cong (_• (f *) [ Sim.Mg ]ᵣ) (Eq.sym (lemma-f*-^ᵣ CZ (toℕ g))) ⟩
    (f *) ([ CZ ^ toℕ g ]ᵣ) • (f *) [ Sim.Mg ]ᵣ ≡⟨ auto ⟩
    (f *) ([ CZ^ g • Sim.Mg ]ᵣ) ∎
    where
    open PB (n Clifford.QRel,_===_) renaming (_===_ to _===₂_ ; _≈_ to _≈₂_ ; cleft_ to cleft₂_ ; cright_ to cright₂_) using (refl')
    open PP (n Clifford.QRel,_===_)
    open SR word-setoid
  f-well-defined {n@(suc (n'@(suc n'')))} (right Sim.order-CZ) = begin
    (f *) ([ CZ ^ p ]ᵣ) ≡⟨ Eq.cong (f *) (lemma-[w^n]ᵣ=[w]ᵣ^n CZ p) ⟩
    (f *) ([ CZ ]ᵣ ^ p) ≡⟨ lemma-f*-w^n p ⟩
    ((f *) [ CZ ]ᵣ) ^ p ≈⟨ _≈₂_.axiom Clifford._QRel,_===_.order-CZ ⟩
    ε ∎
    where
    open PB (n Clifford.QRel,_===_) renaming (_===_ to _===₂_ ; _≈_ to _≈₂_ ; cleft_ to cleft₂_ ; cright_ to cright₂_) using (refl')
    open PP (n Clifford.QRel,_===_)
    open SR word-setoid
  f-well-defined {n} (right Sim.comm-CZ-S↓) = begin
    (f *) ([ CZ • S ]ᵣ) ≡⟨ auto ⟩
    Cli.CZ • Clifford.𝑠 ≈⟨ sym₂ lemma-comm-𝑠-CZ ⟩
    Clifford.𝑠 • Cli.CZ ≡⟨ auto ⟩
    (f *) ([ S • CZ ]ᵣ) ∎
    where
    open PB (n Clifford.QRel,_===_) renaming (_===_ to _===₂_ ; _≈_ to _≈₂_ ; cleft_ to cleft₂_ ; cright_ to cright₂_ ; sym to sym₂) using (refl')
    open PP (n Clifford.QRel,_===_)
    open SR word-setoid
  f-well-defined {n} (right Sim.comm-CZ-S↑) = begin
    (f *) ([ CZ • S Sym.↑ ]ᵣ) ≡⟨ Eq.cong (\ x -> Cli.CZ • x) (lemma-f*-[w]ᵣ {w = S}) ⟩
    Cli.CZ • Clifford.𝑠 ↑ ≈⟨ sym₂ lemma-comm-𝑠↑-CZ ⟩
    Clifford.𝑠 ↑ • Cli.CZ ≡⟨ Eq.cong (\ x -> x • Cli.CZ) (Eq.sym (lemma-f*-[w]ᵣ {w = S})) ⟩
    (f *) ([ S Sym.↑ • CZ ]ᵣ) ∎
    where
    open PB (n Clifford.QRel,_===_) renaming (_===_ to _===₂_ ; _≈_ to _≈₂_ ; cleft_ to cleft₂_ ; cright_ to cright₂_ ; sym to sym₂) using (refl')
    open PP (n Clifford.QRel,_===_)
    open SR word-setoid
  f-well-defined {n} (right Sim.selinger-c10) = begin
    (f *) ([ CZ • H Sym.↑ • CZ ]ᵣ) ≡⟨ auto ⟩
    Cli.CZ • Cli.H ↑ • Cli.CZ ≈⟨ _≈₂_.axiom Clifford._QRel,_===_.selinger-c10 ⟩
    Clifford.𝑠 ↑ ^ p-1 • Cli.H ↑ • Clifford.𝑠 ↑ ^ p-1 • Cli.CZ • Cli.H ↑ • Clifford.𝑠 ↑ ^ p-1 • Clifford.𝑠 ^ p-1
      ≡⟨ Eq.cong (\ x -> x • Cli.H ↑ • Clifford.𝑠 ↑ ^ p-1 • Cli.CZ • Cli.H ↑ • Clifford.𝑠 ↑ ^ p-1 • Clifford.𝑠 ^ p-1) (Eq.sym lemma-f*-S⁻¹↑) ⟩
    (f *) ([ (S ^ p-1) Sym.↑ ]ᵣ) • Cli.H ↑ • Clifford.𝑠 ↑ ^ p-1 • Cli.CZ • Cli.H ↑ • Clifford.𝑠 ↑ ^ p-1 • Clifford.𝑠 ^ p-1
      ≡⟨ Eq.cong (\ x -> (f *) ([ (S ^ p-1) Sym.↑ ]ᵣ) • Cli.H ↑ • x • Cli.CZ • Cli.H ↑ • Clifford.𝑠 ↑ ^ p-1 • Clifford.𝑠 ^ p-1) (Eq.sym lemma-f*-S⁻¹↑) ⟩
    (f *) ([ (S ^ p-1) Sym.↑ ]ᵣ) • Cli.H ↑ • (f *) ([ (S ^ p-1) Sym.↑ ]ᵣ) • Cli.CZ • Cli.H ↑ • Clifford.𝑠 ↑ ^ p-1 • Clifford.𝑠 ^ p-1
      ≡⟨ Eq.cong (\ x -> (f *) ([ (S ^ p-1) Sym.↑ ]ᵣ) • Cli.H ↑ • (f *) ([ (S ^ p-1) Sym.↑ ]ᵣ) • Cli.CZ • Cli.H ↑ • x • Clifford.𝑠 ^ p-1) (Eq.sym lemma-f*-S⁻¹↑) ⟩
    (f *) ([ (S ^ p-1) Sym.↑ ]ᵣ) • Cli.H ↑ • (f *) ([ (S ^ p-1) Sym.↑ ]ᵣ) • Cli.CZ • Cli.H ↑ • (f *) ([ (S ^ p-1) Sym.↑ ]ᵣ) • Clifford.𝑠 ^ p-1
      ≡⟨ Eq.cong (\ x -> (f *) ([ (S ^ p-1) Sym.↑ ]ᵣ) • Cli.H ↑ • (f *) ([ (S ^ p-1) Sym.↑ ]ᵣ) • Cli.CZ • Cli.H ↑ • (f *) ([ (S ^ p-1) Sym.↑ ]ᵣ) • x) (Eq.sym (lemma-f*-^ᵣ S p-1)) ⟩
    (f *) ([ (S ^ p-1) Sym.↑ ]ᵣ) • Cli.H ↑ • (f *) ([ (S ^ p-1) Sym.↑ ]ᵣ) • Cli.CZ • Cli.H ↑ • (f *) ([ (S ^ p-1) Sym.↑ ]ᵣ) • (f *) ([ S ^ p-1 ]ᵣ)
      ≡⟨ auto ⟩
    (f *) ([ (S ^ p-1) Sym.↑ • H Sym.↑ • (S ^ p-1) Sym.↑ • CZ • H Sym.↑ • (S ^ p-1) Sym.↑ • S ^ p-1 ]ᵣ) ∎
    where
    open PB (n Clifford.QRel,_===_) renaming (_===_ to _===₂_ ; _≈_ to _≈₂_ ; cleft_ to cleft₂_ ; cright_ to cright₂_) using (refl')
    open PP (n Clifford.QRel,_===_)
    open SR word-setoid
  f-well-defined {n} (right Sim.selinger-c11) = begin
    (f *) ([ CZ • H • CZ ]ᵣ) ≡⟨ auto ⟩
    Cli.CZ • Cli.H • Cli.CZ ≈⟨ _≈₂_.axiom Clifford._QRel,_===_.selinger-c11 ⟩
    Clifford.𝑠 ^ p-1 • Cli.H • Clifford.𝑠 ^ p-1 • Cli.CZ • Cli.H • Clifford.𝑠 ^ p-1 • Clifford.𝑠 ↑ ^ p-1
      ≡⟨ Eq.cong (\ x -> x • Cli.H • Clifford.𝑠 ^ p-1 • Cli.CZ • Cli.H • Clifford.𝑠 ^ p-1 • Clifford.𝑠 ↑ ^ p-1) (Eq.sym (lemma-f*-^ᵣ S p-1)) ⟩
    (f *) ([ S ^ p-1 ]ᵣ) • Cli.H • Clifford.𝑠 ^ p-1 • Cli.CZ • Cli.H • Clifford.𝑠 ^ p-1 • Clifford.𝑠 ↑ ^ p-1
      ≡⟨ Eq.cong (\ x -> (f *) ([ S ^ p-1 ]ᵣ) • Cli.H • x • Cli.CZ • Cli.H • Clifford.𝑠 ^ p-1 • Clifford.𝑠 ↑ ^ p-1) (Eq.sym (lemma-f*-^ᵣ S p-1)) ⟩
    (f *) ([ S ^ p-1 ]ᵣ) • Cli.H • (f *) ([ S ^ p-1 ]ᵣ) • Cli.CZ • Cli.H • Clifford.𝑠 ^ p-1 • Clifford.𝑠 ↑ ^ p-1
      ≡⟨ Eq.cong (\ x -> (f *) ([ S ^ p-1 ]ᵣ) • Cli.H • (f *) ([ S ^ p-1 ]ᵣ) • Cli.CZ • Cli.H • x • Clifford.𝑠 ↑ ^ p-1) (Eq.sym (lemma-f*-^ᵣ S p-1)) ⟩
    (f *) ([ S ^ p-1 ]ᵣ) • Cli.H • (f *) ([ S ^ p-1 ]ᵣ) • Cli.CZ • Cli.H • (f *) ([ S ^ p-1 ]ᵣ) • Clifford.𝑠 ↑ ^ p-1
      ≡⟨ Eq.cong (\ x -> (f *) ([ S ^ p-1 ]ᵣ) • Cli.H • (f *) ([ S ^ p-1 ]ᵣ) • Cli.CZ • Cli.H • (f *) ([ S ^ p-1 ]ᵣ) • x) (Eq.sym lemma-f*-S⁻¹↑) ⟩
    (f *) ([ S ^ p-1 ]ᵣ) • Cli.H • (f *) ([ S ^ p-1 ]ᵣ) • Cli.CZ • Cli.H • (f *) ([ S ^ p-1 ]ᵣ) • (f *) ([ (S ^ p-1) Sym.↑ ]ᵣ)
      ≡⟨ auto ⟩
    (f *) ([ S ^ p-1 • H • S ^ p-1 • CZ • H • S ^ p-1 • (S ^ p-1) Sym.↑ ]ᵣ) ∎
    where
    open PB (n Clifford.QRel,_===_) renaming (_===_ to _===₂_ ; _≈_ to _≈₂_ ; cleft_ to cleft₂_ ; cright_ to cright₂_) using (refl')
    open PP (n Clifford.QRel,_===_)
    open SR word-setoid
  f-well-defined {n} (right Sim.selinger-c12) = begin
    (f *) ([ CZ ↑ • CZ ]ᵣ) ≡⟨ auto ⟩
    Cli.CZ ↑ • Cli.CZ ≈⟨ _≈₂_.axiom Clifford._QRel,_===_.selinger-c12 ⟩
    Cli.CZ • Cli.CZ ↑ ≡⟨ auto ⟩
    (f *) ([ CZ • CZ ↑ ]ᵣ) ∎
    where
    open PB (n Clifford.QRel,_===_) renaming (_===_ to _===₂_ ; _≈_ to _≈₂_ ; cleft_ to cleft₂_ ; cright_ to cright₂_) using (refl')
    open PP (n Clifford.QRel,_===_)
    open SR word-setoid
  f-well-defined {n} (right Sim.selinger-c13) = begin
    (f *) ([ ⊤⊥ ↑ • CZ ↓ • ⊥⊤ ↑ ]ᵣ) ≡⟨ auto ⟩
    Cli.⊤⊥ ↑ • Cli.CZ ↓ • Cli.⊥⊤ ↑ ≈⟨ _≈₂_.axiom Clifford._QRel,_===_.selinger-c13 ⟩
    Cli.⊥⊤ ↓ • Cli.CZ ↑ • Cli.⊤⊥ ↓ ≡⟨ auto ⟩
    (f *) ([ ⊥⊤ ↓ • CZ ↑ • ⊤⊥ ↓ ]ᵣ) ∎
    where
    open PB (n Clifford.QRel,_===_) renaming (_===_ to _===₂_ ; _≈_ to _≈₂_ ; cleft_ to cleft₂_ ; cright_ to cright₂_) using (refl')
    open PP (n Clifford.QRel,_===_)
    open SR word-setoid
  f-well-defined {n} (right Sim.selinger-c14) = begin
    (f *) ([ (⊤⊥ ↑ • CZ ↓) ^ 3 ]ᵣ) ≡⟨ auto ⟩
    (Cli.⊤⊥ ↑ • Cli.CZ ↓) ^ 3 ≈⟨ _≈₂_.axiom Clifford._QRel,_===_.selinger-c14 ⟩
    ε ∎
    where
    open PB (n Clifford.QRel,_===_) renaming (_===_ to _===₂_ ; _≈_ to _≈₂_ ; cleft_ to cleft₂_ ; cright_ to cright₂_) using (refl')
    open PP (n Clifford.QRel,_===_)
    open SR word-setoid
  f-well-defined {n} (right Sim.selinger-c15) = begin
    (f *) ([ (⊥⊤ ↓ • CZ ↑) ^ 3 ]ᵣ) ≡⟨ auto ⟩
    (Cli.⊥⊤ ↓ • Cli.CZ ↑) ^ 3 ≈⟨ _≈₂_.axiom Clifford._QRel,_===_.selinger-c15 ⟩
    ε ∎
    where
    open PB (n Clifford.QRel,_===_) renaming (_===_ to _===₂_ ; _≈_ to _≈₂_ ; cleft_ to cleft₂_ ; cright_ to cright₂_) using (refl')
    open PP (n Clifford.QRel,_===_)
    open SR word-setoid
  f-well-defined {n} (right (Sim.comm-H {x = x})) = begin
    (f *) ([ [ x Sym.↥ ]ʷ • H ]ᵣ) ≡⟨ auto ⟩
    (f (inj₂ x)) ↑ • Cli.H ≈⟨ sym₂ (Lemmas-Clifford.lemma-comm-H-w↑ (f (inj₂ x))) ⟩
    Cli.H • (f (inj₂ x)) ↑ ≡⟨ auto ⟩
    (f *) ([ H • [ x Sym.↥ ]ʷ ]ᵣ) ∎
    where
    open PB (n Clifford.QRel,_===_) renaming (_===_ to _===₂_ ; _≈_ to _≈₂_ ; cleft_ to cleft₂_ ; cright_ to cright₂_ ; sym to sym₂) using (refl')
    open PP (n Clifford.QRel,_===_)
    open SR word-setoid
  f-well-defined {n} (right (Sim.comm-S {x = x})) = begin
    (f *) ([ [ x Sym.↥ ]ʷ • S ]ᵣ) ≡⟨ auto ⟩
    (f (inj₂ x)) ↑ • Clifford.𝑠 ≈⟨ sym₂ (lemma-comm-𝑠-w↑ (f (inj₂ x))) ⟩
    Clifford.𝑠 • (f (inj₂ x)) ↑ ≡⟨ auto ⟩
    (f *) ([ S • [ x Sym.↥ ]ʷ ]ᵣ) ∎
    where
    open PB (n Clifford.QRel,_===_) renaming (_===_ to _===₂_ ; _≈_ to _≈₂_ ; cleft_ to cleft₂_ ; cright_ to cright₂_ ; sym to sym₂) using (refl')
    open PP (n Clifford.QRel,_===_)
    open SR word-setoid
  f-well-defined {n} (right (Sim.comm-CZ {x = x})) = begin
    (f *) ([ [ x Sym.↥ Sym.↥ ]ʷ • CZ ]ᵣ) ≡⟨ auto ⟩
    (f (inj₂ x)) ↑ ↑ • Cli.CZ ≈⟨ sym₂ (Lemmas-Clifford.lemma-comm-CZ-w↑ (f (inj₂ x))) ⟩
    Cli.CZ • (f (inj₂ x)) ↑ ↑ ≡⟨ auto ⟩
    (f *) ([ CZ • [ x Sym.↥ Sym.↥ ]ʷ ]ᵣ) ∎
    where
    open PB (n Clifford.QRel,_===_) renaming (_===_ to _===₂_ ; _≈_ to _≈₂_ ; cleft_ to cleft₂_ ; cright_ to cright₂_ ; sym to sym₂) using (refl')
    open PP (n Clifford.QRel,_===_)
    open SR word-setoid
  f-well-defined {n@(suc (n'@(suc n'')))} (right (Sim.cong↑ {w = w} {v} x)) = begin
    (f *) ([ w Sym.↑ ]ᵣ) ≡⟨ lemma-f*-[w]ᵣ {w = w} ⟩
    (f *) ([ w ]ᵣ) ↑ ≈⟨ Lemmas-Clifford.lemma-cong↑ ((f *) ([ w ]ᵣ)) ((f *) ([ v ]ᵣ)) (f-well-defined (right x)) ⟩
    (f *) ([ v ]ᵣ) ↑ ≡⟨ Eq.sym (lemma-f*-[w]ᵣ {w = v}) ⟩
    (f *) ([ v Sym.↑ ]ᵣ) ∎
    where
    open PB (n Clifford.QRel,_===_) renaming (_===_ to _===₂_ ; _≈_ to _≈₂_ ; cleft_ to cleft₂_ ; cright_ to cright₂_) using (refl')
    open PP (n Clifford.QRel,_===_)
    open SR word-setoid


  f-well-defined {n@(suc n')} (mid (comm XZ.X-gen NS.Symplectic.H-gen)) = begin
    (f *) ([ [ NS.Symplectic.H-gen ]ʷ ]ᵣ • [ [ XZ.X-gen ]ʷ ]ₗ) ≡⟨ auto ⟩
    Cli.H • Clifford.X ≈⟨ CLb.conj-H-X n' ⟩
    Clifford.Z • Cli.H ≡⟨ auto ⟩
    (f *) ([ SemiDirect.conj NS.Symplectic.H-gen XZ.X-gen ]ₗ • [ [ NS.Symplectic.H-gen ]ʷ ]ᵣ) ∎
    where
    open PB (n Clifford.QRel,_===_) renaming (_===_ to _===₂_ ; _≈_ to _≈₂_ ; cleft_ to cleft₂_ ; cright_ to cright₂_) using (refl')
    open PP (n Clifford.QRel,_===_)
    open SR word-setoid
  f-well-defined {n@(suc n')} (mid (comm XZ.X-gen NS.Symplectic.S-gen)) = begin
    (f *) ([ [ NS.Symplectic.S-gen ]ʷ ]ᵣ • [ [ XZ.X-gen ]ʷ ]ₗ) ≡⟨ auto ⟩
    Clifford.𝑠 • Clifford.X ≈⟨ lemma-conj-𝑠-X ⟩
    (Clifford.X • Clifford.Z) • Clifford.𝑠 ≡⟨ auto ⟩
    (f *) ([ SemiDirect.conj NS.Symplectic.S-gen XZ.X-gen ]ₗ • [ [ NS.Symplectic.S-gen ]ʷ ]ᵣ) ∎
    where
    open PB (n Clifford.QRel,_===_) renaming (_===_ to _===₂_ ; _≈_ to _≈₂_ ; cleft_ to cleft₂_ ; cright_ to cright₂_) using (refl')
    open PP (n Clifford.QRel,_===_)
    open SR word-setoid
  f-well-defined {n@(suc (suc n'))} (mid (comm XZ.X-gen NS.Symplectic.CZ-gen)) = begin
    (f *) ([ [ NS.Symplectic.CZ-gen ]ʷ ]ᵣ • [ [ XZ.X-gen ]ʷ ]ₗ) ≡⟨ auto ⟩
    Cli.CZ • Clifford.X ≈⟨ _≈₂_.axiom Clifford._QRel,_===_.rel-X↓-CZ ⟩
    Clifford.X • Clifford.Z ↑ • Cli.CZ ≡⟨ auto ⟩
    (f *) ([ SemiDirect.conj NS.Symplectic.CZ-gen XZ.X-gen ]ₗ • [ [ NS.Symplectic.CZ-gen ]ʷ ]ᵣ) ∎
    where
    open PB (n Clifford.QRel,_===_) renaming (_===_ to _===₂_ ; _≈_ to _≈₂_ ; cleft_ to cleft₂_ ; cright_ to cright₂_) using (refl')
    open PP (n Clifford.QRel,_===_)
    open SR word-setoid
  f-well-defined {n@(suc (suc n'))} (mid (comm XZ.X-gen (h₁ NS.Symplectic.↥))) = begin
    (f *) ([ [ h₁ NS.Symplectic.↥ ]ʷ ]ᵣ • [ [ XZ.X-gen ]ʷ ]ₗ) ≡⟨ auto ⟩
    (f (inj₂ h₁)) ↑ • Clifford.X ≈⟨ sym₂ (Lemmas-Clifford.lemma-comm-X-w↑ (f (inj₂ h₁))) ⟩
    Clifford.X • (f (inj₂ h₁)) ↑ ≡⟨ auto ⟩
    (f *) ([ SemiDirect.conj (h₁ NS.Symplectic.↥) XZ.X-gen ]ₗ • [ [ h₁ NS.Symplectic.↥ ]ʷ ]ᵣ) ∎
    where
    open PB (n Clifford.QRel,_===_) renaming (_===_ to _===₂_ ; _≈_ to _≈₂_ ; cleft_ to cleft₂_ ; cright_ to cright₂_ ; sym to sym₂) using (refl')
    open PP (n Clifford.QRel,_===_)
    open SR word-setoid
  f-well-defined {n@(suc n')} (mid (comm XZ.Z-gen NS.Symplectic.H-gen)) = begin
    (f *) ([ [ NS.Symplectic.H-gen ]ʷ ]ᵣ • [ [ XZ.Z-gen ]ʷ ]ₗ) ≡⟨ auto ⟩
    Cli.H • Clifford.Z ≈⟨ CLb.conj-H-Z n' ⟩
    Clifford.X^ (- ₁) • Cli.H ≡⟨ Eq.cong (\ x -> Clifford.X ^ x • Cli.H) lemma-toℕ-1ₚ ⟩
    Clifford.X ^ p-1 • Cli.H ≡⟨ Eq.cong (_• Cli.H) (Eq.sym (lemma-f*-^ₗ XZ.X p-1)) ⟩
    (f *) ([ XZ.X ^ p-1 ]ₗ) • Cli.H ≡⟨ auto ⟩
    (f *) ([ SemiDirect.conj NS.Symplectic.H-gen XZ.Z-gen ]ₗ • [ [ NS.Symplectic.H-gen ]ʷ ]ᵣ) ∎
    where
    open PB (n Clifford.QRel,_===_) renaming (_===_ to _===₂_ ; _≈_ to _≈₂_ ; cleft_ to cleft₂_ ; cright_ to cright₂_) using (refl')
    open PP (n Clifford.QRel,_===_)
    open SR word-setoid
  f-well-defined {n@(suc n')} (mid (comm XZ.Z-gen NS.Symplectic.S-gen)) = begin
    (f *) ([ [ NS.Symplectic.S-gen ]ʷ ]ᵣ • [ [ XZ.Z-gen ]ʷ ]ₗ) ≡⟨ auto ⟩
    Clifford.𝑠 • Clifford.Z ≈⟨ lemma-comm-𝑠-Z ⟩
    Clifford.Z • Clifford.𝑠 ≡⟨ auto ⟩
    (f *) ([ SemiDirect.conj NS.Symplectic.S-gen XZ.Z-gen ]ₗ • [ [ NS.Symplectic.S-gen ]ʷ ]ᵣ) ∎
    where
    open PB (n Clifford.QRel,_===_) renaming (_===_ to _===₂_ ; _≈_ to _≈₂_ ; cleft_ to cleft₂_ ; cright_ to cright₂_) using (refl')
    open PP (n Clifford.QRel,_===_)
    open SR word-setoid
  f-well-defined {n@(suc (suc n'))} (mid (comm XZ.Z-gen NS.Symplectic.CZ-gen)) = begin
    (f *) ([ [ NS.Symplectic.CZ-gen ]ʷ ]ᵣ • [ [ XZ.Z-gen ]ʷ ]ₗ) ≡⟨ auto ⟩
    Cli.CZ • Clifford.Z ≈⟨ sym₂ lemma-comm-Z-CZ ⟩
    Clifford.Z • Cli.CZ ≡⟨ auto ⟩
    (f *) ([ SemiDirect.conj NS.Symplectic.CZ-gen XZ.Z-gen ]ₗ • [ [ NS.Symplectic.CZ-gen ]ʷ ]ᵣ) ∎
    where
    open PB (n Clifford.QRel,_===_) renaming (_===_ to _===₂_ ; _≈_ to _≈₂_ ; cleft_ to cleft₂_ ; cright_ to cright₂_ ; sym to sym₂) using (refl')
    open PP (n Clifford.QRel,_===_)
    open SR word-setoid
  f-well-defined {n@(suc (suc n'))} (mid (comm XZ.Z-gen (h₁ NS.Symplectic.↥))) = begin
    (f *) ([ [ h₁ NS.Symplectic.↥ ]ʷ ]ᵣ • [ [ XZ.Z-gen ]ʷ ]ₗ) ≡⟨ auto ⟩
    (f (inj₂ h₁)) ↑ • Clifford.Z ≈⟨ sym₂ (Lemmas-Clifford.lemma-comm-Z-w↑ (f (inj₂ h₁))) ⟩
    Clifford.Z • (f (inj₂ h₁)) ↑ ≡⟨ auto ⟩
    (f *) ([ SemiDirect.conj (h₁ NS.Symplectic.↥) XZ.Z-gen ]ₗ • [ [ h₁ NS.Symplectic.↥ ]ʷ ]ᵣ) ∎
    where
    open PB (n Clifford.QRel,_===_) renaming (_===_ to _===₂_ ; _≈_ to _≈₂_ ; cleft_ to cleft₂_ ; cright_ to cright₂_ ; sym to sym₂) using (refl')
    open PP (n Clifford.QRel,_===_)
    open SR word-setoid
  f-well-defined {n@(suc (suc n'))} (mid (comm (n₁ XZ.↥) NS.Symplectic.H-gen)) = begin
    (f *) ([ [ NS.Symplectic.H-gen ]ʷ ]ᵣ • [ [ n₁ XZ.↥ ]ʷ ]ₗ) ≡⟨ auto ⟩
    Cli.H • (f (inj₁ n₁)) ↑ ≈⟨ Lemmas-Clifford.lemma-comm-H-w↑ (f (inj₁ n₁)) ⟩
    (f (inj₁ n₁)) ↑ • Cli.H ≡⟨ auto ⟩
    (f *) ([ SemiDirect.conj NS.Symplectic.H-gen (n₁ XZ.↥) ]ₗ • [ [ NS.Symplectic.H-gen ]ʷ ]ᵣ) ∎
    where
    open PB (n Clifford.QRel,_===_) renaming (_===_ to _===₂_ ; _≈_ to _≈₂_ ; cleft_ to cleft₂_ ; cright_ to cright₂_ ; sym to sym₂) using (refl')
    open PP (n Clifford.QRel,_===_)
    open SR word-setoid
  f-well-defined {n@(suc (suc n'))} (mid (comm (n₁ XZ.↥) NS.Symplectic.S-gen)) = begin
    (f *) ([ [ NS.Symplectic.S-gen ]ʷ ]ᵣ • [ [ n₁ XZ.↥ ]ʷ ]ₗ) ≡⟨ auto ⟩
    Clifford.𝑠 • (f (inj₁ n₁)) ↑ ≈⟨ lemma-comm-𝑠-w↑ (f (inj₁ n₁)) ⟩
    (f (inj₁ n₁)) ↑ • Clifford.𝑠 ≡⟨ auto ⟩
    (f *) ([ SemiDirect.conj NS.Symplectic.S-gen (n₁ XZ.↥) ]ₗ • [ [ NS.Symplectic.S-gen ]ʷ ]ᵣ) ∎
    where
    open PB (n Clifford.QRel,_===_) renaming (_===_ to _===₂_ ; _≈_ to _≈₂_ ; cleft_ to cleft₂_ ; cright_ to cright₂_ ; sym to sym₂) using (refl')
    open PP (n Clifford.QRel,_===_)
    open SR word-setoid
  f-well-defined {n@(suc (suc n'))} (mid (comm (XZ.X-gen XZ.↥) NS.Symplectic.CZ-gen)) = begin
    (f *) ([ [ NS.Symplectic.CZ-gen ]ʷ ]ᵣ • [ [ XZ.X-gen XZ.↥ ]ʷ ]ₗ) ≡⟨ auto ⟩
    Cli.CZ • Clifford.X ↑ ≈⟨ _≈₂_.axiom Clifford._QRel,_===_.rel-X↑-CZ ⟩
    Clifford.X ↑ • Clifford.Z • Cli.CZ ≡⟨ auto ⟩
    (f *) ([ SemiDirect.conj NS.Symplectic.CZ-gen (XZ.X-gen XZ.↥) ]ₗ • [ [ NS.Symplectic.CZ-gen ]ʷ ]ᵣ) ∎
    where
    open PB (n Clifford.QRel,_===_) renaming (_===_ to _===₂_ ; _≈_ to _≈₂_ ; cleft_ to cleft₂_ ; cright_ to cright₂_) using (refl')
    open PP (n Clifford.QRel,_===_)
    open SR word-setoid
  f-well-defined {n@(suc (suc n'))} (mid (comm (XZ.Z-gen XZ.↥) NS.Symplectic.CZ-gen)) = begin
    (f *) ([ [ NS.Symplectic.CZ-gen ]ʷ ]ᵣ • [ [ XZ.Z-gen XZ.↥ ]ʷ ]ₗ) ≡⟨ auto ⟩
    Cli.CZ • Clifford.Z ↑ ≈⟨ sym₂ lemma-comm-Z↑-CZ ⟩
    Clifford.Z ↑ • Cli.CZ ≡⟨ auto ⟩
    (f *) ([ SemiDirect.conj NS.Symplectic.CZ-gen (XZ.Z-gen XZ.↥) ]ₗ • [ [ NS.Symplectic.CZ-gen ]ʷ ]ᵣ) ∎
    where
    open PB (n Clifford.QRel,_===_) renaming (_===_ to _===₂_ ; _≈_ to _≈₂_ ; cleft_ to cleft₂_ ; cright_ to cright₂_ ; sym to sym₂) using (refl')
    open PP (n Clifford.QRel,_===_)
    open SR word-setoid
  f-well-defined {n@(suc (suc (suc n')))} (mid (comm ((m XZ.↥) XZ.↥) NS.Symplectic.CZ-gen)) = begin
    (f *) ([ [ NS.Symplectic.CZ-gen ]ʷ ]ᵣ • [ [ (m XZ.↥) XZ.↥ ]ʷ ]ₗ) ≡⟨ auto ⟩
    Cli.CZ • (f (inj₁ m)) ↑ ↑ ≈⟨ Lemmas-Clifford.lemma-comm-CZ-w↑ (f (inj₁ m)) ⟩
    (f (inj₁ m)) ↑ ↑ • Cli.CZ ≡⟨ auto ⟩
    (f *) ([ SemiDirect.conj NS.Symplectic.CZ-gen ((m XZ.↥) XZ.↥) ]ₗ • [ [ NS.Symplectic.CZ-gen ]ʷ ]ᵣ) ∎
    where
    open PB (n Clifford.QRel,_===_) renaming (_===_ to _===₂_ ; _≈_ to _≈₂_ ; cleft_ to cleft₂_ ; cright_ to cright₂_) using (refl')
    open PP (n Clifford.QRel,_===_)
    open SR word-setoid
  f-well-defined {n@(suc n')} (mid (comm (n₁ XZ.↥) (h₁ NS.Symplectic.↥))) = begin
    (f *) ([ [ h₁ NS.Symplectic.↥ ]ʷ ]ᵣ • [ [ n₁ XZ.↥ ]ʷ ]ₗ) ≡⟨ Eq.sym (lemma-f*-SD↑ ([ [ h₁ ]ʷ ]ᵣ • [ [ n₁ ]ʷ ]ₗ)) ⟩
    (f *) ([ [ h₁ ]ʷ ]ᵣ • [ [ n₁ ]ʷ ]ₗ) ↑ ≈⟨ Lemmas-Clifford.lemma-cong↑ _ _ (f-well-defined (mid (comm n₁ h₁))) ⟩
    (f *) ([ SemiDirect.conj h₁ n₁ ]ₗ • [ [ h₁ ]ʷ ]ᵣ) ↑ ≡⟨ Eq.sym (lemma-f*-SD↑ ([ SemiDirect.conj h₁ n₁ ]ₗ • [ [ h₁ ]ʷ ]ᵣ)) ⟩
    (f *) (SD._↑ {n'} ([ SemiDirect.conj h₁ n₁ ]ₗ • [ [ h₁ ]ʷ ]ᵣ)) ≡⟨ auto ⟩
    (f *) (SD._↑ {n'} ([_]ₗ {B = Sym.Gen n'} (SemiDirect.conj h₁ n₁)) • [ [ h₁ NS.Symplectic.↥ ]ʷ ]ᵣ) ≡⟨ Eq.cong (\ x -> (f *) (x • [ [ h₁ NS.Symplectic.↥ ]ʷ ]ᵣ)) bridge ⟩
    (f *) ([_]ₗ {B = Sym.Gen (suc n')} (SemiDirect.conj h₁ n₁ XZ.↑) • [ [ h₁ NS.Symplectic.↥ ]ʷ ]ᵣ) ≡⟨ auto ⟩
    (f *) ([ SemiDirect.conj (h₁ NS.Symplectic.↥) (n₁ XZ.↥) ]ₗ • [ [ h₁ NS.Symplectic.↥ ]ʷ ]ᵣ) ∎
    where
    open PB (n Clifford.QRel,_===_) renaming (_===_ to _===₂_ ; _≈_ to _≈₂_ ; cleft_ to cleft₂_ ; cright_ to cright₂_) using (refl')
    open PP (n Clifford.QRel,_===_)
    bridge : SD._↑ {n'} ([_]ₗ {B = Sym.Gen n'} (SemiDirect.conj h₁ n₁)) ≡ [_]ₗ {B = Sym.Gen (suc n')} (SemiDirect.conj h₁ n₁ XZ.↑)
    bridge = lemma-[]ₗ-↑' (SemiDirect.conj h₁ n₁)
    open SR word-setoid
