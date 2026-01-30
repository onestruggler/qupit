{-# OPTIONS  --safe #-}
{-# OPTIONS  --call-by-name #-}
{-# OPTIONS --termination-depth=4 #-}
open import Level using (0ℓ)

open import Relation.Binary using (Rel)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Binary.Morphism.Definitions using (Homomorphic₂)
open import Relation.Binary.PropositionalEquality using (_≡_ ; _≢_ ; inspect ; setoid ; module ≡-Reasoning ; _≗_) renaming ([_] to [_]')
import Relation.Binary.Reasoning.Setoid as SR
import Relation.Binary.PropositionalEquality as Eq
open import Relation.Nullary.Decidable using (yes ; no)


open import Function using (_∘_ ; id)
open import Function.Definitions using (Injective)

open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂ ; map₁ ; ∃ ; Σ ; Σ-syntax)
open import Data.Product.Relation.Binary.Pointwise.NonDependent as PW using (≡×≡⇒≡ ; Pointwise ; ≡⇒≡×≡)
open import Data.Nat hiding (_^_ ; _+_ ; _*_)
open import Agda.Builtin.Nat using (_-_)
import Data.Nat as Nat
open import Data.Bool hiding (_<_ ; _≤_)
--open import Data.List using () hiding ([_] ; _++_ ; last ; head ; tail ; _∷ʳ_)
open import Data.Vec hiding ([_])
open import Data.Vec as V
open import Data.Fin hiding (_+_ ; _-_ ; _≤_ ; _<_)

open import Data.Maybe
open import Data.Sum using (_⊎_ ; inj₁ ; inj₂ ; [_,_] ; [_,_]′)
open import Data.Unit using (⊤ ; tt)
open import Data.Empty using (⊥ ; ⊥-elim)

open import Word.Base as WB hiding (wfoldl ; _* ; _^'_)
open import Word.Properties
import Presentation.Base as PB
import Presentation.Properties as PP
open PP using (NFProperty ; NFProperty')
import Presentation.CosetNF as CA
import Presentation.Reidemeister-Schreier as RS
module RSF = RS.Star-Injective-Full.Reidemeister-Schreier-Full

open import Presentation.Construct.Base hiding (_*_ ; _⊕_)
import Presentation.Construct.Properties.SemiDirectProduct2 as SDP2
import Presentation.Construct.Properties.DirectProduct as DP
import Presentation.Groups.Cyclic as Cyclic


open import Data.Fin using (Fin ; toℕ ; suc ; zero ; fromℕ)
open import Data.Fin.Properties using (suc-injective ; toℕ-inject₁ ; toℕ-fromℕ)
import Data.Nat.Properties as NP
open import Presentation.GroupLike
open import Presentation.Tactics using ()
open import Data.Nat.Primality



module N.BR.One.A (p-2 : ℕ) (p-prime : Prime (2+ p-2)) (n : ℕ)  where

    
pattern auto = Eq.refl

pattern ₀ = zero
pattern ₁ = suc ₀
pattern ₂ = suc ₁
pattern ₃ = suc ₂
pattern ₅ = 5
pattern ₆ = 6
pattern ₇ = 7
pattern ₈ = 8
pattern ₉ = 9
pattern ₁₀ = 10
pattern ₁₁ = 11
pattern ₁₂ = 12
pattern ₁₃ = 13
pattern ₁₄ = 14
pattern ₁₅ = 15

pattern ₁₊ ⱼ = suc ⱼ
pattern ₂₊ ⱼ = suc (suc ⱼ)
pattern ₃₊ ⱼ = suc (suc (suc ⱼ))
pattern ₄₊ ⱼ = suc (suc (suc (suc ⱼ)))


open import Zp.ModularArithmetic
open PrimeModulus p-2 p-prime
open import N.Cosets p-2 p-prime
open import N.Symplectic p-2 p-prime
open Symplectic renaming (M to ZM)
open import N.NF1-Sym p-2 p-prime
open import N.LM-Sym p-2 p-prime

open import N.Action p-2 p-prime
open import N.Action-Lemmas p-2 p-prime
open import Algebra.Properties.Ring (+-*-ring p-2)
open import N.NF2-Sym p-2 p-prime
open LM2


open import Zp.ModularArithmetic
open import N.Lemmas-2Qupit-Sym p-2 p-prime
open import N.NF2-Sym p-2 p-prime
--open Lemmas-2Q 2

open import N.NF1 p-2 p-prime
open import N.Ex-Sym p-2 p-prime
open import N.Ex-Sym1 p-2 p-prime
open import N.Ex-Sym2 p-2 p-prime
open import N.Ex-Sym3 p-2 p-prime
open import N.Ex-Sym4 p-2 p-prime
open import N.Ex-Sym5 p-2 p-prime hiding (module L0)
open import N.Ex-Sym2n p-2 p-prime
open import N.Ex-Sym3n p-2 p-prime

open import N.Lemma-Comm-n p-2 p-prime
open import N.Completeness1-Sym p-2 p-prime renaming (module Completeness to Cp1)
open Lemmas0a
open Lemmas0a1
open Lemmas0b
open Lemmas0c
open Lemmas-Sym
open Duality

open import N.Completeness1-Sym p-2 p-prime renaming (module Completeness to CP1) using ()
open import N.Coset2-Update-Sym p-2 p-prime renaming (module Completeness to CP2) using ()
open import N.Lemmas4-Sym p-2 p-prime
open import N.Pushing.DH p-2 p-prime
open import N.BR.Calculations p-2 p-prime


open PB ((₁₊ n) QRel,_===_)
open PP ((₁₊ n) QRel,_===_)
open SR word-setoid
open Pattern-Assoc
open Lemmas0 n

fig-24-1 : ∀ (b* : ℤ* ₚ) ->
  let
  b = b* .proj₁
  nz : (₀ , b) ≢ (₀ , ₀)
  nz = aux-b≠0⇒ab≠0 ₀ b (b* .proj₂)
  nz' : (b , ₀) ≢ (₀ , ₀)
  nz' = aux-a≠0⇒ab≠0 b ₀ (b* .proj₂)
  in
  
  [ (₀ , b) , nz ]ᵃ • H ≈ [ (b , ₀) , nz' ]ᵃ
  
fig-24-1 b*@(₀ , nzb) = ⊥-elim (nzb auto)
fig-24-1 b*@(b@(₁₊ b-1) , nzb) = begin
  ⟦ (b , λ ()) ⁻¹ , ε ⟧ₘ₊ • H ≈⟨ cleft right-unit ⟩
  ⟦ (b , λ ()) ⁻¹ ⟧ₘ • H ≈⟨ cright sym right-unit ⟩
  ⟦ (b , λ ()) ⁻¹ ⟧ₘ • H • ε ≈⟨ refl ⟩
  ⟦ (b , λ ()) ⁻¹ ⟧ₘ • H • S^ ₀ ≈⟨ cright cright refl' (Eq.cong S^ (Eq.sym (Eq.trans (Eq.cong (_* b⁻¹) -0#≈0#) (*-zeroˡ b⁻¹)))) ⟩
  ⟦ (b , λ ()) ⁻¹ ⟧ₘ • H • S^ (- ₀ * b⁻¹) ≈⟨ refl ⟩
  [ (b , ₀) , aux-a≠0⇒ab≠0 b ₀ nzb  ]ᵃ ∎
  where
  nz : (₀ , b) ≢ (₀ , ₀)
  nz = aux-b≠0⇒ab≠0 ₀ b (b* .proj₂)
  b⁻¹ = (b* ⁻¹).proj₁
  


fig-24-2 : ∀ (a* : ℤ* ₚ) ->
  let
  a = a* .proj₁
  nz : (a , ₀) ≢ (₀ , ₀)
  nz = aux-a≠0⇒ab≠0 a ₀ (a* .proj₂)
  nz' : (₀ , - a ) ≢ (₀ , ₀)
  nz' = aux-b≠0⇒ab≠0 ₀ (- a) ((-' a*) .proj₂)
  in
  
  [ (a , ₀) , nz ]ᵃ • H ≈ [ (₀ , - a) , nz' ]ᵃ
  
fig-24-2 a*@(₀ , nza) = ⊥-elim (nza auto)
fig-24-2 a*@(a@(₁₊ a-1) , nza) = begin
  [ (a , ₀) , nz ]ᵃ • H ≈⟨ refl ⟩
  ⟦ (a , λ ()) ⁻¹ , HS^ -b/a ⟧ₘ₊ • H ≈⟨ cleft cright cright  refl' (Eq.cong S^ ( (Eq.trans (Eq.cong (_* a⁻¹) -0#≈0#) (*-zeroˡ a⁻¹)))) ⟩
  (⟦ (a , λ ()) ⁻¹ ⟧ₘ • H • S^ ₀ ) • H ≈⟨ cleft cright right-unit ⟩
  (⟦ (a , λ ()) ⁻¹ ⟧ₘ • H) • H ≈⟨ assoc ⟩
  ⟦ (a , λ ()) ⁻¹ ⟧ₘ • H • H ≈⟨ cright lemma-HH-M-1  ⟩
  ⟦ (a , λ ()) ⁻¹ ⟧ₘ • ZM (-'₁) ≈⟨ axiom (M-mul ((a , λ ()) ⁻¹) -'₁) ⟩
  ⟦ (a , λ ()) ⁻¹ *' -'₁ ⟧ₘ  ≈⟨ aux-MM (((a , λ ()) ⁻¹ *' -'₁) .proj₂) (( -'₁ *' (a , λ ()) ⁻¹) .proj₂) (*-comm a⁻¹ (- ₁)) ⟩
  ⟦  -'₁ *' (a , λ ()) ⁻¹  ⟧ₘ  ≈⟨ aux-MM  ((-'₁ *' (a , λ ()) ⁻¹) .proj₂) ((-' (a , λ ()) ⁻¹).proj₂) (-1*x≈-x a⁻¹) ⟩
  ⟦  -' (a , λ ()) ⁻¹  ⟧ₘ  ≈⟨ aux-MM  ((-' (a , λ ()) ⁻¹) .proj₂) (( (-' (a , λ ())) ⁻¹) .proj₂) (Eq.sym (inv-neg-comm ((a , λ ())))) ⟩
  ⟦  (-' (a , λ ())) ⁻¹  ⟧ₘ  ≈⟨ refl ⟩
  ⟦  (- a , ((-' a*) .proj₂)) ⁻¹  ⟧ₘ  ≈⟨ sym (aux-abox-nzb (- a) (((-' a*) .proj₂))) ⟩
  [ (₀ , - a) , nz' ]ᵃ ∎
  where
  nz : (a , ₀) ≢ (₀ , ₀)
  nz = aux-a≠0⇒ab≠0 a ₀ (a* .proj₂)
  nz' : (₀ , - a ) ≢ (₀ , ₀)
  nz' = aux-b≠0⇒ab≠0 ₀ (- a) ((-' a*) .proj₂)

  a⁻¹ = ((a , λ ()) ⁻¹) .proj₁
  -b/a = - ₀ * a⁻¹



fig-24-3 : ∀ (a* b* : ℤ* ₚ) ->
  let
  a = a* .proj₁
  b = b* .proj₁
  nz : (a , b) ≢ (₀ , ₀)
  nz = aux-a≠0⇒ab≠0 a b (a* .proj₂)
  nz' : (b , - a ) ≢ (₀ , ₀)
  nz' = aux-a≠0⇒ab≠0 b (- a) (b* .proj₂)
  [ab]⁻¹* = ( a* *' b*) ⁻¹
  [ab]⁻¹ = [ab]⁻¹* .proj₁
  in
  
  [ (a , b) , nz ]ᵃ • H ≈ S^ [ab]⁻¹ • [ (b , - a) , nz' ]ᵃ
  
fig-24-3 a*@(₀ , nza) b* = ⊥-elim (nza auto)
fig-24-3 a*@(a@(₁₊ a-1) , nza) b*@(b , nzb) = begin
  [ (a , b) , nz ]ᵃ • H ≈⟨ refl ⟩
  ⟦ (a , λ ()) ⁻¹ , HS^ -b/a ⟧ₘ₊ • H ≈⟨ special-assoc (□ ^ 3 • □) (□ ^ 4) auto ⟩
  ⟦ (a , λ ()) ⁻¹ ⟧ₘ • H • S^ -b/a • H ≈⟨ derived-7  x y nzx nzy ⟩
  S^ (-x⁻¹ * (y * y)) • ZM -y/x' • (H • S^ -x⁻¹) ≈⟨ cong (refl' (Eq.cong S^ (cal .proj₁))) (cong (aux-MM  (-y/x' .proj₂) ((b* ⁻¹) .proj₂) (cal .proj₂ .proj₁)) (cright refl' (Eq.cong S^ (cal .proj₂ .proj₂)))) ⟩
  S^ [ab]⁻¹ • ZM (b* ⁻¹) • (H • S^ (- - a * b⁻¹)) ≈⟨ sym (cright aux-abox-nza b (- a) nzb) ⟩
  S^ [ab]⁻¹ • [ (b , - a) , nz' ]ᵃ ∎
  where
  nz : (a , b) ≢ (₀ , ₀)
  nz = aux-a≠0⇒ab≠0 a b (a* .proj₂)
  nz' : (b , - a ) ≢ (₀ , ₀)
  nz' = aux-a≠0⇒ab≠0 b (- a) (b* .proj₂)
  b⁻¹ = (b* ⁻¹) .proj₁

  a⁻¹ = ((a , λ ()) ⁻¹) .proj₁
  -b/a = - b * a⁻¹
  y = a⁻¹
  nzy = ((a , λ ()) ⁻¹) .proj₂
  x = -b/a
  nzx = (-' b* *' a* ⁻¹).proj₂
  
  x⁻¹ = ((x , nzx) ⁻¹) .proj₁
  x⁻¹⁻¹ = (((x , nzx) ⁻¹) ⁻¹) .proj₁
  -x⁻¹ = - x⁻¹
  -y/x' = (((y , nzy) *' ((x , nzx) ⁻¹)) *' -'₁)
  -y/x = -y/x' .proj₁

  [ab]⁻¹* = (  (a , λ ()) *' (b , nzb)  ) ⁻¹
  [ab]⁻¹ = [ab]⁻¹* .proj₁

  cal = fig-24-3-cal-1 a* b*



fig-25-1 : ∀ (b*@(b , nzb) : ℤ* ₚ) ->
  let
  b⁻¹ = (b* ⁻¹) .proj₁
  b⁻² = b⁻¹ * b⁻¹
  nz : (₀ , b) ≢ (₀ , ₀)
  nz = aux-b≠0⇒ab≠0 ₀ b nzb
  in
  
  [(₀ , b) , nz ]ᵃ • S ≈ S^ b⁻² • [(₀ , b) , nz ]ᵃ

fig-25-1 b*@(b , nzb) = begin
  [(₀ , b) , nz ]ᵃ • S ≈⟨ cleft aux-abox-nzb b nzb ⟩
  ⟦ (b , nzb) ⁻¹ ⟧ₘ • S ≈⟨ axiom (semi-MS ((b , nzb) ⁻¹)) ⟩
  S^ b⁻² • ⟦ (b , nzb) ⁻¹ ⟧ₘ ≈⟨ cright sym (aux-abox-nzb b nzb) ⟩
  S^ b⁻² • [(₀ , b) , nz ]ᵃ ∎
  where
  b⁻¹ = (b* ⁻¹) .proj₁
  b⁻² = b⁻¹ * b⁻¹
  nz : (₀ , b) ≢ (₀ , ₀)
  nz = aux-b≠0⇒ab≠0 ₀ b nzb
  

fig-25-2 : ∀ (a*@(a , nza) : ℤ* ₚ) (b : ℤ ₚ) ->
  let
  nz : (a , b) ≢ (₀ , ₀)
  nz = aux-a≠0⇒ab≠0 a b nza
  a⁻¹ = ((a , nza) ⁻¹) .proj₁
  -b/a = - b * a⁻¹
  nz' : (a , b + - a) ≢ (₀ , ₀)
  nz' = aux-a≠0⇒ab≠0 a (b + - a) nza
  in
  
  [(a , b) , nz ]ᵃ • S ≈ [(a , b + - a) , nz' ]ᵃ

fig-25-2 a*@(a , nza) b = begin
  [(a , b) , nz ]ᵃ • S ≈⟨ cleft aux-abox-nza a b nza ⟩
  ⟦ (a , nza) ⁻¹ , HS^ -b/a ⟧ₘ₊ • S ≈⟨  (  special-assoc (□ ^ 3 • □) (□ ^ 2 • □ ^ 2) auto) ⟩
  ((ZM (a* ⁻¹) • H) • S^ -b/a • S) ≈⟨ (  cright lemma-S^k+l  -b/a ₁) ⟩
  ((ZM (a* ⁻¹) • H) • S^ (-b/a + ₁)) ≈⟨ ( ( assoc)) ⟩
  (ZM (a* ⁻¹) • H • S^ (-b/a + ₁)) ≈⟨ cright cright refl' (Eq.cong S^ (fig-25-2-cal a* b))  ⟩
  (ZM (a* ⁻¹) • H • S^ (- (b + - a) * a⁻¹)) ≈⟨ sym (aux-abox-nza a (b + - a) nza) ⟩
  ([ (a , (b + - a)) , nz' ]ᵃ) ≈⟨ refl ⟩
  ([ (a , b + - a) , nz' ]ᵃ)  ∎
  where
  nz : (a , b) ≢ (₀ , ₀)
  nz = aux-a≠0⇒ab≠0 a b nza
  a⁻¹ = ((a , nza) ⁻¹) .proj₁
  -b/a = - b * a⁻¹
  nz' : (a , b + - a) ≢ (₀ , ₀)
  nz' = aux-a≠0⇒ab≠0 a (b + - a) nza
  

Bottom-Wire-Single : Gen (₁₊ n) -> Set
Bottom-Wire-Single H-gen = ⊤
Bottom-Wire-Single S-gen = ⊤
Bottom-Wire-Single CZ-gen = ⊥
Bottom-Wire-Single (g ↥) = ⊥


dir-and-A'-of : A -> (g : Gen (₁₊ n)) (bws : Bottom-Wire-Single g) -> Word (Gen (₁₊ n)) × A
dir-and-A'-of x@((a@₀ , b@₀) , nz) _ = ⊥-elim (nz auto)
dir-and-A'-of x@((a@₀ , b@(₁₊ _)) , nz) H-gen bws          =     ε          ,     (b , ₀) , λ ()
dir-and-A'-of x@((a@(₁₊ _) , b@₀) , nz) H-gen bws          =     ε          ,     (₀ , - a) , nz'
  where
  nz' = aux-b≠0⇒ab≠0 ₀ (- a) ((-' (a , λ ())) .proj₂)
dir-and-A'-of x@((a@(₁₊ _) , b@(₁₊ _)) , nz) H-gen bws     =     S^ [ab]⁻¹  ,     (b , - a) , nz'
  where
  nz' = aux-a≠0⇒ab≠0 b (- a) λ ()
  [ab]⁻¹ = ((  (a , λ ()) *' (b , λ ())  ) ⁻¹) .proj₁
dir-and-A'-of x@((a@₀ , b@(₁₊ _)) , nz) S-gen bws          =     S^ b⁻²     ,     (₀ , b) , nz
  where
  b* = (b , λ ())
  b⁻² = ((b* ⁻¹) .proj₁) * ((b* ⁻¹) .proj₁)
dir-and-A'-of x@((a@(₁₊ _) , b) , nz) S-gen bws            =     ε          ,     (a , b + - a) , nz'
  where
  nz' = aux-a≠0⇒ab≠0 a (b + - a) λ ()


lemma-single-qupit-br-A : ∀ (x : A) (g : Gen (₁₊ n)) (bws : Bottom-Wire-Single g) ->
  let (dir , x') = dir-and-A'-of x g bws in
  
  [ x ]ᵃ • [ g ]ʷ ≈ dir • [ x' ]ᵃ

lemma-single-qupit-br-A x@((a@₀ , b@₀) , nz) _ bws = ⊥-elim (nz auto)
lemma-single-qupit-br-A x@((a@₀ , b@(₁₊ _)) , nz) S-gen bws = fig-25-1 (b , (λ ()))
lemma-single-qupit-br-A x@((a@(₁₊ _) , b@₀) , nz) S-gen bws = trans (fig-25-2 (a , (λ ())) b) (sym left-unit)
lemma-single-qupit-br-A x@((a@(₁₊ _) , b@(₁₊ _)) , nz) S-gen bws = trans (fig-25-2 (a , (λ ())) b) (sym left-unit)
lemma-single-qupit-br-A x@((a@₀ , b@(₁₊ _)) , nz) H-gen bws = trans (fig-24-1 (b , (λ ()))) (sym left-unit)
lemma-single-qupit-br-A x@((a@(₁₊ _) , b@₀) , nz) H-gen bws = trans (fig-24-2 (a , (λ ()))) (sym left-unit)
lemma-single-qupit-br-A x@((a@(₁₊ _) , b@(₁₊ _)) , nz) H-gen bws = fig-24-3 (a , (λ ())) (b , λ ()) 




aux-x≠0⇒x=₁₊y : ∀ (x : ℤ ₚ) (nz : x ≢ ₀) -> ∃ \ y -> x ≡ ₁₊ y
aux-x≠0⇒x=₁₊y ₀ nz = ⊥-elim (nz auto)
aux-x≠0⇒x=₁₊y (₁₊ x) nz = x , auto


aux-AA : ∀ {n} (x y : A) (eq : x .proj₁ ≡ y .proj₁) -> [_]ᵃ {n} x ≡ [ y ]ᵃ
aux-AA {n} ((₀ , ₀) , px) ((c , d) , py) eq = ⊥-elim (px auto)
aux-AA {n} ((a , b) , px) ((₀ , ₀) , py) eq = ⊥-elim (py auto)
aux-AA {n} ((a@₀ , b@(₁₊ _)) , px) ((c@₀ , d@(₁₊ _)) , py) eq = Eq.cong (_• ε) (aux-M≡M' ((b , λ ()) ⁻¹) ((d , λ ()) ⁻¹) (inv-cong (b , (λ ())) (d , (λ ())) (Eq.cong proj₂ eq)))
aux-AA {n} ((a@(₁₊ _) , b) , px) ((c@(₁₊ _) , d) , py) eq = Eq.cong₂ (\ xx yy -> xx • H • S^ yy ) (aux-M≡M' ((a , λ ()) ⁻¹) ((c , λ ()) ⁻¹) (inv-cong (a , (λ ())) (c , (λ ())) (Eq.cong proj₁ eq))) (Eq.cong₂ _*_ (Eq.cong -_ (Eq.cong proj₂ eq)) ( (inv-cong (a , (λ ())) (c , (λ ())) (Eq.cong proj₁ eq))))


lemma-A-HH : ∀ a b (nz : a ≢ ₀) ->
  let
  nzp = aux-a≠0⇒ab≠0 a b nz
  nzp' = aux-a≠0⇒ab≠0 (- a) (- b) ((-' (a , nz)) .proj₂)
  in
  
  [ (a , b) , nzp ]ᵃ • HH ≈ [ (- a , - b)  , nzp' ]ᵃ

lemma-A-HH a@₀ b nz = ⊥-elim (nz auto)

lemma-A-HH a@(₁₊ _) b@₀ nz = begin
  [ (a , b) , nzp ]ᵃ • HH ≈⟨ sym assoc ⟩
  ([ (a , b) , nzp ]ᵃ • H) • H ≈⟨ cleft lemma-single-qupit-br-A ((a , b) , nzp) H-gen tt ⟩
  (ε • [ (₀ , - a) , nzp'' ]ᵃ) • H ≈⟨ trans assoc left-unit ⟩
  [ (₀ , - a) , nzp'' ]ᵃ • H ≈⟨ cleft refl' (aux-AA ((₀ , - a) , nzp'') ((₀ , ₁₊ y) , (λ ())) (≡×≡⇒≡ (auto , eq))) ⟩
  [ (₀ , ₁₊ y) , (λ ()) ]ᵃ • H ≈⟨ lemma-single-qupit-br-A ((₀ , ₁₊ y) , (λ ())) H-gen tt ⟩
  ε • [ (₁₊ y , ₀) , (λ ()) ]ᵃ ≈⟨ left-unit ⟩
  [ (₁₊ y , ₀) , (λ ()) ]ᵃ ≈⟨ sym (refl' (aux-AA ((- a , ₀) , nzp'0) ((₁₊ y , ₀) , (λ ())) (≡×≡⇒≡ (eq , auto)))) ⟩
  [ (- a , ₀)  , nzp'0 ]ᵃ ≈⟨ refl' (aux-AA ((- a , ₀)  , nzp'0) ((- a , - b)  , nzp') (≡×≡⇒≡ (auto , (Eq.sym -0#≈0#)))) ⟩
  [ (- a , - b)  , nzp' ]ᵃ ∎
  where
  nz-a = ((-' (a , nz)) .proj₂)
  nzp = aux-a≠0⇒ab≠0 a b nz
  nzp' = aux-a≠0⇒ab≠0 (- a) (- b) nz-a
  nzp'0 = aux-a≠0⇒ab≠0 (- a) ₀ nz-a
  nzp'' = aux-b≠0⇒ab≠0 ₀ (- a) nz-a
  1+y = aux-x≠0⇒x=₁₊y (- a) nz-a
  y = 1+y .proj₁
  eq = 1+y .proj₂

lemma-A-HH a@(₁₊ _) b@(₁₊ _) nz = begin
  [ (a , b) , nzp ]ᵃ • HH ≈⟨ sym assoc ⟩
  ([ (a , b) , nzp ]ᵃ • H) • H ≈⟨ cleft lemma-single-qupit-br-A ((a , b) , nzp) H-gen tt ⟩
  (S^ [ab]⁻¹ • [ (b , - a) , nzp'' ]ᵃ) • H ≈⟨ assoc ⟩
  S^ [ab]⁻¹ • [ (b , - a) , nzp'' ]ᵃ • H ≈⟨ cright cleft refl' (aux-AA ((b , - a) , nzp'') ((b , ₁₊ y) , (λ ())) (≡×≡⇒≡ (auto , eq))) ⟩
  S^ [ab]⁻¹ • [ (b , ₁₊ y) , (λ ()) ]ᵃ • H ≈⟨ cright lemma-single-qupit-br-A ((b , ₁₊ y) , (λ ())) H-gen tt ⟩
  S^ [ab]⁻¹ • S^ [ba']⁻¹ • [ (₁₊ y , - b) , (λ ()) ]ᵃ ≈⟨ sym assoc ⟩
  (S^ [ab]⁻¹ • S^ [ba']⁻¹) • [ (₁₊ y , - b) , (λ ()) ]ᵃ ≈⟨ cleft lemma-S^k+l [ab]⁻¹ [ba']⁻¹ ⟩
  S^ ([ab]⁻¹ + [ba']⁻¹) • [ (₁₊ y , - b) , (λ ()) ]ᵃ ≈⟨ cleft refl' (Eq.cong S^ aux) ⟩
  ε • [ (₁₊ y , - b) , (λ ()) ]ᵃ ≈⟨ left-unit ⟩
  [ (₁₊ y , - b) , (λ ()) ]ᵃ ≈⟨ sym (refl' (aux-AA ((- a , - b) , nzp') ((₁₊ y , - b) , (λ ())) (≡×≡⇒≡ (eq , auto)))) ⟩
  [ (- a , - b)  , nzp' ]ᵃ ∎
  where
  nz-a = ((-' (a , nz)) .proj₂)
  nzp = aux-a≠0⇒ab≠0 a b nz
  nzp' = aux-a≠0⇒ab≠0 (- a) (- b) nz-a
  nzp'' = aux-b≠0⇒ab≠0 b (- a) nz-a
  1+y = aux-x≠0⇒x=₁₊y (- a) nz-a
  y = 1+y .proj₁
  eq = 1+y .proj₂
  nz' = aux-a≠0⇒ab≠0 b (- a) λ ()
  [ab]⁻¹ = ((  (a , λ ()) *' (b , λ ())  ) ⁻¹) .proj₁
  [ba']⁻¹ = ((  (b , λ ()) *' (₁₊ y , λ ())  ) ⁻¹) .proj₁
  aux0 : [ba']⁻¹ ≡ ((-' (  (a , λ ()) *' (b , λ ())  )) ⁻¹) .proj₁
  aux0 = (inv-cong (  (b , λ ()) *' (₁₊ y , λ ())  )  (-'(  ( a , λ ()) *' (b , λ ())  )))  (Eq.trans (*-comm b (₁₊ y)) (Eq.trans (Eq.cong (_* b) (Eq.sym eq)) (Eq.sym (-‿distribˡ-* a b))))
  aux : [ab]⁻¹ + [ba']⁻¹ ≡ ₀
  aux = Eq.trans (Eq.cong ([ab]⁻¹ +_) aux0) (Eq.trans (Eq.cong ([ab]⁻¹ +_) (inv-neg-comm ((a , λ ()) *' (b , λ ())))) (+-inverseʳ [ab]⁻¹))


lemma-A-HH' : ∀ b (nz : b ≢ ₀) ->
  let
  nzp = aux-b≠0⇒ab≠0 ₀ b nz
  nzp' = aux-b≠0⇒ab≠0 ₀ (- b) ((-' (b , nz)) .proj₂)
  in
  
  [ (₀ , b) , nzp ]ᵃ • HH ≈ [ (₀ , - b)  , nzp' ]ᵃ

lemma-A-HH' b@₀ nz = ⊥-elim (nz auto)
lemma-A-HH' b@(₁₊ _) nz = begin
  [ (a , b) , nzp ]ᵃ • HH ≈⟨ sym assoc ⟩
  ([ (a , b) , nzp ]ᵃ • H) • H ≈⟨ cleft lemma-single-qupit-br-A ((a , b) , nzp) H-gen tt ⟩
  (ε • [ (b , ₀) , nzp'' ]ᵃ) • H ≈⟨ trans assoc left-unit ⟩
  [ (b , ₀) , nzp'' ]ᵃ • H ≈⟨ lemma-single-qupit-br-A ((b , ₀) , nzp'') H-gen tt ⟩
  ε • [ (₀ , - b) , nzp' ]ᵃ ≈⟨ left-unit ⟩
  [ (₀ , - b)  , nzp' ]ᵃ ∎
  where
  a = ₀
  nz-b = ((-' (b , nz)) .proj₂)
  nzp = aux-b≠0⇒ab≠0 a b nz
  nzp' = aux-b≠0⇒ab≠0 ₀ (- b) nz-b
  nzp'' = aux-a≠0⇒ab≠0 b ₀ nz

