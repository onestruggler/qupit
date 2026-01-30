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



module N.Pushing.DH (p-2 : ℕ) (p-prime : Prime (2+ p-2))  where

private
  variable
    n : ℕ
    
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


aux-mc1ε : let open PB ((₁₊ n) QRel,_===_) in ⟦ ₁* , ε ⟧ₘ₊ ≈ ε
aux-mc1ε {n} = PB.trans (PB.cong (PB.sym lemma-M1) PB.refl) PB.left-unit
  where
  open Lemmas0 n


aux-b≠0⇒ab≠0 : ∀ (a b : ℤ ₚ) (nz : b ≢ ₀) -> _≢_ {A = ℤ ₚ × ℤ ₚ} (a , b) (₀ , ₀)
aux-b≠0⇒ab≠0 a b nz eq0 = ⊥-elim (nz (Eq.cong proj₂ eq0))

aux-abox-nza : let open PB ((₁₊ n) QRel,_===_) in ∀ a b -> (nz : a ≢ ₀) ->
  let
  a⁻¹ = ((a , nz) ⁻¹) .proj₁
  -b/a = - b * a⁻¹
  in
  [ (a , b) , aux-a≠0⇒ab≠0 a b nz ]ᵃ ≈  ⟦ (a , nz) ⁻¹ , HS^ -b/a ⟧ₘ₊
aux-abox-nza {n} a@₀ b nz = ⊥-elim (nz auto)
aux-abox-nza {n} a@(₁₊ a-1) b nz = PB.refl


aux-abox-nzb : let open PB ((₁₊ n) QRel,_===_) in ∀ b -> (nz : b ≢ ₀) ->
  [ (₀ , b) , aux-b≠0⇒ab≠0 ₀ b nz ]ᵃ ≈  ⟦ (b , nz) ⁻¹ ⟧ₘ
aux-abox-nzb {n} b@₀ nz = ⊥-elim (nz auto)
aux-abox-nzb {n} b@(₁₊ b-1) nz = PB.right-unit


{- old
aux-dbox-nza : let open PB ((₂₊ n) QRel,_===_) in ∀ a b -> (nz : a ≢ ₀) ->
  [ (a , b) ]ᵈ ≈ Ex • CZ^ (- ₁) • [ (a , b) , aux-a≠0⇒ab≠0 a b nz ]ᵃ
aux-dbox-nza {n} a@₀ b nz = ⊥-elim (nz auto)
aux-dbox-nza {n} a@(₁₊ a-1) b nz = PB.refl

aux-dbox-nzb : let open PB ((₂₊ n) QRel,_===_) in ∀ b -> (nz : b ≢ ₀) ->
  [ (₀ , b) ]ᵈ ≈ Ex • CZ^ (- ₁) • [ (₀ , b) , aux-b≠0⇒ab≠0 ₀ b nz ]ᵃ
aux-dbox-nzb {n} b@₀ nz = ⊥-elim (nz auto)
aux-dbox-nzb {n} b@(₁₊ b-1) nz = PB.refl

aux-dbox-nzb' : let open PB ((₂₊ n) QRel,_===_) in ∀ b -> (nz : b ≢ ₀) ->
  [ (₀ , b) ]ᵈ ≈ Ex • CZ^ (- ₁) • ⟦ (b , nz) ⁻¹ ⟧ₘ
aux-dbox-nzb' {n} b@₀ nz = ⊥-elim (nz auto)
aux-dbox-nzb' {n} b@(₁₊ b-1) nz = PB.trans (aux-dbox-nzb b nz) (PB.cong PB.refl (PB.cong PB.refl (aux-abox-nzb b nz)))


aux-dbox'-nzb : let open PB ((₂₊ n) QRel,_===_) in ∀ b -> (nz : b ≢ ₀) ->
  [ (₀ , b) ]ᵈ' ≈ CZ^ (- ₁) • [ (₀ , b) , aux-b≠0⇒ab≠0 ₀ b nz ]ᵃ ↑ • Ex
aux-dbox'-nzb {n} b@₀ nz = ⊥-elim (nz auto)
aux-dbox'-nzb {n} b@(₁₊ b-1) nz = PB.refl

aux-dbox'-nzb' : let open PB ((₂₊ n) QRel,_===_) in ∀ b -> (nz : b ≢ ₀) ->
  [ (₀ , b) ]ᵈ' ≈ CZ^ (- ₁) • ⟦ (b , nz) ⁻¹ ⟧ₘ ↑ • Ex
aux-dbox'-nzb' {n} b@₀ nz = ⊥-elim (nz auto)
aux-dbox'-nzb' {n} b@(₁₊ b-1) nz = PB.trans (aux-dbox'-nzb b nz) (PB.cong PB.refl (PB.cong (lemma-cong↑ _ _ (aux-abox-nzb b nz)) PB.refl))


aux-dbox-nza' : let open PB ((₂₊ n) QRel,_===_) in ∀ a b -> (nz : a ≢ ₀) ->
  let
  a⁻¹ = ((a , nz) ⁻¹) .proj₁
  -b/a = - b * a⁻¹
  in
  [ (a , b) ]ᵈ ≈ Ex • CZ^ (- ₁) • ⟦ (a , nz) ⁻¹ , HS^ -b/a ⟧ₘ₊
aux-dbox-nza' {n} a@₀ b nz = ⊥-elim (nz auto)
aux-dbox-nza' {n} a@(₁₊ a-1) b nz = PB.trans (aux-dbox-nza a b nz) (PB.cong PB.refl (PB.cong PB.refl (aux-abox-nza a b nz)))



aux-bbox-nza : let open PB ((₂₊ n) QRel,_===_) in ∀ a b -> (nz : a ≢ ₀) ->
  [ (a , b) ]ᵇ ≈ Ex • CX • [ (a , b) , aux-a≠0⇒ab≠0 a b nz ]ᵃ ↑
aux-bbox-nza {n} a@₀ b nz = ⊥-elim (nz auto)
aux-bbox-nza {n} a@(₁₊ a-1) b nz = PB.refl

aux-bbox-nzb : let open PB ((₂₊ n) QRel,_===_) in ∀ b -> (nz : b ≢ ₀) ->
  [ (₀ , b) ]ᵇ ≈ Ex • CX • [ (₀ , b) , aux-b≠0⇒ab≠0 ₀ b nz ]ᵃ ↑
aux-bbox-nzb {n} b@₀ nz = ⊥-elim (nz auto)
aux-bbox-nzb {n} b@(₁₊ b-1) nz = PB.refl

aux-bbox-nzb' : let open PB ((₂₊ n) QRel,_===_) in ∀ b -> (nz : b ≢ ₀) ->
  [ (₀ , b) ]ᵇ ≈ Ex • CX • ⟦ (b , nz) ⁻¹ ⟧ₘ ↑
aux-bbox-nzb' {n} b@₀ nz = ⊥-elim (nz auto)
aux-bbox-nzb' {n} b@(₁₊ b-1) nz = PB.trans (aux-bbox-nzb b nz) (PB.cong PB.refl (PB.cong PB.refl (lemma-cong↑ _ _ (aux-abox-nzb b nz))))

aux-bbox-nza' : let open PB ((₂₊ n) QRel,_===_) in ∀ a b -> (nz : a ≢ ₀) ->
  let
  a⁻¹ = ((a , nz) ⁻¹) .proj₁
  -b/a = - b * a⁻¹
  in
  [ (a , b) ]ᵇ ≈ Ex • CX • ⟦ (a , nz) ⁻¹ , HS^ -b/a ⟧ₘ₊ ↑ 
aux-bbox-nza' {n} a@₀ b nz = ⊥-elim (nz auto)
aux-bbox-nza' {n} a@(₁₊ a-1) b nz = PB.trans (aux-bbox-nza a b nz) (PB.cong PB.refl (PB.cong PB.refl (lemma-cong↑ _ _ (aux-abox-nza a b nz))))





dir-of-DH : D -> Word (Gen (₁₊ n))
dir-of-DH (₀ , ₀) = H
dir-of-DH (₀ , ₁₊ _) = ε
dir-of-DH (₁₊ _ , ₀) = ε
dir-of-DH (a@(₁₊ _) , b@(₁₊ _)) = S^ [ab]⁻¹
  where
  [ab]⁻¹* = (  (a , λ ()) *' (b , λ ())  ) ⁻¹
  [ab]⁻¹ = [ab]⁻¹* .proj₁


d-of-DH : D -> D
d-of-DH (₀ , ₀) = ₀ , ₀
d-of-DH (₀ , b@(₁₊ _)) = b , ₀
d-of-DH (a@(₁₊ _) , ₀) = ₀ , - a
d-of-DH (a@(₁₊ _) , b@(₁₊ _)) = (b , - a)

aux-DH : let open PB ((₂₊ n) QRel,_===_) in

  ∀ d ->
  let
  d' = d-of-DH d
  w = dir-of-DH d
  in
  [ d ]ᵈ • H ≈ w ↑ • [ d' ]ᵈ

aux-DH {n} d@(₀ , b@(₁₊ _)) = claim
  where
  open PB ((₂₊ n) QRel,_===_)  
  open PP ((₂₊ n) QRel,_===_)
  open SR word-setoid
  open Lemmas0 (₁₊ n)
  open Pattern-Assoc
  open Lemmas-2Q n

  b* : ℤ* ₚ
  b* = (b , λ ())
  nz : b ≢ ₀
  nz = λ ()

  b⁻¹ : ℤ* ₚ
  b⁻¹ = b* ⁻¹
  b⁻¹' = b⁻¹ .proj₁

  w = ε
  d' = (b , ₀)
  claim : [ d ]ᵈ • H ≈ w ↑ • [ d' ]ᵈ
  claim = begin
    ([ d ]ᵈ • H) ≈⟨ ( (cleft {!!} b nz)) ⟩
    ((Ex • CZ^ (- ₁) • ⟦ (b , nz) ⁻¹ ⟧ₘ) • H) ≈⟨ ( trans assoc (cong refl assoc)) ⟩
    (Ex • CZ^ (- ₁) • ⟦ (b , nz) ⁻¹ ⟧ₘ • H) ≈⟨ ( (cright cright cright sym right-unit)) ⟩
    (Ex • CZ^ (- ₁) • ⟦ (b , nz) ⁻¹ ⟧ₘ • H • ε) ≈⟨ ( (cright cright cright cright sym (refl' (Eq.cong (S^) (Eq.trans (Eq.cong (_* b⁻¹') -0#≈0#) (*-zeroˡ b⁻¹')))))) ⟩
    (Ex • CZ^ (- ₁) • ⟦ (b , nz) ⁻¹ ⟧ₘ • H • S^ (- ₀ * b⁻¹')) ≈⟨ ( sym ({!!} b ₀ nz)) ⟩
    [ (b , ₀) ]ᵈ  ≈⟨ sym left-unit ⟩
    ε • [ (b , ₀) ]ᵈ  ∎


aux-DH {n} d@(a@(₁₊ _) , b@(₁₊ _)) = trans claim claim'
  where
  a⁻¹ = ((a , λ ()) ⁻¹) .proj₁
  -a⁻¹ = ((-'(a , λ ())) ⁻¹) .proj₁
  -b/a = - b * a⁻¹
  b/a = - b * -a⁻¹

  x = -b/a
  nz : x ≢ ₀
  nz = (-' (b , λ ()) *' ((a , λ ()) ⁻¹)) .proj₂
  y = a⁻¹
  nzy : y ≢ ₀
  nzy = ((a , λ ()) ⁻¹) .proj₂
  
  y⁻¹ = ((y , nzy) ⁻¹) .proj₁
  x⁻¹ = ((x , nz) ⁻¹) .proj₁
  x⁻¹⁻¹ = (((x , nz) ⁻¹) ⁻¹) .proj₁
  y⁻¹⁻¹ = (((y , nzy) ⁻¹) ⁻¹) .proj₁
  -x⁻¹ = - x⁻¹
  mnz = (-' (x , nz)) .proj₂
  -y/x' = (((y , nzy) *' ((x , nz) ⁻¹)) *' -'₁)
  -y/x = -y/x' .proj₁
  a' = - x * y⁻¹
  b' = - y⁻¹
  
  nza' = (-' (x , nz) *' (y , nzy) ⁻¹) .proj₂
  a'⁻¹ = ((a' , nza') ⁻¹) .proj₁
  -b'/a' = - b' * a'⁻¹

  aux1 : -y/x ≡ a'⁻¹
  aux1 = Eq.sym ( begin
    ((- x * y⁻¹ , nza') ⁻¹) .proj₁ ≡⟨ (inv-distrib ((- x , mnz)) (((y , nzy) ⁻¹))) ⟩
    (((- x , mnz) ⁻¹) .proj₁ * y⁻¹⁻¹) ≡⟨ Eq.cong (\ xx -> (((- x , mnz) ⁻¹) .proj₁ * xx)) (inv-involutive (y , nzy)) ⟩
    (((- x , mnz) ⁻¹) .proj₁ * y) ≡⟨ Eq.cong (\ xx -> (xx * y)) (inv-neg-comm (x , nz)) ⟩
    ((-' (x , nz) ⁻¹) .proj₁ * y) ≡⟨ (*-comm -x⁻¹ y) ⟩
    (y * -x⁻¹) ≡⟨ Eq.sym (-‿distribʳ-* y x⁻¹) ⟩
    - (y * x⁻¹) ≡⟨ Eq.sym (-1*x≈-x ((y * x⁻¹))) ⟩
    - ₁ * (y * x⁻¹) ≡⟨ *-comm (- ₁) ((y * x⁻¹)) ⟩
    (y * x⁻¹) * - ₁ ≡⟨ auto ⟩
    -y/x ∎
    )
    where
    open ≡-Reasoning
  
  aux2a : -b'/a' ≡ -x⁻¹
  aux2a = begin
    -b'/a' ≡⟨ Eq.cong (_* ((- x * y⁻¹ , nza') ⁻¹) .proj₁) ( -‿involutive y⁻¹) ⟩
    y⁻¹ * ((- x * y⁻¹ , nza') ⁻¹) .proj₁ ≡⟨ Eq.cong (y⁻¹ *_) (inv-distrib ((- x , mnz)) (((y , nzy) ⁻¹))) ⟩
    y⁻¹ * (((- x , mnz) ⁻¹) .proj₁ * y⁻¹⁻¹) ≡⟨ Eq.cong (\ xx -> y⁻¹ * (((- x , mnz) ⁻¹) .proj₁ * xx)) (inv-involutive (y , nzy)) ⟩
    y⁻¹ * (((- x , mnz) ⁻¹) .proj₁ * y) ≡⟨ Eq.cong (\ xx -> y⁻¹ * (xx * y)) (inv-neg-comm (x , nz)) ⟩
    y⁻¹ * ((-' (x , nz) ⁻¹) .proj₁ * y) ≡⟨ Eq.cong (y⁻¹ *_) (*-comm -x⁻¹ y) ⟩
    y⁻¹ * (y * -x⁻¹) ≡⟨ Eq.sym (*-assoc (y⁻¹) y -x⁻¹) ⟩
    y⁻¹ * y * -x⁻¹ ≡⟨ Eq.cong (_* -x⁻¹) (lemma-⁻¹ˡ y {{nztoℕ {y = y} {neq0 = nzy}}}) ⟩
    ₁ * -x⁻¹ ≡⟨ *-identityˡ -x⁻¹ ⟩
    -x⁻¹ ∎
    where
    open ≡-Reasoning


  w = S^ (-x⁻¹ * (y * y))
  d' = (a' , b')

  [ab]⁻¹* = (  (a , λ ()) *' (b , λ ())  ) ⁻¹
  [ab]⁻¹ = [ab]⁻¹* .proj₁

  w' = S^ [ab]⁻¹
  d'' = (b , - a)

  aux'-2 : a' ≡ b
  aux'-2 = begin
    - x * y⁻¹ ≡⟨ Eq.cong (- x *_) (inv-involutive (a , (λ ()))) ⟩
    - -b/a * a ≡⟨ Eq.cong (_* a) (-‿distribˡ-* (- b) a⁻¹) ⟩
    (- - b * a⁻¹) * a ≡⟨ Eq.cong (\ xx -> (xx * a⁻¹) * a) (-‿involutive b) ⟩
    (b * a⁻¹) * a ≡⟨ *-assoc b a⁻¹ a ⟩
    b * (a⁻¹ * a) ≡⟨ Eq.cong (b *_) (lemma-⁻¹ˡ a {{nztoℕ {y = a} {neq0 = λ ()}}}) ⟩
    b * ₁ ≡⟨ *-identityʳ b ⟩
    b ∎
    where
    open ≡-Reasoning

  aux'-3 : b' ≡ - a
  aux'-3 = begin
    - y⁻¹ ≡⟨ Eq.cong -_ (inv-involutive (a , (λ ()))) ⟩
    - a ∎
    where
    open ≡-Reasoning

  b* : ℤ* ₚ
  b* = (b , λ ())
  b⁻¹ = (b* ⁻¹) .proj₁
  
  a* : ℤ* ₚ
  a* = (a , λ ())
  
  aux'-1 : -x⁻¹ * (y * y) ≡ [ab]⁻¹
  aux'-1 = begin
    -x⁻¹ * (y * y) ≡⟨ Eq.cong (\ xx -> - xx * (y * y)) (inv-distrib (-' b*) (a* ⁻¹)) ⟩
    - (((-' b*) ⁻¹) .proj₁ * (a* ⁻¹ ⁻¹) .proj₁) * (a⁻¹ * a⁻¹) ≡⟨ Eq.cong (_* (a⁻¹ * a⁻¹)) (-‿distribˡ-* (((-' b*) ⁻¹) .proj₁) ((a* ⁻¹ ⁻¹) .proj₁)) ⟩
    (- ((-' b*) ⁻¹) .proj₁ * (a* ⁻¹ ⁻¹) .proj₁) * (a⁻¹ * a⁻¹) ≡⟨ Eq.cong₂ (\ xx yy -> (xx * yy) * (a⁻¹ * a⁻¹)) (Eq.cong -_ (inv-neg-comm b*)) (inv-involutive a*) ⟩
    (- - (b⁻¹) * a) * (a⁻¹ * a⁻¹) ≡⟨ Eq.cong (\ xx -> (xx * a) * (a⁻¹ * a⁻¹)) (-‿involutive ((b⁻¹))) ⟩
    ((b⁻¹) * a) * (a⁻¹ * a⁻¹) ≡⟨ *-assoc b⁻¹ a (a⁻¹ * a⁻¹) ⟩
    (b⁻¹) * (a * (a⁻¹ * a⁻¹)) ≡⟨ Eq.cong ((b⁻¹) *_) (Eq.sym (*-assoc a a⁻¹ a⁻¹)) ⟩
    (b⁻¹) * ((a * a⁻¹) * a⁻¹) ≡⟨ Eq.cong (\ xx -> (b⁻¹) * (xx * a⁻¹)) (lemma-⁻¹ʳ a {{nztoℕ {y = a} {neq0 = λ ()}}} ) ⟩
    (b⁻¹) * (₁ * a⁻¹) ≡⟨ Eq.cong ((b⁻¹) *_) (*-identityˡ ((a⁻¹))) ⟩
    (b⁻¹) * a⁻¹ ≡⟨ *-comm ((b⁻¹)) a⁻¹ ⟩
    a⁻¹ * (b⁻¹) ≡⟨ Eq.sym (inv-distrib a* b*) ⟩
    [ab]⁻¹ ∎
    where
    open ≡-Reasoning


  open PB ((₂₊ n) QRel,_===_)  
  open PP ((₂₊ n) QRel,_===_)
  open SR word-setoid
  open Pattern-Assoc
  open Lemmas0 (₁₊ n)

  claim' : S^ (-x⁻¹ * (y * y)) ↑ • [ a' , b' ]ᵈ ≈ w' ↑ • [ d'' ]ᵈ
  claim' = begin
    S^ (-x⁻¹ * (y * y)) ↑ • [ a' , b' ]ᵈ ≈⟨ cong (refl' (Eq.cong (\ xx -> S^ xx ↑) aux'-1)) (refl' (Eq.cong₂ (\ xx yy -> [ ( xx , yy) ]ᵈ ) aux'-2 aux'-3)) ⟩
    w' ↑ • [ d'' ]ᵈ ∎

  claim : [ d ]ᵈ • H ≈ w ↑ • [ d' ]ᵈ
  claim = begin
    [ d ]ᵈ • H ≈⟨ special-assoc (□ ^ 3 • □) (□ ^ 4) {!!} ⟩
    (Ex • CZ^ (- ₁) • [ (a , b) , (λ ()) ]ᵃ • H) ≈⟨ ( cright cright sym refl) ⟩
    (Ex • CZ^ (- ₁) • (ZM ((a , λ ()) ⁻¹) • H • S^ -b/a) • H) ≈⟨ ( cright cright special-assoc (□ ^ 3 • □) (□ ^ 2 • □ ^ 2) auto) ⟩
    (Ex • CZ^ (- ₁) • (ZM ((a , λ ()) ⁻¹) • H) • S^ -b/a • H) ≈⟨ ( cright cright assoc) ⟩
    (Ex • CZ^ (- ₁) • ZM ((a , λ ()) ⁻¹) • H • S^ -b/a • H) ≈⟨ ( cright cright derived-7 x y nz nzy) ⟩
    (Ex • CZ^ (- ₁) • S^ (-x⁻¹ * (y * y)) • ZM -y/x' • (H • S^ -x⁻¹)) ≈⟨ ( cright sym assoc) ⟩
    (Ex • (CZ^ (- ₁) • S^ (-x⁻¹ * (y * y))) • ZM -y/x' • (H • S^ -x⁻¹)) ≈⟨ ( cright cleft word-comm (toℕ (- ₁)) (toℕ (-x⁻¹ * (y * y))) (axiom comm-CZ-S↓)) ⟩
    (Ex • (S^ (-x⁻¹ * (y * y)) • CZ^ (- ₁)) • ZM -y/x' • (H • S^ -x⁻¹)) ≈⟨ ( special-assoc (□ • □ ^ 2 • □) (□ ^ 2 • □ ^ 2) auto) ⟩
    ((Ex • S^ (-x⁻¹ * (y * y))) • CZ^ (- ₁) • ZM -y/x' • (H • S^ -x⁻¹)) ≈⟨ ( cleft lemma-Induction lemma-Ex-S (toℕ (-x⁻¹ * (y * y)))) ⟩
    ((S ↑ ^ toℕ (-x⁻¹ * (y * y)) • Ex) • CZ^ (- ₁) • ZM -y/x' • (H • S^ -x⁻¹)) ≈⟨ ( cleft cleft refl' (lemma-^-↑ S ( toℕ (-x⁻¹ * (y * y))))) ⟩
    (((S ^ toℕ (-x⁻¹ * (y * y))) ↑ • Ex) • CZ^ (- ₁) • ZM -y/x' • (H • S^ -x⁻¹)) ≈⟨ assoc ⟩
    S^ (-x⁻¹ * (y * y)) ↑ • (Ex • CZ^ (- ₁) • ZM -y/x' • (H • S^ -x⁻¹)) ≈⟨ (cright  cright cright cong (aux-MM (-y/x' .proj₂) (((a' , nza') ⁻¹) .proj₂) aux1) (cright refl' (Eq.cong S^ (Eq.sym aux2a)))) ⟩
    S^ (-x⁻¹ * (y * y)) ↑ • (Ex • CZ^ (- ₁) • ⟦ (a' , nza') ⁻¹ , HS^ -b'/a' ⟧ₘ₊) ≈⟨ (cright  sym ({!!} a' b' nza')) ⟩
    S^ (-x⁻¹ * (y * y)) ↑ • [ a' , b' ]ᵈ ∎

  

aux-DH {n} d@(₀ , ₀) = PB.sym {!!}


aux-DH {n} d@(a@(₁₊ _) , b@₀) = claim
  where
  a⁻¹ = ((a , λ ()) ⁻¹) .proj₁
  -a⁻¹ = ((-'(a , λ ())) ⁻¹) .proj₁
  -b/a = - b * a⁻¹
  b/a = - b * -a⁻¹
  aux : -b/a ≡ ₀
  aux = begin
    (- b * a⁻¹) ≡⟨ Eq.cong (_* a⁻¹) -0#≈0# ⟩
    (₀ * a⁻¹) ≡⟨ *-zeroˡ a⁻¹ ⟩
    ₀ ∎
    where
    open ≡-Reasoning
    
  aux2 : ((a , λ ()) ⁻¹ *' -'₁) .proj₁ ≡ ((-' (a , λ ())) ⁻¹) .proj₁
  aux2 = begin
    ((a , λ ()) ⁻¹ *' -'₁) .proj₁ ≡⟨ *-comm a⁻¹ (- ₁) ⟩
    (-'₁ *' (a , λ ()) ⁻¹) .proj₁ ≡⟨ -1*x≈-x a⁻¹ ⟩
    (-' (a , λ ()) ⁻¹) .proj₁ ≡⟨ Eq.sym (inv-neg-comm (a , (λ ()))) ⟩
    ((-' (a , λ ())) ⁻¹) .proj₁ ∎
    where
    open ≡-Reasoning

  
  open PB ((₂₊ n) QRel,_===_)  
  open PP ((₂₊ n) QRel,_===_)
  open SR word-setoid
  open Pattern-Assoc
  open Lemmas0 (₁₊ n)

  w = ε
  d' = (₀ , - a)
  
  claim : [ d ]ᵈ • H ≈ w ↑ • ([ d' ]ᵈ)
  claim = begin
    ([ d ]ᵈ • H) ≈⟨ ( trans assoc (cong refl {!!})) ⟩
    (Ex • CZ^ (- ₁) • [ (a , b) , (λ ()) ]ᵃ • H) ≈⟨ ( cright cright sym refl) ⟩
    (Ex • CZ^ (- ₁) • (ZM ((a , λ ()) ⁻¹) • H • S^ -b/a) • H) ≈⟨ ( cright cright special-assoc (□ ^ 3 • □) (□ ^ 2 • □ ^ 2) auto) ⟩
    (Ex • CZ^ (- ₁) • (ZM ((a , λ ()) ⁻¹) • H) • S^ -b/a • H) ≈⟨ ( cright cright assoc) ⟩
    (Ex • CZ^ (- ₁) • ZM ((a , λ ()) ⁻¹) • H • S^ -b/a • H) ≈⟨ ( cright cright cright (cright cleft refl' (Eq.cong S^ aux))) ⟩
    (Ex • CZ^ (- ₁) • ZM ((a , λ ()) ⁻¹) • H • ε • H) ≈⟨ ( cright cright cright cong refl left-unit) ⟩
    (Ex • CZ^ (- ₁) • ZM ((a , λ ()) ⁻¹) • H • H) ≈⟨ ( cright cright cright lemma-HH-M-1) ⟩
    (Ex • CZ^ (- ₁) • ZM ((a , λ ()) ⁻¹) • ZM -'₁) ≈⟨ ( cright cright axiom (M-mul ((a , λ ()) ⁻¹) -'₁)) ⟩
    (Ex • CZ^ (- ₁) • ZM ((a , λ ()) ⁻¹ *' -'₁)) ≈⟨ ( cright  cright aux-MM (((a , λ ()) ⁻¹ *' -'₁) .proj₂) (((-' (a , λ ())) ⁻¹) .proj₂) aux2 ) ⟩
    (Ex • CZ^ (- ₁) • ZM ((-' (a , λ ())) ⁻¹)) ≈⟨ ( sym ({!!} (- a) (((-' (a , λ ())) ) .proj₂))) ⟩
    ([ ₀ , - a ]ᵈ) ≈⟨ sym left-unit ⟩
    ε • ([ ₀ , - a ]ᵈ)  ∎


{-

dir-of-DH^2 : D -> Word (Gen (₁₊ n))
dir-of-DH^2 (₀ , ₀) = H ^ 2
dir-of-DH^2 (₀ , ₁₊ _) = ε
dir-of-DH^2 (₁₊ _ , ₀) = ε
dir-of-DH^2 (a@(₁₊ _) , b@(₁₊ _)) = ε
  where
  [ab]⁻¹* = (  (a , λ ()) *' (b , λ ()) ) ⁻¹
  [ab]⁻¹ = [ab]⁻¹* .proj₁


d-of-DH^2 : D -> D
d-of-DH^2 (₀ , ₀) = ₀ , ₀
d-of-DH^2 (₀ , b@(₁₊ _)) = ₀ , - b
d-of-DH^2 (a@(₁₊ _) , ₀) = - a , ₀
d-of-DH^2 (a@(₁₊ _) , b@(₁₊ _)) = (- a , - b)


aux-mnz : ∀ (b : ℤ ₚ) -> (nz : b ≢ ₀) -> ∃ \ x -> - b ≡ ₁₊ x
aux-mnz b nz with - b | inspect -_ b
... | ₀ | [ eq ]' = ⊥-elim ((-' (b , nz)) .proj₂ eq)
... | ₁₊ x' | [ eq ]' = x' , auto

aux-DH^2 : let open PB ((₂₊ n) QRel,_===_) in

  ∀ d ->
  let
  d' = d-of-DH^2 d
  w = dir-of-DH^2 d
  in
  [ d ]ᵈ • H ^ 2 ≈ w ↑ • [ d' ]ᵈ

aux-DH^2 {n} d@(₀ , ₀) = {!!} -- lemma-Induction (PB.sym lemma-comm-Ex-H-n) 2
aux-DH^2 {n} d@(₀ , b@(₁₊ _)) = begin
  [ ₀ , b ]ᵈ • H • H ≈⟨ sym assoc ⟩
  ([ ₀ , b ]ᵈ • H) • H ≈⟨ (cleft aux-DH (₀ , b)) ⟩
  (ε • [ b , ₀ ]ᵈ) • H ≈⟨ (cleft left-unit) ⟩
  [ b , ₀ ]ᵈ • H ≈⟨ aux-DH (b , ₀) ⟩
  (ε ↑) • [ ₀ , - b ]ᵈ ∎
  where
  open PB ((₂₊ n) QRel,_===_)  
  open PP ((₂₊ n) QRel,_===_)
  open SR word-setoid
  open Pattern-Assoc
  open Lemmas0 (₁₊ n)
aux-DH^2 {n} d@(a@(₁₊ _) , ₀) = begin
  [ d ]ᵈ • H ^ 2 ≈⟨ sym assoc ⟩
  ([ d ]ᵈ • H) • H ≈⟨ (cleft aux-DH d) ⟩
  (ε • [ ₀ , - a ]ᵈ) • H ≈⟨ (cleft left-unit) ⟩
  ([ ₀ , - a ]ᵈ) • H ≈⟨ aux-DH (₀ , - a) ⟩
  (dir-of-DH (₀ , - a)) ↑ • [ d-of-DH (₀ , - a) ]ᵈ ≈⟨ refl' (Eq.cong (\ xx -> (dir-of-DH (₀ , xx)) ↑ • [ d-of-DH (₀ , xx) ]ᵈ) eqx) ⟩
  (dir-of-DH (₀ , ₁₊ x)) ↑ • [ d-of-DH (₀ , ₁₊ x) ]ᵈ ≈⟨ refl ⟩
  ε ↑ • [ ₁₊ x , ₀ ]ᵈ ≈⟨ refl' (Eq.cong (\ xx -> ε ↑ • [ xx , ₀ ]ᵈ) (Eq.sym eqx)) ⟩
  ε ↑ • [ - a , ₀ ]ᵈ ∎
  where
  open PB ((₂₊ n) QRel,_===_)  
  open PP ((₂₊ n) QRel,_===_)
  open SR word-setoid
  open Pattern-Assoc
  open Lemmas0 (₁₊ n)
  ma = aux-mnz a λ ()
  x = ma .proj₁
  eqx = ma .proj₂


aux-DH^2 {n} d@(a@(₁₊ _) , b@(₁₊ _)) = begin
  [ d ]ᵈ • H ^ 2 ≈⟨ sym assoc ⟩
  ([ d ]ᵈ • H) • H ≈⟨ (cleft aux-DH d) ⟩
  (S^ [ab]⁻¹ ↑ • [ b , - a ]ᵈ) • H ≈⟨ assoc ⟩
  S^ [ab]⁻¹ ↑ • ([ b , - a ]ᵈ) • H ≈⟨ cright aux-DH (b , - a) ⟩
  S^ [ab]⁻¹ ↑ • ((dir-of-DH (b , - a)) ↑ • [ d-of-DH (b , - a) ]ᵈ) ≈⟨ cright refl' (Eq.cong (\ xx -> (dir-of-DH (b , xx)) ↑ • [ d-of-DH (b , xx) ]ᵈ) eqx) ⟩
  S^ [ab]⁻¹ ↑ • ((dir-of-DH (b , ₁₊ x)) ↑ • [ d-of-DH (b , ₁₊ x) ]ᵈ) ≈⟨ refl ⟩
  S^ [ab]⁻¹ ↑  • (S^ [ba]⁻¹ ↑ • [ ₁₊ x , - b ]ᵈ) ≈⟨ cright refl' (Eq.cong (\ xx -> S^ [ba]⁻¹ ↑ • [ xx , - b ]ᵈ) (Eq.sym eqx)) ⟩
  S^ [ab]⁻¹ ↑ • (S^ [ba]⁻¹ ↑ • [ - a , - b ]ᵈ) ≈⟨ sym assoc ⟩
  (S^ [ab]⁻¹ ↑ • S^ [ba]⁻¹ ↑) • [ - a , - b ]ᵈ ≈⟨  (cleft lemma-cong↑ _ _ (L0.lemma-S^k+l [ab]⁻¹ [ba]⁻¹)) ⟩
  S^ ([ab]⁻¹ + [ba]⁻¹) ↑ • [ - a , - b ]ᵈ ≈⟨ (cleft refl' (Eq.cong (\ xx -> S^ xx ↑) aux2)) ⟩
  ε ↑ • [ - a , - b ]ᵈ ∎
  where
  ma = aux-mnz a λ ()
  x = ma .proj₁
  eqx = ma .proj₂
  [ab]⁻¹* = (  (a , λ ()) *' (b , λ ())  ) ⁻¹
  [ab]⁻¹ = [ab]⁻¹* .proj₁

  [ba]⁻¹* = (  (b , λ ()) *' (₁₊ x , λ ())  ) ⁻¹
  [ba]⁻¹ = [ba]⁻¹* .proj₁
  aux : [ba]⁻¹ ≡ - [ab]⁻¹
  aux = begin
    ((  (b , λ ()) *' (₁₊ x , λ ())  ) ⁻¹) .proj₁ ≡⟨ inv-distrib (b , λ ()) (₁₊ x , λ ()) ⟩
    (  (b , λ ()) ⁻¹) .proj₁  * (((₁₊ x , λ ())  ) ⁻¹) .proj₁ ≡⟨ Eq.cong (\ xx -> (  (b , λ ()) ⁻¹) .proj₁  * xx) (inv-cong ((₁₊ x , λ ())) (-' (a , λ ())) (Eq.sym eqx)) ⟩
    (  (b , λ ()) ⁻¹) .proj₁  * (( -' (a , λ ())  ) ⁻¹) .proj₁ ≡⟨ *-comm ((  (b , λ ()) ⁻¹) .proj₁) ((( -' (a , λ ())  ) ⁻¹) .proj₁) ⟩
    (( -' (a , λ ())  ) ⁻¹) .proj₁ * (  (b , λ ()) ⁻¹) .proj₁  ≡⟨ Eq.cong (_* (  (b , λ ()) ⁻¹) .proj₁) (inv-neg-comm (a , λ ())) ⟩
    - (( (a , λ ())  ) ⁻¹) .proj₁ * (  (b , λ ()) ⁻¹) .proj₁  ≡⟨ Eq.sym (-‿distribˡ-* ((( (a , λ ())  ) ⁻¹) .proj₁) ((  (b , λ ()) ⁻¹) .proj₁)) ⟩
    - ((( (a , λ ())  ) ⁻¹) .proj₁ * (  (b , λ ()) ⁻¹) .proj₁)  ≡⟨ Eq.cong -_ (Eq.sym (inv-distrib (a , λ ()) (b , λ ()))) ⟩
    - [ab]⁻¹ ∎
    where
    open ≡-Reasoning
  aux2 : [ab]⁻¹ + [ba]⁻¹ ≡ ₀
  aux2 = begin
    [ab]⁻¹ + [ba]⁻¹ ≡⟨ Eq.cong ([ab]⁻¹ +_) aux ⟩
    [ab]⁻¹ + - [ab]⁻¹ ≡⟨ +-inverseʳ [ab]⁻¹ ⟩
    ₀ ∎
    where
    open ≡-Reasoning

  open PB ((₂₊ n) QRel,_===_)  
  open PP ((₂₊ n) QRel,_===_)
  open SR word-setoid
  open Pattern-Assoc
  open Lemmas0 (₁₊ n)
  module L0 = Lemmas0 n






dir-of-DH^3 : D -> Word (Gen (₁₊ n))
dir-of-DH^3 (₀ , ₀) = H ^ 3
dir-of-DH^3 (₀ , ₁₊ _) = ε
dir-of-DH^3 (₁₊ _ , ₀) = ε
dir-of-DH^3 (a@(₁₊ _) , b@(₁₊ _)) = S^ [ab]⁻¹
  where
  [ab]⁻¹* = (  (a , λ ()) *' (b , λ ())  ) ⁻¹
  [ab]⁻¹ = [ab]⁻¹* .proj₁


d-of-DH^3 : D -> D
d-of-DH^3 (₀ , ₀) = ₀ , ₀
d-of-DH^3 (₀ , b@(₁₊ _)) = - b , ₀
d-of-DH^3 (a@(₁₊ _) , ₀) = ₀ , a
d-of-DH^3 (a@(₁₊ _) , b@(₁₊ _)) = (- b , a)


aux-DH^3 : let open PB ((₂₊ n) QRel,_===_) in

  ∀ d ->
  let
  d' = d-of-DH^3 d
  w = dir-of-DH^3 d
  in
  [ d ]ᵈ • H ^ 3 ≈ w ↑ • [ d' ]ᵈ

aux-DH^3 {n} d@(₀ , ₀) = {!!} -- lemma-Induction (PB.sym lemma-comm-Ex-H-n) 3


aux-DH^3 {n} d@(₀ , b@(₁₊ _)) = begin
  [ ₀ , b ]ᵈ • H ^ 3 ≈⟨ sym assoc ⟩
  ([ ₀ , b ]ᵈ • H) • H ^ 2 ≈⟨ (cleft aux-DH (₀ , b)) ⟩
  (ε • [ b , ₀ ]ᵈ) • H ^ 2 ≈⟨ (cleft left-unit) ⟩
  [ b , ₀ ]ᵈ • H ^ 2 ≈⟨ aux-DH^2 (b , ₀) ⟩
  (ε ↑) • [ - b , ₀ ]ᵈ ∎
  where
  open PB ((₂₊ n) QRel,_===_)  
  open PP ((₂₊ n) QRel,_===_)
  open SR word-setoid
  open Pattern-Assoc
  open Lemmas0 (₁₊ n)

aux-DH^3 {n} d@(a@(₁₊ _) , ₀) = begin
  [ d ]ᵈ • H ^ 3 ≈⟨ sym assoc ⟩
  ([ d ]ᵈ • H) • H ^ 2 ≈⟨ (cleft aux-DH d) ⟩
  (ε • [ ₀ , - a ]ᵈ) • H ^ 2 ≈⟨ (cleft left-unit) ⟩
  ([ ₀ , - a ]ᵈ) • H ^ 2 ≈⟨ aux-DH^2 (₀ , - a) ⟩
  (dir-of-DH^2 (₀ , - a)) ↑ • [ d-of-DH^2 (₀ , - a) ]ᵈ ≈⟨ refl' (Eq.cong (\ xx -> (dir-of-DH^2 (₀ , xx)) ↑ • [ d-of-DH^2 (₀ , xx) ]ᵈ) eqx) ⟩
  (dir-of-DH^2 (₀ , ₁₊ x)) ↑ • [ d-of-DH^2 (₀ , ₁₊ x) ]ᵈ ≈⟨ refl ⟩
  ε ↑ • [ ₀ , - (₁₊ x) ]ᵈ ≈⟨ refl' (Eq.cong (\ xx -> ε ↑ • [ ₀ , - xx ]ᵈ) (Eq.sym eqx)) ⟩
  ε ↑ • [ ₀ , - - a ]ᵈ ≡⟨ Eq.cong (\ xx -> ε ↑ • [ ₀ , xx ]ᵈ) (-‿involutive a) ⟩
  ε ↑ • [ ₀ , a ]ᵈ ∎
  where
  open PB ((₂₊ n) QRel,_===_)  
  open PP ((₂₊ n) QRel,_===_)
  open SR word-setoid
  open Pattern-Assoc
  open Lemmas0 (₁₊ n)
  ma = aux-mnz a λ ()
  x = ma .proj₁
  eqx = ma .proj₂


aux-DH^3 {n} d@(a@(₁₊ _) , b@(₁₊ _)) = begin
  [ d ]ᵈ • H ^ 3 ≈⟨ sym assoc ⟩
  ([ d ]ᵈ • H) • H ^ 2 ≈⟨ (cleft aux-DH d) ⟩
  (S^ [ab]⁻¹ ↑ • [ b , - a ]ᵈ) • H ^ 2 ≈⟨ assoc ⟩
  S^ [ab]⁻¹ ↑ • ([ b , - a ]ᵈ) • H ^ 2 ≈⟨ cright aux-DH^2 (b , - a) ⟩
  S^ [ab]⁻¹ ↑ • ((dir-of-DH^2 (b , - a)) ↑ • [ d-of-DH^2 (b , - a) ]ᵈ) ≈⟨ cright refl' (Eq.cong (\ xx -> (dir-of-DH^2 (b , xx)) ↑ • [ d-of-DH^2 (b , xx) ]ᵈ) eqx) ⟩
  S^ [ab]⁻¹ ↑ • ((dir-of-DH^2 (b , ₁₊ x)) ↑ • [ d-of-DH^2 (b , ₁₊ x) ]ᵈ) ≈⟨ refl ⟩
  S^ [ab]⁻¹ ↑  • (ε ↑ • [ - b ,  - (₁₊ x) ]ᵈ) ≈⟨ cright refl' (Eq.cong (\ xx -> ε ↑ • [ - b , - xx  ]ᵈ) (Eq.sym eqx)) ⟩
  S^ [ab]⁻¹ ↑ • (ε ↑ • [ - b  ,  - - a ]ᵈ) ≈⟨ sym assoc ⟩
  (S^ [ab]⁻¹ ↑ • ε ↑) • [ - b , - - a ]ᵈ ≈⟨  (cleft right-unit) ⟩
  S^ ([ab]⁻¹) ↑ • [ - b , - - a ]ᵈ ≡⟨ Eq.cong (\ xx -> S^ ([ab]⁻¹) ↑ • [ - b , xx ]ᵈ) (-‿involutive a) ⟩
  S^ ([ab]⁻¹) ↑ • [ - b , a ]ᵈ ∎
  where
  ma = aux-mnz a λ ()
  x = ma .proj₁
  eqx = ma .proj₂
  [ab]⁻¹* = (  (a , λ ()) *' (b , λ ())  ) ⁻¹
  [ab]⁻¹ = [ab]⁻¹* .proj₁

  [ba]⁻¹* = (  (b , λ ()) *' (₁₊ x , λ ())  ) ⁻¹
  [ba]⁻¹ = [ba]⁻¹* .proj₁
  aux : [ba]⁻¹ ≡ - [ab]⁻¹
  aux = begin
    ((  (b , λ ()) *' (₁₊ x , λ ())  ) ⁻¹) .proj₁ ≡⟨ inv-distrib (b , λ ()) (₁₊ x , λ ()) ⟩
    (  (b , λ ()) ⁻¹) .proj₁  * (((₁₊ x , λ ())  ) ⁻¹) .proj₁ ≡⟨ Eq.cong (\ xx -> (  (b , λ ()) ⁻¹) .proj₁  * xx) (inv-cong ((₁₊ x , λ ())) (-' (a , λ ())) (Eq.sym eqx)) ⟩
    (  (b , λ ()) ⁻¹) .proj₁  * (( -' (a , λ ())  ) ⁻¹) .proj₁ ≡⟨ *-comm ((  (b , λ ()) ⁻¹) .proj₁) ((( -' (a , λ ())  ) ⁻¹) .proj₁) ⟩
    (( -' (a , λ ())  ) ⁻¹) .proj₁ * (  (b , λ ()) ⁻¹) .proj₁  ≡⟨ Eq.cong (_* (  (b , λ ()) ⁻¹) .proj₁) (inv-neg-comm (a , λ ())) ⟩
    - (( (a , λ ())  ) ⁻¹) .proj₁ * (  (b , λ ()) ⁻¹) .proj₁  ≡⟨ Eq.sym (-‿distribˡ-* ((( (a , λ ())  ) ⁻¹) .proj₁) ((  (b , λ ()) ⁻¹) .proj₁)) ⟩
    - ((( (a , λ ())  ) ⁻¹) .proj₁ * (  (b , λ ()) ⁻¹) .proj₁)  ≡⟨ Eq.cong -_ (Eq.sym (inv-distrib (a , λ ()) (b , λ ()))) ⟩
    - [ab]⁻¹ ∎
    where
    open ≡-Reasoning
  aux2 : [ab]⁻¹ + [ba]⁻¹ ≡ ₀
  aux2 = begin
    [ab]⁻¹ + [ba]⁻¹ ≡⟨ Eq.cong ([ab]⁻¹ +_) aux ⟩
    [ab]⁻¹ + - [ab]⁻¹ ≡⟨ +-inverseʳ [ab]⁻¹ ⟩
    ₀ ∎
    where
    open ≡-Reasoning

  open PB ((₂₊ n) QRel,_===_)  
  open PP ((₂₊ n) QRel,_===_)
  open SR word-setoid
  open Pattern-Assoc
  open Lemmas0 (₁₊ n)
  module L0 = Lemmas0 n

-}
-}
