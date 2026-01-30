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



module N.BR.Three.B-CZ (p-2 : ℕ) (p-prime : Prime (2+ p-2))  where

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
open Symplectic
open import N.NF1-Sym p-2 p-prime
open import N.LM-Sym p-2 p-prime hiding (M)

open import N.Action p-2 p-prime
open import N.Action-Lemmas p-2 p-prime
open import Algebra.Properties.Ring (+-*-ring p-2)
open import N.NF2-Sym p-2 p-prime
open LM2


open import Zp.ModularArithmetic
open import N.Lemmas-2Qupit-Sym p-2 p-prime
open import N.Lemmas-2Qupit-Sym3 p-2 p-prime
open import N.NF2-Sym p-2 p-prime
--open Lemmas-2Q 2

open import N.NF1 p-2 p-prime
open import N.Ex-Sym p-2 p-prime
open import N.Ex-Sym1 p-2 p-prime
open import N.Ex-Sym2 p-2 p-prime
open import N.Ex-Sym3 p-2 p-prime
open import N.Ex-Sym4 p-2 p-prime hiding (lemma-Ex-S^ᵏ ; lemma-Ex-S^ᵏ↑)
--open import N.Ex-Sym5 p-2 p-prime hiding (module L0)
open import N.Ex-Sym2n p-2 p-prime
open import N.Ex-Sym3n p-2 p-prime
open import N.Ex-Sym4n p-2 p-prime
open import N.Ex-Sym4n2 p-2 p-prime
open import N.Ex-Sym4n3 p-2 p-prime


open import N.Lemma-Comm-n p-2 p-prime 0
import N.Lemma-Comm-n p-2 p-prime 1 as LCn1
open import N.Completeness1-Sym p-2 p-prime renaming (module Completeness to Cp1)
open Lemmas0a
open Lemmas0a1
open Lemmas0b
open Lemmas0c
open Lemmas-Sym
open Duality

open import N.Completeness1-Sym p-2 p-prime renaming (module Completeness to CP1) using ()
--open import N.Coset2-Update-Sym p-2 p-prime renaming (module Completeness to CP2) using ()
open import N.Lemmas4-Sym p-2 p-prime as L4
open import N.Lemmas-3Q p-2 p-prime
open import N.Pushing.DH p-2 p-prime
open import N.Duality p-2 p-prime
open import N.BR.Calculations p-2 p-prime
open import N.BR.Three.Lemmas p-2 p-prime
open import N.BR.Three.Lemmas2 p-2 p-prime
open import N.BR.Three.Lemmas3 p-2 p-prime hiding (module L02)
open import N.BR.Three.Lemmas4 p-2 p-prime
open import N.BR.Three.Lemmas5 p-2 p-prime
open import N.Embeding-2n p-2 p-prime 1 renaming (f* to emb ; by-emb' to lemma-cong⇣' ; by-emb to lemma-cong⇣ )

open PB (3 QRel,_===_)
open PP (3 QRel,_===_)
-- module B2 = PB (2 QRel,_===_)
-- module P2 = PP (2 QRel,_===_)
-- module B1 = PB (1 QRel,_===_)
-- module P1 = PP (1 QRel,_===_)
open SR word-setoid
open Pattern-Assoc
open Lemmas0 1
module L02 = Lemmas0 2
open Lemmas-2Q 1
--module L2Q0 = Lemmas-2Q 0
open Sym0-Rewriting 2
open Rewriting-Powers 2
open Rewriting-Swap 2
open Rewriting-Swap0 2
open Symplectic-GroupLike
open Basis-Change _ (3 QRel,_===_) grouplike
open import N.EX-Rewriting p-2 p-prime
open Rewriting-EX 2
open Homo 2 renaming (lemma-f* to lemma-f*-EX)
open Commuting-Symplectic 1
open import Data.List hiding (reverse)
open import N.BR.Two.Lemmas p-2 p-prime hiding (sa)
open import N.BR.Two.D p-2 p-prime hiding (dir-of)
open import N.BR.Three.DD-CZ p-2 p-prime renaming (dir-of to dir-of-dd)
open import N.BR.Three.BB-CZ p-2 p-prime renaming (dir-of to dir-of-bb)


lemma-CX↑-CZ' : 
  CX ↑ • CZ ≈ CZ • CZ02^ (- ₁) • CX ↑
lemma-CX↑-CZ' = begin
  CX ↑ • CZ ≈⟨ lemma-CX↑-CZ ⟩
  CZ • CZ02⁻¹ • CX ↑ ≈⟨ cright cleft (cright cleft refl' (Eq.cong (\ xx -> (CZ ^ xx) ↑) (Eq.sym lemma-toℕ-1ₚ))) ⟩
  CZ • CZ02^ (- ₁) • CX ↑ ∎


{-
lemma-M↑CX'^k : ∀ (x*@(x , nz) : ℤ* ₚ) k ->  let x⁻¹ = (x* ⁻¹) .proj₁ in
  M x* ↑ • CX'^ k ≈ CX'^ (k * x) • M (x , nz) ↑
lemma-M↑CX'^k x*@(x , nz) k = begin
  M x* ↑ • H ^ 3 • CZ^ k • H ≈⟨ special-assoc (□ ^ 4) (□ ^ 2 • □ ^ 2) auto ⟩
  (M x* ↑ • H ^ 3) • CZ^ k • H ≈⟨ cleft sym (lemma-comm-Hᵏ-w↑ 3 (M x*)) ⟩
  (H ^ 3 • M x* ↑) • CZ^ k • H ≈⟨ sa (□ ^ 2 • □ ^ 2) (□ • □ ^ 2 • □) auto ⟩
  H ^ 3 • (M x* ↑ • CZ^ k) • H ≈⟨ cright cleft lemma-M↑CZ^k x k nz ⟩
  H ^ 3 • (CZ^ (k * x) • M x* ↑) • H ≈⟨ sa (□ • □ ^ 2 • □) (□ ^ 4) auto ⟩
  H ^ 3 • CZ^ (k * x) • M x* ↑ • H ≈⟨ cright cright sym (lemma-comm-H-w↑ (M x*)) ⟩
  H ^ 3 • CZ^ (k * x) • H • M x* ↑ ≈⟨ sa (□ ^ 4) (□ ^ 3 • □) auto ⟩
  CX'^ (k * x) • M (x , nz) ↑ ∎
-}


lemma-CX'^k↑-CZ :  ∀ (k*@(k , nz) : ℤ* ₚ) ->

  CX'^ k ↑ • CZ ≈ CZ • CZ02^ (- k) • CX'^ k ↑
  
lemma-CX'^k↑-CZ k*@(k , nz) = bbc (M (k* ⁻¹) ↑ ↑) ε claim
  where
  k⁻¹ = (k* ⁻¹) .proj₁
  k⁻¹⁻¹ = (k* ⁻¹ ⁻¹) .proj₁
  claim : M (k* ⁻¹) ↑ ↑ • (CX'^ k ↑ • CZ) • ε ≈ M (k* ⁻¹) ↑ ↑ • (CZ • CZ02^ (- k) • CX'^ k ↑) • ε
  claim = begin
    M (k* ⁻¹) ↑ ↑ • (CX'^ k ↑ • CZ) • ε ≈⟨ cong refl right-unit ⟩
    M (k* ⁻¹) ↑ ↑ • (CX'^ k ↑ • CZ) ≈⟨ sym assoc ⟩
    (M (k* ⁻¹) ↑ ↑ • CX'^ k ↑) • CZ ≈⟨ cleft lemma-cong↑ _ _ (lemma-M↑CX'^k (k* ⁻¹) k) ⟩
    (CX'^ (k * k⁻¹) ↑ • M (k* ⁻¹) ↑ ↑) • CZ ≈⟨ cleft cleft (cright cleft refl' (Eq.cong (\ xx -> CZ^ xx ↑) (lemma-⁻¹ʳ k {{nztoℕ {y = k} {neq0 = nz}}}))) ⟩
    (CX ↑ • M (k* ⁻¹) ↑ ↑) • CZ ≈⟨ assoc ⟩
    CX ↑ • M (k* ⁻¹) ↑ ↑ • CZ ≈⟨ cright sym (lemma-comm-CZ-w↑↑ (M (k* ⁻¹))) ⟩
    CX ↑ • CZ • M (k* ⁻¹) ↑ ↑ ≈⟨ sym assoc ⟩
    (CX ↑ • CZ) • M (k* ⁻¹) ↑ ↑ ≈⟨ cleft lemma-CX↑-CZ' ⟩
    (CZ • CZ02^ (- ₁) • CX ↑) • M (k* ⁻¹) ↑ ↑ ≈⟨ sa (□ ^ 3 • □) (□ ^ 2 • □ ^ 2) auto ⟩
    (CZ • CZ02^ (- ₁)) • CX ↑ • M (k* ⁻¹) ↑ ↑ ≈⟨ cright cleft cright cleft lemma-cong↑ _ _ (B2.refl' (Eq.cong CZ^ (Eq.sym (lemma-⁻¹ʳ k {{nztoℕ {y = k} {neq0 = nz}}})))) ⟩
    (CZ • CZ02^ (- ₁)) • CX'^ (k * k⁻¹) ↑ • M (k* ⁻¹) ↑ ↑ ≈⟨ cright lemma-cong↑ _ _ (B2.sym (lemma-M↑CX'^k (k* ⁻¹) k)) ⟩
    (CZ • CZ02^ (- ₁)) • M (k* ⁻¹) ↑ ↑ • CX'^ k ↑ ≈⟨ sa (□ ^ 2 • □ ^ 2)  (□ • □ ^ 2 • □) auto ⟩
    CZ • (CZ02^ (- ₁) • M (k* ⁻¹) ↑ ↑) • CX'^ k ↑ ≈⟨ cright cleft lemma-CZ02^kM↑↑ k⁻¹ (- ₁) ((k* ⁻¹) .proj₂) ⟩
    CZ • (M (k* ⁻¹) ↑ ↑ • CZ02^ (- ₁ * k⁻¹⁻¹)) • CX'^ k ↑ ≈⟨ cright cleft cright refl' (Eq.cong CZ02^ (Eq.trans (Eq.cong (- ₁ *_) (inv-involutive k*)) (-1*x≈-x k))) ⟩
    CZ • (M (k* ⁻¹) ↑ ↑ • CZ02^ (- k)) • CX'^ k ↑ ≈⟨ sym (sa (□ ^ 2 • □ ^ 2)  (□ • □ ^ 2 • □) auto) ⟩
    (CZ • M (k* ⁻¹) ↑ ↑) • CZ02^ (- k) • CX'^ k ↑ ≈⟨ cleft lemma-comm-CZ-w↑↑ (M (k* ⁻¹)) ⟩
    (M (k* ⁻¹) ↑ ↑ • CZ) • CZ02^ (- k) • CX'^ k ↑ ≈⟨ assoc ⟩
    M (k* ⁻¹) ↑ ↑ • CZ • CZ02^ (- k) • CX'^ k ↑ ≈⟨ sym (cong refl right-unit) ⟩
    M (k* ⁻¹) ↑ ↑ • (CZ • CZ02^ (- k) • CX'^ k ↑) • ε ∎



aux-Ex↑-CZ^k : ∀ k -> CZ02^ k • Ex ↑ ≈ Ex ↑ • CZ^ k
aux-Ex↑-CZ^k k = bbc (Ex ↑) (Ex ↑) claim
  where
  claim : Ex ↑ • (CZ02^ k • Ex ↑) • Ex ↑ ≈ Ex ↑ • (Ex ↑ • CZ^ k) • Ex ↑
  claim = begin
    Ex ↑ • (CZ02^ k • Ex ↑) • Ex ↑ ≈⟨ sa (□ • □ ^ 2 • □) (□ ^ 2 • □ ^ 2) auto ⟩
    (Ex ↑ • CZ02^ k) • Ex ↑ • Ex ↑ ≈⟨ trans (cright rewrite-swap 100 auto) right-unit ⟩
    (Ex ↑ • CZ02^ k) ≈⟨ aux-Ex↑-CZ02^k k ⟩
    CZ^ k • Ex ↑  ≈⟨ sym (trans (cleft rewrite-swap 100 auto) left-unit) ⟩
    (Ex ↑ • Ex ↑) • CZ^ k • Ex ↑  ≈⟨ sym (sa (□ • □ ^ 2 • □) (□ ^ 2 • □ ^ 2) auto) ⟩
    Ex ↑ • (Ex ↑ • CZ^ k) • Ex ↑ ∎



b'-of : B -> B
b'-of = id

dir-of : B -> Word (Gen 3)
dir-of (₀ , b) = CZ02 • CZ^ (- b)
dir-of (a@(₁₊ _) , b) = CZ02 • CZ^ (- a)

lemma-dir-and-b'-cz : ∀ (b : B) ->
  let
  dir = dir-of b
  b' = b'-of b
  in
  
  [ b ]ᵇ ↑ • CZ ≈ dir • [ b' ]ᵇ ↑

lemma-dir-and-b'-cz x@(a@₀ , b@₀) = begin
  [ x ]ᵇ ↑ • CZ ≈⟨ assoc ⟩
  Ex ↑ • CX'^ b ↑ • CZ ≈⟨ rewrite-sym0 100 auto ⟩
  Ex ↑ • CZ ≈⟨  sym (aux-Ex↑-CZ^k ₁) ⟩
  CZ02 • Ex ↑ ≈⟨ cong (sym (trans (cright (refl' (Eq.cong CZ^ -0#≈0#))) right-unit)) (rewrite-sym0 100 auto) ⟩
  (CZ02 • CZ^ (- ₀)) • Ex ↑ • CX'^ ₀ ≈⟨ cright rewrite-sym0 100 auto ⟩
  dir • [ x' ]ᵇ ↑ ∎
  where
  dir = dir-of x
  x' = b'-of x


lemma-dir-and-b'-cz x@(a@₀ , b@(₁₊ _)) = begin
  [ x ]ᵇ ↑ • CZ ≈⟨ assoc ⟩
  Ex ↑ • CX'^ b ↑ • CZ ≈⟨  cright lemma-CX'^k↑-CZ (b , (λ ()))  ⟩
  Ex ↑ • CZ • CZ02^ (- b) • CX'^ b ↑ ≈⟨  sym assoc  ⟩
  (Ex ↑ • CZ) • CZ02^ (- b) • CX'^ b ↑ ≈⟨  cleft sym (aux-Ex↑-CZ^k ₁)  ⟩
  (CZ02 • Ex ↑) • CZ02^ (- b) • CX'^ b ↑ ≈⟨  sym (sa (□ • □ ^ 2 • □) (□ ^ 2 • □ ^ 2) auto)  ⟩
  CZ02 • (Ex ↑ • CZ02^ (- b)) • CX'^ b ↑ ≈⟨  cright cleft aux-Ex↑-CZ02^k (- b)  ⟩
  CZ02 • (CZ^ (- b) • Ex ↑) • CX'^ b ↑ ≈⟨  sa (□ • □ ^ 2 • □) (□ ^ 2 • □ ^ 2) auto  ⟩
  dir • [ x' ]ᵇ ↑ ∎
  where
  dir = dir-of x
  x' = b'-of x


lemma-dir-and-b'-cz x@(a@(₁₊ _) , b) = begin
  [ x ]ᵇ ↑ • CZ ≈⟨ sa (□ ^ 4 • □) (□ ^ 2 • □ ^ 2 • □) auto ⟩
  (Ex • CX'^ a) ↑ • (H ↑ • S^ -b/a ↑) ↑ • CZ ≈⟨ cright sym (lemma-comm-CZ-w↑↑ (H • S^ -b/a)) ⟩
  (Ex • CX'^ a) ↑ • CZ • (H ↑ • S^ -b/a ↑) ↑ ≈⟨ sa (□ ^ 2 • □ ^ 3) ((□ ^ 2 • □) • □ ^ 2) auto ⟩
  ((Ex • CX'^ a) ↑ • CZ) • (H ↑ • S^ -b/a ↑) ↑ ≈⟨ cleft lemma-dir-and-b'-cz (₀ , a) ⟩
  ((CZ02 • CZ^ (- a)) • Ex ↑ • CX'^ a ↑) • (H ↑ • S^ -b/a ↑) ↑ ≈⟨ sa ((□ ^ 2 • □ ^ 2) • □ ^ 2) (□ ^ 2 • □ ^ 4) auto ⟩
  dir • [ x' ]ᵇ ↑ ∎
  where
  dir = dir-of x
  x' = b'-of x

  a⁻¹ = ((a , λ ()) ⁻¹) .proj₁
  -b/a = - b * a⁻¹
