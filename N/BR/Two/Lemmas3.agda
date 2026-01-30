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



module N.BR.Two.Lemmas3 (p-2 : ℕ) (p-prime : Prime (2+ p-2)) where

n : ℕ
n = 0
    
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
open import Zp.Mod-Lemmas p-2 p-prime
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
open import N.Ex-Sym4 p-2 p-prime
open import N.Ex-Sym5 p-2 p-prime hiding (module L0)
open import N.Ex-Sym2n p-2 p-prime
open import N.Ex-Sym3n p-2 p-prime

open import N.Lemma-Comm-n p-2 p-prime 0
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
open import N.Lemmas-3Q p-2 p-prime
open import N.Pushing.DH p-2 p-prime
open import N.Duality p-2 p-prime
open import N.BR.Calculations p-2 p-prime
open import N.BR.Two.Lemmas p-2 p-prime hiding (n ; sa ; module L01)
open import N.BR.Two.Lemmas2 p-2 p-prime hiding (n ; sa ; module L01)
open import N.BR.One.A p-2 p-prime


open PB ((₂₊ n) QRel,_===_)
open PP ((₂₊ n) QRel,_===_)
open SR word-setoid
open Pattern-Assoc
sa = special-assoc
open Lemmas0 n
module L01 = Lemmas0 (₁₊ n)
open Lemmas-2Q n
open Sym0-Rewriting (₁₊ n)
open Symplectic-GroupLike
open Basis-Change _ ((₂₊ n) QRel,_===_) grouplike

open Rewriting-Swap 1
open Commuting-Symplectic 0

open import Data.Nat.DivMod
open import Data.Fin.Properties

⌶ : ∀ {n} → Word (Gen (₂₊ n))
⌶ = H ↓ • H ↑ • CZ • H ↓ • H ↑


aux-hEx-4 : H ↑ ^ 2 • CZ • H • H ↑ • CZ • H ^ 2 • Ex ≈ H ↓ • H ↑ • CZ • H ↓ • H ↑
aux-hEx-4 = bbc (H ↑ ^ 2) (Ex • H ^ 2) claim
  where
  claim : H ↑ ^ 2 • (H ↑ ^ 2 • CZ • H • H ↑ • CZ • H ^ 2 • Ex) • (Ex • H ^ 2) ≈ H ↑ ^ 2 • (H ↓ • H ↑ • CZ • H ↓ • H ↑) • (Ex • H ^ 2)
  claim = begin
    H ↑ ^ 2 • (H ↑ ^ 2 • CZ • H • H ↑ • CZ • H ^ 2 • Ex) • (Ex • H ^ 2) ≈⟨ rewrite-swap 100 auto ⟩
    CZ • H • H ↑ • CZ ≈⟨ aux-hEx'' ⟩
    H ↑ • H ↓ • (CZ⁻¹) • H ↑ • H ↓ • Ex ≈⟨ cright cright cleft sym right-unit ⟩
    H ↑ • H ↓ • (CZ⁻¹ • ε) • H ↑ • H ↓ • Ex ≈⟨ cright cright cleft (cong (refl' (Eq.cong (CZ ^_) (Eq.sym lemma-toℕ₋₁))) (rewrite-sym0 100 auto)) ⟩
    H ↑ • H ↓ • (CZ^ ₋₁ • H ↑ ^ 2 • H ↑ ^ 2) • H ↑ • H ↓ • Ex ≈⟨ cright cright cleft sym assoc ⟩
    H ↑ • H ↓ • ((CZ^ ₋₁ • H ↑ ^ 2) • H ↑ ^ 2) • H ↑ • H ↓ • Ex ≈⟨ cright cright cleft cleft sym lemma-semi-HH↑-CZ ⟩
    H ↑ • H ↓ • ((H ↑ ^ 2 • CZ) • H ↑ ^ 2) • H ↑ • H ↓ • Ex ≈⟨ general-comm auto ⟩
    H ↑ ^ 2 • (H ↓ • H ↑ • CZ • H ↓ • H ↑) • (H ↑ ^ 2 • Ex) ≈⟨ cright cright rewrite-swap 100 auto ⟩
    H ↑ ^ 2 • (H ↓ • H ↑ • CZ • H ↓ • H ↑) • (Ex • H ^ 2) ∎

y≠1⇒1-y≠0 : ∀ (y : ℤ ₚ) -> y ≢ ₁ -> ₁ + - y ≢ ₀
y≠1⇒1-y≠0 y neq1 eq0 = neq1 ((Eq.trans (Eq.trans (Eq.sym (+-identityˡ y)) (Eq.cong (_+ y) (Eq.sym eq0))) (Eq.trans (+-assoc ₁ (- y ) y) (Eq.trans (Eq.cong (₁ +_) (+-inverseˡ y)) (+-identityʳ ₁)))))

aux-M|| : ∀ (y*@(y , nz) : ℤ* ₚ) -> M (y* ⁻¹) ↑ • CZ^ y • H • H ↑ • CZ • M (y* ⁻¹) ↑ ≈ CZ • H • H ↑ • CZ^ y
aux-M|| y*@(y , nz) = begin
  M (y* ⁻¹) ↑ • CZ^ y • H • H ↑ • CZ • M (y* ⁻¹) ↑ ≈⟨ sym assoc ⟩
  (M (y* ⁻¹) ↑ • CZ^ y) • H • H ↑ • CZ • M (y* ⁻¹) ↑ ≈⟨ cleft lemma-M↑CZ^k y⁻¹ y ((y* ⁻¹) .proj₂) ⟩
  (CZ^ (y * y⁻¹) • M (y* ⁻¹) ↑) • H • H ↑ • CZ • M (y* ⁻¹) ↑ ≈⟨ sa (□ ^ 2 • □ ^ 2) (□ • □ ^ 2 • □) auto ⟩
  CZ^ (y * y⁻¹) • (M (y* ⁻¹) ↑ • H) • H ↑ • CZ • M (y* ⁻¹) ↑ ≈⟨ cong (refl' (Eq.cong CZ^ (lemma-⁻¹ʳ y {{nztoℕ {y = y} {neq0 = nz}}}))) (sym (cleft lemma-comm-H-w↑ (M (y* ⁻¹)))) ⟩
  CZ • (H • M (y* ⁻¹) ↑) • H ↑ • CZ • M (y* ⁻¹) ↑ ≈⟨ cright sa (□ ^ 2 • □ ^ 2) (□ • □ ^ 2 • □) auto ⟩
  CZ • H • (M (y* ⁻¹) ↑ • H ↑) • CZ • M (y* ⁻¹) ↑ ≈⟨ cright cright cleft sym (lemma-cong↑ _ _ (semi-HM y*)) ⟩
  CZ • H • (H ↑ • M y* ↑) • CZ • M (y* ⁻¹) ↑ ≈⟨ cright cright sa (□ ^ 2 • □ ^ 2) (□ • □ ^ 2 • □) auto ⟩
  CZ • H • H ↑ • (M y* ↑ • CZ) • M (y* ⁻¹) ↑ ≈⟨ cright cright cright cleft axiom (semi-M↑CZ y*) ⟩
  CZ • H • H ↑ • (CZ^ y • M y* ↑) • M (y* ⁻¹) ↑ ≈⟨ cright cright cright assoc ⟩
  CZ • H • H ↑ • CZ^ y • M y* ↑ • M (y* ⁻¹) ↑ ≈⟨ cright cright cright (cright lemma-cong↑ _ _ (aux-M-mul y*)) ⟩
  CZ • H • H ↑ • CZ^ y • ε ≈⟨ cright cright (cright right-unit) ⟩
  CZ • H • H ↑ • CZ^ y ∎
  where
  y⁻¹ = (y* ⁻¹) .proj₁

lemma-⌶-CZ^y : ∀ (y*@(y , nz) : ℤ* ₚ) (neq1 : y ≢ ₁) ->
  let
  nzm : ₁ + - y ≢ ₀
  nzm = y≠1⇒1-y≠0 y neq1
  ₁-y : ℤ* ₚ
  ₁-y = (₁ + - y , nzm)
  in
  ⌶ • CZ^ y ≈ M (₁-y ⁻¹) ↑ • CZ^ y • ⌶ • M (₁-y ⁻¹)
lemma-⌶-CZ^y y*@(y , nz) neq1 = begin
  ⌶ • CZ^ y ≈⟨ refl ⟩
  (H ↓ • H ↑ • CZ • H ↓ • H ↑) • CZ^ y ≈⟨ cleft sym aux-hEx-4 ⟩
  (H ↑ ^ 2 • CZ • H • H ↑ • CZ • H ^ 2 • Ex) • CZ^ y ≈⟨ sa (□ ^ 7 • □) (□ ^ 6 • □ ^ 2) auto ⟩
  (H ↑ ^ 2 • CZ • H • H ↑ • CZ • H ^ 2) • Ex • CZ^ y ≈⟨ cright word-comm 1 (toℕ y) (sym lemma-comm-Ex-CZ-n) ⟩
  (H ↑ ^ 2 • CZ • H • H ↑ • CZ • H ^ 2) • CZ^ y • Ex ≈⟨ sa (□ ^ 6 • □ ^ 2) (□ ^ 5 • □ ^ 2 • □) auto ⟩
  (H ↑ ^ 2 • CZ • H • H ↑ • CZ) • (H ^ 2 • CZ^ y) • Ex ≈⟨ cright cleft lemma-semi-HH↓-CZ^k' y ⟩
  (H ↑ ^ 2 • CZ • H • H ↑ • CZ) • (CZ^ (- y) • H ^ 2) • Ex ≈⟨ sa (□ ^ 5 • □ ^ 2 • □) (□ ^ 4 • □ ^ 2 • □ ^ 2) auto ⟩
  (H ↑ ^ 2 • CZ • H • H ↑) • (CZ • CZ^ (- y)) • H ^ 2 • Ex ≈⟨ cright cleft lemma-CZ^k+l ₁ (- y) ⟩
  (H ↑ ^ 2 • CZ • H • H ↑) • CZ^ (₁ + - y) • H ^ 2 • Ex ≈⟨ sa (□ ^ 4 • □ ^ 3) (□ • □ ^ 4 • □ ^ 2) auto ⟩
  H ↑ ^ 2 • (CZ • H • H ↑ • CZ^ (₁ + - y)) • H ^ 2 • Ex ≈⟨ cright cleft sym (aux-M|| ₁-y) ⟩
  H ↑ ^ 2 • (M (₁-y ⁻¹) ↑ • CZ^ (₁ + - y) • H • H ↑ • CZ • M (₁-y ⁻¹) ↑) • H ^ 2 • Ex ≈⟨ sa (□ • □ ^ 6 • □ ^ 2) (□ ^ 2 • □ • □ ^ 3 • □ ^ 2 • □) auto ⟩
  (H ↑ ^ 2 • M (₁-y ⁻¹) ↑) • CZ^ (₁ + - y) • (H • H ↑ • CZ) • (M (₁-y ⁻¹) ↑ • H ^ 2) • Ex ≈⟨ cright cong (refl' (Eq.cong CZ^ (+-comm ₁ (- y)))) (cright cleft sym (lemma-comm-Hᵏ-w↑ 2 (M (₁-y ⁻¹)))) ⟩
  (H ↑ ^ 2 • M (₁-y ⁻¹) ↑) • CZ^ (- y + ₁) • (H • H ↑ • CZ) • (H ^ 2 • M (₁-y ⁻¹) ↑) • Ex ≈⟨ cong (lemma-cong↑ _ _ (aux-comm-HHM (₁-y ⁻¹))) (cleft sym (lemma-CZ^k+l (- y) ₁)) ⟩
  (M (₁-y ⁻¹) ↑ • H ↑ ^ 2) • (CZ^ (- y) • CZ) • (H • H ↑ • CZ) • (H ^ 2 • M (₁-y ⁻¹) ↑) • Ex ≈⟨ sa (□ ^ 2 • □ ^ 2 • □ ^ 3 • □ ^ 2 • □) (□ • □ ^ 2 • □ ^ 4 • □ ^ 2 • □) auto ⟩
  M (₁-y ⁻¹) ↑ • (H ↑ ^ 2 • CZ^ (- y)) • (CZ • H • H ↑ • CZ) • (H ^ 2 • M (₁-y ⁻¹) ↑) • Ex ≈⟨ cright cleft lemma-semi-HH↑-CZ^k'' y ⟩
  M (₁-y ⁻¹) ↑ • (CZ^ y • H ↑ ^ 2) • (CZ • H • H ↑ • CZ) • (H ^ 2 • M (₁-y ⁻¹) ↑) • Ex ≈⟨ sa (□ • □ ^ 2 • □ ^ 2) (□ • □ • □ ^ 2 • □) auto ⟩
  M (₁-y ⁻¹) ↑ • CZ^ y • (H ↑ ^ 2 • CZ • H • H ↑ • CZ) • (H ^ 2 • M (₁-y ⁻¹) ↑) • Ex ≈⟨ cright cright sa (□ ^ 5 • □ ^ 2 • □) (□ ^ 6 • □ ^ 2) auto ⟩
  M (₁-y ⁻¹) ↑ • CZ^ y • (H ↑ ^ 2 • CZ • H • H ↑ • CZ • H ^ 2) • M (₁-y ⁻¹) ↑ • Ex ≈⟨ cright cright cright sym (lemma-Ex-M (₁-y ⁻¹)) ⟩
  M (₁-y ⁻¹) ↑ • CZ^ y • (H ↑ ^ 2 • CZ • H • H ↑ • CZ • H ^ 2) • Ex • M (₁-y ⁻¹) ≈⟨ cright cright sa (□ ^ 6 • □ ^ 2) (□ ^ 7 • □) auto ⟩
  M (₁-y ⁻¹) ↑ • CZ^ y • (H ↑ ^ 2 • CZ • H • H ↑ • CZ • H ^ 2 • Ex) • M (₁-y ⁻¹) ≈⟨ cright cright cleft aux-hEx-4 ⟩
  M (₁-y ⁻¹) ↑ • CZ^ y • ⌶ • M (₁-y ⁻¹) ∎
  where
  nzm : ₁ + - y ≢ ₀
  nzm = y≠1⇒1-y≠0 y neq1
  ₁-y : ℤ* ₚ
  ₁-y = (₁ + - y , nzm)

  
