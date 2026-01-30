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



module N.Completeness (p-2 : ℕ) (p-prime : Prime (2+ p-2))  where

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
open import N.Lemmas-2Qupit p-2 p-prime
open import N.NF2-Sym p-2 p-prime
--open Lemmas-2Q 2

open import N.NF1 p-2 p-prime
open import N.Ex-Sym p-2 p-prime
open import N.Ex-Sym1 p-2 p-prime
open import N.Ex-Sym2 p-2 p-prime
open import N.Ex-Sym3 p-2 p-prime
open import N.Ex-Sym4 p-2 p-prime
open import N.Ex-Sym5 p-2 p-prime hiding (module L0)

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


lemma-coset-update : let open PB ((₁₊ n) QRel,_===_) in

  ∀ (lm : LM (₁₊ n)) (g : (Gen (₁₊ n))) ->
  -------------------------------------------------------
  ∃ \ lm' -> ∃ \ w -> [ lm ]ˡᵐ • [ g ]ʷ ≈ w ↑ • [ lm' ]ˡᵐ

lemma-coset-update {n@0} lm g@H-gen = lm' , ε , claim
  where
  open PB ((₁₊ n) QRel,_===_)  
  open PP ((₁₊ n) QRel,_===_)
  open SR word-setoid
  
  cp1 = CP1.Lemma-single-qupit-completeness {0} lm g  _
  lm' = cp1 .proj₁
  claim : [ lm ]ˡᵐ • [ H-gen ]ʷ ≈ (ε ↑) • [ lm' ]ˡᵐ
  claim = begin
    [ lm ]ˡᵐ • [ H-gen ]ʷ ≈⟨ cp1 .proj₂ ⟩
    [ lm' ]ˡᵐ ≈⟨ sym left-unit ⟩
    (ε ↑) • [ lm' ]ˡᵐ ∎
  
lemma-coset-update {n@0} lm g@S-gen = lm' , ε , claim
  where
  open PB ((₁₊ n) QRel,_===_)  
  open PP ((₁₊ n) QRel,_===_)
  open SR word-setoid
  
  cp1 = CP1.Lemma-single-qupit-completeness {0} lm g  _
  lm' = cp1 .proj₁
  claim : [ lm ]ˡᵐ • [ S-gen ]ʷ ≈ (ε ↑) • [ lm' ]ˡᵐ
  claim = begin
    [ lm ]ˡᵐ • [ S-gen ]ʷ ≈⟨ cp1 .proj₂ ⟩
    [ lm' ]ˡᵐ ≈⟨ sym left-unit ⟩
    (ε ↑) • [ lm' ]ˡᵐ ∎

lemma-coset-update {n@1} lm g = CP2.Lemma-two-qupit-completeness lm g
lemma-coset-update {n@2} lm@(inj₂ (d , lm↑)) (g ↥) = lm' , w ↑ , claim
  where
  open PB ((₁₊ n) QRel,_===_)  
  open PP ((₁₊ n) QRel,_===_)
  open SR word-setoid
  
  ih = lemma-coset-update lm↑ g
  lm↑' = ih .proj₁
  lm' = inj₂ (d , lm↑')
  w = ih .proj₂ .proj₁
  claim : [ lm ]ˡᵐ • [ g ↥ ]ʷ ≈ (w ↑ ↑) • [ lm' ]ˡᵐ
  claim = begin
    [ lm ]ˡᵐ • [ g ↥ ]ʷ ≈⟨ assoc ⟩
    [ d ]ᵈ • [ lm↑ ]ˡᵐ ↑ • [ g ↥ ]ʷ ≈⟨ refl ⟩
    [ d ]ᵈ • [ lm↑ ]ˡᵐ ↑ • [ g ]ʷ ↑ ≈⟨ (cright lemma-cong↑ _ _ (ih .proj₂ .proj₂)) ⟩
    [ d ]ᵈ • w ↑ ↑ • [ lm↑' ]ˡᵐ ↑ ≈⟨ sym assoc ⟩
    ([ d ]ᵈ • w ↑ ↑) • [ lm↑' ]ˡᵐ ↑ ≈⟨ (cleft comm-dbox-w↑↑ d w) ⟩
    (w ↑ ↑ • [ d ]ᵈ) • [ lm↑' ]ˡᵐ ↑ ≈⟨ assoc ⟩
    w ↑ ↑ • [ d ]ᵈ • [ lm↑' ]ˡᵐ ↑ ∎

lemma-coset-update {n@2} (inj₁ x) g = {!!}
lemma-coset-update {n@2} lm@(inj₂ (d@(₀ , b) , lm↑)) g@S-gen = lm' , w , claim
  where
  open PB ((₁₊ n) QRel,_===_)  
  open PP ((₁₊ n) QRel,_===_)
  open SR word-setoid

  lm' = lm
  w = S
  claim : [ lm ]ˡᵐ • [ g ]ʷ ≈ (S ↑) • [ lm' ]ˡᵐ
  claim = begin
    ([ d ]ᵈ • [ lm↑ ]ˡᵐ ↑) • [ g ]ʷ ≈⟨ assoc ⟩
    [ d ]ᵈ • [ lm↑ ]ˡᵐ ↑ • [ g ]ʷ ≈⟨ (cright sym (lemma-comm-S-w↑ [ lm↑ ]ˡᵐ)) ⟩
    [ d ]ᵈ • [ g ]ʷ • [ lm↑ ]ˡᵐ ↑ ≈⟨ sym assoc ⟩
    ([ d ]ᵈ • [ g ]ʷ) • [ lm↑ ]ˡᵐ ↑ ≈⟨ (cleft assoc) ⟩
    (Ex • CZ^ (- b) • [ g ]ʷ) • [ lm↑ ]ˡᵐ ↑ ≈⟨ (cleft cright word-comm (toℕ (- b)) 1 (axiom comm-CZ-S↓)) ⟩
    (Ex • [ g ]ʷ • CZ^ (- b)) • [ lm↑ ]ˡᵐ ↑ ≈⟨ sym (cong assoc refl) ⟩
    ((Ex • [ g ]ʷ) • CZ^ (- b)) • [ lm↑ ]ˡᵐ ↑ ≈⟨ (cleft cleft sym lemma-comm-Ex-S) ⟩
    ((S ↑ • Ex) • CZ^ (- b)) • [ lm↑ ]ˡᵐ ↑ ≈⟨ trans (cong assoc refl) assoc ⟩
    (S ↑) • [ lm' ]ˡᵐ ∎

lemma-coset-update {n@2} lm@(inj₂ (d@(a@(₁₊ _) , b) , lm↑)) g@S-gen = {!!}
  where
  open PB ((₁₊ n) QRel,_===_)  
  open PP ((₁₊ n) QRel,_===_)
  open SR word-setoid

  lm' = lm
  w = S
  claim : [ lm ]ˡᵐ • [ g ]ʷ ≈ (S ↑) • [ lm' ]ˡᵐ
  claim = begin
    ([ d ]ᵈ • [ lm↑ ]ˡᵐ ↑) • [ g ]ʷ ≈⟨ assoc ⟩
    [ d ]ᵈ • [ lm↑ ]ˡᵐ ↑ • [ g ]ʷ ≈⟨ (cright sym (lemma-comm-S-w↑ [ lm↑ ]ˡᵐ)) ⟩
    [ d ]ᵈ • [ g ]ʷ • [ lm↑ ]ˡᵐ ↑ ≈⟨ sym assoc ⟩
    ([ d ]ᵈ • [ g ]ʷ) • [ lm↑ ]ˡᵐ ↑ ≈⟨ (cleft {!!}) ⟩
    (Ex • CZ^ (- b) • [ g ]ʷ) • [ lm↑ ]ˡᵐ ↑ ≈⟨ (cleft cright word-comm (toℕ (- b)) 1 (axiom comm-CZ-S↓)) ⟩
    (Ex • [ g ]ʷ • CZ^ (- b)) • [ lm↑ ]ˡᵐ ↑ ≈⟨ sym (cong assoc refl) ⟩
    ((Ex • [ g ]ʷ) • CZ^ (- b)) • [ lm↑ ]ˡᵐ ↑ ≈⟨ (cleft cleft sym lemma-comm-Ex-S) ⟩
    ((S ↑ • Ex) • CZ^ (- b)) • [ lm↑ ]ˡᵐ ↑ ≈⟨ trans (cong assoc refl) {!!} ⟩
    (S ↑) • [ lm' ]ˡᵐ ∎

lemma-coset-update {n@2} lm@(inj₂ (d@(₀ , b@(₁₊ _)) , lm↑)) g@H-gen = lm' , w , claim
  where
  open PB ((₁₊ n) QRel,_===_)  
  open PP ((₁₊ n) QRel,_===_)
  open SR word-setoid
  open Lemmas0 n
  open Pattern-Assoc

  b* : ℤ* ₚ
  b* = (b , λ ())

  b⁻¹ : ℤ* ₚ
  b⁻¹ = b* ⁻¹

  lm' : LM 3
  lm' = inj₂ (((b , ₀)) , lm↑)
  w = ZM b*
  claim : [ lm ]ˡᵐ • [ g ]ʷ ≈ ZM b* ↑ • [ lm' ]ˡᵐ
  claim = begin
    ([ d ]ᵈ • [ lm↑ ]ˡᵐ ↑) • H ≈⟨ assoc ⟩
    [ d ]ᵈ • [ lm↑ ]ˡᵐ ↑ • H ≈⟨ (cright sym (lemma-comm-H-w↑ [ lm↑ ]ˡᵐ)) ⟩
    [ d ]ᵈ • H • [ lm↑ ]ˡᵐ ↑ ≈⟨ sym assoc ⟩
    ([ d ]ᵈ • H) • [ lm↑ ]ˡᵐ ↑ ≈⟨ (cleft assoc) ⟩
    (Ex • CZ^ (- b) • H) • [ lm↑ ]ˡᵐ ↑ ≈⟨ (cleft cright cleft sym right-unit) ⟩
    (Ex • (CZ^ (- b) • ε) • H) • [ lm↑ ]ˡᵐ ↑ ≈⟨ (cleft cright cleft (cright sym (aux-M-mul b*))) ⟩
    (Ex • (CZ^ (- b) • ZM b* • ZM b⁻¹ ) • H) • [ lm↑ ]ˡᵐ ↑ ≈⟨ (cleft cright cleft sym assoc) ⟩
    (Ex • ((CZ^ (- b) • ZM b*) • ZM b⁻¹ ) • H) • [ lm↑ ]ˡᵐ ↑ ≈⟨ (cleft cright cleft (cleft {!lemma-CZ^kM!})) ⟩
    (Ex • ((ZM b* • CZ^ (- b * b⁻¹ ^1)) • ZM b⁻¹ ) • H) • [ lm↑ ]ˡᵐ ↑ ≡⟨ Eq.cong (\ xx -> (Ex • ((ZM b* • CZ^ xx) • ZM b⁻¹ ) • H) • [ lm↑ ]ˡᵐ ↑) aux2 ⟩
    (Ex • ((ZM b* • CZ^ (- ₁)) • ZM b⁻¹ ) • H) • [ lm↑ ]ˡᵐ ↑ ≈⟨ special-assoc ((□ • (□ ^ 2 • □) • □) • □ ) (□ ^ 2 • □ • □ ^ 2 • □) auto ⟩
    (Ex • ZM b*) • CZ^ (- ₁) • (ZM b⁻¹ • H) • [ lm↑ ]ˡᵐ ↑ ≈⟨ (cleft {!lemma-Ex-M!}) ⟩
    (ZM b* ↑ • Ex) • CZ^ (- ₁) • (ZM b⁻¹ • H) • [ lm↑ ]ˡᵐ ↑ ≈⟨ special-assoc  (□ ^ 2 • □ • □ ^ 2 • □) (□ • (□ ^ 2 • □ ^ 2) • □) auto ⟩
    ZM b* ↑ • ((Ex • CZ^ (- ₁)) • (ZM b⁻¹ • H)) • [ lm↑ ]ˡᵐ ↑ ≈⟨ (cright cleft cright  sym (lemma-Aa0 b*)) ⟩
    ZM b* ↑ • ((Ex • CZ^ (- ₁)) • ([ (b , ₀) , aux-a≠0⇒ab≠0 (b) (λ ()) ]ᵃ)) • [ lm↑ ]ˡᵐ ↑ ≈⟨ (cright  (cleft refl)) ⟩
    ZM b* ↑ • [ lm' ]ˡᵐ ∎
    where
    aux2 : - b * b⁻¹ ^1 ≡ - ₁
    aux2 = Eq.trans (Eq.sym (-‿distribˡ-* b (b⁻¹ ^1))) (Eq.cong -_ (lemma-⁻¹ʳ (b) {{nztoℕ {y = b} {neq0 = λ ()} }}))

lemma-coset-update {n@2} lm@(inj₂ (d@(₀ , b@₀) , lm↑)) g@H-gen = lm' , w , claim
  where
  open PB ((₁₊ n) QRel,_===_)  
  open PP ((₁₊ n) QRel,_===_)
  open SR word-setoid
  open Lemmas0 n
  open Pattern-Assoc

  lm' : LM 3
  lm' = inj₂ (((₀ , ₀)) , lm↑)
  w = H
  claim : [ lm ]ˡᵐ • [ g ]ʷ ≈ w ↑ • [ lm' ]ˡᵐ
  claim = begin
    [ lm ]ˡᵐ • H ≈⟨ refl ⟩
    ((Ex • CZ^ (- ₀)) • [ lm↑ ]ˡᵐ ↑) • H ≡⟨ Eq.cong (\ xx -> ((Ex • CZ^ xx) • [ lm↑ ]ˡᵐ ↑) • H) -0#≈0# ⟩
    ((Ex • CZ^ (₀)) • [ lm↑ ]ˡᵐ ↑) • H ≈⟨ cong (cong right-unit refl) refl ⟩
    ((Ex) • [ lm↑ ]ˡᵐ ↑) • H ≈⟨ assoc ⟩
    Ex • [ lm↑ ]ˡᵐ ↑ • H ≈⟨ (cright sym (lemma-comm-H-w↑ [ lm↑ ]ˡᵐ)) ⟩
    Ex • H • [ lm↑ ]ˡᵐ ↑ ≈⟨ sym assoc ⟩
    (Ex • H) • [ lm↑ ]ˡᵐ ↑ ≈⟨ (cleft {!-0#≈0#!}) ⟩
    (H ↑ • Ex) • [ lm↑ ]ˡᵐ ↑ ≈⟨ assoc ⟩
    H ↑ • Ex • [ lm↑ ]ˡᵐ ↑ ≈⟨ (cright cleft sym right-unit) ⟩
    H ↑ • (Ex • CZ^ ₀) • [ lm↑ ]ˡᵐ ↑ ≡⟨ Eq.cong (\ xx -> H ↑ • (Ex • CZ^ xx) • [ lm↑ ]ˡᵐ ↑) (Eq.sym -0#≈0#) ⟩
    H ↑ • (Ex • CZ^ (- ₀)) • [ lm↑ ]ˡᵐ ↑ ≈⟨ refl ⟩
    w ↑ • [ lm' ]ˡᵐ ∎
