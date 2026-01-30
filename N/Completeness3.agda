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
open import Data.Nat.DivMod
open import Data.Fin.Properties


module N.Completeness3 (p-2 : ℕ) (p-prime : Prime (2+ p-2))  where

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
open import N.Lemmas-3Q p-2 p-prime
open import N.NF2-Sym p-2 p-prime

open import N.NF1 p-2 p-prime
open import N.Ex-Sym p-2 p-prime
open import N.Ex-Sym1 p-2 p-prime
open import N.Ex-Sym2 p-2 p-prime
open import N.Ex-Sym3 p-2 p-prime
open import N.Ex-Sym4 p-2 p-prime
open import N.Ex-Sym5 p-2 p-prime hiding (module L0)
open import N.Ex-Sym2n p-2 p-prime
open import N.Ex-Sym3n p-2 p-prime
open import N.Ex-Sym4n p-2 p-prime
open import N.Ex-Sym4n2 p-2 p-prime as Sym4n
open import N.Ex-Sym4n3 p-2 p-prime as Sym4n3 hiding (module P1)

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
open import N.Pushing.DS p-2 p-prime
open import N.Pushing.AS p-2 p-prime
open import N.Ex-Rewriting p-2 p-prime



lemma-coset-update : let open PB ((₁₊ n) QRel,_===_) in

  ∀ (lm : LM' (₁₊ n)) (g : (Gen (₁₊ n))) ->
  ----------------------------------------------------------------------
  ∃ \ (lm' : LM' (₁₊ n)) -> ∃ \ w -> [ lm ]ˡᵐ' • [ g ]ʷ ≈ w ↑ • [ lm' ]ˡᵐ'

{-
lemma-coset-update {n@2} lm@(case-I d@(a@(₁₊ a-1) , b) c2@(case-Ex-| nf1 mc@(m , HS^ hs))) g@CZ-gen = {!!}
  where
  nz : a ≢ ₀
  nz = λ ()
  a⁻¹ = ((a , nz) ⁻¹) .proj₁
  -b/a = - b * a⁻¹
  
  m' = m .proj₁
  k = toℕ (m' * a)
  
  w = H • (CZ ^ k) • H ^ 3 • ⟦ m ⟧ₘ ↑
  lm' = case-I d (case-Ex-nf1 nf1)

  open PB ((₁₊ n) QRel,_===_)  
  open PP ((₁₊ n) QRel,_===_)
  module B1 = PB ((n) QRel,_===_)
  module P1 = PP ((n) QRel,_===_)
  open SR word-setoid
  open Pattern-Assoc
  open Lemmas-2Q 0
  open Lemmas0 1
  open Sym0-Rewriting 2
  
  
  claim : [ lm ]ˡᵐ' • CZ ≈ (w ↑) • [ lm' ]ˡᵐ'
  claim = begin
    [ lm ]ˡᵐ' • CZ ≈⟨ {!!} ⟩
    (H ↑ • CZ ↑ ^ k • H ↑ ^ 3) • [ d ]ᵈ • Ex ↑ • ((CZ ^ ₁₊ k) ↑) • ⟦ nf1 ⟧₁ ↑ ↑ • ⟦ m ⟧ₘ ↑ • ε ≈⟨ (cright cright cright cleft lemma-cong↑ _ _ (lemma-CZ^k-% ((₁₊ k)))) ⟩
    (H ↑ • CZ ↑ ^ k • H ↑ ^ 3) • [ d ]ᵈ • Ex ↑ • ((CZ ^ ((₁₊ k) Nat.% p)) ↑) • ⟦ nf1 ⟧₁ ↑ ↑ • ⟦ m ⟧ₘ ↑ • ε ≈⟨ (cright cright cright cleft (lemma-cong↑ _ _ (B1.refl' (Eq.cong (CZ ^_) {!!})))) ⟩
    (H ↑ • CZ ↑ ^ k • H ↑ ^ 3) • [ d ]ᵈ • Ex ↑ • ((CZ ^ 0) ↑) • ⟦ nf1 ⟧₁ ↑ ↑ • ⟦ m ⟧ₘ ↑ • ε ≈⟨ (cright cright cright left-unit ) ⟩
    (H ↑ • CZ ↑ ^ k • H ↑ ^ 3) • [ d ]ᵈ • Ex ↑ • ⟦ nf1 ⟧₁ ↑ ↑ • ⟦ m ⟧ₘ ↑ • ε ≈⟨ (cright cright sym assoc) ⟩
    (H ↑ • CZ ↑ ^ k • H ↑ ^ 3) • [ d ]ᵈ • (Ex ↑ • ⟦ nf1 ⟧₁ ↑ ↑) • ⟦ m ⟧ₘ ↑ • ε ≈⟨ (cright cright cleft lemma-cong↑ _ _ (Sym4n.lemma-Ex-SMC 0 nf1)) ⟩
    (H ↑ • CZ ↑ ^ k • H ↑ ^ 3) • [ d ]ᵈ • (⟦ nf1 ⟧₁ ↑ • Ex ↑) • ⟦ m ⟧ₘ ↑ • ε ≈⟨ (cright cright assoc) ⟩
    (H ↑ • CZ ↑ ^ k • H ↑ ^ 3) • [ d ]ᵈ • ⟦ nf1 ⟧₁ ↑ • Ex ↑ • ⟦ m ⟧ₘ ↑ • ε ≈⟨ (cright cright cright cright right-unit) ⟩
    (H ↑ • CZ ↑ ^ k • H ↑ ^ 3) • [ d ]ᵈ • ⟦ nf1 ⟧₁ ↑ • Ex ↑ • ⟦ m ⟧ₘ ↑  ≈⟨ (cright cright cright lemma-cong↑ _ _ (lemma-Ex-M m)) ⟩
    (H ↑ • CZ ↑ ^ k • H ↑ ^ 3) • [ d ]ᵈ • ⟦ nf1 ⟧₁ ↑ • ⟦ m ⟧ₘ ↑ ↑ • Ex ↑  ≈⟨ (cright cright sym assoc) ⟩
    (H ↑ • CZ ↑ ^ k • H ↑ ^ 3) • [ d ]ᵈ • (⟦ nf1 ⟧₁ ↑ • ⟦ m ⟧ₘ ↑ ↑) • Ex ↑  ≈⟨ (cright cright cleft lemma-cong↑ _ _ (B1.sym (aux-comm-SMCM 0 m nf1))) ⟩
    (H ↑ • CZ ↑ ^ k • H ↑ ^ 3) • [ d ]ᵈ • (⟦ m ⟧ₘ ↑ ↑ • ⟦ nf1 ⟧₁ ↑) • Ex ↑  ≈⟨ (cright special-assoc (□ • □ ^ 2 • □) (□ ^ 2 • □ ^ 2) auto) ⟩
    (H ↑ • CZ ↑ ^ k • H ↑ ^ 3) • ([ d ]ᵈ • ⟦ m ⟧ₘ ↑ ↑) • ⟦ nf1 ⟧₁ ↑ • Ex ↑  ≈⟨ (cright cong (comm-dbox-w↑↑ d ⟦ m ⟧ₘ) (sym (((lemma-cong↑ _ _ (Sym4n.lemma-Ex-SMC 0 nf1))))) ) ⟩
    (H ↑ • CZ ↑ ^ k • H ↑ ^ 3) • (⟦ m ⟧ₘ ↑ ↑ • [ d ]ᵈ) • Ex ↑ • ⟦ nf1 ⟧₁ ↑ ↑  ≈⟨ special-assoc (□ ^ 3 • □ ^ 2 • □ ^ 2) (□ ^ 4 • □ ^ 3) auto ⟩
    (H ↑ • CZ ↑ ^ k • H ↑ ^ 3 • ⟦ m ⟧ₘ ↑ ↑) • [ d ]ᵈ • Ex ↑ • ⟦ nf1 ⟧₁ ↑ ↑  ≈⟨ (cleft cright cleft refl' (lemma-^-↑ CZ k)) ⟩
    (H ↑ • (CZ ^ k) ↑ • H ↑ ^ 3 • ⟦ m ⟧ₘ ↑ ↑) • [ d ]ᵈ • Ex ↑ • ⟦ nf1 ⟧₁ ↑ ↑  ≈⟨ refl ⟩
    (H • (CZ ^ k) • H ^ 3 • ⟦ m ⟧ₘ ↑) ↑ • [ d ]ᵈ • Ex ↑ • ⟦ nf1 ⟧₁ ↑ ↑  ≈⟨ refl ⟩
    (w ↑) • [ lm' ]ˡᵐ' ∎




lemma-coset-update {n@2} lm@(case-I d@(a@(₁₊ a-1) , b) c2@(case-Ex-| nf1 mc@(m , ε))) g@CZ-gen with (suc (toℕ (m .proj₁ * a))) Nat.% p | inspect (Nat._% p ) (suc (toℕ (m .proj₁ * a)))

lemma-coset-update {n@_} lm@(case-I d@(a@(₁₊ a-1) , b) c2@(case-Ex-| nf1 mc@(m , ε))) g@CZ-gen | 0 | [ eq ]' = lm' , w  , claim
  where
  nz : a ≢ ₀
  nz = λ ()
  a⁻¹ = ((a , nz) ⁻¹) .proj₁
  -b/a = - b * a⁻¹
  
  m' = m .proj₁
  k = toℕ (m' * a)
  
  w = H • (CZ ^ k) • H ^ 3 • ⟦ m ⟧ₘ ↑
  lm' = case-I d (case-Ex-nf1 nf1)

  open PB ((₁₊ n) QRel,_===_)  
  open PP ((₁₊ n) QRel,_===_)
  module B1 = PB ((n) QRel,_===_)
  module P1 = PP ((n) QRel,_===_)
  open SR word-setoid
  open Pattern-Assoc
  open Lemmas-2Q 0
  open Lemmas0 1
  open Sym0-Rewriting 2
  
  
  claim : [ lm ]ˡᵐ' • CZ ≈ (w ↑) • [ lm' ]ˡᵐ'
  claim = begin
    [ lm ]ˡᵐ' • CZ ≈⟨ lemma-coset-update-I-Ex-| a-1 b nf1 m ⟩
    (H ↑ • CZ ↑ ^ k • H ↑ ^ 3) • [ d ]ᵈ • Ex ↑ • ((CZ ^ ₁₊ k) ↑) • ⟦ nf1 ⟧₁ ↑ ↑ • ⟦ m ⟧ₘ ↑ • ε ≈⟨ (cright cright cright cleft lemma-cong↑ _ _ (lemma-CZ^k-% ((₁₊ k)))) ⟩
    (H ↑ • CZ ↑ ^ k • H ↑ ^ 3) • [ d ]ᵈ • Ex ↑ • ((CZ ^ ((₁₊ k) Nat.% p)) ↑) • ⟦ nf1 ⟧₁ ↑ ↑ • ⟦ m ⟧ₘ ↑ • ε ≈⟨ (cright cright cright cleft (lemma-cong↑ _ _ (B1.refl' (Eq.cong (CZ ^_) eq)))) ⟩
    (H ↑ • CZ ↑ ^ k • H ↑ ^ 3) • [ d ]ᵈ • Ex ↑ • ((CZ ^ 0) ↑) • ⟦ nf1 ⟧₁ ↑ ↑ • ⟦ m ⟧ₘ ↑ • ε ≈⟨ (cright cright cright left-unit ) ⟩
    (H ↑ • CZ ↑ ^ k • H ↑ ^ 3) • [ d ]ᵈ • Ex ↑ • ⟦ nf1 ⟧₁ ↑ ↑ • ⟦ m ⟧ₘ ↑ • ε ≈⟨ (cright cright sym assoc) ⟩
    (H ↑ • CZ ↑ ^ k • H ↑ ^ 3) • [ d ]ᵈ • (Ex ↑ • ⟦ nf1 ⟧₁ ↑ ↑) • ⟦ m ⟧ₘ ↑ • ε ≈⟨ (cright cright cleft lemma-cong↑ _ _ (Sym4n.lemma-Ex-SMC 0 nf1)) ⟩
    (H ↑ • CZ ↑ ^ k • H ↑ ^ 3) • [ d ]ᵈ • (⟦ nf1 ⟧₁ ↑ • Ex ↑) • ⟦ m ⟧ₘ ↑ • ε ≈⟨ (cright cright assoc) ⟩
    (H ↑ • CZ ↑ ^ k • H ↑ ^ 3) • [ d ]ᵈ • ⟦ nf1 ⟧₁ ↑ • Ex ↑ • ⟦ m ⟧ₘ ↑ • ε ≈⟨ (cright cright cright cright right-unit) ⟩
    (H ↑ • CZ ↑ ^ k • H ↑ ^ 3) • [ d ]ᵈ • ⟦ nf1 ⟧₁ ↑ • Ex ↑ • ⟦ m ⟧ₘ ↑  ≈⟨ (cright cright cright lemma-cong↑ _ _ (lemma-Ex-M m)) ⟩
    (H ↑ • CZ ↑ ^ k • H ↑ ^ 3) • [ d ]ᵈ • ⟦ nf1 ⟧₁ ↑ • ⟦ m ⟧ₘ ↑ ↑ • Ex ↑  ≈⟨ (cright cright sym assoc) ⟩
    (H ↑ • CZ ↑ ^ k • H ↑ ^ 3) • [ d ]ᵈ • (⟦ nf1 ⟧₁ ↑ • ⟦ m ⟧ₘ ↑ ↑) • Ex ↑  ≈⟨ (cright cright cleft lemma-cong↑ _ _ (B1.sym (aux-comm-SMCM 0 m nf1))) ⟩
    (H ↑ • CZ ↑ ^ k • H ↑ ^ 3) • [ d ]ᵈ • (⟦ m ⟧ₘ ↑ ↑ • ⟦ nf1 ⟧₁ ↑) • Ex ↑  ≈⟨ (cright special-assoc (□ • □ ^ 2 • □) (□ ^ 2 • □ ^ 2) auto) ⟩
    (H ↑ • CZ ↑ ^ k • H ↑ ^ 3) • ([ d ]ᵈ • ⟦ m ⟧ₘ ↑ ↑) • ⟦ nf1 ⟧₁ ↑ • Ex ↑  ≈⟨ (cright cong (comm-dbox-w↑↑ d ⟦ m ⟧ₘ) (sym (((lemma-cong↑ _ _ (Sym4n.lemma-Ex-SMC 0 nf1))))) ) ⟩
    (H ↑ • CZ ↑ ^ k • H ↑ ^ 3) • (⟦ m ⟧ₘ ↑ ↑ • [ d ]ᵈ) • Ex ↑ • ⟦ nf1 ⟧₁ ↑ ↑  ≈⟨ special-assoc (□ ^ 3 • □ ^ 2 • □ ^ 2) (□ ^ 4 • □ ^ 3) auto ⟩
    (H ↑ • CZ ↑ ^ k • H ↑ ^ 3 • ⟦ m ⟧ₘ ↑ ↑) • [ d ]ᵈ • Ex ↑ • ⟦ nf1 ⟧₁ ↑ ↑  ≈⟨ (cleft cright cleft refl' (lemma-^-↑ CZ k)) ⟩
    (H ↑ • (CZ ^ k) ↑ • H ↑ ^ 3 • ⟦ m ⟧ₘ ↑ ↑) • [ d ]ᵈ • Ex ↑ • ⟦ nf1 ⟧₁ ↑ ↑  ≈⟨ refl ⟩
    (H • (CZ ^ k) • H ^ 3 • ⟦ m ⟧ₘ ↑) ↑ • [ d ]ᵈ • Ex ↑ • ⟦ nf1 ⟧₁ ↑ ↑  ≈⟨ refl ⟩
    (w ↑) • [ lm' ]ˡᵐ' ∎


lemma-coset-update {n@_} lm@(case-I d@(a@(₁₊ a-1) , b) c2@(case-Ex-| nf1 mc@(m , ε))) g@CZ-gen | ₁₊ k-1 | [ eq ]' = lm' , w , claim
  where
  nz : a ≢ ₀
  nz = λ ()
  a⁻¹ = ((a , nz) ⁻¹) .proj₁
  -b/a = - b * a⁻¹
  
  m' = m .proj₁
  k = ( toℕ (m' * a))
  k' : ℤ ₚ
  k' = fromℕ< (m%n<n (suc k) p)

  nzk : k' ≢ ₀
  nzk with k' | inspect (\ k -> fromℕ< (m%n<n (suc k) p)) k
  ... | ₀ | [ eq2 ]' = ⊥-elim (NP.0≢1+n aux-0=1)
    where
    aux-0=1 : ₀ ≡ ₁₊ k-1
    aux-0=1 = begin
      ₀ ≡⟨ Eq.cong toℕ (Eq.sym eq2) ⟩
      toℕ k' ≡⟨ toℕ-fromℕ< (m%n<n (suc k) p) ⟩
      (suc k) Nat.% p ≡⟨ eq ⟩
      ₁₊ k-1 ∎
      where
      open ≡-Reasoning
  ... | ₁₊ k'-1 | [ eq2 ]' = λ ()

  k'⁻¹ : ℤ ₚ
  k'⁻¹ = ((k' , nzk) ⁻¹) .proj₁

  
  w = H • (CZ ^ k) • H ^ 3 • ZM (k' , nzk) ↑
  lm' = case-I d (case-Ex-| nf1 ((k' , nzk)⁻¹ *' m , ε))

  open PB ((₁₊ n) QRel,_===_)  
  open PP ((₁₊ n) QRel,_===_)
  module B1 = PB ((n) QRel,_===_)
  module P1 = PP ((n) QRel,_===_)
  open SR word-setoid
  open Pattern-Assoc
  open Lemmas-2Q 0
  open Lemmas0 1
  open Sym0-Rewriting 2
  
  
  claim : [ lm ]ˡᵐ' • CZ ≈ (w ↑) • [ lm' ]ˡᵐ'
  claim = begin
    [ lm ]ˡᵐ' • CZ ≈⟨ lemma-coset-update-I-Ex-| a-1 b nf1 m ⟩
    (H ↑ • CZ ↑ ^ k • H ↑ ^ 3) • [ d ]ᵈ • Ex ↑ • ((CZ ^ ₁₊ k) ↑) • ⟦ nf1 ⟧₁ ↑ ↑ • ⟦ m ⟧ₘ ↑ • ε ≈⟨ (cright cright cright cleft lemma-cong↑ _ _ (lemma-CZ^k-% ((₁₊ k)))) ⟩
    (H ↑ • CZ ↑ ^ k • H ↑ ^ 3) • [ d ]ᵈ • Ex ↑ • ((CZ ^ ((₁₊ k) Nat.% p)) ↑) • ⟦ nf1 ⟧₁ ↑ ↑ • ⟦ m ⟧ₘ ↑ • ε ≈⟨ (cright cright cright cleft (lemma-cong↑ _ _ (B1.refl' (Eq.cong (CZ ^_) (Eq.sym (toℕ-fromℕ< (m%n<n (suc k) p))))))) ⟩
    (H ↑ • CZ ↑ ^ k • H ↑ ^ 3) • [ d ]ᵈ • Ex ↑ • ((CZ^ k') ↑) • ⟦ nf1 ⟧₁ ↑ ↑ • ⟦ m ⟧ₘ ↑ • ε ≈⟨ (cright cright cright sym (cleft left-unit) ) ⟩
    (H ↑ • CZ ↑ ^ k • H ↑ ^ 3) • [ d ]ᵈ • Ex ↑ • (ε • (CZ^ k') ↑) • ⟦ nf1 ⟧₁ ↑ ↑ • ⟦ m ⟧ₘ ↑ • ε ≈⟨ (cright cright cright (cleft cleft sym (lemma-cong↑ _ _ (aux-M-mul ((k' , nzk))))) ) ⟩
    (H ↑ • CZ ↑ ^ k • H ↑ ^ 3) • [ d ]ᵈ • Ex ↑ • ((ZM (k' , nzk) • ZM ((k' , nzk)⁻¹)) • (CZ^ k')) ↑ • ⟦ nf1 ⟧₁ ↑ ↑ • ⟦ m ⟧ₘ ↑ • ε ≈⟨ (cright cright cright (cleft assoc) ) ⟩
    (H ↑ • CZ ↑ ^ k • H ↑ ^ 3) • [ d ]ᵈ • Ex ↑ • (ZM (k' , nzk) • ZM ((k' , nzk)⁻¹) • (CZ^ k')) ↑ • ⟦ nf1 ⟧₁ ↑ ↑ • ⟦ m ⟧ₘ ↑ • ε ≈⟨ (cright cright cright (cleft cright lemma-cong↑ _ _ (lemma-M↓CZ^k k'⁻¹ k' (((k' , nzk) ⁻¹) .proj₂))) ) ⟩
    (H ↑ • CZ ↑ ^ k • H ↑ ^ 3) • [ d ]ᵈ • Ex ↑ • (ZM (k' , nzk) • (CZ^ (k' * k'⁻¹)) • ZM ((k' , nzk)⁻¹)) ↑ • ⟦ nf1 ⟧₁ ↑ ↑ • ⟦ m ⟧ₘ ↑ • ε ≈⟨ (cright cright cright (cleft cright cleft (lemma-cong↑ _ _ (B1.refl' (Eq.cong CZ^ (lemma-⁻¹ʳ k' {{nztoℕ {y = k'} {neq0 = nzk}}})))) )) ⟩
    (H ↑ • CZ ↑ ^ k • H ↑ ^ 3) • [ d ]ᵈ • Ex ↑ • (ZM (k' , nzk) • (CZ^ ₁) • ZM ((k' , nzk)⁻¹)) ↑ • ⟦ nf1 ⟧₁ ↑ ↑ • ⟦ m ⟧ₘ ↑ • ε ≈⟨ (cright cright  special-assoc (□ • □ ^ 3 • □) (□ ^ 2 • □ ^ 3) auto ) ⟩
    (H ↑ • CZ ↑ ^ k • H ↑ ^ 3) • [ d ]ᵈ • (Ex ↑ • ZM (k' , nzk) ↑) • CZ ↑ • ZM ((k' , nzk)⁻¹) ↑ • ⟦ nf1 ⟧₁ ↑ ↑ • ⟦ m ⟧ₘ ↑ • ε ≈⟨ (cright cright  (cleft lemma-cong↑ _ _ (lemma-Ex-M ((k' , nzk)))) ) ⟩
    (H ↑ • CZ ↑ ^ k • H ↑ ^ 3) • [ d ]ᵈ • (ZM (k' , nzk) ↑ ↑ • Ex ↑) • CZ ↑ • ZM ((k' , nzk)⁻¹) ↑ • ⟦ nf1 ⟧₁ ↑ ↑ • ⟦ m ⟧ₘ ↑ • ε ≈⟨ (cright  special-assoc (□ • □ ^ 2 • □) (□ ^ 2 • □ ^ 2) auto ) ⟩
    (H ↑ • CZ ↑ ^ k • H ↑ ^ 3) • ([ d ]ᵈ • ZM (k' , nzk) ↑ ↑) • Ex ↑ • CZ ↑ • ZM ((k' , nzk)⁻¹) ↑ • ⟦ nf1 ⟧₁ ↑ ↑ • ⟦ m ⟧ₘ ↑ • ε ≈⟨ (cright cleft (comm-dbox-w↑↑ d (ZM (k' , nzk)))  ) ⟩
    (H ↑ • CZ ↑ ^ k • H ↑ ^ 3) • (ZM (k' , nzk) ↑ ↑ • [ d ]ᵈ) • Ex ↑ • CZ ↑ • ZM ((k' , nzk)⁻¹) ↑ • ⟦ nf1 ⟧₁ ↑ ↑ • ⟦ m ⟧ₘ ↑ • ε ≈⟨ (   special-assoc (□ ^ 3 • □ ^ 2 • □ ^ 6) (□ ^ 4 • □ • □ • □ • □ ^ 2 • □ ^ 2) auto ) ⟩
    (H ↑ • CZ ↑ ^ k • H ↑ ^ 3 • ZM (k' , nzk) ↑ ↑) • [ d ]ᵈ • Ex ↑ • CZ ↑ • (ZM ((k' , nzk)⁻¹) ↑ • ⟦ nf1 ⟧₁ ↑ ↑) • ⟦ m ⟧ₘ ↑ • ε ≈⟨ (   cright cright cright cright cleft lemma-cong↑ _ _ (aux-comm-MSMC 0 ((k' , nzk)⁻¹) nf1) ) ⟩
    (H ↑ • CZ ↑ ^ k • H ↑ ^ 3 • ZM (k' , nzk) ↑ ↑) • [ d ]ᵈ • Ex ↑ • CZ ↑ • (⟦ nf1 ⟧₁ ↑ ↑ • ZM ((k' , nzk)⁻¹) ↑) • ⟦ m ⟧ₘ ↑ • ε ≈⟨ (   cright cright cright cright special-assoc (□ ^ 2 • □ ^ 2) (□ • □ ^ 2 • □) auto ) ⟩
    (H ↑ • CZ ↑ ^ k • H ↑ ^ 3 • ZM (k' , nzk) ↑ ↑) • [ d ]ᵈ • Ex ↑ • CZ ↑ • ⟦ nf1 ⟧₁ ↑ ↑ • (ZM ((k' , nzk)⁻¹) ↑ • ⟦ m ⟧ₘ ↑) • ε ≈⟨ (   cright cright cright cright cright cleft axiom (cong↑ (M-mul ((k' , nzk)⁻¹) m)) ) ⟩
    (H ↑ • CZ ↑ ^ k • H ↑ ^ 3 • ZM (k' , nzk) ↑ ↑) • [ d ]ᵈ • Ex ↑ • CZ ↑ • ⟦ nf1 ⟧₁ ↑ ↑ • ZM ((k' , nzk)⁻¹ *' m) ↑ • ε ≈⟨ (   cleft cright cleft refl' (lemma-^-↑ CZ k) ) ⟩
    (H ↑ • (CZ ^ k) ↑ • H ↑ ^ 3 • ZM (k' , nzk) ↑ ↑) • [ d ]ᵈ • Ex ↑ • CZ ↑ • ⟦ nf1 ⟧₁ ↑ ↑ • ZM ((k' , nzk)⁻¹ *' m) ↑ • ε ≈⟨ (   refl ) ⟩
    (H • (CZ ^ k) • H ^ 3 • ZM (k' , nzk) ↑) ↑ • [ d ]ᵈ • Ex ↑ • CZ ↑ • ⟦ nf1 ⟧₁ ↑ ↑ • ZM ((k' , nzk)⁻¹ *' m) ↑ • ε ≈⟨ (   refl ) ⟩

    (w ↑) • [ lm' ]ˡᵐ' ∎


lemma-coset-update {n@2} lm@(case-I d@(a@₀ , b@(₁₊ _)) c2@(case-Ex-| nf1 mc@(m , ε))) g@CZ-gen = lm' , w  , claim
  where
  nz : b ≢ ₀
  nz = λ ()
  b⁻¹ = ((b , nz) ⁻¹) .proj₁
  
  m' = m .proj₁
  w = CZ^ (m' * b⁻¹)
  lm' = case-I d c2

  open PB ((₁₊ n) QRel,_===_)  
  open PP ((₁₊ n) QRel,_===_)
  open SR word-setoid
  open Pattern-Assoc
  open Lemmas-2Q 0
  claim : [ lm ]ˡᵐ' • CZ ≈ (w ↑) • [ lm' ]ˡᵐ'
  claim = begin
    [ lm ]ˡᵐ' • CZ ≈⟨ refl ⟩
    ([ d ]ᵈ • ((Ex • CZ • ⟦ nf1 ⟧₁ ↑ • ⟦ mc ⟧ₘ₊) ↑)) • CZ ≈⟨ (cleft (cright cright cright cright right-unit)) ⟩
    ([ d ]ᵈ • ((Ex • CZ • ⟦ nf1 ⟧₁ ↑ • ⟦ m ⟧ₘ) ↑)) • CZ ≈⟨ special-assoc (□ ^ 5 • □) (□ ^ 4 • □ ^ 2) auto ⟩
    ([ d ]ᵈ • Ex ↑ • CZ ↑ • ⟦ nf1 ⟧₁ ↑ ↑) • ⟦ m ⟧ₘ ↑ • CZ ≈⟨ (cright axiom (semi-M↑CZ m)) ⟩
    ([ d ]ᵈ • Ex ↑ • CZ ↑ • ⟦ nf1 ⟧₁ ↑ ↑) • CZ^ m' • ⟦ m ⟧ₘ ↑ ≈⟨ special-assoc (□ ^ 4 • □ ^ 2) (□ ^ 3 • □ ^ 2 • □) auto ⟩
    ([ d ]ᵈ • Ex ↑ • CZ ↑) • (⟦ nf1 ⟧₁ ↑ ↑ • CZ^ m') • ⟦ m ⟧ₘ ↑ ≈⟨ (cright cleft word-comm 1 (toℕ m') (sym (lemma-comm-CZ-w↑↑ ⟦ nf1 ⟧₁))) ⟩
    ([ d ]ᵈ • Ex ↑ • CZ ↑) • (CZ^ m' • ⟦ nf1 ⟧₁ ↑ ↑) • ⟦ m ⟧ₘ ↑ ≈⟨ special-assoc (□ ^ 3 • □ ^ 2 • □) (□ ^ 2 • □ ^ 2 • □ ^ 2) auto ⟩
    ([ d ]ᵈ • Ex ↑) • (CZ ↑ • CZ^ m') • ⟦ nf1 ⟧₁ ↑ ↑ • ⟦ m ⟧ₘ ↑ ≈⟨ (cright cleft word-comm 1 (toℕ m') (axiom selinger-c12)) ⟩
    ([ d ]ᵈ • Ex ↑) • (CZ^ m' • CZ ↑) • ⟦ nf1 ⟧₁ ↑ ↑ • ⟦ m ⟧ₘ ↑ ≈⟨ special-assoc (□ • □ ^ 2 • □) (□ ^ 2 • □ ^ 2) auto ⟩
    (([ d ]ᵈ • Ex ↑) • CZ^ m') • CZ ↑ • ⟦ nf1 ⟧₁ ↑ ↑ • ⟦ m ⟧ₘ ↑ ≈⟨ (cleft (cleft cleft aux-dd d)) ⟩
    (([ d ]ᵈ' • Ex ↑) • CZ^ m') • CZ ↑ • ⟦ nf1 ⟧₁ ↑ ↑ • ⟦ m ⟧ₘ ↑ ≈⟨ special-assoc (((□ ^ 3 • □) • □) • □ ^ 3) (□ ^ 2 • (□ ^ 2 • □) • □ ^ 3) auto ⟩
    (CZ^ (- ₁) • [ (a , b) , (λ ()) ]ᵃ ↑) • ((Ex • Ex ↑) • CZ^ m') • CZ ↑ • ⟦ nf1 ⟧₁ ↑ ↑ • ⟦ m ⟧ₘ ↑ ≈⟨ (cright cleft lemma-Induction lemma-[Ex-Ex↑]-CZ (toℕ m')) ⟩
    (CZ^ (- ₁) • [ (a , b) , (λ ()) ]ᵃ ↑) • (CZ ↑ ^ toℕ m' • (Ex • Ex ↑)) • CZ ↑ • ⟦ nf1 ⟧₁ ↑ ↑ • ⟦ m ⟧ₘ ↑ ≈⟨ (cleft cright right-unit) ⟩
    (CZ^ (- ₁) • ⟦ (b , nz) ⁻¹ ⟧ₘ ↑) • (CZ ↑ ^ toℕ m' • (Ex • Ex ↑)) • CZ ↑ • ⟦ nf1 ⟧₁ ↑ ↑ • ⟦ m ⟧ₘ ↑ ≈⟨ special-assoc (□ ^ 2 • □ ^ 2 • □) (□ • □ ^  2 • □ • □) auto ⟩
    CZ^ (- ₁) • (⟦ (b , nz) ⁻¹ ⟧ₘ ↑ • CZ ↑ ^ toℕ m') • (Ex • Ex ↑) • CZ ↑ • ⟦ nf1 ⟧₁ ↑ ↑ • ⟦ m ⟧ₘ ↑ ≈⟨ (cright cleft cright refl' (lemma-^-↑ CZ (toℕ m'))) ⟩
    CZ^ (- ₁) • (⟦ (b , nz) ⁻¹ ⟧ₘ ↑ • CZ^ m' ↑) • (Ex • Ex ↑) • CZ ↑ • ⟦ nf1 ⟧₁ ↑ ↑ • ⟦ m ⟧ₘ ↑ ≈⟨ (cright cleft lemma-cong↑ _ _ (lemma-M↓CZ^k b⁻¹ m' (((b , nz) ⁻¹) .proj₂))) ⟩
    CZ^ (- ₁) • (CZ^ (m' * b⁻¹) ↑ • ⟦ (b , nz) ⁻¹ ⟧ₘ ↑) • (Ex • Ex ↑) • CZ ↑ • ⟦ nf1 ⟧₁ ↑ ↑ • ⟦ m ⟧ₘ ↑ ≈⟨ special-assoc  (□ • □ ^  2 • □ • □) (□ ^ 2 • □ ^ 3) auto ⟩
    (CZ^ (- ₁) • CZ^ (m' * b⁻¹) ↑) • ⟦ (b , nz) ⁻¹ ⟧ₘ ↑ • (Ex • Ex ↑) • CZ ↑ • ⟦ nf1 ⟧₁ ↑ ↑ • ⟦ m ⟧ₘ ↑ ≈⟨ (cleft cright refl' (Eq.sym (lemma-^-↑ CZ (toℕ (m' * b⁻¹))))) ⟩
    (CZ^ (- ₁) • CZ ↑ ^ toℕ (m' * b⁻¹)) • ⟦ (b , nz) ⁻¹ ⟧ₘ ↑ • (Ex • Ex ↑) • CZ ↑ • ⟦ nf1 ⟧₁ ↑ ↑ • ⟦ m ⟧ₘ ↑ ≈⟨  (cleft word-comm (toℕ (- ₁)) (toℕ (m' * b⁻¹)) (sym (axiom selinger-c12))) ⟩
    (CZ ↑ ^ toℕ (m' * b⁻¹) • CZ^ (- ₁)) • ⟦ (b , nz) ⁻¹ ⟧ₘ ↑ • (Ex • Ex ↑) • CZ ↑ • ⟦ nf1 ⟧₁ ↑ ↑ • ⟦ m ⟧ₘ ↑ ≈⟨ special-assoc (□ ^ 2 • □ • □ ^ 2 • □ ^ 2) (□ • □ ^ 3 • □ ^ 3) auto ⟩
    CZ ↑ ^ toℕ (m' * b⁻¹) • (CZ^ (- ₁) • ⟦ (b , nz) ⁻¹ ⟧ₘ ↑ • Ex) • Ex ↑ • CZ ↑ • ⟦ nf1 ⟧₁ ↑ ↑ • ⟦ m ⟧ₘ ↑ ≈⟨ (cright cleft cright cleft sym right-unit) ⟩
    CZ ↑ ^ toℕ (m' * b⁻¹) • (CZ^ (- ₁) • [ (a , b) , (λ ()) ]ᵃ ↑ • Ex) • Ex ↑ • CZ ↑ • ⟦ nf1 ⟧₁ ↑ ↑ • ⟦ m ⟧ₘ ↑ ≈⟨ refl ⟩
    CZ ↑ ^ toℕ (m' * b⁻¹) • [ d ]ᵈ' • Ex ↑ • CZ ↑ • ⟦ nf1 ⟧₁ ↑ ↑ • ⟦ m ⟧ₘ ↑ ≈⟨ (cright cong (sym (aux-dd d)) (cright cright cright sym right-unit)) ⟩
    CZ ↑ ^ toℕ (m' * b⁻¹) • [ d ]ᵈ • Ex ↑ • CZ ↑ • ⟦ nf1 ⟧₁ ↑ ↑ • ⟦ m ⟧ₘ ↑ • ε ≈⟨ (cleft refl' (lemma-^-↑ CZ (toℕ (m' * b⁻¹)))) ⟩
    CZ^ (m' * b⁻¹) ↑ • [ d ]ᵈ • Ex ↑ • CZ ↑ • ⟦ nf1 ⟧₁ ↑ ↑ • ⟦ m ⟧ₘ ↑ • ε ≈⟨ refl ⟩
    (w ↑) • [ lm' ]ˡᵐ' ∎



lemma-coset-update {n@0} lm g@H-gen = lm' , ε , claim
  where
  open PB ((₁₊ n) QRel,_===_)  
  open PP ((₁₊ n) QRel,_===_)
  open SR word-setoid
  
  cp1 = CP1.Lemma-single-qupit-completeness {0} lm g  _
  lm' = cp1 .proj₁
  claim : [ lm ]ˡᵐ' • [ H-gen ]ʷ ≈ (ε ↑) • [ lm' ]ˡᵐ'
  claim = begin
    [ lm ]ˡᵐ' • [ H-gen ]ʷ ≈⟨ cp1 .proj₂ ⟩
    [ lm' ]ˡᵐ' ≈⟨ sym left-unit ⟩
    (ε ↑) • [ lm' ]ˡᵐ' ∎
  
lemma-coset-update {n@0} lm g@S-gen = lm' , ε , claim
  where
  open PB ((₁₊ n) QRel,_===_)  
  open PP ((₁₊ n) QRel,_===_)
  open SR word-setoid
  
  cp1 = CP1.Lemma-single-qupit-completeness {0} lm g  _
  lm' = cp1 .proj₁
  claim : [ lm ]ˡᵐ' • [ S-gen ]ʷ ≈ (ε ↑) • [ lm' ]ˡᵐ'
  claim = begin
    [ lm ]ˡᵐ' • [ S-gen ]ʷ ≈⟨ cp1 .proj₂ ⟩
    [ lm' ]ˡᵐ' ≈⟨ sym left-unit ⟩
    (ε ↑) • [ lm' ]ˡᵐ' ∎

lemma-coset-update {n@1} lm g = CP2.Lemma-two-qupit-completeness lm g


lemma-coset-update {n@2} lm@(case-I d lm↑) (g ↥) = lm' , w ↑ , claim
  where
  open PB ((₁₊ n) QRel,_===_)  
  open PP ((₁₊ n) QRel,_===_)
  open SR word-setoid
  
  ih = lemma-coset-update lm↑ g
  lm↑' = ih .proj₁
  lm' = case-I d lm↑'
  w = ih .proj₂ .proj₁
  claim : [ lm ]ˡᵐ' • [ g ↥ ]ʷ ≈ (w ↑ ↑) • [ lm' ]ˡᵐ'
  claim = begin
    [ lm ]ˡᵐ' • [ g ↥ ]ʷ ≈⟨ assoc ⟩
    [ d ]ᵈ • [ lm↑ ]ˡᵐ' ↑ • [ g ↥ ]ʷ ≈⟨ refl ⟩
    [ d ]ᵈ • [ lm↑ ]ˡᵐ' ↑ • [ g ]ʷ ↑ ≈⟨ (cright lemma-cong↑ _ _ (ih .proj₂ .proj₂)) ⟩
    [ d ]ᵈ • w ↑ ↑ • [ lm↑' ]ˡᵐ' ↑ ≈⟨ sym assoc ⟩
    ([ d ]ᵈ • w ↑ ↑) • [ lm↑' ]ˡᵐ' ↑ ≈⟨ (cleft comm-dbox-w↑↑ d w) ⟩
    (w ↑ ↑ • [ d ]ᵈ) • [ lm↑' ]ˡᵐ' ↑ ≈⟨ assoc ⟩
    w ↑ ↑ • [ d ]ᵈ • [ lm↑' ]ˡᵐ' ↑ ∎


lemma-coset-update {n@2} lm@(case-I (d)  lm↑) g@S-gen = lm' , w , claim
  where
  open PB ((₁₊ n) QRel,_===_)  
  open PP ((₁₊ n) QRel,_===_)
  open SR word-setoid

  d' = (d-of-DS d)
  lm' = case-I d' lm↑
  w = dir-of-DS d
  claim : [ lm ]ˡᵐ' • S ≈ (w ↑) • [ lm' ]ˡᵐ'
  claim = begin
    ([ d ]ᵈ • [ lm↑ ]ˡᵐ' ↑) • S ≈⟨ assoc ⟩
    [ d ]ᵈ • [ lm↑ ]ˡᵐ' ↑ • S ≈⟨ (cright sym (lemma-comm-S-w↑ [ lm↑ ]ˡᵐ')) ⟩
    [ d ]ᵈ • S • [ lm↑ ]ˡᵐ' ↑ ≈⟨ sym assoc ⟩
    ([ d ]ᵈ • S) • [ lm↑ ]ˡᵐ' ↑ ≈⟨ (cleft (aux-DS d)) ⟩
    (w ↑ • [ d' ]ᵈ ) • [ lm↑ ]ˡᵐ' ↑ ≈⟨ assoc ⟩
    w ↑ • [ lm' ]ˡᵐ' ∎

lemma-coset-update {n@2} lm@(case-I (d)  lm↑) g@H-gen = lm' , w , claim
  where
  open PB ((₁₊ n) QRel,_===_)  
  open PP ((₁₊ n) QRel,_===_)
  open SR word-setoid

  d' = (d-of-DH d)
  lm' = case-I d' lm↑
  w = dir-of-DH d
  claim : [ lm ]ˡᵐ' • H ≈ (w ↑) • [ lm' ]ˡᵐ'
  claim = begin
    ([ d ]ᵈ • [ lm↑ ]ˡᵐ' ↑) • H ≈⟨ assoc ⟩
    [ d ]ᵈ • [ lm↑ ]ˡᵐ' ↑ • H ≈⟨ (cright sym (lemma-comm-H-w↑ [ lm↑ ]ˡᵐ')) ⟩
    [ d ]ᵈ • H • [ lm↑ ]ˡᵐ' ↑ ≈⟨ sym assoc ⟩
    ([ d ]ᵈ • H) • [ lm↑ ]ˡᵐ' ↑ ≈⟨ (cleft (aux-DH d)) ⟩
    (w ↑ • [ d' ]ᵈ ) • [ lm↑ ]ˡᵐ' ↑ ≈⟨ assoc ⟩
    w ↑ • [ lm' ]ˡᵐ' ∎



lemma-coset-update {n@2} lm@(case-I d@(a@₀ , b@₀) c2@(case-Ex-| nf1 mc@(m , HS^ hs))) g@CZ-gen = lm' , w  , claim
  where
  m' = m .proj₁
  m⁻¹ = (m ⁻¹) .proj₁
  k = toℕ m⁻¹
  w = H ↑ • CZ ^ k • ZM (( m) ⁻¹) • H ↑ ^ 3
  lm' = case-I (₀ , m⁻¹) c2

  open PB ((₁₊ n) QRel,_===_)  
  open PP ((₁₊ n) QRel,_===_)
  open SR word-setoid
  open Pattern-Assoc
  open Lemmas0 n
  open Rewriting-Powers n
  open Rewriting-Swap 2
  module L2Q = Lemmas-2Q 1


  claim : [ lm ]ˡᵐ' • CZ ≈ (w ↑) • [ lm' ]ˡᵐ'
  claim = begin
    [ lm ]ˡᵐ' • CZ ≈⟨ refl ⟩
    (Ex • ((Ex • CZ • ⟦ nf1 ⟧₁ ↑ • ⟦ mc ⟧ₘ₊) ↑)) • CZ ≈⟨ refl ⟩
    (Ex • ((Ex • CZ • ⟦ nf1 ⟧₁ ↑ • ⟦ m ⟧ₘ • H • S^ hs) ↑)) • CZ ≈⟨ special-assoc (□ ^ 7 • □) ((□ • (□ ^ 3 • □ ^ 2 • □)) • □) auto ⟩
    (Ex • ((Ex • CZ • ⟦ nf1 ⟧₁ ↑) • (⟦ m ⟧ₘ • H) • S^ hs) ↑) • CZ ≈⟨ (cleft cright cright cleft sym (lemma-cong↑ _ _  (semi-HM' m))) ⟩
    (Ex • ((Ex • CZ • ⟦ nf1 ⟧₁ ↑) • (H • ⟦ m ⁻¹ ⟧ₘ) • S^ hs) ↑) • CZ ≈⟨ special-assoc ((□ • (□ ^ 3 • □ ^ 2 • □)) • □) ((□ • (□ ^ 3 • □ ^ 2)) • □ ^ 2) auto ⟩
    (Ex • ((Ex • CZ • ⟦ nf1 ⟧₁ ↑) • (H • ⟦ m ⁻¹ ⟧ₘ)) ↑) • S^ hs ↑ • CZ ≈⟨ (cright sym (aux-comm-CZ-S^k↑ hs)) ⟩
    (Ex • ((Ex • CZ • ⟦ nf1 ⟧₁ ↑) • (H • ⟦ m ⁻¹ ⟧ₘ)) ↑) • CZ • S^ hs ↑ ≈⟨ special-assoc ((□ • (□ ^ 3 • □ ^ 2)) • □ ^ 2) ((□ • (□ ^ 3 • □ ^ 1)) • □ ^ 2 • □) auto ⟩
    (Ex • ((Ex • CZ • ⟦ nf1 ⟧₁ ↑) • H) ↑) • (⟦ m ⁻¹ ⟧ₘ ↑ • CZ) • S^ hs ↑ ≈⟨ (cright cleft axiom (semi-M↑CZ (m ⁻¹))) ⟩
    (Ex • ((Ex • CZ • ⟦ nf1 ⟧₁ ↑) • H) ↑) • (CZ^ m⁻¹ • ⟦ m ⁻¹ ⟧ₘ ↑) • S^ hs ↑ ≈⟨ cleft special-assoc (□ • □ ^ 3 • □) (□ ^ 3 • □ ^ 2) auto ⟩
    ((Ex • Ex ↑ • CZ ↑) • (⟦ nf1 ⟧₁ ↑ ↑ • H ↑)) • (CZ^ m⁻¹ • ⟦ m ⁻¹ ⟧ₘ ↑) • S^ hs ↑ ≈⟨ sym (cleft cright lemma-cong↑ _ _ (lemma-comm-Hᵏ-w↑ 1 ⟦ nf1 ⟧₁)) ⟩
    ((Ex • Ex ↑ • CZ ↑) • (H ↑ • ⟦ nf1 ⟧₁ ↑ ↑)) • (CZ^ m⁻¹ • ⟦ m ⁻¹ ⟧ₘ ↑) • S^ hs ↑ ≈⟨ special-assoc ((□ ^ 3 • □ ^ 2) • □ ^ 2 • □) (□ ^ 3 • □ • □ ^ 2 • □ ^ 2) auto ⟩
    (Ex • Ex ↑ • CZ ↑) • H ↑ • (⟦ nf1 ⟧₁ ↑ ↑ • CZ^ m⁻¹) • ⟦ m ⁻¹ ⟧ₘ ↑ • S^ hs ↑ ≈⟨ (cright cright cleft word-comm 1 (toℕ m⁻¹) (sym (lemma-comm-CZ-w↑↑ ⟦ nf1 ⟧₁))) ⟩
    (Ex • Ex ↑ • CZ ↑) • H ↑ • (CZ^ m⁻¹ • ⟦ nf1 ⟧₁ ↑ ↑) • ⟦ m ⁻¹ ⟧ₘ ↑ • S^ hs ↑ ≈⟨ special-assoc (□ ^ 3 • □ • □ ^ 2 • □ ^ 2) (□ ^ 4 • □ ^ 2 • □ ^ 2) auto ⟩
    (Ex • Ex ↑ • CZ ↑ • H ↑) • (CZ^ m⁻¹ • ⟦ nf1 ⟧₁ ↑ ↑) • ⟦ m ⁻¹ ⟧ₘ ↑ • S^ hs ↑ ≈⟨ (cleft rewrite-powers 100 auto) ⟩
    (Ex • Ex ↑ • H ↑ • CX ↑) • (CZ^ m⁻¹ • ⟦ nf1 ⟧₁ ↑ ↑) • ⟦ m ⁻¹ ⟧ₘ ↑ • S^ hs ↑ ≈⟨ special-assoc (□ ^ 4 • □ ^ 2 • □) (□ ^ 3 • □ ^ 2 • □ ^ 2) auto ⟩
    (Ex • Ex ↑ • H ↑) • (CX ↑ • CZ^ m⁻¹) • ⟦ nf1 ⟧₁ ↑ ↑ • ⟦ m ⁻¹ ⟧ₘ ↑ • S^ hs ↑ ≈⟨ (cright cleft lemma-CX↑-CZ^k k) ⟩
    (Ex • Ex ↑ • H ↑) • (CZ ^ k • CZ02⁻ᵏ k • CX ↑) • ⟦ nf1 ⟧₁ ↑ ↑ • ⟦ m ⁻¹ ⟧ₘ ↑ • S^ hs ↑ ≈⟨ (cleft rewrite-swap 100 auto) ⟩
    (H ↑ ↑ • Ex • Ex ↑) • (CZ ^ k • CZ02⁻ᵏ k • CX ↑) • ⟦ nf1 ⟧₁ ↑ ↑ • ⟦ m ⁻¹ ⟧ₘ ↑ • S^ hs ↑ ≈⟨ special-assoc (□ ^ 3 • □ ^ 3 • □) (□ • (□ ^ 2 • □) • □ ^ 2 • □) auto ⟩
    H ↑ ↑ • ((Ex • Ex ↑) • CZ ^ k) • (CZ02⁻ᵏ k • CX ↑) • ⟦ nf1 ⟧₁ ↑ ↑ • ⟦ m ⁻¹ ⟧ₘ ↑ • S^ hs ↑ ≈⟨ (cright cleft lemma-Induction lemma-[Ex-Ex↑]-CZ k) ⟩
    H ↑ ↑ • (CZ ↑ ^ k • Ex • Ex ↑) • (CZ02⁻ᵏ k • CX ↑) • ⟦ nf1 ⟧₁ ↑ ↑ • ⟦ m ⁻¹ ⟧ₘ ↑ • S^ hs ↑ ≈⟨ (cright cright cleft cleft lemma-CZ02⁻ᵏ-alt k) ⟩
    H ↑ ↑ • (CZ ↑ ^ k • Ex • Ex ↑) • (CZ02'⁻ᵏ k • CX ↑) • ⟦ nf1 ⟧₁ ↑ ↑ • ⟦ m ⁻¹ ⟧ₘ ↑ • S^ hs ↑ ≈⟨ (cright special-assoc (□ ^ 3 • (□ ^ 3 • □) • □ ) (□ ^ 2 • □ ^ 2 • □ ^ 4) auto) ⟩
    H ↑ ↑ • (CZ ↑ ^ k • Ex) • (Ex ↑ • Ex ↑) • CZ⁻¹ ^ k • Ex ↑ • CX ↑ • ⟦ nf1 ⟧₁ ↑ ↑ • ⟦ m ⁻¹ ⟧ₘ ↑ • S^ hs ↑ ≈⟨ (cright cright cleft lemma-cong↑ _ _ lemma-order-Ex-n) ⟩
    H ↑ ↑ • (CZ ↑ ^ k • Ex) • ε • CZ⁻¹ ^ k • Ex ↑ • CX ↑ • ⟦ nf1 ⟧₁ ↑ ↑ • ⟦ m ⁻¹ ⟧ₘ ↑ • S^ hs ↑ ≈⟨ (cright cright left-unit) ⟩
    H ↑ ↑ • (CZ ↑ ^ k • Ex) • CZ⁻¹ ^ k • Ex ↑ • CX ↑ • ⟦ nf1 ⟧₁ ↑ ↑ • ⟦ m ⁻¹ ⟧ₘ ↑ • S^ hs ↑ ≈⟨ (cright cright cleft aux-CZ^-k m⁻¹) ⟩
    H ↑ ↑ • (CZ ↑ ^ k • Ex) • CZ^ (- m⁻¹) • Ex ↑ • CX ↑ • ⟦ nf1 ⟧₁ ↑ ↑ • ⟦ m ⁻¹ ⟧ₘ ↑ • S^ hs ↑ ≈⟨ (cright cright cright sym left-unit) ⟩
    H ↑ ↑ • (CZ ↑ ^ k • Ex) • CZ^ (- m⁻¹) • ε • Ex ↑ • CX ↑ • ⟦ nf1 ⟧₁ ↑ ↑ • ⟦ m ⁻¹ ⟧ₘ ↑ • S^ hs ↑ ≈⟨ (cright cright cright  cleft sym (aux-M-mulˡ (m))) ⟩
    H ↑ ↑ • (CZ ↑ ^ k • Ex) • CZ^ (- m⁻¹) • (ZM ((m) ⁻¹) • ZM (m)) • Ex ↑ • CX ↑ • ⟦ nf1 ⟧₁ ↑ ↑ • ⟦ m ⁻¹ ⟧ₘ ↑ • S^ hs ↑ ≈⟨ special-assoc (□ • □ ^ 2 • □ • □ ^ 2 • □ • □ ^ 3 • □ ^ 2) (□ • □ ^ 2 • □ ^ 2 • □ • □ • □ • □ • □ ^ 2 • □) auto ⟩
    H ↑ ↑ • (CZ ↑ ^ k • Ex) • (CZ^ (- m⁻¹) • ZM ((m) ⁻¹)) • ZM (m) • Ex ↑ • H ↑ ^ 3 • CZ ↑ • (H ↑ • ⟦ nf1 ⟧₁ ↑ ↑) • ⟦ m ⁻¹ ⟧ₘ ↑ • S^ hs ↑ ≈⟨ (cright cright cleft cleft refl' (Eq.cong CZ^ (Eq.sym (-1*x≈-x m⁻¹)))) ⟩
    H ↑ ↑ • (CZ ↑ ^ k • Ex) • (CZ^ (- ₁ * m⁻¹) • ZM ((m) ⁻¹)) • ZM (m) • Ex ↑ • H ↑ ^ 3 • CZ ↑ • (H ↑ • ⟦ nf1 ⟧₁ ↑ ↑) • ⟦ m ⁻¹ ⟧ₘ ↑ • S^ hs ↑ ≈⟨ (cright cright cong (sym (L2Q.lemma-M↓CZ^k m⁻¹ (- ₁) ((m ⁻¹) .proj₂))) (cright cright cright cright (cleft lemma-cong↑ _ _ (lemma-comm-H-w↑ ⟦ nf1 ⟧₁)))) ⟩
    H ↑ ↑ • (CZ ↑ ^ k • Ex) • (ZM ((m) ⁻¹) • CZ^ (- ₁)) • ZM (m) • Ex ↑ • H ↑ ^ 3 • CZ ↑ • (⟦ nf1 ⟧₁ ↑ ↑ • H ↑) • ⟦ m ⁻¹ ⟧ₘ ↑ • S^ hs ↑ ≈⟨ (cright cright cright cright  special-assoc (□ • □ • □ • □ ^ 2 • □ ^ 2) (□ ^ 2 • □ • □ • □ ^ 2 • □) auto) ⟩
    H ↑ ↑ • (CZ ↑ ^ k • Ex) • (ZM ((m) ⁻¹) • CZ^ (- ₁)) • ZM (m) • (Ex ↑ • H ↑ ^ 3) • CZ ↑ • ⟦ nf1 ⟧₁ ↑ ↑ • (H ↑ • ⟦ m ⁻¹ ⟧ₘ ↑) • S^ hs ↑ ≈⟨ (cright cright cright cright  cong (lemma-Induction (lemma-cong↑ _ _ lemma-Ex-H) 3) (cright cright (cleft lemma-cong↑ _ _ (semi-HM' m)))) ⟩
    H ↑ ↑ • (CZ ↑ ^ k • Ex) • (ZM ((m) ⁻¹) • CZ^ (- ₁)) • ZM (m) • (H ↑ ↑ ^ 3 • Ex ↑) • CZ ↑ • ⟦ nf1 ⟧₁ ↑ ↑ • (⟦ m ⟧ₘ ↑ • H ↑) • S^ hs ↑ ≈⟨ (cright cright cright cright cright cright cong refl assoc) ⟩
    H ↑ ↑ • (CZ ↑ ^ k • Ex) • (ZM ((m) ⁻¹) • CZ^ (- ₁)) • ZM (m) • (H ↑ ↑ ^ 3 • Ex ↑) • CZ ↑ • ⟦ nf1 ⟧₁ ↑ ↑ • ⟦ m ⟧ₘ ↑ • H ↑ • S^ hs ↑ ≈⟨ (cright cright cright cright assoc) ⟩
    H ↑ ↑ • (CZ ↑ ^ k • Ex) • (ZM ((m) ⁻¹) • CZ^ (- ₁)) • ZM (m) • H ↑ ↑ ^ 3 • Ex ↑ • CZ ↑ • ⟦ nf1 ⟧₁ ↑ ↑ • ⟦ m ⟧ₘ ↑ • H ↑ • S^ hs ↑ ≈⟨ refl ⟩
    H ↑ ↑ • (CZ ↑ ^ k • Ex) • (ZM ((m) ⁻¹) • CZ^ (- ₁)) • ZM (m) • H ↑ ↑ ^ 3 • ⟦ c2 ⟧₂ ↑ ≈⟨ (cright cright cright sym assoc) ⟩
    H ↑ ↑ • (CZ ↑ ^ k • Ex) • (ZM ((m) ⁻¹) • CZ^ (- ₁)) • (ZM (m) • H ↑ ↑ ^ 3) • ⟦ c2 ⟧₂ ↑ ≈⟨ (cright cright cright (cleft aux-comm-m-w↑ (m) (H ↑ ^ 3))) ⟩
    H ↑ ↑ • (CZ ↑ ^ k • Ex) • (ZM ((m) ⁻¹) • CZ^ (- ₁)) • (H ↑ ↑ ^ 3 • ZM (m)) • ⟦ c2 ⟧₂ ↑ ≈⟨ special-assoc (□ • □ ^ 2 • □ ^ 2 • □ ^ 2 • □) (□ ^ 2 • □ ^ 2 • □ ^ 2 • □ ^ 2) auto ⟩
    (H ↑ ↑ • CZ ↑ ^ k) • (Ex • ZM ((m) ⁻¹)) • (CZ^ (- ₁) • H ↑ ↑ ^ 3) • ZM (m) • ⟦ c2 ⟧₂ ↑ ≈⟨ (cright cong (Sym4n.lemma-Ex-M-n 1 ((m) ⁻¹)) (cleft word-comm (toℕ (- ₁)) 3 (lemma-comm-CZ-w↑↑ H))) ⟩
    (H ↑ ↑ • CZ ↑ ^ k) • (ZM ((m) ⁻¹) ↑ • Ex) • (H ↑ ↑ ^ 3 • CZ^ (- ₁)) • ZM (m) • ⟦ c2 ⟧₂ ↑ ≈⟨ special-assoc (□ ^ 2 • □ ^ 2 • □ ^ 2 • □ ^ 2) (□ ^ 3 • □ ^ 2 • □ ^ 3) auto ⟩
    (H ↑ ↑ • CZ ↑ ^ k • ZM ((m) ⁻¹) ↑) • (Ex • H ↑ ↑ ^ 3) • CZ^ (- ₁) • ZM (m) • ⟦ c2 ⟧₂ ↑ ≈⟨ (cright cleft word-comm 1 3 (lemma-comm-Ex-w↑↑ H)) ⟩
    (H ↑ ↑ • CZ ↑ ^ k • ZM ((m) ⁻¹) ↑) • (H ↑ ↑ ^ 3 • Ex) • CZ^ (- ₁) • ZM (m) • ⟦ c2 ⟧₂ ↑ ≈⟨ (cleft cright cleft refl' (lemma-^-↑ CZ k)) ⟩
    (H ↑ ↑ • (CZ ^ k) ↑ • ZM ((m) ⁻¹) ↑) • (H ↑ ↑ ^ 3 • Ex) • CZ^ (- ₁) • ZM (m) • ⟦ c2 ⟧₂ ↑ ≈⟨ special-assoc (□ ^ 3 • □ ^ 2 • □ ^ 3) (□ ^ 4 • □ • □ • □ ^ 2) auto ⟩
    (H ↑ • CZ ^ k • ZM ((m) ⁻¹) • H ↑ ^ 3) ↑ • Ex • CZ^ (- ₁) • ZM ((m)) • ⟦ c2 ⟧₂ ↑ ≈⟨ (cright cright cright cleft sym (aux-MM (((m)⁻¹ ⁻¹) .proj₂) ((m) .proj₂) (inv-involutive (m)))) ⟩
    (H ↑ • CZ ^ k • ZM ((m) ⁻¹) • H ↑ ^ 3) ↑ • Ex • CZ^ (- ₁) • ZM ((m)⁻¹ ⁻¹) • ⟦ c2 ⟧₂ ↑ ≈⟨  (cright special-assoc (□ ^ 4) (□ ^ 3 • □) auto) ⟩
    (H ↑ • CZ ^ k • ZM ((m) ⁻¹) • H ↑ ^ 3) ↑ • (Ex • CZ^ (- ₁) • ZM ((m)⁻¹ ⁻¹)) • ⟦ c2 ⟧₂ ↑ ≈⟨  (cright cleft sym (aux-dbox-nzb' m⁻¹ ((m ⁻¹) .proj₂))) ⟩
    (H ↑ • CZ ^ k • ZM ((m) ⁻¹) • H ↑ ^ 3) ↑ • [ ₀ , m⁻¹ ]ᵈ • ⟦ c2 ⟧₂ ↑ ≈⟨  refl ⟩
    
    (w ↑) • [ lm' ]ˡᵐ' ∎



lemma-coset-update {n@2} lm@(case-I d@(a@₀ , b@₀) c2@(case-Ex-| nf1 mc@(m , ε))) g@CZ-gen = lm' , w  , claim
  where
  m' = m .proj₁
  w = CZ^ m'
  lm' = case-I d c2

  open PB ((₁₊ n) QRel,_===_)  
  open PP ((₁₊ n) QRel,_===_)
  open SR word-setoid
  open Pattern-Assoc
  claim : [ lm ]ˡᵐ' • CZ ≈ (w ↑) • [ lm' ]ˡᵐ'
  claim = begin
    [ lm ]ˡᵐ' • CZ ≈⟨ refl ⟩
    (Ex • ((Ex • CZ • ⟦ nf1 ⟧₁ ↑ • ⟦ mc ⟧ₘ₊) ↑)) • CZ ≈⟨ (cleft (cright cright cright cright right-unit)) ⟩
    (Ex • ((Ex • CZ • ⟦ nf1 ⟧₁ ↑ • ⟦ m ⟧ₘ) ↑)) • CZ ≈⟨ special-assoc (□ ^ 5 • □) (□ ^ 4 • □ ^ 2) auto ⟩
    (Ex • Ex ↑ • CZ ↑ • ⟦ nf1 ⟧₁ ↑ ↑) • ⟦ m ⟧ₘ ↑ • CZ ≈⟨ (cright axiom (semi-M↑CZ m)) ⟩
    (Ex • Ex ↑ • CZ ↑ • ⟦ nf1 ⟧₁ ↑ ↑) • CZ^ m' • ⟦ m ⟧ₘ ↑ ≈⟨ special-assoc (□ ^ 4 • □ ^ 2) (□ ^ 3 • □ ^ 2 • □) auto ⟩
    (Ex • Ex ↑ • CZ ↑) • (⟦ nf1 ⟧₁ ↑ ↑ • CZ^ m') • ⟦ m ⟧ₘ ↑ ≈⟨ (cright cleft word-comm 1 (toℕ m') (sym (lemma-comm-CZ-w↑↑ ⟦ nf1 ⟧₁))) ⟩
    (Ex • Ex ↑ • CZ ↑) • (CZ^ m' • ⟦ nf1 ⟧₁ ↑ ↑) • ⟦ m ⟧ₘ ↑ ≈⟨ special-assoc (□ ^ 3 • □ ^ 2 • □) (□ ^ 2 • □ ^ 2 • □ ^ 2) auto ⟩
    (Ex • Ex ↑) • (CZ ↑ • CZ^ m') • ⟦ nf1 ⟧₁ ↑ ↑ • ⟦ m ⟧ₘ ↑ ≈⟨ (cright cleft word-comm 1 (toℕ m') (axiom selinger-c12)) ⟩
    (Ex • Ex ↑) • (CZ^ m' • CZ ↑) • ⟦ nf1 ⟧₁ ↑ ↑ • ⟦ m ⟧ₘ ↑ ≈⟨ special-assoc (□ • □ ^ 2 • □) (□ ^ 2 • □ ^ 2) auto ⟩
    ((Ex • Ex ↑) • CZ^ m') • CZ ↑ • ⟦ nf1 ⟧₁ ↑ ↑ • ⟦ m ⟧ₘ ↑ ≈⟨ (cleft lemma-Induction lemma-[Ex-Ex↑]-CZ (toℕ m')) ⟩
    (CZ ↑ ^ toℕ m' • Ex • Ex ↑) • CZ ↑ • ⟦ nf1 ⟧₁ ↑ ↑ • ⟦ m ⟧ₘ ↑ ≈⟨ (cleft cleft refl' (lemma-^-↑ CZ (toℕ m'))) ⟩
    ((CZ ^ toℕ m') ↑ • Ex • Ex ↑) • CZ ↑ • ⟦ nf1 ⟧₁ ↑ ↑ • ⟦ m ⟧ₘ ↑ ≈⟨ special-assoc (□ ^ 3 • □ ^ 3) (□ • □ ^ 5) auto ⟩
    (CZ^ m') ↑ • Ex • Ex ↑ • CZ ↑ • ⟦ nf1 ⟧₁ ↑ ↑ • ⟦ m ⟧ₘ ↑ ≈⟨ (cright cright cright cright cright sym right-unit) ⟩
    (w ↑) • [ lm' ]ˡᵐ' ∎


lemma-coset-update {n@2} lm@(case-I d@(a@₀ , b@₀) (case-Ex-nf1 nf1)) g@CZ-gen = lm' , w  , claim
  where
  w = CZ
  lm' = case-I d (case-Ex-nf1 nf1)

  open PB ((₁₊ n) QRel,_===_)  
  open PP ((₁₊ n) QRel,_===_)
  open SR word-setoid
  open Pattern-Assoc
  claim : [ lm ]ˡᵐ' • CZ ≈ (w ↑) • [ lm' ]ˡᵐ'
  claim = begin
    [ lm ]ˡᵐ' • CZ ≈⟨ refl ⟩
    (Ex • ((Ex • (⟦ nf1 ⟧₁ ↑)) ↑)) • CZ ≈⟨ special-assoc (□ ^ 3 • □) (□ ^ 2 • □ ^ 2) auto ⟩
    (Ex • Ex ↑) • ⟦ nf1 ⟧₁ ↑ ↑ • CZ ≈⟨ (cright sym (lemma-comm-CZ-w↑↑ ⟦ nf1 ⟧₁)) ⟩
    (Ex • Ex ↑) • CZ • ⟦ nf1 ⟧₁ ↑ ↑ ≈⟨ sym (special-assoc (□ ^ 3 • □) (□ ^ 2 • □ ^ 2) auto) ⟩
    (Ex • Ex ↑ • CZ) • ⟦ nf1 ⟧₁ ↑ ↑ ≈⟨ (cleft lemma-Ex-Ex↑-CZ) ⟩
    (CZ ↑ • Ex • Ex ↑) • ⟦ nf1 ⟧₁ ↑ ↑ ≈⟨ special-assoc (□ ^ 3 • □) (□ ^ 4) auto ⟩
    (w ↑) • [ lm' ]ˡᵐ' ∎

-}

lemma-coset-update {n@2} lm@(case-I d c2@(case-nf1 nf1@(s , mc@(m , ε)))) CZ-gen = lm' , w , claim
  where
  w = dir-of-DH^3 d
  xy : B'
  y = m .proj₁
  xy = (₀ , y)
  lm' = case-II (d-of-DH^3 d) (case-nf1 nf1) xy
  open PB ((₁₊ n) QRel,_===_)  
  open PP ((₁₊ n) QRel,_===_)
  open SR word-setoid
  open Pattern-Assoc
  open Lemmas0 2
  open Rewriting-Powers n
  
  claim : [ case-I d c2 ]ˡᵐ' • CZ ≈ w ↑ • [ lm' ]ˡᵐ'
  claim = begin
    [ case-I d c2 ]ˡᵐ' • CZ ≈⟨ refl ⟩
    ([ d ]ᵈ • ⟦ c2 ⟧₂ ↑)  • CZ ≈⟨ (cleft cright lemma-cong↑ _ _ (aux-mc-of2 c2)) ⟩
    ([ d ]ᵈ • (⟦ rm-mc2 c2 ⟧₂ • ⟦ mc-of2 c2 ⟧ₘ₊) ↑) • CZ ≈⟨ refl ⟩
    ([ d ]ᵈ • ⟦ rm-mc2 c2 ⟧₂ ↑ • ⟦ m , ε ⟧ₘ₊ ↑) • CZ ≈⟨ special-assoc (□ ^ 3 • □) (□ ^ 2 • □ ^ 2) auto ⟩
    ([ d ]ᵈ • ⟦ rm-mc2 c2 ⟧₂ ↑) • ⟦ m , ε ⟧ₘ₊ ↑ • CZ ≈⟨ (cright cleft right-unit) ⟩
    ([ d ]ᵈ • ⟦ rm-mc2 c2 ⟧₂ ↑) • (⟦ m ⟧ₘ ↑  • CZ) ≈⟨ (cright axiom (semi-M↑CZ m)) ⟩
    ([ d ]ᵈ • ⟦ rm-mc2 c2 ⟧₂ ↑) • (CZ^ y • ⟦ m ⟧ₘ ↑) ≈⟨ (cright cright sym right-unit) ⟩
    ([ d ]ᵈ • ⟦ rm-mc2 c2 ⟧₂ ↑) • (CZ^ y • (⟦ m ⟧ₘ • ε) ↑) ≈⟨ sym (cong refl left-unit) ⟩
    ([ d ]ᵈ • ⟦ rm-mc2 c2 ⟧₂ ↑) • ε • (CZ^ y • (⟦ m ⟧ₘ • ε) ↑) ≈⟨ (cright (cleft rewrite-powers 100 auto)) ⟩
    ([ d ]ᵈ • ⟦ rm-mc2 c2 ⟧₂ ↑) • (H ^ 3 • CZ ^ 0 • H) • (CZ^ y • (⟦ m ⟧ₘ • ε) ↑) ≈⟨ special-assoc (□ ^ 2 • □ ^ 3 • □ ^ 2) (□ • □ ^ 2 • □ ^ 3 • □) auto ⟩
    [ d ]ᵈ • (⟦ rm-mc2 c2 ⟧₂ ↑ • H ^ 3) • (CZ ^ 0 • H • CZ^ y) • (⟦ m ⟧ₘ • ε) ↑ ≈⟨ (cright cleft sym (lemma-comm-Hᵏ-w↑ 3 ⟦ rm-mc2 c2 ⟧₂)) ⟩
    [ d ]ᵈ • (H ^ 3 • ⟦ rm-mc2 c2 ⟧₂ ↑) • (CZ ^ 0 • H • CZ^ y) • (⟦ m ⟧ₘ • ε) ↑ ≈⟨ special-assoc (□ • □ ^ 2 • □) ((□ ^ 2 • □) • □) auto ⟩
    (([ d ]ᵈ • H ^ 3) • ⟦ rm-mc2 c2 ⟧₂ ↑) • (CZ ^ 0 • H • CZ^ y) • (⟦ m ⟧ₘ • ε) ↑ ≈⟨ (cleft cleft aux-DH^3 d ) ⟩
    ((w ↑ • [ d-of-DH^3 d ]ᵈ) • ⟦ rm-mc2 c2 ⟧₂ ↑) • (CZ ^ 0 • H • CZ^ y) • (⟦ m ⟧ₘ • ε) ↑ ≈⟨ refl ⟩
    ((w ↑ • [ d-of-DH^3 d ]ᵈ) • ⟦ rm-mc2 c2 ⟧₂ ↑) • (CZ ^ 0 • H • CZ^ y) • (⟦ m ⟧ₘ • ε) ↑ ≈⟨ special-assoc ((□ ^ 2 • □ ^ 2) • □) (□ • □ ^ 3 • □) auto ⟩
    w ↑ • ([ d-of-DH^3 d ]ᵈ • ⟦ rm-mc2 c2 ⟧₂ ↑) • (CZ ^ 0 • H • CZ^ y) • (⟦ m ⟧ₘ • ε) ↑ ≈⟨ cong refl {!!} ⟩
    w ↑ • [ lm' ]ˡᵐ' ∎



{-
lemma-coset-update {n@2} lm@(case-I d c2@(case-| mc↑ nf1@(s , mc@(m , ε)))) CZ-gen = lm' , w , claim
  where
  w = dir-of-DH^3 d
  xy : B'
  y = m .proj₁
  xy = (₀ , y)
  lm' = case-II (d-of-DH^3 d) (case-| mc↑ nf1) xy
  open PB ((₁₊ n) QRel,_===_)  
  open PP ((₁₊ n) QRel,_===_)
  open SR word-setoid
  open Pattern-Assoc
  open Lemmas0 2
  open Rewriting-Powers n
  
  claim : [ case-I d c2 ]ˡᵐ' • CZ ≈ w ↑ • [ lm' ]ˡᵐ'
  claim = begin
    [ case-I d c2 ]ˡᵐ' • CZ ≈⟨ refl ⟩
    ([ d ]ᵈ • ⟦ c2 ⟧₂ ↑)  • CZ ≈⟨ (cleft cright lemma-cong↑ _ _ (aux-mc-of2 c2)) ⟩
    ([ d ]ᵈ • (⟦ rm-mc2 c2 ⟧₂ • ⟦ mc-of2 c2 ⟧ₘ₊) ↑) • CZ ≈⟨ refl ⟩
    ([ d ]ᵈ • ⟦ rm-mc2 c2 ⟧₂ ↑ • ⟦ m , ε ⟧ₘ₊ ↑) • CZ ≈⟨ special-assoc (□ ^ 3 • □) (□ ^ 2 • □ ^ 2) auto ⟩
    ([ d ]ᵈ • ⟦ rm-mc2 c2 ⟧₂ ↑) • ⟦ m , ε ⟧ₘ₊ ↑ • CZ ≈⟨ (cright cleft right-unit) ⟩
    ([ d ]ᵈ • ⟦ rm-mc2 c2 ⟧₂ ↑) • (⟦ m ⟧ₘ ↑  • CZ) ≈⟨ (cright axiom (semi-M↑CZ m)) ⟩
    ([ d ]ᵈ • ⟦ rm-mc2 c2 ⟧₂ ↑) • (CZ^ y • ⟦ m ⟧ₘ ↑) ≈⟨ (cright cright sym right-unit) ⟩
    ([ d ]ᵈ • ⟦ rm-mc2 c2 ⟧₂ ↑) • (CZ^ y • (⟦ m ⟧ₘ • ε) ↑) ≈⟨ sym (cong refl left-unit) ⟩
    ([ d ]ᵈ • ⟦ rm-mc2 c2 ⟧₂ ↑) • ε • (CZ^ y • (⟦ m ⟧ₘ • ε) ↑) ≈⟨ (cright (cleft rewrite-powers 100 auto)) ⟩
    ([ d ]ᵈ • ⟦ rm-mc2 c2 ⟧₂ ↑) • (H ^ 3 • CZ ^ 0 • H) • (CZ^ y • (⟦ m ⟧ₘ • ε) ↑) ≈⟨ special-assoc (□ ^ 2 • □ ^ 3 • □ ^ 2) (□ • □ ^ 2 • □ ^ 3 • □) auto ⟩
    [ d ]ᵈ • (⟦ rm-mc2 c2 ⟧₂ ↑ • H ^ 3) • (CZ ^ 0 • H • CZ^ y) • (⟦ m ⟧ₘ • ε) ↑ ≈⟨ (cright cleft sym (lemma-comm-Hᵏ-w↑ 3 ⟦ rm-mc2 c2 ⟧₂)) ⟩
    [ d ]ᵈ • (H ^ 3 • ⟦ rm-mc2 c2 ⟧₂ ↑) • (CZ ^ 0 • H • CZ^ y) • (⟦ m ⟧ₘ • ε) ↑ ≈⟨ special-assoc (□ • □ ^ 2 • □) ((□ ^ 2 • □) • □) auto ⟩
    (([ d ]ᵈ • H ^ 3) • ⟦ rm-mc2 c2 ⟧₂ ↑) • (CZ ^ 0 • H • CZ^ y) • (⟦ m ⟧ₘ • ε) ↑ ≈⟨ (cleft cleft aux-DH^3 d ) ⟩
    ((w ↑ • [ d-of-DH^3 d ]ᵈ) • ⟦ rm-mc2 c2 ⟧₂ ↑) • (CZ ^ 0 • H • CZ^ y) • (⟦ m ⟧ₘ • ε) ↑ ≈⟨ refl ⟩
    ((w ↑ • [ d-of-DH^3 d ]ᵈ) • ⟦ rm-mc2 c2 ⟧₂ ↑) • (CZ ^ 0 • H • CZ^ y) • (⟦ m ⟧ₘ • ε) ↑ ≈⟨ special-assoc ((□ ^ 2 • □ ^ 2) • □) (□ • □ ^ 3 • □) auto ⟩
    w ↑ • ([ d-of-DH^3 d ]ᵈ • ⟦ rm-mc2 c2 ⟧₂ ↑) • (CZ ^ 0 • H • CZ^ y) • (⟦ m ⟧ₘ • ε) ↑ ≈⟨ cong refl {!!} ⟩
    w ↑ • [ lm' ]ˡᵐ' ∎


lemma-coset-update {n@2} lm@(case-I d c2@(case-|| k* l pf@(s , mc↑ , mc@(m , ε)))) CZ-gen = lm' , w , claim
  where
  w = dir-of-DH^3 d
  xy : B'
  y = m .proj₁
  xy = (₀ , y)
  lm' = case-II (d-of-DH^3 d) (case-|| k* l pf) xy
  open PB ((₁₊ n) QRel,_===_)  
  open PP ((₁₊ n) QRel,_===_)
  open SR word-setoid
  open Pattern-Assoc
  open Lemmas0 2
  open Rewriting-Powers n
  
  claim : [ case-I d c2 ]ˡᵐ' • CZ ≈ w ↑ • [ lm' ]ˡᵐ'
  claim = begin
    [ case-I d c2 ]ˡᵐ' • CZ ≈⟨ refl ⟩
    ([ d ]ᵈ • ⟦ c2 ⟧₂ ↑)  • CZ ≈⟨ (cleft cright lemma-cong↑ _ _ (aux-mc-of2 c2)) ⟩
    ([ d ]ᵈ • (⟦ rm-mc2 c2 ⟧₂ • ⟦ mc-of2 c2 ⟧ₘ₊) ↑) • CZ ≈⟨ refl ⟩
    ([ d ]ᵈ • ⟦ rm-mc2 c2 ⟧₂ ↑ • ⟦ m , ε ⟧ₘ₊ ↑) • CZ ≈⟨ special-assoc (□ ^ 3 • □) (□ ^ 2 • □ ^ 2) auto ⟩
    ([ d ]ᵈ • ⟦ rm-mc2 c2 ⟧₂ ↑) • ⟦ m , ε ⟧ₘ₊ ↑ • CZ ≈⟨ (cright cleft right-unit) ⟩
    ([ d ]ᵈ • ⟦ rm-mc2 c2 ⟧₂ ↑) • (⟦ m ⟧ₘ ↑  • CZ) ≈⟨ (cright axiom (semi-M↑CZ m)) ⟩
    ([ d ]ᵈ • ⟦ rm-mc2 c2 ⟧₂ ↑) • (CZ^ y • ⟦ m ⟧ₘ ↑) ≈⟨ (cright cright sym right-unit) ⟩
    ([ d ]ᵈ • ⟦ rm-mc2 c2 ⟧₂ ↑) • (CZ^ y • (⟦ m ⟧ₘ • ε) ↑) ≈⟨ sym (cong refl left-unit) ⟩
    ([ d ]ᵈ • ⟦ rm-mc2 c2 ⟧₂ ↑) • ε • (CZ^ y • (⟦ m ⟧ₘ • ε) ↑) ≈⟨ (cright (cleft rewrite-powers 100 auto)) ⟩
    ([ d ]ᵈ • ⟦ rm-mc2 c2 ⟧₂ ↑) • (H ^ 3 • CZ ^ 0 • H) • (CZ^ y • (⟦ m ⟧ₘ • ε) ↑) ≈⟨ special-assoc (□ ^ 2 • □ ^ 3 • □ ^ 2) (□ • □ ^ 2 • □ ^ 3 • □) auto ⟩
    [ d ]ᵈ • (⟦ rm-mc2 c2 ⟧₂ ↑ • H ^ 3) • (CZ ^ 0 • H • CZ^ y) • (⟦ m ⟧ₘ • ε) ↑ ≈⟨ (cright cleft sym (lemma-comm-Hᵏ-w↑ 3 ⟦ rm-mc2 c2 ⟧₂)) ⟩
    [ d ]ᵈ • (H ^ 3 • ⟦ rm-mc2 c2 ⟧₂ ↑) • (CZ ^ 0 • H • CZ^ y) • (⟦ m ⟧ₘ • ε) ↑ ≈⟨ special-assoc (□ • □ ^ 2 • □) ((□ ^ 2 • □) • □) auto ⟩
    (([ d ]ᵈ • H ^ 3) • ⟦ rm-mc2 c2 ⟧₂ ↑) • (CZ ^ 0 • H • CZ^ y) • (⟦ m ⟧ₘ • ε) ↑ ≈⟨ (cleft cleft aux-DH^3 d ) ⟩
    ((w ↑ • [ d-of-DH^3 d ]ᵈ) • ⟦ rm-mc2 c2 ⟧₂ ↑) • (CZ ^ 0 • H • CZ^ y) • (⟦ m ⟧ₘ • ε) ↑ ≈⟨ refl ⟩
    ((w ↑ • [ d-of-DH^3 d ]ᵈ) • ⟦ rm-mc2 c2 ⟧₂ ↑) • (CZ ^ 0 • H • CZ^ y) • (⟦ m ⟧ₘ • ε) ↑ ≈⟨ special-assoc ((□ ^ 2 • □ ^ 2) • □) (□ • □ ^ 3 • □) auto ⟩
    w ↑ • ([ d-of-DH^3 d ]ᵈ • ⟦ rm-mc2 c2 ⟧₂ ↑) • (CZ ^ 0 • H • CZ^ y) • (⟦ m ⟧ₘ • ε) ↑ ≈⟨ cong refl {!!} ⟩
    w ↑ • [ lm' ]ˡᵐ' ∎


lemma-coset-update {n@2} lm@(case-I d c2@(case-||ₐ k pf@(s , mc↑ , mc@(m , ε)))) CZ-gen = lm' , w , claim
  where
  w = dir-of-DH^3 d
  xy : B'
  y = m .proj₁
  xy = (₀ , y)
  lm' = case-II (d-of-DH^3 d) (case-||ₐ k pf) xy
  open PB ((₁₊ n) QRel,_===_)  
  open PP ((₁₊ n) QRel,_===_)
  open SR word-setoid
  open Pattern-Assoc
  open Lemmas0 2
  open Rewriting-Powers n
  
  claim : [ case-I d c2 ]ˡᵐ' • CZ ≈ w ↑ • [ lm' ]ˡᵐ'
  claim = begin
    [ case-I d c2 ]ˡᵐ' • CZ ≈⟨ refl ⟩
    ([ d ]ᵈ • ⟦ c2 ⟧₂ ↑)  • CZ ≈⟨ (cleft cright lemma-cong↑ _ _ (aux-mc-of2 c2)) ⟩
    ([ d ]ᵈ • (⟦ rm-mc2 c2 ⟧₂ • ⟦ mc-of2 c2 ⟧ₘ₊) ↑) • CZ ≈⟨ refl ⟩
    ([ d ]ᵈ • ⟦ rm-mc2 c2 ⟧₂ ↑ • ⟦ m , ε ⟧ₘ₊ ↑) • CZ ≈⟨ special-assoc (□ ^ 3 • □) (□ ^ 2 • □ ^ 2) auto ⟩
    ([ d ]ᵈ • ⟦ rm-mc2 c2 ⟧₂ ↑) • ⟦ m , ε ⟧ₘ₊ ↑ • CZ ≈⟨ (cright cleft right-unit) ⟩
    ([ d ]ᵈ • ⟦ rm-mc2 c2 ⟧₂ ↑) • (⟦ m ⟧ₘ ↑  • CZ) ≈⟨ (cright axiom (semi-M↑CZ m)) ⟩
    ([ d ]ᵈ • ⟦ rm-mc2 c2 ⟧₂ ↑) • (CZ^ y • ⟦ m ⟧ₘ ↑) ≈⟨ (cright cright sym right-unit) ⟩
    ([ d ]ᵈ • ⟦ rm-mc2 c2 ⟧₂ ↑) • (CZ^ y • (⟦ m ⟧ₘ • ε) ↑) ≈⟨ sym (cong refl left-unit) ⟩
    ([ d ]ᵈ • ⟦ rm-mc2 c2 ⟧₂ ↑) • ε • (CZ^ y • (⟦ m ⟧ₘ • ε) ↑) ≈⟨ (cright (cleft rewrite-powers 100 auto)) ⟩
    ([ d ]ᵈ • ⟦ rm-mc2 c2 ⟧₂ ↑) • (H ^ 3 • CZ ^ 0 • H) • (CZ^ y • (⟦ m ⟧ₘ • ε) ↑) ≈⟨ special-assoc (□ ^ 2 • □ ^ 3 • □ ^ 2) (□ • □ ^ 2 • □ ^ 3 • □) auto ⟩
    [ d ]ᵈ • (⟦ rm-mc2 c2 ⟧₂ ↑ • H ^ 3) • (CZ ^ 0 • H • CZ^ y) • (⟦ m ⟧ₘ • ε) ↑ ≈⟨ (cright cleft sym (lemma-comm-Hᵏ-w↑ 3 ⟦ rm-mc2 c2 ⟧₂)) ⟩
    [ d ]ᵈ • (H ^ 3 • ⟦ rm-mc2 c2 ⟧₂ ↑) • (CZ ^ 0 • H • CZ^ y) • (⟦ m ⟧ₘ • ε) ↑ ≈⟨ special-assoc (□ • □ ^ 2 • □) ((□ ^ 2 • □) • □) auto ⟩
    (([ d ]ᵈ • H ^ 3) • ⟦ rm-mc2 c2 ⟧₂ ↑) • (CZ ^ 0 • H • CZ^ y) • (⟦ m ⟧ₘ • ε) ↑ ≈⟨ (cleft cleft aux-DH^3 d ) ⟩
    ((w ↑ • [ d-of-DH^3 d ]ᵈ) • ⟦ rm-mc2 c2 ⟧₂ ↑) • (CZ ^ 0 • H • CZ^ y) • (⟦ m ⟧ₘ • ε) ↑ ≈⟨ refl ⟩
    ((w ↑ • [ d-of-DH^3 d ]ᵈ) • ⟦ rm-mc2 c2 ⟧₂ ↑) • (CZ ^ 0 • H • CZ^ y) • (⟦ m ⟧ₘ • ε) ↑ ≈⟨ special-assoc ((□ ^ 2 • □ ^ 2) • □) (□ • □ ^ 3 • □) auto ⟩
    w ↑ • ([ d-of-DH^3 d ]ᵈ • ⟦ rm-mc2 c2 ⟧₂ ↑) • (CZ ^ 0 • H • CZ^ y) • (⟦ m ⟧ₘ • ε) ↑ ≈⟨ cong refl {!!} ⟩
    w ↑ • [ lm' ]ˡᵐ' ∎



lemma-coset-update {n@2} lm@(case-I d c2@(case-||ₐ k pf@(s , mc↑ , mc@(m , HS^ hs)))) CZ-gen = {!!}
lemma-coset-update {n@2} lm@(case-I d c2@(case-|| k* l pf@(s , mc↑ , mc@(m , HS^ hs)))) CZ-gen = {!!}
lemma-coset-update {n@2} lm@(case-I d c2@(case-nf1 nf1@(s , mc@(m , HS^ hs)))) CZ-gen = {!!}
lemma-coset-update {n@2} lm@(case-I d c2@(case-| mc↑ nf1@(s , mc@(m , HS^ hs)))) CZ-gen = {!!}



lemma-coset-update {n@₂} lm@(case-II d c2 b) H-gen = {!!}
lemma-coset-update {n@₂} lm@(case-II d c2 b) S-gen = {!!}


lemma-coset-update {n@2} (case-II d c2 b) g = {!!}
lemma-coset-update {n@(₃₊ n-3)} lm g = {!!}


-}
