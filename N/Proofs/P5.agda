{-# OPTIONS  --safe #-}
{-# OPTIONS --termination-depth=2 #-}
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
open import Data.List hiding ([_] ; _++_ ; last ; head ; tail ; _∷ʳ_)
open import Data.Vec hiding ([_])
import Data.Vec as Vec
open import Data.Fin hiding (_+_ ; _-_)

open import Data.Maybe
open import Data.Sum using (_⊎_ ; inj₁ ; inj₂ ; [_,_] ; [_,_]′)
open import Data.Unit using (⊤ ; tt)
open import Data.Empty using (⊥ ; ⊥-elim)

open import Word.Base as WB hiding (wfoldl ; _*)
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
open import Presentation.Tactics hiding ([_] ; inspect)
open import Data.Nat.Primality



module N.Proofs.P5 (p-2 : ℕ) (p-prime : Prime (2+ p-2))  where

pattern auto = Eq.refl

pattern ₀ = zero
pattern ₁ = suc ₀
pattern ₂ = suc ₁
pattern ₃ = suc ₂
pattern ₄ = 4
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


open import Zp.ModularArithmetic
open PrimeModulus p-2 p-prime
open import N.Symplectic p-2 p-prime
open import N.Lemmas-2Qupit-Sym p-2 p-prime
open import N.NF2-Sym p-2 p-prime
open Lemmas-2Q 0
open Symplectic
open Lemmas-Sym
open import N.NF1-Sym p-2 p-prime
open import N.Ex-Sym p-2 p-prime
open import N.Ex-Sym1 p-2 p-prime
open import N.Ex-Sym2 p-2 p-prime
open import N.Ex-Sym3 p-2 p-prime
open import N.Ex-Sym4 p-2 p-prime
open import N.Duality p-2 p-prime
open import N.Derived p-2 p-prime
open import N.Lemma-Comm p-2 p-prime 0
open import N.Cosets p-2 p-prime
open import N.Lemma-Postfix p-2 p-prime
open Lemmas0a
open Lemmas0a1
open Lemmas0b
open Lemmas0c

open LM2
open import N.Completeness1-Sym p-2 p-prime renaming (module Completeness to CP1) using ()

open PB (2 QRel,_===_)
open PP (2 QRel,_===_)
open SR word-setoid
open Pattern-Assoc

open import Algebra.Properties.Ring (+-*-ring p-2)
open import N.Proofs.P1

open Duality
open Lemmas0 1

lemma-postfix-case-| : ∀ s mc m'' k' ->
  let
  m'′ = m'' ⁻¹
  m' = -' m'′
  nf' = (k' * (m' .proj₁ * m' .proj₁) , m' , ε)
  in
  ⟦ (s , mc , (m'' , HS^ k')) ⟧ₚ ≈ S^ s • H ^ 3 • ⟦ case-| mc nf' ⟧₂
lemma-postfix-case-| s mc m'' k' = claim'
  where
  m'′ = m'' ⁻¹
  m' = -' m'′
  mc'' = (m'' , HS^ k')
  nf' = (k' * (m' .proj₁ * m' .proj₁) , m' , ε)
  claim' : ⟦ (s , mc , (m'' , HS^ k')) ⟧ₚ ≈ S^ s • H ^ 3 • ⟦ case-| mc nf' ⟧₂
  claim' = begin
    ⟦ (s , mc , mc'') ⟧ₚ ≈⟨ refl ⟩
    (S^ s • (H^ ₃ • CZ • H) • ⟦ mc ⟧ₘ₊ ↑ • ⟦ mc'' ⟧ₘ₊) ≈⟨ special-assoc (□ • □ ^ 3 • □ ^ 2) (□ ^ 3 • □ ^ 2 • □) auto ⟩
    (S^ s • H^ ₃ • CZ) • (H • ⟦ mc ⟧ₘ₊ ↑) • ⟦ mc'' ⟧ₘ₊ ≈⟨ (cright (cleft lemma-comm-H-w↑ ⟦ mc ⟧ₘ₊)) ⟩
    (S^ s • H^ ₃ • CZ) • (⟦ mc ⟧ₘ₊ ↑ • H) • ⟦ mc'' ⟧ₘ₊ ≈⟨ cright assoc ⟩
    (S^ s • H^ ₃ • CZ) • ⟦ mc ⟧ₘ₊ ↑ • (H • ⟦ mc'' ⟧ₘ₊) ≈⟨ (cright cright  sym assoc) ⟩
    (S^ s • H^ ₃ • CZ) • ⟦ mc ⟧ₘ₊ ↑ • ((H • ⟦ m'' ⟧ₘ) • H • S^ k') ≈⟨ (cright cright cleft  semi-HM m'') ⟩
    (S^ s • H^ ₃ • CZ) • ⟦ mc ⟧ₘ₊ ↑ • ((⟦ m'′ ⟧ₘ • H) • H • S^ k') ≈⟨ cright cright special-assoc (□ ^ 2 • □ ^ 2) (□ ^ 3 • □) auto ⟩
    (S^ s • H^ ₃ • CZ) • ⟦ mc ⟧ₘ₊ ↑ • ((⟦ m'′ ⟧ₘ • HH) • S^ k') ≈⟨ (cright cright cleft  cright lemma-HH-M-1) ⟩
    (S^ s • H^ ₃ • CZ) • ⟦ mc ⟧ₘ₊ ↑ • ((⟦ m'′ ⟧ₘ • M -'₁) • S^ k') ≈⟨ (cright cright cleft  axiom (M-mul m'′ -'₁)) ⟩
    (S^ s • H^ ₃ • CZ) • ⟦ mc ⟧ₘ₊ ↑ • (⟦ m'′ *' -'₁ ⟧ₘ • S^ k') ≈⟨ (cright cright cleft  aux-MM ((m'′ *' -'₁) .proj₂) (m' .proj₂) (Eq.trans (Eq.sym (-‿distribʳ-* (m'′ .proj₁) ₁)) (Eq.cong -_ (*-identityʳ (m'′ .proj₁))))) ⟩
    (S^ s • H^ ₃ • CZ) • ⟦ mc ⟧ₘ₊ ↑ • (⟦ m' ⟧ₘ • S^ k') ≈⟨ (cright cright  lemma-MS^k (m' .proj₁) k' (m' .proj₂)) ⟩
    (S^ s • H^ ₃ • CZ) • ⟦ mc ⟧ₘ₊ ↑ • (S^ (k' * (m' .proj₁ * m' .proj₁)) • ⟦ m' ⟧ₘ) ≈⟨ special-assoc (□ ^ 3 • □ • □ ^ 2) (□ ^ 2 • □ ^ 4) auto ⟩
    (S^ s • H^ ₃) • (CZ • ⟦ mc ⟧ₘ₊ ↑ • (S^ (k' * (m' .proj₁ * m' .proj₁)) • ⟦ m' ⟧ₘ)) ≈⟨ cright cright cright cright sym right-unit ⟩
    (S^ s • H^ ₃) • (CZ • ⟦ mc ⟧ₘ₊ ↑ • (S^ (k' * (m' .proj₁ * m' .proj₁)) • ⟦ m' ⟧ₘ • ε)) ≈⟨ assoc ⟩
    S^ s • H ^ 3 • ⟦ case-| mc nf' ⟧₂ ∎



lemma-postfix-case-|b : ∀ s mc m'' ->
  let
  m' = m'' ⁻¹
  nf' = (₀ , m' , HS^ ₀)
  in
  ⟦ (s , mc , (m'' , ε)) ⟧ₚ ≈ S^ s • H ^ 3 • ⟦ case-| mc nf' ⟧₂
lemma-postfix-case-|b s mc m'' = claim'
  where
  m' = m'' ⁻¹
  mc'' = (m'' , ε)
  nf' = (₀ , m' , HS^ ₀)
  claim' : ⟦ (s , mc , (m'' , ε)) ⟧ₚ ≈ S^ s • H ^ 3 • ⟦ case-| mc nf' ⟧₂
  claim' = begin
    ⟦ (s , mc , mc'') ⟧ₚ ≈⟨ refl ⟩
    (S^ s • (H^ ₃ • CZ • H) • ⟦ mc ⟧ₘ₊ ↑ • ⟦ mc'' ⟧ₘ₊) ≈⟨ special-assoc (□ • □ ^ 3 • □ ^ 2) (□ ^ 3 • □ ^ 2 • □) auto ⟩
    (S^ s • H^ ₃ • CZ) • (H • ⟦ mc ⟧ₘ₊ ↑) • ⟦ mc'' ⟧ₘ₊ ≈⟨ (cright (cleft lemma-comm-H-w↑ ⟦ mc ⟧ₘ₊)) ⟩
    (S^ s • H^ ₃ • CZ) • (⟦ mc ⟧ₘ₊ ↑ • H) • ⟦ mc'' ⟧ₘ₊ ≈⟨ cright assoc ⟩
    (S^ s • H^ ₃ • CZ) • ⟦ mc ⟧ₘ₊ ↑ • (H • ⟦ mc'' ⟧ₘ₊) ≈⟨ (cright cright  sym (sym (cong refl right-unit))) ⟩
    (S^ s • H^ ₃ • CZ) • ⟦ mc ⟧ₘ₊ ↑ • ((H • ⟦ m'' ⟧ₘ)) ≈⟨ (cright cright   semi-HM m'') ⟩
    (S^ s • H^ ₃ • CZ) • ⟦ mc ⟧ₘ₊ ↑ • (⟦ m' ⟧ₘ • H) ≈⟨ cright cright cright sym right-unit ⟩
    (S^ s • H^ ₃ • CZ) • ⟦ mc ⟧ₘ₊ ↑ • (⟦ m' ⟧ₘ • H • ε) ≈⟨ special-assoc (□ ^ 3 • □ ) (□ ^ 4) auto ⟩
    S^ s • H^ ₃ • CZ • ⟦ mc ⟧ₘ₊ ↑ • (⟦ m' ⟧ₘ • H • ε) ≈⟨ cright cright cright cright sym left-unit ⟩
    S^ s • H^ ₃ • CZ • ⟦ mc ⟧ₘ₊ ↑ • (ε • ⟦ m' ⟧ₘ • H • ε) ≈⟨ refl ⟩

    S^ s • H ^ 3 • ⟦ case-| mc nf' ⟧₂ ∎


open Commuting-Symplectic 0
open Sym0-Rewriting 1


lemma-postfix-case-|c : ∀ s m k ->
  
  ⟦ (s , (m , HS^ k) , (m , ε)) ⟧ₚ • CZ ≈ H ↑ ^ 3 • ⟦ case-Ex-| (s , m , HS^ k) ((-' m) ⁻¹ , HS^ ₀)  ⟧₂
  
lemma-postfix-case-|c s m k = begin
  ⟦ s , (m , HS^ k) , (m , ε) ⟧ₚ • CZ ≈⟨ cleft lemma-postfix-case-|b s mc m ⟩
  (S^ s • H ^ 3 • ⟦ case-| mc nf' ⟧₂) • CZ ≈⟨  refl ⟩
  (S^ s • H ^ 3 • CZ • (M m • H • S^ k) ↑ • S^ ₀ • M m' • H • S^ ₀) • CZ ≈⟨  special-assoc ((□ • □ • □ • □ ^ 3 • □ ^ 4) • □) (□ ^ 2 • □ • (□ ^ 3 • □ ^ 2) • □ ^ 3) auto ⟩
  (S^ s • H ^ 3) • CZ • ((M m • H • S^ k) ↑ • S^ ₀ • M m') • H • S^ ₀ • CZ ≈⟨  cright cright cong (cright left-unit) (cright left-unit) ⟩
  (S^ s • H ^ 3) • CZ • ((M m • H • S^ k) ↑ • M m') • H • CZ ≈⟨  cright  special-assoc (□ • (□ ^ 3 • □) • □ ^ 2) (□ ^ 2 • (□ ^ 2 • □) • □ ^ 2) auto ⟩
  (S^ s • H ^ 3) • (CZ • M m ↑) • ((H • S^ k) ↑ • M m') • H • CZ ≈⟨  cright cleft lemma-CZM↑ (m .proj₁) (m .proj₂) ⟩
  (S^ s • H ^ 3) • (M m ↑ • CZ^ m⁻¹) • ((H • S^ k) ↑ • M m') • H • CZ ≈⟨  cright cright cleft sym (aux-comm-MC m' (HS^ k)) ⟩
  (S^ s • H ^ 3) • (M m ↑ • CZ^ m⁻¹) • (M m' • (H • S^ k) ↑) • H • CZ ≈⟨  cright special-assoc (□ ^ 2 • □ ^ 3 • □ ^ 2) (□ • □ ^ 2 • □ ^ 2 • □ ^ 2) auto ⟩
  (S^ s • H ^ 3) • M m ↑ • (CZ^ m⁻¹ • M m') • (H • S^ k) ↑ • H • CZ ≈⟨  cright cright cleft lemma-CZ^kM↓ (m' .proj₁) m⁻¹ (m' .proj₂) ⟩
  (S^ s • H ^ 3) • M m ↑ • (M m' • CZ^ (m⁻¹ * m'⁻¹)) • (H • S^ k) ↑ • H • CZ ≈⟨  cright special-assoc (□ • □ ^ 2 • □ ^ 2 • □ ^ 2) (□ ^ 2 • □ ^ 2 • □ ^ 2 • □) auto ⟩
  (S^ s • H ^ 3) • (M m ↑ • M m') • (CZ^ (m⁻¹ * m'⁻¹) • H ↑) • (S^ k ↑ • H) • CZ ≈⟨  cright cright cright cleft sym (lemma-comm-H-w↑ (S^ k)) ⟩
  (S^ s • H ^ 3) • (M m ↑ • M m') • (CZ^ (m⁻¹ * m'⁻¹) • H ↑) • (H • S^ k ↑) • CZ ≈⟨  cright cright special-assoc (□ ^ 2 • □ ^ 2 • □) (□ ^ 3 • □ ^ 2) auto ⟩
  (S^ s • H ^ 3) • (M m ↑ • M m') • (CZ^ (m⁻¹ * m'⁻¹) • H ↑ • H) • S^ k ↑ • CZ ≈⟨  cright cright cright sym (aux-comm-CZ^a-S^b↑ ₁ k) ⟩
  (S^ s • H ^ 3) • (M m ↑ • M m') • (CZ^ (m⁻¹ * m'⁻¹) • H ↑ • H) • CZ • S^ k ↑ ≈⟨  cright cright special-assoc (□ ^ 3 • □ ^ 2) (□ ^ 4 • □) auto ⟩
  (S^ s • H ^ 3) • (M m ↑ • M m') • (CZ^ (m⁻¹ * m'⁻¹) • H ↑ • H • CZ) • S^ k ↑ ≈⟨  cright cright cleft cleft refl' (Eq.cong CZ^ aux) ⟩
  (S^ s • H ^ 3) • (M m ↑ • M m') • (CZ • H ↑ • H • CZ) • S^ k ↑ ≈⟨  cright cright cleft general-comm auto ⟩
  (S^ s • H ^ 3) • (M m ↑ • M m') • (CZ • H • H ↑ • CZ) • S^ k ↑ ≈⟨  cright cright cleft aux-hEx''' ⟩
  (S^ s • H ^ 3) • (M m ↑ • M m') • (Ex • H • H ↑ • CZ⁻¹ • H • H ↑) • S^ k ↑ ≈⟨  special-assoc (□ ^ 2 • □ ^ 2 • □ ^ 6 • □) ((□ ^ 2 • □) • □ ^ 2 • □ ^ 6) auto ⟩
  ((S^ s • H ^ 3) • M m ↑) • (M m' • Ex) • H • H ↑ • CZ⁻¹ • H • H ↑ • S^ k ↑ ≈⟨  cong (lemma-comm-S^aH^b s ₃ (M m)) (cleft sym (lemma-Ex-M' m')) ⟩
  (M m ↑ • (S^ s • H ^ 3)) • (Ex • M m' ↑) • H • H ↑ • CZ⁻¹ • H • H ↑ • S^ k ↑ ≈⟨  special-assoc (□ ^ 3 • □ ^ 2 • □) (□ ^ 2 • □ ^ 2 • □ ^ 2) auto ⟩
  (M m ↑ • S^ s) • (H ^ 3 • Ex) • M m' ↑ • H • H ↑ • CZ⁻¹ • H • H ↑ • S^ k ↑ ≈⟨  cright cleft sym (lemma-Induction lemma-Ex-H↑ 3) ⟩
  (M m ↑ • S^ s) • (Ex • H ↑ ^ 3) • M m' ↑ • H • H ↑ • CZ⁻¹ • H • H ↑ • S^ k ↑ ≈⟨  special-assoc  (□ ^ 2 • □ ^ 2 • □ ^ 4) (□ • □ ^ 2 • □ ^ 2 • □ ^ 2 • □) auto ⟩
  M m ↑ • (S^ s • Ex) • (H ↑ ^ 3 • M m' ↑) • (H • H ↑) • CZ⁻¹ • H • H ↑ • S^ k ↑ ≈⟨  cright cong (sym ( lemma-Ex-S^ᵏ↑ s)) (cong (lemma-cong↑ _ _ (semi-H³M m')) (cleft sym (axiom comm-H))) ⟩
  M m ↑ • (Ex • S^ s ↑) • (M (m' ⁻¹) ↑ • H ↑ ^ 3) • (H ↑ • H) • CZ⁻¹ • H • H ↑ • S^ k ↑ ≈⟨  cright cright special-assoc (□ ^ 2 • □ ^ 2 • □) (□ • □ ^ 3 • □) auto ⟩
  M m ↑ • (Ex • S^ s ↑) • M (m' ⁻¹) ↑ • (H ↑ ^ 3 • H ↑ • H) • CZ⁻¹ • H • H ↑ • S^ k ↑ ≈⟨  cright cright cright cleft rewrite-sym0 100 auto ⟩
  M m ↑ • (Ex • S^ s ↑) • M (m' ⁻¹) ↑ • H • CZ⁻¹ • H • H ↑ • S^ k ↑ ≈⟨  cright cright sym assoc ⟩
  M m ↑ • (Ex • S^ s ↑) • (M (m' ⁻¹) ↑ • H) • CZ⁻¹ • H • H ↑ • S^ k ↑ ≈⟨  cright cright cong (sym (lemma-comm-H-w↑ (M (m' ⁻¹))))(cleft refl' (Eq.cong (CZ ^_) (Eq.sym lemma-toℕ-ₚ₋₁))) ⟩
  M m ↑ • (Ex • S^ s ↑) • (H • M (m' ⁻¹) ↑) • CZ^ ₋₁ • H • H ↑ • S^ k ↑ ≈⟨  cright special-assoc (□ ^ 2 • □ ^ 2 • □ ^ 2 ) (□ • □ ^ 2 • □ ^ 2 • □) auto ⟩
  M m ↑ • Ex • (S^ s ↑ • H) • (M (m' ⁻¹) ↑ • CZ^ ₋₁) • H • H ↑ • S^ k ↑ ≈⟨  cright cright cong (sym (lemma-comm-H-w↑ (S^ s))) (cleft lemma-M↑CZ^k ((m' ⁻¹) .proj₁) ₋₁ ((m' ⁻¹) .proj₂)) ⟩
  M m ↑ • Ex • (H • S^ s ↑) • (CZ^ (₋₁ * (m' ⁻¹) .proj₁) • M (m' ⁻¹) ↑) • H • H ↑ • S^ k ↑ ≈⟨  cright special-assoc (□ • □ ^ 2 • □ ^ 2 • □ ^ 2) (□ ^ 2 • □ ^ 2 • □ ^ 2 • □) auto ⟩
  M m ↑ • (Ex • H) • (S^ s ↑ • CZ^ (₋₁ * (m' ⁻¹) .proj₁)) • (M (m' ⁻¹) ↑ • H) • H ↑ • S^ k ↑ ≈⟨  cright cong (sym lemma-comm-Ex-H) (cong (sym (aux-comm-CZ^a-S^b↑ ((₋₁ * (m' ⁻¹) .proj₁)) s)) (cleft sym (lemma-comm-H-w↑ (M (m' ⁻¹))))) ⟩
  M m ↑ • (H ↑ • Ex) • (CZ^ (₋₁ * (m' ⁻¹) .proj₁) • S^ s ↑) • (H • M (m' ⁻¹) ↑) • H ↑ • S^ k ↑ ≈⟨  cright cright special-assoc (□ ^ 2 • □ ^ 2 • □) (□ • □ ^ 2 • □ ^ 2) auto ⟩
  M m ↑ • (H ↑ • Ex) • CZ^ (₋₁ * (m' ⁻¹) .proj₁) • (S^ s ↑ • H) • M (m' ⁻¹) ↑ • H ↑ • S^ k ↑ ≈⟨  cright cright cright (cleft sym (lemma-comm-H-w↑ (S^ s))) ⟩
  M m ↑ • (H ↑ • Ex) • CZ^ (₋₁ * (m' ⁻¹) .proj₁) • (H • S^ s ↑) • M (m' ⁻¹) ↑ • H ↑ • S^ k ↑ ≈⟨  cright cright cright assoc ⟩
  M m ↑ • (H ↑ • Ex) • CZ^ (₋₁ * (m' ⁻¹) .proj₁) • H • S^ s ↑ • M (m' ⁻¹) ↑ • H ↑ • S^ k ↑ ≈⟨  cright cright cleft refl' (Eq.cong CZ^ (Eq.trans ( (Eq.cong₂ (_*_) p-1=-1ₚ (inv-involutive m)  )) (-1*x≈-x mf))) ⟩
  M m ↑ • (H ↑ • Ex) • CZ^ (- mf) • H • S^ s ↑ • M (m' ⁻¹) ↑ • H ↑ • S^ k ↑ ≈⟨  cright cright sym left-unit ⟩
  M m ↑ • (H ↑ • Ex) • ε • CZ^ (- mf) • H • S^ s ↑ • M (m' ⁻¹) ↑ • H ↑ • S^ k ↑ ≈⟨  cright cright cleft sym (aux-M-mul (-' m)) ⟩
  M m ↑ • (H ↑ • Ex) • (M (-' m) • M ((-' m) ⁻¹)) • CZ^ (- mf) • H • S^ s ↑ • M (m' ⁻¹) ↑ • H ↑ • S^ k ↑ ≈⟨  cright cright special-assoc (□ ^ 2 • □ ^ 2) (□ • □ ^ 2 • □) auto ⟩
  M m ↑ • (H ↑ • Ex) • M (-' m) • (M ((-' m) ⁻¹) • CZ^ (- mf)) • H • S^ s ↑ • M (m' ⁻¹) ↑ • H ↑ • S^ k ↑ ≈⟨  cright cright cright cleft lemma-M↓CZ^k (((-' m) ⁻¹) .proj₁) (- mf) (((-' m) ⁻¹) .proj₂) ⟩
  M m ↑ • (H ↑ • Ex) • M (-' m) • (CZ^ (- mf * ((-' m) ⁻¹) .proj₁ ) • M ((-' m) ⁻¹)) • H • S^ s ↑ • M (m' ⁻¹) ↑ • H ↑ • S^ k ↑ ≈⟨  cright cright cright (cleft (cleft refl' (Eq.cong CZ^ (Eq.trans (Eq.cong (- mf *_) (inv-neg-comm m)) (Eq.trans (Eq.sym (-‿distribˡ-* mf (- m⁻¹))) (Eq.trans (Eq.cong (-_) (Eq.sym (-‿distribʳ-* mf m⁻¹))) (Eq.trans (-‿involutive (mf * m⁻¹)) (lemma-⁻¹ʳ mf {{nztoℕ {y = mf} {neq0 = m .proj₂}}})))))))) ⟩
  M m ↑ • (H ↑ • Ex) • M (-' m) • (CZ • M ((-' m) ⁻¹)) • H • S^ s ↑ • M (m' ⁻¹) ↑ • H ↑ • S^ k ↑ ≈⟨  special-assoc (□ • □ ^ 2 • □ • □ ^ 2 • □ ^ 2) (□ ^ 2 • □ ^ 2 • □ • □ ^ 2 • □) auto ⟩
  (M m ↑ • H ↑) • (Ex • M (-' m)) • CZ • (M ((-' m) ⁻¹) • H) • S^ s ↑ • M (m' ⁻¹) ↑ • H ↑ • S^ k ↑ ≈⟨  cong (sym (lemma-cong↑ _ _ (semi-HM' m))) (cong (lemma-Ex-M ((-' m))) refl) ⟩
  (H ↑ • M (m ⁻¹) ↑) • (M (-' m) ↑ • Ex) • CZ • (M ((-' m) ⁻¹) • H) • S^ s ↑ • M (m' ⁻¹) ↑ • H ↑ • S^ k ↑ ≈⟨  special-assoc (□ ^ 2 • □ ^ 2 • □) (□ • □ ^ 2 • □ ^ 2) auto ⟩
  H ↑ • (M (m ⁻¹) ↑ • M (-' m) ↑) • Ex • CZ • (M ((-' m) ⁻¹) • H) • S^ s ↑ • M (m' ⁻¹) ↑ • H ↑ • S^ k ↑ ≈⟨  cright cong (lemma-cong↑ _ _ (PB1.trans (PB1.axiom (M-mul (m ⁻¹) (-' m))) (L0.aux-MM ((m ⁻¹ *' -' m) .proj₂) ((-'₁) .proj₂) (Eq.trans (Eq.sym (-‿distribʳ-* m⁻¹ mf)) (Eq.cong -_ (lemma-⁻¹ˡ mf {{nztoℕ {y = mf} {neq0 = m .proj₂}}})))))) refl ⟩
  H ↑ • M (-'₁) ↑ • Ex • CZ • (M ((-' m) ⁻¹) • H) • S^ s ↑ • M (m' ⁻¹) ↑ • H ↑ • S^ k ↑ ≈⟨  sym assoc ⟩
  (H ↑ • M (-'₁) ↑) • Ex • CZ • (M ((-' m) ⁻¹) • H) • S^ s ↑ • M (m' ⁻¹) ↑ • H ↑ • S^ k ↑ ≈⟨  cleft cright lemma-cong↑ _ _ (PB1.sym L0.lemma-HH-M-1) ⟩
  (H ↑ • HH ↑) • Ex • CZ • (M ((-' m) ⁻¹) • H) • S^ s ↑ • M (m' ⁻¹) ↑ • H ↑ • S^ k ↑ ≈⟨  cleft refl ⟩
  H ↑ ^ 3 • Ex • CZ • (M ((-' m) ⁻¹) • H) • S^ s ↑ • M (m' ⁻¹) ↑ • H ↑ • S^ k ↑ ≈⟨  cright cright cright cleft (cright sym right-unit) ⟩
  H ↑ ^ 3 • Ex • CZ • (M ((-' m) ⁻¹) • H • ε) • S^ s ↑ • M (m' ⁻¹) ↑ • H ↑ • S^ k ↑ ≈⟨  cright cright cright cright cright cleft lemma-cong↑ _ _ (L0.aux-MM ((m' ⁻¹) .proj₂) (m .proj₂) (inv-involutive m)) ⟩
  H ↑ ^ 3 • Ex • CZ • (M ((-' m) ⁻¹) • H • ε) • S^ s ↑ • M m ↑ • H ↑ • S^ k ↑ ≈⟨  cright cright cright aux-comm-MCSMC ((-' m) ⁻¹ , HS^ ₀) (s , m , HS^ k) ⟩
  H ↑ ^ 3 • Ex • CZ • (S^ s ↑ • M m ↑ • H ↑ • S^ k ↑) • (M ((-' m) ⁻¹) • H • ε) ≈⟨  refl ⟩
  H ↑ ^ 3 • ⟦ case-Ex-| (s , m , HS^ k) ((-' m) ⁻¹ , HS^ ₀)  ⟧₂ ∎
  where
  m' = m ⁻¹
  mf = m .proj₁
  m⁻¹ = (m ⁻¹) .proj₁
  m'⁻¹ = (m' ⁻¹) .proj₁
  m'f = m' .proj₁
  nf' = (₀ , m' , HS^ ₀)
  mc = (m , HS^ k)
  aux : m⁻¹ * m'⁻¹ ≡ ₁
  aux = Eq.trans (Eq.cong (m⁻¹ *_) (inv-involutive m)) (lemma-⁻¹ˡ mf {{nztoℕ {y = mf} {neq0 = m .proj₂}}})
