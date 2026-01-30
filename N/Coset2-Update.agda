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



module N.Coset2-Update (p-2 : ℕ) (p-prime : Prime (2+ p-2))  where

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
open import N.Symplectic-Derived p-2 p-prime
open import N.Lemmas-2Qupit p-2 p-prime
open import N.NF2 p-2 p-prime
open Lemmas-2Q 2
open Symplectic-Derived-Gen
open import N.NF1 p-2 p-prime
open Normal-Form1
open Action
open LM2
open import N.Completeness1 p-2 p-prime renaming (module Completeness to CP1) using ()


module Completeness where

  open PB (2 QRel,_===_)
  open PP (2 QRel,_===_)
  open SR word-setoid
  open Pattern-Assoc

  PrimitiveGen : Gen 2 -> Set
  PrimitiveGen (H-gen ₁) = ⊤
  PrimitiveGen (S-gen ₁) = ⊤
  PrimitiveGen (H-gen ₁ ↥) = ⊤
  PrimitiveGen (S-gen ₁ ↥) = ⊤
  PrimitiveGen (CZ-gen ₁) = ⊤
  PrimitiveGen _ = ⊥

  PrimitiveWord : Word(Gen 2) -> Set
  PrimitiveWord [ x ]ʷ = PrimitiveGen x
  PrimitiveWord ε = ⊤
  PrimitiveWord (w • w₁) = PrimitiveWord w × PrimitiveWord w₁

  desugar-gen :(Gen 2) -> Word(Gen 2)
  desugar-gen (H-gen x) = H ^ toℕ x
  desugar-gen (S-gen x) = S ^ toℕ x
  desugar-gen (H-gen x ↥) = (H ^ toℕ x) ↑
  desugar-gen (S-gen x ↥) = (S ^ toℕ x) ↑
  desugar-gen (CZ-gen x) = CZ ^ toℕ x

  desugar-word = desugar-gen WB.*

  lemma-H^-Prim : ∀ x -> PrimitiveWord (H ^ x)
  lemma-H^-Prim ₀ = tt
  lemma-H^-Prim ₁ = tt
  lemma-H^-Prim (₂₊ k) = tt , (lemma-H^-Prim (₁₊ k))

  lemma-H↑^-Prim : ∀ x -> PrimitiveWord ((H ^ x) ↑)
  lemma-H↑^-Prim ₀ = tt
  lemma-H↑^-Prim ₁ = tt
  lemma-H↑^-Prim (₂₊ k) = tt , (lemma-H↑^-Prim (₁₊ k))

  lemma-S^-Prim : ∀ x -> PrimitiveWord (S ^ x)
  lemma-S^-Prim ₀ = tt
  lemma-S^-Prim ₁ = tt
  lemma-S^-Prim (₂₊ k) = tt , (lemma-S^-Prim (₁₊ k))

  lemma-S↑^-Prim : ∀ x -> PrimitiveWord ((S ^ x) ↑)
  lemma-S↑^-Prim ₀ = tt
  lemma-S↑^-Prim ₁ = tt
  lemma-S↑^-Prim (₂₊ k) = tt , (lemma-S↑^-Prim (₁₊ k))

  lemma-CZ^-Prim : ∀ x -> PrimitiveWord (CZ ^ x)
  lemma-CZ^-Prim ₀ = tt
  lemma-CZ^-Prim ₁ = tt
  lemma-CZ^-Prim (₂₊ k) = tt , (lemma-CZ^-Prim (₁₊ k))
  
  lemma-desugar-gen : (g :(Gen 2)) -> PrimitiveWord (desugar-gen g)
  lemma-desugar-gen (H-gen x) = lemma-H^-Prim (toℕ x)
  lemma-desugar-gen (S-gen x) = lemma-S^-Prim (toℕ x)
  lemma-desugar-gen (H-gen x ↥) = lemma-H↑^-Prim (toℕ x)
  lemma-desugar-gen (S-gen x ↥) = lemma-S↑^-Prim (toℕ x)
  lemma-desugar-gen (CZ-gen x) = lemma-CZ^-Prim (toℕ x)

  lemma-desugar-word : (w : Word(Gen 2)) -> PrimitiveWord (desugar-word w)
  lemma-desugar-word [ x ]ʷ = lemma-desugar-gen x
  lemma-desugar-word ε = tt
  lemma-desugar-word (w • w₁) = (lemma-desugar-word w) , (lemma-desugar-word w₁)

  lemma-desugar-gen-≈ : (g :(Gen 2)) -> desugar-gen g ≈ [ g ]ʷ
  lemma-desugar-gen-≈ (H-gen x) = sym (axiom (derived-H x))
  lemma-desugar-gen-≈ (S-gen x) = sym (axiom (derived-S x))
  lemma-desugar-gen-≈ (H-gen x ↥) = sym (axiom (cong↑ (derived-H x)))
  lemma-desugar-gen-≈ (S-gen x ↥) = sym (axiom (cong↑ (derived-S x)))
  lemma-desugar-gen-≈ (CZ-gen x) = sym (axiom (derived-CZ x))

  lemma-desugar-word-≈ : (w : Word(Gen 2)) -> desugar-word w ≈ w
  lemma-desugar-word-≈ [ x ]ʷ = lemma-desugar-gen-≈ x
  lemma-desugar-word-≈ ε = refl
  lemma-desugar-word-≈ (w • w₁) = cong (lemma-desugar-word-≈ w) (lemma-desugar-word-≈ w₁)

  aux-comm-S^k-H↑ : ∀ k -> S^ k • H ↑ ≈ H ↑ • S^ k
  aux-comm-S^k-H↑ k = begin
    S^ k • H ↑ ≈⟨ (cleft axiom (derived-S k)) ⟩
    S ^ toℕ k • H ↑ ≈⟨ lemma-comm-Sᵏ-w↑ (toℕ k) [ H-gen ₁ ]ʷ ⟩
    H ↑ • S ^ toℕ k ≈⟨ (cright sym (axiom (derived-S k))) ⟩
    H ↑ • S^ k ∎
  
  aux-comm-c-H↑ : ∀ c -> ⟦ c ⟧ₕₛ • H ↑ ≈ H ↑ • ⟦ c ⟧ₕₛ
  aux-comm-c-H↑ c@ε = begin
    ⟦ c ⟧ₕₛ • H ↑ ≈⟨ trans left-unit (sym right-unit) ⟩
    H ↑ • ⟦ c ⟧ₕₛ ∎
  aux-comm-c-H↑ c@(HS^ k) = begin
    ⟦ c ⟧ₕₛ • H ↑ ≈⟨ assoc ⟩
    H • S^ k • H ↑ ≈⟨ (cright aux-comm-S^k-H↑ k) ⟩
    H • H ↑ • S^ k ≈⟨ sym assoc ⟩
    (H • H ↑) • S^ k ≈⟨ (cleft sym (axiom comm-H)) ⟩
    (H ↑ • H) • S^ k ≈⟨ assoc ⟩
    H ↑ • ⟦ c ⟧ₕₛ ∎

  aux-comm-m-H↑ : ∀ m -> ⟦ m ⟧ₘ • H ↑ ≈ H ↑ • ⟦ m ⟧ₘ
  aux-comm-m-H↑ m = begin
    ⟦ m ⟧ₘ • H ↑ ≈⟨ refl ⟩
    (S^ x • H • S^ x⁻¹ • H • S^ x • H) • H ↑ ≈⟨ by-assoc auto ⟩
    (S^ x • H • S^ x⁻¹ • H • S^ x) • H • H ↑ ≈⟨ (cright sym (axiom comm-H)) ⟩
    (S^ x • H • S^ x⁻¹ • H • S^ x) • H ↑ • H ≈⟨ by-assoc auto ⟩
    (S^ x • H • S^ x⁻¹ • H) • (S^ x • H ↑) • H ≈⟨ (cright cleft aux-comm-S^k-H↑ x) ⟩
    (S^ x • H • S^ x⁻¹ • H) • (H ↑ • S^ x) • H ≈⟨ by-assoc auto ⟩
    (S^ x • H • S^ x⁻¹) • (H • H ↑) • S^ x • H ≈⟨ (cright cleft sym (axiom comm-H)) ⟩
    (S^ x • H • S^ x⁻¹) • (H ↑ • H) • S^ x • H ≈⟨ by-assoc auto ⟩
    (S^ x • H) • (S^ x⁻¹ • H ↑) • H • S^ x • H ≈⟨ (cright cleft aux-comm-S^k-H↑ x⁻¹) ⟩
    (S^ x • H) • (H ↑ • S^ x⁻¹) • H • S^ x • H ≈⟨ by-assoc auto ⟩
    S^ x • (H • H ↑) • S^ x⁻¹ • H • S^ x • H ≈⟨ (cright cleft sym (axiom comm-H)) ⟩
    S^ x • (H ↑ • H) • S^ x⁻¹ • H • S^ x • H ≈⟨ by-assoc auto ⟩
    (S^ x • H ↑) • H • S^ x⁻¹ • H • S^ x • H ≈⟨ (cleft aux-comm-S^k-H↑ x) ⟩
    (H ↑ • S^ x) • H • S^ x⁻¹ • H • S^ x • H ≈⟨ assoc ⟩
    H ↑ • ⟦ m ⟧ₘ ∎
    where
    x = m .proj₁
    x⁻¹ = ((m ⁻¹) .proj₁ )


  aux-comm-mc-H↑ : ∀ mc -> ⟦ mc ⟧ₘ₊ • H ↑ ≈ H ↑ • ⟦ mc ⟧ₘ₊
  aux-comm-mc-H↑ mc@(m , c) = begin
    ⟦ mc ⟧ₘ₊ • H ↑ ≈⟨ assoc ⟩
    ⟦ m ⟧ₘ • ⟦ c ⟧ₕₛ • H ↑ ≈⟨ (cright aux-comm-c-H↑ c) ⟩
    ⟦ m ⟧ₘ • H ↑ • ⟦ c ⟧ₕₛ ≈⟨ sym assoc ⟩
    (⟦ m ⟧ₘ • H ↑) • ⟦ c ⟧ₕₛ ≈⟨ cong (aux-comm-m-H↑ m) refl ⟩
    (H ↑ • ⟦ m ⟧ₘ) • ⟦ c ⟧ₕₛ ≈⟨ assoc ⟩
    H ↑ • ⟦ mc ⟧ₘ₊ ∎


  aux-comm-S^k-S↑ : ∀ k -> S^ k • S ↑ ≈ S ↑ • S^ k
  aux-comm-S^k-S↑ k = begin
    S^ k • S ↑ ≈⟨ (cleft axiom (derived-S k)) ⟩
    S ^ toℕ k • S ↑ ≈⟨ lemma-comm-Sᵏ-w↑ (toℕ k) S ⟩
    S ↑ • S ^ toℕ k ≈⟨ (cright sym (axiom (derived-S k))) ⟩
    S ↑ • S^ k ∎
  
  aux-comm-c-S↑ : ∀ c -> ⟦ c ⟧ₕₛ • S ↑ ≈ S ↑ • ⟦ c ⟧ₕₛ
  aux-comm-c-S↑ c@ε = begin
    ⟦ c ⟧ₕₛ • S ↑ ≈⟨ trans left-unit (sym right-unit) ⟩
    S ↑ • ⟦ c ⟧ₕₛ ∎
  aux-comm-c-S↑ c@(HS^ k) = begin
    ⟦ c ⟧ₕₛ • S ↑ ≈⟨ assoc ⟩
    H • S^ k • S ↑ ≈⟨ (cright aux-comm-S^k-S↑ k) ⟩
    H • S ↑ • S^ k ≈⟨ sym assoc ⟩
    (H • S ↑) • S^ k ≈⟨ (cleft sym (axiom comm-H)) ⟩
    (S ↑ • H) • S^ k ≈⟨ assoc ⟩
    S ↑ • ⟦ c ⟧ₕₛ ∎

  aux-comm-m-S↑ : ∀ m -> ⟦ m ⟧ₘ • S ↑ ≈ S ↑ • ⟦ m ⟧ₘ
  aux-comm-m-S↑ m = begin
    ⟦ m ⟧ₘ • S ↑ ≈⟨ refl ⟩
    (S^ x • H • S^ x⁻¹ • H • S^ x • H) • S ↑ ≈⟨ by-assoc auto ⟩
    (S^ x • H • S^ x⁻¹ • H • S^ x) • H • S ↑ ≈⟨ (cright sym (axiom comm-H)) ⟩
    (S^ x • H • S^ x⁻¹ • H • S^ x) • S ↑ • H ≈⟨ by-assoc auto ⟩
    (S^ x • H • S^ x⁻¹ • H) • (S^ x • S ↑) • H ≈⟨ (cright cleft aux-comm-S^k-S↑ x) ⟩
    (S^ x • H • S^ x⁻¹ • H) • (S ↑ • S^ x) • H ≈⟨ by-assoc auto ⟩
    (S^ x • H • S^ x⁻¹) • (H • S ↑) • S^ x • H ≈⟨ (cright cleft sym (axiom comm-H)) ⟩
    (S^ x • H • S^ x⁻¹) • (S ↑ • H) • S^ x • H ≈⟨ by-assoc auto ⟩
    (S^ x • H) • (S^ x⁻¹ • S ↑) • H • S^ x • H ≈⟨ (cright cleft aux-comm-S^k-S↑ x⁻¹) ⟩
    (S^ x • H) • (S ↑ • S^ x⁻¹) • H • S^ x • H ≈⟨ by-assoc auto ⟩
    S^ x • (H • S ↑) • S^ x⁻¹ • H • S^ x • H ≈⟨ (cright cleft sym (axiom comm-H)) ⟩
    S^ x • (S ↑ • H) • S^ x⁻¹ • H • S^ x • H ≈⟨ by-assoc auto ⟩
    (S^ x • S ↑) • H • S^ x⁻¹ • H • S^ x • H ≈⟨ (cleft aux-comm-S^k-S↑ x) ⟩
    (S ↑ • S^ x) • H • S^ x⁻¹ • H • S^ x • H ≈⟨ assoc ⟩
    S ↑ • ⟦ m ⟧ₘ ∎
    where
    x = m .proj₁
    x⁻¹ = ((m ⁻¹) .proj₁ )

  aux-comm-mc-S↑ : ∀ mc -> ⟦ mc ⟧ₘ₊ • S ↑ ≈ S ↑ • ⟦ mc ⟧ₘ₊
  aux-comm-mc-S↑ mc@(m , c) = begin
    ⟦ mc ⟧ₘ₊ • S ↑ ≈⟨ assoc ⟩
    ⟦ m ⟧ₘ • ⟦ c ⟧ₕₛ • S ↑ ≈⟨ (cright aux-comm-c-S↑ c) ⟩
    ⟦ m ⟧ₘ • S ↑ • ⟦ c ⟧ₕₛ ≈⟨ sym assoc ⟩
    (⟦ m ⟧ₘ • S ↑) • ⟦ c ⟧ₕₛ ≈⟨ cong (aux-comm-m-S↑ m) refl ⟩
    (S ↑ • ⟦ m ⟧ₘ) • ⟦ c ⟧ₕₛ ≈⟨ assoc ⟩
    S ↑ • ⟦ mc ⟧ₘ₊ ∎
  
  aux-comm-nf1-S↑ : ∀ nf1 -> ⟦ nf1 ⟧₁ • S ↑ ≈ S ↑ • ⟦ nf1 ⟧₁
  aux-comm-nf1-S↑ nf1@(s , mc) = begin
    ⟦ nf1 ⟧₁ • S ↑ ≈⟨ assoc ⟩
    S^ s • ⟦ mc ⟧ₘ₊ • S ↑ ≈⟨ (cright aux-comm-mc-S↑ mc) ⟩
    S^ s • S ↑ • ⟦ mc ⟧ₘ₊ ≈⟨ sym assoc ⟩
    (S^ s • S ↑) • ⟦ mc ⟧ₘ₊ ≈⟨ (cleft aux-comm-S^k-S↑ s) ⟩
    (S ↑ • S^ s) • ⟦ mc ⟧ₘ₊ ≈⟨ assoc ⟩
    S ↑ • ⟦ nf1 ⟧₁ ∎

  aux-comm-nf1-H↑ : ∀ nf1 -> ⟦ nf1 ⟧₁ • H ↑ ≈ H ↑ • ⟦ nf1 ⟧₁
  aux-comm-nf1-H↑ nf1@(s , mc) = begin
    ⟦ nf1 ⟧₁ • H ↑ ≈⟨ assoc ⟩
    S^ s • ⟦ mc ⟧ₘ₊ • H ↑ ≈⟨ (cright aux-comm-mc-H↑ mc) ⟩
    S^ s • H ↑ • ⟦ mc ⟧ₘ₊ ≈⟨ sym assoc ⟩
    (S^ s • H ↑) • ⟦ mc ⟧ₘ₊ ≈⟨ (cleft aux-comm-S^k-H↑ s) ⟩
    (H ↑ • S^ s) • ⟦ mc ⟧ₘ₊ ≈⟨ assoc ⟩
    H ↑ • ⟦ nf1 ⟧₁ ∎


  Lemma-two-qupit-completeness :
    
    ∀ (lm : Cosets2) (g :(Gen 2)) (pg : PrimitiveGen g) ->
    -------------------------------------------------------
    ∃ \ lm' -> ∃ \ w -> ⟦ lm ⟧₂ • [ g ]ʷ ≈ w ↑ • ⟦ lm' ⟧₂
    
  Lemma-two-qupit-completeness (case-||ₐ x x₁) (H-gen ₁) pg = {!!}
  Lemma-two-qupit-completeness (case-||ₐ x x₁) (S-gen ₁) pg = {!!}
  Lemma-two-qupit-completeness (case-||ₐ x x₁) (CZ-gen ₁) pg = {!!}
  Lemma-two-qupit-completeness (case-||ₐ x x₁) (H-gen ₁ ↥) pg = {!!}
  Lemma-two-qupit-completeness (case-||ₐ x x₁) (S-gen ₁ ↥) pg = {!!}
  Lemma-two-qupit-completeness (case-|| x x₁ x₂) (H-gen ₁) pg = {!!}
  Lemma-two-qupit-completeness (case-|| x x₁ x₂) (S-gen ₁) pg = {!!}
  Lemma-two-qupit-completeness (case-|| x x₁ x₂) (CZ-gen ₁) pg = {!!}
  Lemma-two-qupit-completeness (case-|| x x₁ x₂) (H-gen ₁ ↥) pg = {!!}
  Lemma-two-qupit-completeness (case-|| x x₁ x₂) (S-gen ₁ ↥) pg = {!!}
  Lemma-two-qupit-completeness (case-|-Ex nf1 mc) (H-gen ₁) pg = {!!}
  Lemma-two-qupit-completeness (case-|-Ex nf1 (m , ε)) (S-gen ₁) pg = {!!}
  Lemma-two-qupit-completeness (case-|-Ex nf1 (m , HS^ k)) (S-gen ₁) pg = {!!}
  Lemma-two-qupit-completeness (case-|-Ex nf1 mc) (CZ-gen ₁) pg = {!!}
  Lemma-two-qupit-completeness (case-|-Ex nf1 mc) (H-gen ₁ ↥) pg = (case-|-Ex nf1' mc) , ε , claim
    where
    nf1't = CP1.Corollary-single-qupit-completeness {0} nf1 H tt
    nf1' = nf1't .proj₁
    claim : ⟦ case-|-Ex nf1 mc ⟧₂ • H ↑ ≈ (ε ↑) • ⟦ case-|-Ex nf1' mc ⟧₂
    claim = begin
      ⟦ case-|-Ex nf1 mc ⟧₂ • H ↑ ≈⟨ {!!} ⟩
      (CZ • ⟦ nf1 ⟧₁ ↑ • ⟦ mc ⟧ₘ₊) • H ↑ ≈⟨ trans (by-assoc auto) assoc ⟩
      (CZ • ⟦ nf1 ⟧₁ ↑) • ⟦ mc ⟧ₘ₊ • H ↑ ≈⟨ (cright aux-comm-mc-H↑ mc) ⟩
      (CZ • ⟦ nf1 ⟧₁ ↑) • H ↑ • ⟦ mc ⟧ₘ₊ ≈⟨ sym (trans (by-assoc auto) assoc) ⟩
      (CZ • ⟦ nf1 ⟧₁ ↑ • H ↑) • ⟦ mc ⟧ₘ₊ ≈⟨ (cleft cright lemma-cong↑ _ _ (nf1't .proj₂)) ⟩
      (CZ • ⟦ nf1' ⟧₁ ↑) • ⟦ mc ⟧ₘ₊ ≈⟨ {!!} ⟩
      ⟦ case-|-Ex nf1' mc ⟧₂ ≈⟨ sym left-unit ⟩
      (ε ↑) • ⟦ case-|-Ex nf1' mc ⟧₂ ∎
  Lemma-two-qupit-completeness (case-|-Ex nf1 mc) (S-gen ₁ ↥) pg = (case-|-Ex nf1' mc) , ε , claim
    where
    nf1't = CP1.Corollary-single-qupit-completeness {0} nf1 S tt
    nf1' = nf1't .proj₁
    claim : ⟦ case-|-Ex nf1 mc ⟧₂ • S ↑ ≈ (ε ↑) • ⟦ case-|-Ex nf1' mc ⟧₂
    claim = begin
      ⟦ case-|-Ex nf1 mc ⟧₂ • S ↑ ≈⟨ {!!} ⟩
      (CZ • ⟦ nf1 ⟧₁ ↑ • ⟦ mc ⟧ₘ₊) • S ↑ ≈⟨ trans (by-assoc auto) assoc ⟩
      (CZ • ⟦ nf1 ⟧₁ ↑) • ⟦ mc ⟧ₘ₊ • S ↑ ≈⟨ (cright aux-comm-mc-S↑ mc) ⟩
      (CZ • ⟦ nf1 ⟧₁ ↑) • S ↑ • ⟦ mc ⟧ₘ₊ ≈⟨ sym (trans (by-assoc auto) assoc) ⟩
      (CZ • ⟦ nf1 ⟧₁ ↑ • S ↑) • ⟦ mc ⟧ₘ₊ ≈⟨ (cleft cright lemma-cong↑ _ _ (nf1't .proj₂)) ⟩
      (CZ • ⟦ nf1' ⟧₁ ↑) • ⟦ mc ⟧ₘ₊ ≈⟨ {!!} ⟩
      ⟦ case-|-Ex nf1' mc ⟧₂ ≈⟨ sym left-unit ⟩
      (ε ↑) • ⟦ case-|-Ex nf1' mc ⟧₂ ∎
  Lemma-two-qupit-completeness (case-| mc nf1) (H-gen ₁) pg = (case-| mc nf1') , ε , claim
    where
    nf1't = CP1.Corollary-single-qupit-completeness {1} nf1 H tt
    nf1' = nf1't .proj₁
    claim : ⟦ case-| mc nf1 ⟧₂ • [ H-gen ₁ ]ʷ ≈ (ε ↑) • ⟦ case-| mc nf1' ⟧₂
    claim = begin
      ⟦ case-| mc nf1 ⟧₂ • H ≈⟨ {!!} ⟩
      (Ex • CZ • ⟦ mc ⟧ₘ₊ ↑ • ⟦ nf1 ⟧₁) • H ≈⟨ trans (by-assoc auto) assoc ⟩
      (Ex • CZ • ⟦ mc ⟧ₘ₊ ↑) • ⟦ nf1 ⟧₁ • H ≈⟨ (cright ((nf1't .proj₂))) ⟩
      (Ex • CZ • ⟦ mc ⟧ₘ₊ ↑) • ⟦ nf1't .proj₁ ⟧₁ ≈⟨ trans assoc (cong {!!} {!!}) ⟩
      ⟦ case-| mc nf1' ⟧₂ ≈⟨ sym left-unit ⟩
      (ε ↑) • ⟦ case-| mc nf1' ⟧₂ ∎
  
  Lemma-two-qupit-completeness (case-| mc nf1) (S-gen ₁) pg = (case-| mc nf1') , ε , claim
    where
    nf1't = CP1.Corollary-single-qupit-completeness {1} nf1 S tt
    nf1' = nf1't .proj₁
    claim : ⟦ case-| mc nf1 ⟧₂ • [ S-gen ₁ ]ʷ ≈ (ε ↑) • ⟦ case-| mc nf1' ⟧₂
    claim = begin
      ⟦ case-| mc nf1 ⟧₂ • S ≈⟨ {!!} ⟩
      (Ex • CZ • ⟦ mc ⟧ₘ₊ ↑ • ⟦ nf1 ⟧₁) • S ≈⟨ trans (by-assoc auto) assoc ⟩
      (Ex • CZ • ⟦ mc ⟧ₘ₊ ↑) • ⟦ nf1 ⟧₁ • S ≈⟨ (cright ((nf1't .proj₂))) ⟩
      (Ex • CZ • ⟦ mc ⟧ₘ₊ ↑) • ⟦ nf1't .proj₁ ⟧₁ ≈⟨ trans assoc (cong {!!} {!!}) ⟩
      ⟦ case-| mc nf1' ⟧₂ ≈⟨ sym left-unit ⟩
      (ε ↑) • ⟦ case-| mc nf1' ⟧₂ ∎
  Lemma-two-qupit-completeness (case-| mc nf1) (CZ-gen ₁) pg = {!!}
  Lemma-two-qupit-completeness (case-| mc nf1) (H-gen ₁ ↥) pg = {!!}
  Lemma-two-qupit-completeness (case-| mc nf1) (S-gen ₁ ↥) pg = {!!}
  Lemma-two-qupit-completeness (case-nf1-Ex nf1) (H-gen ₁) pg = (case-nf1-Ex (nf1't .proj₁)) , ε , claim
    where
    nf1't = CP1.Corollary-single-qupit-completeness {1} nf1 H tt
    claim : ⟦ case-nf1-Ex nf1 ⟧₂ • [ H-gen ₁ ]ʷ ≈ (ε ↑) • ⟦ case-nf1-Ex (nf1't .proj₁) ⟧₂
    claim = begin
      ⟦ case-nf1-Ex nf1 ⟧₂ • [ H-gen ₁ ]ʷ ≈⟨ {!!} ⟩
      ⟦ nf1 ⟧₁ ↑ • H ≈⟨ {!!} ⟩
      (ε ↑) • ⟦ case-nf1-Ex (nf1't .proj₁) ⟧₂ ∎
    
  Lemma-two-qupit-completeness (case-nf1-Ex nf1) (S-gen ₁) pg = (case-nf1-Ex nf1) , (S , claim)
    where
    claim : ⟦ case-nf1-Ex nf1 ⟧₂ • [ S-gen ₁ ]ʷ ≈ (S ↑) • ⟦ case-nf1-Ex nf1 ⟧₂
    claim = begin
      ⟦ case-nf1-Ex nf1 ⟧₂ • [ S-gen ₁ ]ʷ ≈⟨ assoc ⟩
      Ex • ⟦ nf1 ⟧₁ ↑ • [ S-gen ₁ ]ʷ ≈⟨ (cright sym (lemma-comm-S-w↑ ⟦ nf1 ⟧₁)) ⟩
      Ex • [ S-gen ₁ ]ʷ • ⟦ nf1 ⟧₁ ↑ ≈⟨ sym assoc ⟩
      (Ex • [ S-gen ₁ ]ʷ) • ⟦ nf1 ⟧₁ ↑ ≈⟨ {!!} ⟩
      (S ↑) • ⟦ case-nf1-Ex nf1 ⟧₂ ∎
      
  Lemma-two-qupit-completeness (case-nf1-Ex nf1) (CZ-gen ₁) pg = {!!}
  Lemma-two-qupit-completeness (case-nf1-Ex nf1) (H-gen ₁ ↥) pg =  case-nf1-Ex nf1' , ε , claim
    where
    nf1't = CP1.Corollary-single-qupit-completeness nf1 H tt
    nf1' = nf1't .proj₁
    claim : ⟦ case-nf1-Ex nf1 ⟧₂ • H ↑ ≈ (ε ↑) • ⟦ case-nf1-Ex (nf1't .proj₁) ⟧₂
    claim = begin
      ⟦ case-nf1-Ex nf1 ⟧₂ • H ↑ ≈⟨ assoc ⟩
      Ex • ⟦ nf1 ⟧₁ ↑ • H ↑ ≈⟨ (cright lemma-cong↑ _ _ (nf1't .proj₂)) ⟩
      Ex • ⟦ nf1' ⟧₁ ↑ ≈⟨ sym left-unit ⟩
      (ε ↑) • ⟦ case-nf1-Ex (nf1't .proj₁) ⟧₂ ∎
      
  Lemma-two-qupit-completeness (case-nf1-Ex nf1) (S-gen ₁ ↥) pg = case-nf1-Ex nf1' , ε , claim
    where
    nf1't = CP1.Corollary-single-qupit-completeness nf1 S tt
    nf1' = nf1't .proj₁
    claim : ⟦ case-nf1-Ex nf1 ⟧₂ • S ↑ ≈ (ε ↑) • ⟦ case-nf1-Ex (nf1't .proj₁) ⟧₂
    claim = begin
      ⟦ case-nf1-Ex nf1 ⟧₂ • S ↑ ≈⟨ assoc ⟩
      Ex • ⟦ nf1 ⟧₁ ↑ • S ↑ ≈⟨ (cright lemma-cong↑ _ _ (nf1't .proj₂)) ⟩
      Ex • ⟦ nf1' ⟧₁ ↑ ≈⟨ sym left-unit ⟩
      (ε ↑) • ⟦ case-nf1-Ex (nf1't .proj₁) ⟧₂ ∎
      
  Lemma-two-qupit-completeness (case-nf1 nf1) (H-gen ₁) pg = case-nf1 nf1' , ε , claim
    where
    nf1't = CP1.Corollary-single-qupit-completeness nf1 H tt
    nf1' = nf1't .proj₁
    claim : ⟦ case-nf1 nf1 ⟧₂ • H ≈ (ε ↑) • ⟦ case-nf1 (nf1't .proj₁) ⟧₂
    claim = begin
      ⟦ case-nf1 nf1 ⟧₂ • H ≈⟨ refl ⟩
      ⟦ nf1 ⟧₁ • H ≈⟨ ( (nf1't .proj₂)) ⟩
      ⟦ nf1' ⟧₁ ≈⟨ sym left-unit ⟩
      (ε ↑) • ⟦ case-nf1 (nf1't .proj₁) ⟧₂ ∎
      
  Lemma-two-qupit-completeness (case-nf1 nf1) (S-gen ₁) pg = case-nf1 nf1' , ε , claim
    where
    nf1't = CP1.Corollary-single-qupit-completeness nf1 S tt
    nf1' = nf1't .proj₁
    claim : ⟦ case-nf1 nf1 ⟧₂ • S ≈ (ε ↑) • ⟦ case-nf1 (nf1't .proj₁) ⟧₂
    claim = begin
      ⟦ case-nf1 nf1 ⟧₂ • S ≈⟨ refl ⟩
      ⟦ nf1 ⟧₁ • S ≈⟨ ( (nf1't .proj₂)) ⟩
      ⟦ nf1' ⟧₁ ≈⟨ sym left-unit ⟩
      (ε ↑) • ⟦ case-nf1 (nf1't .proj₁) ⟧₂ ∎
      
  Lemma-two-qupit-completeness (case-nf1 x) (CZ-gen ₁) pg = {!!}
  Lemma-two-qupit-completeness (case-nf1 x) (H-gen ₁ ↥) pg = (case-nf1 x) , (H , aux-comm-nf1-H↑ x)
  Lemma-two-qupit-completeness (case-nf1 x) (S-gen ₁ ↥) pg = (case-nf1 x) , (S , aux-comm-nf1-S↑ x)

