{-# OPTIONS  --safe #-}
{-# OPTIONS  --call-by-name #-}
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
open import Data.Nat hiding (_^_ ; _+_ ; _*_ ;  _≟_)
open import Agda.Builtin.Nat using (_-_)
import Data.Nat as Nat
open import Data.Bool hiding (_<_ ; _≤_ ; _≟_)
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
import Data.Fin.Properties as FP



module N.Proofs.P9 (p-2 : ℕ) (p-prime : Prime (2+ p-2))  where

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
open import N.Lemmas-2Qupit p-2 p-prime
open import N.NF2-Sym p-2 p-prime
--open Lemmas-2Q 2
open Symplectic
open Lemmas-Sym
open import N.NF1-Sym p-2 p-prime
open import N.Ex-Sym p-2 p-prime
open import N.Ex-Sym1 p-2 p-prime
open import N.Ex-Sym2 p-2 p-prime
open import N.Ex-Sym3 p-2 p-prime
open import N.Ex-Sym4 p-2 p-prime
open import N.Ex-Sym5 p-2 p-prime hiding (module L0)
open import N.Cosets p-2 p-prime

open import N.Lemma-Comm p-2 p-prime 0
open import N.Completeness1-Sym p-2 p-prime renaming (module Completeness to Cp1)
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
open Sym0-Rewriting 1

open import N.Proofs.P1 p-2 p-prime
open import N.Proofs.P2 p-2 p-prime
open import N.Proofs.P3 p-2 p-prime
open import N.Proofs.P4 p-2 p-prime
open import N.Proofs.P5 p-2 p-prime
open import N.Proofs.P6 p-2 p-prime
open import N.Proofs.P7 p-2 p-prime
open import N.Lemmas-2Qupit-Sym p-2 p-prime as TQ
open import N.Lemma-Postfix p-2 p-prime
open import N.Derived p-2 p-prime
open import N.Derived2 p-2 p-prime
--  open import N.NF1-Sym p-2 p-prime as NF1
--  open NF1.Normal-Form1 using ()

open TQ.Lemmas-2Q 0
open Duality
import N.Duality p-2 p-prime as ND
open Lemmas0 1
--module L0 = Lemmas0 0
open import Algebra.Properties.Ring (+-*-ring p-2)
open import Zp.Mod-Lemmas p-2 p-prime



Lemma-two-qupit-completeness-||ₐ-mε-mε :

  ∀ cz s m m' ->
  let
  mc : MC
  mc = (m , ε)
  mc'' : MC
  mc'' = (m' , ε)
  lm = case-||ₐ cz (s , mc , mc'')
  in
  -------------------------------------------------
  ∃ \ lm' -> ∃ \ w -> ⟦ lm ⟧₂ • CZ ≈ w ↑ • ⟦ lm' ⟧₂

--Lemma-two-qupit-completeness-||ₐ-mε-mε lm@(case-||ₐ cz (s , mc@(m , c@ε) , mc''@(m' , c''@ε))) (CZ-gen) = lm' , w' , claim'
Lemma-two-qupit-completeness-||ₐ-mε-mε cz s m m' = lm' , w' , claim'

  where
  mc : MC
  mc = (m , ε)
  mc'' : MC
  mc'' = (m' , ε)
  s' : ℤ ₚ
  s' = ₀

  m'⁻¹ = (m' ⁻¹) .proj₁
  m⁻¹ = (m ⁻¹) .proj₁

  mf = m .proj₁
  m'f = m' .proj₁
  m*m' = mf * m'f


  w' = S^ (- (m'f * mf) + - (m'f * mf))
  lm' = case-||ₐ (cz  + (m'f * mf)) (s , (m , ε) , (m' , ε))


  claim' : ⟦ case-||ₐ cz (s , mc , mc'') ⟧₂ • CZ ≈ S^ (- (m'f * mf) + - (m'f * mf)) ↑  • ⟦ case-||ₐ (cz  + (m'f * mf)) (s , (m , ε) , (m' , ε)) ⟧₂
  claim' = begin
    ⟦ case-||ₐ cz (s , mc , mc'') ⟧₂ • CZ ≈⟨ refl ⟩
    (CZ^ cz • S^ s • CX • ⟦ mc ⟧ₘ₊ ↑ • ⟦ mc'' ⟧ₘ₊) • CZ ≈⟨ (cleft cright cright cright cong (lemma-cong↑ _ _ PB1.right-unit) right-unit) ⟩
    (CZ^ cz • S^ s • CX • ⟦ m ⟧ₘ ↑ • ⟦ m' ⟧ₘ) • CZ ≈⟨ special-assoc (□ ^ 5 • □) (□ ^ 4 • □ ^ 2) auto ⟩
    (CZ^ cz • S^ s • CX • ⟦ m ⟧ₘ ↑) • ⟦ m' ⟧ₘ • CZ ≈⟨ (cright  lemma-M↓CZ m') ⟩
    (CZ^ cz • S^ s • CX • ⟦ m ⟧ₘ ↑) • CZ^ m'f • ⟦ m' ⟧ₘ ≈⟨ special-assoc (□ ^ 4 • □ ^ 2) (□ ^ 3 • □ ^ 2 • □) auto ⟩
    (CZ^ cz • S^ s • CX) • (⟦ m ⟧ₘ ↑ • CZ^ m'f) • ⟦ m' ⟧ₘ ≈⟨ (cright cleft lemma-M↑CZ^k (m .proj₁) m'f (m .proj₂)) ⟩
    (CZ^ cz • S^ s • CX) • (CZ^ (m'f * mf) • ⟦ m ⟧ₘ ↑) • ⟦ m' ⟧ₘ ≈⟨ special-assoc  (□ ^ 3 • □ ^ 2 • □) (□ ^ 2 • □ ^ 2 • □ ^ 2) auto ⟩
    (CZ^ cz • S^ s) • (CX • CZ^ (m'f * mf)) • ⟦ m ⟧ₘ ↑ • ⟦ m' ⟧ₘ ≈⟨ (cright cleft lemma-semi-CXCZ^k (m' *' m)) ⟩
    (CZ^ cz • S^ s) • (S^ (- (m'f * mf) + - (m'f * mf)) ↑ • CZ^ (m'f * mf) • CX) • ⟦ m ⟧ₘ ↑ • ⟦ m' ⟧ₘ ≈⟨ special-assoc (□ ^ 2 • □ ^ 3 • □ ^ 2) (□ • □ ^ 2 • □ ^ 4) auto ⟩
    CZ^ cz • (S^ s • S^ (- (m'f * mf) + - (m'f * mf)) ↑) • CZ^ (m'f * mf) • CX • ⟦ m ⟧ₘ ↑ • ⟦ m' ⟧ₘ ≈⟨ (cright cleft lemma-comm-Sᵏ-w↑ (toℕ s) (S^ (- (m'f * mf) + - (m'f * mf)))) ⟩
    CZ^ cz • (S^ (- (m'f * mf) + - (m'f * mf)) ↑ • S^ s) • CZ^ (m'f * mf) • CX • ⟦ m ⟧ₘ ↑ • ⟦ m' ⟧ₘ ≈⟨ special-assoc (□ • □ ^ 2 • □ ^ 4) (□ ^ 2 • □ ^ 2 • □ ^ 3) auto ⟩
    (CZ^ cz • S^ (- (m'f * mf) + - (m'f * mf)) ↑) • (S^ s • CZ^ (m'f * mf)) • CX • ⟦ m ⟧ₘ ↑ • ⟦ m' ⟧ₘ ≈⟨ cong (aux-comm-CZ^a-S^b↑ cz ((- (m'f * mf) + - (m'f * mf)))) (cleft word-comm (toℕ s) (toℕ (m'f * mf)) (sym (axiom comm-CZ-S↓))) ⟩
    (S^ (- (m'f * mf) + - (m'f * mf)) ↑ • CZ^ cz) • (CZ^ (m'f * mf) • S^ s) • CX • ⟦ m ⟧ₘ ↑ • ⟦ m' ⟧ₘ ≈⟨ special-assoc (□ ^ 2 • □ ^ 2 • □ ^ 3)  (□ • □ ^ 2 • □ ^ 4) auto  ⟩
    S^ (- (m'f * mf) + - (m'f * mf)) ↑  • (CZ^ cz • CZ^ (m'f * mf)) • S^ s • CX • ⟦ m ⟧ₘ ↑ • ⟦ m' ⟧ₘ ≈⟨ (cright cleft lemma-CZ^k+l cz (m'f * mf)) ⟩
    S^ (- (m'f * mf) + - (m'f * mf)) ↑  • CZ^ (cz + (m'f * mf)) • S^ s • CX • ⟦ m ⟧ₘ ↑ • ⟦ m' ⟧ₘ ≈⟨ (cright cright cright cright cong (sym (lemma-cong↑ _ _ PB1.right-unit)) (sym right-unit)) ⟩
    S^ (- (m'f * mf) + - (m'f * mf)) ↑  • CZ^ (cz + (m'f * mf)) • S^ s • CX • (⟦ m ⟧ₘ • ε) ↑ • (⟦ m' ⟧ₘ • ε) ≈⟨ refl ⟩
    S^ (- (m'f * mf) + - (m'f * mf)) ↑  • ⟦ case-||ₐ (cz  + (m'f * mf)) (s , (m , ε) , (m' , ε)) ⟧₂ ∎




Lemma-two-qupit-completeness-||ₐ-mHS^k-mHS^k' :

  ∀ cz s m k m'' k' ->
  let
  mc : MC
  mc = (m , HS^ k)
  mc'' : MC
  mc'' = (m'' , HS^ k')
  lm = case-||ₐ cz (s , mc , mc'')
  in
  -------------------------------------------------
  ∃ \ lm' -> ∃ \ w -> ⟦ lm ⟧₂ • CZ ≈ w ↑ • ⟦ lm' ⟧₂


--Lemma-two-qupit-completeness-||ₐ-mHS^k-mHS^k' lm@(case-||ₐ cz@₀ (s , mc@(m , c@(HS^ k)) , mc''@(m'' , c''@(HS^ k')))) (CZ-gen) = lm'' , w'' , claim'
Lemma-two-qupit-completeness-||ₐ-mHS^k-mHS^k' cz@₀ s m k m'' k' = lm'' , w'' , claim'

  where
  mc : MC
  mc = (m , HS^ k)
  mc'' : MC
  mc'' = (m'' , HS^ k')
  
  m'′ = (m'' ⁻¹)
  m' = -' m'′

  m⁻¹ = (m ⁻¹) .proj₁
  m'⁻¹ = (m' ⁻¹) .proj₁
  mf = m .proj₁
  a* = m ⁻¹
  a = a* .proj₁
  l = m' .proj₁
  -l : ℤ ₚ
  -l = - l
  l⁻¹ : ℤ ₚ
  l⁻¹ = ((m' ⁻¹) .proj₁)
  -l⁻¹ : ℤ ₚ
  -l⁻¹ = - l⁻¹

  s' = k' * (m' .proj₁ * m' .proj₁)
  s'' = -l * a + s'
  s1' = - mf * m'⁻¹
  mc1' : MC
  mc1' =  m , HS^ (- (m' *' m) .proj₁ + k)
  nf1' : NF1
  nf1' = (s1' , mc1')

  w' = ⟦ - mf * m'⁻¹ ,  m *' m' ⁻¹ , HS^ (- mf * m'⁻¹) ⟧₁
  lm' = case-| mc1' (-l * a + s' , m' , ε)
  nf' : NF1
  nf' = (k' * (m' .proj₁ * m' .proj₁) , m' , ε)

  lm'' = case-||ₐ ₀  ( s , mc1' , (m'' , HS^ (s'' * (m'⁻¹ * m'⁻¹))))
  w'' = w'

  claim' : ⟦ case-||ₐ cz (s , mc , mc'') ⟧₂ • CZ ≈ w'' ↑ • ⟦ lm'' ⟧₂
  claim' = begin
    ⟦ case-||ₐ cz (s , mc , mc'') ⟧₂ • CZ ≈⟨ (cleft cright lemma-postfix-case-| s mc m'' k') ⟩
    (CZ^ cz • S^ s • H ^ 3 • ⟦ case-| mc nf' ⟧₂) • CZ ≈⟨ ( special-assoc (□ ^ 4 • □) (□ ^ 3 • □ ^ 2) auto) ⟩
    (CZ^ cz • S^ s • H ^ 3) • ⟦ case-| mc nf' ⟧₂ • CZ ≈⟨ ( cright step-|-CZ m k s' m') ⟩
    (CZ^ cz • S^ s • H^ ₃) • w' ↑ • ⟦ lm' ⟧₂ ≈⟨ special-assoc (□ ^ 3 • □ ^ 2) (□ • (□ ^ 2 • □) • □) auto ⟩
    CZ^ cz • ((S^ s • H^ ₃) • w' ↑) • ⟦ lm' ⟧₂ ≈⟨ (cright (cleft lemma-comm-S^aH^b s ₃ w')) ⟩
    CZ^ cz • (w' ↑ • S^ s • H^ ₃) • ⟦ lm' ⟧₂ ≈⟨ special-assoc (□ • □ ^ 3 • □ ) (□ ^ 2 • □ ^ 3) auto ⟩
    (CZ^ cz • w' ↑) • S^ s • H^ ₃ • ⟦ lm' ⟧₂ ≈⟨ refl ⟩
    (CZ^ cz • w' ↑) • S^ s • H^ ₃ • CZ • ⟦ mc1' ⟧ₘ₊ ↑ • ⟦ (s'' , m' , ε) ⟧₁  ≈⟨ ( cright cright cright cright cright cright right-unit ) ⟩
    (CZ^ cz • w' ↑) • S^ s • H^ ₃ • CZ • ⟦ mc1' ⟧ₘ₊ ↑ • S^ s'' • ⟦ m' ⟧ₘ  ≈⟨ (cright cright cright cright cong (lemma-cong↑ _ _ PB1.refl) (lemma-S^kM (m' .proj₁) s'' (m' .proj₂))) ⟩
    (CZ^ cz • w' ↑) • S^ s • H^ ₃ • CZ • ⟦ mc1' ⟧ₘ₊ ↑ • ⟦ m' ⟧ₘ • S^ (s'' * ((m' ⁻¹) .proj₁ * (m' ⁻¹) .proj₁))  ≈⟨ ( cright cright cright cright cright cright sym left-unit) ⟩
    (CZ^ cz • w' ↑) • S^ s • H^ ₃ • CZ • ⟦ mc1' ⟧ₘ₊ ↑ • ⟦ m' ⟧ₘ • ε • S^ (s'' * ((m' ⁻¹) .proj₁ * (m' ⁻¹) .proj₁))  ≈⟨ ( cright cright cright cright cright cright (cleft sym (axiom order-H))) ⟩
    (CZ^ cz • w' ↑) • S^ s • H^ ₃ • CZ • ⟦ mc1' ⟧ₘ₊ ↑ • ⟦ m' ⟧ₘ • H ^ 4 • S^ (s'' * ((m' ⁻¹) .proj₁ * (m' ⁻¹) .proj₁))  ≈⟨ ( cright cright cright cright cright special-assoc (□ • □ ^ 4 • □) (□ ^ 4 • □ ^ 2) auto) ⟩
    (CZ^ cz • w' ↑) • S^ s • H^ ₃ • CZ • ⟦ mc1' ⟧ₘ₊ ↑ • (⟦ m' ⟧ₘ • H ^ 3) • H • S^ (s'' * ((m' ⁻¹) .proj₁ * (m' ⁻¹) .proj₁))  ≈⟨ ( cright cright cright cright cright cleft aux) ⟩
    (CZ^ cz • w' ↑) • S^ s • H^ ₃ • CZ • ⟦ mc1' ⟧ₘ₊ ↑ • (H • ⟦ m'' ⟧ₘ) • H • S^ (s'' * ((m' ⁻¹) .proj₁ * (m' ⁻¹) .proj₁))  ≈⟨ ( cright  cright  cright  cright special-assoc (□  • □ ^ 2 • □) (□ ^ 2 • □ ^ 2) auto) ⟩
    (CZ^ cz • w' ↑) • S^ s • H^ ₃ • CZ • (⟦ mc1' ⟧ₘ₊ ↑ • H) • ⟦ m'' ⟧ₘ • H • S^ (s'' * ((m' ⁻¹) .proj₁ * (m' ⁻¹) .proj₁))  ≈⟨ (cright cright cright cright cleft sym (lemma-comm-H-w↑ ⟦ mc1' ⟧ₘ₊)) ⟩
    (CZ^ cz • w' ↑) • S^ s • H^ ₃ • CZ • (H • ⟦ mc1' ⟧ₘ₊ ↑) • ⟦ m'' ⟧ₘ • H • S^ (s'' * ((m' ⁻¹) .proj₁ * (m' ⁻¹) .proj₁))  ≈⟨ (cright cright special-assoc (□ • □ • □ ^ 2 • □) (□ ^ 3 • □ ^ 2) auto) ⟩
    (CZ^ cz • w' ↑) • S^ s • (H^ ₃ • CZ • H) • ⟦ mc1' ⟧ₘ₊ ↑ • ⟦ m'' ⟧ₘ • H • S^ (s'' * ((m' ⁻¹) .proj₁ * (m' ⁻¹) .proj₁))  ≈⟨ (cright cright cright cleft sym (lemma-cong↑ _ _ PB1.refl)) ⟩
    (CZ^ cz • w' ↑) • S^ s • (H^ ₃ • CZ • H) • ⟦ mc1' ⟧ₘ₊ ↑ • ⟦ m'' ⟧ₘ • H • S^ (s'' * ((m' ⁻¹) .proj₁ * (m' ⁻¹) .proj₁))  ≈⟨ (cleft left-unit) ⟩
    (w' ↑) • S^ s • (H^ ₃ • CZ • H) • ⟦ mc1' ⟧ₘ₊ ↑ • ⟦ m'' ⟧ₘ • H • S^ (s'' * ((m' ⁻¹) .proj₁ * (m' ⁻¹) .proj₁))  ≈⟨ (cright sym left-unit) ⟩
    (w' ↑) •  CZ^ ₀ • S^ s • (H^ ₃ • CZ • H) • ⟦ mc1' ⟧ₘ₊ ↑ • ⟦ m'' ⟧ₘ • H • S^ (s'' * ((m' ⁻¹) .proj₁ * (m' ⁻¹) .proj₁))  ≈⟨ refl ⟩
    w' ↑ • ⟦ case-||ₐ ₀  ( s , mc1' , (m'' , HS^ (s'' * (m'⁻¹ * m'⁻¹)))) ⟧₂  ∎
    where
    aux : ⟦ m' ⟧ₘ • H ^ 3 ≈ H • ⟦ m'' ⟧ₘ
    aux = begin
      ⟦ m' ⟧ₘ • H ^ 3 ≈⟨ special-assoc (□ ^ 4) (□ ^ 3 • □) auto ⟩
      (⟦ m' ⟧ₘ • HH) • H ≈⟨ (cleft cright lemma-HH-M-1) ⟩
      (⟦ m' ⟧ₘ • M -'₁) • H ≈⟨ (cleft axiom (M-mul m' -'₁)) ⟩
      (⟦ m' *' -'₁ ⟧ₘ) • H ≈⟨ refl ⟩
      ⟦ m' *' -'₁ ⟧ₘ • H ≈⟨ (cleft aux-MM ((m' *' -'₁) .proj₂) (m'′ .proj₂) (Eq.trans (Eq.sym (-‿distribʳ-* (m' .proj₁) ₁)) (Eq.trans (Eq.cong -_ (*-identityʳ (m' .proj₁))) (-‿involutive (m'′ .proj₁))))) ⟩
      ⟦ m'′ ⟧ₘ • H ≈⟨ sym (semi-HM m'') ⟩
      H • ⟦ m'' ⟧ₘ ∎



Lemma-two-qupit-completeness-||ₐ-mHS^k-mHS^k' cz@(₁₊ cz-1) s m k m'' k' = lm'' , w'' , claim'

  where
  mc : MC
  mc = (m , HS^ k)
  mc'' : MC
  mc'' = (m'' , HS^ k')
  
  m'′ = (m'' ⁻¹)
  m' = -' m'′

  m⁻¹ = (m ⁻¹) .proj₁
  m'⁻¹ = (m' ⁻¹) .proj₁
  mf = m .proj₁
  a* = m ⁻¹
  a = a* .proj₁
  l = m' .proj₁
  -l : ℤ ₚ
  -l = - l
  l⁻¹ : ℤ ₚ
  l⁻¹ = ((m' ⁻¹) .proj₁)
  -l⁻¹ : ℤ ₚ
  -l⁻¹ = - l⁻¹

  s' = k' * (m' .proj₁ * m' .proj₁)
  s'' = -l * a + s'
  s1' = - mf * m'⁻¹
  mc1' : MC
  mc1' =  m , HS^ (- (m' *' m) .proj₁ + k)
  nf1' : NF1
  nf1' = (s1' , mc1')

  w' = ⟦ - mf * m'⁻¹ ,  m *' m' ⁻¹ , HS^ (- mf * m'⁻¹) ⟧₁
  lm' = case-| mc1' (-l * a + s' , m' , ε)
  nf' : NF1
  nf' = (k' * (m' .proj₁ * m' .proj₁) , m' , ε)

  aux1 : - (cz * ((m *' m' ⁻¹) ⁻¹) .proj₁) ≢ ₀
  aux1 = (-' ((cz , λ ()) *' ((m *' m' ⁻¹) ⁻¹))) .proj₂


  lm'' = case-|| (- (cz * ((m *' m' ⁻¹) ⁻¹) .proj₁) , aux1)   (- mf * m'⁻¹)   ( s , mc1' , (m'' , HS^ (s'' * (m'⁻¹ * m'⁻¹))))
  w'' = (S^ (- mf * m'⁻¹) • M (m *' m' ⁻¹) • HH)

  claim' : ⟦ case-||ₐ cz (s , mc , mc'') ⟧₂ • CZ ≈ w'' ↑ • ⟦ lm'' ⟧₂
  claim' = begin
    ⟦ case-||ₐ cz (s , mc , mc'') ⟧₂ • CZ ≈⟨ (cleft cright lemma-postfix-case-| s mc m'' k') ⟩
    (CZ^ cz • S^ s • H ^ 3 • ⟦ case-| mc nf' ⟧₂) • CZ ≈⟨ ( special-assoc (□ ^ 4 • □) (□ ^ 3 • □ ^ 2) auto) ⟩
    (CZ^ cz • S^ s • H ^ 3) • ⟦ case-| mc nf' ⟧₂ • CZ ≈⟨ ( cright step-|-CZ m k s' m') ⟩
    (CZ^ cz • S^ s • H^ ₃) • w' ↑ • ⟦ lm' ⟧₂ ≈⟨ special-assoc (□ ^ 3 • □ ^ 2) (□ • (□ ^ 2 • □) • □) auto ⟩
    CZ^ cz • ((S^ s • H^ ₃) • w' ↑) • ⟦ lm' ⟧₂ ≈⟨ (cright (cleft lemma-comm-S^aH^b s ₃ w')) ⟩
    CZ^ cz • (w' ↑ • S^ s • H^ ₃) • ⟦ lm' ⟧₂ ≈⟨ special-assoc (□ • □ ^ 3 • □ ) (□ ^ 2 • □ ^ 3) auto ⟩
    (CZ^ cz • w' ↑) • S^ s • H^ ₃ • ⟦ lm' ⟧₂ ≈⟨ refl ⟩
    (CZ^ cz • w' ↑) • S^ s • H^ ₃ • CZ • ⟦ mc1' ⟧ₘ₊ ↑ • ⟦ (s'' , m' , ε) ⟧₁  ≈⟨ ( cright cright cright cright cright cright right-unit ) ⟩
    (CZ^ cz • w' ↑) • S^ s • H^ ₃ • CZ • ⟦ mc1' ⟧ₘ₊ ↑ • S^ s'' • ⟦ m' ⟧ₘ  ≈⟨ (cright cright cright cright cong (lemma-cong↑ _ _ PB1.refl) (lemma-S^kM (m' .proj₁) s'' (m' .proj₂))) ⟩
    (CZ^ cz • w' ↑) • S^ s • H^ ₃ • CZ • ⟦ mc1' ⟧ₘ₊ ↑ • ⟦ m' ⟧ₘ • S^ (s'' * ((m' ⁻¹) .proj₁ * (m' ⁻¹) .proj₁))  ≈⟨ ( cright cright cright cright cright cright sym left-unit) ⟩
    (CZ^ cz • w' ↑) • S^ s • H^ ₃ • CZ • ⟦ mc1' ⟧ₘ₊ ↑ • ⟦ m' ⟧ₘ • ε • S^ (s'' * ((m' ⁻¹) .proj₁ * (m' ⁻¹) .proj₁))  ≈⟨ ( cright cright cright cright cright cright (cleft sym (axiom order-H))) ⟩
    (CZ^ cz • w' ↑) • S^ s • H^ ₃ • CZ • ⟦ mc1' ⟧ₘ₊ ↑ • ⟦ m' ⟧ₘ • H ^ 4 • S^ (s'' * ((m' ⁻¹) .proj₁ * (m' ⁻¹) .proj₁))  ≈⟨ ( cright cright cright cright cright special-assoc (□ • □ ^ 4 • □) (□ ^ 4 • □ ^ 2) auto) ⟩
    (CZ^ cz • w' ↑) • S^ s • H^ ₃ • CZ • ⟦ mc1' ⟧ₘ₊ ↑ • (⟦ m' ⟧ₘ • H ^ 3) • H • S^ (s'' * ((m' ⁻¹) .proj₁ * (m' ⁻¹) .proj₁))  ≈⟨ ( cright cright cright cright cright cleft aux) ⟩
    (CZ^ cz • w' ↑) • S^ s • H^ ₃ • CZ • ⟦ mc1' ⟧ₘ₊ ↑ • (H • ⟦ m'' ⟧ₘ) • H • S^ (s'' * ((m' ⁻¹) .proj₁ * (m' ⁻¹) .proj₁))  ≈⟨ ( cright  cright  cright  cright special-assoc (□  • □ ^ 2 • □) (□ ^ 2 • □ ^ 2) auto) ⟩
    (CZ^ cz • w' ↑) • S^ s • H^ ₃ • CZ • (⟦ mc1' ⟧ₘ₊ ↑ • H) • ⟦ m'' ⟧ₘ • H • S^ (s'' * ((m' ⁻¹) .proj₁ * (m' ⁻¹) .proj₁))  ≈⟨ (cright cright cright cright cleft sym (lemma-comm-H-w↑ ⟦ mc1' ⟧ₘ₊)) ⟩
    (CZ^ cz • w' ↑) • S^ s • H^ ₃ • CZ • (H • ⟦ mc1' ⟧ₘ₊ ↑) • ⟦ m'' ⟧ₘ • H • S^ (s'' * ((m' ⁻¹) .proj₁ * (m' ⁻¹) .proj₁))  ≈⟨ (cright cright special-assoc (□ • □ • □ ^ 2 • □) (□ ^ 3 • □ ^ 2) auto) ⟩
    (CZ^ cz • w' ↑) • S^ s • (H^ ₃ • CZ • H) • ⟦ mc1' ⟧ₘ₊ ↑ • ⟦ m'' ⟧ₘ • H • S^ (s'' * ((m' ⁻¹) .proj₁ * (m' ⁻¹) .proj₁))  ≈⟨ (cright cright cright cleft sym (lemma-cong↑ _ _ PB1.refl)) ⟩
    (CZ^ cz • w' ↑) • S^ s • (H^ ₃ • CZ • H) • ⟦ mc1' ⟧ₘ₊ ↑ • ⟦ m'' ⟧ₘ • H • S^ (s'' * ((m' ⁻¹) .proj₁ * (m' ⁻¹) .proj₁))  ≈⟨ (cleft cright lemma-cong↑ _ _ (PB1._≈_.refl)) ⟩
    (CZ^ cz • (⟦ - mf * m'⁻¹ ,  m *' m' ⁻¹ , HS^ (- mf * m'⁻¹) ⟧₁) ↑) • S^ s • (H^ ₃ • CZ • H) • ⟦ mc1' ⟧ₘ₊ ↑ • ⟦ m'' ⟧ₘ • H • S^ (s'' * ((m' ⁻¹) .proj₁ * (m' ⁻¹) .proj₁))  ≈⟨ cleft special-assoc (□ • □ ^ 3) (□ ^ 2 • □ ^ 2) auto ⟩
    ((CZ^ cz • S^ (- mf * m'⁻¹) ↑) • (M (m *' m' ⁻¹) •  H • S^ (- mf * m'⁻¹) ) ↑) • S^ s • (H^ ₃ • CZ • H) • ⟦ mc1' ⟧ₘ₊ ↑ • ⟦ m'' ⟧ₘ • H • S^ (s'' * ((m' ⁻¹) .proj₁ * (m' ⁻¹) .proj₁))  ≈⟨  (cleft (cleft aux-comm-CZ^a-S^b↑ cz (- mf * m'⁻¹))) ⟩
    ((S^ (- mf * m'⁻¹) ↑ • CZ^ cz) • (M (m *' m' ⁻¹) •  H • S^ (- mf * m'⁻¹) ) ↑) • S^ s • (H^ ₃ • CZ • H) • ⟦ mc1' ⟧ₘ₊ ↑ • ⟦ m'' ⟧ₘ • H • S^ (s'' * ((m' ⁻¹) .proj₁ * (m' ⁻¹) .proj₁))  ≈⟨  (cleft special-assoc (□ ^ 2 • □ ^ 2) (□ • □ ^ 2 • □) auto) ⟩
    (S^ (- mf * m'⁻¹) ↑ • (CZ^ cz • M (m *' m' ⁻¹) ↑)  • ( H • S^ (- mf * m'⁻¹) ) ↑) • S^ s • (H^ ₃ • CZ • H) • ⟦ mc1' ⟧ₘ₊ ↑ • ⟦ m'' ⟧ₘ • H • S^ (s'' * ((m' ⁻¹) .proj₁ * (m' ⁻¹) .proj₁))  ≈⟨  (cleft cright cleft lemma-CZ^kM↑ ((m *' m' ⁻¹) .proj₁) cz ((m *' m' ⁻¹) .proj₂)) ⟩
    (S^ (- mf * m'⁻¹) ↑ • (M (m *' m' ⁻¹) ↑ • CZ^ (cz * ((m *' m' ⁻¹) ⁻¹) .proj₁)) • (H • S^ (- mf * m'⁻¹) ) ↑) • S^ s • (H^ ₃ • CZ • H) • ⟦ mc1' ⟧ₘ₊ ↑ • ⟦ m'' ⟧ₘ • H • S^ (s'' * ((m' ⁻¹) .proj₁ * (m' ⁻¹) .proj₁))  ≈⟨  (cleft cright cright sym (trans (cleft lemma-cong↑ _ _ (PB1._≈_.axiom order-H)) left-unit) ) ⟩
    (S^ (- mf * m'⁻¹) ↑ • (M (m *' m' ⁻¹) ↑ • CZ^ (cz * ((m *' m' ⁻¹) ⁻¹) .proj₁)) • H ↑ ^ 4 •  (H • S^ (- mf * m'⁻¹) ) ↑) • S^ s • (H^ ₃ • CZ • H) • ⟦ mc1' ⟧ₘ₊ ↑ • ⟦ m'' ⟧ₘ • H • S^ (s'' * ((m' ⁻¹) .proj₁ * (m' ⁻¹) .proj₁))  ≈⟨  (cleft cright  special-assoc (□ ^ 2 • □ ^ 4 • □ ^ 2) (□ • □ ^ 3 • (□ ^ 3 • □)) auto ) ⟩
    (S^ (- mf * m'⁻¹) ↑ • M (m *' m' ⁻¹) ↑ • (CZ^ (cz * ((m *' m' ⁻¹) ⁻¹) .proj₁) • HH ↑) • (H ^ 3 • S^ (- mf * m'⁻¹) ) ↑) • S^ s • (H^ ₃ • CZ • H) • ⟦ mc1' ⟧ₘ₊ ↑ • ⟦ m'' ⟧ₘ • H • S^ (s'' * ((m' ⁻¹) .proj₁ * (m' ⁻¹) .proj₁))  ≈⟨  (cleft cright cright cleft lemma-semi-CZ^k-HH↑ (cz * ((m *' m' ⁻¹) ⁻¹) .proj₁)) ⟩
    (S^ (- mf * m'⁻¹) ↑ • M (m *' m' ⁻¹) ↑ • (HH ↑ • CZ^ (- (cz * ((m *' m' ⁻¹) ⁻¹) .proj₁))) • (H ^ 3 • S^ (- mf * m'⁻¹) ) ↑) • S^ s • (H^ ₃ • CZ • H) • ⟦ mc1' ⟧ₘ₊ ↑ • ⟦ m'' ⟧ₘ • H • S^ (s'' * ((m' ⁻¹) .proj₁ * (m' ⁻¹) .proj₁))  ≈⟨  (cleft (cright cright assoc)) ⟩
    (S^ (- mf * m'⁻¹) ↑ • M (m *' m' ⁻¹) ↑ • HH ↑ • CZ^ (- (cz * ((m *' m' ⁻¹) ⁻¹) .proj₁)) • (H ^ 3 • S^ (- mf * m'⁻¹) ) ↑) • S^ s • (H^ ₃ • CZ • H) • ⟦ mc1' ⟧ₘ₊ ↑ • ⟦ m'' ⟧ₘ • H • S^ (s'' * ((m' ⁻¹) .proj₁ * (m' ⁻¹) .proj₁))  ≈⟨  special-assoc (□ ^ 6 • □) (□ ^ 3 • □ ^ 4) auto ⟩
    (S^ (- mf * m'⁻¹) • M (m *' m' ⁻¹) • HH) ↑ • CZ^ (- (cz * ((m *' m' ⁻¹) ⁻¹) .proj₁)) • H ↑ ^ 3 • S^ (- mf * m'⁻¹) ↑ • S^ s • (H^ ₃ • CZ • H) • ⟦ mc1' ⟧ₘ₊ ↑ • ⟦ m'' ⟧ₘ • H • S^ (s'' * ((m' ⁻¹) .proj₁ * (m' ⁻¹) .proj₁))  ≈⟨  refl ⟩
    (S^ (- mf * m'⁻¹) • M (m *' m' ⁻¹) • HH) ↑ • ⟦ case-|| (- (cz * ((m *' m' ⁻¹) ⁻¹) .proj₁) , aux1)   (- mf * m'⁻¹)   ( s , mc1' , (m'' , HS^ (s'' * (m'⁻¹ * m'⁻¹)))) ⟧₂  ∎
    where
    aux : ⟦ m' ⟧ₘ • H ^ 3 ≈ H • ⟦ m'' ⟧ₘ
    aux = begin
      ⟦ m' ⟧ₘ • H ^ 3 ≈⟨ special-assoc (□ ^ 4) (□ ^ 3 • □) auto ⟩
      (⟦ m' ⟧ₘ • HH) • H ≈⟨ (cleft cright lemma-HH-M-1) ⟩
      (⟦ m' ⟧ₘ • M -'₁) • H ≈⟨ (cleft axiom (M-mul m' -'₁)) ⟩
      (⟦ m' *' -'₁ ⟧ₘ) • H ≈⟨ refl ⟩
      ⟦ m' *' -'₁ ⟧ₘ • H ≈⟨ (cleft aux-MM ((m' *' -'₁) .proj₂) (m'′ .proj₂) (Eq.trans (Eq.sym (-‿distribʳ-* (m' .proj₁) ₁)) (Eq.trans (Eq.cong -_ (*-identityʳ (m' .proj₁))) (-‿involutive (m'′ .proj₁))))) ⟩
      ⟦ m'′ ⟧ₘ • H ≈⟨ sym (semi-HM m'') ⟩
      H • ⟦ m'' ⟧ₘ ∎




Lemma-two-qupit-completeness-||ₐ-mε-mHS^k' :

  ∀ cz s m m'' k' ->
  let
  mc : MC
  mc = (m , ε)
  mc'' : MC
  mc'' = (m'' , HS^ k')
  lm = case-||ₐ cz (s , mc , mc'')
  in
  -------------------------------------------------
  ∃ \ lm' -> ∃ \ w -> ⟦ lm ⟧₂ • CZ ≈ w ↑ • ⟦ lm' ⟧₂

--Lemma-two-qupit-completeness-||ₐ-mε-mHS^k' lm@(case-||ₐ cz@(₁₊ cz-1) (s , mc@(m , c@ε) , mc''@(m'' , c'@(HS^ k')))) (CZ-gen) with ((m ⁻¹) .proj₁ + - (m'' ⁻¹) .proj₁) | inspect (\ m -> ((m ⁻¹) .proj₁ + - (m'' ⁻¹) .proj₁)) m
Lemma-two-qupit-completeness-||ₐ-mε-mHS^k' cz@(₁₊ cz-1) s m m'' k' with ((m ⁻¹) .proj₁ + - (m'' ⁻¹) .proj₁) | inspect (\ m -> ((m ⁻¹) .proj₁ + - (m'' ⁻¹) .proj₁)) m
... | ₀ | [ eq ]' = lm'' , w'' , claim' -- lm'' , w'' , claim'

  where
  mc : MC
  mc = (m , ε)
  mc'' : MC
  mc'' = (m'' , HS^ k')
  
  m'′ = (m'' ⁻¹)
  m' = -' m'′
  m'⁻¹ = (m' ⁻¹) .proj₁
  m⁻¹ = (m ⁻¹) .proj₁
  a* = m' ⁻¹
  a = a* .proj₁
  l = m .proj₁
  -l : ℤ ₚ
  -l = - l
  l⁻¹ : ℤ ₚ
  l⁻¹ = ((m ⁻¹) .proj₁)
  -l⁻¹ : ℤ ₚ
  -l⁻¹ = - l⁻¹

  k′ : ℤ ₚ
  k′ = m'⁻¹
  a′ = m⁻¹
  m'0 = m' .proj₁
  k′⁻¹ = (((m') ⁻¹ ⁻¹) .proj₁)
  -k′⁻¹ = - k′⁻¹
  -k′ = - k′
  -m' = - m'0

  s' : ℤ ₚ
  s' =  (k' * (m' .proj₁ * m' .proj₁))

  lm' = case-nf1 (s' , m' , ε)
  w' = ⟦ m ⟧ₘ

  open CP1
  tw : TopwWord {1} (S^ s • H^ ₃ • ⟦ (s' , m' , ε) ⟧₁)
  tw = top-S^k (toℕ s) , (tt , tt , tt) , top-S^k {n = 1} (toℕ s') , top-M m' , tt

  nf1' = CP1.Theorem-single-qupit-completeness (S^ s • H^ ₃ • ⟦ (s' , m' , ε) ⟧₁) tw

  claim : ⟦ case-| (m , ε) (s' , m' , ε) ⟧₂ • CZ ≈ w' ↑ • ⟦ lm' ⟧₂
  claim = step-|-CZa m s' m' eq

  lm'' = case-|  (((cz , λ ()) *' m ⁻¹) ⁻¹ ,  ε)  (nf1' .proj₁)
  w'' = w' • M ((cz , λ () ) *' m ⁻¹) 

  claim' : ⟦ case-||ₐ cz (s , mc , mc'') ⟧₂ • CZ ≈ (w' • M ((cz , λ () ) *' m ⁻¹) ) ↑  • ⟦ case-|  (((cz , λ ()) *' m ⁻¹) ⁻¹ ,  ε)  (nf1' .proj₁) ⟧₂
  claim' = begin
    ⟦ case-||ₐ cz (s , mc , mc'') ⟧₂ • CZ ≈⟨ refl ⟩
    (CZ^ cz • S^ s • (H^ ₃ • CZ • H) • ⟦ mc ⟧ₘ₊ ↑ • ⟦ mc'' ⟧ₘ₊) • CZ ≈⟨ special-assoc ((□ • □ • □ ^ 3 • □ • □) • □) (□ ^ 4 • □ ^ 2 • □ ^ 2) auto ⟩
    (CZ^ cz • S^ s • H^ ₃ • CZ) • (H • ⟦ mc ⟧ₘ₊ ↑) • ⟦ mc'' ⟧ₘ₊ • CZ ≈⟨ (cright (cleft lemma-comm-H-w↑ ⟦ mc ⟧ₘ₊)) ⟩
    (CZ^ cz • S^ s • H^ ₃ • CZ) • (⟦ mc ⟧ₘ₊ ↑ • H) • ⟦ mc'' ⟧ₘ₊ • CZ ≈⟨ (cright special-assoc (□ ^ 2 • □ ^ 2) (□ • □ ^ 2 • □) auto) ⟩
    (CZ^ cz • S^ s • H^ ₃ • CZ) • ⟦ mc ⟧ₘ₊ ↑ • (H • ⟦ mc'' ⟧ₘ₊) • CZ ≈⟨ (cright cright cleft sym assoc) ⟩
    (CZ^ cz • S^ s • H^ ₃ • CZ) • ⟦ mc ⟧ₘ₊ ↑ • ((H • ⟦ m'' ⟧ₘ) • H • S^ k') • CZ ≈⟨ (cright cright cleft cleft semi-HM m'') ⟩
    (CZ^ cz • S^ s • H^ ₃ • CZ) • ⟦ mc ⟧ₘ₊ ↑ • ((⟦ m'′ ⟧ₘ • H) • H • S^ k') • CZ ≈⟨ (cright cright cleft special-assoc (□ ^ 2 • □ ^ 2) (□ ^ 3 • □) auto) ⟩
    (CZ^ cz • S^ s • H^ ₃ • CZ) • ⟦ mc ⟧ₘ₊ ↑ • ((⟦ m'′ ⟧ₘ • HH) • S^ k') • CZ ≈⟨ (cright cright cleft cleft cright lemma-HH-M-1) ⟩
    (CZ^ cz • S^ s • H^ ₃ • CZ) • ⟦ mc ⟧ₘ₊ ↑ • ((⟦ m'′ ⟧ₘ • M -'₁) • S^ k') • CZ ≈⟨ (cright cright cleft cleft axiom (M-mul m'′ -'₁)) ⟩
    (CZ^ cz • S^ s • H^ ₃ • CZ) • ⟦ mc ⟧ₘ₊ ↑ • (⟦ m'′ *' -'₁ ⟧ₘ • S^ k') • CZ ≈⟨ (cright cright cleft cleft aux-MM ((m'′ *' -'₁) .proj₂) (m' .proj₂) (Eq.trans (Eq.sym (-‿distribʳ-* (m'′ .proj₁) ₁)) (Eq.cong -_ (*-identityʳ (m'′ .proj₁))))) ⟩
    (CZ^ cz • S^ s • H^ ₃ • CZ) • ⟦ mc ⟧ₘ₊ ↑ • (⟦ m' ⟧ₘ • S^ k') • CZ ≈⟨ (cright cright cleft lemma-MS^k (m' .proj₁) k' (m' .proj₂)) ⟩
    (CZ^ cz • S^ s • H^ ₃ • CZ) • ⟦ mc ⟧ₘ₊ ↑ • (S^ (k' * (m' .proj₁ * m' .proj₁)) • ⟦ m' ⟧ₘ) • CZ ≈⟨ special-assoc (□ ^ 4 • □ • □ ^ 2 • □) (□ ^ 3 • □ ^ 4 • □) auto ⟩
    (CZ^ cz • S^ s • H^ ₃) • (CZ • ⟦ mc ⟧ₘ₊ ↑ • (S^ (k' * (m' .proj₁ * m' .proj₁)) • ⟦ m' ⟧ₘ)) • CZ ≈⟨ (cright cleft (cright cright cright  sym right-unit)) ⟩
    (CZ^ cz • S^ s • H^ ₃) • (CZ • ⟦ mc ⟧ₘ₊ ↑ • (S^ (k' * (m' .proj₁ * m' .proj₁)) • ⟦ m' ⟧ₘ • ε)) • CZ ≈⟨ (cright claim) ⟩
    (CZ^ cz • S^ s • H^ ₃) • w' ↑ • ⟦ lm' ⟧₂ ≈⟨ special-assoc (□ ^ 3 • □ ^ 2) (□ • (□ ^ 2 • □) • □) auto ⟩
    CZ^ cz • ((S^ s • H^ ₃) • w' ↑) • ⟦ lm' ⟧₂ ≈⟨ (cright (cleft lemma-comm-S^aH^b s ₃ w')) ⟩
    CZ^ cz • (w' ↑ • S^ s • H^ ₃) • ⟦ lm' ⟧₂ ≈⟨ special-assoc (□ • □ ^ 3 • □ ) (□ ^ 2 • □ ^ 3) auto ⟩
    (CZ^ cz • w' ↑) • S^ s • H^ ₃ • ⟦ lm' ⟧₂ ≈⟨ (cleft lemma-CZ^kM↑ (m .proj₁) cz (m .proj₂)) ⟩
    (w' ↑ • CZ^ (cz * m⁻¹)) • S^ s • H^ ₃ • ⟦ lm' ⟧₂ ≈⟨ refl ⟩
    (w' ↑ • CZ^ (cz * m⁻¹)) • S^ s • H^ ₃ • ⟦ (s' , m' , ε) ⟧₁ ≈⟨ (cright nf1' .proj₂) ⟩
    (w' ↑ • CZ^ (cz * m⁻¹)) • ⟦ nf1' .proj₁ ⟧₁ ≈⟨ (cleft cright sym left-unit) ⟩
    (w' ↑ • ε • CZ^ (cz * m⁻¹)) • ⟦ nf1' .proj₁ ⟧₁ ≈⟨ (cleft cright cleft sym (lemma-cong↑ _ _ (L0.aux-M-mul ((cz , λ () ) *' m ⁻¹)))) ⟩
    (w' ↑ • (M ((cz , λ () ) *' m ⁻¹) • M (((cz , λ () ) *' m ⁻¹) ⁻¹) ) ↑ • CZ^ (cz * m⁻¹)) • ⟦ nf1' .proj₁ ⟧₁ ≈⟨ special-assoc ((□ • □ ^ 2 • □) • □) (□ ^ 2 • □ ^ 2 • □ ) auto ⟩
    (w' ↑ • M ((cz , λ () ) *' m ⁻¹) ↑) • (M (((cz , λ () ) *' m ⁻¹) ⁻¹) ↑ • CZ^ (cz * m⁻¹)) • ⟦ nf1' .proj₁ ⟧₁ ≈⟨ (cright cleft lemma-M↑CZ^k ((((cz , λ () ) *' m ⁻¹) ⁻¹)  .proj₁) (cz * m⁻¹) ((((cz , λ () ) *' m ⁻¹) ⁻¹) .proj₂)) ⟩
    (w' ↑ • M ((cz , λ () ) *' m ⁻¹) ↑) • (CZ^ (cz * m⁻¹ * (((cz , λ () ) *' m ⁻¹) ⁻¹) .proj₁) • M (((cz , λ () ) *' m ⁻¹) ⁻¹) ↑) • ⟦ nf1' .proj₁ ⟧₁ ≈⟨ (cright cleft cleft refl' (Eq.cong CZ^ aux)) ⟩
    (w' ↑ • M ((cz , λ () ) *' m ⁻¹) ↑) • (CZ • M (((cz , λ () ) *' m ⁻¹) ⁻¹) ↑) • ⟦ nf1' .proj₁ ⟧₁ ≈⟨ (cright cleft cright sym right-unit) ⟩
    (w' ↑ • M ((cz , λ () ) *' m ⁻¹) ↑) • (CZ • (M (((cz , λ () ) *' m ⁻¹) ⁻¹) ↑ • ε)) • ⟦ nf1' .proj₁ ⟧₁ ≈⟨ (cright assoc) ⟩
    (w' ↑ • M ((cz , λ () ) *' m ⁻¹) ↑) • CZ • (M (((cz , λ () ) *' m ⁻¹) ⁻¹) ↑ • ε) • ⟦ nf1' .proj₁ ⟧₁ ≈⟨ refl ⟩
    (w' • M ((cz , λ () ) *' m ⁻¹) ) ↑  • ⟦ case-|  (((cz , λ ()) *' m ⁻¹) ⁻¹ ,  ε)  (nf1' .proj₁) ⟧₂ ∎
    where
    aux : (cz * m⁻¹ * (((cz , λ () ) *' m ⁻¹) ⁻¹) .proj₁) ≡ ₁
    aux = lemma-⁻¹ʳ (cz * m⁻¹) {{nztoℕ {y = cz * m⁻¹} {neq0 = ((cz , λ () ) *' m ⁻¹) .proj₂}}}

... | (₁₊ sm) | [ eq ]' = lm'' , ⟦ m *' aa* ⟧ₘ , claim'

  where
  mc : MC
  mc = (m , ε)
  mc'' : MC
  mc'' = (m'' , HS^ k')
  
  open import Data.Fin.Properties
  m'′ = (m'' ⁻¹)
  m' = -' m'′
  m'⁻¹ = (m' ⁻¹) .proj₁
  m⁻¹ = (m ⁻¹) .proj₁
  a* = m' ⁻¹
  a = a* .proj₁
  l = m .proj₁
  -l : ℤ ₚ
  -l = - l
  l⁻¹ : ℤ ₚ
  l⁻¹ = ((m ⁻¹) .proj₁)
  -l⁻¹ : ℤ ₚ
  -l⁻¹ = - l⁻¹

  k′ : ℤ ₚ
  k′ = m'⁻¹
  a′ = m⁻¹
  m'0 = m' .proj₁
  k′⁻¹ = (((m') ⁻¹ ⁻¹) .proj₁)
  -k′⁻¹ = - k′⁻¹
  -k′ = - k′
  -m' = - m'0

  s' : ℤ ₚ
  s' =  (k' * (m' .proj₁ * m' .proj₁))

  aa = ((m ⁻¹) .proj₁ + - (m'' ⁻¹) .proj₁)
  neqaa : aa ≢ ₀
  neqaa eq0 = 0≢1+n (Eq.trans (Eq.sym eq0) eq)
  aa* = (aa , neqaa)
  lm' = case-| (aa* ⁻¹ , ε) (s' , m' , ε)
  w' = ⟦ m ⟧ₘ • M (aa , neqaa)

  open CP1
  tw : TopwWord {1} (S^ s • H^ ₃ • ⟦ (s' , m' , ε) ⟧₁)
  tw = top-S^k (toℕ s) , (tt , tt , tt) , top-S^k {n = 1} (toℕ s') , top-M m' , tt

  nf1' = CP1.Theorem-single-qupit-completeness (S^ s • H^ ₃ • ⟦ (s' , m' , ε) ⟧₁) tw


  claim : ⟦ case-| (m , ε) (s' , m' , ε) ⟧₂ • CZ ≈ w' ↑ • ⟦ lm' ⟧₂
  claim = step-|-CZb m s' m' neqaa

  lm'' = case-||ₐ (cz * ((m *' aa*)⁻¹).proj₁) (s , (aa* ⁻¹ , ε) , (m'' , HS^ (s' * ((m' ⁻¹) .proj₁ * (m' ⁻¹) .proj₁))))
  -- w'' = ⟦ m *' aa* ⟧ₘ

  claim' : ⟦ case-||ₐ cz (s , mc , mc'') ⟧₂ • CZ ≈ ⟦ m *' aa* ⟧ₘ ↑ • ⟦ case-||ₐ (cz * ((m *' aa*)⁻¹).proj₁) (s , (aa* ⁻¹ , ε) , (m'' , HS^ (s' * ((m' ⁻¹) .proj₁ * (m' ⁻¹) .proj₁)))) ⟧₂
  claim' = begin
    ⟦ case-||ₐ cz (s , mc , mc'') ⟧₂ • CZ ≈⟨ refl ⟩
    (CZ^ cz • S^ s • (H^ ₃ • CZ • H) • ⟦ mc ⟧ₘ₊ ↑ • ⟦ mc'' ⟧ₘ₊) • CZ ≈⟨ special-assoc ((□ • □ • □ ^ 3 • □ • □) • □) (□ ^ 4 • □ ^ 2 • □ ^ 2) auto ⟩
    (CZ^ cz • S^ s • H^ ₃ • CZ) • (H • ⟦ mc ⟧ₘ₊ ↑) • ⟦ mc'' ⟧ₘ₊ • CZ ≈⟨ (cright (cleft lemma-comm-H-w↑ ⟦ mc ⟧ₘ₊)) ⟩
    (CZ^ cz • S^ s • H^ ₃ • CZ) • (⟦ mc ⟧ₘ₊ ↑ • H) • ⟦ mc'' ⟧ₘ₊ • CZ ≈⟨ (cright special-assoc (□ ^ 2 • □ ^ 2) (□ • □ ^ 2 • □) auto) ⟩
    (CZ^ cz • S^ s • H^ ₃ • CZ) • ⟦ mc ⟧ₘ₊ ↑ • (H • ⟦ mc'' ⟧ₘ₊) • CZ ≈⟨ (cright cright cleft sym assoc) ⟩
    (CZ^ cz • S^ s • H^ ₃ • CZ) • ⟦ mc ⟧ₘ₊ ↑ • ((H • ⟦ m'' ⟧ₘ) • H • S^ k') • CZ ≈⟨ (cright cright cleft cleft semi-HM m'') ⟩
    (CZ^ cz • S^ s • H^ ₃ • CZ) • ⟦ mc ⟧ₘ₊ ↑ • ((⟦ m'′ ⟧ₘ • H) • H • S^ k') • CZ ≈⟨ (cright cright cleft special-assoc (□ ^ 2 • □ ^ 2) (□ ^ 3 • □) auto) ⟩
    (CZ^ cz • S^ s • H^ ₃ • CZ) • ⟦ mc ⟧ₘ₊ ↑ • ((⟦ m'′ ⟧ₘ • HH) • S^ k') • CZ ≈⟨ (cright cright cleft cleft cright lemma-HH-M-1) ⟩
    (CZ^ cz • S^ s • H^ ₃ • CZ) • ⟦ mc ⟧ₘ₊ ↑ • ((⟦ m'′ ⟧ₘ • M -'₁) • S^ k') • CZ ≈⟨ (cright cright cleft cleft axiom (M-mul m'′ -'₁)) ⟩
    (CZ^ cz • S^ s • H^ ₃ • CZ) • ⟦ mc ⟧ₘ₊ ↑ • (⟦ m'′ *' -'₁ ⟧ₘ • S^ k') • CZ ≈⟨ (cright cright cleft cleft aux-MM ((m'′ *' -'₁) .proj₂) (m' .proj₂) (Eq.trans (Eq.sym (-‿distribʳ-* (m'′ .proj₁) ₁)) (Eq.cong -_ (*-identityʳ (m'′ .proj₁))))) ⟩
    (CZ^ cz • S^ s • H^ ₃ • CZ) • ⟦ mc ⟧ₘ₊ ↑ • (⟦ m' ⟧ₘ • S^ k') • CZ ≈⟨ (cright cright cleft lemma-MS^k (m' .proj₁) k' (m' .proj₂)) ⟩
    (CZ^ cz • S^ s • H^ ₃ • CZ) • ⟦ mc ⟧ₘ₊ ↑ • (S^ (k' * (m' .proj₁ * m' .proj₁)) • ⟦ m' ⟧ₘ) • CZ ≈⟨ special-assoc (□ ^ 4 • □ • □ ^ 2 • □) (□ ^ 3 • □ ^ 4 • □) auto ⟩
    (CZ^ cz • S^ s • H^ ₃) • (CZ • ⟦ mc ⟧ₘ₊ ↑ • (S^ (k' * (m' .proj₁ * m' .proj₁)) • ⟦ m' ⟧ₘ)) • CZ ≈⟨ (cright cleft (cright cright cright  sym right-unit)) ⟩
    (CZ^ cz • S^ s • H^ ₃) • (CZ • ⟦ mc ⟧ₘ₊ ↑ • (S^ (k' * (m' .proj₁ * m' .proj₁)) • ⟦ m' ⟧ₘ • ε)) • CZ ≈⟨ (cright (cleft cright cright refl)) ⟩
    (CZ^ cz • S^ s • H^ ₃) • (CZ • ⟦ mc ⟧ₘ₊ ↑ • (S^ (k' * (m' .proj₁ * m' .proj₁)) • ⟦ m' ⟧ₘ • ε)) • CZ ≈⟨ (cright claim) ⟩

    (CZ^ cz • S^ s • H^ ₃) • w' ↑ • ⟦ lm' ⟧₂ ≈⟨ special-assoc (□ ^ 3 • □ ^ 2) (□ • (□ ^ 2 • □) • □) auto ⟩
    CZ^ cz • ((S^ s • H^ ₃) • w' ↑) • ⟦ lm' ⟧₂ ≈⟨ (cright (cleft lemma-comm-S^aH^b s ₃ w')) ⟩
    CZ^ cz • (w' ↑ • S^ s • H^ ₃) • ⟦ lm' ⟧₂ ≈⟨ special-assoc (□ • □ ^ 3 • □ ) (□ ^ 2 • □ ^ 3) auto ⟩
    (CZ^ cz • w' ↑) • S^ s • H^ ₃ • ⟦ lm' ⟧₂ ≈⟨ refl ⟩
    (CZ^ cz • w' ↑) • S^ s • H^ ₃ • CZ • ⟦ aa* ⁻¹ , ε ⟧ₘ₊ ↑ • ⟦ (s' , m' , ε) ⟧₁  ≈⟨ ( cright cright cright cright cright cright right-unit ) ⟩
    (CZ^ cz • w' ↑) • S^ s • H^ ₃ • CZ • ⟦ aa* ⁻¹ , ε ⟧ₘ₊ ↑ • S^ s' • ⟦ m' ⟧ₘ  ≈⟨ (cright cright cright cright cong (lemma-cong↑ _ _ PB1.right-unit) (lemma-S^kM (m' .proj₁) s' (m' .proj₂))) ⟩
    (CZ^ cz • w' ↑) • S^ s • H^ ₃ • CZ • ⟦ aa* ⁻¹ ⟧ₘ ↑ • ⟦ m' ⟧ₘ • S^ (s' * ((m' ⁻¹) .proj₁ * (m' ⁻¹) .proj₁))  ≈⟨ ( cright cright cright cright cright cright sym left-unit) ⟩
    (CZ^ cz • w' ↑) • S^ s • H^ ₃ • CZ • ⟦ aa* ⁻¹ ⟧ₘ ↑ • ⟦ m' ⟧ₘ • ε • S^ (s' * ((m' ⁻¹) .proj₁ * (m' ⁻¹) .proj₁))  ≈⟨ ( cright cright cright cright cright cright (cleft sym (axiom order-H))) ⟩
    (CZ^ cz • w' ↑) • S^ s • H^ ₃ • CZ • ⟦ aa* ⁻¹ ⟧ₘ ↑ • ⟦ m' ⟧ₘ • H ^ 4 • S^ (s' * ((m' ⁻¹) .proj₁ * (m' ⁻¹) .proj₁))  ≈⟨ ( cright cright cright cright cright special-assoc (□ • □ ^ 4 • □) (□ ^ 4 • □ ^ 2) auto) ⟩
    (CZ^ cz • w' ↑) • S^ s • H^ ₃ • CZ • ⟦ aa* ⁻¹ ⟧ₘ ↑ • (⟦ m' ⟧ₘ • H ^ 3) • H • S^ (s' * ((m' ⁻¹) .proj₁ * (m' ⁻¹) .proj₁))  ≈⟨ ( cright cright cright cright cright cleft aux) ⟩
    (CZ^ cz • w' ↑) • S^ s • H^ ₃ • CZ • ⟦ aa* ⁻¹ ⟧ₘ ↑ • (H • ⟦ m'' ⟧ₘ) • H • S^ (s' * ((m' ⁻¹) .proj₁ * (m' ⁻¹) .proj₁))  ≈⟨ ( cright  cright  cright  cright special-assoc (□  • □ ^ 2 • □) (□ ^ 2 • □ ^ 2) auto) ⟩
    (CZ^ cz • w' ↑) • S^ s • H^ ₃ • CZ • (⟦ aa* ⁻¹ ⟧ₘ ↑ • H) • ⟦ m'' ⟧ₘ • H • S^ (s' * ((m' ⁻¹) .proj₁ * (m' ⁻¹) .proj₁))  ≈⟨ (cright cright cright cright cleft sym (lemma-comm-H-w↑ ⟦ aa* ⁻¹ ⟧ₘ)) ⟩
    (CZ^ cz • w' ↑) • S^ s • H^ ₃ • CZ • (H • ⟦ aa* ⁻¹ ⟧ₘ ↑) • ⟦ m'' ⟧ₘ • H • S^ (s' * ((m' ⁻¹) .proj₁ * (m' ⁻¹) .proj₁))  ≈⟨ (cright cright special-assoc (□ • □ • □ ^ 2 • □) (□ ^ 3 • □ ^ 2) auto) ⟩
    (CZ^ cz • w' ↑) • S^ s • (H^ ₃ • CZ • H) • ⟦ aa* ⁻¹ ⟧ₘ ↑ • ⟦ m'' ⟧ₘ • H • S^ (s' * ((m' ⁻¹) .proj₁ * (m' ⁻¹) .proj₁))  ≈⟨ (cright cright cright cleft sym (lemma-cong↑ _ _ PB1.right-unit)) ⟩
    (CZ^ cz • w' ↑) • S^ s • (H^ ₃ • CZ • H) • ⟦ aa* ⁻¹ , ε ⟧ₘ₊ ↑ • ⟦ m'' ⟧ₘ • H • S^ (s' * ((m' ⁻¹) .proj₁ * (m' ⁻¹) .proj₁))  ≈⟨ (cleft cright lemma-cong↑ _ _ (PB1.axiom (M-mul m aa*))) ⟩
    (CZ^ cz • ⟦ m *' aa* ⟧ₘ ↑) • S^ s • (H^ ₃ • CZ • H) • ⟦ aa* ⁻¹ , ε ⟧ₘ₊ ↑ • ⟦ m'' ⟧ₘ • H • S^ (s' * ((m' ⁻¹) .proj₁ * (m' ⁻¹) .proj₁))  ≈⟨ (cleft lemma-CZ^kM↑ ((m *' aa*) .proj₁) cz ((m *' aa*) .proj₂)) ⟩
    (⟦ m *' aa* ⟧ₘ ↑ • CZ^ (cz * ((m *' aa*) ⁻¹) .proj₁ )) • S^ s • (H^ ₃ • CZ • H) • ⟦ aa* ⁻¹ , ε ⟧ₘ₊ ↑ • ⟦ m'' ⟧ₘ • H • S^ (s' * ((m' ⁻¹) .proj₁ * (m' ⁻¹) .proj₁))  ≈⟨ assoc ⟩
    ⟦ m *' aa* ⟧ₘ ↑ • ⟦ case-||ₐ (cz * ((m *' aa*)⁻¹).proj₁) (s , (aa* ⁻¹ , ε) , (m'' , HS^ (s' * ((m' ⁻¹) .proj₁ * (m' ⁻¹) .proj₁)))) ⟧₂  ∎
    where
    aux : ⟦ m' ⟧ₘ • H ^ 3 ≈ H • ⟦ m'' ⟧ₘ
    aux = begin
      ⟦ m' ⟧ₘ • H ^ 3 ≈⟨ special-assoc (□ ^ 4) (□ ^ 3 • □) auto ⟩
      (⟦ m' ⟧ₘ • HH) • H ≈⟨ (cleft cright lemma-HH-M-1) ⟩
      (⟦ m' ⟧ₘ • M -'₁) • H ≈⟨ (cleft axiom (M-mul m' -'₁)) ⟩
      (⟦ m' *' -'₁ ⟧ₘ) • H ≈⟨ refl ⟩
      ⟦ m' *' -'₁ ⟧ₘ • H ≈⟨ (cleft aux-MM ((m' *' -'₁) .proj₂) (m'′ .proj₂) (Eq.trans (Eq.sym (-‿distribʳ-* (m' .proj₁) ₁)) (Eq.trans (Eq.cong -_ (*-identityʳ (m' .proj₁))) (-‿involutive (m'′ .proj₁))))) ⟩
      ⟦ m'′ ⟧ₘ • H ≈⟨ sym (semi-HM m'') ⟩
      H • ⟦ m'' ⟧ₘ ∎


--Lemma-two-qupit-completeness lm@(case-||ₐ cz@₀ (s , mc@(m , c@ε) , mc''@(m'' , c'@(HS^ k'@(₁₊ k'-1))))) (CZ-gen) with ((m ⁻¹) .proj₁ + - (m'' ⁻¹) .proj₁) | inspect (\ m -> ((m ⁻¹) .proj₁ + - (m'' ⁻¹) .proj₁)) m
Lemma-two-qupit-completeness-||ₐ-mε-mHS^k' cz@₀ s m m'' k'@(₁₊ k'-1) with ((m ⁻¹) .proj₁ + - (m'' ⁻¹) .proj₁) | inspect (\ m -> ((m ⁻¹) .proj₁ + - (m'' ⁻¹) .proj₁)) m
... | ₀ | [ eq ]' = lm'' , w' , claim' -- lm'' , w' , claim'

  where
  mc : MC
  mc = (m , ε)
  mc'' : MC
  mc'' = (m'' , HS^ k')
  
  m'′ = (m'' ⁻¹)
  m' = -' m'′
  m'⁻¹ = (m' ⁻¹) .proj₁
  m⁻¹ = (m ⁻¹) .proj₁
  a* = m' ⁻¹
  a = a* .proj₁
  l = m .proj₁
  -l : ℤ ₚ
  -l = - l
  l⁻¹ : ℤ ₚ
  l⁻¹ = ((m ⁻¹) .proj₁)
  -l⁻¹ : ℤ ₚ
  -l⁻¹ = - l⁻¹

  k′ : ℤ ₚ
  k′ = m'⁻¹
  a′ = m⁻¹
  m'0 = m' .proj₁
  k′⁻¹ = (((m') ⁻¹ ⁻¹) .proj₁)
  -k′⁻¹ = - k′⁻¹
  -k′ = - k′
  -m' = - m'0

  s' : ℤ ₚ
  s' =  (k' * (m' .proj₁ * m' .proj₁))

  lm' = case-nf1 (s' , m' , ε)
  w' = ⟦ m ⟧ₘ

  open CP1
  tw : TopwWord {1} (S^ s • H^ ₃ • ⟦ (s' , m' , ε) ⟧₁)
  tw = top-S^k (toℕ s) , (tt , tt , tt) , top-S^k {n = 1} (toℕ s') , top-M m' , tt

  nf1' = CP1.Theorem-single-qupit-completeness (S^ s • H^ ₃ • ⟦ (s' , m' , ε) ⟧₁) tw

  claim : ⟦ case-| (m , ε) (s' , m' , ε) ⟧₂ • CZ ≈ w' ↑ • ⟦ lm' ⟧₂
  claim = step-|-CZa m s' m' eq

  lm'' = case-nf1 (nf1' .proj₁)

  claim' : ⟦ case-||ₐ cz (s , mc , mc'') ⟧₂ • CZ ≈ w' ↑ • ⟦ lm'' ⟧₂
  claim' = begin
    ⟦ case-||ₐ cz (s , mc , mc'') ⟧₂ • CZ ≈⟨ refl ⟩
    (CZ^ cz • S^ s • (H^ ₃ • CZ • H) • ⟦ mc ⟧ₘ₊ ↑ • ⟦ mc'' ⟧ₘ₊) • CZ ≈⟨ special-assoc ((□ • □ • □ ^ 3 • □ • □) • □) (□ ^ 4 • □ ^ 2 • □ ^ 2) auto ⟩
    (CZ^ cz • S^ s • H^ ₃ • CZ) • (H • ⟦ mc ⟧ₘ₊ ↑) • ⟦ mc'' ⟧ₘ₊ • CZ ≈⟨ (cright (cleft lemma-comm-H-w↑ ⟦ mc ⟧ₘ₊)) ⟩
    (CZ^ cz • S^ s • H^ ₃ • CZ) • (⟦ mc ⟧ₘ₊ ↑ • H) • ⟦ mc'' ⟧ₘ₊ • CZ ≈⟨ (cright special-assoc (□ ^ 2 • □ ^ 2) (□ • □ ^ 2 • □) auto) ⟩
    (CZ^ cz • S^ s • H^ ₃ • CZ) • ⟦ mc ⟧ₘ₊ ↑ • (H • ⟦ mc'' ⟧ₘ₊) • CZ ≈⟨ (cright cright cleft sym assoc) ⟩
    (CZ^ cz • S^ s • H^ ₃ • CZ) • ⟦ mc ⟧ₘ₊ ↑ • ((H • ⟦ m'' ⟧ₘ) • H • S^ k') • CZ ≈⟨ (cright cright cleft cleft semi-HM m'') ⟩
    (CZ^ cz • S^ s • H^ ₃ • CZ) • ⟦ mc ⟧ₘ₊ ↑ • ((⟦ m'′ ⟧ₘ • H) • H • S^ k') • CZ ≈⟨ (cright cright cleft special-assoc (□ ^ 2 • □ ^ 2) (□ ^ 3 • □) auto) ⟩
    (CZ^ cz • S^ s • H^ ₃ • CZ) • ⟦ mc ⟧ₘ₊ ↑ • ((⟦ m'′ ⟧ₘ • HH) • S^ k') • CZ ≈⟨ (cright cright cleft cleft cright lemma-HH-M-1) ⟩
    (CZ^ cz • S^ s • H^ ₃ • CZ) • ⟦ mc ⟧ₘ₊ ↑ • ((⟦ m'′ ⟧ₘ • M -'₁) • S^ k') • CZ ≈⟨ (cright cright cleft cleft axiom (M-mul m'′ -'₁)) ⟩
    (CZ^ cz • S^ s • H^ ₃ • CZ) • ⟦ mc ⟧ₘ₊ ↑ • (⟦ m'′ *' -'₁ ⟧ₘ • S^ k') • CZ ≈⟨ (cright cright cleft cleft aux-MM ((m'′ *' -'₁) .proj₂) (m' .proj₂) (Eq.trans (Eq.sym (-‿distribʳ-* (m'′ .proj₁) ₁)) (Eq.cong -_ (*-identityʳ (m'′ .proj₁))))) ⟩
    (CZ^ cz • S^ s • H^ ₃ • CZ) • ⟦ mc ⟧ₘ₊ ↑ • (⟦ m' ⟧ₘ • S^ k') • CZ ≈⟨ (cright cright cleft lemma-MS^k (m' .proj₁) k' (m' .proj₂)) ⟩
    (CZ^ cz • S^ s • H^ ₃ • CZ) • ⟦ mc ⟧ₘ₊ ↑ • (S^ (k' * (m' .proj₁ * m' .proj₁)) • ⟦ m' ⟧ₘ) • CZ ≈⟨ special-assoc (□ ^ 4 • □ • □ ^ 2 • □) (□ ^ 3 • □ ^ 4 • □) auto ⟩
    (CZ^ cz • S^ s • H^ ₃) • (CZ • ⟦ mc ⟧ₘ₊ ↑ • (S^ (k' * (m' .proj₁ * m' .proj₁)) • ⟦ m' ⟧ₘ)) • CZ ≈⟨ (cright cleft (cright cright cright  sym right-unit)) ⟩
    (CZ^ cz • S^ s • H^ ₃) • (CZ • ⟦ mc ⟧ₘ₊ ↑ • (S^ (k' * (m' .proj₁ * m' .proj₁)) • ⟦ m' ⟧ₘ • ε)) • CZ ≈⟨ (cright claim) ⟩
    (CZ^ cz • S^ s • H^ ₃) • w' ↑ • ⟦ lm' ⟧₂ ≈⟨ special-assoc (□ ^ 3 • □ ^ 2) (□ • (□ ^ 2 • □) • □) auto ⟩
    CZ^ cz • ((S^ s • H^ ₃) • w' ↑) • ⟦ lm' ⟧₂ ≈⟨ (cright (cleft lemma-comm-S^aH^b s ₃ w')) ⟩
    CZ^ cz • (w' ↑ • S^ s • H^ ₃) • ⟦ lm' ⟧₂ ≈⟨ special-assoc (□ • □ ^ 3 • □ ) (□ ^ 2 • □ ^ 3) auto ⟩
    (CZ^ cz • w' ↑) • S^ s • H^ ₃ • ⟦ lm' ⟧₂ ≈⟨ (cleft lemma-CZ^kM↑ (m .proj₁) cz (m .proj₂)) ⟩
    (w' ↑ • CZ^ (cz * m⁻¹)) • S^ s • H^ ₃ • ⟦ lm' ⟧₂ ≈⟨ refl ⟩
    (w' ↑ • CZ^ (cz * m⁻¹)) • S^ s • H^ ₃ • ⟦ (s' , m' , ε) ⟧₁ ≈⟨ (cright nf1' .proj₂) ⟩
    (w' ↑ • CZ^ (cz * m⁻¹)) • ⟦ nf1' .proj₁ ⟧₁ ≈⟨ (cleft cright refl' (Eq.cong CZ^ (*-zeroˡ m⁻¹))) ⟩
    (w' ↑ • ε) • ⟦ nf1' .proj₁ ⟧₁ ≈⟨ (cleft right-unit) ⟩
    w' ↑ • ⟦ nf1' .proj₁ ⟧₁ ≈⟨ refl ⟩
    w' ↑ • ⟦ case-nf1 (nf1' .proj₁) ⟧₂  ∎


... | (₁₊ sm) | [ eq ]' = lm'' , ⟦ m *' aa* ⟧ₘ , claim'

  where
  mc : MC
  mc = (m , ε)
  mc'' : MC
  mc'' = (m'' , HS^ k')
  
  open import Data.Fin.Properties
  m'′ = (m'' ⁻¹)
  m' = -' m'′
  m'⁻¹ = (m' ⁻¹) .proj₁
  m⁻¹ = (m ⁻¹) .proj₁
  a* = m' ⁻¹
  a = a* .proj₁
  l = m .proj₁
  -l : ℤ ₚ
  -l = - l
  l⁻¹ : ℤ ₚ
  l⁻¹ = ((m ⁻¹) .proj₁)
  -l⁻¹ : ℤ ₚ
  -l⁻¹ = - l⁻¹

  k′ : ℤ ₚ
  k′ = m'⁻¹
  a′ = m⁻¹
  m'0 = m' .proj₁
  k′⁻¹ = (((m') ⁻¹ ⁻¹) .proj₁)
  -k′⁻¹ = - k′⁻¹
  -k′ = - k′
  -m' = - m'0

  s' : ℤ ₚ
  s' =  (k' * (m' .proj₁ * m' .proj₁))

  aa = ((m ⁻¹) .proj₁ + - (m'' ⁻¹) .proj₁)
  neqaa : aa ≢ ₀
  neqaa eq0 = 0≢1+n (Eq.trans (Eq.sym eq0) eq)
  aa* = (aa , neqaa)
  lm' = case-| (aa* ⁻¹ , ε) (s' , m' , ε)
  w' = ⟦ m ⟧ₘ • M (aa , neqaa)

  open CP1
  tw : TopwWord {1} (S^ s • H^ ₃ • ⟦ (s' , m' , ε) ⟧₁)
  tw = top-S^k (toℕ s) , (tt , tt , tt) , top-S^k {n = 1} (toℕ s') , top-M m' , tt

  nf1' = CP1.Theorem-single-qupit-completeness (S^ s • H^ ₃ • ⟦ (s' , m' , ε) ⟧₁) tw


  claim : ⟦ case-| (m , ε) (s' , m' , ε) ⟧₂ • CZ ≈ w' ↑ • ⟦ lm' ⟧₂
  claim = step-|-CZb m s' m' neqaa

  lm'' = case-||ₐ (cz * ((m *' aa*)⁻¹).proj₁) (s , (aa* ⁻¹ , ε) , (m'' , HS^ (s' * ((m' ⁻¹) .proj₁ * (m' ⁻¹) .proj₁))))
  -- w'' = ⟦ m *' aa* ⟧ₘ

  claim' : ⟦ case-||ₐ cz (s , mc , mc'') ⟧₂ • CZ ≈ ⟦ m *' aa* ⟧ₘ ↑ • ⟦ case-||ₐ (cz * ((m *' aa*)⁻¹).proj₁) (s , (aa* ⁻¹ , ε) , (m'' , HS^ (s' * ((m' ⁻¹) .proj₁ * (m' ⁻¹) .proj₁)))) ⟧₂
  claim' = begin
    ⟦ case-||ₐ cz (s , mc , mc'') ⟧₂ • CZ ≈⟨ refl ⟩
    (CZ^ cz • S^ s • (H^ ₃ • CZ • H) • ⟦ mc ⟧ₘ₊ ↑ • ⟦ mc'' ⟧ₘ₊) • CZ ≈⟨ special-assoc ((□ • □ • □ ^ 3 • □ • □) • □) (□ ^ 4 • □ ^ 2 • □ ^ 2) auto ⟩
    (CZ^ cz • S^ s • H^ ₃ • CZ) • (H • ⟦ mc ⟧ₘ₊ ↑) • ⟦ mc'' ⟧ₘ₊ • CZ ≈⟨ (cright (cleft lemma-comm-H-w↑ ⟦ mc ⟧ₘ₊)) ⟩
    (CZ^ cz • S^ s • H^ ₃ • CZ) • (⟦ mc ⟧ₘ₊ ↑ • H) • ⟦ mc'' ⟧ₘ₊ • CZ ≈⟨ (cright special-assoc (□ ^ 2 • □ ^ 2) (□ • □ ^ 2 • □) auto) ⟩
    (CZ^ cz • S^ s • H^ ₃ • CZ) • ⟦ mc ⟧ₘ₊ ↑ • (H • ⟦ mc'' ⟧ₘ₊) • CZ ≈⟨ (cright cright cleft sym assoc) ⟩
    (CZ^ cz • S^ s • H^ ₃ • CZ) • ⟦ mc ⟧ₘ₊ ↑ • ((H • ⟦ m'' ⟧ₘ) • H • S^ k') • CZ ≈⟨ (cright cright cleft cleft semi-HM m'') ⟩
    (CZ^ cz • S^ s • H^ ₃ • CZ) • ⟦ mc ⟧ₘ₊ ↑ • ((⟦ m'′ ⟧ₘ • H) • H • S^ k') • CZ ≈⟨ (cright cright cleft special-assoc (□ ^ 2 • □ ^ 2) (□ ^ 3 • □) auto) ⟩
    (CZ^ cz • S^ s • H^ ₃ • CZ) • ⟦ mc ⟧ₘ₊ ↑ • ((⟦ m'′ ⟧ₘ • HH) • S^ k') • CZ ≈⟨ (cright cright cleft cleft cright lemma-HH-M-1) ⟩
    (CZ^ cz • S^ s • H^ ₃ • CZ) • ⟦ mc ⟧ₘ₊ ↑ • ((⟦ m'′ ⟧ₘ • M -'₁) • S^ k') • CZ ≈⟨ (cright cright cleft cleft axiom (M-mul m'′ -'₁)) ⟩
    (CZ^ cz • S^ s • H^ ₃ • CZ) • ⟦ mc ⟧ₘ₊ ↑ • (⟦ m'′ *' -'₁ ⟧ₘ • S^ k') • CZ ≈⟨ (cright cright cleft cleft aux-MM ((m'′ *' -'₁) .proj₂) (m' .proj₂) (Eq.trans (Eq.sym (-‿distribʳ-* (m'′ .proj₁) ₁)) (Eq.cong -_ (*-identityʳ (m'′ .proj₁))))) ⟩
    (CZ^ cz • S^ s • H^ ₃ • CZ) • ⟦ mc ⟧ₘ₊ ↑ • (⟦ m' ⟧ₘ • S^ k') • CZ ≈⟨ (cright cright cleft lemma-MS^k (m' .proj₁) k' (m' .proj₂)) ⟩
    (CZ^ cz • S^ s • H^ ₃ • CZ) • ⟦ mc ⟧ₘ₊ ↑ • (S^ (k' * (m' .proj₁ * m' .proj₁)) • ⟦ m' ⟧ₘ) • CZ ≈⟨ special-assoc (□ ^ 4 • □ • □ ^ 2 • □) (□ ^ 3 • □ ^ 4 • □) auto ⟩
    (CZ^ cz • S^ s • H^ ₃) • (CZ • ⟦ mc ⟧ₘ₊ ↑ • (S^ (k' * (m' .proj₁ * m' .proj₁)) • ⟦ m' ⟧ₘ)) • CZ ≈⟨ (cright cleft (cright cright cright  sym right-unit)) ⟩
    (CZ^ cz • S^ s • H^ ₃) • (CZ • ⟦ mc ⟧ₘ₊ ↑ • (S^ (k' * (m' .proj₁ * m' .proj₁)) • ⟦ m' ⟧ₘ • ε)) • CZ ≈⟨ (cright (cleft cright cright refl)) ⟩
    (CZ^ cz • S^ s • H^ ₃) • (CZ • ⟦ mc ⟧ₘ₊ ↑ • (S^ (k' * (m' .proj₁ * m' .proj₁)) • ⟦ m' ⟧ₘ • ε)) • CZ ≈⟨ (cright claim) ⟩

    (CZ^ cz • S^ s • H^ ₃) • w' ↑ • ⟦ lm' ⟧₂ ≈⟨ special-assoc (□ ^ 3 • □ ^ 2) (□ • (□ ^ 2 • □) • □) auto ⟩
    CZ^ cz • ((S^ s • H^ ₃) • w' ↑) • ⟦ lm' ⟧₂ ≈⟨ (cright (cleft lemma-comm-S^aH^b s ₃ w')) ⟩
    CZ^ cz • (w' ↑ • S^ s • H^ ₃) • ⟦ lm' ⟧₂ ≈⟨ special-assoc (□ • □ ^ 3 • □ ) (□ ^ 2 • □ ^ 3) auto ⟩
    (CZ^ cz • w' ↑) • S^ s • H^ ₃ • ⟦ lm' ⟧₂ ≈⟨ refl ⟩
    (CZ^ cz • w' ↑) • S^ s • H^ ₃ • CZ • ⟦ aa* ⁻¹ , ε ⟧ₘ₊ ↑ • ⟦ (s' , m' , ε) ⟧₁  ≈⟨ ( cright cright cright cright cright cright right-unit ) ⟩
    (CZ^ cz • w' ↑) • S^ s • H^ ₃ • CZ • ⟦ aa* ⁻¹ , ε ⟧ₘ₊ ↑ • S^ s' • ⟦ m' ⟧ₘ  ≈⟨ (cright cright cright cright cong (lemma-cong↑ _ _ PB1.right-unit) (lemma-S^kM (m' .proj₁) s' (m' .proj₂))) ⟩
    (CZ^ cz • w' ↑) • S^ s • H^ ₃ • CZ • ⟦ aa* ⁻¹ ⟧ₘ ↑ • ⟦ m' ⟧ₘ • S^ (s' * ((m' ⁻¹) .proj₁ * (m' ⁻¹) .proj₁))  ≈⟨ ( cright cright cright cright cright cright sym left-unit) ⟩
    (CZ^ cz • w' ↑) • S^ s • H^ ₃ • CZ • ⟦ aa* ⁻¹ ⟧ₘ ↑ • ⟦ m' ⟧ₘ • ε • S^ (s' * ((m' ⁻¹) .proj₁ * (m' ⁻¹) .proj₁))  ≈⟨ ( cright cright cright cright cright cright (cleft sym (axiom order-H))) ⟩
    (CZ^ cz • w' ↑) • S^ s • H^ ₃ • CZ • ⟦ aa* ⁻¹ ⟧ₘ ↑ • ⟦ m' ⟧ₘ • H ^ 4 • S^ (s' * ((m' ⁻¹) .proj₁ * (m' ⁻¹) .proj₁))  ≈⟨ ( cright cright cright cright cright special-assoc (□ • □ ^ 4 • □) (□ ^ 4 • □ ^ 2) auto) ⟩
    (CZ^ cz • w' ↑) • S^ s • H^ ₃ • CZ • ⟦ aa* ⁻¹ ⟧ₘ ↑ • (⟦ m' ⟧ₘ • H ^ 3) • H • S^ (s' * ((m' ⁻¹) .proj₁ * (m' ⁻¹) .proj₁))  ≈⟨ ( cright cright cright cright cright cleft aux) ⟩
    (CZ^ cz • w' ↑) • S^ s • H^ ₃ • CZ • ⟦ aa* ⁻¹ ⟧ₘ ↑ • (H • ⟦ m'' ⟧ₘ) • H • S^ (s' * ((m' ⁻¹) .proj₁ * (m' ⁻¹) .proj₁))  ≈⟨ ( cright  cright  cright  cright special-assoc (□  • □ ^ 2 • □) (□ ^ 2 • □ ^ 2) auto) ⟩
    (CZ^ cz • w' ↑) • S^ s • H^ ₃ • CZ • (⟦ aa* ⁻¹ ⟧ₘ ↑ • H) • ⟦ m'' ⟧ₘ • H • S^ (s' * ((m' ⁻¹) .proj₁ * (m' ⁻¹) .proj₁))  ≈⟨ (cright cright cright cright cleft sym (lemma-comm-H-w↑ ⟦ aa* ⁻¹ ⟧ₘ)) ⟩
    (CZ^ cz • w' ↑) • S^ s • H^ ₃ • CZ • (H • ⟦ aa* ⁻¹ ⟧ₘ ↑) • ⟦ m'' ⟧ₘ • H • S^ (s' * ((m' ⁻¹) .proj₁ * (m' ⁻¹) .proj₁))  ≈⟨ (cright cright special-assoc (□ • □ • □ ^ 2 • □) (□ ^ 3 • □ ^ 2) auto) ⟩
    (CZ^ cz • w' ↑) • S^ s • (H^ ₃ • CZ • H) • ⟦ aa* ⁻¹ ⟧ₘ ↑ • ⟦ m'' ⟧ₘ • H • S^ (s' * ((m' ⁻¹) .proj₁ * (m' ⁻¹) .proj₁))  ≈⟨ (cright cright cright cleft sym (lemma-cong↑ _ _ PB1.right-unit)) ⟩
    (CZ^ cz • w' ↑) • S^ s • (H^ ₃ • CZ • H) • ⟦ aa* ⁻¹ , ε ⟧ₘ₊ ↑ • ⟦ m'' ⟧ₘ • H • S^ (s' * ((m' ⁻¹) .proj₁ * (m' ⁻¹) .proj₁))  ≈⟨ (cleft cright lemma-cong↑ _ _ (PB1.axiom (M-mul m aa*))) ⟩
    (CZ^ cz • ⟦ m *' aa* ⟧ₘ ↑) • S^ s • (H^ ₃ • CZ • H) • ⟦ aa* ⁻¹ , ε ⟧ₘ₊ ↑ • ⟦ m'' ⟧ₘ • H • S^ (s' * ((m' ⁻¹) .proj₁ * (m' ⁻¹) .proj₁))  ≈⟨ (cleft lemma-CZ^kM↑ ((m *' aa*) .proj₁) cz ((m *' aa*) .proj₂)) ⟩
    (⟦ m *' aa* ⟧ₘ ↑ • CZ^ (cz * (m *' aa*) .proj₁ )) • S^ s • (H^ ₃ • CZ • H) • ⟦ aa* ⁻¹ , ε ⟧ₘ₊ ↑ • ⟦ m'' ⟧ₘ • H • S^ (s' * ((m' ⁻¹) .proj₁ * (m' ⁻¹) .proj₁))  ≈⟨ assoc ⟩
    ⟦ m *' aa* ⟧ₘ ↑ • ⟦ case-||ₐ (cz * ((m *' aa*)⁻¹).proj₁) (s , (aa* ⁻¹ , ε) , (m'' , HS^ (s' * ((m' ⁻¹) .proj₁ * (m' ⁻¹) .proj₁)))) ⟧₂  ∎
    where
    aux : ⟦ m' ⟧ₘ • H ^ 3 ≈ H • ⟦ m'' ⟧ₘ
    aux = begin
      ⟦ m' ⟧ₘ • H ^ 3 ≈⟨ special-assoc (□ ^ 4) (□ ^ 3 • □) auto ⟩
      (⟦ m' ⟧ₘ • HH) • H ≈⟨ (cleft cright lemma-HH-M-1) ⟩
      (⟦ m' ⟧ₘ • M -'₁) • H ≈⟨ (cleft axiom (M-mul m' -'₁)) ⟩
      (⟦ m' *' -'₁ ⟧ₘ) • H ≈⟨ refl ⟩
      ⟦ m' *' -'₁ ⟧ₘ • H ≈⟨ (cleft aux-MM ((m' *' -'₁) .proj₂) (m'′ .proj₂) (Eq.trans (Eq.sym (-‿distribʳ-* (m' .proj₁) ₁)) (Eq.trans (Eq.cong -_ (*-identityʳ (m' .proj₁))) (-‿involutive (m'′ .proj₁))))) ⟩
      ⟦ m'′ ⟧ₘ • H ≈⟨ sym (semi-HM m'') ⟩
      H • ⟦ m'' ⟧ₘ ∎


Lemma-two-qupit-completeness-||ₐ-mε-mHS^k' cz@₀ s m m'' k'@₀ with ((m ⁻¹) .proj₁ + - (m'' ⁻¹) .proj₁) | inspect (\ m -> ((m ⁻¹) .proj₁ + - (m'' ⁻¹) .proj₁)) m
... | ₀ | [ eq ]' = lm'' , w' , claim' -- lm'' , w' , claim'

  where
  mc : MC
  mc = (m , ε)
  mc'' : MC
  mc'' = (m'' , HS^ k')
  
  m'′ = (m'' ⁻¹)
  m' = -' m'′
  m'⁻¹ = (m' ⁻¹) .proj₁
  m⁻¹ = (m ⁻¹) .proj₁
  a* = m' ⁻¹
  a = a* .proj₁
  l = m .proj₁
  -l : ℤ ₚ
  -l = - l
  l⁻¹ : ℤ ₚ
  l⁻¹ = ((m ⁻¹) .proj₁)
  -l⁻¹ : ℤ ₚ
  -l⁻¹ = - l⁻¹

  k′ : ℤ ₚ
  k′ = m'⁻¹
  a′ = m⁻¹
  m'0 = m' .proj₁
  k′⁻¹ = (((m') ⁻¹ ⁻¹) .proj₁)
  -k′⁻¹ = - k′⁻¹
  -k′ = - k′
  -m' = - m'0

  s' : ℤ ₚ
  s' =  (k' * (m' .proj₁ * m' .proj₁))

  lm' = case-nf1 (s' , m' , ε)
  w' = ⟦ m ⟧ₘ

  open CP1
  tw : TopwWord {1} (S^ s • H^ ₃ • ⟦ (s' , m' , ε) ⟧₁)
  tw = top-S^k (toℕ s) , (tt , tt , tt) , top-S^k {n = 1} (toℕ s') , top-M m' , tt

  nf1' = CP1.Theorem-single-qupit-completeness (S^ s • H^ ₃ • ⟦ (s' , m' , ε) ⟧₁) tw

  claim : ⟦ case-| (m , ε) (s' , m' , ε) ⟧₂ • CZ ≈ w' ↑ • ⟦ lm' ⟧₂
  claim = step-|-CZa m s' m' eq

  lm'' = case-nf1 (nf1' .proj₁)

  claim' : ⟦ case-||ₐ cz (s , mc , mc'') ⟧₂ • CZ ≈ w' ↑ • ⟦ lm'' ⟧₂
  claim' = begin
    ⟦ case-||ₐ cz (s , mc , mc'') ⟧₂ • CZ ≈⟨ refl ⟩
    (CZ^ cz • S^ s • (H^ ₃ • CZ • H) • ⟦ mc ⟧ₘ₊ ↑ • ⟦ mc'' ⟧ₘ₊) • CZ ≈⟨ special-assoc ((□ • □ • □ ^ 3 • □ • □) • □) (□ ^ 4 • □ ^ 2 • □ ^ 2) auto ⟩
    (CZ^ cz • S^ s • H^ ₃ • CZ) • (H • ⟦ mc ⟧ₘ₊ ↑) • ⟦ mc'' ⟧ₘ₊ • CZ ≈⟨ (cright (cleft lemma-comm-H-w↑ ⟦ mc ⟧ₘ₊)) ⟩
    (CZ^ cz • S^ s • H^ ₃ • CZ) • (⟦ mc ⟧ₘ₊ ↑ • H) • ⟦ mc'' ⟧ₘ₊ • CZ ≈⟨ (cright special-assoc (□ ^ 2 • □ ^ 2) (□ • □ ^ 2 • □) auto) ⟩
    (CZ^ cz • S^ s • H^ ₃ • CZ) • ⟦ mc ⟧ₘ₊ ↑ • (H • ⟦ mc'' ⟧ₘ₊) • CZ ≈⟨ (cright cright cleft sym assoc) ⟩
    (CZ^ cz • S^ s • H^ ₃ • CZ) • ⟦ mc ⟧ₘ₊ ↑ • ((H • ⟦ m'' ⟧ₘ) • H • S^ k') • CZ ≈⟨ (cright cright cleft cleft semi-HM m'') ⟩
    (CZ^ cz • S^ s • H^ ₃ • CZ) • ⟦ mc ⟧ₘ₊ ↑ • ((⟦ m'′ ⟧ₘ • H) • H • S^ k') • CZ ≈⟨ (cright cright cleft special-assoc (□ ^ 2 • □ ^ 2) (□ ^ 3 • □) auto) ⟩
    (CZ^ cz • S^ s • H^ ₃ • CZ) • ⟦ mc ⟧ₘ₊ ↑ • ((⟦ m'′ ⟧ₘ • HH) • S^ k') • CZ ≈⟨ (cright cright cleft cleft cright lemma-HH-M-1) ⟩
    (CZ^ cz • S^ s • H^ ₃ • CZ) • ⟦ mc ⟧ₘ₊ ↑ • ((⟦ m'′ ⟧ₘ • M -'₁) • S^ k') • CZ ≈⟨ (cright cright cleft cleft axiom (M-mul m'′ -'₁)) ⟩
    (CZ^ cz • S^ s • H^ ₃ • CZ) • ⟦ mc ⟧ₘ₊ ↑ • (⟦ m'′ *' -'₁ ⟧ₘ • S^ k') • CZ ≈⟨ (cright cright cleft cleft aux-MM ((m'′ *' -'₁) .proj₂) (m' .proj₂) (Eq.trans (Eq.sym (-‿distribʳ-* (m'′ .proj₁) ₁)) (Eq.cong -_ (*-identityʳ (m'′ .proj₁))))) ⟩
    (CZ^ cz • S^ s • H^ ₃ • CZ) • ⟦ mc ⟧ₘ₊ ↑ • (⟦ m' ⟧ₘ • S^ k') • CZ ≈⟨ (cright cright cleft lemma-MS^k (m' .proj₁) k' (m' .proj₂)) ⟩
    (CZ^ cz • S^ s • H^ ₃ • CZ) • ⟦ mc ⟧ₘ₊ ↑ • (S^ (k' * (m' .proj₁ * m' .proj₁)) • ⟦ m' ⟧ₘ) • CZ ≈⟨ special-assoc (□ ^ 4 • □ • □ ^ 2 • □) (□ ^ 3 • □ ^ 4 • □) auto ⟩
    (CZ^ cz • S^ s • H^ ₃) • (CZ • ⟦ mc ⟧ₘ₊ ↑ • (S^ (k' * (m' .proj₁ * m' .proj₁)) • ⟦ m' ⟧ₘ)) • CZ ≈⟨ (cright cleft (cright cright cright  sym right-unit)) ⟩
    (CZ^ cz • S^ s • H^ ₃) • (CZ • ⟦ mc ⟧ₘ₊ ↑ • (S^ (k' * (m' .proj₁ * m' .proj₁)) • ⟦ m' ⟧ₘ • ε)) • CZ ≈⟨ (cright claim) ⟩
    (CZ^ cz • S^ s • H^ ₃) • w' ↑ • ⟦ lm' ⟧₂ ≈⟨ special-assoc (□ ^ 3 • □ ^ 2) (□ • (□ ^ 2 • □) • □) auto ⟩
    CZ^ cz • ((S^ s • H^ ₃) • w' ↑) • ⟦ lm' ⟧₂ ≈⟨ (cright (cleft lemma-comm-S^aH^b s ₃ w')) ⟩
    CZ^ cz • (w' ↑ • S^ s • H^ ₃) • ⟦ lm' ⟧₂ ≈⟨ special-assoc (□ • □ ^ 3 • □ ) (□ ^ 2 • □ ^ 3) auto ⟩
    (CZ^ cz • w' ↑) • S^ s • H^ ₃ • ⟦ lm' ⟧₂ ≈⟨ (cleft lemma-CZ^kM↑ (m .proj₁) cz (m .proj₂)) ⟩
    (w' ↑ • CZ^ (cz * m⁻¹)) • S^ s • H^ ₃ • ⟦ lm' ⟧₂ ≈⟨ refl ⟩
    (w' ↑ • CZ^ (cz * m⁻¹)) • S^ s • H^ ₃ • ⟦ (s' , m' , ε) ⟧₁ ≈⟨ (cright nf1' .proj₂) ⟩
    (w' ↑ • CZ^ (cz * m⁻¹)) • ⟦ nf1' .proj₁ ⟧₁ ≈⟨ (cleft cright refl' (Eq.cong CZ^ (*-zeroˡ m⁻¹))) ⟩
    (w' ↑ • ε) • ⟦ nf1' .proj₁ ⟧₁ ≈⟨ (cleft right-unit) ⟩
    w' ↑ • ⟦ nf1' .proj₁ ⟧₁ ≈⟨ refl ⟩
    w' ↑ • ⟦ case-nf1 (nf1' .proj₁) ⟧₂  ∎


... | (₁₊ sm) | [ eq ]' = lm'' , ⟦ m *' aa* ⟧ₘ , claim' -- lm'' , w' , claim'

  where
  mc : MC
  mc = (m , ε)
  mc'' : MC
  mc'' = (m'' , HS^ k')
  
  open import Data.Fin.Properties
  m'′ = (m'' ⁻¹)
  m' = -' m'′
  m'⁻¹ = (m' ⁻¹) .proj₁
  m⁻¹ = (m ⁻¹) .proj₁
  a* = m' ⁻¹
  a = a* .proj₁
  l = m .proj₁
  -l : ℤ ₚ
  -l = - l
  l⁻¹ : ℤ ₚ
  l⁻¹ = ((m ⁻¹) .proj₁)
  -l⁻¹ : ℤ ₚ
  -l⁻¹ = - l⁻¹

  k′ : ℤ ₚ
  k′ = m'⁻¹
  a′ = m⁻¹
  m'0 = m' .proj₁
  k′⁻¹ = (((m') ⁻¹ ⁻¹) .proj₁)
  -k′⁻¹ = - k′⁻¹
  -k′ = - k′
  -m' = - m'0

  s' : ℤ ₚ
  s' =  (k' * (m' .proj₁ * m' .proj₁))

  aa = ((m ⁻¹) .proj₁ + - (m'' ⁻¹) .proj₁)
  neqaa : aa ≢ ₀
  neqaa eq0 = 0≢1+n (Eq.trans (Eq.sym eq0) eq)
  aa* = (aa , neqaa)
  lm' = case-| (aa* ⁻¹ , ε) (s' , m' , ε)
  w' = ⟦ m ⟧ₘ • M (aa , neqaa)

  open CP1
  tw : TopwWord {1} (S^ s • H^ ₃ • ⟦ (s' , m' , ε) ⟧₁)
  tw = top-S^k (toℕ s) , (tt , tt , tt) , top-S^k {n = 1} (toℕ s') , top-M m' , tt

  nf1' = CP1.Theorem-single-qupit-completeness (S^ s • H^ ₃ • ⟦ (s' , m' , ε) ⟧₁) tw


  claim : ⟦ case-| (m , ε) (s' , m' , ε) ⟧₂ • CZ ≈ w' ↑ • ⟦ lm' ⟧₂
  claim = step-|-CZb m s' m' neqaa

  lm'' = case-||ₐ (cz * ((m *' aa*)⁻¹).proj₁) (s , (aa* ⁻¹ , ε) , (m'' , HS^ ₀))
  -- w'' = ⟦ m *' aa* ⟧ₘ

  claim' : ⟦ case-||ₐ cz (s , mc , mc'') ⟧₂ • CZ ≈ ⟦ m *' aa* ⟧ₘ ↑ • ⟦ case-||ₐ (cz * ((m *' aa*)⁻¹).proj₁) (s , (aa* ⁻¹ , ε) , (m'' , HS^ ₀)) ⟧₂
  claim' = begin
    ⟦ case-||ₐ cz (s , mc , mc'') ⟧₂ • CZ ≈⟨ refl ⟩
    (CZ^ cz • S^ s • (H^ ₃ • CZ • H) • ⟦ mc ⟧ₘ₊ ↑ • ⟦ mc'' ⟧ₘ₊) • CZ ≈⟨ special-assoc ((□ • □ • □ ^ 3 • □ • □) • □) (□ ^ 4 • □ ^ 2 • □ ^ 2) auto ⟩
    (CZ^ cz • S^ s • H^ ₃ • CZ) • (H • ⟦ mc ⟧ₘ₊ ↑) • ⟦ mc'' ⟧ₘ₊ • CZ ≈⟨ (cright (cleft lemma-comm-H-w↑ ⟦ mc ⟧ₘ₊)) ⟩
    (CZ^ cz • S^ s • H^ ₃ • CZ) • (⟦ mc ⟧ₘ₊ ↑ • H) • ⟦ mc'' ⟧ₘ₊ • CZ ≈⟨ (cright special-assoc (□ ^ 2 • □ ^ 2) (□ • □ ^ 2 • □) auto) ⟩
    (CZ^ cz • S^ s • H^ ₃ • CZ) • ⟦ mc ⟧ₘ₊ ↑ • (H • ⟦ mc'' ⟧ₘ₊) • CZ ≈⟨ (cright cright cleft sym assoc) ⟩
    (CZ^ cz • S^ s • H^ ₃ • CZ) • ⟦ mc ⟧ₘ₊ ↑ • ((H • ⟦ m'' ⟧ₘ) • H • S^ k') • CZ ≈⟨ (cright cright cleft cleft semi-HM m'') ⟩
    (CZ^ cz • S^ s • H^ ₃ • CZ) • ⟦ mc ⟧ₘ₊ ↑ • ((⟦ m'′ ⟧ₘ • H) • H • S^ k') • CZ ≈⟨ (cright cright cleft special-assoc (□ ^ 2 • □ ^ 2) (□ ^ 3 • □) auto) ⟩
    (CZ^ cz • S^ s • H^ ₃ • CZ) • ⟦ mc ⟧ₘ₊ ↑ • ((⟦ m'′ ⟧ₘ • HH) • S^ k') • CZ ≈⟨ (cright cright cleft cleft cright lemma-HH-M-1) ⟩
    (CZ^ cz • S^ s • H^ ₃ • CZ) • ⟦ mc ⟧ₘ₊ ↑ • ((⟦ m'′ ⟧ₘ • M -'₁) • S^ k') • CZ ≈⟨ (cright cright cleft cleft axiom (M-mul m'′ -'₁)) ⟩
    (CZ^ cz • S^ s • H^ ₃ • CZ) • ⟦ mc ⟧ₘ₊ ↑ • (⟦ m'′ *' -'₁ ⟧ₘ • S^ k') • CZ ≈⟨ (cright cright cleft cleft aux-MM ((m'′ *' -'₁) .proj₂) (m' .proj₂) (Eq.trans (Eq.sym (-‿distribʳ-* (m'′ .proj₁) ₁)) (Eq.cong -_ (*-identityʳ (m'′ .proj₁))))) ⟩
    (CZ^ cz • S^ s • H^ ₃ • CZ) • ⟦ mc ⟧ₘ₊ ↑ • (⟦ m' ⟧ₘ • S^ k') • CZ ≈⟨ (cright cright cleft lemma-MS^k (m' .proj₁) k' (m' .proj₂)) ⟩
    (CZ^ cz • S^ s • H^ ₃ • CZ) • ⟦ mc ⟧ₘ₊ ↑ • (S^ (k' * (m' .proj₁ * m' .proj₁)) • ⟦ m' ⟧ₘ) • CZ ≈⟨ special-assoc (□ ^ 4 • □ • □ ^ 2 • □) (□ ^ 3 • □ ^ 4 • □) auto ⟩
    (CZ^ cz • S^ s • H^ ₃) • (CZ • ⟦ mc ⟧ₘ₊ ↑ • (S^ (k' * (m' .proj₁ * m' .proj₁)) • ⟦ m' ⟧ₘ)) • CZ ≈⟨ (cright cleft (cright cright cright  sym right-unit)) ⟩
    (CZ^ cz • S^ s • H^ ₃) • (CZ • ⟦ mc ⟧ₘ₊ ↑ • (S^ (k' * (m' .proj₁ * m' .proj₁)) • ⟦ m' ⟧ₘ • ε)) • CZ ≈⟨ (cright (cleft cright cright refl)) ⟩
    (CZ^ cz • S^ s • H^ ₃) • (CZ • ⟦ mc ⟧ₘ₊ ↑ • (ε • ⟦ m' ⟧ₘ • ε)) • CZ ≈⟨ (cright claim) ⟩

    (CZ^ cz • S^ s • H^ ₃) • w' ↑ • ⟦ lm' ⟧₂ ≈⟨ special-assoc (□ ^ 3 • □ ^ 2) (□ • (□ ^ 2 • □) • □) auto ⟩
    CZ^ cz • ((S^ s • H^ ₃) • w' ↑) • ⟦ lm' ⟧₂ ≈⟨ (cright (cleft lemma-comm-S^aH^b s ₃ w')) ⟩
    CZ^ cz • (w' ↑ • S^ s • H^ ₃) • ⟦ lm' ⟧₂ ≈⟨ special-assoc (□ • □ ^ 3 • □ ) (□ ^ 2 • □ ^ 3) auto ⟩
    (CZ^ cz • w' ↑) • S^ s • H^ ₃ • ⟦ lm' ⟧₂ ≈⟨ refl ⟩
    (CZ^ cz • w' ↑) • S^ s • H^ ₃ • CZ • ⟦ aa* ⁻¹ , ε ⟧ₘ₊ ↑ • ⟦ (₀ , m' , ε) ⟧₁  ≈⟨ ( cright cright cright cright cright trans left-unit right-unit ) ⟩
    (CZ^ cz • w' ↑) • S^ s • H^ ₃ • CZ • ⟦ aa* ⁻¹ , ε ⟧ₘ₊ ↑ • ⟦ m' ⟧ₘ  ≈⟨ ( cright cright cright cright cright trans (sym right-unit) (cright sym (axiom order-H)) ) ⟩
    (CZ^ cz • w' ↑) • S^ s • H^ ₃ • CZ • ⟦ aa* ⁻¹ , ε ⟧ₘ₊ ↑ • ⟦ m' ⟧ₘ • H ^ 4  ≈⟨ ( cright cright cright cright cright special-assoc (□ ^ 5) (□ ^ 3 • □ ^ 2) auto ) ⟩
    (CZ^ cz • w' ↑) • S^ s • H^ ₃ • CZ • ⟦ aa* ⁻¹ , ε ⟧ₘ₊ ↑ • (⟦ m' ⟧ₘ • HH) • HH  ≈⟨ ( cright cright cright cright cright cleft cright lemma-HH-M-1 ) ⟩
    (CZ^ cz • w' ↑) • S^ s • H^ ₃ • CZ • ⟦ aa* ⁻¹ , ε ⟧ₘ₊ ↑ • (⟦ m' ⟧ₘ • M -'₁) • HH  ≈⟨ ( cright cright cright cright cright cleft axiom (M-mul m' -'₁) ) ⟩
    (CZ^ cz • w' ↑) • S^ s • H^ ₃ • CZ • ⟦ aa* ⁻¹ , ε ⟧ₘ₊ ↑ • (⟦ m' *' -'₁ ⟧ₘ) • HH  ≈⟨ ( cright cright cright cright cright cleft aux-MM ((m' *' -'₁) .proj₂) (m'′ .proj₂) (Eq.trans (Eq.sym (-‿distribʳ-* (m' .proj₁) ₁)) (Eq.trans (Eq.cong -_ (*-identityʳ (m' .proj₁))) (-‿involutive (m'′ .proj₁)))) ) ⟩
    (CZ^ cz • w' ↑) • S^ s • H^ ₃ • CZ • ⟦ aa* ⁻¹ , ε ⟧ₘ₊ ↑ • (⟦ m'′ ⟧ₘ) • HH  ≈⟨ ( cright cright cright cright cright sym assoc ) ⟩
    (CZ^ cz • w' ↑) • S^ s • H^ ₃ • CZ • ⟦ aa* ⁻¹ , ε ⟧ₘ₊ ↑ • (⟦ m'′ ⟧ₘ • H) • H  ≈⟨ ( cright cright cright cright cright cleft sym (semi-HM m'') ) ⟩
    (CZ^ cz • w' ↑) • S^ s • H^ ₃ • CZ • ⟦ aa* ⁻¹ , ε ⟧ₘ₊ ↑ • (H • ⟦ m'' ⟧ₘ) • H  ≈⟨ ( cright cright cright cright special-assoc (□ • □ ^ 2 • □) (□ ^ 2 • □ ^ 2) auto ) ⟩
    (CZ^ cz • w' ↑) • S^ s • H^ ₃ • CZ • (⟦ aa* ⁻¹ , ε ⟧ₘ₊ ↑ • H) • (⟦ m'' ⟧ₘ • H)  ≈⟨ ( cright cright cright cright cong (sym (lemma-comm-H-w↑ ⟦ aa* ⁻¹ , ε ⟧ₘ₊)) (cright sym right-unit) ) ⟩
    (CZ^ cz • w' ↑) • S^ s • H^ ₃ • CZ • (H • ⟦ aa* ⁻¹ , ε ⟧ₘ₊ ↑) • (⟦ m'' ⟧ₘ • H • ε)  ≈⟨ ( cright cright special-assoc (□ • □ • □ ^ 2 • □) (□ ^ 3 • □ ^ 2) auto ) ⟩
    (CZ^ cz • w' ↑) • S^ s • (H^ ₃ • CZ • H) • ⟦ aa* ⁻¹ , ε ⟧ₘ₊ ↑ • (⟦ m'' ⟧ₘ • H • ε)  ≈⟨ ( cleft (cright lemma-cong↑ _ _ (PB1.axiom (M-mul m aa*))) ) ⟩
    (CZ^ cz • ⟦ m *' aa* ⟧ₘ ↑) • S^ s • (H^ ₃ • CZ • H) • ⟦ aa* ⁻¹ , ε ⟧ₘ₊ ↑ • (⟦ m'' ⟧ₘ • H • ε)  ≈⟨ ( cleft lemma-CZ^kM↑ ((m *' aa*) .proj₁) cz ((m *' aa*) .proj₂) ) ⟩
    (⟦ m *' aa* ⟧ₘ ↑ • CZ^ (cz * ((m *' aa*)⁻¹).proj₁)) • S^ s • (H^ ₃ • CZ • H) • ⟦ aa* ⁻¹ , ε ⟧ₘ₊ ↑ • (⟦ m'' ⟧ₘ • H • ε)  ≈⟨ ( special-assoc (□ ^ 2 • □ ) (□ • □ ^ 2) auto ) ⟩
    ⟦ m *' aa* ⟧ₘ ↑ • CZ^ (cz * ((m *' aa*)⁻¹).proj₁) • S^ s • (H^ ₃ • CZ • H) • ⟦ aa* ⁻¹ , ε ⟧ₘ₊ ↑ • (⟦ m'' ⟧ₘ • H • ε)  ≈⟨ ( refl ) ⟩
    ⟦ m *' aa* ⟧ₘ ↑ • ⟦ case-||ₐ (cz * ((m *' aa*)⁻¹).proj₁) (s , (aa* ⁻¹ , ε) , (m'' , HS^ ₀)) ⟧₂  ∎

