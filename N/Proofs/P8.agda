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



module N.Proofs.P8 (p-2 : ℕ) (p-prime : Prime (2+ p-2))  where

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
open import N.NF1-Sym p-2 p-prime
open import N.Ex-Sym p-2 p-prime
open import N.Ex-Sym1 p-2 p-prime
open import N.Ex-Sym2 p-2 p-prime
open import N.Ex-Sym3 p-2 p-prime
open import N.Ex-Sym4 p-2 p-prime
open import N.Proofs.P2 p-2 p-prime
open import N.Proofs.P6 p-2 p-prime
open import N.Proofs.P7 p-2 p-prime
open import N.Proofs.P9 p-2 p-prime
open import N.Duality p-2 p-prime
open import N.Lemma-Comm p-2 p-prime 0
open import N.Lemma-Postfix p-2 p-prime
open import N.Derived p-2 p-prime
open import N.Cosets p-2 p-prime

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

open Sym0-Rewriting 1
open Commuting-Symplectic 0
open Symplectic-GroupLike
open import Zp.Mod-Lemmas p-2 p-prime

open Basis-Change _ ((₂₊ 0) QRel,_===_) grouplike



lemma-case-||'' : ∀ k* l' (pf : Postfix) -> (k≠1 : k* .proj₁ ≢ ₁) -> let l = ₁₊ l' in

  ∃ \ w -> ∃ \ nf2 -> ⟦ case-|| k* l pf ⟧₂ ≈ w ↑ • ⟦ nf2 ⟧₂ • Ex

lemma-case-||'' k*@(k , nzk) l' pf@(sp , mc2 , mc1) k≠1 = w' ,  lm' , (aux-NF2''' k* l pf nz k≠1) .proj₂ .proj₂
  where

  l = ₁₊ l'
  1⁻¹ : ℤ ₚ
  1⁻¹ = (((₁ , λ ()) ⁻¹)) .proj₁
  
  pf' = (sp + l , mc1 , mc2)
  w : Word (Gen 1)
  w = H • S^ l
  kp = prede k*
  nz : l ≢ ₀
  nz = λ ()
  l* = (l , nz)
  -l = - l
  l⁻¹ = ((l* ⁻¹) .proj₁)
  l⁻¹⁻¹ = ((l* ⁻¹ ⁻¹) .proj₁)
  -l⁻¹ = -((l* ⁻¹) .proj₁)
  -k = - k
  -kl = -k * l
  -kl' = - (k * l)
  kl = k * l
  sp' = sp + kl

--  smc : H ^ 3 • S^ -kl • H • S^ -l⁻¹ • H ≈  ⟦ (ss , mm , HS^ kk) ⟧₁
  smc = aux5 k* l* k≠1 -- 

  ss = smc .proj₁
  mm = smc .proj₂ .proj₁
  kk = smc .proj₂ .proj₂ .proj₁
  mm⁻¹ = (mm ⁻¹) .proj₁
  
  w' = (M (l* ⁻¹) • S^ -l • S^ kl • H • S^ ss • M mm • HH)
  lm' = case-|| (mm ⁻¹)  kk (sp' , mc1 , mc2)




Lemma-two-qupit-completeness-||-mHS^k-mε :

  ∀ cz* l sp m2 k m1 ->
  let
  mc2 = (m2 , HS^ k)
  mc1 = (m1 , ε)
  lm = case-|| cz* l (sp , mc2 , mc1)
  in
  -------------------------------------------------
  ∃ \ lm' -> ∃ \ w -> ⟦ lm ⟧₂ • CZ ≈ w ↑ • ⟦ lm' ⟧₂


--Lemma-two-qupit-completeness-||-mHS^k-mε lm@(case-|| cz*@(₂₊ cz-2 , czneq) l@(₁₊ l-1) pf@(sp , mc2@(m2 , c2@(HS^ k)) , mc1@(m1 , c1@ε))) (CZ-gen) = lm''' , w''' , claim''
Lemma-two-qupit-completeness-||-mHS^k-mε cz*@((₂₊ cz-2) , czneq) l@(₁₊ l-1) sp m2 k2 m1 = lm''' , w''' , claim''

  where
  mc2 = (m2 , HS^ k2)
  mc1 = (m1 , ε)
  pf = (sp , mc2 , mc1)
  
  lm = case-|| cz* l (sp , mc2 , mc1)
  1⁻¹ : ℤ ₚ
  1⁻¹ = (((₁ , λ ()) ⁻¹)) .proj₁

  w : Word (Gen 1)
  w = H • S^ l
  k* = cz*
  k = cz* .proj₁
  kp = prede k*
  nz : l ≢ ₀
  nz = λ ()
  l* = (l , nz)
  -l = - l
  l⁻¹ = ((l* ⁻¹) .proj₁)
  l⁻¹⁻¹ = ((l* ⁻¹ ⁻¹) .proj₁)
  -l⁻¹ = -((l* ⁻¹) .proj₁)
  -k = - k
  -kl = -k * l
  -kl' = - (k * l)
  kl = k * l
  sp' = sp + kl


  k≠1 : k* .proj₁ ≢ ₁
  k≠1 = λ ()
  smc = aux5 k* l* k≠1
  ss = smc .proj₁
  mm = smc .proj₂ .proj₁
  kk = smc .proj₂ .proj₂ .proj₁
  mm⁻¹ = (mm ⁻¹) .proj₁

  w' = (M (l* ⁻¹) • S^ -l • S^ kl • H • S^ ss • M mm • HH)
  lm' = case-|| (mm ⁻¹)  kk (sp' , mc1 , mc2)


  aux2a : ⟦ case-|| cz* l pf ⟧₂ ≈ w' ↑ • ⟦ lm' ⟧₂ • Ex 
  aux2a = begin
    ⟦ case-|| cz* l pf ⟧₂ ≈⟨ (lemma-case-||' k* l-1 pf k≠1) .proj₂ .proj₂ ⟩ 
    w' ↑ • ⟦ lm' ⟧₂ • Ex ∎


  ih = Lemma-two-qupit-completeness-||-mε-mHS^k' (mm ⁻¹)  kk sp' m1 m2 k2
  ihp = ih .proj₂ .proj₂
  w'' = ih .proj₂ .proj₁
  lm'' = ih .proj₁
  cd = Theorem-NF2-duality lm''
  w4 = cd .proj₁
  lm''' = cd .proj₂ .proj₁
  cdp = cd .proj₂ .proj₂
  w''' = w' • w'' • w4

  claim'' : ⟦ case-|| cz* l (sp , mc2 , mc1) ⟧₂ • CZ ≈ w''' ↑ • ⟦ lm''' ⟧₂
  claim'' = begin
    ⟦ case-|| cz* l (sp , mc2 , mc1) ⟧₂ • CZ ≈⟨ (cleft aux2a) ⟩
    (w' ↑ • ⟦ lm' ⟧₂ • Ex) • CZ ≈⟨ special-assoc (□ ^ 3 • □) (□ ^ 2 • □ ^ 2) auto ⟩
    (w' ↑ • ⟦ lm' ⟧₂) • Ex • CZ ≈⟨ (cright sym lemma-comm-Ex-CZ) ⟩
    (w' ↑ • ⟦ lm' ⟧₂) • CZ • Ex ≈⟨ special-assoc (□ ^ 2 • □ ^ 2) (□ • □ ^ 2 • □) auto ⟩
    w' ↑ • (⟦ lm' ⟧₂ • CZ) • Ex ≈⟨ (cright cleft ihp) ⟩
    w' ↑ • (w'' ↑ • ⟦ lm'' ⟧₂) • Ex ≈⟨ sym (special-assoc (□ ^ 2 • □ ^ 2) (□ • □ ^ 2 • □) auto) ⟩
    (w' • w'') ↑ • ⟦ lm'' ⟧₂ • Ex ≈⟨ (cright cdp) ⟩
    (w' • w'') ↑ • w4 ↑ • ⟦ lm''' ⟧₂ ≈⟨ special-assoc (□ ^ 2 • □ ^ 2) (□ ^ 3 • □) auto ⟩
    (w' • w'' • w4) ↑ • ⟦ lm''' ⟧₂ ≈⟨ refl ⟩
    w''' ↑ • ⟦ lm''' ⟧₂ ∎

Lemma-two-qupit-completeness-||-mHS^k-mε cz*@(₂₊ cz-2 , czneq) l@₀ sp m2 k m1 = lm''' , w''' , claim''

  where
  mc2 = (m2 , HS^ k)
  mc1 = (m1 , ε)
  pf = (sp , mc2 , mc1)
  
  czp = prede cz*
  cz = cz* .proj₁
  cz≠1 : cz ≢ ₁
  cz≠1 = λ ()
  aux : - czp ≢ ₀
  aux = (-' (czp , aux-k*≠1 cz* cz≠1)) .proj₂
  nf2 = case-|| (- czp , aux)  ₀  (sp , mc1 , mc2)
  aux2 : ⟦ case-|| cz* l pf ⟧₂ ≈ HH ↑ • ⟦ nf2 ⟧₂ • Ex 
  aux2 = begin
    ⟦ case-|| cz* l pf ⟧₂ ≈⟨ aux-NF2'''0b cz* pf (aux-k*≠1 cz* cz≠1) ⟩
    HH ↑ • ⟦ nf2 ⟧₂ • Ex ∎

  ih = Lemma-two-qupit-completeness-||-mε-mHS^k' (- czp , aux) ₀ sp m1 m2 k
  ihp = ih .proj₂ .proj₂
  w'' = ih .proj₂ .proj₁
  lm'' = ih .proj₁
  cd = Theorem-NF2-duality lm''
  w4 = cd .proj₁
  lm''' = cd .proj₂ .proj₁
  cdp = cd .proj₂ .proj₂
  w''' = HH • w'' • w4

  claim'' : ⟦ case-|| cz* l (sp , mc2 , mc1) ⟧₂ • CZ ≈ w''' ↑ • ⟦ lm''' ⟧₂
  claim'' = begin
    ⟦ case-|| cz* l (sp , mc2 , mc1) ⟧₂ • CZ ≈⟨ (cleft aux2) ⟩
    (HH ↑ • ⟦ nf2 ⟧₂ • Ex) • CZ ≈⟨ special-assoc (□ ^ 3 • □) (□ ^ 2 • □ ^ 2) auto ⟩
    (HH ↑ • ⟦ nf2 ⟧₂) • Ex • CZ ≈⟨ (cright sym lemma-comm-Ex-CZ) ⟩
    (HH ↑ • ⟦ nf2 ⟧₂) • CZ • Ex ≈⟨ special-assoc (□ ^ 2 • □ ^ 2) (□ • □ ^ 2 • □) auto ⟩
    HH ↑ • (⟦ nf2 ⟧₂ • CZ) • Ex ≈⟨ (cright cleft ihp) ⟩
    HH ↑ • (w'' ↑ • ⟦ lm'' ⟧₂) • Ex ≈⟨ sym (special-assoc (□ ^ 2 • □ ^ 2) (□ • □ ^ 2 • □) auto) ⟩
    (HH • w'') ↑ • ⟦ lm'' ⟧₂ • Ex ≈⟨ (cright cdp) ⟩
    (HH • w'') ↑ • w4 ↑ • ⟦ lm''' ⟧₂ ≈⟨ special-assoc (□ ^ 2 • □ ^ 2) (□ ^ 3 • □) auto ⟩
    (HH • w'' • w4) ↑ • ⟦ lm''' ⟧₂ ≈⟨ refl ⟩
    w''' ↑ • ⟦ lm''' ⟧₂ ∎


Lemma-two-qupit-completeness-||-mHS^k-mε cz*@(₀ , czneq) l sp m2 k m1 = ⊥-elim (czneq auto)
Lemma-two-qupit-completeness-||-mHS^k-mε cz*@(₁ , czneq) l sp m2 k m1 = lm''' , w''' , claim''

  where
  mc2 = (m2 , HS^ k)
  mc1 = (m1 , ε)
  
  w = H • S^ l
  pf' = (sp + l , mc1 , mc2)

  ih = Lemma-two-qupit-completeness-||ₐ-mε-mHS^k' (- l) (sp + l) m1 m2 k
  ihp = ih .proj₂ .proj₂
  w'' = ih .proj₂ .proj₁
  lm'' = ih .proj₁

  cd = Theorem-NF2-duality lm''
  w4 = cd .proj₁
  lm''' = cd .proj₂ .proj₁
  cdp = cd .proj₂ .proj₂
  w''' = w • w'' • w4

  claim'' : ⟦ case-|| cz* l (sp , mc2 , mc1) ⟧₂ • CZ ≈ w''' ↑ • ⟦ lm''' ⟧₂
  claim'' = begin
    ⟦ case-|| cz* l (sp , mc2 , mc1) ⟧₂ • CZ ≈⟨ (cleft aux-NF2′ l (sp , mc2 , mc1)) ⟩
    (w ↑ • ⟦ case-||ₐ (- l) pf' ⟧₂ • Ex) • CZ ≈⟨ special-assoc (□ ^ 3 • □) (□ ^ 2 • □ ^ 2) auto ⟩
    (w ↑ • ⟦ case-||ₐ (- l) pf' ⟧₂) • Ex • CZ ≈⟨ (cright sym lemma-comm-Ex-CZ) ⟩
    (w ↑ • ⟦ case-||ₐ (- l) pf' ⟧₂) • CZ • Ex ≈⟨ (special-assoc (□ ^ 2 • □ ^ 2) (□ • □ ^ 2 • □) auto) ⟩
    w ↑ • (⟦ case-||ₐ (- l) pf' ⟧₂ • CZ) • Ex ≈⟨ (cright cleft ihp) ⟩
    w ↑ • (w'' ↑ • ⟦ lm'' ⟧₂) • Ex ≈⟨ sym (special-assoc (□ ^ 2 • □ ^ 2) (□ • □ ^ 2 • □) auto) ⟩
    (w • w'') ↑ • ⟦ lm'' ⟧₂ • Ex ≈⟨ (cright cdp) ⟩
    (w • w'') ↑ • w4 ↑ • ⟦ lm''' ⟧₂ ≈⟨ sym (special-assoc (□ ^ 3 • □) (□ ^ 2 • □ ^ 2) auto) ⟩
    w''' ↑ • ⟦ lm''' ⟧₂ ∎
