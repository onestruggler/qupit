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



module N.Proofs.P6 (p-2 : ℕ) (p-prime : Prime (2+ p-2))  where

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
open import N.Proofs.P2 p-2 p-prime
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


lemma-case-Ex-nf1-Ex : ∀ x -> ⟦ case-Ex-nf1 x ⟧₂ • Ex ≈ ⟦ case-nf1 x ⟧₂
lemma-case-Ex-nf1-Ex x = bbc ε Ex aux
  where
  aux : ε • (⟦ case-Ex-nf1 x ⟧₂ • Ex) • Ex ≈ ε • ⟦ case-nf1 x ⟧₂ • Ex
  aux = begin
    ε • (⟦ case-Ex-nf1 x ⟧₂ • Ex) • Ex ≈⟨ left-unit ⟩
    (⟦ case-Ex-nf1 x ⟧₂ • Ex) • Ex ≈⟨ assoc ⟩
    ⟦ case-Ex-nf1 x ⟧₂ • Ex • Ex ≈⟨ cright lemma-order-Ex ⟩
    ⟦ case-Ex-nf1 x ⟧₂ • ε ≈⟨ right-unit ⟩
    ⟦ case-Ex-nf1 x ⟧₂ ≈⟨ lemma-Ex-SMC x ⟩
    ⟦ case-nf1 x ⟧₂ • Ex ≈⟨ sym left-unit ⟩
    ε • ⟦ case-nf1 x ⟧₂ • Ex ∎



lemma-Ex-SMC↑ : ∀ nf1 -> Ex • ⟦ nf1 ⟧₁ ≈ ⟦ nf1 ⟧₁ ↑ • Ex
lemma-Ex-SMC↑ nf1 = bbc Ex Ex claim
  where
  claim : Ex • (Ex • ⟦ nf1 ⟧₁) • Ex ≈ Ex • (⟦ nf1 ⟧₁ ↑ • Ex) • Ex
  claim = begin
    Ex • (Ex • ⟦ nf1 ⟧₁) • Ex ≈⟨ special-assoc (□ • □ ^ 2 • □) (□ ^ 2 • □ ^ 2) auto ⟩
    (Ex • Ex) • ⟦ nf1 ⟧₁ • Ex ≈⟨ trans (cleft lemma-order-Ex) left-unit ⟩
    ⟦ nf1 ⟧₁ • Ex ≈⟨ sym (lemma-Ex-SMC nf1) ⟩
    Ex • ⟦ nf1 ⟧₁ ↑ ≈⟨ sym (trans (cright lemma-order-Ex) right-unit) ⟩
    (Ex • ⟦ nf1 ⟧₁ ↑) • Ex • Ex ≈⟨ sym (special-assoc (□ • □ ^ 2 • □) (□ ^ 2 • □ ^ 2) auto) ⟩
    Ex • (⟦ nf1 ⟧₁ ↑ • Ex) • Ex ∎


lemma-case-|-Ex : ∀ x y -> ⟦ case-| x y ⟧₂ • Ex ≈ ⟦ case-Ex-| y x ⟧₂
lemma-case-|-Ex x y = begin
  ⟦ case-| x y ⟧₂ • Ex ≈⟨ special-assoc (□ ^ 3 • □) (□ ^ 2 • □ ^ 2) auto ⟩
  (CZ • ⟦ x ⟧ₘ₊ ↑) • ⟦ y ⟧₁ • Ex ≈⟨ cright sym (lemma-Ex-SMC y) ⟩
  (CZ • ⟦ x ⟧ₘ₊ ↑) • Ex • ⟦ y ⟧₁ ↑ ≈⟨ sym (special-assoc (□ • □ ^ 2 • □) (□ ^ 2 • □ ^ 2) auto) ⟩
  CZ • (⟦ x ⟧ₘ₊ ↑ • Ex) • ⟦ y ⟧₁ ↑ ≈⟨ cright cleft sym (lemma-Ex-MC x) ⟩
  CZ • (Ex • ⟦ x ⟧ₘ₊) • ⟦ y ⟧₁ ↑ ≈⟨ special-assoc (□ • □ ^ 2 • □) (□ ^ 2 • □ ^ 2) auto ⟩
  (CZ • Ex) • ⟦ x ⟧ₘ₊ • ⟦ y ⟧₁ ↑ ≈⟨ cong lemma-comm-Ex-CZ (aux-comm-MCSMC x y) ⟩
  (Ex • CZ) • ⟦ y ⟧₁ ↑ • ⟦ x ⟧ₘ₊ ≈⟨ assoc ⟩
  ⟦ case-Ex-| y x ⟧₂ ∎


lemma-case-Ex-|-Ex : ∀ x y -> ⟦ case-Ex-| x y ⟧₂ • Ex ≈ ⟦ case-| y x ⟧₂
lemma-case-Ex-|-Ex x y = bbc ε Ex aux
  where
  aux : ε • (⟦ case-Ex-| x y ⟧₂ • Ex) • Ex ≈ ε • ⟦ case-| y x ⟧₂ • Ex
  aux = begin
    ε • (⟦ case-Ex-| x y ⟧₂ • Ex) • Ex ≈⟨ left-unit ⟩
    (⟦ case-Ex-| x y ⟧₂ • Ex) • Ex ≈⟨ assoc ⟩
    ⟦ case-Ex-| x y ⟧₂ • Ex • Ex ≈⟨ cright lemma-order-Ex ⟩
    ⟦ case-Ex-| x y ⟧₂ • ε ≈⟨ right-unit ⟩
    ⟦ case-Ex-| x y ⟧₂ ≈⟨ sym (lemma-case-|-Ex y x) ⟩
    ⟦ case-| y x ⟧₂ • Ex ≈⟨ sym left-unit ⟩
    ε • ⟦ case-| y x ⟧₂ • Ex ∎


lemma-case-||ₐ : ∀ l (pf : Postfix) -> let (sp , mc2 , mc1) = pf in let pf' = (sp + l , mc1 , mc2) in let w = S^ l • H ^ 3 in
  ⟦ case-||ₐ l pf ⟧₂ • Ex ≈ w ↑ • ⟦ case-|| (₁ , λ ()) (- l) pf' ⟧₂
lemma-case-||ₐ l pf@(sp , mc2 , mc1) = begin
  ⟦ case-||ₐ l pf ⟧₂ • Ex ≈⟨ cleft sym (lemma-Ex-dual' ⟦ case-||ₐ l pf ⟧₂) ⟩
  (Ex • dual ⟦ case-||ₐ l pf ⟧₂ • Ex) • Ex ≈⟨ trans (by-assoc auto) assoc ⟩
  (Ex • dual ⟦ case-||ₐ l pf ⟧₂) • Ex • Ex ≈⟨ trans (cright lemma-order-Ex) right-unit ⟩
  (Ex • dual ⟦ case-||ₐ l pf ⟧₂) ≈⟨ sym (aux-NF2'' l pf) ⟩
  w ↑ • ⟦ case-|| (₁ , λ ()) (- l) pf' ⟧₂ ∎
  where
  w = (S^ l • H ^ 3)
  pf' = (sp + l , mc1 , mc2)

  
lemma-case-|| : ∀ k* l (pf : Postfix) -> (k≠1 : k* .proj₁ ≢ ₁) ->

  ∃ \ w -> ∃ \ nf2 -> ⟦ case-|| k* l pf ⟧₂ • Ex ≈ w ↑ • ⟦ nf2 ⟧₂

lemma-case-|| k* l@₀ pf@(sp , mc2 , mc1) k≠1 = HH , nf2 , bbc ε Ex claim
  where
  kp = prede k*
  aux : - kp ≢ ₀
  aux = (-' (kp , aux-k*≠1 k* k≠1)) .proj₂
  nf2 = case-|| (- kp , aux)  ₀  (sp , mc1 , mc2)
  aux2 : ⟦ case-|| k* l pf ⟧₂ ≈ HH ↑ • ⟦ nf2 ⟧₂ • Ex 
  aux2 = begin
    ⟦ case-|| k* l pf ⟧₂ ≈⟨ aux-NF2'''0b k* pf (aux-k*≠1 k* k≠1) ⟩
    HH ↑ • ⟦ nf2 ⟧₂ • Ex ∎
  w = HH
  claim : ε • (⟦ case-|| k* l pf ⟧₂ • Ex) • Ex ≈ ε • (w ↑ • ⟦ nf2 ⟧₂) • Ex
  claim = begin
    ε • (⟦ case-|| k* l pf ⟧₂ • Ex) • Ex ≈⟨ left-unit ⟩
    (⟦ case-|| k* l pf ⟧₂ • Ex) • Ex ≈⟨ assoc ⟩
    ⟦ case-|| k* l pf ⟧₂ • Ex • Ex ≈⟨ (trans (cright lemma-order-Ex) right-unit) ⟩
    ⟦ case-|| k* l pf ⟧₂ ≈⟨ aux2 ⟩
    w ↑ • ⟦ nf2 ⟧₂ • Ex ≈⟨ sym assoc ⟩
    (w ↑ • ⟦ nf2 ⟧₂) • Ex ≈⟨ sym left-unit ⟩
    ε • (w ↑ • ⟦ nf2 ⟧₂) • Ex ∎

  
lemma-case-|| k*@(k , nzk) l@(₁₊ l') pf@(sp , mc2 , mc1) k≠1 = w' ,  lm' , bbc ε Ex claim
  where
  open import Data.Fin.Properties

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


  aux-kl=kl' : -kl ≡ -kl'
  aux-kl=kl' = Eq.sym (-‿distribˡ-* k l)

  aux : CZ ^ p-1 • H ↑ ^ 3 •  H ↑ • CZ ≈ ε
  aux = begin
    CZ ^ p-1 • H ↑ ^ 3 •  H ↑ • CZ ≈⟨ cright sym assoc ⟩
    CZ ^ p-1 • (H ↑ ^ 3 •  H ↑) • CZ ≈⟨ cright cleft rewrite-sym0 100 auto ⟩
    CZ ^ p-1 • ε • CZ ≈⟨ cright left-unit ⟩
    CZ ^ p-1 • CZ ≈⟨ word-comm p-1 1 refl ⟩
    CZ ^ p ≈⟨ axiom order-CZ ⟩
    ε ∎
  aux1 : -1⁻¹ * -kl ≡ - -kl
  aux1 = Eq.trans (Eq.cong (_* -kl) inv-neg₁ ) (-1*x≈-x -kl)
  aux2 : 1⁻¹ * -kl ≡ -kl
  aux2 = Eq.trans (Eq.cong (_* -kl) aux₁⁻¹') (*-identityˡ -kl)
  aux3 : - -kl ≡ kl
  aux3 = Eq.trans (Eq.cong -_ (Eq.sym (-‿distribˡ-* k l))) (-‿involutive kl)
  aux4 : (S^ kl ↑ • H ↑ • CZ • H ↑ ^ 3 • S^ -kl ↑ • H ↑) • S^ kl ≈ S^ kl • (S^ kl ↑ • H ↑ • CZ • H ↑ ^ 3 • S^ -kl ↑ • H ↑)
  aux4 = begin
    (S^ kl ↑ • H ↑ • CZ • H ↑ ^ 3 • S^ -kl ↑ • H ↑) • S^ kl ≈⟨ special-assoc (□ ^ 6 • □) (□ ^ 3 • □ ^ 3 • □) auto ⟩
    (S^ kl ↑ • H ↑ • CZ) • (H ↑ ^ 3 • S^ -kl ↑ • H ↑) • S^ kl ≈⟨ cright sym (lemma-comm-Sᵏ-w↑ (toℕ kl) (H ^ 3 • S^ -kl • H)) ⟩
    (S^ kl ↑ • H ↑ • CZ) • S^ kl • (H ↑ ^ 3 • S^ -kl ↑ • H ↑) ≈⟨ special-assoc (□ ^ 3 • □ • □ ^ 3) (□ ^ 2 • □ ^ 2 • □ ^ 3) auto ⟩
    (S^ kl ↑ • H ↑) • (CZ • S^ kl) • (H ↑ ^ 3 • S^ -kl ↑ • H ↑) ≈⟨ cright cleft word-comm 1 (toℕ kl) (axiom comm-CZ-S↓) ⟩
    (S^ kl ↑ • H ↑) • (S^ kl • CZ) • (H ↑ ^ 3 • S^ -kl ↑ • H ↑) ≈⟨ special-assoc (□ ^ 2 • □ ^ 2 • □ ^ 3) ((□ ^ 2 • □) • □ • □ ^ 3) auto ⟩
    ((S^ kl ↑ • H ↑) • S^ kl) • CZ • (H ↑ ^ 3 • S^ -kl ↑ • H ↑) ≈⟨ cleft sym (lemma-comm-Sᵏ-w↑ (toℕ kl) (S^ kl • H)) ⟩
    (S^ kl • (S^ kl ↑ • H ↑)) • CZ • (H ↑ ^ 3 • S^ -kl ↑ • H ↑) ≈⟨ special-assoc (□ ^ 3 • □ • □ ^ 3) (□ • □ ^ 6) auto ⟩
    S^ kl • (S^ kl ↑ • H ↑ • CZ • H ↑ ^ 3 • S^ -kl ↑ • H ↑) ∎


  open CP1
  tw : TopwWord {0} (H ^ 3 • S^ -kl • H • S^ -l⁻¹ • H)
  tw = (tt , tt , tt) , top-S^k (toℕ -kl) , tt , top-S^k (toℕ -l⁻¹) , tt
  nf1p = CP1.Theorem-single-qupit-completeness (H ^ 3 • S^ -kl • H • S^ -l⁻¹ • H) tw
  nf₁ = nf1p .proj₁
  s₁ = nf₁ .proj₁
  mc₁ = nf₁ .proj₂
  smc = aux5 k* l* k≠1
  ss = smc .proj₁
  mm = smc .proj₂ .proj₁
  kk = smc .proj₂ .proj₂ .proj₁
  mm⁻¹ = (mm ⁻¹) .proj₁
  
  w' = (M (l* ⁻¹) • S^ -l • S^ kl • H • S^ ss • M mm • HH)
  lm' = case-|| (mm ⁻¹)  kk (sp' , mc1 , mc2)

  claim : ε • (⟦ case-|| k* l pf ⟧₂ • Ex) • Ex ≈ ε • (w' ↑ • ⟦ lm' ⟧₂) • Ex
  claim = begin
    ε • (⟦ case-|| k* l pf ⟧₂ • Ex) • Ex ≈⟨ left-unit ⟩
    (⟦ case-|| k* l pf ⟧₂ • Ex) • Ex ≈⟨ assoc ⟩
    ⟦ case-|| k* l pf ⟧₂ • Ex • Ex ≈⟨ (trans (cright lemma-order-Ex) right-unit) ⟩
    ⟦ case-|| k* l pf ⟧₂ ≈⟨ (aux-NF2''' k* l pf nz k≠1) .proj₂ .proj₂ ⟩
    w' ↑ • ⟦ lm' ⟧₂ • Ex ≈⟨ sym assoc ⟩
    (w' ↑ • ⟦ lm' ⟧₂) • Ex ≈⟨ sym left-unit ⟩
    ε • (w' ↑ • ⟦ lm' ⟧₂) • Ex ∎



lemma-case-||₁ : ∀ l (pf : Postfix) -> 

  ∃ \ w -> ∃ \ lm -> ⟦ case-|| (₁ , λ ()) l pf ⟧₂ • Ex ≈ w ↑ • ⟦ lm ⟧₂

lemma-case-||₁ l pf@(sp , mc2 , mc1) = w , case-||ₐ (- l) pf' , bbc ε Ex claim
  where
  pf' = (sp + l , mc1 , mc2)
  w = H • S^ l
  lm = case-||ₐ (- l) pf'
  claim : ε • (⟦ case-|| (₁ , λ ()) l pf ⟧₂ • Ex) • Ex ≈ ε • (w ↑ • ⟦ lm ⟧₂) • Ex
  claim = begin
    ε • (⟦ case-|| (₁ , λ ()) l pf ⟧₂ • Ex) • Ex ≈⟨ left-unit ⟩
    (⟦ case-|| (₁ , λ ()) l pf ⟧₂ • Ex) • Ex ≈⟨ assoc ⟩
    ⟦ case-|| (₁ , λ ()) l pf ⟧₂ • Ex • Ex ≈⟨ trans (cright lemma-order-Ex) right-unit ⟩
    ⟦ case-|| (₁ , λ ()) l pf ⟧₂ ≈⟨ aux-NF2′ l pf ⟩
    w ↑ • ⟦ lm ⟧₂ • Ex ≈⟨ sym assoc ⟩
    (w ↑ • ⟦ lm ⟧₂) • Ex ≈⟨ sym left-unit ⟩
    ε • (w ↑ • ⟦ lm ⟧₂) • Ex ∎


Theorem-NF2-duality :

    ∀ (lm : Cosets2) ->
    -------------------------------------------------
    ∃ \ w -> ∃ \ lm' -> ⟦ lm ⟧₂ • Ex ≈ w ↑ • ⟦ lm' ⟧₂

Theorem-NF2-duality (case-||ₐ l pf@(sp , mc2 , mc1)) = S^ l • H ^ 3 , case-|| (₁ , λ ()) (- l) (sp + l , mc1 , mc2) , lemma-case-||ₐ l pf
Theorem-NF2-duality (case-|| k*@(₀ , nz) l pf) = ⊥-elim (nz auto)
Theorem-NF2-duality (case-|| k*@(₁ , nz) l pf) = lemma-case-||₁ l pf
Theorem-NF2-duality (case-|| k*@(₂₊ k-2 , nz) l pf) = lemma-case-|| k* l pf (λ ())
Theorem-NF2-duality (case-Ex-| x y) = ε , case-| y x , trans (lemma-case-Ex-|-Ex x y) (sym left-unit)
Theorem-NF2-duality (case-| x y) = ε , case-Ex-| y x , trans (lemma-case-|-Ex x y) (sym left-unit)
Theorem-NF2-duality (case-nf1 x) = ε , (case-Ex-nf1 x) , trans (sym (lemma-Ex-SMC x)) (sym left-unit)
Theorem-NF2-duality (case-Ex-nf1 x) = ε , case-nf1 x , trans (lemma-case-Ex-nf1-Ex x) (sym left-unit)






lemma-case-||' : ∀ k* l' (pf : Postfix) -> (k≠1 : k* .proj₁ ≢ ₁) -> let l = ₁₊ l' in

  ∃ \ w -> ∃ \ nf2 -> ⟦ case-|| k* l pf ⟧₂ ≈ w ↑ • ⟦ nf2 ⟧₂ • Ex

lemma-case-||' k*@(k , nzk) l' pf@(sp , mc2 , mc1) k≠1 = w' ,  lm' , (aux-NF2''' k* l pf nz k≠1) .proj₂ .proj₂
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


  aux-kl=kl' : -kl ≡ -kl'
  aux-kl=kl' = Eq.sym (-‿distribˡ-* k l)

  aux : CZ ^ p-1 • H ↑ ^ 3 •  H ↑ • CZ ≈ ε
  aux = begin
    CZ ^ p-1 • H ↑ ^ 3 •  H ↑ • CZ ≈⟨ cright sym assoc ⟩
    CZ ^ p-1 • (H ↑ ^ 3 •  H ↑) • CZ ≈⟨ cright cleft rewrite-sym0 100 auto ⟩
    CZ ^ p-1 • ε • CZ ≈⟨ cright left-unit ⟩
    CZ ^ p-1 • CZ ≈⟨ word-comm p-1 1 refl ⟩
    CZ ^ p ≈⟨ axiom order-CZ ⟩
    ε ∎
  aux1 : -1⁻¹ * -kl ≡ - -kl
  aux1 = Eq.trans (Eq.cong (_* -kl) inv-neg₁ ) (-1*x≈-x -kl)
  aux2 : 1⁻¹ * -kl ≡ -kl
  aux2 = Eq.trans (Eq.cong (_* -kl) aux₁⁻¹') (*-identityˡ -kl)
  aux3 : - -kl ≡ kl
  aux3 = Eq.trans (Eq.cong -_ (Eq.sym (-‿distribˡ-* k l))) (-‿involutive kl)
  aux4 : (S^ kl ↑ • H ↑ • CZ • H ↑ ^ 3 • S^ -kl ↑ • H ↑) • S^ kl ≈ S^ kl • (S^ kl ↑ • H ↑ • CZ • H ↑ ^ 3 • S^ -kl ↑ • H ↑)
  aux4 = begin
    (S^ kl ↑ • H ↑ • CZ • H ↑ ^ 3 • S^ -kl ↑ • H ↑) • S^ kl ≈⟨ special-assoc (□ ^ 6 • □) (□ ^ 3 • □ ^ 3 • □) auto ⟩
    (S^ kl ↑ • H ↑ • CZ) • (H ↑ ^ 3 • S^ -kl ↑ • H ↑) • S^ kl ≈⟨ cright sym (lemma-comm-Sᵏ-w↑ (toℕ kl) (H ^ 3 • S^ -kl • H)) ⟩
    (S^ kl ↑ • H ↑ • CZ) • S^ kl • (H ↑ ^ 3 • S^ -kl ↑ • H ↑) ≈⟨ special-assoc (□ ^ 3 • □ • □ ^ 3) (□ ^ 2 • □ ^ 2 • □ ^ 3) auto ⟩
    (S^ kl ↑ • H ↑) • (CZ • S^ kl) • (H ↑ ^ 3 • S^ -kl ↑ • H ↑) ≈⟨ cright cleft word-comm 1 (toℕ kl) (axiom comm-CZ-S↓) ⟩
    (S^ kl ↑ • H ↑) • (S^ kl • CZ) • (H ↑ ^ 3 • S^ -kl ↑ • H ↑) ≈⟨ special-assoc (□ ^ 2 • □ ^ 2 • □ ^ 3) ((□ ^ 2 • □) • □ • □ ^ 3) auto ⟩
    ((S^ kl ↑ • H ↑) • S^ kl) • CZ • (H ↑ ^ 3 • S^ -kl ↑ • H ↑) ≈⟨ cleft sym (lemma-comm-Sᵏ-w↑ (toℕ kl) (S^ kl • H)) ⟩
    (S^ kl • (S^ kl ↑ • H ↑)) • CZ • (H ↑ ^ 3 • S^ -kl ↑ • H ↑) ≈⟨ special-assoc (□ ^ 3 • □ • □ ^ 3) (□ • □ ^ 6) auto ⟩
    S^ kl • (S^ kl ↑ • H ↑ • CZ • H ↑ ^ 3 • S^ -kl ↑ • H ↑) ∎


  open CP1
  tw : TopwWord {0} (H ^ 3 • S^ -kl • H • S^ -l⁻¹ • H)
  tw = (tt , tt , tt) , top-S^k (toℕ -kl) , tt , top-S^k (toℕ -l⁻¹) , tt
  nf1p = CP1.Theorem-single-qupit-completeness (H ^ 3 • S^ -kl • H • S^ -l⁻¹ • H) tw
  nf₁ = nf1p .proj₁
  s₁ = nf₁ .proj₁
  mc₁ = nf₁ .proj₂
  smc = aux5 k* l* k≠1
  ss = smc .proj₁
  mm = smc .proj₂ .proj₁
  kk = smc .proj₂ .proj₂ .proj₁
  mm⁻¹ = (mm ⁻¹) .proj₁
  
  w' = (M (l* ⁻¹) • S^ -l • S^ kl • H • S^ ss • M mm • HH)
  lm' = case-|| (mm ⁻¹)  kk (sp' , mc1 , mc2)

