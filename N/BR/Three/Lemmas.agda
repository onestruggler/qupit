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



module N.BR.Three.Lemmas (p-2 : ℕ) (p-prime : Prime (2+ p-2))  where

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
--open import N.Ex-Sym5 p-2 p-prime hiding (module L0)
open import N.Ex-Sym2n p-2 p-prime
open import N.Ex-Sym3n p-2 p-prime
open import N.Ex-Sym4n p-2 p-prime

open import N.Lemma-Comm-n p-2 p-prime 0
open import N.Completeness1-Sym p-2 p-prime renaming (module Completeness to Cp1)
open Lemmas0a
open Lemmas0a1
open Lemmas0b
open Lemmas0c
open Lemmas-Sym
open Duality

open import N.Completeness1-Sym p-2 p-prime renaming (module Completeness to CP1) using ()
--open import N.Coset2-Update-Sym p-2 p-prime renaming (module Completeness to CP2) using ()
open import N.Lemmas4-Sym p-2 p-prime
open import N.Lemmas-3Q p-2 p-prime
open import N.Pushing.DH p-2 p-prime
open import N.Duality p-2 p-prime
open import N.BR.Calculations p-2 p-prime


open PB (3 QRel,_===_)
open PP (3 QRel,_===_)
module B2 = PB (2 QRel,_===_)
module P2 = PP (2 QRel,_===_)
module B1 = PB (1 QRel,_===_)
module P1 = PP (1 QRel,_===_)
open SR word-setoid
open Pattern-Assoc
open Lemmas0 1
open Lemmas-2Q 1
module L2Q0 = Lemmas-2Q 0
open Sym0-Rewriting 2
open Rewriting-Powers 2
open Rewriting-Swap 2
open Rewriting-Swap0 2
open Symplectic-GroupLike
open Basis-Change _ (3 QRel,_===_) grouplike
open import N.EX-Rewriting p-2 p-prime
open Rewriting-EX 2
open Homo 2
open import Data.List
open import N.BR.Two.Lemmas p-2 p-prime hiding (sa)
open import N.Embeding-2n p-2 p-prime 1 as Em
open Commuting-Symplectic 1

--module EX = Symplectic-EX

lemma-|||-mm : ∀ m↑ m -> CZ02 • ⟦ m↑ ⟧ₘ ↑ ↑ • CZ • ⟦ m ⟧ₘ ↑ • CZ ↑ ≈ (CZ^ (m .proj₁ * m↑ .proj₁)) ↑ • CZ02 • ⟦ m↑ ⟧ₘ ↑ ↑ • CZ • ⟦ m ⟧ₘ ↑
lemma-|||-mm m↑@(m↑' , nz↑) m@(m' , nz) = begin
  CZ02 • ⟦ m↑ ⟧ₘ ↑ ↑ • CZ • ⟦ m ⟧ₘ ↑ • CZ ↑ ≈⟨ cright cright cright lemma-cong↑ _ _ (B2.axiom (semi-M↓CZ m)) ⟩
  CZ02 • ⟦ m↑ ⟧ₘ ↑ ↑ • CZ • (CZ^ m') ↑ • ⟦ m ⟧ₘ ↑ ≈⟨ cright cright cright sym (cleft refl' (lemma-^-↑ CZ (toℕ m'))) ⟩
  CZ02 • ⟦ m↑ ⟧ₘ ↑ ↑ • CZ • (CZ ↑ ^ toℕ m') • ⟦ m ⟧ₘ ↑ ≈⟨ cright cright sym assoc ⟩
  CZ02 • ⟦ m↑ ⟧ₘ ↑ ↑ • (CZ • (CZ ↑ ^ toℕ m')) • ⟦ m ⟧ₘ ↑ ≈⟨ cright cright cleft word-comm 1 (toℕ m') (sym (axiom selinger-c12)) ⟩
  CZ02 • ⟦ m↑ ⟧ₘ ↑ ↑ • ((CZ ↑ ^ toℕ m') • CZ) • ⟦ m ⟧ₘ ↑ ≈⟨ cright special-assoc (□ • □ ^ 2 • □) (□ ^ 2 • □ ^ 2) auto ⟩
  CZ02 • (⟦ m↑ ⟧ₘ ↑ ↑ • (CZ ↑ ^ toℕ m')) • CZ • ⟦ m ⟧ₘ ↑ ≈⟨ cright cleft cright refl' (lemma-^-↑ CZ (toℕ m')) ⟩
  CZ02 • (⟦ m↑ ⟧ₘ ↑ ↑ • (CZ^ m') ↑) • CZ • ⟦ m ⟧ₘ ↑ ≈⟨ cright cleft lemma-cong↑ _ _ (L2Q0.lemma-M↑CZ^k m↑' m' nz↑) ⟩
  CZ02 • ((CZ^ (m' * m↑')) ↑ • ⟦ m↑ ⟧ₘ ↑ ↑) • CZ • ⟦ m ⟧ₘ ↑ ≈⟨ special-assoc (□ • □ ^ 2 • □) (□ ^ 2 • □ ^ 2) auto ⟩
  (CZ02 • (CZ^ (m' * m↑')) ↑) • ⟦ m↑ ⟧ₘ ↑ ↑ • CZ • ⟦ m ⟧ₘ ↑ ≈⟨ cleft cright sym (refl' (lemma-^-↑ CZ (toℕ (m' * m↑')))) ⟩
  (CZ02 • (CZ ↑ ^ toℕ (m' * m↑'))) • ⟦ m↑ ⟧ₘ ↑ ↑ • CZ • ⟦ m ⟧ₘ ↑ ≈⟨ cleft word-comm 1 (toℕ (m' * m↑')) (sym lemma-comm-CZ↑-CZ02) ⟩
  ((CZ ↑ ^ toℕ (m' * m↑')) • CZ02) • ⟦ m↑ ⟧ₘ ↑ ↑ • CZ • ⟦ m ⟧ₘ ↑ ≈⟨ assoc ⟩
  (CZ ↑ ^ toℕ (m' * m↑')) • CZ02 • ⟦ m↑ ⟧ₘ ↑ ↑ • CZ • ⟦ m ⟧ₘ ↑ ≈⟨ cleft refl' (lemma-^-↑ CZ (toℕ (m' * m↑'))) ⟩
  (CZ^ (m' * m↑')) ↑ • CZ02 • ⟦ m↑ ⟧ₘ ↑ ↑ • CZ • ⟦ m ⟧ₘ ↑ ∎


aux-comm-CZ↑-S↑↑ : ∀ m k -> CZ^ m ↑ • S^ k ↑ ↑ ≈ S^ k ↑ ↑ • CZ^ m ↑
aux-comm-CZ↑-S↑↑ m k = begin
  CZ^ m ↑ • S^ k ↑ ↑ ≈⟨ sym (cong (refl' (lemma-^-↑ CZ (toℕ m))) (lemma-cong↑ _ _ (B2.refl' (lemma-^-↑ S (toℕ k))))) ⟩
  CZ ↑ ^ toℕ m • (S ↑ ^ toℕ k) ↑ ≈⟨ cright sym (refl' (lemma-^-↑ (S ↑) (toℕ k))) ⟩
  CZ ↑ ^ toℕ m • (S ↑ ↑ ^ toℕ k) ≈⟨ word-comm (toℕ m) (toℕ k) (axiom (cong↑ comm-CZ-S↑)) ⟩
  (S ↑ ↑ ^ toℕ k) • CZ ↑ ^ toℕ m ≈⟨ cong (refl' (lemma-^-↑ (S ↑) (toℕ k))) (refl' (lemma-^-↑ CZ (toℕ m))) ⟩
  (S ↑ ^ toℕ k) ↑ • CZ^ m ↑ ≈⟨ cleft lemma-cong↑ _ _ (B2.refl' (lemma-^-↑ S (toℕ k))) ⟩
  S^ k ↑ ↑ • CZ^ m ↑ ∎


sa = special-assoc


aux-EX↑-EX-CZ^k↑ : ∀ k -> Ex ↑ • Ex • CZ^ k ↑ ≈ CZ^ k • Ex ↑ • Ex
aux-EX↑-EX-CZ^k↑ k = begin
  Ex ↑ • Ex • CZ^ k ↑ ≈⟨ sym assoc ⟩
  (Ex ↑ • Ex) • CZ^ k ↑ ≈⟨ cright sym (refl' (lemma-^-↑ CZ (toℕ k))) ⟩
  (Ex ↑ • Ex) • CZ ↑ ^ toℕ k ≈⟨ lemma-Induction lemma-[Ex↑-Ex]-CZ↑ (toℕ k) ⟩
  CZ ^ toℕ k • (Ex ↑ • Ex) ≈⟨ refl ⟩
  CZ^ k • Ex ↑ • Ex ∎


aux-CZ⁻¹↑^k-CZ↑^-k : ∀ (k : ℤ ₚ) -> CZ⁻¹ ↑ ^ toℕ k ≈ CZ ↑ ^ toℕ (- k)
aux-CZ⁻¹↑^k-CZ↑^-k k = begin
  CZ⁻¹ ↑ ^ toℕ k ≈⟨ refl' (lemma-^-↑ CZ⁻¹ (toℕ k)) ⟩
  (CZ⁻¹ ^ toℕ k) ↑ ≈⟨ lemma-cong↑ _ _ (aux-CZ⁻¹^k-CZ^-k k) ⟩
  (CZ ^ toℕ (- k)) ↑ ≈⟨ sym (refl' (lemma-^-↑ CZ (toℕ (- k)))) ⟩
  CZ ↑ ^ toℕ (- k) ∎

aux-CZ02⁻ᵏ-CZ02k : ∀ (k : ℤ ₚ) -> CZ02⁻ᵏ (toℕ k) ≈ CZ02k (toℕ (- k))
aux-CZ02⁻ᵏ-CZ02k k = begin
  Ex • CZ⁻¹ ↑ ^ toℕ k • Ex ≈⟨ cright cleft aux-CZ⁻¹↑^k-CZ↑^-k k ⟩
  Ex • CZ ↑ ^ toℕ (- k) • Ex ∎


aux-XC02-CZ^k↑ : ∀ k -> XC02 • CZ^ k ↑ ≈ CZ^ k ↑ • CZ^ (- k) • XC02
aux-XC02-CZ^k↑ k = bbc (Ex ↑ • Ex) (Ex • Ex ↑) claim
  where
  claim : (Ex ↑ • Ex) • (XC02 • CZ^ k ↑) • Ex • Ex ↑ ≈ (Ex ↑ • Ex) • (CZ^ k ↑ • CZ^ (- k) • XC02) • Ex • Ex ↑
  claim = begin
    (Ex ↑ • Ex) • (XC02 • CZ^ k ↑) • Ex • Ex ↑ ≈⟨ sa (□ ^ 2 • □ ^ 2 • □ ^ 2) (□ ^ 3 • □ ^ 3) auto ⟩
    (Ex ↑ • Ex • XC02) • CZ^ k ↑ • Ex • Ex ↑ ≈⟨ cleft by-ex {w = EX.Ex EX.↑ • EX.Ex • EX.XC02} {v = EX.CX EX.↑ • EX.Ex EX.↑ • EX.Ex} (rewrite-EX 100 auto) ⟩
    (CX ↑ • Ex ↑ • Ex) • CZ^ k ↑ • Ex • Ex ↑ ≈⟨ special-assoc (□ ^ 3 • □ ^ 3) (□ • (□ ^ 3) • □ ^ 2) auto ⟩
    CX ↑ • (Ex ↑ • Ex • CZ^ k ↑) • Ex • Ex ↑ ≈⟨ cright cleft aux-EX↑-EX-CZ^k↑ k ⟩
    CX ↑ • (CZ^ k • Ex ↑ • Ex) • Ex • Ex ↑ ≈⟨ sa (□ • □ ^ 3 • □ ^ 2) (□ ^ 2 • □ ^ 4) auto ⟩
    (CX ↑ • CZ^ k) • Ex ↑ • Ex • Ex • Ex ↑ ≈⟨ cright rewrite-swap 100 auto ⟩
    (CX ↑ • CZ^ k) • ε ≈⟨ right-unit ⟩
    (CX ↑ • CZ^ k) ≈⟨ lemma-CX↑-CZ^k (toℕ k) ⟩

    CZ^ k • (CZ02⁻ᵏ (toℕ (k))) • CX ↑ ≈⟨ cright cleft (cright cleft aux-CZ⁻¹↑^k-CZ↑^-k k) ⟩
    CZ^ k • (CZ02k (toℕ (- k))) • CX ↑ ≈⟨ cright cleft lemma-CZ02k-alt (toℕ (- k)) ⟩
    CZ^ k • (Ex ↑ • CZ^ (- k) • Ex ↑) • CX ↑ ≈⟨ sa (□ • □ ^ 3 • □) (□ ^ 3 • □ ^ 2) auto ⟩
    (CZ^ k • Ex ↑ • CZ^ (- k)) • Ex ↑ • CX ↑ ≈⟨ cright rewrite-swap 100 auto ⟩
    (CZ^ k • Ex ↑ • CZ^ (- k)) • Ex • Ex • Ex ↑ • CX ↑ ≈⟨ sa (□ ^ 3 • □ ^ 4) (□ ^ 2 • □ ^ 2 • □ ^ 3) auto ⟩
    (CZ^ k • Ex ↑) • (CZ^ (- k) • Ex) • Ex • Ex ↑ • CX ↑ ≈⟨ cright cleft word-comm (toℕ (- k)) 1 lemma-comm-Ex-CZ-n ⟩
    (CZ^ k • Ex ↑) • (Ex • CZ^ (- k)) • Ex • Ex ↑ • CX ↑ ≈⟨ sa (□ ^ 2 • □ ^ 2 • □) (□ ^ 3 • □ ^ 2) auto ⟩
    (CZ^ k • Ex ↑ • Ex) • CZ^ (- k) • Ex • Ex ↑ • CX ↑ ≈⟨ cong (sym (aux-EX↑-EX-CZ^k↑ k)) (cright rewrite-swap 100 auto) ⟩
    (Ex ↑ • Ex • CZ^ k ↑) • CZ^ (- k) • XC02 • Ex • Ex ↑ ≈⟨ sa (□ ^ 3 • □ ^ 4) (□ ^ 2 • □ ^ 3 • □ ^ 2) auto ⟩
    (Ex ↑ • Ex) • (CZ^ k ↑ • CZ^ (- k) • XC02) • Ex • Ex ↑ ∎

aux-CZ02-H-CZ↑ : ∀ k -> CZ02 • H ↑ ↑ • CZ^ k ↑ ≈ XC'^ (- k) ↑ • CZ^ (- k) • CZ02 • H ↑ ↑ 
aux-CZ02-H-CZ↑ k = begin
  CZ02 • H ↑ ↑ • CZ^ k ↑ ≈⟨ sym assoc ⟩
  (CZ02 • H ↑ ↑) • CZ^ k ↑ ≈⟨ cleft rewrite-powers 1000 auto ⟩
  (H ↑ ↑ • H ↑ ↑ ^ 3 • CZ02 • H ↑ ↑) • CZ^ k ↑ ≈⟨ assoc ⟩
  H ↑ ↑ • XC02 • CZ^ k ↑ ≈⟨ cright aux-XC02-CZ^k↑ k ⟩
  H ↑ ↑ • CZ^ k ↑ • CZ^ (- k) • XC02 ≈⟨ special-assoc (□ ^ 6) (□ ^ 4 • □ ^ 2) auto ⟩
  (H ↑ ↑ • CZ^ k ↑ • CZ^ (- k) • H ↑ ↑ ^ 3) • CZ02 • H ↑ ↑ ≈⟨ cleft cright cright word-comm (toℕ (- k)) 3 (sym (axiom comm-CZ)) ⟩
  (H ↑ ↑ • CZ^ k ↑ • H ↑ ↑ ^ 3 • CZ^ (- k)) • CZ02 • H ↑ ↑ ≈⟨ special-assoc ((□ • □ • □ ^ 3 • □) • □) ((□ • □ ^ 3 • □) • □ ^ 2) auto ⟩
  (H ↑ ↑ • (CZ^ k ↑ • H ↑ ↑ ^ 2) • H ↑ ↑) • CZ^ (- k) • CZ02 • H ↑ ↑ ≈⟨ sym (cleft cright cleft lemma-cong↑ _ _ (L2Q0.lemma-semi-HH↑-CZ^k'' k)) ⟩
  (H ↑ ↑ • (H ↑ ↑ ^ 2 • CZ^ (- k) ↑) • H ↑ ↑) • CZ^ (- k) • CZ02 • H ↑ ↑ ≈⟨ cleft special-assoc (□ • (□ ^ 2 • □) • □) (□ ^ 3 • □ • □) auto ⟩
  XC'^ (- k) ↑ • CZ^ (- k) • CZ02 • H ↑ ↑  ∎


lemma-|||-mhm : ∀ m↑ k m ->
  let
  m↑⁻¹ = (m↑ ⁻¹) .proj₁
  m/m↑ = m .proj₁ * m↑⁻¹
  in
  
  CZ02 • ⟦ m↑ , HS^ k ⟧ₘ₊ ↑ ↑ • CZ • ⟦ m ⟧ₘ ↑ • CZ ↑ ≈ (XC'^ (- m/m↑) ↑ • CZ^ (- m/m↑)) • CZ02 • ⟦ m↑ , HS^ k ⟧ₘ₊ ↑ ↑ • CZ • ⟦ m ⟧ₘ ↑
  
lemma-|||-mhm m↑@(m↑' , nz↑) k  m@(m' , nz) = begin
  CZ02 • ⟦ m↑ , HS^ k ⟧ₘ₊ ↑ ↑ • CZ • ⟦ m ⟧ₘ ↑ • CZ ↑ ≈⟨ cright cright cright lemma-cong↑ _ _ (B2.axiom (semi-M↓CZ m)) ⟩
  CZ02 • ⟦ m↑ , HS^ k ⟧ₘ₊ ↑ ↑ • CZ • (CZ^ m') ↑ • ⟦ m ⟧ₘ ↑ ≈⟨ cright cright cright sym (cleft refl' (lemma-^-↑ CZ (toℕ m'))) ⟩
  CZ02 • ⟦ m↑ , HS^ k ⟧ₘ₊ ↑ ↑ • CZ • (CZ ↑ ^ toℕ m') • ⟦ m ⟧ₘ ↑ ≈⟨ cright cright sym assoc ⟩
  CZ02 • ⟦ m↑ , HS^ k ⟧ₘ₊ ↑ ↑ • (CZ • (CZ ↑ ^ toℕ m')) • ⟦ m ⟧ₘ ↑ ≈⟨ cright cright cleft word-comm 1 (toℕ m') (sym (axiom selinger-c12)) ⟩
  CZ02 • ⟦ m↑ , HS^ k ⟧ₘ₊ ↑ ↑ • ((CZ ↑ ^ toℕ m') • CZ) • ⟦ m ⟧ₘ ↑ ≈⟨ cright special-assoc (□ • □ ^ 2 • □) (□ ^ 2 • □ ^ 2) auto ⟩
  CZ02 • (⟦ m↑ , HS^ k ⟧ₘ₊ ↑ ↑ • (CZ ↑ ^ toℕ m')) • CZ • ⟦ m ⟧ₘ ↑ ≈⟨ cright cleft cright refl' (lemma-^-↑ CZ (toℕ m')) ⟩
  CZ02 • (⟦ m↑ , HS^ k ⟧ₘ₊ ↑ ↑ • (CZ^ m') ↑) • CZ • ⟦ m ⟧ₘ ↑ ≈⟨ cright cleft special-assoc (□ ^ 3 • □) (□ ^ 4) auto ⟩
  CZ02 • (⟦ m↑ ⟧ₘ ↑ ↑ • H ↑ ↑ • S^ k ↑ ↑ • (CZ^ m') ↑) • CZ • ⟦ m ⟧ₘ ↑ ≈⟨ cright cleft cright cright sym (aux-comm-CZ↑-S↑↑ m' k) ⟩
  CZ02 • (⟦ m↑ ⟧ₘ ↑ ↑ • H ↑ ↑ • (CZ^ m') ↑ • S^ k ↑ ↑) • CZ • ⟦ m ⟧ₘ ↑ ≈⟨ cright special-assoc (□ ^ 4 • □) (□ ^ 2 • □ ^ 2 • □) auto ⟩
  CZ02 • (⟦ m↑ ⟧ₘ ↑ ↑ • H ↑ ↑) • (CZ^ m' ↑ • S^ k ↑ ↑) • CZ • ⟦ m ⟧ₘ ↑ ≈⟨ cright cleft lemma-cong↑ _ _ (lemma-cong↑ _ _ (B1.sym (semi-HM' m↑))) ⟩
  CZ02 • (H ↑ ↑ • ⟦ m↑ ⁻¹ ⟧ₘ ↑ ↑) • (CZ^ m' ↑ • S^ k ↑ ↑) • CZ • ⟦ m ⟧ₘ ↑ ≈⟨ special-assoc (□ • □ ^ 2 • □ ^ 2 • □) (□ ^ 2 • □ ^ 2 • □ ^ 2) auto ⟩
  (CZ02 • H ↑ ↑) • (⟦ m↑ ⁻¹ ⟧ₘ ↑ ↑ • CZ^ m' ↑) • S^ k ↑ ↑ • CZ • ⟦ m ⟧ₘ ↑ ≈⟨ cright cleft lemma-cong↑ _ _ (L2Q0.lemma-M↑CZ^k m↑⁻¹ m' ((m↑ ⁻¹) .proj₂))  ⟩
  (CZ02 • H ↑ ↑) • (CZ^ (m' * m↑⁻¹) ↑ • ⟦ m↑ ⁻¹ ⟧ₘ ↑ ↑) • S^ k ↑ ↑ • CZ • ⟦ m ⟧ₘ ↑ ≈⟨ special-assoc (□ ^ 2 • □ ^ 2 • □) (□ ^ 3 • □ ^ 2) auto ⟩
  (CZ02 • H ↑ ↑ • CZ^ (m' * m↑⁻¹) ↑) • ⟦ m↑ ⁻¹ ⟧ₘ ↑ ↑ • S^ k ↑ ↑ • CZ • ⟦ m ⟧ₘ ↑ ≈⟨ cleft aux-CZ02-H-CZ↑ mm ⟩
  (XC'^ (- mm) ↑ • CZ^ (- mm) • CZ02 • H ↑ ↑) • ⟦ m↑ ⁻¹ ⟧ₘ ↑ ↑ • S^ k ↑ ↑ • CZ • ⟦ m ⟧ₘ ↑ ≈⟨ special-assoc (□ ^ 4 • □ ^ 4) (□ ^ 3 • □ ^ 2 • □ ^ 3) auto ⟩
  (XC'^ (- mm) ↑ • CZ^ (- mm) • CZ02) • (H ↑ ↑ • ⟦ m↑ ⁻¹ ⟧ₘ ↑ ↑) • S^ k ↑ ↑ • CZ • ⟦ m ⟧ₘ ↑ ≈⟨ cright cleft sym (lemma-cong↑ _ _ (lemma-cong↑ _ _ (B1.sym (semi-HM' m↑)))) ⟩
  (XC'^ (- mm) ↑ • CZ^ (- mm) • CZ02) • (⟦ m↑ ⟧ₘ ↑ ↑ • H ↑ ↑) • S^ k ↑ ↑ • CZ • ⟦ m ⟧ₘ ↑ ≈⟨ special-assoc (□ ^ 3 • □ ^ 2 • □ ^ 3) (□ ^ 2 • □ • □ ^ 3 • □ ^ 2) auto ⟩
  (XC'^ (- mm) ↑ • CZ^ (- mm)) • CZ02 • ⟦ m↑ , HS^ k ⟧ₘ₊ ↑ ↑ • CZ • ⟦ m ⟧ₘ ↑ ∎
  where
  m↑⁻¹ = (m↑ ⁻¹) .proj₁
  mm = m' * m↑⁻¹


aux-comm-XC02-H↑ : XC02 • H ↑ ≈ H ↑ • XC02
aux-comm-XC02-H↑ = begin
  XC02 • H ↑ ≈⟨ rewrite-swap 100 auto ⟩
  Ex • XC ↑ • H • Ex ≈⟨ general-comm auto ⟩
  Ex • H • XC ↑ • Ex ≈⟨ rewrite-swap 100 auto ⟩
  H ↑ • XC02 ∎

aux-XC02-CX^k↑ : ∀ k -> XC02 • CX^ k ↑ ≈ CX^ k ↑ • XC^ (- k) • XC02
aux-XC02-CX^k↑ k = bbc (H ↑) (H ↑ ^ 3) claim
  where
  claim : H ↑ • (XC02 • CX^ k ↑) • H ↑ ^ 3 ≈ H ↑ • (CX^ k ↑ • XC^ (- k) • XC02) • H ↑ ^ 3
  claim = begin
    H ↑ • (XC02 • CX^ k ↑) • H ↑ ^ 3 ≈⟨ sa (□ • □ ^ 2 • □) (□ ^ 2 • □ ^ 2) auto ⟩
    (H ↑ • XC02) • CX^ k ↑ • H ↑ ^ 3 ≈⟨ cleft rewrite-swap 100 auto ⟩
    (Ex • H • XC ↑ • Ex) • CX^ k ↑ • H ↑ ^ 3 ≈⟨ cleft general-comm auto ⟩
    (Ex • XC ↑ • H • Ex) • CX^ k ↑ • H ↑ ^ 3 ≈⟨ cleft rewrite-swap 100 auto ⟩
    (XC02 • H ↑) • CX^ k ↑ • H ↑ ^ 3 ≈⟨ cright cleft lemma-cong↑ _ _ (aux-CX^-CX'^ k) ⟩
    (XC02 • H ↑) • CX'^ k ↑ • H ↑ ^ 3 ≈⟨ sa (□ ^ 2 • □ ^ 3 • □) (□ • □ ^ 2 • □ ^ 3) auto ⟩
    XC02 • (H ↑ • H ↑ ^ 3) • CZ^ k ↑ • H ↑ • H ↑ ^ 3 ≈⟨ cright cong (rewrite-sym0 100 auto) (cright rewrite-sym0 100 auto) ⟩
    XC02 • ε • CZ^ k ↑ • ε ≈⟨ cright trans left-unit right-unit ⟩
    XC02 • CZ^ k ↑ ≈⟨ aux-XC02-CZ^k↑ k ⟩
    CZ^ k ↑ • CZ^ (- k) • XC02 ≈⟨ cright sym left-unit ⟩
    CZ^ k ↑ • ε • CZ^ (- k) • XC02 ≈⟨ cright cong (rewrite-sym0 100 auto) (cright rewrite-sym0 100 auto) ⟩
    CZ^ k ↑ • (H ↑ • H ↑ ^ 3) • CZ^ (- k) • H ↑ • H ↑ ^ 3 • XC02 ≈⟨ sa (□ • □ ^ 2 • □ ^ 4) (□ • □ • □ ^ 3 • □ ^ 2) auto ⟩
    CZ^ k ↑ • H ↑ • XC'^ (- k) • H ↑ ^ 3 • XC02 ≈⟨ cright cright cleft sym (by-emb' (aux-XC^-XC'^ (- k)) (Em.lemma-f* XC (toℕ (- k))) (cright cleft Em.lemma-f* CZ (toℕ (- k)))) ⟩
    CZ^ k ↑ • H ↑ • XC^ (- k) • H ↑ ^ 3 • XC02 ≈⟨ sym left-unit ⟩
    ε • CZ^ k ↑ • H ↑ • XC^ (- k) • H ↑ ^ 3 • XC02 ≈⟨ cong (rewrite-sym0 100 auto) (cright cright cright word-comm 3 1 (sym aux-comm-XC02-H↑)) ⟩
    (H ↑ • H ↑ ^ 3) • CZ^ k ↑ • H ↑ • XC^ (- k) • XC02 • H ↑ ^ 3 ≈⟨ sa (□ ^ 2 • □ ^ 5) (□ • (□ ^ 3 • □ ^ 2) • □) auto ⟩
    H ↑ • (CX'^ k ↑ • XC^ (- k) • XC02) • H ↑ ^ 3 ≈⟨ cright cleft cleft lemma-cong↑ _ _ (B2.sym (aux-CX^-CX'^ k)) ⟩
    H ↑ • (CX^ k ↑ • XC^ (- k) • XC02) • H ↑ ^ 3 ∎
