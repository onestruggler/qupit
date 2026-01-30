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



module N.BR.Three.Lemmas5 (p-2 : ℕ) (p-prime : Prime (2+ p-2))  where

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
open import N.Ex-Sym4 p-2 p-prime hiding (lemma-Ex-S^ᵏ↑)
--open import N.Ex-Sym5 p-2 p-prime hiding (module L0)
open import N.Ex-Sym2n p-2 p-prime
open import N.Ex-Sym3n p-2 p-prime
open import N.Ex-Sym4n p-2 p-prime
open import N.Ex-Sym4n2 p-2 p-prime
open import N.Ex-Sym4n3 p-2 p-prime
open import N.Ex-Sym4n4 p-2 p-prime

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
open import N.Lemmas4-Sym p-2 p-prime as L4 hiding (lemma-Ex-M-n)
open import N.Lemmas-3Q p-2 p-prime
open import N.Pushing.DH p-2 p-prime
open import N.Duality p-2 p-prime
open import N.BR.Calculations p-2 p-prime
open import N.BR.Two.Lemmas p-2 p-prime hiding (sa)
open import N.BR.Three.Lemmas p-2 p-prime
open import N.BR.Three.Lemmas2 p-2 p-prime
open import N.BR.Three.Lemmas3 p-2 p-prime
open import N.BR.Three.Lemmas4 p-2 p-prime

open PB (3 QRel,_===_)
open PP (3 QRel,_===_)
-- module B2 = PB (2 QRel,_===_)
-- module P2 = PP (2 QRel,_===_)
-- module B1 = PB (1 QRel,_===_)
-- module P1 = PP (1 QRel,_===_)

open Pattern-Assoc
open Lemmas0 1
--module L02 = Lemmas0 2
open Lemmas-2Q 1
module L2Q1 = Lemmas-2Q 1
open Sym0-Rewriting 2
--module Sym01 = Sym0-Rewriting 1
open Rewriting-Powers 2
open Rewriting-Swap 2
open Rewriting-Swap0 2
open Symplectic-GroupLike
open Basis-Change _ (3 QRel,_===_) grouplike
open import N.EX-Rewriting p-2 p-prime
open Rewriting-EX 2
open Homo 2 renaming (lemma-f* to lemma-f*-EX)
open Commuting-Symplectic 1
open import Data.List
open import N.BR.TwoQupit p-2 p-prime
open import N.Embeding-2n p-2 p-prime 1
open import N.EX-Rewriting p-2 p-prime



lemma-CZ02^k-CZ^l↑-CZ : ∀ (k*@(k , nzk) l*@(l , nzl) : ℤ* ₚ) ->
  let
  k⁻¹ = (k* ⁻¹) .proj₁
  l⁻¹ = (l* ⁻¹) .proj₁
  in
  CZ02^ (- k) • H • CZ^ (- l) ↑ • H ↑ • CZ ≈ H • H ↑ • CZ • S^ (- l * k⁻¹) • CX02^ (- k) • S^ (l * k⁻¹) • S^ (- k * l⁻¹) ↑ • CX^ (- l) ↑ • S^ (k * l⁻¹) ↑
  
lemma-CZ02^k-CZ^l↑-CZ k*@(k , nzk) l*@(l , nzl) = bbc (M (k* ⁻¹) • M (l* ⁻¹) ↑) ε claim
  where
  k⁻¹ = (k* ⁻¹) .proj₁
  l⁻¹ = (l* ⁻¹) .proj₁
  aux2 : l * k * (l⁻¹ * l⁻¹) ≡ k * l⁻¹
  aux2 = begin
    l * k * (l⁻¹ * l⁻¹) ≡⟨ Eq.cong (_* (l⁻¹ * l⁻¹)) (*-comm l k) ⟩
    k * l * (l⁻¹ * l⁻¹) ≡⟨ aux-lkkk l* k* ⟩
    k * l⁻¹ ∎
    where
    open ≡-Reasoning

  open SR word-setoid
  claim : (M (k* ⁻¹) • M (l* ⁻¹) ↑) • (CZ02^ (- k) • H • CZ^ (- l) ↑ • H ↑ • CZ) • ε ≈ (M (k* ⁻¹) • M (l* ⁻¹) ↑) • (H • H ↑ • CZ • S^ (- l * k⁻¹) • CX02^ (- k) • S^ (l * k⁻¹) • S^ (- k * l⁻¹) ↑ • CX^ (- l) ↑ • S^ (k * l⁻¹) ↑) • ε
  claim = begin
    (M (k* ⁻¹) • M (l* ⁻¹) ↑) • (CZ02^ (- k) • H • CZ^ (- l) ↑ • H ↑ • CZ) • ε ≈⟨ cong refl right-unit ⟩
    (M (k* ⁻¹) • M (l* ⁻¹) ↑) • (CZ02^ (- k) • H • CZ^ (- l) ↑ • H ↑ • CZ) ≈⟨ sa (□ ^ 2 • □ ^ 2) (□ • □ ^ 2 • □) auto ⟩
    M (k* ⁻¹) • (M (l* ⁻¹) ↑ • CZ02^ (- k)) • H • CZ^ (- l) ↑ • H ↑ • CZ ≈⟨ cright cleft aux-comm-m-CZ02^k (l* ⁻¹) (- k) ⟩
    M (k* ⁻¹) • (CZ02^ (- k) • M (l* ⁻¹) ↑) • H • CZ^ (- l) ↑ • H ↑ • CZ ≈⟨ sa (□ • □ ^ 2 • □ ^ 2) (□ ^ 2 • □ ^ 2 • □) auto ⟩
    (M (k* ⁻¹) • CZ02^ (- k)) • (M (l* ⁻¹) ↑ • H) • CZ^ (- l) ↑ • H ↑ • CZ ≈⟨ cong (lemma-M↓CZ02^k k⁻¹ (- k) ((k* ⁻¹) .proj₂)) (cleft sym (lemma-comm-H-w↑ ( M (l* ⁻¹)))) ⟩
    (CZ02^ (- k * k⁻¹) • M (k* ⁻¹)) • (H • M (l* ⁻¹) ↑) • CZ^ (- l) ↑ • H ↑ • CZ ≈⟨ sa (□ ^ 2 • □ ^ 2 • □ ^ 2) (□ • □ ^ 2 • □ ^ 2 • □) auto ⟩
    CZ02^ (- k * k⁻¹) • (M (k* ⁻¹) • H) • (M (l* ⁻¹) ↑ • CZ^ (- l) ↑) • H ↑ • CZ ≈⟨ cright cong (sym (L02.semi-HM k*)) (cleft lemma-cong↑ _ _ (L2Q0.lemma-M↓CZ^k l⁻¹ (- l) ((l* ⁻¹) .proj₂))) ⟩
    CZ02^ (- k * k⁻¹) • (H • M k*) • (CZ^ (- l * l⁻¹) ↑ • M (l* ⁻¹) ↑) • H ↑ • CZ ≈⟨ cong (refl' (Eq.cong CZ02^ (Eq.trans (Eq.sym (-‿distribˡ-* k k⁻¹)) (Eq.cong -_ (lemma-⁻¹ʳ k {{nztoℕ {y = k} {neq0 = nzk}}}))))) (cright cleft cleft refl' (Eq.cong (\ xx -> CZ^ xx ↑) ((Eq.trans (Eq.sym (-‿distribˡ-* l l⁻¹)) (Eq.cong -_ (lemma-⁻¹ʳ l {{nztoℕ {y = l} {neq0 = nzl}}})))))) ⟩
    CZ02^ (- ₁) • (H • M k*) • (CZ^ (- ₁) ↑ • M (l* ⁻¹) ↑) • H ↑ • CZ ≈⟨ cright sa (□ ^ 2 • □ ^ 2 • □ ^ 2) (□ • □ ^ 2 • □ ^ 2 • □) auto ⟩
    CZ02^ (- ₁) • H • (M k* • CZ^ (- ₁) ↑) • (M (l* ⁻¹) ↑ • H ↑) • CZ ≈⟨ cright cright cong (aux-comm-m-w↑ k* (CZ^ (- ₁))) (cleft lemma-cong↑ _ _ (B2.sym (semi-HM l*))) ⟩
    CZ02^ (- ₁) • H • (CZ^ (- ₁) ↑ • M k*) • (H ↑ • M l* ↑) • CZ ≈⟨ cright cright sa (□ ^ 2 • □ ^ 2 • □) (□ • □ ^ 2 • □ ^ 2) auto ⟩
    CZ02^ (- ₁) • H • CZ^ (- ₁) ↑ • (M k* • H ↑) • M l* ↑ • CZ ≈⟨ cright cright cright cong (aux-comm-m-w↑ k* H) (axiom (semi-M↑CZ l*)) ⟩
    CZ02^ (- ₁) • H • CZ^ (- ₁) ↑ • (H ↑ • M k*) • CZ^ l • M l* ↑ ≈⟨ cright cright cright sa (□ ^ 2 • □ ^ 2) (□ • □ ^ 2 • □) auto ⟩
    CZ02^ (- ₁) • H • CZ^ (- ₁) ↑ • H ↑ • (M k* • CZ^ l) • M l* ↑ ≈⟨ cright cright cright cright (cleft lemma-M↓CZ^k k l nzk) ⟩
    CZ02^ (- ₁) • H • CZ^ (- ₁) ↑ • H ↑ • (CZ^ (l * k) • M k*) • M l* ↑ ≈⟨ sa (□ • □ • □ • □ • □ ^ 2 • □) (□ ^ 5 • □ ^ 2) auto ⟩

    
    (CZ02^ (- ₁) • H • CZ^ (- ₁) ↑ • H ↑ • CZ^ (l * k)) • M k* • M l* ↑ ≈⟨ cleft lemma-CZ02⁻¹-CZ⁻¹↑-CZ^k (l * k) ⟩
    (H • H ↑ • CZ^ (l * k) • S^ (- (l * k)) • CX02^ (- ₁) • S^ (l * k) • (S^ (- (l * k)) ↑ • CX^ (- ₁) ↑ • S^ (l * k) ↑)) • M k* • M l* ↑ ≈⟨ sa (□ ^ 9 • □ ^ 2) (□ ^ 6 • (□ ^ 3 • □) • □) auto ⟩
    (H • H ↑ • CZ^ (l * k) • S^ (- (l * k)) • CX02^ (- ₁) • S^ (l * k)) • ((S^ (- (l * k)) ↑ • CX^ (- ₁) ↑ • S^ (l * k) ↑) • M k*) • M l* ↑ ≈⟨ cright cleft sym (aux-comm-m-w↑ k* (S^ (- (l * k)) • CX^ (- ₁) • S^ (l * k))) ⟩
    (H • H ↑ • CZ^ (l * k) • S^ (- (l * k)) • CX02^ (- ₁) • S^ (l * k)) • (M k* • (S^ (- (l * k)) ↑ • CX^ (- ₁) ↑ • S^ (l * k) ↑)) • M l* ↑ ≈⟨ sa ((□ ^ 6 • (□ ^ 4) • □)) (□ ^ 5 • □ ^ 2 • □ ^ 2 • □ ^ 2) auto ⟩
    (H • H ↑ • CZ^ (l * k) • S^ (- (l * k)) • CX02^ (- ₁)) • (S^ (l * k) • M k*) • (S^ (- (l * k)) ↑ • CX^ (- ₁) ↑) • S^ (l * k) ↑ • M l* ↑ ≈⟨ cright cong (L02.lemma-S^kM k (l * k) nzk) (cright lemma-cong↑ _ _ (lemma-S^kM l (l * k) nzl)) ⟩
    (H • H ↑ • CZ^ (l * k) • S^ (- (l * k)) • CX02^ (- ₁)) • (M k* • S^ (l * k * (k⁻¹ * k⁻¹))) • (S^ (- (l * k)) ↑ • CX^ (- ₁) ↑) • M l* ↑ • S^ (l * k * (l⁻¹ * l⁻¹)) ↑ ≈⟨ cright cong (cright refl' (Eq.cong S^ (aux-lkkk k* l*))) (cright cright refl' (Eq.cong (\ xx -> S^ xx ↑) aux2)) ⟩
    (H • H ↑ • CZ^ (l * k) • S^ (- (l * k)) • CX02^ (- ₁)) • (M k* • S^ (l * k⁻¹)) • (S^ (- (l * k)) ↑ • CX^ (- ₁) ↑) • M l* ↑ • S^ (k * l⁻¹) ↑ ≈⟨ sa (□ ^ 5 • □ ^ 2 • □ ^ 2 • □ ^ 2) (□ ^ 4 • □ ^ 2 • □ • □ • □ ^ 2 • □) auto ⟩
    (H • H ↑ • CZ^ (l * k) • S^ (- (l * k))) • (CX02^ (- ₁) • M k*) • S^ (l * k⁻¹) • S^ (- (l * k)) ↑ • (CX^ (- ₁) ↑ • M l* ↑) • S^ (k * l⁻¹) ↑ ≈⟨ cright cong (aux-CX02^kM↓ k* (- ₁)) (cright cright cleft lemma-cong↑ _ _ (aux-CX^kM↓ (- ₁) l*)) ⟩
    (H • H ↑ • CZ^ (l * k) • S^ (- (l * k))) • (M k* • CX02^ (- ₁ * k)) • S^ (l * k⁻¹) • S^ (- (l * k)) ↑ • (M l* ↑ • CX^ (- ₁ * l) ↑) • S^ (k * l⁻¹) ↑ ≈⟨ cright cong (cright refl' (Eq.cong CX02^ (-1*x≈-x k))) (cright cright cleft cright refl' (Eq.cong (\ xx -> CX^ xx ↑) (-1*x≈-x l))) ⟩
    (H • H ↑ • CZ^ (l * k) • S^ (- (l * k))) • (M k* • CX02^ (- k)) • S^ (l * k⁻¹) • S^ (- (l * k)) ↑ • (M l* ↑ • CX^ (- l) ↑) • S^ (k * l⁻¹) ↑ ≈⟨ sa (□ ^ 4 • □ ^ 2 • □ • □ • □ ^ 2 • □) (□ ^ 3 • □ ^ 2 • □ • □ • □ ^ 2 • □ ^ 2) auto ⟩
    (H • H ↑ • CZ^ (l * k)) • (S^ (- (l * k)) • M k*) • CX02^ (- k) • S^ (l * k⁻¹) • (S^ (- (l * k)) ↑ • M l* ↑) • CX^ (- l) ↑ • S^ (k * l⁻¹) ↑ ≈⟨ cright cong (L02.lemma-S^kM k (- (l * k)) nzk) (cright cright cleft lemma-cong↑ _ _ (lemma-S^kM l (- (l * k)) nzl)) ⟩
    (H • H ↑ • CZ^ (l * k)) • (M k* • S^ (- (l * k) * (k⁻¹ * k⁻¹))) • CX02^ (- k) • S^ (l * k⁻¹) • (M l* ↑ • S^ (- (l * k) * (l⁻¹ * l⁻¹)) ↑) • CX^ (- l) ↑ • S^ (k * l⁻¹) ↑ ≈⟨ cright cong (cright refl' (Eq.cong S^ (Eq.trans (Eq.sym (-‿distribˡ-* (l * k) (k⁻¹ * k⁻¹))) (Eq.cong -_ (aux-lkkk k* l*))))) (cright cright cleft cright refl' (Eq.cong (\ xx -> S^ xx ↑) (Eq.trans (Eq.sym (-‿distribˡ-* (l * k) (l⁻¹ * l⁻¹))) (Eq.cong -_ aux2)))) ⟩
    (H • H ↑ • CZ^ (l * k)) • (M k* • S^ (- (l * k⁻¹))) • CX02^ (- k) • S^ (l * k⁻¹) • (M l* ↑ • S^ (- (k * l⁻¹)) ↑) • CX^ (- l) ↑ • S^ (k * l⁻¹) ↑ ≈⟨ sa ((□ ^ 3 • □ ^ 2 • □ • □ • □ ^ 2 • □ ^ 2)) (□ ^ 2 • □ ^ 2 • □ • □ • □ ^ 2 • □ ^ 3) auto ⟩
    (H • H ↑) • (CZ^ (l * k) • M k*) • S^ (- (l * k⁻¹)) • CX02^ (- k) • (S^ (l * k⁻¹) • M l* ↑) • S^ (- (k * l⁻¹)) ↑ • CX^ (- l) ↑ • S^ (k * l⁻¹) ↑ ≈⟨ cright cong (sym (L2Q1.lemma-M↓CZ^k k l nzk)) (cright cright cleft lemma-comm-Sᵏ-w↑ (toℕ (l * k⁻¹)) (M l*)) ⟩
    (H • H ↑) • (M k* • CZ^ l) • S^ (- (l * k⁻¹)) • CX02^ (- k) • (M l* ↑ • S^ (l * k⁻¹)) • S^ (- (k * l⁻¹)) ↑ • CX^ (- l) ↑ • S^ (k * l⁻¹) ↑ ≈⟨ cright cright cright sa (□ • □ ^ 2 • □ ^ 3) (□ ^ 2 • □ ^ 4) auto ⟩
    (H • H ↑) • (M k* • CZ^ l) • S^ (- (l * k⁻¹)) • (CX02^ (- k) • M l* ↑) • S^ (l * k⁻¹) • S^ (- (k * l⁻¹)) ↑ • CX^ (- l) ↑ • S^ (k * l⁻¹) ↑ ≈⟨ cright cright cright cleft sym (aux-comm-m-CX02^k l* (- k)) ⟩
    (H • H ↑) • (M k* • CZ^ l) • S^ (- (l * k⁻¹)) • (M l* ↑ • CX02^ (- k)) • S^ (l * k⁻¹) • S^ (- (k * l⁻¹)) ↑ • CX^ (- l) ↑ • S^ (k * l⁻¹) ↑ ≈⟨ sa (□ ^ 2 • □ ^ 2 • □ • □ ^ 2 • □) (□ • □ ^ 2 • □ • □ • □ ^ 2 • □) auto ⟩
    H • (H ↑ • M k*) • CZ^ l • S^ (- (l * k⁻¹)) • (M l* ↑ • CX02^ (- k)) • S^ (l * k⁻¹) • S^ (- (k * l⁻¹)) ↑ • CX^ (- l) ↑ • S^ (k * l⁻¹) ↑ ≈⟨ cright cong (sym (aux-comm-m-w↑ k* H)) refl ⟩
    H • (M k* • H ↑) • CZ^ l • S^ (- (l * k⁻¹)) • (M l* ↑ • CX02^ (- k)) • S^ (l * k⁻¹) • S^ (- (k * l⁻¹)) ↑ • CX^ (- l) ↑ • S^ (k * l⁻¹) ↑ ≈⟨ sa (□ • □ ^ 2 • □ • □ • □ ^ 2 • □) (□ ^ 2 • □ • □ • □ ^ 2 • □ • □) auto ⟩
    (H • M k*) • H ↑ • CZ^ l • (S^ (- (l * k⁻¹)) • M l* ↑) • CX02^ (- k) • S^ (l * k⁻¹) • S^ (- (k * l⁻¹)) ↑ • CX^ (- l) ↑ • S^ (k * l⁻¹) ↑ ≈⟨ cong (L02.semi-HM k*) (cright cright cleft lemma-comm-Sᵏ-w↑ (toℕ (- (l * k⁻¹))) (M l*)) ⟩
    (M (k* ⁻¹) • H) • H ↑ • CZ^ l • (M l* ↑ • S^ (- (l * k⁻¹))) • CX02^ (- k) • S^ (l * k⁻¹) • S^ (- (k * l⁻¹)) ↑ • CX^ (- l) ↑ • S^ (k * l⁻¹) ↑ ≈⟨ cright cright sa (□ • □ ^ 2 • □ ) (□ ^ 2 • □ ^ 2) auto ⟩
    (M (k* ⁻¹) • H) • H ↑ • (CZ^ l • M l* ↑) • S^ (- (l * k⁻¹)) • CX02^ (- k) • S^ (l * k⁻¹) • S^ (- (k * l⁻¹)) ↑ • CX^ (- l) ↑ • S^ (k * l⁻¹) ↑ ≈⟨ cright cright cleft sym (axiom (semi-M↑CZ l*)) ⟩
    (M (k* ⁻¹) • H) • H ↑ • (M l* ↑ • CZ) • S^ (- (l * k⁻¹)) • CX02^ (- k) • S^ (l * k⁻¹) • S^ (- (k * l⁻¹)) ↑ • CX^ (- l) ↑ • S^ (k * l⁻¹) ↑ ≈⟨ cright sa (□ • □ ^ 2 • □) (□ ^ 2 • □ ^ 2) auto ⟩
    (M (k* ⁻¹) • H) • (H ↑ • M l* ↑) • CZ • S^ (- (l * k⁻¹)) • CX02^ (- k) • S^ (l * k⁻¹) • S^ (- (k * l⁻¹)) ↑ • CX^ (- l) ↑ • S^ (k * l⁻¹) ↑ ≈⟨ cright cleft lemma-cong↑ _ _ (semi-HM l*) ⟩
    (M (k* ⁻¹) • H) • (M (l* ⁻¹) ↑ • H ↑) • CZ • S^ (- (l * k⁻¹)) • CX02^ (- k) • S^ (l * k⁻¹) • S^ (- (k * l⁻¹)) ↑ • CX^ (- l) ↑ • S^ (k * l⁻¹) ↑ ≈⟨ sa (□ ^ 2 • □ ^ 2 • □) (□ • □ ^ 2 • □ ^ 2) auto ⟩
    M (k* ⁻¹) • (H • M (l* ⁻¹) ↑) • H ↑ • CZ • S^ (- (l * k⁻¹)) • CX02^ (- k) • S^ (l * k⁻¹) • S^ (- (k * l⁻¹)) ↑ • CX^ (- l) ↑ • S^ (k * l⁻¹) ↑ ≈⟨ cright cleft lemma-comm-H-w↑ ( M (l* ⁻¹)) ⟩
    M (k* ⁻¹) • (M (l* ⁻¹) ↑ • H) • H ↑ • CZ • S^ (- (l * k⁻¹)) • CX02^ (- k) • S^ (l * k⁻¹) • S^ (- (k * l⁻¹)) ↑ • CX^ (- l) ↑ • S^ (k * l⁻¹) ↑ ≈⟨ sa (□ • □ ^ 2 • □) (□ ^ 2 • □ ^ 2) auto ⟩
    (M (k* ⁻¹) • M (l* ⁻¹) ↑) • H • H ↑ • CZ • S^ (- (l * k⁻¹)) • CX02^ (- k) • S^ (l * k⁻¹) • S^ (- (k * l⁻¹)) ↑ • CX^ (- l) ↑ • S^ (k * l⁻¹) ↑ ≈⟨ cright cright cright cright cong (refl' (Eq.cong S^ (-‿distribˡ-* l k⁻¹))) (cright cright cleft refl' (Eq.cong (\ xx -> S^ xx ↑) (-‿distribˡ-* k l⁻¹))) ⟩
    (M (k* ⁻¹) • M (l* ⁻¹) ↑) • H • H ↑ • CZ • S^ (- l * k⁻¹) • CX02^ (- k) • S^ (l * k⁻¹) • S^ (- k * l⁻¹) ↑ • CX^ (- l) ↑ • S^ (k * l⁻¹) ↑ ≈⟨ sym (cong refl right-unit) ⟩
    (M (k* ⁻¹) • M (l* ⁻¹) ↑) • (H • H ↑ • CZ • S^ (- l * k⁻¹) • CX02^ (- k) • S^ (l * k⁻¹) • S^ (- k * l⁻¹) ↑ • CX^ (- l) ↑ • S^ (k * l⁻¹) ↑) • ε ∎

