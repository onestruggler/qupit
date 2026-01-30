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



module N.BR.Three.DD-CZ (p-2 : ℕ) (p-prime : Prime (2+ p-2))  where

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
open import N.Lemmas-2Qupit-Sym3 p-2 p-prime
open import N.NF2-Sym p-2 p-prime
--open Lemmas-2Q 2

open import N.NF1 p-2 p-prime
open import N.Ex-Sym p-2 p-prime
open import N.Ex-Sym1 p-2 p-prime
open import N.Ex-Sym2 p-2 p-prime
open import N.Ex-Sym3 p-2 p-prime
open import N.Ex-Sym4 p-2 p-prime hiding (lemma-Ex-S^ᵏ ; lemma-Ex-S^ᵏ↑)
open import N.Ex-Sym5 p-2 p-prime hiding (module L0)
open import N.Ex-Sym2n p-2 p-prime
open import N.Ex-Sym3n p-2 p-prime
open import N.Ex-Sym4n p-2 p-prime
open import N.Ex-Sym4n2 p-2 p-prime
open import N.Ex-Sym4n3 p-2 p-prime


open import N.Lemma-Comm-n p-2 p-prime 0
import N.Lemma-Comm-n p-2 p-prime 1 as LCn1
open import N.Completeness1-Sym p-2 p-prime renaming (module Completeness to Cp1)
open Lemmas0a
open Lemmas0a1
open Lemmas0b
open Lemmas0c
open Lemmas-Sym
open Duality

open import N.Completeness1-Sym p-2 p-prime renaming (module Completeness to CP1) using ()
open import N.Coset2-Update-Sym p-2 p-prime renaming (module Completeness to CP2) using ()
open import N.Lemmas4-Sym p-2 p-prime as L4
open import N.Lemmas-3Q p-2 p-prime
open import N.Pushing.DH p-2 p-prime
open import N.Duality p-2 p-prime
open import N.BR.Calculations p-2 p-prime
open import N.BR.Three.Lemmas p-2 p-prime
open import N.BR.Three.Lemmas2 p-2 p-prime
open import N.BR.Three.Lemmas3 p-2 p-prime hiding (module L02)
open import N.BR.Three.Lemmas4 p-2 p-prime
open import N.BR.Three.Lemmas5 p-2 p-prime
open import N.Embeding-2n p-2 p-prime 1

open PB (3 QRel,_===_)
open PP (3 QRel,_===_)
-- module B2 = PB (2 QRel,_===_)
-- module P2 = PP (2 QRel,_===_)
-- module B1 = PB (1 QRel,_===_)
-- module P1 = PP (1 QRel,_===_)
open SR word-setoid
open Pattern-Assoc
open Lemmas0 1
module L02 = Lemmas0 2
open Lemmas-2Q 1
--module L2Q0 = Lemmas-2Q 0
open Sym0-Rewriting 2
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
open import N.BR.Two.Lemmas p-2 p-prime hiding (sa)
open import N.BR.Two.D p-2 p-prime hiding (dir-of)
--open import N.BR.TwoQupit p-2 p-prime



aux-Ex-D↑ : ∀ b (nz : b ≢ ₀) -> let b⁻¹ = ((b , nz) ⁻¹) .proj₁ in

  Ex • [ ₀ , b ]ᵈ ↑ • CZ ≈ CZ ↑ • Ex • [ ₀ , b ]ᵈ ↑

aux-Ex-D↑ b@₀ nz = ⊥-elim (nz auto)
aux-Ex-D↑ b@(₁₊ _) nz = begin
  Ex • [ ₀ , b ]ᵈ ↑ • CZ ≈⟨ cright assoc ⟩
  Ex • Ex ↑ • CZ^ (- b) ↑ • CZ ≈⟨ cright cright cleft sym (refl' (lemma-^-↑ CZ (toℕ (- b)))) ⟩
  Ex • Ex ↑ • CZ ↑ ^ toℕ (- b) • CZ ≈⟨ cright cright word-comm (toℕ (- b)) 1 (axiom selinger-c12) ⟩
  Ex • Ex ↑ • CZ • CZ ↑ ^ toℕ (- b) ≈⟨ sa (□ ^ 4) (□ ^ 3 • □) auto ⟩
  (Ex • Ex ↑ • CZ) • CZ ↑ ^ toℕ (- b) ≈⟨ cleft lemma-Ex-Ex↑-CZ ⟩
  (CZ ↑ • Ex • Ex ↑) • CZ ↑ ^ toℕ (- b) ≈⟨ cright (refl' (lemma-^-↑ CZ (toℕ (- b)))) ⟩
  (CZ ↑ • Ex • Ex ↑) • CZ^ (- b) ↑ ≈⟨ sa (□ ^ 3 • □) (□ • □ • □ ^ 2) auto ⟩
  CZ ↑ • Ex • [ ₀ , b ]ᵈ ↑ ∎


aux-D-Ex↑-CZ^k : ∀ k b (nz : b ≢ ₀) -> let b⁻¹ = ((b , nz) ⁻¹) .proj₁ in

  [ ₀ , b ]ᵈ • Ex ↑ • CZ^ k ≈ CZ^ k ↑ • [ ₀ , b ]ᵈ • Ex ↑

aux-D-Ex↑-CZ^k k b@₀ nz = ⊥-elim (nz auto)
aux-D-Ex↑-CZ^k k b@(₁₊ _) nz = begin
  [ ₀ , b ]ᵈ • Ex ↑ • CZ^ k ≈⟨ cleft aux-dd (₀ , b) ⟩
  [ ₀ , b ]ᵈ' • Ex ↑ • CZ^ k ≈⟨ sa (□ ^ 2 • □ ^ 2) (□ • □ ^ 2 • □) auto ⟩
  (CZ^ (- b)) • (Ex • Ex ↑) • CZ^ k ≈⟨ cright lemma-Ex-Ex↑-CZ^k k ⟩
  (CZ^ (- b)) • CZ^ k ↑ • (Ex • Ex ↑) ≈⟨ sa (□ ^ 4) (□ ^ 2 • □ ^ 2) auto ⟩
  (CZ^ (- b) • CZ^ k ↑) • (Ex • Ex ↑) ≈⟨ cleft (cright refl' (Eq.sym (lemma-^-↑ CZ (toℕ k)))) ⟩
  (CZ^ (- b) • CZ ↑ ^ toℕ k) • (Ex • Ex ↑) ≈⟨ cleft word-comm (toℕ (- b)) (toℕ k) (sym (axiom selinger-c12)) ⟩
  (CZ ↑ ^ (toℕ k) • CZ^ (- b)) • (Ex • Ex ↑) ≈⟨ cleft cleft refl' (lemma-^-↑ CZ (toℕ k)) ⟩
  (CZ^ k ↑ • CZ^ (- b)) • (Ex • Ex ↑) ≈⟨ assoc ⟩
  CZ^ (k) ↑ • CZ^ (- b) • (Ex • Ex ↑) ≈⟨ cright sym assoc ⟩
  CZ^ (k) ↑ • [ ₀ , b ]ᵈ' • Ex ↑ ≈⟨ cright cleft sym (aux-dd (₀ , b)) ⟩
  CZ^ (k) ↑ • [ ₀ , b ]ᵈ • Ex ↑ ∎


aux-swap-DD : ∀ b d ->  Ex ↑ • ([ ₀ , b ]ᵈ • [ ₀ , d ]ᵈ ↑) • Ex ≈ [ ₀ , d ]ᵈ • [ ₀ , b ]ᵈ ↑
aux-swap-DD b d = begin
  Ex ↑ • ([ ₀ , b ]ᵈ • [ ₀ , d ]ᵈ ↑) • Ex ≈⟨ refl ⟩
  Ex ↑ • ((Ex • CZ^ (- b)) • (Ex • CZ^ (- d)) ↑) • Ex ≈⟨ sa (□ • (□ ^ 2 • □ ^ 2) • □) (□ ^ 6) auto ⟩
  Ex ↑ • Ex • CZ^ (- b) • Ex ↑ • CZ^ (- d) ↑ • Ex ≈⟨ cright cright sym assoc ⟩
  Ex ↑ • Ex • (CZ^ (- b) • Ex ↑) • CZ^ (- d) ↑ • Ex ≈⟨ cright cright cleft sym (aux-Ex↑-CZ02^k (- b)) ⟩
  Ex ↑ • Ex • (Ex ↑ • CZ02^ (- b)) • CZ^ (- d) ↑ • Ex ≈⟨ sa (□ • □ • □ ^ 2 • □ ^ 2) (□ ^ 3 • □ ^ 3) auto ⟩
  (Ex ↑ • Ex • Ex ↑) • CZ02^ (- b) • CZ^ (- d) ↑ • Ex ≈⟨ cleft lemma-yang-baxter ⟩
  (Ex • Ex ↑ • Ex) • CZ02^ (- b) • CZ^ (- d) ↑ • Ex ≈⟨ sa (□ ^ 3 • □ ^ 3 • □ ^ 2) (□ ^ 2 • □ ^ 2 • □ ^ 4) auto ⟩
  (Ex • Ex ↑) • (Ex • Ex) • CZ^ (- b) ↑ • Ex • CZ^ (- d) ↑ • Ex ≈⟨ cright cleft lemma-order-Ex-n ⟩
  (Ex • Ex ↑) • ε • CZ^ (- b) ↑ • Ex • CZ^ (- d) ↑ • Ex ≈⟨ cright left-unit ⟩
  (Ex • Ex ↑) • CZ^ (- b) ↑ • Ex • CZ^ (- d) ↑ • Ex ≈⟨ refl ⟩
  (Ex • Ex ↑) • CZ^ (- b) ↑ • CZ02^ (- d) ≈⟨ cright sym (aux-comm-CZ02^l-CZ^k↑ (- d) (- b)) ⟩
  (Ex • Ex ↑) • CZ02^ (- d) • CZ^ (- b) ↑ ≈⟨ sym (sa (□ • □ ^ 2 • □) (□ ^ 2 • □ ^ 2) auto) ⟩
  Ex • (Ex ↑ • CZ02^ (- d)) • CZ^ (- b) ↑ ≈⟨ cright cleft aux-Ex↑-CZ02^k (- d) ⟩
  Ex • (CZ^ (- d) • Ex ↑) • CZ^ (- b) ↑ ≈⟨ sa (□ • □ ^ 2 • □) (□ ^ 2 • □ ^ 2) auto ⟩
  (Ex • CZ^ (- d)) • Ex ↑ • CZ^ (- b) ↑ ≈⟨ refl ⟩
  [ ₀ , d ]ᵈ • [ ₀ , b ]ᵈ ↑ ∎


lemma-swap-DD : ∀ d1 d2 -> Ex ↑ • ([ d1 ∷ d2 ∷ [] ]ᵛᵈ) • Ex ≈ [ d2 ∷ d1 ∷ [] ]ᵛᵈ
lemma-swap-DD d1@(₀ , b) d2@(₀ , d) = begin
  Ex ↑ • ([ d1 ∷ d2 ∷ [] ]ᵛᵈ) • Ex ≈⟨ cright cleft cong refl right-unit ⟩
  Ex ↑ • ([ d1 ]ᵈ • [ d2 ]ᵈ ↑) • Ex ≈⟨ aux-swap-DD b d ⟩
  [ ₀ , d ]ᵈ • [ ₀ , b ]ᵈ ↑ ≈⟨ cong refl (sym right-unit) ⟩
  [ d2 ∷ d1 ∷ [] ]ᵛᵈ ∎

lemma-swap-DD d1@(a@(₁₊ _) , b) d2@(₀ , d) = begin
  Ex ↑ • ([ d1 ∷ d2 ∷ [] ]ᵛᵈ) • Ex ≈⟨ cright cleft cong refl right-unit ⟩
  Ex ↑ • ([ d1 ]ᵈ • [ d2 ]ᵈ ↑) • Ex ≈⟨ cright cleft sa (□ ^ 4 • □) (□ • □ • □ ^ 2 • □) auto ⟩
  Ex ↑ • (Ex • CZ^ (- a) • (H • S^ -b/a) • [ d2 ]ᵈ ↑) • Ex ≈⟨ cright cleft cright cright comm-hs-w↑ -b/a [ d2 ]ᵈ ⟩
  Ex ↑ • (Ex • CZ^ (- a) • [ d2 ]ᵈ ↑ • (H • S^ -b/a)) • Ex ≈⟨ cright sa (□ ^ 4 • □) (□ ^ 3 • □ ^ 2) auto ⟩
  Ex ↑ • (Ex • CZ^ (- a) • [ d2 ]ᵈ ↑) • (H • S^ -b/a) • Ex ≈⟨ cright cright sym left-unit ⟩
  Ex ↑ • (Ex • CZ^ (- a) • [ d2 ]ᵈ ↑) • ε • (H • S^ -b/a) • Ex ≈⟨ cright cright cleft rewrite-swap 100 auto ⟩
  Ex ↑ • (Ex • CZ^ (- a) • [ d2 ]ᵈ ↑) • (Ex • Ex) • (H • S^ -b/a) • Ex ≈⟨ sa (□ • □ ^ 3 • □ ^ 2 • □) ((□ • (□ ^ 2 • □) • □) • □ ^ 2) auto ⟩
  (Ex ↑ • ((Ex • CZ^ (- a)) • [ d2 ]ᵈ ↑) • Ex) • Ex • (H • S^ -b/a) • Ex ≈⟨ cleft aux-swap-DD a d ⟩
  (([ d2 ]ᵈ • (Ex • CZ^ (- a)) ↑)) • Ex • (H • S^ -b/a) • Ex ≈⟨ cright sa (□ • □ ^ 2 • □) (□ ^ 2 • □ ^ 2) auto ⟩
  (([ d2 ]ᵈ • (Ex • CZ^ (- a)) ↑)) • (Ex • H) • S^ -b/a • Ex ≈⟨ cright cong (rewrite-swap 100 auto) (sym (lemma-Ex-S^ᵏ↑ 1 -b/a)) ⟩
  (([ d2 ]ᵈ • (Ex • CZ^ (- a)) ↑)) • (H ↑ • Ex) • Ex • S^ -b/a ↑ ≈⟨ sym (cright sa (□ • □ ^ 2 • □) (□ ^ 2 • □ ^ 2) auto) ⟩
  (([ d2 ]ᵈ • (Ex • CZ^ (- a)) ↑)) • H ↑ • (Ex • Ex) • S^ -b/a ↑ ≈⟨ cright cright cleft rewrite-swap 100 auto ⟩
  (([ d2 ]ᵈ • (Ex • CZ^ (- a)) ↑)) • H ↑ • ε • S^ -b/a ↑ ≈⟨ cright cright left-unit ⟩
  (([ d2 ]ᵈ • (Ex • CZ^ (- a)) ↑)) • H ↑ • S^ -b/a ↑ ≈⟨ sa (□ ^ 3 • □ ^ 2) (□ • □ ^ 4) auto ⟩
  [ d2 ]ᵈ • Ex ↑ • CZ^ (- a) ↑ • H ↑ • S^ -b/a ↑ ≈⟨ refl ⟩
  [ ₀ , d ]ᵈ • [ a , b ]ᵈ ↑ ≈⟨ cong refl (sym right-unit) ⟩
  [ d2 ∷ d1 ∷ [] ]ᵛᵈ ∎
  where
  a⁻¹ = ((a , λ ()) ⁻¹) .proj₁
  -b/a = - b * a⁻¹


lemma-swap-DD d1@(₀ , b) d2@(c@(₁₊ _) , d) = begin
  Ex ↑ • ([ d1 ∷ d2 ∷ [] ]ᵛᵈ) • Ex ≈⟨ cright cleft cong refl right-unit ⟩
  Ex ↑ • ([ d1 ]ᵈ • [ d2 ]ᵈ ↑) • Ex ≈⟨ cright sa (□ ^ 5 • □) (□ ^ 3 • □ ^ 2 • □) auto ⟩
  Ex ↑ • ([ d1 ]ᵈ • (Ex • CZ^ (- c)) ↑) • (H • S^ -d/c) ↑ • Ex ≈⟨ cright cright sym left-unit ⟩
  Ex ↑ • ([ d1 ]ᵈ • (Ex • CZ^ (- c)) ↑) • ε • (H • S^ -d/c) ↑ • Ex ≈⟨ cright cright (cleft rewrite-swap 100 auto) ⟩
  Ex ↑ • ([ d1 ]ᵈ • (Ex • CZ^ (- c)) ↑) • (Ex • Ex) • (H • S^ -d/c) ↑ • Ex ≈⟨ sa (□ • □ ^ 3 • □ ^ 2 • □ ^ 2 • □) ((□ • (□ ^ 3) • □) • □ ^ 2 • □ ^ 2) auto ⟩
  (Ex ↑ • ([ d1 ]ᵈ • (Ex • CZ^ (- c)) ↑) • Ex) • (Ex • H ↑) • S^ -d/c ↑ • Ex ≈⟨ cong (aux-swap-DD b c) (cong (rewrite-swap 100 auto) (sym (lemma-Ex-S^ᵏ 1 -d/c))) ⟩
  (((Ex • CZ^ (- c)) • [ d1 ]ᵈ ↑)) • (H • Ex) • Ex • S^ -d/c ≈⟨ cright sym (sa (□ • □ ^ 2 • □) (□ ^ 2 • □ ^ 2) auto) ⟩
  (((Ex • CZ^ (- c)) • [ d1 ]ᵈ ↑)) • H • (Ex • Ex) • S^ -d/c ≈⟨ cright cright trans (cleft rewrite-swap 100 auto) left-unit ⟩
  (((Ex • CZ^ (- c)) • [ d1 ]ᵈ ↑)) • H • S^ -d/c ≈⟨ assoc ⟩
  (Ex • CZ^ (- c)) • [ d1 ]ᵈ ↑ • H • S^ -d/c ≈⟨ cright sym (comm-hs-w↑ -d/c [ d1 ]ᵈ) ⟩
  (Ex • CZ^ (- c)) • (H • S^ -d/c) • [ d1 ]ᵈ ↑ ≈⟨ sa (□ ^ 2 • □ ^ 2 • □) (□ ^ 4 • □) auto ⟩
  (Ex • CZ^ (- c) • H • S^ -d/c) • [ d1 ]ᵈ ↑ ≈⟨ refl ⟩
  [ c , d ]ᵈ • [ ₀ , b ]ᵈ ↑ ≈⟨ cong refl (sym right-unit) ⟩
  [ d2 ∷ d1 ∷ [] ]ᵛᵈ ∎
  where
  c⁻¹ = ((c , λ ()) ⁻¹) .proj₁
  -d/c = - d * c⁻¹


lemma-swap-DD d1@(a@(₁₊ _) , b) d2@(c@(₁₊ _) , d) = begin
  Ex ↑ • ([ d1 ∷ d2 ∷ [] ]ᵛᵈ) • Ex ≈⟨ cright cleft cong refl right-unit ⟩
  Ex ↑ • ([ d1 ]ᵈ • [ d2 ]ᵈ ↑) • Ex ≈⟨ refl ⟩
  Ex ↑ • ([ d1 ]ᵈ • [ d2 ]ᵈ ↑) • Ex ≈⟨ cright sa (□ ^ 5 • □) (□ ^ 3 • □ ^ 2 • □) auto ⟩
  Ex ↑ • ([ d1 ]ᵈ • (Ex • CZ^ (- c)) ↑) • (H • S^ -d/c) ↑ • Ex ≈⟨ cright cright sym left-unit ⟩
  Ex ↑ • ([ d1 ]ᵈ • (Ex • CZ^ (- c)) ↑) • ε • (H • S^ -d/c) ↑ • Ex ≈⟨ cright cright (cleft rewrite-swap 100 auto) ⟩
  Ex ↑ • ([ d1 ]ᵈ • (Ex • CZ^ (- c)) ↑) • (Ex • Ex) • (H • S^ -d/c) ↑ • Ex ≈⟨ sa (□ • □ ^ 3 • □ ^ 2 • □ ^ 2 • □) ((□ • (□ ^ 3) • □) • □ ^ 2 • □ ^ 2) auto ⟩
  (Ex ↑ • ([ d1 ]ᵈ • (Ex • CZ^ (- c)) ↑) • Ex) • (Ex • H ↑) • S^ -d/c ↑ • Ex ≈⟨ cleft cright cleft cright sym right-unit ⟩
  (Ex ↑ • ([ d1 ]ᵈ • (Ex • CZ^ (- c)) ↑ • ε) • Ex) • (Ex • H ↑) • S^ -d/c ↑ • Ex ≈⟨ cong (lemma-swap-DD d1 (₀ , c)) (cong (rewrite-swap 100 auto) (sym (lemma-Ex-S^ᵏ 1 -d/c))) ⟩
  (((Ex • CZ^ (- c)) • [ d1 ]ᵈ ↑ • ε)) • (H • Ex) • Ex • S^ -d/c ≈⟨ cleft cright  right-unit ⟩
  (((Ex • CZ^ (- c)) • [ d1 ]ᵈ ↑)) • (H • Ex) • Ex • S^ -d/c ≈⟨ cright sym (sa (□ • □ ^ 2 • □) (□ ^ 2 • □ ^ 2) auto) ⟩
  (((Ex • CZ^ (- c)) • [ d1 ]ᵈ ↑)) • H • (Ex • Ex) • S^ -d/c ≈⟨ cright cright trans (cleft rewrite-swap 100 auto) left-unit ⟩
  (((Ex • CZ^ (- c)) • [ d1 ]ᵈ ↑)) • H • S^ -d/c ≈⟨ assoc ⟩
  (Ex • CZ^ (- c)) • [ d1 ]ᵈ ↑ • H • S^ -d/c ≈⟨ cright sym (comm-hs-w↑ -d/c [ d1 ]ᵈ) ⟩
  (Ex • CZ^ (- c)) • (H • S^ -d/c) • [ d1 ]ᵈ ↑ ≈⟨ sa (□ ^ 2 • □ ^ 2 • □) (□ ^ 4 • □) auto ⟩
  (Ex • CZ^ (- c) • H • S^ -d/c) • [ d1 ]ᵈ ↑ ≈⟨ refl ⟩
  [ c , d ]ᵈ • [ a , b ]ᵈ ↑ ≈⟨ cong refl (sym right-unit) ⟩
  [ d2 ∷ d1 ∷ [] ]ᵛᵈ ∎
  where
  c⁻¹ = ((c , λ ()) ⁻¹) .proj₁
  -d/c = - d * c⁻¹
  a⁻¹ = ((a , λ ()) ⁻¹) .proj₁
  -b/a = - b * a⁻¹




vd'-of : Vec D 2 -> Vec D 2
vd'-of ((a , b) ∷ (c , d) ∷ []) =  (a , b + - c) ∷ (c , d + - a) ∷ []

dir-of : Vec D 2 -> Word (Gen 2)
dir-of ((₀ , b) ∷ (₀ , d) ∷ [])                   =  CZ
dir-of ((₀ , b) ∷ (₁₊ _ , d) ∷ [])                =  H ↑ • CZ • H ↑ ^ 3
dir-of ((₁₊ _ , b) ∷ (₀ , d) ∷ [])                =  H ↓ • CZ • H ↓ ^ 3
dir-of ((a@(₁₊ _) , b) ∷ (c@(₁₊ _) , d) ∷ [])     =  H • H ↑ • CZ • S^ (- c * a⁻¹) • H ^ 3 • S^ (- a * c⁻¹) ↑ • H ↑ ^ 3
  where
  a⁻¹ = ((a , λ ()) ⁻¹) .proj₁
  c⁻¹ = ((c , λ ()) ⁻¹) .proj₁


lemma-dir-and-vd' : ∀ (vd : Vec D 2) ->
  let
  dir = dir-of vd
  vd' = vd'-of vd
  in
  
  [ vd ]ᵛᵈ • CZ ≈ dir ↑ • [ vd' ]ᵛᵈ

lemma-dir-and-vd' vd@((₀ , b) ∷ (₀ , d) ∷ []) = begin
  [ (₀ , b) ∷ (₀ , d) ∷ [] ]ᵛᵈ • CZ ≈⟨ cong (cong refl right-unit) refl ⟩
  ([ (₀ , b) ]ᵈ • [ (₀ , d) ]ᵈ ↑) • CZ ≈⟨ sa ((□ ^ 2 • □ ^ 2) • □) (□ ^ 2 • □ ^ 3) auto ⟩
  (Ex • CZ^ (- b)) • Ex ↑ • CZ^ (- d) ↑ • CZ ≈⟨ cong (word-comm 1 (toℕ (- b)) (sym lemma-comm-Ex-CZ-n)) (cright sym (aux-comm-CZ-CZ^k↑ (- d))) ⟩
  (CZ^ (- b) • Ex) • Ex ↑ • CZ • CZ^ (- d) ↑ ≈⟨ sa (□ ^ 2 • □ ^ 3) (□ • □ ^ 3 • □) auto ⟩
  CZ^ (- b) • (Ex • Ex ↑ • CZ) • CZ^ (- d) ↑ ≈⟨ cright cleft lemma-Ex-Ex↑-CZ ⟩
  CZ^ (- b) • (CZ ↑ • Ex • Ex ↑) • CZ^ (- d) ↑ ≈⟨ sa (□ • □ ^ 3 • □) (□ ^ 2 • □ ^ 3) auto ⟩
  (CZ^ (- b) • CZ ↑) • Ex • Ex ↑ • CZ^ (- d) ↑ ≈⟨ cleft word-comm (toℕ (- b)) 1 (sym (axiom selinger-c12)) ⟩
  (CZ ↑ • CZ^ (- b)) • Ex • Ex ↑ • CZ^ (- d) ↑ ≈⟨ sa (□ ^ 2 • □ ^ 3) (□ • □ ^ 2 • □ ^ 2) auto ⟩
  CZ ↑ • (CZ^ (- b) • Ex) • Ex ↑ • CZ^ (- d) ↑ ≈⟨ cright cleft word-comm (toℕ (- b)) 1 lemma-comm-Ex-CZ-n ⟩
  CZ ↑ • (Ex • CZ^ (- b)) • Ex ↑ • CZ^ (- d) ↑ ≈⟨ cright cong refl (sym right-unit) ⟩
  CZ ↑ • [ (₀ , b) ∷ (₀ , d) ∷ [] ]ᵛᵈ ≈⟨ sym (cright refl' (Eq.cong₂ (\ xx yy -> [ (₀ , xx) ∷ (₀ , yy) ∷ [] ]ᵛᵈ) (Eq.trans (Eq.cong (b +_) -0#≈0#
 ) (+-identityʳ b)) ((Eq.trans (Eq.cong (d +_) -0#≈0# ) (+-identityʳ d))))) ⟩
  CZ ↑ • [ (₀ , b + - ₀) ∷ (₀ , d + - ₀) ∷ [] ]ᵛᵈ ∎
  where
  dir = dir-of vd
  vd' = vd'-of vd


lemma-dir-and-vd' vd@(d1@(a@(₁₊ _) , b) ∷ d2@(₀ , d) ∷ []) = bbc (Ex ↑) Ex claim
  where
  dir = dir-of vd
  vd' = vd'-of vd
  dir-ex = dir-of (d2 ∷ d1 ∷ [])
  vd'-ex = vd'-of (d2 ∷ d1 ∷ [])
  
  claim : Ex ↑ • ([ vd ]ᵛᵈ • CZ) • Ex ≈ Ex ↑ • (dir ↑ • [ vd' ]ᵛᵈ) • Ex
  claim = begin
    Ex ↑ • ([ vd ]ᵛᵈ • CZ) • Ex ≈⟨ sa (□ • □ ^ 2 • □) (□ ^ 2 • □ ^ 2) auto ⟩
    (Ex ↑ • [ vd ]ᵛᵈ) • CZ • Ex ≈⟨ cright rewrite-swap 100 auto ⟩
    (Ex ↑ • [ vd ]ᵛᵈ) • Ex • CZ ≈⟨ sa (□ ^ 2 • □ ^ 2) (□ ^ 3 • □) auto ⟩
    (Ex ↑ • [ vd ]ᵛᵈ • Ex) • CZ ≈⟨ cleft lemma-swap-DD d1 d2 ⟩
    ([ d2 ∷ d1 ∷ [] ]ᵛᵈ) • CZ ≈⟨  lemma-dir-and-vd' (d2 ∷ d1 ∷ []) ⟩
    (dir-ex ↑ • [ vd'-ex ]ᵛᵈ) ≈⟨ cright sym (lemma-swap-DD (V.head vd') (V.head (V.drop 1 vd'))) ⟩
    (H ↑ ↑ • CZ ↑ • H ↑ ↑ ^ 3) • Ex ↑ • [ vd' ]ᵛᵈ • Ex ≈⟨ sym (sa (□ ^ 2 • □ ^ 2) (□ ^ 4) auto) ⟩
    ((H ↑ ↑ • CZ ↑ • H ↑ ↑ ^ 3) • Ex ↑) • [ vd' ]ᵛᵈ • Ex ≈⟨ cleft rewrite-swap 100 auto ⟩
    (Ex ↑ • (H ↓ • CZ • H ↓ ^ 3) ↑) • [ vd' ]ᵛᵈ • Ex ≈⟨ sym (sa (□ • □ ^ 2 • □) (□ ^ 2 • □ ^ 2) auto) ⟩
    Ex ↑ • (dir ↑ • [ vd' ]ᵛᵈ) • Ex ∎

lemma-dir-and-vd' vd@(d1@(₀ , b) ∷ d2@(c@(₁₊ _) , d) ∷ []) = begin
  [ vd ]ᵛᵈ • CZ ≈⟨ refl ⟩
  ([ d1 ]ᵈ • [ d2 ]ᵈ ↑ • ε) • CZ ≈⟨ cleft cright right-unit ⟩
  ([ d1 ]ᵈ • (Ex • CZ^ (- c) • H • S^ -d/c) ↑) • CZ ≈⟨ sa (□ ^ 5 • □) (□ ^ 4 • □ ^ 2) auto ⟩
  ([ d1 ]ᵈ • (Ex • CZ^ (- c) • H) ↑) • S^ -d/c ↑ • CZ ≈⟨ cright sym (aux-comm-CZ-S^k↑ -d/c) ⟩
  ([ d1 ]ᵈ • (Ex • CZ^ (- c) • H) ↑) • CZ • S^ -d/c ↑ ≈⟨ sa ((□ ^ 4) • □ ^ 2) (□ ^ 2 • □ ^ 3 • □) auto ⟩
  ([ d1 ]ᵈ • Ex ↑) • (CZ^ (- c) ↑ • H ↑ • CZ) • S^ -d/c ↑ ≈⟨ cright cleft aux-CZ^k↑H↑-CZ (-' (c , λ ())) ⟩
  ([ d1 ]ᵈ • Ex ↑) • (H ↑ • CZ • CZ02^ (- - c) • CX^ (- c) ↑) • S^ -d/c ↑ ≈⟨ cright cleft cright cright cleft refl' (Eq.cong CZ02^ (-‿involutive c)) ⟩
  ([ d1 ]ᵈ • Ex ↑) • (H ↑ • CZ • CZ02^ c • CX^ (- c) ↑) • S^ -d/c ↑ ≈⟨ sa (□ ^ 2 • □ ^ 4 • □) (□ • □ ^ 2 • □ ^ 4) auto ⟩
  [ d1 ]ᵈ • (Ex ↑ • H ↑) • CZ • CZ02^ c • CX^ (- c) ↑ • S^ -d/c ↑ ≈⟨ cright cleft rewrite-swap 100 auto ⟩
  [ d1 ]ᵈ • (H ↑ ↑ • Ex ↑) • CZ • CZ02^ c • CX^ (- c) ↑ • S^ -d/c ↑ ≈⟨ sa (□ • □ ^ 2 • □) (□ ^ 2 • □ ^ 2) auto ⟩
  ([ d1 ]ᵈ • H ↑ ↑) • Ex ↑ • CZ • CZ02^ c • CX^ (- c) ↑ • S^ -d/c ↑ ≈⟨ cleft comm-dbox-w↑↑ d1 H ⟩
  ( H ↑ ↑ • [ d1 ]ᵈ) • Ex ↑ • CZ • CZ02^ c • CX^ (- c) ↑ • S^ -d/c ↑ ≈⟨ cleft cright aux-dd d1 ⟩
  ( H ↑ ↑ • [ d1 ]ᵈ') • Ex ↑ • CZ • CZ02^ c • CX^ (- c) ↑ • S^ -d/c ↑ ≈⟨ sa (□ ^ 3 • □ ^ 3) (□ ^ 2 • □ ^ 3 • □) auto ⟩
  ( H ↑ ↑ • CZ^ (- b)) • (Ex • Ex ↑ • CZ) • CZ02^ c • CX^ (- c) ↑ • S^ -d/c ↑ ≈⟨ cright cleft lemma-Ex-Ex↑-CZ ⟩
  ( H ↑ ↑ • CZ^ (- b)) • (CZ ↑ • Ex • Ex ↑) • CZ02^ c • CX^ (- c) ↑ • S^ -d/c ↑ ≈⟨ sa (□ ^ 2 • □ ^ 3 • □) (□ • □ ^ 2 • □ ^ 3) auto ⟩
  H ↑ ↑ • (CZ^ (- b) • CZ ↑) • Ex • Ex ↑ • CZ02^ c • CX^ (- c) ↑ • S^ -d/c ↑ ≈⟨ cright cleft word-comm (toℕ (- b)) 1 (sym (axiom selinger-c12)) ⟩
  H ↑ ↑ • (CZ ↑ • CZ^ (- b)) • Ex • Ex ↑ • CZ02^ c • CX^ (- c) ↑ • S^ -d/c ↑ ≈⟨ sa (□ • □ ^ 2 • □ ^ 4) (□ ^ 2 • □ ^ 2 • □ ^ 2 • □) auto ⟩
  (H ↑ ↑ • CZ ↑) • (CZ^ (- b) • Ex) • (Ex ↑ • CZ02^ c) • CX^ (- c) ↑ • S^ -d/c ↑ ≈⟨ cright cong (sym (aux-dd d1))  (cleft aux-Ex↑-CZ02^k c) ⟩
  (H ↑ ↑ • CZ ↑) • (Ex • CZ^ (- b)) • (CZ^ c • Ex ↑) • CX^ (- c) ↑ • S^ -d/c ↑ ≈⟨ cright sa (□ ^ 2 • □ ^ 2 • □) (□ • □ ^ 2 • □ ^ 2) auto ⟩
  (H ↑ ↑ • CZ ↑) • Ex • (CZ^ (- b) • CZ^ c) • Ex ↑ • CX^ (- c) ↑ • S^ -d/c ↑ ≈⟨ cright cright cleft lemma-CZ^k+l (- b) c ⟩
  (H ↑ ↑ • CZ ↑) • Ex • CZ^ (- b + c) • Ex ↑ • CX^ (- c) ↑ • S^ -d/c ↑ ≈⟨ cright cright cright cright cleft lemma-cong↑ _ _ (aux-CX^-CX'^ (- c)) ⟩
  (H ↑ ↑ • CZ ↑) • Ex • CZ^ (- b + c) • Ex ↑ • CX'^ (- c) ↑ • S^ -d/c ↑ ≈⟨ cright cright cright sa (□ • □ ^ 3 • □) (□ ^ 2 • □ ^ 3) auto ⟩
  (H ↑ ↑ • CZ ↑) • Ex • CZ^ (- b + c) • (Ex ↑ • H ↑ ^ 3) • CZ^ (- c) ↑ • H ↑ • S^ -d/c ↑ ≈⟨ cright cright cright cleft rewrite-swap 100 auto ⟩
  (H ↑ ↑ • CZ ↑) • Ex • CZ^ (- b + c) • (H ↑ ↑ ^ 3 • Ex ↑) • CZ^ (- c) ↑ • H ↑ • S^ -d/c ↑ ≈⟨ cright cright sa (□ • □ ^ 2 • □) (□ ^ 2 • □ ^ 2) auto ⟩
  (H ↑ ↑ • CZ ↑) • Ex • (CZ^ (- b + c) • H ↑ ↑ ^ 3) • Ex ↑ • CZ^ (- c) ↑ • H ↑ • S^ -d/c ↑ ≈⟨ cright cright cleft word-comm (toℕ (- b + c)) 3 (lemma-comm-CZ-w↑↑ H) ⟩
  (H ↑ ↑ • CZ ↑) • Ex • (H ↑ ↑ ^ 3 • CZ^ (- b + c)) • Ex ↑ • CZ^ (- c) ↑ • H ↑ • S^ -d/c ↑ ≈⟨ cright sa (□ • □ ^ 2 • □) (□ ^ 2 • □ ^ 2) auto ⟩
  (H ↑ ↑ • CZ ↑) • (Ex • H ↑ ↑ ^ 3) • CZ^ (- b + c) • Ex ↑ • CZ^ (- c) ↑ • H ↑ • S^ -d/c ↑ ≈⟨ cright cleft rewrite-swap 100 auto ⟩
  (H ↑ ↑ • CZ ↑) • (H ↑ ↑ ^ 3 • Ex) • CZ^ (- b + c) • Ex ↑ • CZ^ (- c) ↑ • H ↑ • S^ -d/c ↑ ≈⟨ sa (□ ^ 2 • □ ^ 2 • □ ^ 2) (□ ^ 3 • □ ^ 2 • □) auto ⟩
  (H ↑ ↑ • CZ ↑ • H ↑ ↑ ^ 3) • (Ex • CZ^ (- b + c)) • Ex ↑ • CZ^ (- c) ↑ • H ↑ • S^ -d/c ↑ ≈⟨ cright cleft cright refl' (Eq.cong CZ^ (Eq.sym (Eq.trans (Eq.sym (-‿+-comm b (- c))) (Eq.cong (- b +_) (-‿involutive c))))) ⟩
  (H ↑ ↑ • CZ ↑ • H ↑ ↑ ^ 3) • (Ex • CZ^ (- (b + - c))) • Ex ↑ • CZ^ (- c) ↑ • H ↑ • S^ -d/c ↑ ≈⟨ cright (cright (cright cright cright refl' (Eq.cong (\ xx -> S^ xx ↑) (Eq.sym (Eq.cong (\ xx -> - xx * c⁻¹) (Eq.trans (Eq.cong (d +_) -0#≈0#) (+-identityʳ d))))))) ⟩
  (H ↑ ↑ • CZ ↑ • H ↑ ↑ ^ 3) • (Ex • CZ^ (- (b + - c))) • Ex ↑ • CZ^ (- c) ↑ • H ↑ • S^ -d'/c ↑ ≈⟨ cright (cright sym right-unit) ⟩
  dir ↑ • [ vd' ]ᵛᵈ ∎
  where
  dir = dir-of vd
  vd' = vd'-of vd

  c⁻¹ = ((c , λ ()) ⁻¹) .proj₁
  -d/c = - d * c⁻¹
  -d'/c = - (d + - ₀) * c⁻¹


lemma-dir-and-vd' vd@(d1@(a1@(₁₊ _) , b1) ∷ d2@(a2@(₁₊ _) , b2) ∷ []) = begin
  [ vd ]ᵛᵈ • CZ ≈⟨ refl ⟩
  ([ d1 ]ᵈ • [ d2 ]ᵈ ↑ • ε) • CZ ≈⟨ cleft cong refl right-unit ⟩
  ([ d1 ]ᵈ • [ d2 ]ᵈ ↑) • CZ ≈⟨ refl ⟩
  ((Ex • CZ^ (- a1) • (H • S^ -b1/a1)) • (Ex • CZ^ (- a2) • (H • S^ -b2/a2)) ↑) • CZ ≈⟨ sa ((□ ^ 4 • □ ^ 4) • □) ((□ ^ 4 • □ ^ 3 • □ ^ 2)) auto ⟩
  (Ex • CZ^ (- a1) • H • S^ -b1/a1) • (Ex ↑ • CZ^ (- a2) ↑ • H ↑) • S^ -b2/a2 ↑ • CZ ≈⟨ cright cright sym (aux-comm-CZ-S^k↑ -b2/a2) ⟩
  (Ex • CZ^ (- a1) • H • S^ -b1/a1) • (Ex ↑ • CZ^ (- a2) ↑ • H ↑) • CZ • S^ -b2/a2 ↑ ≈⟨ sa (□ ^ 4 • □ ^ 3 • □ ^ 2) (□ ^ 2 • (□ ^ 2 • □) • □ ^ 4) auto ⟩
  (Ex • CZ^ (- a1)) • ((H • S^ -b1/a1) • Ex ↑) • CZ^ (- a2) ↑ • H ↑ • CZ • S^ -b2/a2 ↑ ≈⟨ cright cleft comm-hs-w↑ -b1/a1 Ex ⟩
  (Ex • CZ^ (- a1)) • (Ex ↑ • H • S^ -b1/a1) • CZ^ (- a2) ↑ • H ↑ • CZ • S^ -b2/a2 ↑ ≈⟨ sa (□ ^ 2 • □ ^ 3 • □ ^ 4) (□ ^ 3 • □ • □ ^ 3 • □ ^ 2) auto ⟩
  (Ex • CZ^ (- a1) • Ex ↑) • H • (S^ -b1/a1 • CZ^ (- a2) ↑ • H ↑) • CZ • S^ -b2/a2 ↑ ≈⟨ cong (cright sym (aux-Ex↑-CZ02^k (- a1))) (cright cleft  lemma-comm-Sᵏ-w↑ (toℕ -b1/a1) (CZ^ (- a2) • H)) ⟩
  (Ex • Ex ↑ • CZ02^ (- a1)) • H • ((CZ^ (- a2) ↑ • H ↑) • S^ -b1/a1) • CZ • S^ -b2/a2 ↑ ≈⟨ sa (□ ^ 3 • □ • (□ ^ 2 • □) • □ ^ 2) (□ ^ 2 • □ ^ 4 • □ ^ 2 • □) auto ⟩
  (Ex • Ex ↑) • (CZ02^ (- a1) • H • CZ^ (- a2) ↑ • H ↑) • (S^ -b1/a1 • CZ) • S^ -b2/a2 ↑ ≈⟨ cright cright cleft word-comm (toℕ -b1/a1) 1 (sym (axiom comm-CZ-S↓)) ⟩
  (Ex • Ex ↑) • (CZ02^ (- a1) • H • CZ^ (- a2) ↑ • H ↑) • (CZ • S^ -b1/a1) • S^ -b2/a2 ↑ ≈⟨ cright sa (□ ^ 4 • □ ^ 2 • □) (□ ^ 5 • □ ^ 2) auto ⟩
  (Ex • Ex ↑) • (CZ02^ (- a1) • H • CZ^ (- a2) ↑ • H ↑ • CZ) • S^ -b1/a1 • S^ -b2/a2 ↑ ≈⟨ cright cleft lemma-CZ02^k-CZ^l↑-CZ a1* a2* ⟩
  (Ex • Ex ↑) • (H • H ↑ • CZ • S^ (- a2 * a1⁻¹) • CX02^ (- a1) • S^ (a2 * a1⁻¹) • S^ (- a1 * a2⁻¹) ↑ • CX^ (- a2) ↑ • S^ (a1 * a2⁻¹) ↑) •  S^ -b1/a1 ↓ • S^ -b2/a2 ↑ ≈⟨ sa (□ ^ 2 • □ ^ 9 • □ ^ 2) (□ ^ 5 • □ ^ 3 • (□ ^ 3 • □) • □) auto ⟩
  
  (Ex • Ex ↑ • H • H ↑ • CZ) • (S^ (- a2 * a1⁻¹) • CX02^ (- a1) • S^ (a2 * a1⁻¹)) • ((S^ (- a1 * a2⁻¹) ↑ • CX^ (- a2) ↑ • S^ (a1 * a2⁻¹) ↑) •  S^ -b1/a1) • S^ -b2/a2 ↑ ≈⟨ cong (rewrite-swap 100 auto) (cright cleft sym (lemma-comm-Sᵏ-w↑ (toℕ -b1/a1) (S^ (- a1 * a2⁻¹) • CX^ (- a2) • S^ (a1 * a2⁻¹)))) ⟩
  (H ↑ • H ↑ ↑ • CZ ↑ • Ex • Ex ↑) • (S^ (- a2 * a1⁻¹) • CX02^ (- a1) • S^ (a2 * a1⁻¹)) • (S^ -b1/a1 • (S^ (- a1 * a2⁻¹) ↑ • CX^ (- a2) ↑ • S^ (a1 * a2⁻¹) ↑)) • S^ -b2/a2 ↑ ≈⟨ sa (□ ^ 5 • □ ^ 3 • □ ^ 4 • □) (□ ^ 4 • □ ^ 2 • □ • □ ^ 2 • □ ^ 2 • □ ^ 2) auto ⟩
  (H ↑ • H ↑ ↑ • CZ ↑ • Ex) • (Ex ↑ • S^ (- a2 * a1⁻¹)) • CX02^ (- a1) • (S^ (a2 * a1⁻¹) • S^ -b1/a1) • (S^ (- a1 * a2⁻¹) ↑ • CX^ (- a2) ↑) • S^ (a1 * a2⁻¹) ↑ • S^ -b2/a2 ↑ ≈⟨ cright cong (sym (lemma-comm-Sᵏ-w↑ (toℕ (- a2 * a1⁻¹)) Ex)) (cright cong (L02.lemma-S^k+l (a2 * a1⁻¹) -b1/a1) (cright lemma-cong↑ _ _ (lemma-S^k+l (a1 * a2⁻¹) -b2/a2))) ⟩
  (H ↑ • H ↑ ↑ • CZ ↑ • Ex) • (S^ (- a2 * a1⁻¹) • Ex ↑) • CX02^ (- a1) • S^ (a2 * a1⁻¹ + -b1/a1) • (S^ (- a1 * a2⁻¹) ↑ • CX^ (- a2) ↑) • S^ (a1 * a2⁻¹ + -b2/a2) ↑ ≈⟨ sa (□ ^ 4 • □ ^ 2 • □ • □ • □ ^ 2 • □ ) (□ ^ 3 • □ ^ 2 • □ ^ 2 • □ ^ 2 • □ ^ 2) auto ⟩
  (H ↑ • H ↑ ↑ • CZ ↑) • (Ex • S^ (- a2 * a1⁻¹)) • (Ex ↑ • CX02^ (- a1)) • (S^ (a2 * a1⁻¹ + -b1/a1) • S^ (- a1 * a2⁻¹) ↑) • CX^ (- a2) ↑ • S^ (a1 * a2⁻¹ + -b2/a2) ↑ ≈⟨ cright cong (lemma-Ex-S^ᵏ 1 (- a2 * a1⁻¹)) (cong (aux-Ex↑-CX02^k (- a1)) (cleft lemma-comm-Sᵏ-w↑ (toℕ (a2 * a1⁻¹ + -b1/a1)) (S^ (- a1 * a2⁻¹)))) ⟩
  (H ↑ • H ↑ ↑ • CZ ↑) • (S^ (- a2 * a1⁻¹) ↑ • Ex) • (CX'^ (- a1) • Ex ↑) • (S^ (- a1 * a2⁻¹) ↑ • S^ (a2 * a1⁻¹ + -b1/a1)) • CX^ (- a2) ↑ • S^ (a1 * a2⁻¹ + -b2/a2) ↑ ≈⟨ sa (□ ^ 3 • □ ^ 2 • (□ ^ 3 • □) • □ ^ 2 • □ ^ 2) (□ ^ 4 • □ ^ 2 • □ ^ 2 • □ ^ 2 • □ ^ 3) auto ⟩
  (H ↑ • H ↑ ↑ • CZ ↑ • S^ (- a2 * a1⁻¹) ↑) • (Ex • H ^ 3) • (CZ^ (- a1) • H) • (Ex ↑ • S^ (- a1 * a2⁻¹) ↑) • S^ (a2 * a1⁻¹ + -b1/a1) • CX^ (- a2) ↑ • S^ (a1 * a2⁻¹ + -b2/a2) ↑ ≈⟨ cright cong (rewrite-swap 100 auto) (cright cleft lemma-cong↑ _ _ (lemma-Ex-S^ᵏ 0 (- a1 * a2⁻¹))) ⟩
  (H ↑ • H ↑ ↑ • CZ ↑ • S^ (- a2 * a1⁻¹) ↑) • (H ↑ ^ 3 • Ex) • (CZ^ (- a1) • H) • (S^ (- a1 * a2⁻¹) ↑ ↑ • Ex ↑) • S^ (a2 * a1⁻¹ + -b1/a1) • CX^ (- a2) ↑ • S^ (a1 * a2⁻¹ + -b2/a2) ↑ ≈⟨ sa (□ ^ 4 • □ ^ 2 • □ ^ 2 • □ ^ 2 • □ ^ 3) (□ ^ 5 • □ ^ 2 • □ ^ 2 • □ ^ 2 • □ ^ 2) auto ⟩
  (H ↑ • H ↑ ↑ • CZ ↑ • S^ (- a2 * a1⁻¹) ↑ • H ↑ ^ 3) • (Ex • CZ^ (- a1)) • (H • S^ (- a1 * a2⁻¹) ↑ ↑) • (Ex ↑ • S^ (a2 * a1⁻¹ + -b1/a1)) • CX^ (- a2) ↑ • S^ (a1 * a2⁻¹ + -b2/a2) ↑ ≈⟨ cright cright cong (lemma-comm-H-w↑ (S^ (- a1 * a2⁻¹) ↑)) (cleft sym (lemma-comm-Sᵏ-w↑ (toℕ (a2 * a1⁻¹ + -b1/a1)) Ex)) ⟩
  (H ↑ • H ↑ ↑ • CZ ↑ • S^ (- a2 * a1⁻¹) ↑ • H ↑ ^ 3) • (Ex • CZ^ (- a1)) • (S^ (- a1 * a2⁻¹) ↑ ↑ • H) • (S^ (a2 * a1⁻¹ + -b1/a1) • Ex ↑) • CX^ (- a2) ↑ • S^ (a1 * a2⁻¹ + -b2/a2) ↑ ≈⟨ sa (□ • □ • □ ^ 2 • □ ^ 2 • □) (□ • □ ^ 2 • □ ^ 4) auto ⟩
  (H ↑ • H ↑ ↑ • CZ ↑ • S^ (- a2 * a1⁻¹) ↑ • H ↑ ^ 3) • ((Ex • CZ^ (- a1)) • S^ (- a1 * a2⁻¹) ↑ ↑) • H • S^ (a2 * a1⁻¹ + -b1/a1) • Ex ↑ • CX^ (- a2) ↑ • S^ (a1 * a2⁻¹ + -b2/a2) ↑ ≈⟨ cright cong (comm-dbox-w↑↑ ((₀ , a1)) (S^ (- a1 * a2⁻¹))) (cright cright cright cleft lemma-cong↑ _ _ (aux-CX^-CX'^ (- a2))) ⟩
  (H ↑ • H ↑ ↑ • CZ ↑ • S^ (- a2 * a1⁻¹) ↑ • H ↑ ^ 3) • (S^ (- a1 * a2⁻¹) ↑ ↑ • (Ex • CZ^ (- a1))) • H • S^ (a2 * a1⁻¹ + -b1/a1) • Ex ↑ • CX'^ (- a2) ↑ • S^ (a1 * a2⁻¹ + -b2/a2) ↑ ≈⟨ sa (□ ^ 5 • □ ^ 3 • □ • □ • □ • □ ^ 3 • □ ) (□ ^ 6 • □ ^ 4 • □ ^ 2 • □ ^ 3) auto ⟩
  (H ↑ • H ↑ ↑ • CZ ↑ • S^ (- a2 * a1⁻¹) ↑ • H ↑ ^ 3 • S^ (- a1 * a2⁻¹) ↑ ↑) • (Ex • CZ^ (- a1) • H • S^ (a2 * a1⁻¹ + -b1/a1)) • (Ex ↑ • H ↑ ^ 3) • CZ^ (- a2) ↑ • H ↑ • S^ (a1 * a2⁻¹ + -b2/a2) ↑ ≈⟨ cright cong (cright cright cright refl' (Eq.cong S^ ( (cal-b1-a2' a1 a2 b1 (λ ()) λ ())))) (cong (rewrite-swap 100 auto) (cright cright refl' (Eq.cong (\ xx -> S^ xx ↑) (cal-b1-a2' a2 a1 b2 (λ ()) (λ ())))))  ⟩
  (H ↑ • H ↑ ↑ • CZ ↑ • S^ (- a2 * a1⁻¹) ↑ • H ↑ ^ 3 • S^ (- a1 * a2⁻¹) ↑ ↑) • (Ex • CZ^ (- a1) • H • S^ (- (b1 + - a2) * a1⁻¹)) • (H ↑ ↑ ^ 3 • Ex ↑) • CZ^ (- a2) ↑ • H ↑ • S^ (-(b2 + - a1) * a2⁻¹) ↑ ≈⟨ cright sa (□ • □ ^ 2 • □ ^ 3) (□ ^ 2 • □ ^ 4) auto ⟩
  (H ↑ • H ↑ ↑ • CZ ↑ • S^ (- a2 * a1⁻¹) ↑ • H ↑ ^ 3 • S^ (- a1 * a2⁻¹) ↑ ↑) • ([ a1 , b1 + - a2 ]ᵈ • H ↑ ↑ ^ 3) • [ a2 , b2 + - a1 ]ᵈ ↑ ≈⟨ cright (cleft comm-dbox-w↑↑ (a1 , b1 + - a2) (H ^ 3)) ⟩
  (H ↑ • H ↑ ↑ • CZ ↑ • S^ (- a2 * a1⁻¹) ↑ • H ↑ ^ 3 • S^ (- a1 * a2⁻¹) ↑ ↑) • (H ↑ ↑ ^ 3 • [ a1 , b1 + - a2 ]ᵈ) • [ a2 , b2 + - a1 ]ᵈ ↑ ≈⟨ sa (□ ^ 6 • □ ^ 2 • □) (□ ^ 7 • □ ^ 2) auto ⟩
  (H ↑ • H ↑ ↑ • CZ ↑ • S^ (- a2 * a1⁻¹) ↑ • H ↑ ^ 3 • S^ (- a1 * a2⁻¹) ↑ ↑ • H ↑ ↑ ^ 3) • [ a1 , b1 + - a2 ]ᵈ • [ a2 , b2 + - a1 ]ᵈ ↑ ≈⟨ cright cong refl (sym right-unit) ⟩
  dir ↑ • [ vd' ]ᵛᵈ ∎
  where
  dir = dir-of vd
  vd' = vd'-of vd
  a1* = (a1 , λ ())
  a2* = (a2 , λ ())
  a1⁻¹ = ((a1 , λ ()) ⁻¹) .proj₁
  a2⁻¹ = ((a2 , λ ()) ⁻¹) .proj₁
  
  -b2/a2 = - b2 * a2⁻¹
  -b1/a1 = - b1 * a1⁻¹

