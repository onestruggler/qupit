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



module N.BR.Two.D (p-2 : ℕ) (p-prime : Prime (2+ p-2)) where

n : ℕ
n = 0
    
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
open import Zp.Mod-Lemmas p-2 p-prime
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
open import N.Ex-Sym5 p-2 p-prime hiding (module L0)
open import N.Ex-Sym2n p-2 p-prime
open import N.Ex-Sym3n p-2 p-prime

open import N.Lemma-Comm-n p-2 p-prime 0
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
open import N.Lemmas-3Q p-2 p-prime
open import N.Pushing.DH p-2 p-prime
open import N.Duality p-2 p-prime
open import N.BR.Calculations p-2 p-prime
open import N.BR.One.A p-2 p-prime
open import N.BR.Two.Lemmas p-2 p-prime hiding (sa ; n ; module L01)


open PB ((₂₊ n) QRel,_===_)
open PP ((₂₊ n) QRel,_===_)
open SR word-setoid
open Pattern-Assoc
open Lemmas0 n
module L01 = Lemmas0 (₁₊ n)
open Lemmas-2Q n
open Sym0-Rewriting (₁₊ n)
open Rewriting-Swap 1


{-
dir-and-d' : ∀ (d : D) (g : Gen 2) (neq : g ≢ H-gen ↥) -> ℤ ₚ × Word (Gen 1) × D

dir-and-d' d@(a@₀ , b@₀)               H-gen neq = ₀ , H              ,   (b , - a)
dir-and-d' d@(a@₀ , b@(₁₊ _))          H-gen neq = ₀ , ε              ,   (b , - a)
dir-and-d' d@(a@(₁₊ _) , b@₀)          H-gen neq = ₀ , HH             ,   (b , - a)
dir-and-d' d@(a@(₁₊ _) , b@(₁₊ _))     H-gen neq = ₀ , dir            ,   (b , - a)
  where
  a⁻¹ = ((a , λ ()) ⁻¹) .proj₁
  b/a = b * a⁻¹
  a/b = (a , λ ()) *' (b , λ ()) ⁻¹
  dir = ZM a/b • S^ b/a
dir-and-d' d@(a@₀ , b)                 S-gen neq = ₀ , S              ,   (a , b + - a)
dir-and-d' d@(a@(₁₊ _) , b)            S-gen neq = ₀ , ε              ,   (a , b + - a)
dir-and-d' d@(a , b)               (S-gen ↥) neq = ₁ , ε              ,   (a , b)

dir-and-d' d@(a@₀ , b)                CZ-gen neq = ₀ , ε              ,   (a , b + - ₁)
dir-and-d' d@(a@(₁₊ _) , b)           CZ-gen neq = a , dir            ,   (a , b + - ₁)
  where
  a⁻¹ = ((a , λ ()) ⁻¹) .proj₁
  dir = H • S^ (- a⁻¹) • H ^ 3
dir-and-d' d@(a , b)               (H-gen ↥) neq = ⊥-elim (neq auto)

-}



d'-of : ∀ (d : D) (g : Gen 2) (neq : g ≢ H-gen ↥) -> D

d'-of (a , b) H-gen _       = (b , - a)
d'-of (a , b) S-gen _       = (a , b + - a)
d'-of (a , b) (S-gen ↥) _   = (a , b)
d'-of (a , b) CZ-gen _      = (a , b + - ₁)

d'-of (a , b) (H-gen ↥) neq = ⊥-elim (neq auto)


dir-of : ∀ (d : D) (g : Gen 2) (neq : g ≢ H-gen ↥) -> ℤ ₚ × Word (Gen 1)

dir-of (₀ , ₀)               H-gen neq = ₀ , H
dir-of (₀ , ₁₊ _)            H-gen neq = ₀ , ε
dir-of (₁₊ _ , ₀)            H-gen neq = ₀ , HH
dir-of (a@(₁₊ _) , b@(₁₊ _)) H-gen neq = ₀ , ZM a/b • S^ b/a
  where
  a⁻¹ = ((a , λ ()) ⁻¹) .proj₁
  b/a = b * a⁻¹
  a/b = (a , λ ()) *' (b , λ ()) ⁻¹
dir-of (₀ , b)               S-gen neq = ₀ , S
dir-of (₁₊ _ , b)            S-gen neq = ₀ , ε
dir-of (a , b)           (S-gen ↥) neq = ₁ , ε

dir-of (₀ , b)              CZ-gen neq = ₀ , ε
dir-of (a@(₁₊ _) , b)       CZ-gen neq = a , H • S^ (- a⁻¹) • H ^ 3
  where
  a⁻¹ = ((a , λ ()) ⁻¹) .proj₁
  
dir-of (a , b)           (H-gen ↥) neq = ⊥-elim (neq auto)


lemma-D-br : ∀ (d : D) (g : Gen 2) (neq : g ≢ H-gen ↥) ->
  let
  (e , dir) = dir-of d g neq
  d'        = d'-of d g neq
  in

  [ d ]ᵈ • [ g ]ʷ ≈ S^ e ↓ • dir ↑ • [ d' ]ᵈ

lemma-D-br d@(a , b) g@(H-gen ↥) neq = ⊥-elim (neq auto)

lemma-D-br d@(a@(₁₊ _) , b@₀) g@CZ-gen neq = begin
  (Ex • CZ^ (- a) • (H • S^ -b/a)) • CZ ≈⟨ special-assoc (□ ^ 4 • □) (□ ^ 2 • □ ^ 3) auto ⟩
  (Ex • CZ^ (- a)) • H • S^ -b/a • CZ ≈⟨ cright cright  (word-comm (toℕ (-b/a)) 1 (sym (axiom comm-CZ-S↓))) ⟩
  (Ex • CZ^ (- a)) • H • CZ • S^ -b/a ≈⟨  special-assoc (□ ^ 2 • □ ^ 3) (□ • □ ^ 3 • □) auto ⟩
  Ex • (CZ^ (- a) • H • CZ) • S^ -b/a ≈⟨ cright cleft aux-CZ^-k-H-CZ (a , (λ ())) ⟩
  Ex • (H • S^ a ↑ • S^ (- a⁻¹) • CX^ (- a) • S^ a⁻¹) • S^ -b/a ≈⟨ special-assoc (□ • □ ^ 5 • □) (□ ^ 2 • □ ^ 3 • □ ^ 2) auto ⟩
  (Ex • H) • (S^ a ↑ • S^ (- a⁻¹) • CX^ (- a)) • S^ a⁻¹ • S^ -b/a ≈⟨ cong (rewrite-swap 100 auto) (cright L01.lemma-S^k+l a⁻¹ -b/a) ⟩
  (H ↑ • Ex) • (S^ a ↑ • S^ (- a⁻¹) • CX^ (- a)) • S^ (a⁻¹ + -b/a) ≈⟨ cright cong (cright cright aux-CX^-CX'^ (- a)) refl ⟩
  (H ↑ • Ex) • (S^ a ↑ • S^ (- a⁻¹) • CX'^ (- a)) • S^ (a⁻¹ + -b/a) ≈⟨ cright special-assoc (□ ^ 5 • □) (□ ^ 4 • □ ^ 2) auto ⟩
  (H ↑ • Ex) • (S^ a ↑ • S^ (- a⁻¹) • H ^ 3 • CZ^ (- a)) • H • S^ (a⁻¹ + -b/a) ≈⟨ special-assoc (□ ^ 2 • □ ^ 4 • □ ^ 2) (□ • □ ^ 2 • □ ^ 3 • □ ^ 2) auto ⟩
  H ↑ • (Ex • S^ a ↑) • (S^ (- a⁻¹) • H ^ 3 • CZ^ (- a)) • H • S^ (a⁻¹ + -b/a) ≈⟨ cright cong (lemma-Ex-S^ᵏ↑ a) refl ⟩
  H ↑ • (S^ a • Ex) • (S^ (- a⁻¹) • H ^ 3 • CZ^ (- a)) • H • S^ (a⁻¹ + -b/a) ≈⟨  special-assoc (□ • □ ^ 2 • □ ^ 3 • □) (□ ^ 2 • □ ^ 2 • □ ^ 2 • □) auto ⟩
  (H ↑ • S^ a) • (Ex • S^ (- a⁻¹)) • (H ^ 3 • CZ^ (- a)) • H • S^ (a⁻¹ + -b/a) ≈⟨ cright cong (lemma-Ex-S^ᵏ (- a⁻¹)) (cright (cright refl' (Eq.cong S^ aux))) ⟩
  (H ↑ • S^ a) • (S^ (- a⁻¹) ↑ • Ex) • (H ^ 3 • CZ^ (- a)) • H • S^ (- (b + - ₁) * a⁻¹) ≈⟨ cright special-assoc (□ ^ 2 • □ ^ 2 • □) (□ • □ ^ 2 • □ ^ 2) auto ⟩
  (H ↑ • S^ a) • S^ (- a⁻¹) ↑ • (Ex • H ^ 3) • CZ^ (- a) • H • S^ (- (b + - ₁) * a⁻¹) ≈⟨ cright cright cleft rewrite-swap 100 auto ⟩
  (H ↑ • S^ a) • S^ (- a⁻¹) ↑ • (H ↑ ^ 3 • Ex) • CZ^ (- a) • H • S^ (- (b + - ₁) * a⁻¹) ≈⟨ cleft sym (lemma-comm-Sᵏ-w↑ (toℕ a) H) ⟩
  (S^ a • H ↑) • S^ (- a⁻¹) ↑ • (H ↑ ^ 3 • Ex) • CZ^ (- a) • H • S^ (- (b + - ₁) * a⁻¹) ≈⟨ special-assoc (□ ^ 2 • □ • □ ^ 2 • □ ^ 3) (□ • □ ^ 3 • □ ^ 4) auto ⟩
  S^ a • (H ↑ • S^ (- a⁻¹) ↑ • H ↑ ^ 3) • Ex • CZ^ (- a) • H • S^ (- (b + - ₁) * a⁻¹) ≈⟨ refl ⟩

  S^ a • (H ↑ • S^ (- a⁻¹) ↑ • H ↑ ^ 3) • [ a , b + - ₁ ]ᵈ ≈⟨  cright refl ⟩
  S^ e • dir ↑ • [ d' ]ᵈ ∎
  where
  edd = dir-of d g neq
  e = edd .proj₁
  dir = edd .proj₂
  d' = d'-of d g neq
  a⁻¹ = ((a , λ ()) ⁻¹) .proj₁
  -b/a = - b * a⁻¹
  aux : a⁻¹ + -b/a ≡ - (b + - ₁) * a⁻¹
  aux = Eq.trans (Eq.cong (_+ -b/a) (Eq.sym (*-identityˡ a⁻¹))) (Eq.trans (Eq.sym (*-distribʳ-+ a⁻¹ ₁ (- b))) (Eq.trans (Eq.cong (_* a⁻¹) (+-comm ₁ (- b))) (Eq.trans (Eq.cong (_* a⁻¹) (Eq.cong (- b +_) (Eq.sym (-‿involutive ₁)))) (Eq.cong (_* a⁻¹) ( (-‿+-comm b (- ₁)))))))

lemma-D-br d@(a@(₁₊ _) , b@(₁₊ _)) g@CZ-gen neq = begin
  (Ex • CZ^ (- a) • (H • S^ -b/a)) • CZ ≈⟨ special-assoc (□ ^ 4 • □) (□ ^ 2 • □ ^ 3) auto ⟩
  (Ex • CZ^ (- a)) • H • S^ -b/a • CZ ≈⟨ cright cright  (word-comm (toℕ (-b/a)) 1 (sym (axiom comm-CZ-S↓))) ⟩
  (Ex • CZ^ (- a)) • H • CZ • S^ -b/a ≈⟨  special-assoc (□ ^ 2 • □ ^ 3) (□ • □ ^ 3 • □) auto ⟩
  Ex • (CZ^ (- a) • H • CZ) • S^ -b/a ≈⟨ cright cleft aux-CZ^-k-H-CZ (a , (λ ())) ⟩
  Ex • (H • S^ a ↑ • S^ (- a⁻¹) • CX^ (- a) • S^ a⁻¹) • S^ -b/a ≈⟨ special-assoc (□ • □ ^ 5 • □) (□ ^ 2 • □ ^ 3 • □ ^ 2) auto ⟩
  (Ex • H) • (S^ a ↑ • S^ (- a⁻¹) • CX^ (- a)) • S^ a⁻¹ • S^ -b/a ≈⟨ cong (rewrite-swap 100 auto) (cright L01.lemma-S^k+l a⁻¹ -b/a) ⟩
  (H ↑ • Ex) • (S^ a ↑ • S^ (- a⁻¹) • CX^ (- a)) • S^ (a⁻¹ + -b/a) ≈⟨ cright cong (cright cright aux-CX^-CX'^ (- a)) refl ⟩
  (H ↑ • Ex) • (S^ a ↑ • S^ (- a⁻¹) • CX'^ (- a)) • S^ (a⁻¹ + -b/a) ≈⟨ cright special-assoc (□ ^ 5 • □) (□ ^ 4 • □ ^ 2) auto ⟩
  (H ↑ • Ex) • (S^ a ↑ • S^ (- a⁻¹) • H ^ 3 • CZ^ (- a)) • H • S^ (a⁻¹ + -b/a) ≈⟨ special-assoc (□ ^ 2 • □ ^ 4 • □ ^ 2) (□ • □ ^ 2 • □ ^ 3 • □ ^ 2) auto ⟩
  H ↑ • (Ex • S^ a ↑) • (S^ (- a⁻¹) • H ^ 3 • CZ^ (- a)) • H • S^ (a⁻¹ + -b/a) ≈⟨ cright cong (lemma-Ex-S^ᵏ↑ a) refl ⟩
  H ↑ • (S^ a • Ex) • (S^ (- a⁻¹) • H ^ 3 • CZ^ (- a)) • H • S^ (a⁻¹ + -b/a) ≈⟨  special-assoc (□ • □ ^ 2 • □ ^ 3 • □) (□ ^ 2 • □ ^ 2 • □ ^ 2 • □) auto ⟩
  (H ↑ • S^ a) • (Ex • S^ (- a⁻¹)) • (H ^ 3 • CZ^ (- a)) • H • S^ (a⁻¹ + -b/a) ≈⟨ cright cong (lemma-Ex-S^ᵏ (- a⁻¹)) (cright (cright refl' (Eq.cong S^ aux))) ⟩
  (H ↑ • S^ a) • (S^ (- a⁻¹) ↑ • Ex) • (H ^ 3 • CZ^ (- a)) • H • S^ (- (b + - ₁) * a⁻¹) ≈⟨ cright special-assoc (□ ^ 2 • □ ^ 2 • □) (□ • □ ^ 2 • □ ^ 2) auto ⟩
  (H ↑ • S^ a) • S^ (- a⁻¹) ↑ • (Ex • H ^ 3) • CZ^ (- a) • H • S^ (- (b + - ₁) * a⁻¹) ≈⟨ cright cright cleft rewrite-swap 100 auto ⟩
  (H ↑ • S^ a) • S^ (- a⁻¹) ↑ • (H ↑ ^ 3 • Ex) • CZ^ (- a) • H • S^ (- (b + - ₁) * a⁻¹) ≈⟨ cleft sym (lemma-comm-Sᵏ-w↑ (toℕ a) H) ⟩
  (S^ a • H ↑) • S^ (- a⁻¹) ↑ • (H ↑ ^ 3 • Ex) • CZ^ (- a) • H • S^ (- (b + - ₁) * a⁻¹) ≈⟨ special-assoc (□ ^ 2 • □ • □ ^ 2 • □ ^ 3) (□ • □ ^ 3 • □ ^ 4) auto ⟩
  S^ a • (H ↑ • S^ (- a⁻¹) ↑ • H ↑ ^ 3) • Ex • CZ^ (- a) • H • S^ (- (b + - ₁) * a⁻¹) ≈⟨ refl ⟩

  S^ a • (H ↑ • S^ (- a⁻¹) ↑ • H ↑ ^ 3) • [ a , b + - ₁ ]ᵈ ≈⟨  cright refl ⟩
  S^ e • dir ↑ • [ d' ]ᵈ ∎
  where
  ed = dir-of d g neq
  e = ed .proj₁
  dir = ed .proj₂
  d' = d'-of d g neq
  a⁻¹ = ((a , λ ()) ⁻¹) .proj₁
  -b/a = - b * a⁻¹
  aux : a⁻¹ + -b/a ≡ - (b + - ₁) * a⁻¹
  aux = Eq.trans (Eq.cong (_+ -b/a) (Eq.sym (*-identityˡ a⁻¹))) (Eq.trans (Eq.sym (*-distribʳ-+ a⁻¹ ₁ (- b))) (Eq.trans (Eq.cong (_* a⁻¹) (+-comm ₁ (- b))) (Eq.trans (Eq.cong (_* a⁻¹) (Eq.cong (- b +_) (Eq.sym (-‿involutive ₁)))) (Eq.cong (_* a⁻¹) ( (-‿+-comm b (- ₁)))))))


lemma-D-br d@(a@₀ , b@₀) g@CZ-gen neq = begin
  (Ex • CZ^ (- b)) • CZ ≈⟨ assoc ⟩
  Ex • CZ^ (- b) • CZ ≈⟨ cright lemma-CZ^k+l (- b) ₁ ⟩
  Ex • CZ^ (- b + ₁) ≈⟨ cright refl' (Eq.cong CZ^ (Eq.sym (Eq.trans (Eq.sym (-‿+-comm b (- ₁))) (Eq.trans (Eq.cong (- b +_) (-‿involutive ₁)) auto)))) ⟩
  Ex • CZ^ (- (b + - ₁)) ≈⟨ sym (trans left-unit left-unit) ⟩
  S^ e • dir ↑ • [ d' ]ᵈ ∎
  where
  ed = dir-of d g neq
  e = ed .proj₁
  dir = ed .proj₂
  d' = d'-of d g neq

lemma-D-br d@(a@₀ , b@(₁₊ _)) g@CZ-gen neq = begin
  (Ex • CZ^ (- b)) • CZ ≈⟨ assoc ⟩
  Ex • CZ^ (- b) • CZ ≈⟨ cright lemma-CZ^k+l (- b) ₁ ⟩
  Ex • CZ^ (- b + ₁) ≈⟨ cright refl' (Eq.cong CZ^ (Eq.sym (Eq.trans (Eq.sym (-‿+-comm b (- ₁))) (Eq.trans (Eq.cong (- b +_) (-‿involutive ₁)) auto)))) ⟩
  Ex • CZ^ (- (b + - ₁)) ≈⟨ sym (trans left-unit left-unit) ⟩
  S^ e • dir ↑ • [ d' ]ᵈ ∎
  where
  ed = dir-of d g neq
  e = ed .proj₁
  dir = ed .proj₂
  d' = d'-of d g neq


lemma-D-br d@(a@₀ , b@₀) g@(S-gen ↥) neq = begin
  (Ex • CZ^ (- b)) • S ↑ ≈⟨ assoc ⟩
  Ex • CZ^ (- b) • S ↑ ≈⟨ cright word-comm (toℕ (- b)) 1 (axiom comm-CZ-S↑) ⟩
  Ex • S ↑ • CZ^ (- b) ≈⟨ sym assoc ⟩
  (Ex • S ↑) • CZ^ (- b) ≈⟨ cleft lemma-Ex-S↑ ⟩
  (S • Ex) • CZ^ (- b) ≈⟨ assoc ⟩
  S • Ex • CZ^ (- b) ≈⟨ sym (cong refl left-unit) ⟩
  S^ e • dir ↑ • [ d' ]ᵈ ∎
  where
  ed = dir-of d g neq
  e = ed .proj₁
  dir = ed .proj₂
  d' = d'-of d g neq

lemma-D-br d@(a@₀ , b@(₁₊ _)) g@(S-gen ↥) neq = begin
  (Ex • CZ^ (- b)) • S ↑ ≈⟨ assoc ⟩
  Ex • CZ^ (- b) • S ↑ ≈⟨ cright word-comm (toℕ (- b)) 1 (axiom comm-CZ-S↑) ⟩
  Ex • S ↑ • CZ^ (- b) ≈⟨ sym assoc ⟩
  (Ex • S ↑) • CZ^ (- b) ≈⟨ cleft lemma-Ex-S↑ ⟩
  (S • Ex) • CZ^ (- b) ≈⟨ assoc ⟩
  S • Ex • CZ^ (- b) ≈⟨ sym (cong refl left-unit) ⟩
  S^ e • dir ↑ • [ d' ]ᵈ ∎
  where
  ed = dir-of d g neq
  e = ed .proj₁
  dir = ed .proj₂
  d' = d'-of d g neq


lemma-D-br d@(a@(₁₊ _) , b@₀) g@(S-gen ↥) neq = begin
  (Ex • CZ^ (- a) • (H • S^ -b/a)) • S ↑ ≈⟨ special-assoc (□ ^ 3 • □) (□ ^ 2 • □ ^ 2) auto ⟩
  (Ex • CZ^ (- a)) • (H • S^ -b/a) • S ↑ ≈⟨ cright comm-hs-w↑ -b/a S ⟩
  (Ex • CZ^ (- a)) • S ↑ • (H • S^ -b/a) ≈⟨ special-assoc (□ ^ 2 • □ ^ 2) (□ • □ ^ 2 • □) auto ⟩
  Ex • (CZ^ (- a) • S ↑) • (H • S^ -b/a) ≈⟨ cright cleft word-comm (toℕ (- a)) 1 (axiom comm-CZ-S↑) ⟩
  Ex • (S ↑ • CZ^ (- a)) • (H • S^ -b/a) ≈⟨ sym (special-assoc (□ ^ 2 • □ ^ 2) (□ • □ ^ 2 • □) auto) ⟩
  (Ex • S ↑) • CZ^ (- a) • (H • S^ -b/a) ≈⟨ cleft lemma-Ex-S↑ ⟩
  (S • Ex) • CZ^ (- a) • (H • S^ -b/a) ≈⟨ assoc ⟩
  S • Ex • CZ^ (- a) • (H • S^ -b/a) ≈⟨ sym (cong refl left-unit) ⟩
  S^ e • dir ↑ • [ d' ]ᵈ ∎
  where
  ed = dir-of d g neq
  e = ed .proj₁
  dir = ed .proj₂
  d' = d'-of d g neq
  a⁻¹ = ((a , λ ()) ⁻¹) .proj₁
  -b/a = - b * a⁻¹

lemma-D-br d@(a@(₁₊ _) , b@(₁₊ _)) g@(S-gen ↥) neq = begin
  (Ex • CZ^ (- a) • (H • S^ -b/a)) • S ↑ ≈⟨ special-assoc (□ ^ 3 • □) (□ ^ 2 • □ ^ 2) auto ⟩
  (Ex • CZ^ (- a)) • (H • S^ -b/a) • S ↑ ≈⟨ cright comm-hs-w↑ -b/a S ⟩
  (Ex • CZ^ (- a)) • S ↑ • (H • S^ -b/a) ≈⟨ special-assoc (□ ^ 2 • □ ^ 2) (□ • □ ^ 2 • □) auto ⟩
  Ex • (CZ^ (- a) • S ↑) • (H • S^ -b/a) ≈⟨ cright cleft word-comm (toℕ (- a)) 1 (axiom comm-CZ-S↑) ⟩
  Ex • (S ↑ • CZ^ (- a)) • (H • S^ -b/a) ≈⟨ sym (special-assoc (□ ^ 2 • □ ^ 2) (□ • □ ^ 2 • □) auto) ⟩
  (Ex • S ↑) • CZ^ (- a) • (H • S^ -b/a) ≈⟨ cleft lemma-Ex-S↑ ⟩
  (S • Ex) • CZ^ (- a) • (H • S^ -b/a) ≈⟨ assoc ⟩
  S • Ex • CZ^ (- a) • (H • S^ -b/a) ≈⟨ sym (cong refl left-unit) ⟩
  S^ e • dir ↑ • [ d' ]ᵈ ∎
  where
  ed = dir-of d g neq
  e = ed .proj₁
  dir = ed .proj₂
  d' = d'-of d g neq
  a⁻¹ = ((a , λ ()) ⁻¹) .proj₁
  -b/a = - b * a⁻¹



lemma-D-br d@(a@₀ , b@₀) g@S-gen neq = begin
  (Ex • CZ^ (- b)) • S  ≈⟨ assoc ⟩
  Ex • CZ^ (- b) • S  ≈⟨ cright word-comm (toℕ (- b)) 1 (axiom comm-CZ-S↓) ⟩
  Ex • S  • CZ^ (- b) ≈⟨ sym assoc ⟩
  (Ex • S ) • CZ^ (- b) ≈⟨ cleft lemma-Ex-S ⟩
  (S ↑ • Ex) • CZ^ (- b) ≈⟨ assoc ⟩
  S ↑ • Ex • CZ^ (- b) ≈⟨ sym left-unit ⟩
  S^ e • dir ↑ • [ a , b ]ᵈ ≈⟨ cright cright refl' (Eq.cong (\ xx -> [ a , xx ]ᵈ) (Eq.sym (Eq.trans (Eq.cong (b +_) -0#≈0#) (+-identityʳ b)))) ⟩
  S^ e • dir ↑ • [ a , b + - a ]ᵈ ∎
  where
  ed = dir-of d g neq
  e = ed .proj₁
  dir = ed .proj₂
  d' = d'-of d g neq

lemma-D-br d@(a@₀ , b@(₁₊ _)) g@S-gen neq = begin
  (Ex • CZ^ (- b)) • S  ≈⟨ assoc ⟩
  Ex • CZ^ (- b) • S  ≈⟨ cright word-comm (toℕ (- b)) 1 (axiom comm-CZ-S↓) ⟩
  Ex • S  • CZ^ (- b) ≈⟨ sym assoc ⟩
  (Ex • S ) • CZ^ (- b) ≈⟨ cleft lemma-Ex-S ⟩
  (S ↑ • Ex) • CZ^ (- b) ≈⟨ assoc ⟩
  S ↑ • Ex • CZ^ (- b) ≈⟨ sym left-unit ⟩
  S^ e • dir ↑ • [ a , b ]ᵈ ≈⟨ cright cright refl' (Eq.cong (\ xx -> [ a , xx ]ᵈ) (Eq.sym (Eq.trans (Eq.cong (b +_) -0#≈0#) (+-identityʳ b)))) ⟩
  S^ e • dir ↑ • [ d' ]ᵈ ∎
  where
  ed = dir-of d g neq
  e = ed .proj₁
  dir = ed .proj₂
  d' = d'-of d g neq


lemma-D-br d@(a@(₁₊ _) , b@₀) g@(S-gen) neq = begin
  (Ex • CZ^ (- a) • (H • S^ -b/a)) • S ≈⟨ special-assoc (□ ^ 4 • □) (□ ^ 3 • □ ^ 2) auto ⟩
  (Ex • CZ^ (- a) • H) • S^ -b/a • S ≈⟨ cright L01.lemma-S^k+l -b/a ₁ ⟩
  (Ex • CZ^ (- a) • H) • S^ (-b/a + ₁) ≈⟨ cright refl' (Eq.cong S^ (aux--b/a+₁ (a , (λ ())) b)) ⟩
  (Ex • CZ^ (- a) • H) • S^ (- (b + - a) * a⁻¹) ≈⟨ special-assoc (□ ^ 3 • □) (□ ^ 4) auto ⟩
  Ex • CZ^ (- a) • H • S^ (- (b + - a) * a⁻¹) ≈⟨ sym (trans left-unit left-unit) ⟩
  S^ e • dir ↑ • [ d' ]ᵈ ∎
  where
  ed = dir-of d g neq
  e = ed .proj₁
  dir = ed .proj₂
  d' = d'-of d g neq
  nz' = aux-a≠0⇒ab≠0 a (b + - a) λ ()
  a⁻¹ = ((a , λ ()) ⁻¹) .proj₁
  -b/a = - b * a⁻¹

lemma-D-br d@(a@(₁₊ _) , b@(₁₊ _)) g@(S-gen) neq = begin
  (Ex • CZ^ (- a) • (H • S^ -b/a)) • S ≈⟨ special-assoc (□ ^ 4 • □) (□ ^ 3 • □ ^ 2) auto ⟩
  (Ex • CZ^ (- a) • H) • S^ -b/a • S ≈⟨ cright L01.lemma-S^k+l -b/a ₁ ⟩
  (Ex • CZ^ (- a) • H) • S^ (-b/a + ₁) ≈⟨ cright refl' (Eq.cong S^ (aux--b/a+₁ (a , (λ ())) b)) ⟩
  (Ex • CZ^ (- a) • H) • S^ (- (b + - a) * a⁻¹) ≈⟨ special-assoc (□ ^ 3 • □) (□ ^ 4) auto ⟩
  Ex • CZ^ (- a) • H • S^ (- (b + - a) * a⁻¹) ≈⟨ sym (trans left-unit left-unit) ⟩
  S^ e • dir ↑ • [ d' ]ᵈ ∎
  where
  ed = dir-of d g neq
  e = ed .proj₁
  dir = ed .proj₂
  d' = d'-of d g neq
  nz' = aux-a≠0⇒ab≠0 a (b + - a) λ ()
  a⁻¹ = ((a , λ ()) ⁻¹) .proj₁
  -b/a = - b * a⁻¹


lemma-D-br d@(a@₀ , b@₀) g@(H-gen) neq = begin
  (Ex • CZ^ (- b)) • H ≈⟨ assoc ⟩
  Ex • CZ^ (- b) • H ≈⟨ cright cleft refl' (Eq.cong CZ^ -0#≈0#) ⟩
  Ex • ε • H ≈⟨ cong refl left-unit ⟩
  Ex • H ≈⟨ lemma-Ex-H ⟩
  H ↑ • Ex ≈⟨ cright sym right-unit ⟩
  H ↑ • Ex • ε ≈⟨ cright cright sym (refl' (Eq.cong CZ^ -0#≈0#)) ⟩
  H ↑ • Ex • CZ^ (- b) ≈⟨ sym left-unit ⟩
  S^ e • dir ↑ • [ ₀ , b ]ᵈ ≈⟨ cright cright refl' (Eq.cong (\ xx -> [ ₀ , xx ]ᵈ) (Eq.sym -0#≈0#) )  ⟩
  S^ e • dir ↑ • [ b , - a ]ᵈ ∎
  where
  ed = dir-of d g neq
  e = ed .proj₁
  dir = ed .proj₂
  d' = d'-of d g neq


lemma-D-br d@(a@₀ , b@(₁₊ _)) g@(H-gen) neq = begin
  (Ex • CZ^ (- b)) • H ≈⟨ assoc ⟩
  Ex • CZ^ (- b) • H ≈⟨ cright cright sym right-unit ⟩
  Ex • CZ^ (- b) • H • S^ ₀ ≈⟨ cright cright cright refl' (Eq.cong S^ (Eq.sym (Eq.trans (Eq.cong (_* b⁻¹) -0#≈0#) (*-zeroˡ b⁻¹)))) ⟩
  Ex • CZ^ (- b) • H • S^ (- ₀ * b⁻¹) ≈⟨ sym (trans left-unit left-unit) ⟩
  S^ e • dir ↑ • [ b , ₀ ]ᵈ ≈⟨ cright cright refl' (Eq.cong (\ xx -> [ b , xx ]ᵈ) (Eq.sym -0#≈0#) )  ⟩
  S^ e • dir ↑ • [ b , - a ]ᵈ ∎
  where
  ed = dir-of d g neq
  e = ed .proj₁
  dir = ed .proj₂
  d' = d'-of d g neq
  b⁻¹ = ((b , λ ()) ⁻¹) .proj₁


lemma-D-br d@(a@(₁₊ _) , b@₀) g@(H-gen) neq = begin
  (Ex • CZ^ (- a) • (H • S^ -b/a)) • H ≈⟨ cleft cright cright cright sym (refl' (Eq.cong S^ (Eq.sym (Eq.trans (Eq.cong (_* a⁻¹) -0#≈0#) (*-zeroˡ a⁻¹))))) ⟩
  (Ex • CZ^ (- a) • H • S^ ₀) • H ≈⟨ cleft cright cright right-unit ⟩
  (Ex • CZ^ (- a) • H) • H ≈⟨ special-assoc (□ ^ 3 • □) (□ ^ 4) auto ⟩
  Ex • CZ^ (- a) • H • H ≈⟨ cright sym (lemma-semi-HH↓-CZ^k' a) ⟩
  Ex • HH • CZ^ a ≈⟨ sym assoc ⟩
  (Ex • HH) • CZ^ a ≈⟨ cleft rewrite-swap 100 auto ⟩
  (HH ↑ • Ex) • CZ^ a ≈⟨ cright refl' (Eq.cong CZ^ (Eq.sym (-‿involutive a))) ⟩
  (HH ↑ • Ex) • CZ^ (- - a) ≈⟨ assoc ⟩
  HH ↑ • Ex • CZ^ (- - a) ≈⟨ sym left-unit ⟩
  S^ e • dir ↑ • [ d' ]ᵈ ∎
  where
  ed = dir-of d g neq
  e = ed .proj₁
  dir = ed .proj₂
  d' = d'-of d g neq
  nz' = aux-b≠0⇒ab≠0 ₀ (- a) ((-' (a , λ ())) .proj₂)
  a⁻¹ = ((a , λ ()) ⁻¹) .proj₁
  -b/a = - b * a⁻¹



lemma-D-br d@(a@(₁₊ _) , b@(₁₊ _)) g@(H-gen) neq = begin
  (Ex • CZ^ (- a) • (H • S^ -b/a)) • H ≈⟨ special-assoc (□ ^ 4 • □) (□ ^ 5) auto ⟩
  Ex • CZ^ (- a) • H • S^ -b/a • H ≈⟨ cright cright lemma-Euler′ k* ⟩
  Ex • CZ^ (- a) • ZM (-' k* ⁻¹) • (S^ (- k) • H • S^ (-k⁻¹)) ≈⟨ cright sym assoc ⟩
  Ex • (CZ^ (- a) • ZM (-' k* ⁻¹)) • (S^ (- k) • H • S^ (-k⁻¹)) ≈⟨ cright cleft lemma-CZ^kM↓ -k⁻¹ (- a) ((-' k* ⁻¹) .proj₂) ⟩
  Ex • (ZM (-' k* ⁻¹) • CZ^ (- a * l)) • (S^ (- k) • H • S^ (-k⁻¹)) ≈⟨ special-assoc (□ • □ ^ 2 • □ ^ 3) (□ ^ 2 • □ ^ 2 • □ ^ 2) auto ⟩
  (Ex • ZM (-' k* ⁻¹)) • (CZ^ (- a * l) • S^ (- k)) • H • S^ (-k⁻¹) ≈⟨ cong (lemma-Ex-M (-' k* ⁻¹)) (cleft word-comm (toℕ (- a * l)) (toℕ (- k)) (axiom comm-CZ-S↓)) ⟩
  (ZM (-' k* ⁻¹) ↑ • Ex) • (S^ (- k) • CZ^ (- a * l)) • H • S^ (-k⁻¹) ≈⟨ special-assoc (□ ^ 2 • □ ^ 2 • □) (□ • □ ^ 2 • □ ^ 2) auto ⟩
  ZM (-' k* ⁻¹) ↑ • (Ex • S^ (- k)) • CZ^ (- a * l) • H • S^ (-k⁻¹) ≈⟨ cright cleft lemma-Ex-S^ᵏ (- k) ⟩
  ZM (-' k* ⁻¹) ↑ • (S^ (- k) ↑ • Ex) • CZ^ (- a * l) • H • S^ (-k⁻¹) ≈⟨ special-assoc (□ • □ ^ 2 • □) (□ ^ 2 • □ ^ 2) auto ⟩
  (ZM (-' k* ⁻¹) ↑ • S^ (- k) ↑) • Ex • CZ^ (- a * l) • H • S^ (-k⁻¹) ≈⟨ cong (cong (lemma-cong↑ _ _ (aux-MM ((-' k* ⁻¹) .proj₂) (a/b .proj₂) (c4 .proj₁))) (refl' (Eq.cong (\ xx -> S^ xx ↑) (c4 .proj₂ .proj₁)))) (cright cong (refl' (Eq.cong CZ^ (c4 .proj₂ .proj₂ .proj₁))) (cright refl' (Eq.cong S^ (c4 .proj₂ .proj₂ .proj₂)))) ⟩
  (ZM a/b ↑ • S^ b/a ↑) • Ex • CZ^ (- b) • H • S^ (- - a * b⁻¹) ≈⟨ sym left-unit ⟩
  S^ e • dir ↑ • [ d' ]ᵈ ∎
  where
  ed = dir-of d g neq
  e = ed .proj₁
  dir = ed .proj₂
  d' = d'-of d g neq
  nz' = aux-b≠0⇒ab≠0 ₀ (- a) ((-' (a , λ ())) .proj₂)
  a⁻¹ = ((a , λ ()) ⁻¹) .proj₁
  b⁻¹ = ((b , λ ()) ⁻¹) .proj₁
  -b/a = - b * a⁻¹
  b/a = b * a⁻¹
  a/b = (a , λ ()) *' (b , λ ()) ⁻¹
  k = -b/a
  k* = -' (b , λ ()) *' (a , λ ()) ⁻¹
  -k⁻¹ = - ((k* ⁻¹) .proj₁)
  l = ((-' k* ⁻¹) ⁻¹) .proj₁
  c4 = aux--k⁻¹ (a , λ ()) (b , λ ())



