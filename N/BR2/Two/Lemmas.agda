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



module N.BR2.Two.Lemmas (p-2 : ℕ) (p-prime : Prime (2+ p-2)) where

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
open import N.Lemmas-2Qupit-Sym3 p-2 p-prime
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
open import N.BR2.Calculations p-2 p-prime
open import N.BR2.One.A p-2 p-prime


open PB ((₂₊ n) QRel,_===_)
open PP ((₂₊ n) QRel,_===_)
open SR word-setoid
open Pattern-Assoc
sa = special-assoc
open Lemmas0 n
module L01 = Lemmas0 (₁₊ n)
open Lemmas-2Q n
open Sym0-Rewriting (₁₊ n)
open Symplectic-GroupLike
open Basis-Change _ ((₂₊ n) QRel,_===_) grouplike

open Rewriting-Swap 1

_^ᵖ_ : ∀ {X : Set} -> Word X -> ℤ ₚ -> Word X
_^ᵖ_ {X} w k = w ^ toℕ k

open import Data.Nat.DivMod
open import Data.Fin.Properties



lemma-S^k*l : ∀ k l -> S^ k ^ᵖ l ≈ S^ (k * l)
lemma-S^k*l k l = begin
  S^ k ^ᵖ l ≈⟨ refl ⟩
  (S ^ toℕ k) ^ toℕ l ≈⟨ lemma-^^ S (toℕ k) (toℕ l) ⟩
  S ^ (toℕ k Nat.* toℕ l) ≡⟨ Eq.cong (S ^_) (m≡m%n+[m/n]*n k*l p) ⟩
  S ^ (k*l Nat.% p Nat.+ (k*l Nat./ p) Nat.* p) ≈⟨ lemma-^-+ S (k*l Nat.% p) (((k*l Nat./ p) Nat.* p)) ⟩
  S ^ (k*l Nat.% p) • S ^ ((k*l Nat./ p) Nat.* p) ≈⟨ cong (refl' (Eq.cong (S ^_) (Eq.sym (toℕ-fromℕ< (m%n<n k*l p))))) (refl' (Eq.cong (S ^_) (NP.*-comm ((k*l Nat./ p)) p))) ⟩
  S ^ toℕ (fromℕ< (m%n<n k*l p)) • S ^ (p Nat.* (k*l Nat./ p) ) ≈⟨ cong (sym (refl)) (sym (lemma-^^ S p (k*l Nat./ p))) ⟩
  S^ (k * l) • (S ^ p) ^ (k*l Nat./ p) ≈⟨ cright (lemma-^-cong (S ^ p) ε (k*l Nat./ p) (axiom order-S)) ⟩
  S^ (k * l) • ε ^ (k*l Nat./ p) ≈⟨ cright lemma-ε^k=ε (k*l Nat./ p) ⟩
  S^ (k * l) • ε ≈⟨ right-unit ⟩
  S^ (k * l) ∎
  where
  k*l = toℕ k Nat.* toℕ l

lemma-CZ^k*l : ∀ k l -> CZ^ k ^ᵖ l ≈ CZ^ (k * l)
lemma-CZ^k*l k l = begin
  CZ^ k ^ᵖ l ≈⟨ refl ⟩
  (CZ ^ toℕ k) ^ toℕ l ≈⟨ lemma-^^ CZ (toℕ k) (toℕ l) ⟩
  CZ ^ (toℕ k Nat.* toℕ l) ≡⟨ Eq.cong (CZ ^_) (m≡m%n+[m/n]*n k*l p) ⟩
  CZ ^ (k*l Nat.% p Nat.+ (k*l Nat./ p) Nat.* p) ≈⟨ lemma-^-+ CZ (k*l Nat.% p) (((k*l Nat./ p) Nat.* p)) ⟩
  CZ ^ (k*l Nat.% p) • CZ ^ ((k*l Nat./ p) Nat.* p) ≈⟨ cong (refl' (Eq.cong (CZ ^_) (Eq.sym (toℕ-fromℕ< (m%n<n k*l p))))) (refl' (Eq.cong (CZ ^_) (NP.*-comm ((k*l Nat./ p)) p))) ⟩
  CZ ^ toℕ (fromℕ< (m%n<n k*l p)) • CZ ^ (p Nat.* (k*l Nat./ p) ) ≈⟨ cong (sym (refl)) (sym (lemma-^^ CZ p (k*l Nat./ p))) ⟩
  CZ^ (k * l) • (CZ ^ p) ^ (k*l Nat./ p) ≈⟨ cright (lemma-^-cong (CZ ^ p) ε (k*l Nat./ p) (axiom order-CZ)) ⟩
  CZ^ (k * l) • ε ^ (k*l Nat./ p) ≈⟨ cright lemma-ε^k=ε (k*l Nat./ p) ⟩
  CZ^ (k * l) • ε ≈⟨ right-unit ⟩
  CZ^ (k * l) ∎
  where
  k*l = toℕ k Nat.* toℕ l

aux-CZ⁻¹^k-CZ^-k : ∀ (k : ℤ ₚ) -> CZ⁻¹ ^ toℕ k ≈ CZ ^ toℕ (- k)
aux-CZ⁻¹^k-CZ^-k k = begin
  CZ⁻¹ ^ toℕ k ≈⟨ sym (lemma-^-cong _ _ (toℕ k) (refl' (Eq.cong (CZ ^_) lemma-toℕ-1ₚ))) ⟩
  CZ^ (- ₁) ^ toℕ k ≈⟨ refl ⟩
  CZ^ (- ₁) ^ᵖ k ≈⟨ lemma-CZ^k*l (- ₁) k  ⟩
  CZ^ (- ₁ * k)  ≈⟨ refl' (Eq.cong CZ^ (-1*x≈-x k)) ⟩
  CZ^ (- k) ≈⟨ refl ⟩
  CZ ^ toℕ (- k) ∎

aux-Ex-CX^k-N : ∀ k -> Ex • CX ^ k ≈ XC ^ k • Ex
aux-Ex-CX^k-N k@0 = trans right-unit (sym left-unit)
aux-Ex-CX^k-N k@1 = rewrite-swap 100 auto
aux-Ex-CX^k-N k@(₁₊ k'@(₁₊ k'')) = begin
  Ex • CX ^ k ≈⟨ sym assoc ⟩
  (Ex • CX) • CX ^ k' ≈⟨ cleft rewrite-swap 100 auto ⟩
  (XC • Ex) • CX ^ k' ≈⟨ assoc ⟩
  XC • Ex • CX ^ k' ≈⟨ cright aux-Ex-CX^k-N k' ⟩
  XC • XC ^ k' • Ex ≈⟨ sym assoc ⟩
  XC ^ k • Ex ∎



aux-Ex-CX^k : ∀ k -> Ex • CX^ k ≈ XC^ k • Ex
aux-Ex-CX^k k = aux-Ex-CX^k-N (toℕ k)

aux-Ex-XC^k : ∀ k -> Ex • XC^ k ≈ CX^ k • Ex
aux-Ex-XC^k k = bbc Ex Ex claim
  where
  claim : Ex • (Ex • XC^ k) • Ex ≈ Ex • (CX^ k • Ex) • Ex
  claim = begin
    Ex • (Ex • XC^ k) • Ex ≈⟨ by-assoc auto ⟩
    (Ex • Ex) • XC^ k • Ex ≈⟨ cleft rewrite-swap 100 auto ⟩
    ε • XC^ k • Ex ≈⟨ left-unit ⟩
    XC^ k • Ex ≈⟨ sym (aux-Ex-CX^k k) ⟩
    Ex • CX^ k ≈⟨ cong refl (sym right-unit) ⟩
    Ex • CX^ k • ε ≈⟨ cright cright rewrite-swap 100 auto ⟩
    Ex • CX^ k • Ex • Ex ≈⟨ sym (cong refl assoc) ⟩
    Ex • (CX^ k • Ex) • Ex ∎


aux-XC^-XC'^-N : ∀ k -> XC ^ k ≈ H ↑ ^ 3 • CZ ^ k • H ↑
aux-XC^-XC'^-N k@0 = rewrite-swap 100 auto
aux-XC^-XC'^-N k@1 = refl
aux-XC^-XC'^-N k@(₁₊ k'@(₁₊ k'')) = begin
  XC ^ k ≈⟨ refl ⟩
  XC • XC ^ k' ≈⟨ cright aux-XC^-XC'^-N k' ⟩
  XC • H ↑ ^ 3 • CZ ^ k' • H ↑ ≈⟨ sym assoc ⟩
  (XC • H ↑ ^ 3) • CZ ^ k' • H ↑ ≈⟨ cleft rewrite-sym0 100 auto  ⟩
  (H ↑ ^ 3 • CZ) • CZ ^ k' • H ↑ ≈⟨ special-assoc (□ ^ 2 • □ ^ 2) (□ • □ ^ 2 • □) auto ⟩
  H ↑ ^ 3 • (CZ • CZ ^ k') • H ↑ ≈⟨ refl ⟩
  H ↑ ^ 3 • CZ ^ k • H ↑ ∎

aux-CX^-CX'^-N : ∀ k -> CX ^ k ≈ H ^ 3 • CZ ^ k • H
aux-CX^-CX'^-N k@0 = rewrite-sym0 100 auto
aux-CX^-CX'^-N k@1 = refl
aux-CX^-CX'^-N k@(₁₊ k'@(₁₊ k'')) = begin
  CX ^ k ≈⟨ refl ⟩
  CX • CX ^ k' ≈⟨ cright aux-CX^-CX'^-N k' ⟩
  CX • H ^ 3 • CZ ^ k' • H ≈⟨ sym assoc ⟩
  (CX • H ^ 3) • CZ ^ k' • H ≈⟨ cleft rewrite-sym0 100 auto  ⟩
  (H ^ 3 • CZ) • CZ ^ k' • H ≈⟨ special-assoc (□ ^ 2 • □ ^ 2) (□ • □ ^ 2 • □) auto ⟩
  H ^ 3 • (CZ • CZ ^ k') • H ≈⟨ refl ⟩
  H ^ 3 • CZ ^ k • H ∎





aux-XC^-XC'^ : ∀ k -> XC^ k ≈ XC'^ k
aux-XC^-XC'^ k = aux-XC^-XC'^-N (toℕ k)

aux-CX^-CX'^ : ∀ k -> CX^ k ≈ CX'^ k
aux-CX^-CX'^ k = aux-CX^-CX'^-N (toℕ k)

open import N.Duality p-2 p-prime
open Duality

lemma-semi-XCCZ^k : ∀ (k*@(k , nz) : ℤ* ₚ) ->
  let
    -2k : ℤ ₚ
    -2k = - k + - k
  in

  XC • CZ^ k ≈ S^ -2k • CZ^ k • XC
lemma-semi-XCCZ^k k*@(k , nz) = by-duality' (lemma-semi-CXCZ^k k*) c1 c2
  where
  -2k : ℤ ₚ
  -2k = - k + - k
  c1 : dual (CX • CZ^ k) ≈ XC • CZ^ k
  c1 = cright refl' (aux-dual-CZ^k (toℕ k))
  c2 : dual (S^ -2k ↑ • CZ^ k • CX) ≈ S^ -2k • CZ^ k • XC
  c2 = begin
    dual (S^ -2k ↑ • CZ^ k • CX) ≈⟨ cong (refl' (aux-dual-S^k↑ (toℕ -2k))) (cleft refl' (aux-dual-CZ^k (toℕ k))) ⟩
    S^ -2k • CZ^ k • XC ∎

aux-CZ-H↑-CZ^k : ∀ (k*@(k , nz) : ℤ* ₚ) ->
  let -2k = - k + - k in
  
  CZ • H ↑ • CZ^ k ≈ (S^ -2k • H ↑ • CZ^ k • H ↑ ^ 3) • CZ • H ↑

aux-CZ-H↑-CZ^k k*@(k , nz) = begin
  CZ • H ↑ • CZ^ k ≈⟨ sym assoc ⟩
  (CZ • H ↑) • CZ^ k ≈⟨ cleft rewrite-sym0 100 auto ⟩
  (H ↑ • XC) • CZ^ k ≈⟨ assoc ⟩
  H ↑ • XC • CZ^ k ≈⟨ cright lemma-semi-XCCZ^k k* ⟩
  H ↑ • S^ -2k • CZ^ k • XC ≈⟨ sym assoc ⟩
  (H ↑ • S^ -2k) • CZ^ k • XC ≈⟨ cleft sym (lemma-comm-Sᵏ-w↑ (toℕ -2k) H) ⟩
  (S^ -2k • H ↑) • CZ^ k • XC ≈⟨ special-assoc (□ ^ 2 • □ ^ 4) (□ ^ 4 • □ ^ 2) auto ⟩
  (S^ -2k • H ↑ • CZ^ k • H ↑ ^ 3) • CZ • H ↑ ∎
  where
  -2k : ℤ ₚ
  -2k = - k + - k


aux-CZ⁻¹-H-CZ^k : ∀ k -> CZ^ (- ₁) • H • CZ^ k ≈ H • S^ k ↑ • S^ (- k) • CX^ (- ₁) • S^ k
aux-CZ⁻¹-H-CZ^k k = bbc (H ^ 5) ε claim
  where
  claim : H ^ 5 • (CZ^ (- ₁) • H • CZ^ k) • ε ≈ H ^ 5 • (H • S^ k ↑ • S^ (- k) • CX^ (- ₁) • S^ k) • ε
  claim = begin
    H ^ 5 • (CZ^ (- ₁) • H • CZ^ k) • ε ≈⟨ cong refl right-unit ⟩
    H ^ 5 • (CZ^ (- ₁) • H • CZ^ k) ≈⟨ sa (□ ^ 5 • □ ^ 3) (□ ^ 3 • (□ ^ 2 • □) • □ ^ 2) auto ⟩
    H ^ 3 • (H ^ 2 • CZ^ (- ₁)) • H • CZ^ k ≈⟨ cright cleft lemma-semi-CZ-HH↓' ⟩
    H ^ 3 • (CZ • H ^ 2) • H • CZ^ k ≈⟨ cright sa (□ ^ 3 • □ ^ 2) (□ ^ 2 • □ ^ 2 • □) auto ⟩
    H ^ 3 • (CZ • H) • H ^ 2 • CZ^ k ≈⟨ cright cright lemma-semi-HH↓-CZ^k' k ⟩
    H ^ 3 • (CZ • H) • CZ^ (- k) • H ^ 2 ≈⟨ sa (□ • □ ^ 2 • □ ^ 2) ((□ ^ 3 • □) • □) auto ⟩
    (CX • CZ^ (- k)) • H ^ 2 ≈⟨ cleft lemma-semi-CXCZ^-alt (- k) ⟩
    (S^ (- k) • CX • S^ (- - k) • S^ (- - k) ↑) • H ^ 2 ≈⟨ cleft cright (cright refl' (Eq.cong (\ xx -> S^ xx • S^ xx ↑) (-‿involutive k))) ⟩
    (S^ (- k) • CX • S^ k • S^ k ↑) • H ^ 2 ≈⟨ cleft cright cright lemma-comm-Sᵏ-w↑ (toℕ k) (S^ k) ⟩
    (S^ (- k) • CX • S^ k ↑ • S^ k) • H ^ 2 ≈⟨ cleft sa (□ ^ 4) (□ • □ ^ 2 • □) auto ⟩
    (S^ (- k) • (CX • S^ k ↑) • S^ k) • H ^ 2 ≈⟨ cleft cright cleft aux-comm-CX-S^k↑ k ⟩
    (S^ (- k) • (S^ k ↑ • CX) • S^ k) • H ^ 2 ≈⟨ cleft sym (sa (□ ^ 2 • □ ^ 2) (□ • □ ^ 2 • □) auto) ⟩
    ((S^ (- k) • S^ k ↑) • (CX • S^ k)) • H ^ 2 ≈⟨ cleft cleft lemma-comm-Sᵏ-w↑ (toℕ (- k)) (S^ k) ⟩
    ((S^ k ↑ • S^ (- k)) • (CX • S^ k)) • H ^ 2 ≈⟨ sa (□ ^ 3 • □) (□ ^ 4) auto ⟩
    (S^ k ↑ • S^ (- k)) • CX • S^ k • H ^ 2 ≈⟨ cright cright word-comm (toℕ k) 1 (sym (trans assoc (axiom comm-HHS))) ⟩
    (S^ k ↑ • S^ (- k)) • CX • H ^ 2 • S^ k ≈⟨ sa (□ ^ 4) (□ • □ ^ 2 • □) auto ⟩
    (S^ k ↑ • S^ (- k)) • (CX • H ^ 2) • S^ k ≈⟨ cright cleft sym lemma-semi-HH↓-CX⁻¹ ⟩
    (S^ k ↑ • S^ (- k)) • (H ^ 2 • CX^ (- ₁)) • S^ k ≈⟨ sa (□ ^ 2 • □ ^ 2 • □) (□ • □ ^ 2 • □ ^ 2) auto ⟩
    S^ k ↑ • (S^ (- k) • H ^ 2) • CX^ (- ₁) • S^ k ≈⟨  cright cleft word-comm (toℕ (- k)) 1 (sym (trans assoc (axiom comm-HHS))) ⟩
    S^ k ↑ • (H ^ 2 • S^ (- k)) • CX^ (- ₁) • S^ k ≈⟨ sa (□ • □ ^ 2 • □) (□ ^ 2 • □ ^ 2) auto ⟩
    (S^ k ↑ • H ^ 2) • S^ (- k) • CX^ (- ₁) • S^ k ≈⟨ cleft sym (lemma-comm-Hᵏ-w↑ 2 (S^ k)) ⟩
    (H ^ 2 • S^ k ↑) • S^ (- k) • CX^ (- ₁) • S^ k ≈⟨ assoc ⟩
    H ^ 2 • S^ k ↑ • S^ (- k) • CX^ (- ₁) • S^ k ≈⟨ cleft rewrite-sym0 100 auto ⟩
    H ^ 6 • S^ k ↑ • S^ (- k) • CX^ (- ₁) • S^ k ≈⟨ sa (□ ^ 6 • □) (□ ^ 5 • □ ^ 2) auto ⟩
    H ^ 5 • (H • S^ k ↑ • S^ (- k) • CX^ (- ₁) • S^ k) ≈⟨ cright sym right-unit ⟩
    H ^ 5 • (H • S^ k ↑ • S^ (- k) • CX^ (- ₁) • S^ k) • ε ∎

{-
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



module N.BR2.Two.Lemmas (p-2 : ℕ) (p-prime : Prime (2+ p-2)) where

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
open import N.Lemmas-2Qupit-Sym3 p-2 p-prime
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
open import N.BR2.Calculations p-2 p-prime
open import N.BR2.One.A p-2 p-prime


open PB ((₂₊ n) QRel,_===_)
open PP ((₂₊ n) QRel,_===_)
open SR word-setoid
open Pattern-Assoc
sa = special-assoc
open Lemmas0 n
module L01 = Lemmas0 (₁₊ n)
open Lemmas-2Q n
open Sym0-Rewriting (₁₊ n)
open Symplectic-GroupLike
open Basis-Change _ ((₂₊ n) QRel,_===_) grouplike

open Rewriting-Swap 1

_^ᵖ_ : ∀ {X : Set} -> Word X -> ℤ ₚ -> Word X
_^ᵖ_ {X} w k = w ^ toℕ k

open import Data.Nat.DivMod
open import Data.Fin.Properties



lemma-S^k*l : ∀ k l -> S^ k ^ᵖ l ≈ S^ (k * l)
lemma-S^k*l k l = begin
  S^ k ^ᵖ l ≈⟨ refl ⟩
  (S ^ toℕ k) ^ toℕ l ≈⟨ lemma-^^ S (toℕ k) (toℕ l) ⟩
  S ^ (toℕ k Nat.* toℕ l) ≡⟨ Eq.cong (S ^_) (m≡m%n+[m/n]*n k*l p) ⟩
  S ^ (k*l Nat.% p Nat.+ (k*l Nat./ p) Nat.* p) ≈⟨ lemma-^-+ S (k*l Nat.% p) (((k*l Nat./ p) Nat.* p)) ⟩
  S ^ (k*l Nat.% p) • S ^ ((k*l Nat./ p) Nat.* p) ≈⟨ cong (refl' (Eq.cong (S ^_) (Eq.sym (toℕ-fromℕ< (m%n<n k*l p))))) (refl' (Eq.cong (S ^_) (NP.*-comm ((k*l Nat./ p)) p))) ⟩
  S ^ toℕ (fromℕ< (m%n<n k*l p)) • S ^ (p Nat.* (k*l Nat./ p) ) ≈⟨ cong (sym (refl)) (sym (lemma-^^ S p (k*l Nat./ p))) ⟩
  S^ (k * l) • (S ^ p) ^ (k*l Nat./ p) ≈⟨ cright (lemma-^-cong (S ^ p) ε (k*l Nat./ p) (axiom order-S)) ⟩
  S^ (k * l) • ε ^ (k*l Nat./ p) ≈⟨ cright lemma-ε^k=ε (k*l Nat./ p) ⟩
  S^ (k * l) • ε ≈⟨ right-unit ⟩
  S^ (k * l) ∎
  where
  k*l = toℕ k Nat.* toℕ l

lemma-CZ^k*l : ∀ k l -> CZ^ k ^ᵖ l ≈ CZ^ (k * l)
lemma-CZ^k*l k l = begin
  CZ^ k ^ᵖ l ≈⟨ refl ⟩
  (CZ ^ toℕ k) ^ toℕ l ≈⟨ lemma-^^ CZ (toℕ k) (toℕ l) ⟩
  CZ ^ (toℕ k Nat.* toℕ l) ≡⟨ Eq.cong (CZ ^_) (m≡m%n+[m/n]*n k*l p) ⟩
  CZ ^ (k*l Nat.% p Nat.+ (k*l Nat./ p) Nat.* p) ≈⟨ lemma-^-+ CZ (k*l Nat.% p) (((k*l Nat./ p) Nat.* p)) ⟩
  CZ ^ (k*l Nat.% p) • CZ ^ ((k*l Nat./ p) Nat.* p) ≈⟨ cong (refl' (Eq.cong (CZ ^_) (Eq.sym (toℕ-fromℕ< (m%n<n k*l p))))) (refl' (Eq.cong (CZ ^_) (NP.*-comm ((k*l Nat./ p)) p))) ⟩
  CZ ^ toℕ (fromℕ< (m%n<n k*l p)) • CZ ^ (p Nat.* (k*l Nat./ p) ) ≈⟨ cong (sym (refl)) (sym (lemma-^^ CZ p (k*l Nat./ p))) ⟩
  CZ^ (k * l) • (CZ ^ p) ^ (k*l Nat./ p) ≈⟨ cright (lemma-^-cong (CZ ^ p) ε (k*l Nat./ p) (axiom order-CZ)) ⟩
  CZ^ (k * l) • ε ^ (k*l Nat./ p) ≈⟨ cright lemma-ε^k=ε (k*l Nat./ p) ⟩
  CZ^ (k * l) • ε ≈⟨ right-unit ⟩
  CZ^ (k * l) ∎
  where
  k*l = toℕ k Nat.* toℕ l

aux-CZ⁻¹^k-CZ^-k : ∀ (k : ℤ ₚ) -> CZ⁻¹ ^ toℕ k ≈ CZ ^ toℕ (- k)
aux-CZ⁻¹^k-CZ^-k k = begin
  CZ⁻¹ ^ toℕ k ≈⟨ sym (lemma-^-cong _ _ (toℕ k) (refl' (Eq.cong (CZ ^_) lemma-toℕ-1ₚ))) ⟩
  CZ^ (- ₁) ^ toℕ k ≈⟨ refl ⟩
  CZ^ (- ₁) ^ᵖ k ≈⟨ lemma-CZ^k*l (- ₁) k  ⟩
  CZ^ (- ₁ * k)  ≈⟨ refl' (Eq.cong CZ^ (-1*x≈-x k)) ⟩
  CZ^ (- k) ≈⟨ refl ⟩
  CZ ^ toℕ (- k) ∎

aux-Ex-CX^k-N : ∀ k -> Ex • CX ^ k ≈ XC ^ k • Ex
aux-Ex-CX^k-N k@0 = trans right-unit (sym left-unit)
aux-Ex-CX^k-N k@1 = rewrite-swap 100 auto
aux-Ex-CX^k-N k@(₁₊ k'@(₁₊ k'')) = begin
  Ex • CX ^ k ≈⟨ sym assoc ⟩
  (Ex • CX) • CX ^ k' ≈⟨ cleft rewrite-swap 100 auto ⟩
  (XC • Ex) • CX ^ k' ≈⟨ assoc ⟩
  XC • Ex • CX ^ k' ≈⟨ cright aux-Ex-CX^k-N k' ⟩
  XC • XC ^ k' • Ex ≈⟨ sym assoc ⟩
  XC ^ k • Ex ∎



aux-Ex-CX^k : ∀ k -> Ex • CX^ k ≈ XC^ k • Ex
aux-Ex-CX^k k = aux-Ex-CX^k-N (toℕ k)

aux-Ex-XC^k : ∀ k -> Ex • XC^ k ≈ CX^ k • Ex
aux-Ex-XC^k k = bbc Ex Ex claim
  where
  claim : Ex • (Ex • XC^ k) • Ex ≈ Ex • (CX^ k • Ex) • Ex
  claim = begin
    Ex • (Ex • XC^ k) • Ex ≈⟨ by-assoc auto ⟩
    (Ex • Ex) • XC^ k • Ex ≈⟨ cleft rewrite-swap 100 auto ⟩
    ε • XC^ k • Ex ≈⟨ left-unit ⟩
    XC^ k • Ex ≈⟨ sym (aux-Ex-CX^k k) ⟩
    Ex • CX^ k ≈⟨ cong refl (sym right-unit) ⟩
    Ex • CX^ k • ε ≈⟨ cright cright rewrite-swap 100 auto ⟩
    Ex • CX^ k • Ex • Ex ≈⟨ sym (cong refl assoc) ⟩
    Ex • (CX^ k • Ex) • Ex ∎


aux-XC^-XC'^-N : ∀ k -> XC ^ k ≈ H ↑ ^ 3 • CZ ^ k • H ↑
aux-XC^-XC'^-N k@0 = rewrite-swap 100 auto
aux-XC^-XC'^-N k@1 = refl
aux-XC^-XC'^-N k@(₁₊ k'@(₁₊ k'')) = begin
  XC ^ k ≈⟨ refl ⟩
  XC • XC ^ k' ≈⟨ cright aux-XC^-XC'^-N k' ⟩
  XC • H ↑ ^ 3 • CZ ^ k' • H ↑ ≈⟨ sym assoc ⟩
  (XC • H ↑ ^ 3) • CZ ^ k' • H ↑ ≈⟨ cleft rewrite-sym0 100 auto  ⟩
  (H ↑ ^ 3 • CZ) • CZ ^ k' • H ↑ ≈⟨ special-assoc (□ ^ 2 • □ ^ 2) (□ • □ ^ 2 • □) auto ⟩
  H ↑ ^ 3 • (CZ • CZ ^ k') • H ↑ ≈⟨ refl ⟩
  H ↑ ^ 3 • CZ ^ k • H ↑ ∎

aux-CX^-CX'^-N : ∀ k -> CX ^ k ≈ H ^ 3 • CZ ^ k • H
aux-CX^-CX'^-N k@0 = rewrite-sym0 100 auto
aux-CX^-CX'^-N k@1 = refl
aux-CX^-CX'^-N k@(₁₊ k'@(₁₊ k'')) = begin
  CX ^ k ≈⟨ refl ⟩
  CX • CX ^ k' ≈⟨ cright aux-CX^-CX'^-N k' ⟩
  CX • H ^ 3 • CZ ^ k' • H ≈⟨ sym assoc ⟩
  (CX • H ^ 3) • CZ ^ k' • H ≈⟨ cleft rewrite-sym0 100 auto  ⟩
  (H ^ 3 • CZ) • CZ ^ k' • H ≈⟨ special-assoc (□ ^ 2 • □ ^ 2) (□ • □ ^ 2 • □) auto ⟩
  H ^ 3 • (CZ • CZ ^ k') • H ≈⟨ refl ⟩
  H ^ 3 • CZ ^ k • H ∎





aux-XC^-XC'^ : ∀ k -> XC^ k ≈ XC'^ k
aux-XC^-XC'^ k = aux-XC^-XC'^-N (toℕ k)

aux-CX^-CX'^ : ∀ k -> CX^ k ≈ CX'^ k
aux-CX^-CX'^ k = aux-CX^-CX'^-N (toℕ k)

open import N.Duality p-2 p-prime
open Duality

lemma-semi-XCCZ^k : ∀ (k*@(k , nz) : ℤ* ₚ) ->
  let
    -2k : ℤ ₚ
    -2k = - k + - k
  in

  XC • CZ^ k ≈ S^ -2k • CZ^ k • XC
lemma-semi-XCCZ^k k*@(k , nz) = by-duality' (lemma-semi-CXCZ^k k*) c1 c2
  where
  -2k : ℤ ₚ
  -2k = - k + - k
  c1 : dual (CX • CZ^ k) ≈ XC • CZ^ k
  c1 = cright refl' (aux-dual-CZ^k (toℕ k))
  c2 : dual (S^ -2k ↑ • CZ^ k • CX) ≈ S^ -2k • CZ^ k • XC
  c2 = begin
    dual (S^ -2k ↑ • CZ^ k • CX) ≈⟨ cong (refl' (aux-dual-S^k↑ (toℕ -2k))) (cleft refl' (aux-dual-CZ^k (toℕ k))) ⟩
    S^ -2k • CZ^ k • XC ∎

aux-CZ-H↑-CZ^k : ∀ (k*@(k , nz) : ℤ* ₚ) ->
  let -2k = - k + - k in
  
  CZ • H ↑ • CZ^ k ≈ (S^ -2k • H ↑ • CZ^ k • H ↑ ^ 3) • CZ • H ↑

aux-CZ-H↑-CZ^k k*@(k , nz) = begin
  CZ • H ↑ • CZ^ k ≈⟨ sym assoc ⟩
  (CZ • H ↑) • CZ^ k ≈⟨ cleft rewrite-sym0 100 auto ⟩
  (H ↑ • XC) • CZ^ k ≈⟨ assoc ⟩
  H ↑ • XC • CZ^ k ≈⟨ cright lemma-semi-XCCZ^k k* ⟩
  H ↑ • S^ -2k • CZ^ k • XC ≈⟨ sym assoc ⟩
  (H ↑ • S^ -2k) • CZ^ k • XC ≈⟨ cleft sym (lemma-comm-Sᵏ-w↑ (toℕ -2k) H) ⟩
  (S^ -2k • H ↑) • CZ^ k • XC ≈⟨ special-assoc (□ ^ 2 • □ ^ 4) (□ ^ 4 • □ ^ 2) auto ⟩
  (S^ -2k • H ↑ • CZ^ k • H ↑ ^ 3) • CZ • H ↑ ∎
  where
  -2k : ℤ ₚ
  -2k = - k + - k


aux-CZ⁻¹-H-CZ^k : ∀ k -> CZ^ (- ₁) • H • CZ^ k ≈ H • S^ k ↑ • S^ (- k) • CX^ (- ₁) • S^ k
aux-CZ⁻¹-H-CZ^k k = bbc (H ^ 5) ε claim
  where
  claim : H ^ 5 • (CZ^ (- ₁) • H • CZ^ k) • ε ≈ H ^ 5 • (H • S^ k ↑ • S^ (- k) • CX^ (- ₁) • S^ k) • ε
  claim = begin
    H ^ 5 • (CZ^ (- ₁) • H • CZ^ k) • ε ≈⟨ cong refl right-unit ⟩
    H ^ 5 • (CZ^ (- ₁) • H • CZ^ k) ≈⟨ sa (□ ^ 5 • □ ^ 3) (□ ^ 3 • (□ ^ 2 • □) • □ ^ 2) auto ⟩
    H ^ 3 • (H ^ 2 • CZ^ (- ₁)) • H • CZ^ k ≈⟨ cright cleft lemma-semi-CZ-HH↓' ⟩
    H ^ 3 • (CZ • H ^ 2) • H • CZ^ k ≈⟨ cright sa (□ ^ 3 • □ ^ 2) (□ ^ 2 • □ ^ 2 • □) auto ⟩
    H ^ 3 • (CZ • H) • H ^ 2 • CZ^ k ≈⟨ cright cright lemma-semi-HH↓-CZ^k' k ⟩
    H ^ 3 • (CZ • H) • CZ^ (- k) • H ^ 2 ≈⟨ sa (□ • □ ^ 2 • □ ^ 2) ((□ ^ 3 • □) • □) auto ⟩
    (CX • CZ^ (- k)) • H ^ 2 ≈⟨ cleft lemma-semi-CXCZ^-alt (- k) ⟩
    (S^ (- k) • CX • S^ (- - k) • S^ (- - k) ↑) • H ^ 2 ≈⟨ cleft cright (cright refl' (Eq.cong (\ xx -> S^ xx • S^ xx ↑) (-‿involutive k))) ⟩
    (S^ (- k) • CX • S^ k • S^ k ↑) • H ^ 2 ≈⟨ cleft cright cright lemma-comm-Sᵏ-w↑ (toℕ k) (S^ k) ⟩
    (S^ (- k) • CX • S^ k ↑ • S^ k) • H ^ 2 ≈⟨ cleft sa (□ ^ 4) (□ • □ ^ 2 • □) auto ⟩
    (S^ (- k) • (CX • S^ k ↑) • S^ k) • H ^ 2 ≈⟨ cleft cright cleft aux-comm-CX-S^k↑ k ⟩
    (S^ (- k) • (S^ k ↑ • CX) • S^ k) • H ^ 2 ≈⟨ cleft sym (sa (□ ^ 2 • □ ^ 2) (□ • □ ^ 2 • □) auto) ⟩
    ((S^ (- k) • S^ k ↑) • (CX • S^ k)) • H ^ 2 ≈⟨ cleft cleft lemma-comm-Sᵏ-w↑ (toℕ (- k)) (S^ k) ⟩
    ((S^ k ↑ • S^ (- k)) • (CX • S^ k)) • H ^ 2 ≈⟨ sa (□ ^ 3 • □) (□ ^ 4) auto ⟩
    (S^ k ↑ • S^ (- k)) • CX • S^ k • H ^ 2 ≈⟨ cright cright word-comm (toℕ k) 1 (sym (trans assoc (axiom comm-HHS))) ⟩
    (S^ k ↑ • S^ (- k)) • CX • H ^ 2 • S^ k ≈⟨ sa (□ ^ 4) (□ • □ ^ 2 • □) auto ⟩
    (S^ k ↑ • S^ (- k)) • (CX • H ^ 2) • S^ k ≈⟨ cright cleft sym lemma-semi-HH↓-CX⁻¹ ⟩
    (S^ k ↑ • S^ (- k)) • (H ^ 2 • CX^ (- ₁)) • S^ k ≈⟨ sa (□ ^ 2 • □ ^ 2 • □) (□ • □ ^ 2 • □ ^ 2) auto ⟩
    S^ k ↑ • (S^ (- k) • H ^ 2) • CX^ (- ₁) • S^ k ≈⟨  cright cleft word-comm (toℕ (- k)) 1 (sym (trans assoc (axiom comm-HHS))) ⟩
    S^ k ↑ • (H ^ 2 • S^ (- k)) • CX^ (- ₁) • S^ k ≈⟨ sa (□ • □ ^ 2 • □) (□ ^ 2 • □ ^ 2) auto ⟩
    (S^ k ↑ • H ^ 2) • S^ (- k) • CX^ (- ₁) • S^ k ≈⟨ cleft sym (lemma-comm-Hᵏ-w↑ 2 (S^ k)) ⟩
    (H ^ 2 • S^ k ↑) • S^ (- k) • CX^ (- ₁) • S^ k ≈⟨ assoc ⟩
    H ^ 2 • S^ k ↑ • S^ (- k) • CX^ (- ₁) • S^ k ≈⟨ cleft rewrite-sym0 100 auto ⟩
    H ^ 6 • S^ k ↑ • S^ (- k) • CX^ (- ₁) • S^ k ≈⟨ sa (□ ^ 6 • □) (□ ^ 5 • □ ^ 2) auto ⟩
    H ^ 5 • (H • S^ k ↑ • S^ (- k) • CX^ (- ₁) • S^ k) ≈⟨ cright sym right-unit ⟩
    H ^ 5 • (H • S^ k ↑ • S^ (- k) • CX^ (- ₁) • S^ k) • ε ∎
-}
