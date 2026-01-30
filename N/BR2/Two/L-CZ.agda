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



module N.BR2.Two.L-CZ (p-2 : ℕ) (p-prime : Prime (2+ p-2)) where

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
open import N.BR2.Calculations p-2 p-prime
open import N.BR2.One.A p-2 p-prime
open import N.BR2.Two.A-CZ p-2 p-prime hiding (n ; module L01)


open PB ((₂₊ n) QRel,_===_)
open PP ((₂₊ n) QRel,_===_)
open SR word-setoid
open Pattern-Assoc
open Lemmas0 n
module L01 = Lemmas0 1
open Lemmas-2Q n
open Sym0-Rewriting (₁₊ n)
open Rewriting-Swap 1
open Symplectic-GroupLike
open Basis-Change _ (2 QRel,_===_) grouplike


dir-and-l' : L 2 -> Word (Gen 2) × L 2
--dir-and-l' l = ε , l

dir-and-l' l@((₀ , z≤n) , ((c@₀ , d@₀) ∷ []) , x@((a@₀ , b@₀) , nzx)) = ⊥-elim (nzx auto)
dir-and-l' l@((₀ , z≤n) , ((c@₀ , d@₀) ∷ []) , x@((a@₀ , b@(₁₊ _)) , nzx))                =     CZ^ b⁻¹     ,     l
  where b⁻¹ = ((b , λ ()) ⁻¹) .proj₁
dir-and-l' l@((₀ , z≤n) , ((c@₀ , d@(₁₊ _)) ∷ []) , x@((a@₀ , b@(₁₊ _)) , nzx))           =     dir         ,     l
  where
  [bd]⁻¹ = ((b , λ ()) ⁻¹) .proj₁ * ((d , λ ()) ⁻¹) .proj₁
  dir = S^ (- [bd]⁻¹ + - [bd]⁻¹) • CZ^ [bd]⁻¹
dir-and-l' ((₀ , z≤n) , ((c@(₁₊ _) , d) ∷ []) , x@((a@₀ , b@(₁₊ _)) , nzx)) with b + - c
... | t@₀                                                                                 =     dir         ,     l'
  where
  l' : L 2
  l' = ((₁ , s≤s z≤n) , [] , ((c , d) , λ ()))
  -- (inverse of the dir of A[-cd]-CZ) • HH
  dir = (H • CZ^ (- ₁) • H ^ 3 • ZM (((c , λ ())) ⁻¹)) • HH
... | t@(₁₊ _)                                                                            =     {!!}

dir-and-l' ((₁ , s≤s z≤n) , [] , x@((a@₀ , b@₀) , nzx)) = ⊥-elim (nzx auto)
dir-and-l' l@((₁ , s≤s z≤n) , [] , x@((a@₀ , b@(₁₊ _)) , nzx))                            =     CZ^ b⁻¹     ,     l
  where b⁻¹ = ((b , λ ()) ⁻¹) .proj₁
dir-and-l' l@((₁ , s≤s z≤n) , [] , x@((a@(₁₊ _) , b) , nzx))                              =     dir         ,     l'
  where
  dir = ZM (a , λ ()) • H • CZ • H ^ 3
  nzx' = aux-b≠0⇒ab≠0 ₀ (- a) ((-' (a , λ ())) .proj₂)
  l' : L 2
  l' = ((₀ , z≤n) , ((a , b) ∷ []) , ((₀ , - a) , nzx'))



lemma-dir-and-l' : ∀ (l : L 2) -> let (dir , l') = dir-and-l' l in

  [ l ]ˡ • CZ ≈ dir • [ l' ]ˡ

lemma-dir-and-l' ((₂₊ j , s≤s ()) , vb , x@((a , b) , nzx))

lemma-dir-and-l' l@((₀ , z≤n) , ((c@(₁₊ _) , d) ∷ []) , x@((a@₀ , b@(₁₊ _)) , nzx)) with b + - c | inspect (b +_) (- c)
... | t@₀ | [ eq0 ]' = bbc dir-acz (CZ^ (- ₁)) claim 
  where
  l' : L 2
  l' = ((₁ , s≤s z≤n) , [] , ((c , d) , λ ()))
  eq : b ≡ c
  eq = b-c=0⇒b=c b c eq0
  dir : Word (Gen 2)
  dir = (H • CZ^ (- ₁) • H ^ 3 • ZM (((c , λ ())) ⁻¹)) • HH
  nz-c : - c ≢ ₀
  nz-c = (-' (c , λ ())) .proj₂
  nz--c : - - c ≢ ₀
  nz--c = (-' (- c , nz-c)) .proj₂
  nz--cp : (₀ , - - c) ≢ (₀ , ₀)
  nz--cp = aux-b≠0⇒ab≠0 ₀ (- - c) nz--c
  nz-cp : (₀ , - c) ≢ (₀ , ₀)
  nz-cp = aux-b≠0⇒ab≠0 ₀ (- c) nz-c
  nz-cp' : (- ₀ , - c) ≢ (₀ , ₀)
  nz-cp' = aux-b≠0⇒ab≠0 (- ₀) (- c) nz-c
  dir-acz : Word (Gen 2)
  dir-acz = ZM ((c , λ ())) • H • CZ • H ^ 3
  

  aux-dir-acz' : dir-acz • dir ≈ HH
  aux-dir-acz' = begin
    (ZM ( (c , λ ())) • H • CZ • H ^ 3) • (H • CZ^ (- ₁) • H ^ 3 • ZM (( (c , λ ())) ⁻¹)) • HH ≈⟨ special-assoc (□ ^ 6 • □ ^ 2 • □) (□ ^ 3 • (□ ^ 4 • □) • □) auto ⟩
    (ZM ( (c , λ ())) • H • CZ) • (H ^ 4 • CZ^ (- ₁) • H ^ 3 • ZM (( (c , λ ())) ⁻¹)) • HH ≈⟨ cright cleft trans (cleft axiom order-H) left-unit ⟩
    (ZM ( (c , λ ())) • H • CZ) • (CZ^ (- ₁) • H ^ 3 • ZM (( (c , λ ())) ⁻¹)) • HH ≈⟨ special-assoc (□ ^ 3 • □ ^ 3 • □) (□ ^ 2 • □ ^ 2 • □ ^ 3) auto ⟩
    (ZM ( (c , λ ())) • H) • (CZ • CZ^ (- ₁)) • H ^ 3 • ZM (( (c , λ ())) ⁻¹) • HH ≈⟨ cright cleft lemma-CZ^k+l ₁ (- ₁) ⟩
    (ZM ( (c , λ ())) • H) • (CZ^ (₁ + - ₁)) • H ^ 3 • ZM (( (c , λ ())) ⁻¹) • HH ≈⟨ cright cleft refl' (Eq.cong CZ^ (+-inverseʳ ₁)) ⟩
    (ZM ( (c , λ ())) • H) • ε • H ^ 3 • ZM (( (c , λ ())) ⁻¹) • HH ≈⟨ cright left-unit ⟩
    (ZM ( (c , λ ())) • H) • H ^ 3 • ZM (( (c , λ ())) ⁻¹) • HH ≈⟨ special-assoc (□ ^ 2 • □ ^ 3 • □) (□ • □ ^ 4 • □) auto ⟩
    (ZM ( (c , λ ()))) • H ^ 4 • ZM (( (c , λ ())) ⁻¹) • HH ≈⟨ cright trans (cleft axiom order-H) left-unit ⟩
    (ZM ( (c , λ ()))) • ZM (( (c , λ ())) ⁻¹) • HH ≈⟨ sym assoc ⟩
    (ZM ( (c , λ ())) • ZM (( (c , λ ())) ⁻¹)) • HH ≈⟨ cleft axiom (M-mul ( (c , λ ())) (( (c , λ ())) ⁻¹)) ⟩
    ZM ( (c , λ ()) *' ( (c , λ ())) ⁻¹) • HH ≈⟨ cleft L01.aux-MM (( (c , λ ()) *' ( (c , λ ())) ⁻¹) .proj₂) (λ ()) (lemma-⁻¹ʳ ( c) {{nztoℕ {y =  c} {neq0 = λ ()}}}) ⟩
    ZM (₁ , λ ()) • HH ≈⟨ cleft sym L01.lemma-M1 ⟩
    ε • HH ≈⟨ left-unit ⟩
    HH ∎

{-
  aux-dir-acz' : dir-acz • dir ≈ ε
  aux-dir-acz' = begin
    dir-acz • dir ≈⟨ cright sym right-unit ⟩
    dir-acz • dir • ε ≈⟨ {!cright cright ?!} ⟩
    dir-acz • dir • H ^ 4 ≈⟨ {!special-assoc!} ⟩
    (dir-acz • dir • HH) • HH ≈⟨ cleft {!!} ⟩
    HH • HH ≈⟨ rewrite-sym0 100 auto ⟩
    ε ∎
-}

  claim : dir-acz • ([ l ]ˡ • CZ) • CZ^ (- ₁) ≈ dir-acz • (dir • [ l' ]ˡ) • CZ^ (- ₁)
  claim = begin
    dir-acz • ([ l ]ˡ • CZ) • CZ^ (- ₁) ≈⟨ special-assoc (□ • □ ^ 2 • □) (□ ^ 4) auto ⟩
    dir-acz • [ l ]ˡ • CZ • CZ^ (- ₁) ≈⟨ cright cright trans (lemma-CZ^k+l ₁ (- ₁)) (refl' (Eq.cong CZ^ (+-inverseʳ ₁))) ⟩
    dir-acz • [ l ]ˡ • ε ≈⟨ cright right-unit ⟩
    dir-acz • [ l ]ˡ ≈⟨ cright trans assoc left-unit ⟩
    dir-acz • [ c , d ]ᵇ • [ (₀ , b) , (λ ()) ]ᵃ ≈⟨ cright cright refl' (aux-AA 1 ((₀ , b) , (λ ())) ((₀ , c) , (λ ())) (≡×≡⇒≡ (auto , eq))) ⟩
    dir-acz • [ c , d ]ᵇ • [ (₀ , c) , (λ ()) ]ᵃ ≈⟨ cright cright refl' (aux-AA 1 ((₀ , c) , (λ ())) ((₀ , - - c) , nz--cp) (≡×≡⇒≡ (auto , Eq.sym (-‿involutive c))) ) ⟩
    dir-acz • [ c , d ]ᵇ • [ (₀ , - - c) , nz--cp ]ᵃ ≈⟨ cright cright sym (lemma-A-HH' 1 (- c)  (nz-c)) ⟩
    dir-acz • [ c , d ]ᵇ • [ ((₀ , - c) , nz-cp) ]ᵃ • HH ≈⟨ special-assoc (□ ^ 4) (□ ^ 3 • □) auto ⟩
    (dir-acz • [ c , d ]ᵇ • [ ((₀ , - c) , nz-cp) ]ᵃ) • HH ≈⟨ cleft sym (lemma-A-CZ-2 (c , λ ()) d) ⟩
    ([ ((c , d) , λ ()) ]ᵃ ↑ • CZ) • HH ≈⟨ assoc ⟩
    [ ((c , d) , λ ()) ]ᵃ ↑ • CZ • HH ≈⟨ cright sym lemma-semi-CZ-HH↓' ⟩
    [ ((c , d) , λ ()) ]ᵃ ↑ • HH • CZ^ (- ₁) ≈⟨ sym assoc ⟩
    ([ ((c , d) , λ ()) ]ᵃ ↑ • HH) • CZ^ (- ₁) ≈⟨ cleft sym (lemma-comm-Hᵏ-w↑ 2 [ ((c , d) , λ ()) ]ᵃ) ⟩
    (HH • [ ((c , d) , λ ()) ]ᵃ ↑) • CZ^ (- ₁) ≈⟨ assoc ⟩
    HH • [ ((c , d) , λ ()) ]ᵃ ↑ • CZ^ (- ₁) ≈⟨ cright cleft sym left-unit ⟩
    HH • [ l' ]ˡ • CZ^ (- ₁) ≈⟨ cleft sym aux-dir-acz' ⟩
    (dir-acz • dir) • [ l' ]ˡ • CZ^ (- ₁) ≈⟨ special-assoc (□ ^ 2 • □ ^ 2) (□ • □ ^ 2 • □) auto ⟩
    dir-acz • (dir • [ l' ]ˡ) • CZ^ (- ₁) ∎


  

{-
lemma-dir-and-l' l@((₀ , z≤n) , vb@((c@₀ , d@(₁₊ _)) ∷ []) , x@((a@₀ , b@(₁₊ _)) , nzx)) = begin
  [ l ]ˡ • CZ ≈⟨ refl ⟩
  ([ vb ]ᵛᵇ • [ x ]ᵃ) • CZ ≈⟨ cleft cleft left-unit ⟩
  ([ c , d ]ᵇ • ⟦ (b , λ ()) ⁻¹ , ε ⟧ₘ₊) • CZ ≈⟨ cleft cright right-unit ⟩
  ([ c , d ]ᵇ • ⟦ (b , λ ()) ⁻¹ ⟧ₘ) • CZ ≈⟨ assoc ⟩
  [ c , d ]ᵇ • ⟦ (b , λ ()) ⁻¹ ⟧ₘ • CZ ≈⟨ cright axiom (semi-M↓CZ ((b , λ ()) ⁻¹)) ⟩
  [ c , d ]ᵇ • CZ^ b⁻¹ • ⟦ (b , λ ()) ⁻¹ ⟧ₘ ≈⟨ cleft (cright cright right-unit) ⟩
  (Ex • CX • ⟦ (d , λ ()) ⁻¹ ⟧ₘ ↑) • CZ^ b⁻¹ • ⟦ (b , λ ()) ⁻¹ ⟧ₘ ≈⟨ special-assoc (□ ^ 3 • □ ^ 2) (□ ^ 2 • □ ^ 2 • □) auto ⟩
  (Ex • CX) • (⟦ (d , λ ()) ⁻¹ ⟧ₘ ↑ • CZ^ b⁻¹) • ⟦ (b , λ ()) ⁻¹ ⟧ₘ ≈⟨ cright cleft lemma-M↑CZ^k (((d , λ ()) ⁻¹) .proj₁) b⁻¹ (((d , λ ()) ⁻¹) .proj₂) ⟩
  (Ex • CX) • (CZ^ (b⁻¹ * d⁻¹) • ⟦ (d , λ ()) ⁻¹ ⟧ₘ ↑) • ⟦ (b , λ ()) ⁻¹ ⟧ₘ ≈⟨ special-assoc (□ ^ 2 • □ ^ 2 • □) (□ • □ ^ 2 • □ ^ 2) auto ⟩
  Ex • (CX • CZ^ (b⁻¹ * d⁻¹)) • ⟦ (d , λ ()) ⁻¹ ⟧ₘ ↑ • ⟦ (b , λ ()) ⁻¹ ⟧ₘ ≈⟨ cright cleft lemma-semi-CXCZ^k ((b , λ ()) ⁻¹ *' (d , λ ()) ⁻¹) ⟩
  Ex • (S^ (- [bd]⁻¹ + - [bd]⁻¹) ↑ • CZ^ (b⁻¹ * d⁻¹) • CX) • ⟦ (d , λ ()) ⁻¹ ⟧ₘ ↑ • ⟦ (b , λ ()) ⁻¹ ⟧ₘ ≈⟨ special-assoc (□ • □ ^ 3 • □) (□ ^ 2 • □ ^ 3) auto ⟩
  (Ex • S^ (- [bd]⁻¹ + - [bd]⁻¹) ↑) • CZ^ (b⁻¹ * d⁻¹) • CX • ⟦ (d , λ ()) ⁻¹ ⟧ₘ ↑ • ⟦ (b , λ ()) ⁻¹ ⟧ₘ ≈⟨ cleft lemma-Ex-S^ᵏ↑ (- [bd]⁻¹ + - [bd]⁻¹) ⟩
  (S^ (- [bd]⁻¹ + - [bd]⁻¹) • Ex) • CZ^ (b⁻¹ * d⁻¹) • CX • ⟦ (d , λ ()) ⁻¹ ⟧ₘ ↑ • ⟦ (b , λ ()) ⁻¹ ⟧ₘ ≈⟨ special-assoc (□ ^ 2 • □ ^ 2) (□ • □ ^ 2 • □) auto ⟩
  S^ (- [bd]⁻¹ + - [bd]⁻¹) • (Ex • CZ^ [bd]⁻¹) • CX • ⟦ (d , λ ()) ⁻¹ ⟧ₘ ↑ • ⟦ (b , λ ()) ⁻¹ ⟧ₘ ≈⟨ cright cleft word-comm 1 (toℕ [bd]⁻¹) (sym lemma-comm-Ex-CZ) ⟩
  S^ (- [bd]⁻¹ + - [bd]⁻¹) • (CZ^ [bd]⁻¹ • Ex) • CX • ⟦ (d , λ ()) ⁻¹ ⟧ₘ ↑ • ⟦ (b , λ ()) ⁻¹ ⟧ₘ ≈⟨ special-assoc (□ • □ ^ 2 • □) (□ ^ 2 • □ ^ 2) auto ⟩
  (S^ (- [bd]⁻¹ + - [bd]⁻¹) • CZ^ [bd]⁻¹) • Ex • CX • ⟦ (d , λ ()) ⁻¹ ⟧ₘ ↑ • ⟦ (b , λ ()) ⁻¹ ⟧ₘ ≈⟨ cright cright cright cong (sym right-unit) (sym right-unit) ⟩
  (S^ (- [bd]⁻¹ + - [bd]⁻¹) • CZ^ [bd]⁻¹) • Ex • CX • ⟦ (d , λ ()) ⁻¹ , ε ⟧ₘ₊ ↑ • ⟦ (b , λ ()) ⁻¹ , ε ⟧ₘ₊ ≈⟨ cright special-assoc (□ ^ 4) (□ ^ 3 • □) auto ⟩
  (S^ (- [bd]⁻¹ + - [bd]⁻¹) • CZ^ [bd]⁻¹) • (Ex • CX • ⟦ (d , λ ()) ⁻¹ , ε ⟧ₘ₊ ↑) • ⟦ (b , λ ()) ⁻¹ , ε ⟧ₘ₊ ≈⟨ cright cleft sym left-unit ⟩
  dir • [ l' ]ˡ ∎
  where
  b⁻¹ = ((b , λ ()) ⁻¹) .proj₁
  d⁻¹ = ((d , λ ()) ⁻¹) .proj₁
  [bd]⁻¹ = ((b , λ ()) ⁻¹) .proj₁ * ((d , λ ()) ⁻¹) .proj₁
  dl = dir-and-l' l
  l' = dl .proj₂
  dir = dl .proj₁


lemma-dir-and-l' ((₁ , s≤s z≤n) , [] , x@((a@₀ , b@₀) , nzx)) = ⊥-elim (nzx auto)
lemma-dir-and-l' l@((₁ , s≤s z≤n) , [] , x@((a@₀ , b@(₁₊ _)) , nzx)) = begin
  [ l ]ˡ • CZ ≈⟨ cleft left-unit ⟩
  [ x ]ᵃ ↑ • CZ ≈⟨ lemma-A-CZ-1 (b , (λ ())) ⟩
  CZ^ b⁻¹ • [ x ]ᵃ ↑ ≈⟨ cright sym left-unit ⟩
  dir • [ l' ]ˡ ∎
  where
  b⁻¹ = ((b , λ ()) ⁻¹) .proj₁
  dl = dir-and-l' l
  l' = dl .proj₂
  dir = dl .proj₁
lemma-dir-and-l' l@((₁ , s≤s z≤n) , [] , x@((a@(₁₊ _) , b) , nzx)) = begin
  [ l ]ˡ • CZ ≈⟨ cleft left-unit ⟩
  [ x ]ᵃ ↑ • CZ ≈⟨ lemma-A-CZ-2 (a , λ ()) b ⟩
  dir • [ a , b ]ᵇ • [ (₀ , - a) , nzx' ]ᵃ ≈⟨ cright sym (trans assoc left-unit)  ⟩
  dir • [ l' ]ˡ ∎
  where
  dir : Word (Gen 2)
  dir = ZM (a , λ ()) • H • CZ • H ^ 3
  nzx' = aux-b≠0⇒ab≠0 ₀ (- a) ((-' (a , λ ())) .proj₂)
  l' : L 2
  l' = ((₀ , z≤n) , ((a , b) ∷ []) , ((₀ , - a) , nzx'))

-}
