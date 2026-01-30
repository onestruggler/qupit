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
open import Relation.Nullary.Decidable using (yes ; no ; does ; proof)
open import Relation.Nullary.Reflects

open import Function using (_∘_ ; id)
open import Function.Definitions using (Injective)

open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂ ; map₁ ; ∃ ; Σ ; Σ-syntax)
open import Data.Product.Relation.Binary.Pointwise.NonDependent as PW using (≡×≡⇒≡ ; Pointwise ; ≡⇒≡×≡)
open import Data.Nat hiding (_^_ ; _+_ ; _*_ ; _≟_)
open import Agda.Builtin.Nat using (_-_)
import Data.Nat as Nat
open import Data.Bool hiding (_<_ ; _≤_ ; _≟_)
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
open import Data.Fin.Properties using (suc-injective ; toℕ-inject₁ ; toℕ-fromℕ ; 0≢1+n)
import Data.Nat.Properties as NP
open import Presentation.GroupLike
open import Presentation.Tactics using ()
open import Data.Nat.Primality



module N.BR.Two.L-CZ (p-2 : ℕ) (p-prime : Prime (2+ p-2)) where

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
open import N.BR.Two.Lemmas p-2 p-prime hiding (n ; module L01 ; sa)
open import N.BR.Two.Lemmas2 p-2 p-prime hiding (n ; module L01)
open import N.BR.Two.Lemmas3 p-2 p-prime hiding (n ; module L01 ; sa)
open import N.BR.Two.A-CZ p-2 p-prime hiding (n ; module L01)


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
open Group-Lemmas (Gen 2) (2 QRel,_===_) grouplike renaming (_⁻¹ to _⁻¹ʷ)
open Commuting-Symplectic 0


{-
l'-of : L 2 -> L 2

l'-of ((₁ , s≤s z≤n) , [] , ((a@₀ , b@(₁₊ _)) , nzp))        =  (₁ , s≤s z≤n) ,   []                   , ((a , b)       , nzp)
l'-of ((₁ , s≤s z≤n) , [] , ((a@(₁₊ _) , b) , nz))           =  (₀ , z≤n)     ,   ((a , b) ∷ [])       , ((₀ , - a)     , nzp)
  where
  nzp : (₀ , - a) ≢ (₀ , ₀)
  nzp = aux-b≠0⇒ab≠0 ₀ (- a) ((-' (a , λ ())) .proj₂)
l'-of ((₀ , z≤n) , ((c , d) ∷ []) , ((a@₀ , b@(₁₊ _)) , _))
    with b + - c | inspect (b +_) (- c)
... | ₀    | [ eq ]'                                         =  (₁ , s≤s z≤n) ,   []                   , ((b , d)       , λ ())
... | ₁₊ _ | [ eq ]'                                         =  (₀ , z≤n)     ,   ((c , d + - a) ∷ []) , ((a , b + - c) , nzp)
  where
  nzp : (a , b + - c) ≢ (₀ , ₀)
  nzp hyp = 0≢1+n (Eq.trans (Eq.sym (Eq.cong proj₂ hyp)) eq)
l'-of ((₀ , z≤n) , ((c , d) ∷ []) , ((a@(₁₊ _) , b) , _))    =  (₀ , z≤n)     ,   ((c , d + - a) ∷ []) , ((a , b + - c) , λ ())
  
l'-of ((₀ , z≤n) , ((c , d) ∷ []) , ((a@₀ , b@₀) , nz))      =  ⊥-elim (nz auto)
l'-of ((₁ , s≤s z≤n) , [] , ((a@₀ , b@₀) , nz))              =  ⊥-elim (nz auto)



dir-of : L 2 -> Word (Gen 2)

dir-of ((₁ , s≤s z≤n) , [] , x@((a@₀ , b@(₁₊ _)) , nzx))                    =   CZ^ b⁻¹
  where b⁻¹ = ((b , λ ()) ⁻¹) .proj₁
dir-of ((₁ , s≤s z≤n) , [] , x@((a@(₁₊ _) , b) , nzx))                      =   H • CZ^ a⁻¹ • H ^ 3
  where a⁻¹ = ((a , λ ()) ⁻¹) .proj₁
dir-of ((₀ , z≤n) , ((c , d) ∷ []) , ((a@₀ , b@(₁₊ _)) , _))
    with b + - c | inspect (b +_) (- c)
... | ₀    | [ eq ]'                                                        =   (H • CZ^ -b⁻¹ • H ^ 3) ⁻¹ʷ • HH
  where -b⁻¹ = ((-' (b , λ ())) ⁻¹) .proj₁
... | ₁₊ _ | [ eq ]'                                                        =   {!!}


{-
dir-of ((₀ , z≤n) , ((c@₀ , d@₀) ∷ []) , x@((a@₀ , b@(₁₊ _)) , nzx))        =   CZ^ b⁻¹
  where b⁻¹ = ((b , λ ()) ⁻¹) .proj₁
dir-of ((₀ , z≤n) , ((c@₀ , d@(₁₊ _)) ∷ []) , x@((a@₀ , b@(₁₊ _)) , nzx))   =   dir
  where
  [bd]⁻¹ = ((b , λ ()) ⁻¹) .proj₁ * ((d , λ ()) ⁻¹) .proj₁
  dir = S^ (- [bd]⁻¹ + - [bd]⁻¹) • CZ^ [bd]⁻¹

-}

dir-of ((₀ , z≤n) , ((c , d) ∷ []) , ((a@₀ , b@₀) , nzx)) = ⊥-elim (nzx auto)
dir-of ((₁ , s≤s z≤n) , [] , ((a@₀ , b@₀) , nzx))         = ⊥-elim (nzx auto)
dir-of _ = {!!}

-}


l'-of : L 2 -> L 2

l'-of ((₁ , s≤s z≤n) , [] , ((a@₀ , b@(₁₊ _)) , nzp))                       = (₁ , s≤s z≤n) ,   []                   , ((a , b)       , nzp)
l'-of ((₁ , s≤s z≤n) , [] , ((a@(₁₊ _) , b) , nz))                          = (₀ , z≤n)     ,   ((a , b) ∷ [])       , ((₀ , - a)     , nzp)
  where
  nzp : (₀ , - a) ≢ (₀ , ₀)
  nzp = aux-b≠0⇒ab≠0 ₀ (- a) ((-' (a , λ ())) .proj₂)
l'-of ((₀ , z≤n) , ((c , d) ∷ []) , ((a@₀ , b@(₁₊ _)) , _)) with b ≟ c
l'-of ((₀ , z≤n) , ((c , d) ∷ []) , ((a@₀ , b@(₁₊ _)) , _)) | yes eq        = (₁ , s≤s z≤n) ,   []                   , ((b , d)       , λ ())
l'-of ((₀ , z≤n) , ((c , d) ∷ []) , ((a@₀ , b@(₁₊ _)) , _)) | no neq        = (₀ , z≤n)     ,   ((c , d + - a) ∷ []) , ((a , b + - c) , nzp)
  where
  nzp : (a , b + - c) ≢ (₀ , ₀)
  nzp eqp = (neq (b-c=0⇒b=c b c (Eq.cong proj₂ eqp)))
l'-of ((₀ , z≤n) , ((c , d) ∷ []) , ((a@(₁₊ _) , b) , _))                   = (₀ , z≤n)     ,   ((c , d + - a) ∷ []) , ((a , b + - c) , λ ())
  
l'-of ((₀ , z≤n) , ((c , d) ∷ []) , ((a@₀ , b@₀) , nz)) = ⊥-elim (nz auto)
l'-of ((₁ , s≤s z≤n) , [] , ((a@₀ , b@₀) , nz))         = ⊥-elim (nz auto)



dir-of : L 2 -> Word (Gen 2)

dir-of ((₁ , s≤s z≤n) , [] , x@((a@₀ , b@(₁₊ _)) , nzx))                        =   CZ^ b⁻¹
  where b⁻¹ = ((b , λ ()) ⁻¹) .proj₁
dir-of ((₁ , s≤s z≤n) , [] , x@((a@(₁₊ _) , b) , nzx))                          =   H • CZ^ a⁻¹ • H ^ 3
  where a⁻¹ = ((a , λ ()) ⁻¹) .proj₁
dir-of ((₀ , z≤n) , ((c@₀ , d@₀) ∷ []) , ((a@₀ , b@(₁₊ _)) , nz)) with b ≟ c
dir-of ((₀ , z≤n) , ((c@₀ , d@₀) ∷ []) , ((a@₀ , b@(₁₊ _)) , nz)) | yes ()
dir-of ((₀ , z≤n) , ((c@₀ , d@₀) ∷ []) , ((a@₀ , b@(₁₊ _)) , nz)) | no neq      =   CZ^ b⁻¹
  where b⁻¹ = (((b , λ ())) ⁻¹) .proj₁

dir-of ((₀ , z≤n) , ((c@₀ , d@(₁₊ _)) ∷ []) , ((a@₀ , b@(₁₊ _)) , nz)) with b ≟ c
dir-of ((₀ , z≤n) , ((c@₀ , d@(₁₊ _)) ∷ []) , ((a@₀ , b@(₁₊ _)) , nz)) | yes ()
  where b⁻¹ = (((b , λ ())) ⁻¹) .proj₁
dir-of ((₀ , z≤n) , ((c@₀ , d@(₁₊ _)) ∷ []) , ((a@₀ , b@(₁₊ _)) , nz)) | no neq =   S^ (- b⁻¹d + - b⁻¹d) • CZ^ b⁻¹
  where
  b⁻¹ = ((b , λ ()) ⁻¹) .proj₁
  b⁻¹d = b⁻¹ * d

dir-of ((₀ , z≤n) , ((c@(₁₊ _) , d) ∷ []) , ((a@₀ , b@(₁₊ _)) , nz)) with b ≟ c
dir-of ((₀ , z≤n) , ((c@(₁₊ _) , d) ∷ []) , ((a@₀ , b@(₁₊ _)) , nz)) | yes eq   =   (H • CZ^ b⁻¹ • H ^ 3) ⁻¹ʷ • HH
  where b⁻¹ = (((b , λ ())) ⁻¹) .proj₁
dir-of ((₀ , z≤n) , ((c@(₁₊ _) , d) ∷ []) , ((a@₀ , b@(₁₊ _)) , nz)) | no neq   =   M [b-c]/b • H • CZ^ b⁻¹ • H ^ 3
  where
  b⁻¹ = ((b , λ ()) ⁻¹) .proj₁
  b-c≠0 : b + - c ≢ ₀
  b-c≠0 eq = neq (b-c=0⇒b=c b c eq)
  [b-c]/b = (b + - c , b-c≠0) *' ((b , λ ()) ⁻¹)


dir-of ((₀ , z≤n) , ((c@₀ , d) ∷ []) , ((a@(₁₊ _) , b) , nz))                   =   ε
dir-of ((₀ , z≤n) , ((c@(₁₊ _) , d) ∷ []) , ((a@(₁₊ _) , b) , nz))              =   H ^ 3 • S^ (- ac⁻¹) • H
  where ac⁻¹ = a * ((c , λ ()) ⁻¹) .proj₁


dir-of ((₀ , z≤n) , ((c , d) ∷ []) , ((a@₀ , b@₀) , nzx)) = ⊥-elim (nzx auto)
dir-of ((₁ , s≤s z≤n) , [] , ((a@₀ , b@₀) , nzx))         = ⊥-elim (nzx auto)


lemma-dir-and-l' : ∀ (l : L 2) ->
  let
  dir = dir-of l
  l' = l'-of l
  in

  [ l ]ˡ • CZ ≈ dir • [ l' ]ˡ

lemma-dir-and-l' ((₀ , z≤n) , ((c , d) ∷ []) , ((a@₀ , b@₀) , nzx)) = ⊥-elim (nzx auto)
lemma-dir-and-l' ((₁ , s≤s z≤n) , [] , ((a@₀ , b@₀) , nzx))         = ⊥-elim (nzx auto)

lemma-dir-and-l' l@((₀ , z≤n) , ((c@(₁₊ _) , d) ∷ []) , ((a@(₁₊ _) , b) , nzx)) = begin
  [ l ]ˡ • CZ ≈⟨ cleft cong left-unit refl ⟩
  ([ c , d ]ᵇ • M a*⁻¹ • H • S^ -b/a) • CZ ≈⟨ sa (□ ^ 4 • □) (□ • □ ^ 2 • □ ^ 2) auto ⟩
  [ c , d ]ᵇ • (M a*⁻¹ • H) • S^ -b/a • CZ ≈⟨ cright cong (sym (L01.semi-HM a*)) (word-comm (toℕ -b/a) 1 (sym (axiom comm-CZ-S↓))) ⟩
  [ c , d ]ᵇ • (H • M a*) • CZ • S^ -b/a ≈⟨ cright sa (□ ^ 2 • □ ^ 2) (□ • □ ^ 2 • □) auto ⟩
  (Ex • (H ^ 3 • CZ^ c • H) • H ↑  • S^ -d/c ↑) • H • (M a* • CZ) • S^ -b/a ≈⟨ cright cright (cleft axiom (semi-M↓CZ a*)) ⟩
  (Ex • (H ^ 3 • CZ^ c • H) • H ↑ • S^ -d/c ↑) • H • (CZ^ a • M a*) • S^ -b/a ≈⟨ cleft cright sa (□ ^ 3 • □ ^ 2) (□ ^ 2 • □ ^ 3) auto ⟩
  (Ex • (H ^ 3 • CZ^ c) • H • H ↑ • S^ -d/c ↑) • H • (CZ^ a • M a*) • S^ -b/a ≈⟨ cleft cright cright lemma-comm-H-w↑ (H • S^ -d/c) ⟩
  (Ex • (H ^ 3 • CZ^ c) • (H ↑ • S^ -d/c ↑) • H) • H • (CZ^ a • M a*) • S^ -b/a ≈⟨ sa (□ ^ 4 • □ • □ ^ 2 • □) (□ ^ 3 • (□ ^ 2 • □) • □ ^ 2) auto ⟩
  (Ex • (H ^ 3 • CZ^ c) • (H ↑ • S^ -d/c ↑)) • (H ^ 2 • CZ^ a) • M a* • S^ -b/a ≈⟨ cright cleft lemma-semi-HH↓-CZ^k' a ⟩
  (Ex • (H ^ 3 • CZ^ c) • (H ↑ • S^ -d/c ↑)) • (CZ^ (- a) • H ^ 2) • M a* • S^ -b/a ≈⟨ sa (□ ^ 4 • □ ^ 2 • □ ^ 2) (□ ^ 3 • □ ^ 2 • □ ^ 3) auto ⟩
  (Ex • (H ^ 3 • CZ^ c) • H ↑) • (S^ -d/c ↑ • CZ^ (- a)) • H ^ 2 • M a* • S^ -b/a ≈⟨ cright cleft sym (aux-comm-CZ^a-S^b↑ (- a) -d/c) ⟩
  (Ex • (H ^ 3 • CZ^ c) • H ↑) • (CZ^ (- a) • S^ -d/c ↑) • H ^ 2 • M a* • S^ -b/a ≈⟨ sa ((□ • □ ^ 2 • □) • □ ^ 2 • □ ^ 3) (□ ^ 2 • □ ^ 3 • □ ^ 4) auto ⟩
  (Ex • H ^ 3) • (CZ^ c • H ↑ • CZ^ (- a)) • S^ -d/c ↑ • H ^ 2 • M a* • S^ -b/a ≈⟨ cright cleft lemma-CZ^-aHCZ^k'-dual (c , (λ ())) (-' (a , λ ())) ⟩
  (Ex • H ^ 3) • (S^ (- -a⁻¹ * c) ↑ • H ↑ • CZ^ -a • H ↑ ^ 3 • S^ (-a⁻¹ * c) ↑ • H ↑ • S^ (- -a * c)) • S^ -d/c ↑ • H ^ 2 • M a* • S^ -b/a ≈⟨ cright cleft cong (refl' (Eq.cong (\ xx -> S^ xx ↑) (Eq.trans (Eq.cong (\ xx -> - xx * c) (inv-neg-comm a*)) (Eq.cong (_* c) (-‿involutive a⁻¹))))) (cright cright cright cright cright  refl' (Eq.cong S^ (Eq.cong (_* c) (-‿involutive a)))) ⟩
  (Ex • H ^ 3) • (S^ (a⁻¹ * c) ↑ • H ↑ • CZ^ -a • H ↑ ^ 3 • S^ (-a⁻¹ * c) ↑ • H ↑ • S^ (a * c)) • S^ -d/c ↑ • H ^ 2 • M a* • S^ -b/a ≈⟨ sa (□ ^ 2 • (□  • □ • □ • □ ^ 3 • □ • □ • □) • □ ^ 4) (□ • □ ^ 3 • □ ^ 3 • □ ^ 3 • □ ^ 2 • □ ^ 3) auto ⟩
  Ex • (H ^ 3 • S^ (a⁻¹ * c) ↑ • H ↑) • (CZ^ -a • H ↑ ^ 2) • (H ↑ • S^ (-a⁻¹ * c) ↑ • H ↑) • (S^ (a * c) • S^ -d/c ↑) • H ^ 2 • M a* • S^ -b/a ≈⟨ cright cong (lemma-comm-Hᵏ-w↑ 3 (S^ (a⁻¹ * c) • H)) (cong (sym (lemma-semi-HH↑-CZ^k a)) (cong (lemma-cong↑ _ _ (lemma-Euler′ bb*)) (cleft lemma-comm-Sᵏ-w↑ (toℕ (a * c)) (S^ -d/c)))) ⟩
  Ex • ((S^ (a⁻¹ * c) ↑ • H ↑) • H ^ 3) • (H ↑ ^ 2 • CZ^ a) • (M (-' bb* ⁻¹) • (S^ (- (-a⁻¹ * c))  • H • S^ (-bb⁻¹))) ↑ • (S^ -d/c ↑ • S^ (a * c)) • H ^ 2 • M a* • S^ -b/a ≈⟨ sa (□ • (□ ^ 2 • □) • □ ^ 2 • □ ^ 4 • □ ^ 2 • □ ^ 3 ) (□ ^ 2 • □ • □ ^ 2 • □ ^ 2 • □ ^ 2 • □ ^ 2 • □ ^ 2 • □ ^ 2) auto ⟩
  (Ex • S^ (a⁻¹ * c) ↑) • H ↑ • (H ^ 3 • H ↑ ^ 2) • (CZ^ a • M (-' bb* ⁻¹) ↑) • (S^ (- (-a⁻¹ * c)) ↑  • H ↑) • (S^ (-bb⁻¹) ↑ • S^ -d/c ↑) • (S^ (a * c) • H ^ 2) • M a* • S^ -b/a ≈⟨ cong (lemma-Ex-S^ᵏ↑ (a⁻¹ * c)) (cright cong (rewrite-sym0 100 auto) (cong (lemma-CZ^kM↑ (((-' bb* ⁻¹) ) .proj₁) a ((-' bb* ⁻¹) .proj₂)) (cright cong (lemma-cong↑ _ _ (lemma-S^k+l -bb⁻¹ -d/c)) (cleft word-comm (toℕ (a * c)) 1 (sym (trans assoc (axiom comm-HHS))))))) ⟩
  (S^ (a⁻¹ * c) • Ex) • H ↑ • (H ↑ ^ 2 • H ^ 3) • (M (-' bb* ⁻¹) ↑ • CZ^ (a * ((-' bb* ⁻¹) ⁻¹) .proj₁)) • (S^ (- (-a⁻¹ * c)) ↑  • H ↑) • (S^ (-bb⁻¹ + -d/c) ↑) • (H ^ 2 • S^ (a * c)) • M a* • S^ -b/a ≈⟨ cright cright cright cong (cong (lemma-cong↑ _ _ (aux-MM ((-' bb* ⁻¹) .proj₂) ((a* *' c* ⁻¹) .proj₂) aux)) (refl' (Eq.cong CZ^ aux2))) (cright  cleft refl' (Eq.cong (\ xx -> S^ xx ↑) aux3)) ⟩
  (S^ (a⁻¹ * c) • Ex) • H ↑ • (H ↑ ^ 2 • H ^ 3) • (M (a* *' c* ⁻¹) ↑ • CZ^ c) • (S^ (- (-a⁻¹ * c)) ↑  • H ↑) • (S^ (- (d + - a) * c⁻¹) ↑) • (H ^ 2 • S^ (a * c)) • M a* • S^ -b/a ≈⟨ sa (□ ^ 2 • □ • □ ^ 2 • □ ^ 2 • □ ^ 2 • □ • □ ^ 2 • □ ^ 2) (□ • □ ^ 3 • □ ^ 2 • □ ^ 2 • □ ^ 2 • □ • □ ^ 2 • □) auto ⟩
  S^ (a⁻¹ * c) • (Ex • H ↑ • H ↑ ^ 2) • (H ^ 3 • M (a* *' c* ⁻¹) ↑) • (CZ^ c • S^ (- (-a⁻¹ * c)) ↑)  • (H ↑ • S^ (- (d + - a) * c⁻¹) ↑) • H ^ 2 • (S^ (a * c) • M a*) • S^ -b/a ≈⟨ cright cong (rewrite-swap 100 auto) (cong (lemma-comm-Hᵏ-w↑ 3 (M (a* *' c* ⁻¹))) (cong (aux-comm-CZ^a-S^b↑ c ((- (-a⁻¹ * c)))) (cright cright cleft L01.lemma-S^kM a (a * c) (λ ())))) ⟩
  S^ (a⁻¹ * c) • (H ^ 3 • Ex) • (M (a* *' c* ⁻¹) ↑ • H ^ 3) • (S^ (- (-a⁻¹ * c)) ↑ • CZ^ c)  • (H ↑ • S^ (- (d + - a) * c⁻¹) ↑) • H ^ 2 • (M a* • S^ (a * c * (a⁻¹ * a⁻¹))) • S^ -b/a ≈⟨ sa (□ • □ ^ 2 • □ ^ 2 • □ ^ 2 • □ ^ 2 • □ ^ 2 • □ ^ 2 • □) (□ ^ 2 • □ ^ 2 • □ ^ 2 • □ • (□ ^ 2 • □) • □ ^ 2 • □ ^ 2) auto ⟩
  (S^ (a⁻¹ * c) • H ^ 3) • (Ex • M (a* *' c* ⁻¹) ↑) • (H ^ 3 • S^ (- (-a⁻¹ * c)) ↑) • CZ^ c  • ((H ↑ • S^ (- (d + - a) * c⁻¹) ↑) • H) • (H • M a*) • S^ (a * c * (a⁻¹ * a⁻¹)) • S^ -b/a ≈⟨ cright cong (lemma-Ex-M' (a* *' c* ⁻¹)) (cong (lemma-comm-Hᵏ-w↑ 3 (S^ (- (-a⁻¹ * c)))) (cright cong (sym (lemma-comm-H-w↑ (H • S^ (- (d + - a) * c⁻¹)))) (cong (L01.semi-HM a*) (L01.lemma-S^k+l (a * c * (a⁻¹ * a⁻¹)) -b/a)))) ⟩
  (S^ (a⁻¹ * c) • H ^ 3) • (M (a* *' c* ⁻¹) • Ex) • (S^ (- (-a⁻¹ * c)) ↑ • H ^ 3) • CZ^ c • (H • (H ↑ • S^ (- (d + - a) * c⁻¹) ↑)) • (M (a* ⁻¹) • H) • S^ (a * c * (a⁻¹ * a⁻¹) + -b/a) ≈⟨ sa (□ ^ 2 • □ ^ 2 • □ ^ 2 • □ • □ ^ 3 • □ ^ 2 • □) (□ ^ 3 • □ ^ 2 • □ ^ 3 • □ ^ 2 • □ ^ 3) auto ⟩
  (S^ (a⁻¹ * c) • H ^ 3 • M (a* *' c* ⁻¹)) • (Ex • S^ (- (-a⁻¹ * c)) ↑) • (H ^ 3 • CZ^ c • H) • (H ↑ • S^ (- (d + - a) * c⁻¹) ↑) • M (a* ⁻¹) • H • S^ (a * c * (a⁻¹ * a⁻¹) + -b/a) ≈⟨ cright cong (lemma-Ex-S^ᵏ↑ ((- (-a⁻¹ * c)))) (cright cright cright cright refl' (Eq.cong S^ aux4)) ⟩
  (S^ (a⁻¹ * c) • H ^ 3 • M (a* *' c* ⁻¹)) • (S^ (- (-a⁻¹ * c)) • Ex) • (H ^ 3 • CZ^ c • H) • (H ↑ • S^ (- (d + - a) * c⁻¹) ↑) • M (a* ⁻¹) • H • S^ (- (b + - c) * a⁻¹) ≈⟨ sa (□ ^ 3 • □ ^ 2 • □ • □ ^ 2 • □ ^ 3) (□ ^ 4 • □ ^ 4 • □ ^ 3) auto ⟩
  (S^ (a⁻¹ * c) • H ^ 3 • M (a* *' c* ⁻¹) • S^ (- (-a⁻¹ * c))) • (Ex • CX'^ c • H ↑ • S^ (- (d + - a) * c⁻¹) ↑) • M (a* ⁻¹) • H • S^ (- (b + - c) * a⁻¹) ≈⟨ cleft cright cright L01.lemma-MS^k ac⁻¹ (- (-a⁻¹ * c)) ((a* *' c* ⁻¹) .proj₂) ⟩
  (S^ (a⁻¹ * c) • H ^ 3 • S^ (- (-a⁻¹ * c) * (ac⁻¹ * ac⁻¹)) • M (a* *' c* ⁻¹)) • (Ex • CX'^ c • H ↑ • S^ (- (d + - a) * c⁻¹) ↑) • M (a* ⁻¹) • H • S^ (- (b + - c) * a⁻¹) ≈⟨ cleft cright cright cleft refl' (Eq.cong S^ aux5) ⟩
  (S^ (a⁻¹ * c) • H ^ 3 • S^ ac⁻¹ • M (a* *' c* ⁻¹)) • (Ex • CX'^ c • H ↑ • S^ (- (d + - a) * c⁻¹) ↑) • M (a* ⁻¹) • H • S^ (- (b + - c) * a⁻¹) ≈⟨ cleft cong (refl' (Eq.cong S^ (Eq.sym aux6))) (cright cong (refl' (Eq.cong S^ (Eq.sym (-‿involutive ac⁻¹)))) (L01.aux-MM ((a* *' c* ⁻¹) .proj₂) ((-' -' (a* *' c* ⁻¹)) .proj₂) (Eq.sym (-‿involutive ac⁻¹)))) ⟩
  (S^ (- ((-' (a* *' c* ⁻¹))⁻¹) .proj₁) • H ^ 3 • S^ (- - ac⁻¹) • M (-' -' (a* *' c* ⁻¹))) • (Ex • CX'^ c • H ↑ • S^ (- (d + - a) * c⁻¹) ↑) • M (a* ⁻¹) • H • S^ (- (b + - c) * a⁻¹) ≈⟨ cleft sa (□ • □ ^ 3 • □ ^ 2) (□ ^ 3 • □ ^ 3) auto ⟩
  ((S^ (- ((-' (a* *' c* ⁻¹))⁻¹) .proj₁) • H ^ 2) • H • S^ (- - ac⁻¹) • M (-' -' (a* *' c* ⁻¹))) • (Ex • CX'^ c • H ↑ • S^ (- (d + - a) * c⁻¹) ↑) • M (a* ⁻¹) • H • S^ (- (b + - c) * a⁻¹) ≈⟨ cleft cleft word-comm (toℕ (- ((-' (a* *' c* ⁻¹))⁻¹) .proj₁)) 1 (sym (trans assoc (axiom comm-HHS))) ⟩
  ((H ^ 2 • S^ (- ((-' (a* *' c* ⁻¹))⁻¹) .proj₁)) • H • S^ (- - ac⁻¹) • M (-' -' (a* *' c* ⁻¹))) • (Ex • CX'^ c • H ↑ • S^ (- (d + - a) * c⁻¹) ↑) • M (a* ⁻¹) • H • S^ (- (b + - c) * a⁻¹) ≈⟨ cleft sa (□ ^ 2 • □ ^ 3) (□ • □ ^ 3 • □) auto ⟩
  (H ^ 2 • (S^ (- ((-' (a* *' c* ⁻¹))⁻¹) .proj₁) • H • S^ (- - ac⁻¹)) • M (-' -' (a* *' c* ⁻¹))) • (Ex • CX'^ c • H ↑ • S^ (- (d + - a) * c⁻¹) ↑) • M (a* ⁻¹) • H • S^ (- (b + - c) * a⁻¹) ≈⟨ cleft cright sym (lemma-Euler-v2 (-' (a* *' c* ⁻¹))) ⟩
  (H ^ 2 • H • S^ (- ac⁻¹) • H) • (Ex • CX'^ c • H ↑ • S^ (- (d + - a) * c⁻¹) ↑) • M (a* ⁻¹) • H • S^ (- (b + - c) * a⁻¹) ≈⟨ cleft sa (□ ^ 2 • □ ^ 3) (□ ^ 3 • □ ^ 2) auto ⟩
  (H ^ 3 • S^ (- ac⁻¹) • H) • (Ex • CX'^ c • H ↑ • S^ (- (d + - a) * c⁻¹) ↑) • M (a* ⁻¹) • H • S^ (- (b + - c) * a⁻¹) ≈⟨ cright (cleft sym left-unit) ⟩
  dir • [ l' ]ˡ ∎
  where
  a* = (a , λ ())
  c* = (c , λ ())
  a*⁻¹ = a* ⁻¹
  c*⁻¹ = c* ⁻¹
  a⁻¹ = a*⁻¹ .proj₁
  -a⁻¹ = ((-' a*) ⁻¹) .proj₁
  -a = - a
  c⁻¹ = c*⁻¹ .proj₁
  ac⁻¹ = a * c⁻¹
  -b/a = - b * a⁻¹
  -d/c = - d * c⁻¹
  bb* = ((-' a*) ⁻¹) *' c*
  -bb⁻¹ = (-' bb* ⁻¹) .proj₁
  
  l' : L 2
  l' = (₀ , z≤n)     ,   ((c , d + - a) ∷ []) , ((a , b + - c) , λ ())
  dir = H ^ 3 • S^ (- ac⁻¹) • H
  aux : -bb⁻¹ ≡ a * c⁻¹
  aux = Eq.trans (Eq.cong -_  (Eq.trans (inv-distrib ((-' a*) ⁻¹) c*) (Eq.cong (_* c⁻¹) (inv-involutive (-' a*))) )) (Eq.trans (-‿distribˡ-* (- a) c⁻¹) (Eq.cong (_* c⁻¹) (-‿involutive a)))
  aux2 : (a * ((-' bb* ⁻¹) ⁻¹) .proj₁) ≡ c
  aux2 = Eq.trans (Eq.cong (\ xx -> a * xx) (Eq.trans (inv-cong ((-' bb* ⁻¹)) (a* *' c* ⁻¹) aux) ((Eq.trans (inv-distrib a* (c* ⁻¹)) (Eq.trans (Eq.cong (a⁻¹ *_) (inv-involutive c*)) auto)) )))  (Eq.trans (Eq.sym (*-assoc a a⁻¹ c)) (Eq.trans (Eq.cong (_* c) (lemma-⁻¹ʳ a {{nztoℕ {y = a} {neq0 = λ ()}}})) (*-identityˡ c)))
  aux3 : -bb⁻¹ + -d/c ≡ - (d + - a) * c⁻¹
  aux3 = Eq.sym (Eq.trans (Eq.cong (\ xx -> (- xx * c⁻¹)) (Eq.trans (+-comm d (- a)) auto ) ) (Eq.trans (Eq.cong (_* c⁻¹) ( (Eq.sym (-‿+-comm (- a) d)))) (Eq.trans (Eq.cong (\ xx -> (xx + - d) * c⁻¹) (-‿involutive a)) ((Eq.trans (*-distribʳ-+ c⁻¹ a (- d)) (Eq.cong (_+ -d/c) (Eq.sym aux)))))))

  aux4 : a * c * (a⁻¹ * a⁻¹) + -b/a ≡ - (b + - c) * a⁻¹
  aux4 = Eq.trans (Eq.cong (\ xx -> xx * (a⁻¹ * a⁻¹) + -b/a) (*-comm a c)) (Eq.trans (Eq.cong (\ xx -> xx + -b/a) (*-assoc c a ((a⁻¹ * a⁻¹)))) (Eq.trans (Eq.cong (\ xx -> c * xx + -b/a) (Eq.sym (*-assoc a a⁻¹ a⁻¹))) (Eq.trans (Eq.cong (\ xx -> c * (xx * a⁻¹) + -b/a) (lemma-⁻¹ʳ a {{nztoℕ {y = a} {neq0 = λ ()}}})) (Eq.trans (Eq.cong (\ xx -> c * xx + -b/a) (*-identityˡ a⁻¹)) (Eq.trans (+-comm (c * a⁻¹) (- b * a⁻¹)) (Eq.trans (Eq.sym (*-distribʳ-+ a⁻¹ (- b) c)) (Eq.trans (Eq.cong (\ xx -> (- b + xx) * a⁻¹) (Eq.sym (-‿involutive c))) (Eq.sym (Eq.cong (_* a⁻¹) (Eq.sym (-‿+-comm b (- c))))))))))))

  aux5a1 : a⁻¹ * c * ac⁻¹ ≡ ₁
  aux5a1 = Eq.trans (Eq.cong (_* ac⁻¹) (*-comm a⁻¹ c)) (Eq.trans (*-assoc c a⁻¹ ac⁻¹) (Eq.trans (Eq.cong (c *_) (Eq.sym (*-assoc a⁻¹ a c⁻¹))) (Eq.trans (Eq.cong (c *_) (Eq.cong (_* c⁻¹) (lemma-⁻¹ˡ a {{nztoℕ {y = a} {neq0 = λ ()}}}))) (Eq.trans (Eq.cong (c *_) (*-identityˡ c⁻¹)) (lemma-⁻¹ʳ c {{nztoℕ {y = c} {neq0 = λ ()}}})))))

  aux5 : - (-a⁻¹ * c) * (ac⁻¹ * ac⁻¹) ≡ ac⁻¹
  aux5 = Eq.trans (Eq.cong (_* (ac⁻¹ * ac⁻¹)) (-‿distribˡ-* -a⁻¹ c)) (Eq.trans (Eq.cong (λ xx → xx * c * (ac⁻¹ * ac⁻¹)) (Eq.trans (Eq.cong -_ (inv-neg-comm a*)) (-‿involutive a⁻¹))) (Eq.trans (Eq.sym (*-assoc (a⁻¹ * c) ac⁻¹ ac⁻¹)) (Eq.trans (Eq.cong (_* ac⁻¹) aux5a1) (*-identityˡ ac⁻¹))))
  aux6 : (- ((-' (a* *' c* ⁻¹))⁻¹) .proj₁) ≡ a⁻¹ * c
  aux6 = Eq.trans (Eq.cong -_ (inv-neg-comm (a* *' c* ⁻¹))) (Eq.trans (-‿involutive ((((a* *' c* ⁻¹))⁻¹) .proj₁)) (Eq.trans (inv-distrib a* (c* ⁻¹)) (Eq.trans (Eq.cong (a⁻¹ *_) (inv-involutive c*)) auto)))




lemma-dir-and-l' l@((₀ , z≤n) , ((c@₀ , d@₀) ∷ []) , ((a@(₁₊ _) , b@₀) , nzx)) =  begin
  [ l ]ˡ • CZ ≈⟨  cleft cong left-unit refl ⟩
  ([ c , d ]ᵇ • M a*⁻¹ • H • S^ -b/a) • CZ ≈⟨ sa (□ ^ 4 • □) (□ • □ ^ 2 • □ ^ 2) auto ⟩
  [ c , d ]ᵇ • (M a*⁻¹ • H) • S^ -b/a • CZ ≈⟨ cright cong (sym (L01.semi-HM a*)) (word-comm (toℕ -b/a) 1 (sym (axiom comm-CZ-S↓))) ⟩
  [ c , d ]ᵇ • (H • M a*) • CZ • S^ -b/a ≈⟨ sa (□ ^ 4 • □ ^ 2 • □ ^ 2) (□ ^ 5 • □ ^ 2 • □) auto ⟩
  (Ex • H ^ 3 • CZ^ d • H ^ 2) • (M a* • CZ) • S^ -b/a ≈⟨ cong (cright cright lemma-semi-CZ^k-HH↓ d) (cleft axiom (semi-M↓CZ a*)) ⟩
  (Ex • H ^ 3 • H ^ 2 • CZ^ (- d)) • (CZ^ a • M a*) • S^ -b/a ≈⟨ sa (□ ^ 4 • □ ^ 2 • □) (□ ^ 3 • □ ^ 2 • □ ^ 2) auto ⟩
  (Ex • H ^ 3 • H ^ 2) • (CZ^ (- d) • CZ^ a) • M a* • S^ -b/a ≈⟨ cright cleft lemma-CZ^k+l (- d) a ⟩
  (Ex • H ^ 3 • H ^ 2) • CZ^ (- d + a) • M a* • S^ -b/a ≈⟨ sa (□ ^ 3 • □ ^ 2) (□ ^ 2 • □ ^ 2 • □ ) auto ⟩
  (Ex • H ^ 3) • (H ^ 2 • CZ^ (- d + a)) • M a* • S^ -b/a ≈⟨ cright cleft lemma-semi-HH↓-CZ^k' (- d + a) ⟩
  (Ex • H ^ 3) • (CZ^ (- (- d + a)) • HH) • M a* • S^ -b/a ≈⟨ cright cleft cleft refl' (Eq.cong CZ^ (Eq.trans (Eq.sym (-‿+-comm (- d) a)) (Eq.cong (_+ - a) (-‿involutive d)))) ⟩
  (Ex • H ^ 3) • (CZ^ (d + - a) • HH) • M a* • S^ -b/a ≈⟨ sa (□ ^ 2 • □ ^ 3 • □ ^ 2) (□ • □ ^ 3 • □ ^ 2 • □) auto ⟩
  Ex • (H ^ 3 • CZ^ (d + - a) • H) • (H • M a*) • S^ -b/a ≈⟨ cright cright cleft L01.semi-HM a* ⟩
  Ex • (H ^ 3 • CZ^ (d + - a) • H) • (M (a* ⁻¹) • H) • S^ -b/a ≈⟨ sa (□ • □ ^ 3 • □ ^ 2 • □) (□ ^ 4 • □ ^ 3) auto ⟩
  (Ex • H ^ 3 • CZ^ (d + - a) • H) • M (a* ⁻¹) • H • S^ -b/a ≈⟨ sym left-unit ⟩
  dir • (Ex • H ^ 3 • CZ^ (d + - a) • H) • M (a* ⁻¹) • H • S^ -b/a ≈⟨ refl ⟩
  dir • ([ c , d + - a ]ᵇ • [ ((a , b) , λ ()) ]ᵃ) ≈⟨ cright cright refl' (aux-AA p-2 (((a , b) , λ ())) (((a , b + - c) , λ ())) (Eq.cong ((a ,_)) (Eq.sym (Eq.trans (Eq.cong (\ xx -> b + xx) -0#≈0#) (+-identityʳ b))))) ⟩
  dir • ([ c , d + - a ]ᵇ • [ ((a , b + - c) , λ ()) ]ᵃ) ≈⟨ sym (trans left-unit assoc) ⟩
  dir • [ l' ]ˡ ∎
  where
  a* = (a , λ ())
  a*⁻¹ = a* ⁻¹
  a⁻¹ = a*⁻¹ .proj₁
  -b/a = - b * a⁻¹
  
  l' : L 2
  l' = (₀ , z≤n)     ,   ((c , d + - a) ∷ []) , ((a , b + - c) , λ ())
  dir = ε


lemma-dir-and-l' l@((₀ , z≤n) , ((c@₀ , d@(₁₊ _)) ∷ []) , ((a@(₁₊ _) , b@₀) , nzx)) =  begin
  [ l ]ˡ • CZ ≈⟨  cleft cong left-unit refl ⟩
  ([ c , d ]ᵇ • M a*⁻¹ • H • S^ -b/a) • CZ ≈⟨ sa (□ ^ 4 • □) (□ • □ ^ 2 • □ ^ 2) auto ⟩
  [ c , d ]ᵇ • (M a*⁻¹ • H) • S^ -b/a • CZ ≈⟨ cright cong (sym (L01.semi-HM a*)) (word-comm (toℕ -b/a) 1 (sym (axiom comm-CZ-S↓))) ⟩
  [ c , d ]ᵇ • (H • M a*) • CZ • S^ -b/a ≈⟨ sa (□ ^ 4 • □ ^ 2 • □ ^ 2) (□ ^ 5 • □ ^ 2 • □) auto ⟩
  (Ex • H ^ 3 • CZ^ d • H ^ 2) • (M a* • CZ) • S^ -b/a ≈⟨ cong (cright cright lemma-semi-CZ^k-HH↓ d) (cleft axiom (semi-M↓CZ a*)) ⟩
  (Ex • H ^ 3 • H ^ 2 • CZ^ (- d)) • (CZ^ a • M a*) • S^ -b/a ≈⟨ sa (□ ^ 4 • □ ^ 2 • □) (□ ^ 3 • □ ^ 2 • □ ^ 2) auto ⟩
  (Ex • H ^ 3 • H ^ 2) • (CZ^ (- d) • CZ^ a) • M a* • S^ -b/a ≈⟨ cright cleft lemma-CZ^k+l (- d) a ⟩
  (Ex • H ^ 3 • H ^ 2) • CZ^ (- d + a) • M a* • S^ -b/a ≈⟨ sa (□ ^ 3 • □ ^ 2) (□ ^ 2 • □ ^ 2 • □ ) auto ⟩
  (Ex • H ^ 3) • (H ^ 2 • CZ^ (- d + a)) • M a* • S^ -b/a ≈⟨ cright cleft lemma-semi-HH↓-CZ^k' (- d + a) ⟩
  (Ex • H ^ 3) • (CZ^ (- (- d + a)) • HH) • M a* • S^ -b/a ≈⟨ cright cleft cleft refl' (Eq.cong CZ^ (Eq.trans (Eq.sym (-‿+-comm (- d) a)) (Eq.cong (_+ - a) (-‿involutive d)))) ⟩
  (Ex • H ^ 3) • (CZ^ (d + - a) • HH) • M a* • S^ -b/a ≈⟨ sa (□ ^ 2 • □ ^ 3 • □ ^ 2) (□ • □ ^ 3 • □ ^ 2 • □) auto ⟩
  Ex • (H ^ 3 • CZ^ (d + - a) • H) • (H • M a*) • S^ -b/a ≈⟨ cright cright cleft L01.semi-HM a* ⟩
  Ex • (H ^ 3 • CZ^ (d + - a) • H) • (M (a* ⁻¹) • H) • S^ -b/a ≈⟨ sa (□ • □ ^ 3 • □ ^ 2 • □) (□ ^ 4 • □ ^ 3) auto ⟩
  (Ex • H ^ 3 • CZ^ (d + - a) • H) • M (a* ⁻¹) • H • S^ -b/a ≈⟨ sym left-unit ⟩
  dir • (Ex • H ^ 3 • CZ^ (d + - a) • H) • M (a* ⁻¹) • H • S^ -b/a ≈⟨ refl ⟩
  dir • ([ c , d + - a ]ᵇ • [ ((a , b) , λ ()) ]ᵃ) ≈⟨ cright cright refl' (aux-AA p-2 (((a , b) , λ ())) (((a , b + - c) , λ ())) (Eq.cong ((a ,_)) (Eq.sym (Eq.trans (Eq.cong (\ xx -> b + xx) -0#≈0#) (+-identityʳ b))))) ⟩
  dir • ([ c , d + - a ]ᵇ • [ ((a , b + - c) , λ ()) ]ᵃ) ≈⟨ sym (trans left-unit assoc) ⟩
  dir • [ l' ]ˡ ∎
  where
  a* = (a , λ ())
  a*⁻¹ = a* ⁻¹
  a⁻¹ = a*⁻¹ .proj₁
  -b/a = - b * a⁻¹
  
  l' : L 2
  l' = (₀ , z≤n)     ,   ((c , d + - a) ∷ []) , ((a , b + - c) , λ ())
  dir = ε


lemma-dir-and-l' l@((₀ , z≤n) , ((c@₀ , d@(₁₊ _)) ∷ []) , ((a@(₁₊ _) , b@(₁₊ _)) , nzx)) =  begin
  [ l ]ˡ • CZ ≈⟨  cleft cong left-unit refl ⟩
  ([ c , d ]ᵇ • M a*⁻¹ • H • S^ -b/a) • CZ ≈⟨ sa (□ ^ 4 • □) (□ • □ ^ 2 • □ ^ 2) auto ⟩
  [ c , d ]ᵇ • (M a*⁻¹ • H) • S^ -b/a • CZ ≈⟨ cright cong (sym (L01.semi-HM a*)) (word-comm (toℕ -b/a) 1 (sym (axiom comm-CZ-S↓))) ⟩
  [ c , d ]ᵇ • (H • M a*) • CZ • S^ -b/a ≈⟨ sa (□ ^ 4 • □ ^ 2 • □ ^ 2) (□ ^ 5 • □ ^ 2 • □) auto ⟩
  (Ex • H ^ 3 • CZ^ d • H ^ 2) • (M a* • CZ) • S^ -b/a ≈⟨ cong (cright cright lemma-semi-CZ^k-HH↓ d) (cleft axiom (semi-M↓CZ a*)) ⟩
  (Ex • H ^ 3 • H ^ 2 • CZ^ (- d)) • (CZ^ a • M a*) • S^ -b/a ≈⟨ sa (□ ^ 4 • □ ^ 2 • □) (□ ^ 3 • □ ^ 2 • □ ^ 2) auto ⟩
  (Ex • H ^ 3 • H ^ 2) • (CZ^ (- d) • CZ^ a) • M a* • S^ -b/a ≈⟨ cright cleft lemma-CZ^k+l (- d) a ⟩
  (Ex • H ^ 3 • H ^ 2) • CZ^ (- d + a) • M a* • S^ -b/a ≈⟨ sa (□ ^ 3 • □ ^ 2) (□ ^ 2 • □ ^ 2 • □ ) auto ⟩
  (Ex • H ^ 3) • (H ^ 2 • CZ^ (- d + a)) • M a* • S^ -b/a ≈⟨ cright cleft lemma-semi-HH↓-CZ^k' (- d + a) ⟩
  (Ex • H ^ 3) • (CZ^ (- (- d + a)) • HH) • M a* • S^ -b/a ≈⟨ cright cleft cleft refl' (Eq.cong CZ^ (Eq.trans (Eq.sym (-‿+-comm (- d) a)) (Eq.cong (_+ - a) (-‿involutive d)))) ⟩
  (Ex • H ^ 3) • (CZ^ (d + - a) • HH) • M a* • S^ -b/a ≈⟨ sa (□ ^ 2 • □ ^ 3 • □ ^ 2) (□ • □ ^ 3 • □ ^ 2 • □) auto ⟩
  Ex • (H ^ 3 • CZ^ (d + - a) • H) • (H • M a*) • S^ -b/a ≈⟨ cright cright cleft L01.semi-HM a* ⟩
  Ex • (H ^ 3 • CZ^ (d + - a) • H) • (M (a* ⁻¹) • H) • S^ -b/a ≈⟨ sa (□ • □ ^ 3 • □ ^ 2 • □) (□ ^ 4 • □ ^ 3) auto ⟩
  (Ex • H ^ 3 • CZ^ (d + - a) • H) • M (a* ⁻¹) • H • S^ -b/a ≈⟨ sym left-unit ⟩
  dir • (Ex • H ^ 3 • CZ^ (d + - a) • H) • M (a* ⁻¹) • H • S^ -b/a ≈⟨ refl ⟩
  dir • ([ c , d + - a ]ᵇ • [ ((a , b) , λ ()) ]ᵃ) ≈⟨ cright cright refl' (aux-AA p-2 (((a , b) , λ ())) (((a , b + - c) , λ ())) (Eq.cong ((a ,_)) (Eq.sym (Eq.trans (Eq.cong (\ xx -> b + xx) -0#≈0#) (+-identityʳ b))))) ⟩
  dir • ([ c , d + - a ]ᵇ • [ ((a , b + - c) , λ ()) ]ᵃ) ≈⟨ sym (trans left-unit assoc) ⟩
  dir • [ l' ]ˡ ∎
  where
  a* = (a , λ ())
  a*⁻¹ = a* ⁻¹
  a⁻¹ = a*⁻¹ .proj₁
  -b/a = - b * a⁻¹
  
  l' : L 2
  l' = (₀ , z≤n)     ,   ((c , d + - a) ∷ []) , ((a , b + - c) , λ ())
  dir = ε


lemma-dir-and-l' l@((₀ , z≤n) , ((c@₀ , d@₀) ∷ []) , ((a@(₁₊ _) , b@(₁₊ _)) , nzx)) =  begin
  [ l ]ˡ • CZ ≈⟨  cleft cong left-unit refl ⟩
  ([ c , d ]ᵇ • M a*⁻¹ • H • S^ -b/a) • CZ ≈⟨ sa (□ ^ 4 • □) (□ • □ ^ 2 • □ ^ 2) auto ⟩
  [ c , d ]ᵇ • (M a*⁻¹ • H) • S^ -b/a • CZ ≈⟨ cright cong (sym (L01.semi-HM a*)) (word-comm (toℕ -b/a) 1 (sym (axiom comm-CZ-S↓))) ⟩
  [ c , d ]ᵇ • (H • M a*) • CZ • S^ -b/a ≈⟨ sa (□ ^ 4 • □ ^ 2 • □ ^ 2) (□ ^ 5 • □ ^ 2 • □) auto ⟩
  (Ex • H ^ 3 • CZ^ d • H ^ 2) • (M a* • CZ) • S^ -b/a ≈⟨ cong (cright cright lemma-semi-CZ^k-HH↓ d) (cleft axiom (semi-M↓CZ a*)) ⟩
  (Ex • H ^ 3 • H ^ 2 • CZ^ (- d)) • (CZ^ a • M a*) • S^ -b/a ≈⟨ sa (□ ^ 4 • □ ^ 2 • □) (□ ^ 3 • □ ^ 2 • □ ^ 2) auto ⟩
  (Ex • H ^ 3 • H ^ 2) • (CZ^ (- d) • CZ^ a) • M a* • S^ -b/a ≈⟨ cright cleft lemma-CZ^k+l (- d) a ⟩
  (Ex • H ^ 3 • H ^ 2) • CZ^ (- d + a) • M a* • S^ -b/a ≈⟨ sa (□ ^ 3 • □ ^ 2) (□ ^ 2 • □ ^ 2 • □ ) auto ⟩
  (Ex • H ^ 3) • (H ^ 2 • CZ^ (- d + a)) • M a* • S^ -b/a ≈⟨ cright cleft lemma-semi-HH↓-CZ^k' (- d + a) ⟩
  (Ex • H ^ 3) • (CZ^ (- (- d + a)) • HH) • M a* • S^ -b/a ≈⟨ cright cleft cleft refl' (Eq.cong CZ^ (Eq.trans (Eq.sym (-‿+-comm (- d) a)) (Eq.cong (_+ - a) (-‿involutive d)))) ⟩
  (Ex • H ^ 3) • (CZ^ (d + - a) • HH) • M a* • S^ -b/a ≈⟨ sa (□ ^ 2 • □ ^ 3 • □ ^ 2) (□ • □ ^ 3 • □ ^ 2 • □) auto ⟩
  Ex • (H ^ 3 • CZ^ (d + - a) • H) • (H • M a*) • S^ -b/a ≈⟨ cright cright cleft L01.semi-HM a* ⟩
  Ex • (H ^ 3 • CZ^ (d + - a) • H) • (M (a* ⁻¹) • H) • S^ -b/a ≈⟨ sa (□ • □ ^ 3 • □ ^ 2 • □) (□ ^ 4 • □ ^ 3) auto ⟩
  (Ex • H ^ 3 • CZ^ (d + - a) • H) • M (a* ⁻¹) • H • S^ -b/a ≈⟨ sym left-unit ⟩
  dir • (Ex • H ^ 3 • CZ^ (d + - a) • H) • M (a* ⁻¹) • H • S^ -b/a ≈⟨ refl ⟩
  dir • ([ c , d + - a ]ᵇ • [ ((a , b) , λ ()) ]ᵃ) ≈⟨ cright cright refl' (aux-AA p-2 (((a , b) , λ ())) (((a , b + - c) , λ ())) (Eq.cong ((a ,_)) (Eq.sym (Eq.trans (Eq.cong (\ xx -> b + xx) -0#≈0#) (+-identityʳ b))))) ⟩
  dir • ([ c , d + - a ]ᵇ • [ ((a , b + - c) , λ ()) ]ᵃ) ≈⟨ sym (trans left-unit assoc) ⟩
  dir • [ l' ]ˡ ∎
  where
  a* = (a , λ ())
  a*⁻¹ = a* ⁻¹
  a⁻¹ = a*⁻¹ .proj₁
  -b/a = - b * a⁻¹
  
  l' : L 2
  l' = (₀ , z≤n)     ,   ((c , d + - a) ∷ []) , ((a , b + - c) , λ ())
  dir = ε



lemma-dir-and-l' l@((₀ , z≤n) , ((c@₀ , d@₀) ∷ []) , ((a@₀ , b@(₁₊ _)) , nzx)) with b ≟ c
... | yes ()
... | no neq = begin
  [ l ]ˡ • CZ ≈⟨  cleft cong left-unit right-unit ⟩
  ([ c , d ]ᵇ • M b*⁻¹) • CZ ≈⟨ assoc ⟩
  [ c , d ]ᵇ • M b*⁻¹ • CZ ≈⟨ cright axiom (semi-M↓CZ b*⁻¹) ⟩
  [ c , d ]ᵇ • CZ^ b⁻¹ • M b*⁻¹ ≈⟨ cleft rewrite-sym0 100 auto ⟩
  Ex • CZ^ b⁻¹ • M b*⁻¹ ≈⟨ sym assoc ⟩
  (Ex • CZ^ b⁻¹) • M b*⁻¹ ≈⟨ cleft word-comm 1 (toℕ b⁻¹) (sym lemma-comm-Ex-CZ-n) ⟩
  (CZ^ b⁻¹ • Ex) • M b*⁻¹ ≈⟨ assoc ⟩
  CZ^ b⁻¹ • Ex • M b*⁻¹ ≈⟨ refl ⟩
  dir • (Ex • M b*⁻¹) ≈⟨ cright cong (rewrite-sym0 100 auto) (L01.aux-MM (b*⁻¹ .proj₂) ([b-c]⁻¹ .proj₂) (inv-cong (b , (λ ()))  ((b + - c , b-c≠0)) ((Eq.sym (Eq.trans (Eq.cong (b +_ ) -0#≈0#) (+-identityʳ b)))))) ⟩
  dir • ([ c , d ]ᵇ • M [b-c]⁻¹) ≈⟨ cright cleft refl' (Eq.cong (\ xx -> [ c , xx ]ᵇ) (Eq.sym (Eq.trans (Eq.cong (d +_ ) -0#≈0#) (+-identityʳ d)))) ⟩
  dir • ([ c , d + - a ]ᵇ • M [b-c]⁻¹) ≈⟨ cright sym (cright aux-abox-nzb (b + - c) b-c≠0) ⟩
  dir • ([ c , d + - a ]ᵇ • [ ((a , b + - c) , nzp) ]ᵃ) ≈⟨ cright cong (sym left-unit) refl ⟩
  dir • [ l' ]ˡ ∎
  where
  b*⁻¹ = (b , λ ()) ⁻¹
  b⁻¹ = b*⁻¹ .proj₁
  nzp : (a , b + - c) ≢ (₀ , ₀)
  nzp eqp = (neq (b-c=0⇒b=c b c (Eq.cong proj₂ eqp)))
  b-c≠0 : b + - c ≢ ₀
  b-c≠0 eq = neq (b-c=0⇒b=c b c eq)
  [b-c]⁻¹ = (b + - c , b-c≠0) ⁻¹
  
  l' : L 2
  l' = (₀ , z≤n)     ,   ((c , d + - a) ∷ []) , ((a , b + - c) , nzp)
  dir = CZ^ b⁻¹


lemma-dir-and-l' l@((₀ , z≤n) , ((c@₀ , d@(₁₊ _)) ∷ []) , ((a@₀ , b@(₁₊ _)) , nzx)) with b ≟ c
... | yes ()
... | no neq = begin
  [ l ]ˡ • CZ ≈⟨  cleft cong left-unit right-unit ⟩
  ([ c , d ]ᵇ • M b*⁻¹) • CZ ≈⟨ assoc ⟩
  [ c , d ]ᵇ • M b*⁻¹ • CZ ≈⟨ cright axiom (semi-M↓CZ b*⁻¹) ⟩
  [ c , d ]ᵇ • CZ^ b⁻¹ • M b*⁻¹ ≈⟨ cleft rewrite-sym0 100 auto ⟩
  (Ex • CX'^ d) • CZ^ b⁻¹ • M b*⁻¹ ≈⟨ special-assoc (□ ^ 2 • □ ^ 2) (□ • □ ^ 2 • □) auto ⟩
  Ex • (CX'^ d • CZ^ b⁻¹) • M b*⁻¹ ≈⟨ cright cleft lemma-semi-CX'^kCZ^l (d , (λ ())) b⁻¹ ⟩
  Ex • (S^ (- b⁻¹d + - b⁻¹d) ↑ • CZ^ b⁻¹ • CX'^ d) • M b*⁻¹ ≈⟨ sa (□ • □ ^ 3 • □) (□ ^ 2 • □ ^ 3) auto ⟩
  (Ex • S^ (- b⁻¹d + - b⁻¹d) ↑) • CZ^ b⁻¹ • CX'^ d • M b*⁻¹ ≈⟨ cleft lemma-Ex-S^ᵏ↑ (- b⁻¹d + - b⁻¹d) ⟩
  (S^ (- b⁻¹d + - b⁻¹d) • Ex) • CZ^ b⁻¹ • CX'^ d • M b*⁻¹ ≈⟨ sa (□ ^ 2 • □ ^ 2) (□ • □ ^ 2 • □) auto ⟩
  S^ (- b⁻¹d + - b⁻¹d) • (Ex • CZ^ b⁻¹) • CX'^ d • M b*⁻¹ ≈⟨ cright cleft word-comm 1 (toℕ b⁻¹) (sym lemma-comm-Ex-CZ-n) ⟩
  S^ (- b⁻¹d + - b⁻¹d) • (CZ^ b⁻¹ • Ex) • CX'^ d • M b*⁻¹ ≈⟨ sa (□ • □ ^ 2 • □ ^ 2) (□ ^ 2 • □ ^ 2 • □) auto ⟩
  (S^ (- b⁻¹d + - b⁻¹d) • CZ^ b⁻¹) • (Ex • CX'^ d) • M b*⁻¹ ≈⟨ refl ⟩
  dir • ((Ex • CX'^ d) • M b*⁻¹) ≈⟨ cright cong (rewrite-sym0 100 auto) (L01.aux-MM (b*⁻¹ .proj₂) ([b-c]⁻¹ .proj₂) (inv-cong (b , (λ ()))  ((b + - c , b-c≠0)) ((Eq.sym (Eq.trans (Eq.cong (b +_ ) -0#≈0#) (+-identityʳ b)))))) ⟩
  dir • ([ c , d ]ᵇ • M [b-c]⁻¹) ≈⟨ cright cleft refl' (Eq.cong (\ xx -> [ c , xx ]ᵇ) (Eq.sym (Eq.trans (Eq.cong (d +_ ) -0#≈0#) (+-identityʳ d)))) ⟩
  dir • ([ c , d + - a ]ᵇ • M [b-c]⁻¹) ≈⟨ cright sym (cright aux-abox-nzb (b + - c) b-c≠0) ⟩
  dir • ([ c , d + - a ]ᵇ • [ ((a , b + - c) , nzp) ]ᵃ) ≈⟨ cright cong (sym left-unit) refl ⟩
  dir • [ l' ]ˡ ∎
  where
  b*⁻¹ = (b , λ ()) ⁻¹
  b⁻¹ = b*⁻¹ .proj₁
  d*⁻¹ = (d , λ ()) ⁻¹
  d⁻¹ = d*⁻¹ .proj₁
  b⁻¹d = b⁻¹ * d
  nzp : (a , b + - c) ≢ (₀ , ₀)
  nzp eqp = (neq (b-c=0⇒b=c b c (Eq.cong proj₂ eqp)))
  b-c≠0 : b + - c ≢ ₀
  b-c≠0 eq = neq (b-c=0⇒b=c b c eq)
  [b-c]⁻¹ = (b + - c , b-c≠0) ⁻¹
  
  l' : L 2
  l' = (₀ , z≤n)     ,   ((c , d + - a) ∷ []) , ((a , b + - c) , nzp)
  dir = S^ (- b⁻¹d + - b⁻¹d) • CZ^ b⁻¹


lemma-dir-and-l' l@((₀ , z≤n) , ((c@(₁₊ _) , d) ∷ []) , ((a@₀ , b@(₁₊ _)) , nzx)) with b ≟ c
... | yes eq  = bbc dir-acz (CZ^ (- ₁)) claim 
  where
  b⁻¹ = (((b , λ ())) ⁻¹) .proj₁
  dir-acz : Word (Gen 2)
  dir-acz = H • CZ^ b⁻¹ • H ^ 3
  dir = dir-acz ⁻¹ʷ • HH
  l' : L 2
  l' = (₁ , s≤s z≤n) , [] , ((b , d) , λ ())

  nz-b = (-' (b , λ ())) .proj₂
  nz--b : - - b ≢ ₀
  nz--b = (-' (- b , nz-b)) .proj₂
  nz--bp : (₀ , - - b) ≢ (₀ , ₀)
  nz--bp = aux-b≠0⇒ab≠0 ₀ (- - b) nz--b
  nz-bp : (₀ , - b) ≢ (₀ , ₀)
  nz-bp = aux-b≠0⇒ab≠0 ₀ (- b) nz-b

  aux-dir-acz' : dir-acz • dir ≈ HH
  aux-dir-acz' = begin
    dir-acz • dir-acz ⁻¹ʷ • HH ≈⟨ sym assoc ⟩
    (dir-acz • dir-acz ⁻¹ʷ) • HH ≈⟨ cleft lemma-right-inverse ⟩
    ε • HH ≈⟨ left-unit ⟩
    HH ∎

  claim : dir-acz • ([ l ]ˡ • CZ) • CZ^ (- ₁) ≈ dir-acz • (dir • [ l' ]ˡ) • CZ^ (- ₁)
  claim = begin
    dir-acz • ([ l ]ˡ • CZ) • CZ^ (- ₁) ≈⟨ special-assoc (□ • □ ^ 2 • □) (□ ^ 4) auto ⟩
    dir-acz • [ l ]ˡ • CZ • CZ^ (- ₁) ≈⟨ cright cright trans (lemma-CZ^k+l ₁ (- ₁)) (refl' (Eq.cong CZ^ (+-inverseʳ ₁))) ⟩
    dir-acz • [ l ]ˡ • ε ≈⟨ cright right-unit ⟩
    dir-acz • [ l ]ˡ ≈⟨ cright trans assoc left-unit ⟩
    dir-acz • [ c , d ]ᵇ • [ (₀ , b) , (λ ()) ]ᵃ ≈⟨ cright cleft refl' (Eq.cong (\ xx -> [ xx , d ]ᵇ) (Eq.sym eq)) ⟩
    dir-acz • [ b , d ]ᵇ • [ (₀ , b) , (λ ()) ]ᵃ ≈⟨ cright cright refl' (aux-AA 1 ((₀ , b) , (λ ())) ((₀ , - - b) , nz--bp) (≡×≡⇒≡ (auto , Eq.sym (-‿involutive b))) ) ⟩
    dir-acz • [ b , d ]ᵇ • [ (₀ , - - b) , nz--bp ]ᵃ ≈⟨ cright cright sym (lemma-A-HH' 1 (- b)  (nz-b)) ⟩
    dir-acz • [ b , d ]ᵇ • [ ((₀ , - b) , nz-bp) ]ᵃ • HH ≈⟨ special-assoc (□ ^ 4) (□ ^ 3 • □) auto ⟩
    (dir-acz • [ b , d ]ᵇ • [ ((₀ , - b) , nz-bp) ]ᵃ) • HH ≈⟨ cleft sym (lemma-A-CZ-2 (b , λ ()) d) ⟩
    ([ ((b , d) , λ ()) ]ᵃ ↑ • CZ) • HH ≈⟨ assoc ⟩
    [ ((b , d) , λ ()) ]ᵃ ↑ • CZ • HH ≈⟨ cright sym lemma-semi-CZ-HH↓' ⟩
    [ ((b , d) , λ ()) ]ᵃ ↑ • HH • CZ^ (- ₁) ≈⟨ sym assoc ⟩
    ([ ((b , d) , λ ()) ]ᵃ ↑ • HH) • CZ^ (- ₁) ≈⟨ cleft sym (lemma-comm-Hᵏ-w↑ 2 [ ((b , d) , λ ()) ]ᵃ) ⟩
    (HH • [ ((b , d) , λ ()) ]ᵃ ↑) • CZ^ (- ₁) ≈⟨ assoc ⟩
    HH • [ ((b , d) , λ ()) ]ᵃ ↑ • CZ^ (- ₁) ≈⟨ cright cleft sym left-unit ⟩
    HH • [ l' ]ˡ • CZ^ (- ₁) ≈⟨ cleft sym aux-dir-acz' ⟩
    (dir-acz • dir) • [ l' ]ˡ • CZ^ (- ₁) ≈⟨ special-assoc (□ ^ 2 • □ ^ 2) (□ • □ ^ 2 • □) auto ⟩
    dir-acz • (dir • [ l' ]ˡ) • CZ^ (- ₁) ∎

... | no neq = begin
  [ l ]ˡ • CZ ≈⟨ cleft cong left-unit right-unit ⟩
  ([ c , d ]ᵇ • M (b* ⁻¹)) • CZ ≈⟨ assoc ⟩
  [ c , d ]ᵇ • M (b* ⁻¹) • CZ ≈⟨ cright axiom (semi-M↓CZ (b* ⁻¹)) ⟩
  [ c , d ]ᵇ • CZ^ b⁻¹ • M (b* ⁻¹) ≈⟨ sa (□ ^ 4 • □ ^ 2) (□ ^ 3 • □ ^ 2 • □) auto ⟩
  (Ex • (H ^ 3 • CZ^ c • H) • H ↑) • (S^ -d/c ↑ • CZ^ b⁻¹) • M (b* ⁻¹) ≈⟨ cong (cright cleft cright sym left-unit) (cleft sym (aux-comm-CZ^a-S^b↑ b⁻¹ -d/c)) ⟩
  (Ex • (H ^ 3 • ε • CZ^ c • H) • H ↑) • (CZ^ b⁻¹ • S^ -d/c ↑) • M (b* ⁻¹) ≈⟨ cleft cright cleft cright cleft sym (lemma-cong↑ _ _ (aux-M-mul c*)) ⟩
  (Ex • (H ^ 3 • (M c* ↑ • M (c* ⁻¹) ↑) • CZ^ c • H) • H ↑) • (CZ^ b⁻¹ • S^ -d/c ↑) • M (b* ⁻¹) ≈⟨ sa ((□ • (□ • □ ^ 2 • □ ^ 2) • □) • □ ^ 2 • □) (□ ^ 3 • □ ^ 2 • □ ^ 5) auto ⟩
  (Ex • H ^ 3 • M c* ↑) • (M (c* ⁻¹) ↑ • CZ^ c) • H • H ↑ • CZ^ b⁻¹ • S^ -d/c ↑ • M (b* ⁻¹) ≈⟨ cright cleft lemma-M↑CZ^k c⁻¹ c ((c* ⁻¹) .proj₂) ⟩
  (Ex • H ^ 3 • M c* ↑) • (CZ^ (c * c⁻¹) • M (c* ⁻¹) ↑) • H • H ↑ • CZ^ b⁻¹ • S^ -d/c ↑ • M (b* ⁻¹) ≈⟨ cright cleft cleft refl' (Eq.cong CZ^ (lemma-⁻¹ʳ c {{nztoℕ {y = c} {neq0 = λ ()}}})) ⟩
  (Ex • H ^ 3 • M c* ↑) • (CZ • M (c* ⁻¹) ↑) • H • H ↑ • CZ^ b⁻¹ • S^ -d/c ↑ • M (b* ⁻¹) ≈⟨ cright sa (□ ^ 2 • □ ^ 2) (□ • □ ^ 2 • □) auto ⟩
  (Ex • H ^ 3 • M c* ↑) • CZ • (M (c* ⁻¹) ↑ • H) • H ↑ • CZ^ b⁻¹ • S^ -d/c ↑ • M (b* ⁻¹) ≈⟨ cright cright cleft sym (lemma-comm-H-w↑ (M (c* ⁻¹))) ⟩
  (Ex • H ^ 3 • M c* ↑) • CZ • (H • M (c* ⁻¹) ↑) • H ↑ • CZ^ b⁻¹ • S^ -d/c ↑ • M (b* ⁻¹) ≈⟨ cright cright sa (□ ^ 2 • □ ^ 2) (□ • □ ^ 2 • □) auto ⟩
  (Ex • H ^ 3 • M c* ↑) • CZ • H • (M (c* ⁻¹) ↑ • H ↑) • CZ^ b⁻¹ • S^ -d/c ↑ • M (b* ⁻¹) ≈⟨ cright cright cright cleft sym (lemma-cong↑ _ _ (semi-HM c*)) ⟩
  (Ex • H ^ 3 • M c* ↑) • CZ • H • (H ↑ • M c* ↑) • CZ^ b⁻¹ • S^ -d/c ↑ • M (b* ⁻¹) ≈⟨ cright cright cright sa (□ ^ 2 • □ ^ 2) (□ • □ ^ 2 • □) auto ⟩
  (Ex • H ^ 3 • M c* ↑) • CZ • H • H ↑ • (M c* ↑ • CZ^ b⁻¹) • S^ -d/c ↑ • M (b* ⁻¹) ≈⟨ cright cright cright cright cleft lemma-M↑CZ^k c b⁻¹ (λ ()) ⟩
  (Ex • H ^ 3 • M c* ↑) • CZ • H • H ↑ • (CZ^ (b⁻¹ * c) • M c* ↑) • S^ -d/c ↑ • M (b* ⁻¹) ≈⟨ cright sa (□ • □ • □ • □ ^ 2 • □ ^ 2) (□ ^ 4 • □ ^ 3) auto ⟩
  (Ex • H ^ 3 • M c* ↑) • (CZ • H • H ↑ • CZ^ (b⁻¹ * c)) • M c* ↑ • S^ -d/c ↑ • M (b* ⁻¹) ≈⟨ cright cleft cleft rewrite-sym0 100 auto ⟩
  (Ex • H ^ 3 • M c* ↑) • ((H ^ 3 • H ↑ ^ 3 • H • H ↑ • CZ) • H • H ↑ • CZ^ (b⁻¹ * c)) • M c* ↑ • S^ -d/c ↑ • M (b* ⁻¹) ≈⟨ cright sa ((□ ^ 5 • □ ^ 3) • □) (□ ^ 2 • (□ ^ 5 • □) • □) auto ⟩
  (Ex • H ^ 3 • M c* ↑) • (H ^ 3 • H ↑ ^ 3) • ((H • H ↑ • CZ • H • H ↑) • CZ^ (b⁻¹ * c)) • M c* ↑ • S^ -d/c ↑ • M (b* ⁻¹) ≈⟨ cright cright cleft lemma-⌶-CZ^y y* y≠₁ ⟩
  (Ex • H ^ 3 • M c* ↑) • (H ^ 3 • H ↑ ^ 3) • (M (₁-y ⁻¹) ↑ • CZ^ y • ⌶ • M (₁-y ⁻¹)) • M c* ↑ • S^ -d/c ↑ • M (b* ⁻¹) ≈⟨ sa (□ ^ 3 • □ ^ 2 • □ ^ 4 • □ ) (□ ^ 2 • □ ^ 2 • (□ ^ 2 • □ ^ 3) • □) auto ⟩
  (Ex • H ^ 3) • (M c* ↑ • H ^ 3) • ((H ↑ ^ 3 • (M (₁-y ⁻¹) ↑)) • CZ^ y • ⌶ • M (₁-y ⁻¹)) • M c* ↑ • S^ -d/c ↑ • M (b* ⁻¹) ≈⟨ cright cong (sym (lemma-comm-Hᵏ-w↑ 3 (M c*))) (cleft ( cleft lemma-cong↑ _ _ (semi-MH³ ₁-y))) ⟩
  (Ex • H ^ 3) • (H ^ 3 • M c* ↑) • ((M (₁-y) ↑ • H ↑ ^ 3 ) • CZ^ y • ⌶ • M (₁-y ⁻¹)) • M c* ↑ • S^ -d/c ↑ • M (b* ⁻¹) ≈⟨ sa (□ ^ 2 • □ ^ 2 • (□ ^ 2 • □ ^ 3) • □) (□ ^ 3 • □ ^ 2 • □ • □ • □ ^ 3) auto ⟩
  (Ex • H ^ 3 • H ^ 3) • (M c* ↑ • M (₁-y) ↑) • H ↑ ^ 3 • CZ^ y • (H ↓ • H ↑ • CZ • H ↓ • H ↑) • M (₁-y ⁻¹) • M c* ↑ • S^ -d/c ↑ • M (b* ⁻¹) ≈⟨ cong (rewrite-sym0 100 auto) (cright cright cright cong (general-comm auto) (sa (□ ^ 4) (□ ^ 2 • □ ^ 2) auto)) ⟩
  (Ex • H ^ 2) • (M c* ↑ • M (₁-y) ↑) • H ↑ ^ 3 • CZ^ y • (H ↑ • H ↓ • CZ • H ↓ • H ↑) • (M (₁-y ⁻¹) • M c* ↑) • S^ -d/c ↑ • M (b* ⁻¹) ≈⟨ sa (□ ^ 2 • □ ^ 2 • □ • □) (□ • □ ^ 4 • □) auto ⟩
  Ex • (H ^ 2 • (M c* ↑ • M (₁-y) ↑ • H ↑ ^ 3)) • CZ^ y • (H ↑ • H ↓ • CZ • H ↓ • H ↑) • (M (₁-y ⁻¹) • M c* ↑) • S^ -d/c ↑ • M (b* ⁻¹) ≈⟨ cright cong (lemma-comm-Hᵏ-w↑ 2 (M c* • M (₁-y) • H ^ 3)) (cright cright cleft aux-comm-m-w↑ (₁-y ⁻¹) (M c*)) ⟩
  Ex • ((M c* ↑ • M (₁-y) ↑ • H ↑ ^ 3) • H ^ 2) • CZ^ y • (H ↑ • H ↓ • CZ • H ↓ • H ↑) • (M c* ↑ • M (₁-y ⁻¹)) • S^ -d/c ↑ • M (b* ⁻¹) ≈⟨ cright sa (□ ^ 2 • □ ^ 2) (□ • □ ^ 2 • □) auto ⟩
  Ex • (M c* ↑ • M (₁-y) ↑ • H ↑ ^ 3) • (H ^ 2 • CZ^ y) • (H ↑ • H ↓ • CZ • H ↓ • H ↑) • (M c* ↑ • M (₁-y ⁻¹)) • S^ -d/c ↑ • M (b* ⁻¹) ≈⟨ cright cright cleft lemma-semi-HH↓-CZ^k' y ⟩
  Ex • (M c* ↑ • M (₁-y) ↑ • H ↑ ^ 3) • (CZ^ (- y) • H ^ 2) • (H ↑ • H ↓ • CZ • H ↓ • H ↑) • (M c* ↑ • M (₁-y ⁻¹)) • S^ -d/c ↑ • M (b* ⁻¹) ≈⟨ cright cright sa (□ ^ 2 • □ ^ 2) (□ • □ ^ 2 • □) auto ⟩
  Ex • (M c* ↑ • M (₁-y) ↑ • H ↑ ^ 3) • CZ^ (- y) • (H ^ 2 • H ↑ • H ↓ • CZ • H ↓ • H ↑) • (M c* ↑ • M (₁-y ⁻¹)) • S^ -d/c ↑ • M (b* ⁻¹) ≈⟨ cright cright cright cong (general-comm auto) (sa (□ ^ 2 • □ ^ 2) (□ • □ ^ 2 • □) auto) ⟩
  Ex • (M c* ↑ • M (₁-y) ↑ • H ↑ ^ 3) • CZ^ (- y) • (H ↑ • CX • H ↑) • M c* ↑ • (M (₁-y ⁻¹) • S^ -d/c ↑) • M (b* ⁻¹) ≈⟨ cright cong (sym assoc) (cright cright cright cleft aux-comm-m-w↑ (₁-y ⁻¹) (S^ -d/c)) ⟩
  Ex • ((M c* ↑ • M (₁-y) ↑) • H ↑ ^ 3) • CZ^ (- y) • (H ↑ • CX • H ↑) • M c* ↑ • (S^ -d/c ↑ • M (₁-y ⁻¹)) • M (b* ⁻¹) ≈⟨ cright cong (cleft lemma-cong↑ _ _ (aux-comm-MM' c* ₁-y)) (cright cright cright sa (□ ^ 2 • □) (□ ^ 3) auto) ⟩
  Ex • ((M (₁-y) ↑ • M c* ↑) • H ↑ ^ 3) • CZ^ (- y) • (H ↑ • CX • H ↑) • M c* ↑ • S^ -d/c ↑ • M (₁-y ⁻¹) • M (b* ⁻¹) ≈⟨ sa (□ • (□ ^ 2 • □) • □ ) (□ ^ 2 • □ ^ 2 • □) auto ⟩
  (Ex • M (₁-y) ↑) • (M c* ↑ • H ↑ ^ 3) • CZ^ (- y) • (H ↑ • CX • H ↑) • M c* ↑ • S^ -d/c ↑ • M (₁-y ⁻¹) • M (b* ⁻¹) ≈⟨ cong (lemma-Ex-M' ₁-y) (cleft sym (lemma-cong↑ _ _ (semi-MH³ c*))) ⟩
  (M (₁-y) • Ex) • (H ↑ ^ 3 • M (c* ⁻¹) ↑) • CZ^ (- y) • (H ↑ • CX • H ↑) • M c* ↑ • S^ -d/c ↑ • M (₁-y ⁻¹) • M (b* ⁻¹) ≈⟨ sa (□ ^ 2 • □ ^ 2 • □ ^ 2) (□ • □ ^ 2 • □ ^ 2 • □) auto ⟩
  M (₁-y) • (Ex • H ↑ ^ 3) • (M (c* ⁻¹) ↑ • CZ^ (- y)) • (H ↑ • CX • H ↑) • M c* ↑ • S^ -d/c ↑ • M (₁-y ⁻¹) • M (b* ⁻¹) ≈⟨ cright cong (rewrite-swap 100 auto) (cleft lemma-M↑CZ^k c⁻¹ (- y) ((c* ⁻¹) .proj₂)) ⟩
  M (₁-y) • (H ^ 3 • Ex) • (CZ^ (- y * c⁻¹) • M (c* ⁻¹) ↑) • (H ↑ • CX • H ↑) • M c* ↑ • S^ -d/c ↑ • M (₁-y ⁻¹) • M (b* ⁻¹) ≈⟨ cright sa (□ ^ 2 • □ ^ 2 • □ ^ 3 • □) (□ • □ ^ 2 • □ ^ 2 • □ ^ 3) auto ⟩
  M (₁-y) • H ^ 3 • (Ex • CZ^ (- y * c⁻¹)) • (M (c* ⁻¹) ↑ • H ↑) • CX • H ↑ • M c* ↑ • S^ -d/c ↑ • M (₁-y ⁻¹) • M (b* ⁻¹) ≈⟨ cright cright cong (word-comm 1 (toℕ (- y * c⁻¹)) (sym lemma-comm-Ex-CZ)) (cleft sym (lemma-cong↑ _ _ (semi-HM c*))) ⟩
  M (₁-y) • H ^ 3 • (CZ^ (- y * c⁻¹) • Ex) • (H ↑ • M c* ↑) • CX • H ↑ • M c* ↑ • S^ -d/c ↑ • M (₁-y ⁻¹) • M (b* ⁻¹) ≈⟨ cright cright sa (□ ^ 2 • □ ^ 2 • □ ^ 2) (□ • □ ^ 2 • □ ^ 2 • □) auto ⟩
  M (₁-y) • H ^ 3 • CZ^ (- y * c⁻¹) • (Ex • H ↑) • (M c* ↑ • CX) • H ↑ • M c* ↑ • S^ -d/c ↑ • M (₁-y ⁻¹) • M (b* ⁻¹) ≈⟨ cright cright cright cong lemma-Ex-H↑ (cleft aux-M↑CX^k c* ₁) ⟩
  M (₁-y) • H ^ 3 • CZ^ (- y * c⁻¹) • (H • Ex) • (CX^ (₁ * c) • M c* ↑) • H ↑ • M c* ↑ • S^ -d/c ↑ • M (₁-y ⁻¹) • M (b* ⁻¹) ≈⟨ cright cright cright cright  cong (cleft trans (refl' (Eq.cong CX^ (*-identityˡ c))) (aux-CX^-CX'^ c)) (cright cright cright axiom (M-mul (₁-y ⁻¹) (b* ⁻¹))) ⟩
  M (₁-y) • H ^ 3 • CZ^ (- y * c⁻¹) • (H • Ex) • (CX'^ c • M c* ↑) • H ↑ • M c* ↑ • S^ -d/c ↑ • M (₁-y ⁻¹ *' b* ⁻¹) ≈⟨ sa (□ • □ • □ • □ ^ 2 • □ ^ 2 • □ • □) (□ ^ 2 • □ ^ 2 • □ ^ 2 • □ ^ 2 • □) auto ⟩
  (M (₁-y) • H ^ 3) • (CZ^ (- y * c⁻¹) • H) • (Ex • CX'^ c) • (M c* ↑ • H ↑) • M c* ↑ • S^ -d/c ↑ • M (₁-y ⁻¹ *' b* ⁻¹) ≈⟨ cong refl (cong (cleft refl' (Eq.cong CZ^ aux)) (cright cong (sym (lemma-cong↑ _ _ (semi-HM' c*))) (cright cright L01.aux-MM ((₁-y ⁻¹ *' b* ⁻¹) .proj₂) ([b-c]⁻¹ .proj₂) aux2))) ⟩
  (M (₁-y) • H ^ 3) • (CZ^ (- b⁻¹) • H) • (Ex • CX'^ c) • (H ↑ • M (c* ⁻¹) ↑) • M c* ↑ • S^ -d/c ↑ • M [b-c]⁻¹ ≈⟨ sa (□ ^ 2 • □ ^ 2 • □ ^ 2 • □ ^ 2 • □ ^ 3) (□ • □ ^ 2 • □ • □ ^ 2 • □ • □ ^ 2 • □ ^ 2) auto ⟩
  M (₁-y) • (H ^ 3 • CZ^ (- b⁻¹)) • H • (Ex • CX'^ c) • H ↑ • (M (c* ⁻¹) ↑ • M c* ↑) • S^ -d/c ↑ • M [b-c]⁻¹ ≈⟨ cong refl (cong refl (cright cright cright cleft lemma-cong↑ _ _ (aux-M-mulˡ c*))) ⟩

  M (₁-y) • (H ^ 3 • CZ^ (- b⁻¹)) • H • (Ex • CX'^ c) • H ↑ • (ε) • S^ -d/c ↑ • M [b-c]⁻¹ ≈⟨ cright cright cright cright cong refl left-unit ⟩
  M (₁-y) • (H ^ 3 • CZ^ (- b⁻¹)) • H • (Ex • CX'^ c) • H ↑ • S^ -d/c ↑ • M [b-c]⁻¹ ≈⟨ sa (□ • □ ^ 2 • □ • □ ^ 2 • □ ^ 3) (□ • □ • □ ^ 2 • □ ^ 4 • □) auto ⟩
  M (₁-y) • H ^ 3 • (CZ^ (- b⁻¹) • H) • (Ex • CX'^ c • H ↑ • S^ -d/c ↑) • M [b-c]⁻¹ ≈⟨ cright cright cright (cleft cright cright cright refl' (Eq.cong (\ xx -> S^ xx ↑) (Eq.cong (\ xx -> - xx * c⁻¹) (Eq.trans (Eq.sym (+-identityʳ d)) (Eq.sym (Eq.cong (d +_) -0#≈0#)))))) ⟩
  M (₁-y) • H ^ 3 • (CZ^ (- b⁻¹) • H) • (Ex • CX'^ c • H ↑ • S^ -[d+a]/c ↑) • M [b-c]⁻¹ ≈⟨ sa (□ • □ ^ 3 • □ ^ 2 • □) (□ • □ • (□ ^ 2 • □) • □ ^ 2) auto ⟩
  M (₁-y) • H • (H ^ 2 • CZ^ (- b⁻¹)) • H • (Ex • CX'^ c • H ↑ • S^ -[d+a]/c ↑) • M [b-c]⁻¹ ≈⟨ cright cright cleft lemma-semi-HH↓-CZ^k'' b⁻¹ ⟩
  M (₁-y) • H • (CZ^ b⁻¹ • H ^ 2) • H • (Ex • CX'^ c • H ↑ • S^ -[d+a]/c ↑) • M [b-c]⁻¹ ≈⟨ sa (□ • □ • □ ^ 3 • □ • □) (□ ^ 6 • □) auto ⟩
  (M (₁-y) • H • CZ^ b⁻¹ • H ^ 3) • (Ex • CX'^ c • H ↑ • S^ -[d+a]/c ↑) • M [b-c]⁻¹ ≈⟨ cleft cleft L01.aux-MM (₁-y .proj₂) ([b-c]/b .proj₂) aux1a ⟩
  (M [b-c]/b • H • CZ^ b⁻¹ • H ^ 3) • (Ex • CX'^ c • H ↑ • S^ -[d+a]/c ↑) • M [b-c]⁻¹ ≈⟨ cright cong (sym left-unit) (sym (aux-abox-nzb (b + - c) b-c≠0)) ⟩

  dir • [ l' ]ˡ ∎
  where
  b* = (b , λ ())
  c* = (c , λ ())
  b⁻¹ = (b* ⁻¹) .proj₁
  c⁻¹ = ((c , λ ()) ⁻¹) .proj₁
  -d/c = - d * c⁻¹
  cp = CP2.Lemma-two-qupit-completeness (case-| (c* ⁻¹ , HS^ -d/c ) (₀ , b* , HS^ ₀)) CZ-gen
  y* = b* ⁻¹ *' c*
  y = y* .proj₁
  y≠₁ : y ≢ ₁
  y≠₁ eq1 = neq (Eq.trans (Eq.sym (*-identityʳ b)) (Eq.trans (Eq.cong (b *_) (Eq.sym eq1)) (Eq.trans (Eq.sym (*-assoc b b⁻¹ c)) (Eq.trans (Eq.cong (_* c) (lemma-⁻¹ʳ b {{nztoℕ {y = b} {neq0 = λ ()}}})) (*-identityˡ c)))))
  nzm : ₁ + - y ≢ ₀
  nzm = y≠1⇒1-y≠0 y y≠₁
  ₁-y : ℤ* ₚ
  ₁-y = (₁ + - y , nzm)

  d⁻¹ = d
  b⁻¹d = b⁻¹ * d
  nzp : (a , b + - c) ≢ (₀ , ₀)
  nzp eqp = (neq (b-c=0⇒b=c b c (Eq.cong proj₂ eqp)))
  b-c≠0 : b + - c ≢ ₀
  b-c≠0 eq = neq (b-c=0⇒b=c b c eq)
  [b-c]⁻¹ = (b + - c , b-c≠0) ⁻¹
  -[b-c]⁻¹ = - [b-c]⁻¹ .proj₁
  -[d+a]/c = - (d + - a) * c⁻¹
  [b-c]/b = (b + - c , b-c≠0) *' (b* ⁻¹)
  dir = M [b-c]/b • H • CZ^ b⁻¹ • H ^ 3
  l' : L 2
  l' = (₀ , z≤n)     ,   ((c , d + - a) ∷ []) , ((a , b + - c) , nzp)
  aux : - y * c⁻¹ ≡ - b⁻¹
  aux = Eq.trans (Eq.cong (_* c⁻¹) (-‿distribˡ-* b⁻¹ c)) (Eq.trans (*-assoc (- b⁻¹) c c⁻¹) (Eq.trans (Eq.cong (- b⁻¹ *_) (lemma-⁻¹ʳ c {{nztoℕ {y = c} {neq0 = λ ()}}})) (*-identityʳ (- b⁻¹))))

  aux1a : (₁-y) .proj₁ ≡ (b + - c) * b⁻¹
  aux1a = Eq.sym (Eq.trans (*-distribʳ-+ b⁻¹ b (- c)) (Eq.trans (Eq.cong (_+ - c * b⁻¹) (lemma-⁻¹ʳ b {{nztoℕ {y = b} {neq0 = λ ()}}})) (Eq.trans (Eq.cong (₁ +_) (Eq.trans (Eq.sym (-‿distribˡ-* c b⁻¹)) (Eq.cong -_ (*-comm c b⁻¹)))) auto)))
  
  aux1 : (₁-y ⁻¹) .proj₁ ≡ ([b-c]⁻¹ .proj₁) * b
  aux1 = Eq.trans (inv-cong ₁-y ((b + - c , b-c≠0) *' b* ⁻¹) aux1a) (Eq.trans (inv-distrib ((b + - c , b-c≠0)) (b* ⁻¹)) (Eq.trans (Eq.cong (([b-c]⁻¹ .proj₁) *_) (inv-involutive b*)) auto))
  aux2 : (₁-y ⁻¹ *' b* ⁻¹) .proj₁ ≡ [b-c]⁻¹ .proj₁
  aux2 = Eq.trans (Eq.cong (_* b⁻¹) aux1) (Eq.trans (*-assoc ([b-c]⁻¹ .proj₁) b b⁻¹) (Eq.trans (Eq.cong (([b-c]⁻¹ .proj₁) *_) (lemma-⁻¹ʳ b {{nztoℕ {y = b} {neq0 = λ ()}}})) (*-identityʳ ([b-c]⁻¹ .proj₁))))
  aux3 : (- b⁻¹ * (₁-y ⁻¹) .proj₁) ≡ -[b-c]⁻¹
  aux3 = Eq.trans (Eq.sym (-‿distribˡ-* b⁻¹ ((₁-y ⁻¹) .proj₁))) (Eq.trans (Eq.cong -_ ((*-comm b⁻¹ ((₁-y ⁻¹) .proj₁)))) (Eq.cong -_ aux2))


lemma-dir-and-l' l@((₁ , s≤s z≤n) , [] , x@((a@₀ , b@(₁₊ _)) , nzx)) = begin
  [ l ]ˡ • CZ ≈⟨ cleft left-unit ⟩
  [ x ]ᵃ ↑ • CZ ≈⟨ lemma-A-CZ-1 (b , (λ ())) ⟩
  CZ^ b⁻¹ • [ x ]ᵃ ↑ ≈⟨ cright sym left-unit ⟩
  dir • [ l' ]ˡ ∎
  where
  b⁻¹ = ((b , λ ()) ⁻¹) .proj₁
  l' = l'-of l
  dir = dir-of l
lemma-dir-and-l' l@((₁ , s≤s z≤n) , [] , x@((a@(₁₊ _) , b) , nzx)) = begin
  [ l ]ˡ • CZ ≈⟨ cleft left-unit ⟩
  [ x ]ᵃ ↑ • CZ ≈⟨ lemma-A-CZ-2 (a , λ ()) b ⟩ 
  dir • [ a , b ]ᵇ • [ (₀ , - a) , nzx' ]ᵃ ≈⟨ cright sym (trans assoc left-unit)  ⟩
  dir • [ l' ]ˡ ∎
  where
  a* : ℤ* ₚ
  a* = (a , λ ())
  a⁻¹ = (a* ⁻¹) .proj₁
  -b/a = - b * a⁻¹
  nz : (a , b) ≢ (₀ , ₀)
  nz = aux-a≠0⇒ab≠0 a b λ ()
  nz' : (₀ , - a) ≢ (₀ , ₀)
  nz' = aux-b≠0⇒ab≠0 ₀ (- a) ((-' a*) .proj₂)
  
  dir : Word (Gen 2)
  dir = (H • CZ^ a⁻¹ • H ^ 3)
  nzx' = aux-b≠0⇒ab≠0 ₀ (- a) ((-' (a , λ ())) .proj₂)
  l' : L 2
  l' = ((₀ , z≤n) , ((a , b) ∷ []) , ((₀ , - a) , nzx'))

