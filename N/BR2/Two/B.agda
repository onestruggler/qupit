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



module N.BR2.Two.B (p-2 : ℕ) (p-prime : Prime (2+ p-2)) where

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
open import N.BR2.TwoQupit p-2 p-prime hiding (n)
open import N.BR2.Two.Lemmas p-2 p-prime hiding (n ; module L01)
open import N.BR2.Two.D p-2 p-prime hiding (n ; module L01)
open import N.Embeding-1n p-2 p-prime


open PB ((₂₊ n) QRel,_===_)
open PP ((₂₊ n) QRel,_===_)
open SR word-setoid
open Pattern-Assoc renaming (special-assoc to sa)
open Lemmas0 n
module L01 = Lemmas0 (₁₊ n)
open Lemmas-2Q n
open Sym0-Rewriting (₁₊ n)
open Rewriting-Swap 1

lemma-B~dualD : ∀ (x : B) -> [ x ]ᵇ ≈ H ↑ • dual [ x ]ᵈ • H ^ 3
lemma-B~dualD x@(₀ , ₀) = begin
  [ x ]ᵇ ≈⟨ rewrite-swap 100 auto ⟩
  H ↑ • Ex • H ^ 3 ≈⟨ cright cleft sym aux-dual-Ex ⟩
  H ↑ • dual [ x ]ᵈ • H ^ 3 ∎
lemma-B~dualD x@(a@₀ , b@(₁₊ _)) = begin
  Ex • CX • [ (a , b) , (λ ()) ]ᵃ ↑ ≈⟨ sa (□ • (□ ^ 3 • □ • □) • □) (□ ^ 2 • (□ ^ 2 • □) • □ • □) auto ⟩
  (Ex • H) • (H ^ 2 • CZ) • H • [ (a , b) , (λ ()) ]ᵃ ↑ ≈⟨ cright cleft lemma-semi-HH↓-CZ^-₁ ⟩
  (Ex • H) • (CZ^ (- ₁) • H ^ 2) • H • [ (a , b) , (λ ()) ]ᵃ ↑ ≈⟨ cright sa (□ ^ 3 • □ ^ 2) (□ • □ ^ 3 • □) auto ⟩
  (Ex • H) • CZ^ (- ₁) • H ^ 3 • [ (a , b) , (λ ()) ]ᵃ ↑ ≈⟨ cong (rewrite-swap 100 auto) (cright lemma-comm-Hᵏ-w↑ 3 [ (a , b) , (λ ()) ]ᵃ) ⟩
  (H ↑ • Ex) • CZ^ (- ₁) • [ (a , b) , (λ ()) ]ᵃ ↑ • H ^ 3 ≈⟨ sa (□ ^ 2 • □ • □ ^ 2) (□ • □ ^ 3 • □) auto ⟩
  H ↑ • (Ex • CZ^ (- ₁) • [ (a , b) , (λ ()) ]ᵃ ↑) • H ^ 3 ≈⟨ sym (cright cleft cong ( aux-dual-Ex) (cong (refl' (aux-dual-CZ^k (toℕ (- ₁)))) (refl' (aux-dual-MC ((b , λ ()) ⁻¹ , ε))))) ⟩
  H ↑ • dual (Ex • CZ^ (- ₁) • [ (a , b) , (λ ()) ]ᵃ) • H ^ 3 ∎
lemma-B~dualD x@(a@(₁₊ _) , b) = begin
  Ex • CX • [ (a , b) , (λ ()) ]ᵃ ↑ ≈⟨ sa (□ • (□ ^ 3 • □ • □) • □) (□ ^ 2 • (□ ^ 2 • □) • □ • □) auto ⟩
  (Ex • H) • (H ^ 2 • CZ) • H • [ (a , b) , (λ ()) ]ᵃ ↑ ≈⟨ cright cleft lemma-semi-HH↓-CZ^-₁ ⟩
  (Ex • H) • (CZ^ (- ₁) • H ^ 2) • H • [ (a , b) , (λ ()) ]ᵃ ↑ ≈⟨ cright sa (□ ^ 3 • □ ^ 2) (□ • □ ^ 3 • □) auto ⟩
  (Ex • H) • CZ^ (- ₁) • H ^ 3 • [ (a , b) , (λ ()) ]ᵃ ↑ ≈⟨ cong (rewrite-swap 100 auto) (cright lemma-comm-Hᵏ-w↑ 3 [ (a , b) , (λ ()) ]ᵃ) ⟩
  (H ↑ • Ex) • CZ^ (- ₁) • [ (a , b) , (λ ()) ]ᵃ ↑ • H ^ 3 ≈⟨ sa (□ ^ 2 • □ • □ ^ 2) (□ • □ ^ 3 • □) auto ⟩
  H ↑ • (Ex • CZ^ (- ₁) • [ (a , b) , (λ ()) ]ᵃ ↑) • H ^ 3 ≈⟨ sym (cright cleft cong ( aux-dual-Ex) (cong (refl' (aux-dual-CZ^k (toℕ (- ₁)))) (refl' (aux-dual-MC ((a , λ ()) ⁻¹ , HS^ -b/a))))) ⟩
  H ↑ • dual (Ex • CZ^ (- ₁) • [ (a , b) , (λ ()) ]ᵃ) • H ^ 3 ∎
  where
  a⁻¹ = ((a , λ ()) ⁻¹) .proj₁
  -b/a = - b * a⁻¹

dir-and-b' : ∀ (d : B) (g : Gen 2) (neqH : g ≢ H-gen) (neqCZ : g ≢ CZ-gen) -> Word (Gen 2) × B

dir-and-b' d@(a , b)                   H-gen neqH neqCZ  =  ⊥-elim (neqH  auto)
dir-and-b' d@(a , b)                  CZ-gen neqH neqCZ  =  ⊥-elim (neqCZ auto)
dir-and-b' d@(a , b)               (H-gen ↥) neqH neqCZ  =  dual dir               ,   d'
  where
  edd = dir-and-d' d H-gen λ ()
  dir = (S^ (edd .proj₁) • (edd .proj₂ .proj₁) ↑)
  d' = edd .proj₂ .proj₂
dir-and-b' d@(a , b)               (S-gen ↥) neqH neqCZ  =  dual dir               ,   d'
  where
  edd = dir-and-d' d S-gen λ ()
  dir = (S^ (edd .proj₁) • (edd .proj₂ .proj₁) ↑)
  d' = edd .proj₂ .proj₂
dir-and-b' d@(a@₀ , b@₀)               S-gen neqH neqCZ  =  S ↑                    ,   (₀ , ₀)
dir-and-b' d@(a@₀ , b@(₁₊ _))          S-gen neqH neqCZ  =  S ↑ • S • CZ^ (- ₁)    ,   (a , b)
dir-and-b' d@(a@(₁₊ _) , b)            S-gen neqH neqCZ  =  S ↑ • S • CZ^ (- ₁)    ,   (a , b)

  

lemma-B-br : ∀ (d : B) (g : Gen 2) (neqH : g ≢ H-gen) (neqCZ : g ≢ CZ-gen) -> let (dir , d') = dir-and-b' d g neqH neqCZ in

  [ d ]ᵇ • [ g ]ʷ ≈ dir • [ d' ]ᵇ

lemma-B-br d@(a , b)                   H-gen neqH neqCZ  =  ⊥-elim (neqH  auto)
lemma-B-br d@(a , b)                  CZ-gen neqH neqCZ  =  ⊥-elim (neqCZ auto)

lemma-B-br d@(a@₀ , b@₀) g@(S-gen) neqH neqCZ = begin
  [ d ]ᵇ • S ≈⟨ lemma-Ex-S ⟩
  dir • [ d' ]ᵇ ∎
  where
  eb = dir-and-b' d S-gen (λ ()) λ ()
  dir = eb .proj₁
  d' = eb .proj₂

lemma-B-br d@(a@₀ , b@(₁₊ _)) g@(S-gen) neqH neqCZ = begin
  (Ex • CX • [ (a , b) , (λ ()) ]ᵃ ↑) • S ≈⟨ sa (□ ^ 3 • □) (□ ^ 4) auto ⟩
  Ex • CX • ⟦ (b , λ ()) ⁻¹ , ε ⟧ₘ₊ ↑ • S ≈⟨ cright cright sym (lemma-comm-S-w↑ ⟦ (b , λ ()) ⁻¹ , ε ⟧ₘ₊) ⟩
  Ex • CX • S • ⟦ (b , λ ()) ⁻¹ , ε ⟧ₘ₊ ↑ ≈⟨ sa (□ ^ 4) (□ • □ ^ 2 • □) auto ⟩
  Ex • (CX • S) • ⟦ (b , λ ()) ⁻¹ , ε ⟧ₘ₊ ↑ ≈⟨ cright cleft sym (lemma-CXS^k ₁) ⟩
  Ex • (S • S ↑ • CZ^ (- ₁) • CX) • ⟦ (b , λ ()) ⁻¹ , ε ⟧ₘ₊ ↑ ≈⟨ sa (□ • □ ^ 4 • □) (□ ^ 3 • □ ^ 3) auto ⟩
  (Ex • S • S ↑) • CZ^ (- ₁) • CX • ⟦ (b , λ ()) ⁻¹ , ε ⟧ₘ₊ ↑ ≈⟨ cleft rewrite-swap 100 auto ⟩
  (S ↑ • S • Ex) • CZ^ (- ₁) • CX • ⟦ (b , λ ()) ⁻¹ , ε ⟧ₘ₊ ↑ ≈⟨ sa (□ ^ 3 • □ ^ 3) (□ ^ 2 • □ ^ 2 • □ ^ 2) auto ⟩
  (S ↑ • S) • (Ex • CZ^ (- ₁)) • CX • ⟦ (b , λ ()) ⁻¹ , ε ⟧ₘ₊ ↑ ≈⟨ cright cleft word-comm 1 (toℕ (- ₁)) (sym lemma-comm-Ex-CZ) ⟩
  (S ↑ • S) • (CZ^ (- ₁) • Ex) • CX • ⟦ (b , λ ()) ⁻¹ , ε ⟧ₘ₊ ↑ ≈⟨ sa (□ ^ 2 • □ ^ 2 • □ ^ 2) (□ ^ 3 • □  ^ 3) auto ⟩
  dir • [ d' ]ᵇ ∎
  where
  eb = dir-and-b' d S-gen (λ ()) λ ()
  dir = eb .proj₁
  d' = eb .proj₂

lemma-B-br d@(a@(₁₊ _) , b) g@(S-gen) neqH neqCZ = begin
  (Ex • CX • [ (a , b) , (λ ()) ]ᵃ ↑) • S ≈⟨ sa (□ ^ 3 • □) (□ ^ 4) auto ⟩
  Ex • CX • ⟦ (a , λ ()) ⁻¹ , HS^ -b/a ⟧ₘ₊ ↑ • S ≈⟨ cright cright sym (lemma-comm-S-w↑ ⟦ (a , λ ()) ⁻¹ , HS^ -b/a ⟧ₘ₊) ⟩
  Ex • CX • S • ⟦ (a , λ ()) ⁻¹ , HS^ -b/a ⟧ₘ₊ ↑ ≈⟨ sa (□ ^ 4) (□ • □ ^ 2 • □) auto ⟩
  Ex • (CX • S) • ⟦ (a , λ ()) ⁻¹ , HS^ -b/a ⟧ₘ₊ ↑ ≈⟨ cright cleft sym (lemma-CXS^k ₁) ⟩
  Ex • (S • S ↑ • CZ^ (- ₁) • CX) • ⟦ (a , λ ()) ⁻¹ , HS^ -b/a ⟧ₘ₊ ↑ ≈⟨ sa (□ • □ ^ 4 • □) (□ ^ 3 • □ ^ 3) auto ⟩
  (Ex • S • S ↑) • CZ^ (- ₁) • CX • ⟦ (a , λ ()) ⁻¹ , HS^ -b/a ⟧ₘ₊ ↑ ≈⟨ cleft rewrite-swap 100 auto ⟩
  (S ↑ • S • Ex) • CZ^ (- ₁) • CX • ⟦ (a , λ ()) ⁻¹ , HS^ -b/a ⟧ₘ₊ ↑ ≈⟨ sa (□ ^ 3 • □ ^ 3) (□ ^ 2 • □ ^ 2 • □ ^ 2) auto ⟩
  (S ↑ • S) • (Ex • CZ^ (- ₁)) • CX • ⟦ (a , λ ()) ⁻¹ , HS^ -b/a ⟧ₘ₊ ↑ ≈⟨ cright cleft word-comm 1 (toℕ (- ₁)) (sym lemma-comm-Ex-CZ) ⟩
  (S ↑ • S) • (CZ^ (- ₁) • Ex) • CX • ⟦ (a , λ ()) ⁻¹ , HS^ -b/a ⟧ₘ₊ ↑ ≈⟨ sa (□ ^ 2 • □ ^ 2 • □ ^ 2) (□ ^ 3 • □  ^ 3) auto ⟩
  dir • [ d' ]ᵇ ∎
  where
  eb = dir-and-b' d S-gen (λ ()) λ ()
  dir = eb .proj₁
  d' = eb .proj₂
  a⁻¹ = ((a , λ ()) ⁻¹) .proj₁
  -b/a = - b * a⁻¹


lemma-B-br d@(a@₀ , b@₀) g@(H-gen ↥) neqH neqCZ = begin
  [ d ]ᵇ • H ↑ ≈⟨ cleft lemma-B~dualD d ⟩
  (H ↑ • dual [ d ]ᵈ • H ^ 3) • H ↑ ≈⟨ refl ⟩
  dual (H • [ d ]ᵈ • H ↑  ^ 3) • dual H ≈⟨ sa (□ ^ 3 • □) (□ ^ 4) auto ⟩
  dual (H • [ d ]ᵈ • H ↑  ^ 3 • H) ≈⟨ by-duality {w = H • [ d ]ᵈ • H ↑  ^ 3 • H } {u = H • [ d ]ᵈ • H • H ↑  ^ 3} (cright cright sym (lemma-comm-H-w↑ (H ^ 3))) ⟩
  dual (H • [ d ]ᵈ • H • H ↑ ^ 3) ≈⟨ by-duality  {w = H • [ d ]ᵈ • H • H ↑  ^ 3 } {u = H • ([ d ]ᵈ • H) • H ↑ ^ 3}(sa (□ ^ 4) (□ • □ ^ 2 • □) auto) ⟩
  dual (H • ([ d ]ᵈ • H) • H ↑ ^ 3) ≈⟨ by-duality {w = (H • ([ d ]ᵈ • H) • H ↑ ^ 3)} {u = (H • (dirs • diro • [ d' ]ᵈ) • H ↑ ^ 3)} (cright cleft lemma-D-br d H-gen (λ ())) ⟩
  dual (H • (dirs • diro • [ d' ]ᵈ) • H ↑ ^ 3) ≈⟨ refl ⟩
  H ↑ • (dual dirs • dual diro • dual [ d' ]ᵈ) • H ^ 3 ≈⟨ cright cleft left-unit ⟩
  H ↑ • (dual diro • dual [ d' ]ᵈ) • H ^ 3 ≈⟨ cright cleft refl ⟩
  H ↑ • (H • dual [ d' ]ᵈ) • H ^ 3 ≈⟨ sa (□ • □ ^ 2 • □) (□ ^ 2 • □ ^ 2) auto ⟩
  (H ↑ • H) • dual [ d' ]ᵈ • H ^ 3 ≈⟨ cleft axiom comm-H ⟩
  (H • H ↑) • dual [ d' ]ᵈ • H ^ 3 ≈⟨ assoc ⟩
  H • H ↑ • dual [ d' ]ᵈ • H ^ 3 ≈⟨ cright sym (lemma-B~dualD d') ⟩
  H • [ d' ]ᵇ ≈⟨ sym (trans assoc left-unit) ⟩
  dual dir • [ d' ]ᵇ ∎
  where
  edd = dir-and-d' d H-gen λ ()
  dir = (S^ (edd .proj₁) • (edd .proj₂ .proj₁) ↑)
  dirs = S^ (edd .proj₁)
  diro = (edd .proj₂ .proj₁) ↑
  d' = edd .proj₂ .proj₂


lemma-B-br d@(a@₀ , b@(₁₊ _)) g@(H-gen ↥) neqH neqCZ = begin
  [ d ]ᵇ • H ↑ ≈⟨ cleft lemma-B~dualD d ⟩
  (H ↑ • dual [ d ]ᵈ • H ^ 3) • H ↑ ≈⟨ refl ⟩
  dual (H • [ d ]ᵈ • H ↑  ^ 3) • dual H ≈⟨ sa (□ ^ 3 • □) (□ ^ 4) auto ⟩
  dual (H • [ d ]ᵈ • H ↑  ^ 3 • H) ≈⟨ by-duality {w = H • [ d ]ᵈ • H ↑  ^ 3 • H } {u = H • [ d ]ᵈ • H • H ↑  ^ 3} (cright cright sym (lemma-comm-H-w↑ (H ^ 3))) ⟩
  dual (H • [ d ]ᵈ • H • H ↑ ^ 3) ≈⟨ by-duality  {w = H • [ d ]ᵈ • H • H ↑  ^ 3 } {u = H • ([ d ]ᵈ • H) • H ↑ ^ 3}(sa (□ ^ 4) (□ • □ ^ 2 • □) auto) ⟩
  dual (H • ([ d ]ᵈ • H) • H ↑ ^ 3) ≈⟨ by-duality {w = (H • ([ d ]ᵈ • H) • H ↑ ^ 3)} {u = (H • (dirs • diro • [ d' ]ᵈ) • H ↑ ^ 3)} (cright cleft lemma-D-br d H-gen (λ ())) ⟩
  dual (H • (dirs • diro • [ d' ]ᵈ) • H ↑ ^ 3) ≈⟨ refl ⟩
  H ↑ • (dual dirs • dual diro • dual [ d' ]ᵈ) • H ^ 3 ≈⟨ cright cleft left-unit ⟩
  H ↑ • (dual diro • dual [ d' ]ᵈ) • H ^ 3 ≈⟨ cright cleft refl ⟩
  H ↑ • (ε • dual [ d' ]ᵈ) • H ^ 3 ≈⟨ cright cleft left-unit ⟩
  H ↑ • (dual [ d' ]ᵈ) • H ^ 3 ≈⟨ sym (lemma-B~dualD d') ⟩
  [ d' ]ᵇ ≈⟨ sym left-unit ⟩
  ε • [ d' ]ᵇ ≈⟨ cleft sym left-unit ⟩
  dual dir • [ d' ]ᵇ ∎
  where
  edd = dir-and-d' d H-gen λ ()
  dir = (S^ (edd .proj₁) • (edd .proj₂ .proj₁) ↑)
  dirs = S^ (edd .proj₁)
  diro = (edd .proj₂ .proj₁) ↑
  d' = edd .proj₂ .proj₂


lemma-B-br d@(a@(₁₊ _) , b@₀) g@(H-gen ↥) neqH neqCZ = begin
  [ d ]ᵇ • H ↑ ≈⟨ cleft lemma-B~dualD d ⟩
  (H ↑ • dual [ d ]ᵈ • H ^ 3) • H ↑ ≈⟨ refl ⟩
  dual (H • [ d ]ᵈ • H ↑  ^ 3) • dual H ≈⟨ sa (□ ^ 3 • □) (□ ^ 4) auto ⟩
  dual (H • [ d ]ᵈ • H ↑  ^ 3 • H) ≈⟨ by-duality {w = H • [ d ]ᵈ • H ↑  ^ 3 • H } {u = H • [ d ]ᵈ • H • H ↑  ^ 3} (cright cright sym (lemma-comm-H-w↑ (H ^ 3))) ⟩
  dual (H • [ d ]ᵈ • H • H ↑ ^ 3) ≈⟨ by-duality  {w = H • [ d ]ᵈ • H • H ↑  ^ 3 } {u = H • ([ d ]ᵈ • H) • H ↑ ^ 3}(sa (□ ^ 4) (□ • □ ^ 2 • □) auto) ⟩
  dual (H • ([ d ]ᵈ • H) • H ↑ ^ 3) ≈⟨ by-duality {w = (H • ([ d ]ᵈ • H) • H ↑ ^ 3)} {u = (H • (dirs • diro • [ d' ]ᵈ) • H ↑ ^ 3)} (cright cleft lemma-D-br d H-gen (λ ())) ⟩
  dual (H • (dirs • diro • [ d' ]ᵈ) • H ↑ ^ 3) ≈⟨ refl ⟩
  H ↑ • (dual dirs • dual diro • dual [ d' ]ᵈ) • H ^ 3 ≈⟨ cright cleft left-unit ⟩
  H ↑ • (dual diro • dual [ d' ]ᵈ) • H ^ 3 ≈⟨ cright cleft refl ⟩
  H ↑ • (ε • dual [ d' ]ᵈ) • H ^ 3 ≈⟨ cright cleft left-unit ⟩
  H ↑ • (dual [ d' ]ᵈ) • H ^ 3 ≈⟨ sym (lemma-B~dualD d') ⟩
  [ d' ]ᵇ ≈⟨ sym left-unit ⟩
  ε • [ d' ]ᵇ ≈⟨ cleft sym left-unit ⟩
  dual dir • [ d' ]ᵇ ∎
  where
  edd = dir-and-d' d H-gen λ ()
  dir = (S^ (edd .proj₁) • (edd .proj₂ .proj₁) ↑)
  dirs = S^ (edd .proj₁)
  diro = (edd .proj₂ .proj₁) ↑
  d' = edd .proj₂ .proj₂




lemma-B-br d@(a@(₁₊ _) , b@(₁₊ _)) g@(H-gen ↥) neqH neqCZ = begin
  [ d ]ᵇ • H ↑ ≈⟨ cleft lemma-B~dualD d ⟩
  (H ↑ • dual [ d ]ᵈ • H ^ 3) • H ↑ ≈⟨ refl ⟩
  dual (H • [ d ]ᵈ • H ↑  ^ 3) • dual H ≈⟨ sa (□ ^ 3 • □) (□ ^ 4) auto ⟩
  dual (H • [ d ]ᵈ • H ↑  ^ 3 • H) ≈⟨ by-duality {w = H • [ d ]ᵈ • H ↑  ^ 3 • H } {u = H • [ d ]ᵈ • H • H ↑  ^ 3} (cright cright sym (lemma-comm-H-w↑ (H ^ 3))) ⟩
  dual (H • [ d ]ᵈ • H • H ↑ ^ 3) ≈⟨ by-duality  {w = H • [ d ]ᵈ • H • H ↑  ^ 3 } {u = H • ([ d ]ᵈ • H) • H ↑ ^ 3}(sa (□ ^ 4) (□ • □ ^ 2 • □) auto) ⟩
  dual (H • ([ d ]ᵈ • H) • H ↑ ^ 3) ≈⟨ by-duality {w = (H • ([ d ]ᵈ • H) • H ↑ ^ 3)} {u = (H • (dirs • diro • [ d' ]ᵈ) • H ↑ ^ 3)} (cright cleft lemma-D-br d H-gen (λ ())) ⟩
  dual (H • (dirs • diro • [ d' ]ᵈ) • H ↑ ^ 3) ≈⟨ refl ⟩
  H ↑ • (dual dirs • dual diro • dual [ d' ]ᵈ) • H ^ 3 ≈⟨ cright cleft left-unit ⟩
  H ↑ • (dual diro • dual [ d' ]ᵈ) • H ^ 3 ≈⟨ cright cleft refl ⟩
  H ↑ • (dual (S^ [ab]⁻¹ ↑) • dual [ d' ]ᵈ) • H ^ 3 ≈⟨ cright cleft (cleft refl' (aux-dual-S^k↑ (toℕ [ab]⁻¹))) ⟩
  H ↑ • (S^ [ab]⁻¹ • dual [ d' ]ᵈ) • H ^ 3 ≈⟨ sa (□ • □ ^ 2 • □) (□ ^ 2 • □ ^ 2) auto ⟩
  (H ↑ • S^ [ab]⁻¹) • dual [ d' ]ᵈ • H ^ 3 ≈⟨ cleft sym (lemma-comm-Sᵏ-w↑ (toℕ [ab]⁻¹) H) ⟩
  (S^ [ab]⁻¹ • H ↑) • dual [ d' ]ᵈ • H ^ 3 ≈⟨ assoc ⟩
  S^ [ab]⁻¹ • H ↑ • dual [ d' ]ᵈ • H ^ 3 ≈⟨ cright sym (lemma-B~dualD d') ⟩
  S^ [ab]⁻¹ • [ d' ]ᵇ ≈⟨ cleft sym (refl' (aux-dual-S^k↑ (toℕ [ab]⁻¹))) ⟩  
  dual (S^ [ab]⁻¹ ↑) • [ d' ]ᵇ ≈⟨ cleft sym left-unit ⟩  
  dual dir • [ d' ]ᵇ ∎
  where
  edd = dir-and-d' d H-gen λ ()
  dir = (S^ (edd .proj₁) • (edd .proj₂ .proj₁) ↑)
  dirs = S^ (edd .proj₁)
  diro = (edd .proj₂ .proj₁) ↑
  d' = edd .proj₂ .proj₂
  [ab]⁻¹ = (((a , λ ()) *' (b , λ ())) ⁻¹) .proj₁


lemma-B-br d@(a@₀ , b@(₁₊ _)) g@(S-gen ↥) neqH neqCZ = begin
  [ d ]ᵇ • S ↑ ≈⟨ cleft lemma-B~dualD d ⟩
  (H ↑ • dual [ d ]ᵈ • H ^ 3) • S ↑ ≈⟨ refl ⟩
  dual (H • [ d ]ᵈ • H ↑  ^ 3) • dual S ≈⟨ sa (□ ^ 3 • □) (□ ^ 4) auto ⟩
  dual (H • [ d ]ᵈ • H ↑  ^ 3 • S) ≈⟨ by-duality {w = H • [ d ]ᵈ • H ↑  ^ 3 • S} {u = H • [ d ]ᵈ • S • H ↑  ^ 3} (cright cright sym (lemma-comm-S-w↑ (H ^ 3))) ⟩
  dual (H • [ d ]ᵈ • S • H ↑ ^ 3) ≈⟨ by-duality  {w = H • [ d ]ᵈ • S • H ↑  ^ 3 } {u = H • ([ d ]ᵈ • S) • H ↑ ^ 3}(sa (□ ^ 4) (□ • □ ^ 2 • □) auto) ⟩
  dual (H • ([ d ]ᵈ • S) • H ↑ ^ 3) ≈⟨ by-duality {w = (H • ([ d ]ᵈ • S) • H ↑ ^ 3)} {u = (H • (dirs • diro • [ d' ]ᵈ) • H ↑ ^ 3)} (cright cleft lemma-D-br d S-gen (λ ())) ⟩
  dual (H • (dirs • diro • [ d' ]ᵈ) • H ↑ ^ 3) ≈⟨ refl ⟩
  H ↑ • (dual dirs • dual diro • dual [ d' ]ᵈ) • H ^ 3 ≈⟨ cright cleft left-unit ⟩
  H ↑ • (dual diro • dual [ d' ]ᵈ) • H ^ 3 ≈⟨ cright cleft refl ⟩
  H ↑ • (dual (S^ b⁻² ↑) • dual [ d' ]ᵈ) • H ^ 3 ≈⟨ cright cleft (cleft refl' (aux-dual-S^k↑ (toℕ b⁻²))) ⟩
  H ↑ • (S^ b⁻² • dual [ d' ]ᵈ) • H ^ 3 ≈⟨ sa (□ • □ ^ 2 • □) (□ ^ 2 • □ ^ 2) auto ⟩
  (H ↑ • S^ b⁻²) • dual [ d' ]ᵈ • H ^ 3 ≈⟨ cleft sym (lemma-comm-Sᵏ-w↑ (toℕ b⁻²) H) ⟩
  (S^ b⁻² • H ↑) • dual [ d' ]ᵈ • H ^ 3 ≈⟨ assoc ⟩
  S^ b⁻² • H ↑ • dual [ d' ]ᵈ • H ^ 3 ≈⟨ cright sym (lemma-B~dualD d') ⟩
  S^ b⁻² • [ d' ]ᵇ ≈⟨ cleft sym (refl' (aux-dual-S^k↑ (toℕ b⁻²))) ⟩  
  dual (S^ b⁻² ↑) • [ d' ]ᵇ ≈⟨ cleft sym left-unit ⟩  
  dual dir • [ d' ]ᵇ ∎
  where
  edd = dir-and-d' d S-gen λ ()
  dir = (S^ (edd .proj₁) • (edd .proj₂ .proj₁) ↑)
  dirs = S^ (edd .proj₁)
  diro = (edd .proj₂ .proj₁) ↑
  d' = edd .proj₂ .proj₂
  b* = (b , λ ())
  b⁻² = ((b* ⁻¹) .proj₁) * ((b* ⁻¹) .proj₁)


lemma-B-br d@(a@₀ , b@₀) g@(S-gen ↥) neqH neqCZ = begin
  [ d ]ᵇ • S ↑ ≈⟨ cleft lemma-B~dualD d ⟩
  (H ↑ • dual [ d ]ᵈ • H ^ 3) • S ↑ ≈⟨ refl ⟩
  dual (H • [ d ]ᵈ • H ↑  ^ 3) • dual S ≈⟨ sa (□ ^ 3 • □) (□ ^ 4) auto ⟩
  dual (H • [ d ]ᵈ • H ↑  ^ 3 • S) ≈⟨ by-duality {w = H • [ d ]ᵈ • H ↑  ^ 3 • S } {u = H • [ d ]ᵈ • S • H ↑  ^ 3} (cright cright sym (lemma-comm-S-w↑ (H ^ 3))) ⟩
  dual (H • [ d ]ᵈ • S • H ↑ ^ 3) ≈⟨ by-duality  {w = H • [ d ]ᵈ • S • H ↑  ^ 3 } {u = H • ([ d ]ᵈ • S) • H ↑ ^ 3}(sa (□ ^ 4) (□ • □ ^ 2 • □) auto) ⟩
  dual (H • ([ d ]ᵈ • S) • H ↑ ^ 3) ≈⟨ by-duality {w = (H • ([ d ]ᵈ • S) • H ↑ ^ 3)} {u = (H • (dirs • diro • [ d' ]ᵈ) • H ↑ ^ 3)} (cright cleft lemma-D-br d S-gen (λ ())) ⟩
  dual (H • (dirs • diro • [ d' ]ᵈ) • H ↑ ^ 3) ≈⟨ refl ⟩
  H ↑ • (dual dirs • dual diro • dual [ d' ]ᵈ) • H ^ 3 ≈⟨ cright cleft left-unit ⟩
  H ↑ • (dual diro • dual [ d' ]ᵈ) • H ^ 3 ≈⟨ cright cleft refl ⟩
  H ↑ • (S • dual [ d' ]ᵈ) • H ^ 3 ≈⟨ sa (□ • □ ^ 2 • □) (□ ^ 2 • □ ^ 2) auto ⟩
  (H ↑ • S) • dual [ d' ]ᵈ • H ^ 3 ≈⟨ cleft axiom comm-S ⟩
  (S • H ↑) • dual [ d' ]ᵈ • H ^ 3 ≈⟨ assoc ⟩
  S • H ↑ • dual [ d' ]ᵈ • H ^ 3 ≈⟨ cright sym (lemma-B~dualD d') ⟩
  S • [ d' ]ᵇ ≈⟨ sym (trans assoc left-unit) ⟩
  dual dir • [ d' ]ᵇ ∎
  where
  edd = dir-and-d' d S-gen λ ()
  dir = (S^ (edd .proj₁) • (edd .proj₂ .proj₁) ↑)
  dirs = S^ (edd .proj₁)
  diro = (edd .proj₂ .proj₁) ↑
  d' = edd .proj₂ .proj₂


lemma-B-br d@(a@(₁₊ _) , b@₀) g@(S-gen ↥) neqH neqCZ = begin
  [ d ]ᵇ • S ↑ ≈⟨ cleft lemma-B~dualD d ⟩
  (H ↑ • dual [ d ]ᵈ • H ^ 3) • S ↑ ≈⟨ refl ⟩
  dual (H • [ d ]ᵈ • H ↑  ^ 3) • dual S ≈⟨ sa (□ ^ 3 • □) (□ ^ 4) auto ⟩
  dual (H • [ d ]ᵈ • H ↑  ^ 3 • S) ≈⟨ by-duality {w = H • [ d ]ᵈ • H ↑  ^ 3 • S } {u = H • [ d ]ᵈ • S • H ↑  ^ 3} (cright cright sym (lemma-comm-S-w↑ (H ^ 3))) ⟩
  dual (H • [ d ]ᵈ • S • H ↑ ^ 3) ≈⟨ by-duality  {w = H • [ d ]ᵈ • S • H ↑  ^ 3 } {u = H • ([ d ]ᵈ • S) • H ↑ ^ 3}(sa (□ ^ 4) (□ • □ ^ 2 • □) auto) ⟩
  dual (H • ([ d ]ᵈ • S) • H ↑ ^ 3) ≈⟨ by-duality {w = (H • ([ d ]ᵈ • S) • H ↑ ^ 3)} {u = (H • (dirs • diro • [ d' ]ᵈ) • H ↑ ^ 3)} (cright cleft lemma-D-br d S-gen (λ ())) ⟩
  dual (H • (dirs • diro • [ d' ]ᵈ) • H ↑ ^ 3) ≈⟨ refl ⟩
  H ↑ • (dual dirs • dual diro • dual [ d' ]ᵈ) • H ^ 3 ≈⟨ cright cleft left-unit ⟩
  H ↑ • (dual diro • dual [ d' ]ᵈ) • H ^ 3 ≈⟨ refl ⟩
  H ↑ • (ε • dual [ d' ]ᵈ) • H ^ 3 ≈⟨ cright cleft left-unit ⟩
  H ↑ • (dual [ d' ]ᵈ) • H ^ 3 ≈⟨ sym (lemma-B~dualD d') ⟩
  [ d' ]ᵇ ≈⟨ sym left-unit ⟩
  ε • [ d' ]ᵇ ≈⟨ cleft sym left-unit ⟩
  dual dir • [ d' ]ᵇ ∎
  where
  edd = dir-and-d' d S-gen λ ()
  dir = (S^ (edd .proj₁) • (edd .proj₂ .proj₁) ↑)
  dirs = S^ (edd .proj₁)
  diro = (edd .proj₂ .proj₁) ↑
  d' = edd .proj₂ .proj₂

lemma-B-br d@(a@(₁₊ _) , b@(₁₊ _)) g@(S-gen ↥) neqH neqCZ = begin
  [ d ]ᵇ • S ↑ ≈⟨ cleft lemma-B~dualD d ⟩
  (H ↑ • dual [ d ]ᵈ • H ^ 3) • S ↑ ≈⟨ refl ⟩
  dual (H • [ d ]ᵈ • H ↑  ^ 3) • dual S ≈⟨ sa (□ ^ 3 • □) (□ ^ 4) auto ⟩
  dual (H • [ d ]ᵈ • H ↑  ^ 3 • S) ≈⟨ by-duality {w = H • [ d ]ᵈ • H ↑  ^ 3 • S } {u = H • [ d ]ᵈ • S • H ↑  ^ 3} (cright cright sym (lemma-comm-S-w↑ (H ^ 3))) ⟩
  dual (H • [ d ]ᵈ • S • H ↑ ^ 3) ≈⟨ by-duality  {w = H • [ d ]ᵈ • S • H ↑  ^ 3 } {u = H • ([ d ]ᵈ • S) • H ↑ ^ 3}(sa (□ ^ 4) (□ • □ ^ 2 • □) auto) ⟩
  dual (H • ([ d ]ᵈ • S) • H ↑ ^ 3) ≈⟨ by-duality {w = (H • ([ d ]ᵈ • S) • H ↑ ^ 3)} {u = (H • (dirs • diro • [ d' ]ᵈ) • H ↑ ^ 3)} (cright cleft lemma-D-br d S-gen (λ ())) ⟩
  dual (H • (dirs • diro • [ d' ]ᵈ) • H ↑ ^ 3) ≈⟨ refl ⟩
  H ↑ • (dual dirs • dual diro • dual [ d' ]ᵈ) • H ^ 3 ≈⟨ cright cleft left-unit ⟩
  H ↑ • (dual diro • dual [ d' ]ᵈ) • H ^ 3 ≈⟨ refl ⟩
  H ↑ • (ε • dual [ d' ]ᵈ) • H ^ 3 ≈⟨ cright cleft left-unit ⟩
  H ↑ • (dual [ d' ]ᵈ) • H ^ 3 ≈⟨ sym (lemma-B~dualD d') ⟩
  [ d' ]ᵇ ≈⟨ sym left-unit ⟩
  ε • [ d' ]ᵇ ≈⟨ cleft sym left-unit ⟩
  dual dir • [ d' ]ᵇ ∎
  where
  edd = dir-and-d' d S-gen λ ()
  dir = (S^ (edd .proj₁) • (edd .proj₂ .proj₁) ↑)
  dirs = S^ (edd .proj₁)
  diro = (edd .proj₂ .proj₁) ↑
  d' = edd .proj₂ .proj₂


