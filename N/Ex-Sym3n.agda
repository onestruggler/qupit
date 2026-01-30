{-# OPTIONS  --safe #-}
--{-# OPTIONS --termination-depth=2 #-}
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
open import Presentation.Tactics hiding ([_])
open import Data.Nat.Primality



module N.Ex-Sym3n (p-2 : ℕ) (p-prime : Prime (2+ p-2)) where

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

private
  variable
    n : ℕ

open import Zp.ModularArithmetic
open PrimeModulus p-2 p-prime
open import N.Symplectic p-2 p-prime
open import N.Lemmas-2Qupit-Sym p-2 p-prime
open import N.Ex-Sym p-2 p-prime
open import N.Ex-Sym2 p-2 p-prime
open import N.Ex-Sym2n p-2 p-prime
open Lemmas0a
open Lemmas0b hiding (lemma-comm-Ex-H')


open Symplectic
open Lemmas-Sym

open Symplectic-GroupLike

open import Data.Nat.DivMod
open import Data.Fin.Properties


open import N.Ex-Sym1 p-2 p-prime
open import N.Ex-Sym3 p-2 p-prime
open Lemmas0a1
open Lemmas0c

open Lemmas0b hiding (lemma-comm-Ex-H')

open Duality


lemma-Ex-Ex↑-CZ'a : let open PB ((₃₊ n) QRel,_===_) in
  Ex ↑ • CZ • Ex ↑ ≈ ⊤⊥ ↑ • CZ ↓ • ⊥⊤ ↑
lemma-Ex-Ex↑-CZ'a {n@₀} = begin
  (CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑) ↑ • CZ • (CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑) ↑ ≈⟨ (cright (cright lemma-cong↑ _ _ lemma-comm-Ex-CZ')) ⟩
  (CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑) ↑ • CZ • ((H ↓ • H ↑ • CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑) • CZ) ↑ ≈⟨ general-comm auto ⟩
  (((CZ • H ↑ • H • CZ • H ↑ • H • CZ) • H) • H ↑) ↑ • CZ • (H ↑ • (H ↓ • CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑ • CZ)) ↑ ≈⟨ cong (cleft (sym (lemma-cong↑ _ _ lemma-comm-Ex-H↑'-n ))) (cright (cright lemma-cong↑ _ _ lemma-comm-Ex-H')) ⟩ 
  ((H ↑  • CZ • H ↑  • H • CZ • H ↑ • H • CZ) • H ↑) ↑ • CZ • (H ↑ • ((CZ • H • H ↑ • CZ • H • H ↑ • CZ) • H ↑)) ↑ ≈⟨ general-comm auto ⟩
  (H ↑  • CZ • H ↑  • H • CZ • H ↑ • H) ↑ • (CZ ↑ • H ↑ ↑ ^ 2) • CZ  • (((CZ • H ↑ • H • CZ • H • H ↑ • CZ) • H ↑)) ↑ ≈⟨ (cright (cleft  (lemma-cong↑ _ _ lemma-semi-CZ-HH↑))) ⟩
  (H ↑  • CZ • H ↑  • H • CZ • H ↑ • H) ↑ • (H ↑ ↑ ^ 2 • CZ^ (₋₁) ↑) • CZ  • (((CZ • H ↑ • H • CZ • H • H ↑ • CZ) • H ↑)) ↑ ≈⟨ cright cright general-comm auto ⟩
  (H ↑  • CZ • H ↑  • H • CZ • H ↑ • H) ↑ • (H ↑ ↑ ^ 2 • CZ^ (₋₁) ↑) • CZ ↑ • CZ  • ((( H ↑ • H • CZ • H • H ↑ • CZ) • H ↑)) ↑ ≈⟨ (cright special-assoc (□ ^ 2 • □ ^ 3) (□ ^ 3 • □ ^ 2) auto) ⟩
  (H ↑  • CZ • H ↑  • H • CZ • H ↑ • H) ↑ • (H ↑ ↑ ^ 2 • CZ^ (₋₁) ↑ • CZ ↑) • CZ  • ((( H ↑ • H • CZ • H • H ↑ • CZ) • H ↑)) ↑ ≈⟨ (cright cleft cright aux) ⟩
  (H ↑  • CZ • H ↑  • H • CZ • H ↑ • H) ↑ • (H ↑ ↑ ^ 2 • ε) • CZ  • ((( H ↑ • H • CZ • H • H ↑ • CZ) • H ↑)) ↑ ≈⟨ general-comm auto ⟩
  (H ↑  • CZ • H ↑  • H • CZ • H ↑ • H) ↑ • (H ↑ ↑ ^ 2) • CZ  • ((( H ↑ • H • CZ • H • H ↑ • CZ) • H ↑)) ↑ ≈⟨ general-comm auto ⟩
  (H ↑  • CZ • H ↑  • H • CZ • H) ↑ • (H ↑ ↑ ^ 4) • CZ  • (((H • CZ • H • H ↑ • CZ) • H ↑)) ↑ ≈⟨ (cright rewrite-sym0 100 auto) ⟩
  (H ↑  • CZ • H ↑  • H • CZ • H) ↑ • CZ  • (((H • CZ • H • H ↑ • CZ) • H ↑)) ↑ ≈⟨ by-assoc auto ⟩
  ⊤⊥ ↑ • CZ ↓ • ⊥⊤ ↑ ∎
  where
  open PB ((₃₊ n) QRel,_===_)
  open PP ((₃₊ n) QRel,_===_)
  module B1 = PB ((₂₊ n) QRel,_===_)
  module P1 = PP ((₂₊ n) QRel,_===_)
  open SR word-setoid
  open Sym0-Rewriting (₂₊ n)
  open Commuting-Symplectic (suc n)
  open Lemmas-2Q n
  open Pattern-Assoc
  aux : CZ^ (₋₁) ↑ • CZ ↑ ≈ ε
  aux = begin
    CZ^ (₋₁) ↑ • CZ ↑ ≈⟨ lemma-cong↑ _ _ (P1.word-comm (toℕ ₋₁) 1 B1.refl) ⟩
    CZ ↑ • CZ^ (₋₁) ↑ ≡⟨ Eq.cong (\ xx -> CZ ↑ • (CZ ^ xx) ↑) (toℕ-fromℕ< (NP.n<1+n (₁₊ p-2))) ⟩
    CZ ↑ • (CZ ^ p-1) ↑ ≈⟨ lemma-cong↑ _ _ (B1.axiom order-CZ) ⟩
    ε ∎

lemma-Ex-Ex↑-CZ'a {n@(suc _)} = begin
  (CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑) ↑ • CZ • (CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑) ↑ ≈⟨ (cright (cright lemma-cong↑ _ _ lemma-comm-Ex-CZ'-n)) ⟩
  (CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑) ↑ • CZ • ((H ↓ • H ↑ • CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑) • CZ) ↑ ≈⟨ general-comm auto ⟩
  (((CZ • H ↑ • H • CZ • H ↑ • H • CZ) • H) • H ↑) ↑ • CZ • (H ↑ • (H ↓ • CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑ • CZ)) ↑ ≈⟨ cong (cleft (sym (lemma-cong↑ _ _ lemma-comm-Ex-H↑'-n ))) (cright (cright lemma-cong↑ _ _ lemma-comm-Ex-H')) ⟩ 
  ((H ↑  • CZ • H ↑  • H • CZ • H ↑ • H • CZ) • H ↑) ↑ • CZ • (H ↑ • ((CZ • H • H ↑ • CZ • H • H ↑ • CZ) • H ↑)) ↑ ≈⟨ general-comm auto ⟩
  (H ↑  • CZ • H ↑  • H • CZ • H ↑ • H) ↑ • (CZ ↑ • H ↑ ↑ ^ 2) • CZ  • (((CZ • H ↑ • H • CZ • H • H ↑ • CZ) • H ↑)) ↑ ≈⟨ (cright (cleft  (lemma-cong↑ _ _ lemma-semi-CZ-HH↑))) ⟩
  (H ↑  • CZ • H ↑  • H • CZ • H ↑ • H) ↑ • (H ↑ ↑ ^ 2 • CZ^ (₋₁) ↑) • CZ  • (((CZ • H ↑ • H • CZ • H • H ↑ • CZ) • H ↑)) ↑ ≈⟨ cright cright general-comm auto ⟩
  (H ↑  • CZ • H ↑  • H • CZ • H ↑ • H) ↑ • (H ↑ ↑ ^ 2 • CZ^ (₋₁) ↑) • CZ ↑ • CZ  • ((( H ↑ • H • CZ • H • H ↑ • CZ) • H ↑)) ↑ ≈⟨ (cright special-assoc (□ ^ 2 • □ ^ 3) (□ ^ 3 • □ ^ 2) auto) ⟩
  (H ↑  • CZ • H ↑  • H • CZ • H ↑ • H) ↑ • (H ↑ ↑ ^ 2 • CZ^ (₋₁) ↑ • CZ ↑) • CZ  • ((( H ↑ • H • CZ • H • H ↑ • CZ) • H ↑)) ↑ ≈⟨ (cright cleft cright aux) ⟩
  (H ↑  • CZ • H ↑  • H • CZ • H ↑ • H) ↑ • (H ↑ ↑ ^ 2 • ε) • CZ  • ((( H ↑ • H • CZ • H • H ↑ • CZ) • H ↑)) ↑ ≈⟨ general-comm auto ⟩
  (H ↑  • CZ • H ↑  • H • CZ • H ↑ • H) ↑ • (H ↑ ↑ ^ 2) • CZ  • ((( H ↑ • H • CZ • H • H ↑ • CZ) • H ↑)) ↑ ≈⟨ general-comm auto ⟩
  (H ↑  • CZ • H ↑  • H • CZ • H) ↑ • (H ↑ ↑ ^ 4) • CZ  • (((H • CZ • H • H ↑ • CZ) • H ↑)) ↑ ≈⟨ (cright rewrite-sym0 100 auto) ⟩
  (H ↑  • CZ • H ↑  • H • CZ • H) ↑ • CZ  • (((H • CZ • H • H ↑ • CZ) • H ↑)) ↑ ≈⟨ by-assoc auto ⟩
  ⊤⊥ ↑ • CZ ↓ • ⊥⊤ ↑ ∎
  where
  open PB ((₃₊ n) QRel,_===_)
  open PP ((₃₊ n) QRel,_===_)
  module B1 = PB ((₂₊ n) QRel,_===_)
  module P1 = PP ((₂₊ n) QRel,_===_)
  open SR word-setoid
  open Sym0-Rewriting (₂₊ n)
  open Commuting-Symplectic (suc n)
  open Lemmas-2Q n
  open Pattern-Assoc
  aux : CZ^ (₋₁) ↑ • CZ ↑ ≈ ε
  aux = begin
    CZ^ (₋₁) ↑ • CZ ↑ ≈⟨ lemma-cong↑ _ _ (P1.word-comm (toℕ ₋₁) 1 B1.refl) ⟩
    CZ ↑ • CZ^ (₋₁) ↑ ≡⟨ Eq.cong (\ xx -> CZ ↑ • (CZ ^ xx) ↑) (toℕ-fromℕ< (NP.n<1+n (₁₊ p-2))) ⟩
    CZ ↑ • (CZ ^ p-1) ↑ ≈⟨ lemma-cong↑ _ _ (B1.axiom order-CZ) ⟩
    ε ∎



lemma-Ex-Ex↑-CZ'b : let open PB ((₃₊ n) QRel,_===_) in
  Ex • CZ ↑ • Ex ≈ ⊥⊤ ↓ • CZ ↑ • ⊤⊥ ↓
lemma-Ex-Ex↑-CZ'b {n} = begin
  Ex • CZ ↑ • Ex ≈⟨ refl ⟩
  (CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑) • CZ ↑ • (CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑) ≈⟨ (cright (cright lemma-comm-Ex-CZ'-n)) ⟩
  (CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑) • CZ ↑  • ((H ↓ • H ↑ • CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑) • CZ) ≈⟨ general-comm auto ⟩
  (((CZ • H • H ↑  • CZ • H • H ↑ • CZ) • H ↑) • H) • CZ ↑ • (H • (H ↑  • CZ • H ↑  • H • CZ • H ↑  • H • CZ)) ≈⟨ cong (cleft sym lemma-comm-Ex-H') (cright (cright lemma-comm-Ex-H↑'-n)) ⟩
  ((H ↓ • CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑ • CZ) • H) • CZ ↑ • (H • ((CZ • H ↑ • H • CZ • H ↑ • H • CZ) • H)) ≈⟨ general-comm auto ⟩
  (H ↓ • CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑) • (CZ • H ^ 2) • CZ ↑ • (((CZ • H • H ↑ • CZ • H ↑ • H • CZ) • H)) ≈⟨ (cright (cleft lemma-semi-CZ-HH↓)) ⟩
  (H ↓ • CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑) • (H ^ 2 • CZ^ ₋₁) • CZ ↑ • (((CZ • H • H ↑ • CZ • H ↑ • H • CZ) • H)) ≈⟨ cright cright general-comm auto ⟩
  (H ↓ • CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑) • (H ^ 2 • CZ^ ₋₁) • CZ • CZ ↑ • (((H • H ↑ • CZ • H ↑ • H • CZ) • H)) ≈⟨ (cright special-assoc (□ ^ 2 • □ ^ 2) (□ ^ 3 • □) auto) ⟩
  (H ↓ • CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑) • (H ^ 2 • CZ^ ₋₁ • CZ) • CZ ↑ • (((H • H ↑ • CZ • H ↑ • H • CZ) • H)) ≈⟨ (cright cleft cright aux) ⟩
  (H ↓ • CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑) • (H ^ 2 • ε) • CZ ↑ • (((H • H ↑ • CZ • H ↑ • H • CZ) • H)) ≈⟨ rewrite-sym0 100 auto ⟩
  (H ↓ • CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑) • (H ^ 2) • CZ ↑ • (((H • H ↑ • CZ • H ↑ • H • CZ) • H)) ≈⟨ general-comm auto ⟩
  (H ↓ • CZ • H ↓ • H ↑ • CZ • H ↑) • (H ^ 4) • CZ ↑ • (((H ↑ • CZ • H ↑ • H • CZ) • H)) ≈⟨ rewrite-sym0 100 auto ⟩
  ⊥⊤ ↓ • CZ ↑ • ⊤⊥ ↓ ∎
  where
  open PB ((₃₊ n) QRel,_===_)
  open PP ((₃₊ n) QRel,_===_)
  open SR word-setoid
  open Sym0-Rewriting (₂₊ n)
  open Commuting-Symplectic (suc n)
  open Lemmas-2Q (₁₊ n)
  open Pattern-Assoc
  aux : CZ^ (₋₁)  • CZ  ≈ ε
  aux = begin
    CZ^ (₋₁)  • CZ  ≈⟨ (word-comm (toℕ ₋₁) 1 refl) ⟩
    CZ  • CZ^ (₋₁)  ≡⟨ Eq.cong (\ xx -> CZ  • (CZ ^ xx) ) (toℕ-fromℕ< (NP.n<1+n (₁₊ p-2))) ⟩
    CZ  • (CZ ^ p-1)  ≈⟨ (axiom order-CZ) ⟩
    ε ∎



lemma-CZ02-alt : let open PB ((₃₊ n) QRel,_===_) in
  Ex ↑ • CZ • Ex ↑ ≈ Ex • CZ ↑ • Ex
lemma-CZ02-alt {n} = begin
  Ex ↑ • CZ • Ex ↑ ≈⟨ lemma-Ex-Ex↑-CZ'a ⟩
  ⊤⊥ ↑ • CZ ↓ • ⊥⊤ ↑ ≈⟨ axiom selinger-c13 ⟩
  ⊥⊤ ↓ • CZ ↑ • ⊤⊥ ↓ ≈⟨ sym lemma-Ex-Ex↑-CZ'b ⟩
  Ex • CZ ↑ • Ex ∎
  where
  open PB ((₃₊ n) QRel,_===_)
  open PP ((₃₊ n) QRel,_===_)
  open SR word-setoid
  open Commuting-Symplectic (suc n)




module Powers-Rewriting where

  open Symplectic
  open Rewriting
  open Lemmas0

  lemma-comm-Ex-S↑↑ : let open PB ((₃₊ n) QRel,_===_) in
    Ex • S ↑ ↑ ≈ S ↑ ↑ • Ex
  lemma-comm-Ex-S↑↑ {n} = general-comm auto
    where
    open Commuting-Symplectic (₁₊ n)

  lemma-comm-Ex↑-S : let open PB ((₃₊ n) QRel,_===_) in
    Ex ↑ • S ≈ S • Ex ↑
  lemma-comm-Ex↑-S {n} = general-comm auto
    where
    open Commuting-Symplectic (suc n)

  lemma-comm-Ex-H↑↑ : let open PB ((₃₊ n) QRel,_===_) in
    Ex • H ↑ ↑ ≈ H ↑ ↑ • Ex
  lemma-comm-Ex-H↑↑ {n} = general-comm auto
    where
    open PB ((₂₊ n) QRel,_===_)
    open PP ((₂₊ n) QRel,_===_)
    open Commuting-Symplectic (suc n)

  lemma-comm-Ex↑-H : let open PB ((₃₊ n) QRel,_===_) in
    Ex ↑ • H ≈ H • Ex ↑
  lemma-comm-Ex↑-H {n} = general-comm auto
    where
    open PB ((₂₊ n) QRel,_===_)
    open PP ((₂₊ n) QRel,_===_)
    open Commuting-Symplectic (suc n)



  step-powers : ∀ {n} -> let open PB ((₁₊ n) QRel,_===_) hiding (_===_) in Step-Function (Gen (₁₊ n))  ((₁₊ n) QRel,_===_)

  -- Order of generators.
  step-powers ((H-gen) ∷ (H-gen) ∷ (H-gen) ∷ (H-gen) ∷ xs) = just (xs , at-head (PB.axiom order-H))
  step-powers ((H-gen ↥) ∷ (H-gen ↥) ∷ (H-gen ↥) ∷ (H-gen ↥) ∷ xs) = just (xs , at-head (PB.axiom (cong↑ order-H)))
  step-powers ((H-gen ↥ ↥) ∷ (H-gen ↥ ↥) ∷ (H-gen ↥ ↥) ∷ (H-gen ↥ ↥) ∷ xs) = just (xs , at-head (PB.axiom (cong↑ (cong↑ order-H))))

  step-powers ((S-gen) ∷ (H-gen) ∷ (S-gen) ∷ (H-gen) ∷ (S-gen) ∷ (H-gen) ∷ xs) = just (xs , at-head (PB.axiom order-SH))
  step-powers ((S-gen ↥) ∷ (H-gen ↥) ∷ (S-gen ↥) ∷ (H-gen ↥) ∷ (S-gen ↥) ∷ (H-gen ↥) ∷ xs) = just (xs , at-head (PB.axiom (cong↑ order-SH)))
  step-powers ((S-gen ↥ ↥) ∷ (H-gen ↥ ↥) ∷ (S-gen ↥ ↥) ∷ (H-gen ↥ ↥) ∷ (S-gen ↥ ↥) ∷ (H-gen ↥ ↥) ∷ xs) = just (xs , at-head (PB.axiom (cong↑ (cong↑ order-SH))))

  step-powers (CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ xs) = just (xs , at-head (lemma-order-Ex-n))
  step-powers (CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ xs) = just (xs , at-head ( (lemma-cong↑ _ _ lemma-order-Ex-n)))

  step-powers (H-gen ∷ CZ-gen ∷ H-gen ∷ H-gen ∷ CZ-gen ∷ H-gen ∷ xs) = just (xs , at-head (lemma-order-ₕ|ₕ))
  step-powers (H-gen ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ xs) = just (xs , at-head (lemma-cong↑ _ _ lemma-order-ₕ|ₕ))

{-
  step-powers (CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ xs) = just (CZ-gen ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ xs , at-head (PB.sym (lemma-comm-Ex-CZ-n)))
  step-powers (CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ xs) = just (CZ-gen ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ xs , at-head (PB.sym ( (lemma-cong↑ _ _ lemma-comm-Ex-CZ-n))))

  step-powers (CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ H-gen ∷ xs) = just (H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ xs , at-head (PB.sym (lemma-comm-Ex-H-n)))
  step-powers (CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ H-gen ↥ ∷ xs) = just (H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ xs , at-head (PB.sym ( (lemma-cong↑ _ _ lemma-comm-Ex-H-n))))

  step-powers (CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ S-gen ∷ xs) = just (S-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ xs , at-head (PB.sym (lemma-comm-Ex-S)))
  step-powers (CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ S-gen ↥ ∷ xs) = just (S-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ xs , at-head (PB.sym ( (lemma-cong↑ _ _ lemma-comm-Ex-S))))

  step-powers {suc n} (CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ S-gen ↥ ∷ xs) = just (S-gen ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ xs , at-head (((lemma-Ex-S↑-n {n}))))
  step-powers (CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ S-gen ↥ ↥ ∷ xs) = just (S-gen ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ xs , at-head (lemma-cong↑ _ _ lemma-Ex-S↑-n))

  step-powers {suc n} (CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ H-gen ↥ ∷ xs) = just (H-gen ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ xs , at-head (((lemma-Ex-H↑-n {n}))))
  step-powers (CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ H-gen ↥ ↥ ∷ xs) = just (H-gen ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ xs , at-head (lemma-cong↑ _ _ lemma-Ex-H↑-n))
-}

  -- Trivial commutations.
  step-powers (CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ S-gen ↥ ↥ ∷ xs) = just (S-gen ↥ ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ xs , at-head ( (lemma-comm-Ex-S↑↑)))
  step-powers (CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ S-gen ∷ xs) = just (S-gen ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ xs , at-head ( ( (lemma-comm-Ex↑-S))))
  step-powers (CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ xs) = just (H-gen ↥ ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ xs , at-head ( (lemma-comm-Ex-H↑↑)))
  step-powers (CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ H-gen ∷ xs) = just (H-gen ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ xs , at-head ( ( (lemma-comm-Ex↑-H))))

  -- Catch-all
  step-powers _ = nothing


module Rewriting-Powers (m : ℕ) where
  open Symplectic
  open Rewriting
  open Powers-Rewriting
  open Rewriting.Step (step-cong (step-powers {m})) renaming (general-rewrite to rewrite-powers) public



-- ----------------------------------------------------------------------
-- * Lemmas

module Lemmas where
open Lemmas0

open Symplectic
open import Zp.ModularArithmetic


lemma-Ex-Ex↑-CZ : let open PB ((₃₊ n) QRel,_===_) in
  Ex • Ex ↑ • CZ ≈ CZ ↑ • Ex • Ex ↑
lemma-Ex-Ex↑-CZ {n} = begin
  Ex • Ex ↑ • CZ ≈⟨ rewrite-powers 100 auto ⟩
  Ex • (Ex ↑ • CZ • Ex ↑) • Ex ↑ ≈⟨ cong refl (cong lemma-CZ02-alt refl) ⟩
  Ex • (Ex • CZ ↑ • Ex) • Ex ↑ ≈⟨ rewrite-powers 100 auto ⟩
  CZ ↑ • Ex • Ex ↑ ∎
  where
  open PB ((₃₊ n) QRel,_===_)
  open PP ((₃₊ n) QRel,_===_)
  open SR word-setoid
  open Rewriting-Powers (₂₊ n)


lemma-Ex↑-Ex-CZ↑ : let open PB ((₃₊ n) QRel,_===_) in
  Ex ↑ • Ex • CZ ↑ ≈ CZ • Ex ↑ • Ex
lemma-Ex↑-Ex-CZ↑ {n} = bbc (Ex • Ex ↑) (Ex • Ex ↑) aux
  where
  open PB ((₃₊ n) QRel,_===_)
  open PP ((₃₊ n) QRel,_===_)
  open Rewriting-Powers (₂₊ n)
  open SR word-setoid
  open Basis-Change _ ((₃₊ n) QRel,_===_) grouplike
  aux : (Ex • Ex ↑) • (Ex ↑ • Ex • CZ ↑) • Ex • Ex ↑ ≈ (Ex • Ex ↑) • (CZ • Ex ↑ • Ex) • Ex • Ex ↑
  aux = begin
    (Ex • Ex ↑) • (Ex ↑ • Ex • CZ ↑) • Ex • Ex ↑ ≈⟨ rewrite-powers 100 auto ⟩
    (CZ ↑) • Ex • Ex ↑ ≈⟨ sym lemma-Ex-Ex↑-CZ ⟩
    Ex • Ex ↑ • CZ ≈⟨ rewrite-powers 100 auto ⟩
    (Ex • Ex ↑) • (CZ • Ex ↑ • Ex) • Ex • Ex ↑ ∎
  

lemma-[Ex-Ex↑]-CZ : let open PB ((₃₊ n) QRel,_===_) in
  (Ex • Ex ↑) • CZ ≈ CZ ↑ • Ex • Ex ↑
lemma-[Ex-Ex↑]-CZ {n} = begin
  (Ex • Ex ↑) • CZ ≈⟨ rewrite-powers 100 auto ⟩
  Ex • Ex ↑ • CZ ≈⟨ rewrite-powers 100 auto ⟩
  Ex • (Ex ↑ • CZ • Ex ↑) • Ex ↑ ≈⟨ cong refl (cong lemma-CZ02-alt refl) ⟩
  Ex • (Ex • CZ ↑ • Ex) • Ex ↑ ≈⟨ rewrite-powers 100 auto ⟩
  CZ ↑ • Ex • Ex ↑ ∎
  where
  open PB ((₃₊ n) QRel,_===_)
  open PP ((₃₊ n) QRel,_===_)
  open SR word-setoid
  open Rewriting-Powers (₂₊ n)


lemma-[Ex↑-Ex]-CZ↑ : let open PB ((₃₊ n) QRel,_===_) in
  (Ex ↑ • Ex) • CZ ↑ ≈ CZ • Ex ↑ • Ex
lemma-[Ex↑-Ex]-CZ↑ {n} = begin
  (Ex ↑ • Ex) • CZ ↑ ≈⟨ rewrite-powers 100 auto ⟩
  Ex ↑ • Ex • CZ ↑ ≈⟨ rewrite-powers 100 auto ⟩
  Ex ↑ • (Ex • CZ ↑ • Ex) • Ex ≈⟨ cong refl (cong (sym lemma-CZ02-alt) refl) ⟩
  Ex ↑ • (Ex ↑ • CZ • Ex ↑) • Ex ≈⟨ rewrite-powers 100 auto ⟩
  CZ • Ex ↑ • Ex ∎
  where
  open PB ((₃₊ n) QRel,_===_)
  open PP ((₃₊ n) QRel,_===_)
  open SR word-setoid
  open Rewriting-Powers (₂₊ n)

lemma-Ex-S : let open PB ((₂₊ n) QRel,_===_) in 

  Ex • S ≈ S ↑ • Ex

lemma-Ex-S = PB.sym (lemma-comm-Ex-S)





lemma-Ex-H : let open PB ((₂₊ n) QRel,_===_) in 

  Ex • H ≈ H ↑ • Ex

lemma-Ex-H = PB.sym (lemma-comm-Ex-H-n)

lemma-Ex-Hᵏ : ∀ k → let open PB ((₂₊ n) QRel,_===_) in 

  Ex • H ^ k ≈ H ↑ ^ k • Ex

lemma-Ex-Hᵏ {n} ₀ = trans right-unit (sym left-unit)
  where
  open PB ((₂₊ n) QRel,_===_)
lemma-Ex-Hᵏ {n} ₁ = lemma-Ex-H
lemma-Ex-Hᵏ {n} (₂₊ k) = begin
  Ex • H • H ^ ₁₊ k ≈⟨ sym assoc ⟩
  (Ex • H) • H ^ ₁₊ k ≈⟨ cong lemma-Ex-H refl ⟩
  (H ↑ • Ex) • H ^ ₁₊ k ≈⟨ assoc ⟩
  H ↑ • Ex • H ^ ₁₊ k ≈⟨ cong refl (lemma-Ex-Hᵏ (₁₊ k)) ⟩
  H ↑ • H ↑ ^ ₁₊ k • Ex ≈⟨ sym assoc ⟩
  ((H ↑) • (H ↑) ^ ₁₊ k) • Ex ∎
  where
  open PB ((₂₊ n) QRel,_===_)
  open PP ((₂₊ n) QRel,_===_)
  open SR word-setoid



lemma-comm-H↑-Sᵏ : ∀ {n} k →
  let open PB ((₂₊ n) QRel,_===_) in

  H ↑ • S ^ k ≈ S ^ k • H ↑

lemma-comm-H↑-Sᵏ {n} ₀ = trans right-unit (sym left-unit)
  where
  open PB ((₂₊ n) QRel,_===_)
  open PP ((₂₊ n) QRel,_===_)
  open SR word-setoid
lemma-comm-H↑-Sᵏ {n} (₁) = axiom comm-S
  where
  open PB ((₂₊ n) QRel,_===_)
  open PP ((₂₊ n) QRel,_===_)
  open SR word-setoid
lemma-comm-H↑-Sᵏ {n} (₂₊ k) = begin
  (H ↑) • S ^ ₂₊ k ≈⟨ refl ⟩
  (H ↑) • S • S ^ ₁₊ k ≈⟨ sym assoc ⟩
  (H ↑ • S) • S ^ ₁₊ k ≈⟨ cong (axiom comm-S) refl ⟩
  (S • H ↑) • S ^ ₁₊ k ≈⟨ assoc ⟩
  S • H ↑ • S ^ ₁₊ k ≈⟨ cong refl (lemma-comm-H↑-Sᵏ (₁₊ k)) ⟩
  S • S ^ ₁₊ k • H ↑ ≈⟨ sym assoc ⟩
  S ^ ₂₊ k • (H ↑) ∎
  where
  open PB ((₂₊ n) QRel,_===_)
  open PP ((₂₊ n) QRel,_===_)
  open SR word-setoid




lemma-comm-CZ-w↑↑ : ∀ {n} w → let open PB ((₂₊ n) QRel,_===_) in

  CZ • w ↑ ↑ ≈ w ↑ ↑ • CZ

lemma-comm-CZ-w↑↑ {n} [ H-gen ]ʷ = PB.sym (PB.axiom comm-CZ)
lemma-comm-CZ-w↑↑ {n} [ S-gen ]ʷ = PB.sym (PB.axiom comm-CZ)
lemma-comm-CZ-w↑↑ {n} [ CZ-gen ]ʷ = PB.sym (PB.axiom comm-CZ)
--lemma-comm-CZ-w↑↑ {n} [ EX-gen ]ʷ = PB.sym (PB.axiom comm-CZ)
lemma-comm-CZ-w↑↑ {n} [ x ↥ ]ʷ = PB.sym (PB.axiom comm-CZ)
lemma-comm-CZ-w↑↑ {n} ε = PB.trans PB.right-unit (PB.sym PB.left-unit)
lemma-comm-CZ-w↑↑ {n} (w • v) = begin
  CZ • (((w • v) ↑) ↑) ≈⟨ refl ⟩
  CZ • w ↑ ↑ • v ↑ ↑ ≈⟨ sym assoc ⟩
  (CZ • w ↑ ↑) • v ↑ ↑ ≈⟨ cong (lemma-comm-CZ-w↑↑ w) refl ⟩
  (w ↑ ↑ • CZ) • v ↑ ↑ ≈⟨ assoc ⟩
  w ↑ ↑ • CZ • v ↑ ↑ ≈⟨ cong refl (lemma-comm-CZ-w↑↑ v) ⟩
  w ↑ ↑ • v ↑ ↑ • CZ ≈⟨ sym assoc ⟩
  (((w • v) ↑) ↑) • CZ ∎
  where
  open PB ((₂₊ n) QRel,_===_)
  open PP ((₂₊ n) QRel,_===_)
  open SR word-setoid


lemma-comm-CX-w↑↑ : ∀ {n} w → let open PB ((₂₊ n) QRel,_===_) in

  CX • w ↑ ↑ ≈ w ↑ ↑ • CX

lemma-comm-CX-w↑↑ {n} w = begin
  CX • w ↑ ↑ ≈⟨ by-assoc auto ⟩
  H ^ 3 • CZ • H • w ↑ ↑ ≈⟨ (cright cright lemma-comm-H-w↑ (w ↑)) ⟩
  H ^ 3 • CZ • w ↑ ↑ • H ≈⟨ by-assoc auto ⟩
  H ^ 3 • (CZ • w ↑ ↑) • H ≈⟨ (cright cleft lemma-comm-CZ-w↑↑ w) ⟩
  H ^ 3 • (w ↑ ↑ • CZ) • H ≈⟨ trans (by-assoc auto) assoc ⟩
  (H ^ 3 • w ↑ ↑) • CZ • H ≈⟨ (cleft lemma-comm-Hᵏ-w↑ 3 (w ↑)) ⟩
  (w ↑ ↑ • H ^ 3) • CZ • H ≈⟨ assoc ⟩
  w ↑ ↑ • CX ∎
  where
  open PB ((₂₊ n) QRel,_===_)
  open PP ((₂₊ n) QRel,_===_)
  open SR word-setoid


lemma-comm-S-w↑↑ : ∀ {n} w → let open PB ((₂₊ n) QRel,_===_) in

  S • w ↑ ↑ ≈ w ↑ ↑ • S

lemma-comm-S-w↑↑ {n} [ H-gen ]ʷ = PB.sym (PB.axiom comm-S)
lemma-comm-S-w↑↑ {n} [ S-gen ]ʷ = PB.sym (PB.axiom comm-S)
lemma-comm-S-w↑↑ {n} [ CZ-gen ]ʷ = PB.sym (PB.axiom comm-S)
lemma-comm-S-w↑↑ {n} [ EX-gen ]ʷ = PB.sym (PB.axiom comm-S)
--lemma-comm-S-w↑↑ {n} [ x ↥ ]ʷ = PB.sym (PB.axiom comm-S)
lemma-comm-S-w↑↑ {n} ε = PB.trans PB.right-unit (PB.sym PB.left-unit)
lemma-comm-S-w↑↑ {n} (w • v) = begin
  S • (((w • v) ↑) ↑) ≈⟨ refl ⟩
  S • w ↑ ↑ • v ↑ ↑ ≈⟨ sym assoc ⟩
  (S • w ↑ ↑) • v ↑ ↑ ≈⟨ cong (lemma-comm-S-w↑↑ w) refl ⟩
  (w ↑ ↑ • S) • v ↑ ↑ ≈⟨ assoc ⟩
  w ↑ ↑ • S • v ↑ ↑ ≈⟨ cong refl (lemma-comm-S-w↑↑ v) ⟩
  w ↑ ↑ • v ↑ ↑ • S ≈⟨ sym assoc ⟩
  (((w • v) ↑) ↑) • S ∎
  where
  open PB ((₂₊ n) QRel,_===_)
  open PP ((₂₊ n) QRel,_===_)
  open SR word-setoid


lemma-comm-H-w↑↑ : ∀ {n} w → let open PB ((₂₊ n) QRel,_===_) in

  H • w ↑ ↑ ≈ w ↑ ↑ • H

lemma-comm-H-w↑↑ {n} [ H-gen ]ʷ = PB.sym (PB.axiom comm-H)
lemma-comm-H-w↑↑ {n} [ S-gen ]ʷ = PB.sym (PB.axiom comm-H)
lemma-comm-H-w↑↑ {n} [ CZ-gen ]ʷ = PB.sym (PB.axiom comm-H)
lemma-comm-H-w↑↑ {n} [ EX-gen ]ʷ = PB.sym (PB.axiom comm-H)
--lemma-comm-H-w↑↑ {n} [ x ↥ ]ʷ = PB.sym (PB.axiom comm-H)
lemma-comm-H-w↑↑ {n} ε = PB.trans PB.right-unit (PB.sym PB.left-unit)
lemma-comm-H-w↑↑ {n} (w • v) = begin
  H • (((w • v) ↑) ↑) ≈⟨ refl ⟩
  H • w ↑ ↑ • v ↑ ↑ ≈⟨ sym assoc ⟩
  (H • w ↑ ↑) • v ↑ ↑ ≈⟨ cong (lemma-comm-H-w↑↑ w) refl ⟩
  (w ↑ ↑ • H) • v ↑ ↑ ≈⟨ assoc ⟩
  w ↑ ↑ • H • v ↑ ↑ ≈⟨ cong refl (lemma-comm-H-w↑↑ v) ⟩
  w ↑ ↑ • v ↑ ↑ • H ≈⟨ sym assoc ⟩
  (((w • v) ↑) ↑) • H ∎
  where
  open PB ((₂₊ n) QRel,_===_)
  open PP ((₂₊ n) QRel,_===_)
  open SR word-setoid


lemma-comm-CZᵏ-w↑↑ : ∀ {n} k w → let open PB ((₂₊ n) QRel,_===_) in

  CZ ^ k • w ↑ ↑ ≈ w ↑ ↑ • CZ ^ k

lemma-comm-CZᵏ-w↑↑ {n} ₀ w = trans left-unit (sym right-unit)
  where
  open PB ((₂₊ n) QRel,_===_)
lemma-comm-CZᵏ-w↑↑ {n} ₁ w = lemma-comm-CZ-w↑↑ w
  where
  open PB ((₂₊ n) QRel,_===_)
lemma-comm-CZᵏ-w↑↑ {n} (₂₊ k) w = begin
  (CZ • CZ ^ ₁₊ k) • (w ↑ ↑) ≈⟨ assoc ⟩
  CZ • CZ ^ ₁₊ k • (w ↑ ↑) ≈⟨ cong refl (lemma-comm-CZᵏ-w↑↑ (₁₊ k) w) ⟩
  CZ • (w ↑ ↑) • CZ ^ ₁₊ k ≈⟨ sym assoc ⟩
  (CZ • w ↑ ↑) • CZ ^ ₁₊ k ≈⟨ cong (lemma-comm-CZ-w↑↑ w) refl ⟩
  (w ↑ ↑ • CZ) • CZ ^ ₁₊ k ≈⟨ assoc ⟩
  (w ↑ ↑) • CZ • CZ ^ ₁₊ k ∎
  where
  open PB ((₂₊ n) QRel,_===_)
  open PP ((₂₊ n) QRel,_===_)
  open SR word-setoid

lemma-comm-Sᵏ-w↑↑ : ∀ {n} k w → let open PB ((₂₊ n) QRel,_===_) in

  S ^ k • w ↑ ↑ ≈ w ↑ ↑ • S ^ k

lemma-comm-Sᵏ-w↑↑ {n} ₀ w = trans left-unit (sym right-unit)
  where
  open PB ((₂₊ n) QRel,_===_)
lemma-comm-Sᵏ-w↑↑ {n} ₁ w = lemma-comm-S-w↑↑ w
  where
  open PB ((₂₊ n) QRel,_===_)
lemma-comm-Sᵏ-w↑↑ {n} (₂₊ k) w = begin
  (S • S ^ ₁₊ k) • (w ↑ ↑) ≈⟨ assoc ⟩
  S • S ^ ₁₊ k • (w ↑ ↑) ≈⟨ cong refl (lemma-comm-Sᵏ-w↑↑ (₁₊ k) w) ⟩
  S • (w ↑ ↑) • S ^ ₁₊ k ≈⟨ sym assoc ⟩
  (S • w ↑ ↑) • S ^ ₁₊ k ≈⟨ cong (lemma-comm-S-w↑↑ w) refl ⟩
  (w ↑ ↑ • S) • S ^ ₁₊ k ≈⟨ assoc ⟩
  (w ↑ ↑) • S • S ^ ₁₊ k ∎
  where
  open PB ((₂₊ n) QRel,_===_)
  open PP ((₂₊ n) QRel,_===_)
  open SR word-setoid

lemma-comm-Hᵏ-w↑↑ : ∀ {n} k w → let open PB ((₂₊ n) QRel,_===_) in

  H ^ k • w ↑ ↑ ≈ w ↑ ↑ • H ^ k

lemma-comm-Hᵏ-w↑↑ {n} ₀ w = trans left-unit (sym right-unit)
  where
  open PB ((₂₊ n) QRel,_===_)
lemma-comm-Hᵏ-w↑↑ {n} ₁ w = lemma-comm-H-w↑↑ w
  where
  open PB ((₂₊ n) QRel,_===_)
lemma-comm-Hᵏ-w↑↑ {n} (₂₊ k) w = begin
  (H • H ^ ₁₊ k) • (w ↑ ↑) ≈⟨ assoc ⟩
  H • H ^ ₁₊ k • (w ↑ ↑) ≈⟨ cong refl (lemma-comm-Hᵏ-w↑↑ (₁₊ k) w) ⟩
  H • (w ↑ ↑) • H ^ ₁₊ k ≈⟨ sym assoc ⟩
  (H • w ↑ ↑) • H ^ ₁₊ k ≈⟨ cong (lemma-comm-H-w↑↑ w) refl ⟩
  (w ↑ ↑ • H) • H ^ ₁₊ k ≈⟨ assoc ⟩
  (w ↑ ↑) • H • H ^ ₁₊ k ∎
  where
  open PB ((₂₊ n) QRel,_===_)
  open PP ((₂₊ n) QRel,_===_)
  open SR word-setoid

{-
lemma-CZᵏ-H↑² : ∀ (k : ℤ ₚ) → let open PB ((₂₊ n) QRel,_===_) in

  CZ ^ toℕ k • H ↑ ^ 2 ≈ H ↑ ^ 2 • CZ ^ toℕ (- k)

lemma-CZᵏ-H↑² {n} ₀ = trans left-unit (sym right-unit)
  where open PB ((₂₊ n) QRel,_===_)
lemma-CZᵏ-H↑² {n} ₁ = lemma-semi-CZ-HH↑
  where
  open PB ((₂₊ n) QRel,_===_)
  open Lemmas-2Q n
lemma-CZᵏ-H↑² {n} ₂ = begin
  CZ ^ 2 • H ↑ ^ 2 ≈⟨ by-assoc auto ⟩
  CZ • (CZ • H ↑ ^ 2) ≈⟨ cong refl (lemma-semi-CZ-HH↑) ⟩
  CZ • (H ↑ ^ 2 • CZ ^ 2) ≈⟨ sym assoc ⟩
  (CZ • H ↑ ^ 2) • CZ ^ 2 ≈⟨ cong (lemma-semi-CZ-HH↑) refl ⟩
  (H ↑ ^ 2 • CZ ^ 2) • CZ ^ 2 ≈⟨ by-assoc auto  ⟩
  (H ↑ ^ 2 • CZ) • CZ ^ 3 ≈⟨ cong refl (axiom order-CZ) ⟩
  (H ↑ ^ 2 • CZ) • ε ≈⟨ right-unit ⟩
  ((H ↑) • (H ↑)) • CZ ∎
  where
  open PB ((₂₊ n) QRel,_===_)
  open PP ((₂₊ n) QRel,_===_)
  open SR word-setoid
  open Lemmas-2Q n
-}

lemma-Ex-HᵏSˡ : let open PB ((₂₊ n) QRel,_===_) in ∀ k l →

  Ex • (H ^ k • S ^ l) ≈ (H ^ k • S ^ l) ↑ • Ex

lemma-Ex-HᵏSˡ {n} k l = begin
  Ex • H ^ k • S ^ l ≈⟨ sym assoc ⟩
  (Ex • H ^ k) • S ^ l ≈⟨ cong (lemma-Ex-Hᵏ k) refl ⟩
  (H ↑ ^ k • Ex) • S ^ l ≈⟨ assoc ⟩
  H ↑ ^ k • Ex • S ^ l ≈⟨ cong refl (lemma-Ex-Sᵏ l) ⟩
  H ↑ ^ k • S ↑ ^ l • Ex ≈⟨ sym assoc ⟩
  (H ↑ ^ k • S ↑ ^ l) • Ex ≈⟨ cong (cong (refl' (lemma-^-↑ H k)) (refl' (lemma-^-↑ S l))) refl ⟩
  ((H ^ k) ↑ • (S ^ l) ↑) • Ex ≈⟨ cong refl refl ⟩
  ((H ) ^ k • (S ) ^ l) ↑ • Ex ∎
  where
  open PB ((₂₊ n) QRel,_===_)
  open PP ((₂₊ n) QRel,_===_)
  open SR word-setoid


-- ----------------------------------------------------------------------
-- * Lemmas

module Lemmas2 where
open Lemmas0
open Lemmas-Sym

open Symplectic
open import Zp.ModularArithmetic


lemma-CZᵏ-S↑ : let open PB ((₂₊ n) QRel,_===_) in ∀  k →

  CZ ^ k • S ↑ ≈ S ↑ • CZ ^ k

lemma-CZᵏ-S↑ {n} ₀ = PB.trans PB.left-unit (PB.sym PB.right-unit)
lemma-CZᵏ-S↑ {n} ₁ = PB.axiom comm-CZ-S↑
lemma-CZᵏ-S↑ {n} (₂₊ k) = begin
  (CZ • CZ ^ ₁₊ k) • (S ↑) ≈⟨ assoc ⟩
  CZ • CZ ^ ₁₊ k • (S ↑) ≈⟨ cong refl (lemma-CZᵏ-S↑ (₁₊ k)) ⟩
  CZ • (S ↑) • CZ ^ ₁₊ k ≈⟨ sym assoc ⟩
  (CZ • S ↑) • CZ ^ ₁₊ k ≈⟨ cong (axiom comm-CZ-S↑) refl ⟩
  (S ↑ • CZ) • CZ ^ ₁₊ k ≈⟨ assoc ⟩
  (S ↑) • CZ • CZ ^ ₁₊ k ∎
  where
  open PB ((₂₊ n) QRel,_===_)
  open PP ((₂₊ n) QRel,_===_)
  open SR word-setoid

lemma-CZᵏ-S↑² : let open PB ((₂₊ n) QRel,_===_) in ∀  k →

  CZ ^ k • S⁻¹ ↑ ≈ S⁻¹ ↑ • CZ ^ k

lemma-CZᵏ-S↑² {n} k = begin
  CZ ^ k • (S⁻¹ ↑) ≈⟨ (cright sym (refl' (lemma-^-↑ S p-1))) ⟩
  CZ ^ k • (S ↑) ^ p-1 ≈⟨  word-comm k p-1 (lemma-CZᵏ-S↑ ₁) ⟩
  (S ↑) ^ p-1 • CZ ^ k ≈⟨  (cleft refl' (lemma-^-↑ S p-1)) ⟩
  (S⁻¹ ↑) • CZ ^ k ∎
  where
  open PB ((₂₊ n) QRel,_===_)
  open PP ((₂₊ n) QRel,_===_)
  open SR word-setoid

lemma-CZᵏ-Ex : let open PB ((₂₊ n) QRel,_===_) in ∀  k →

  CZ ^ k • Ex ≈ Ex • CZ ^ k

lemma-CZᵏ-Ex {n} ₀ = PB.trans PB.left-unit (PB.sym PB.right-unit)
lemma-CZᵏ-Ex {n} ₁ = lemma-comm-Ex-CZ-n
lemma-CZᵏ-Ex {n} (₂₊ k) = begin
  (CZ • CZ ^ ₁₊ k) • (Ex) ≈⟨ assoc ⟩
  CZ • CZ ^ ₁₊ k • (Ex) ≈⟨ cong refl (lemma-CZᵏ-Ex (₁₊ k)) ⟩
  CZ • (Ex) • CZ ^ ₁₊ k ≈⟨ sym assoc ⟩
  (CZ • Ex) • CZ ^ ₁₊ k ≈⟨ cong (lemma-comm-Ex-CZ-n) refl ⟩
  (Ex • CZ) • CZ ^ ₁₊ k ≈⟨ assoc ⟩
  (Ex) • CZ • CZ ^ ₁₊ k ∎
  where
  open PB ((₂₊ n) QRel,_===_)
  open PP ((₂₊ n) QRel,_===_)
  open SR word-setoid


lemma-CZᵏ-CZ↑ : let open PB ((₃₊ n) QRel,_===_) in ∀  k →

  CZ ^ k • CZ ↑ ≈ CZ ↑ • CZ ^ k

lemma-CZᵏ-CZ↑ {n} ₀ = PB.trans PB.left-unit (PB.sym PB.right-unit)
lemma-CZᵏ-CZ↑ {n} ₁ = PB.sym (PB.axiom selinger-c12)
lemma-CZᵏ-CZ↑ {n} (₂₊ k) = begin
  (CZ • CZ ^ ₁₊ k) • (CZ ↑) ≈⟨ assoc ⟩
  CZ • CZ ^ ₁₊ k • (CZ ↑) ≈⟨ cong refl (lemma-CZᵏ-CZ↑ (₁₊ k)) ⟩
  CZ • (CZ ↑) • CZ ^ ₁₊ k ≈⟨ sym assoc ⟩
  (CZ • CZ ↑) • CZ ^ ₁₊ k ≈⟨ sym (cong (axiom selinger-c12) refl) ⟩
  (CZ ↑ • CZ) • CZ ^ ₁₊ k ≈⟨ assoc ⟩
  (CZ ↑) • CZ • CZ ^ ₁₊ k ∎
  where
  open PB ((₃₊ n) QRel,_===_)
  open PP ((₃₊ n) QRel,_===_)
  open SR word-setoid


lemma-CZᵏ↑-CZ : let open PB ((₃₊ n) QRel,_===_) in ∀  k →

  (CZ ^ k) ↑ • CZ ≈ CZ • (CZ ^ k) ↑

lemma-CZᵏ↑-CZ {n} ₀ = PB.trans PB.left-unit (PB.sym PB.right-unit)
lemma-CZᵏ↑-CZ {n} ₁ = PB.axiom selinger-c12
lemma-CZᵏ↑-CZ {n} (₂₊ k) = begin
  (CZ • CZ ^ ₁₊ k) ↑ • (CZ) ≈⟨ assoc ⟩
  CZ ↑ • (CZ ^ ₁₊ k) ↑ • (CZ) ≈⟨ cong refl (lemma-CZᵏ↑-CZ (₁₊ k)) ⟩
  CZ ↑ • (CZ) • (CZ ^ ₁₊ k) ↑ ≈⟨ sym assoc ⟩
  (CZ ↑ • CZ) • (CZ ^ ₁₊ k) ↑ ≈⟨ cong (axiom selinger-c12) refl ⟩
  (CZ • CZ ↑) • (CZ ^ ₁₊ k) ↑ ≈⟨ assoc ⟩
  (CZ) • (CZ • CZ ^ ₁₊ k) ↑ ∎
  where
  open PB ((₃₊ n) QRel,_===_)
  open PP ((₃₊ n) QRel,_===_)
  open SR word-setoid

{-
lemma-CZᵏ-HH↑ : let open PB ((₂₊ n) QRel,_===_) in ∀  k →

  CZ ^ toℕ k • H ↑ ^ 2 ≈ H ↑ ^ 2 • CZ ^ toℕ (- k)

lemma-CZᵏ-HH↑ {n} ₀ = PB.trans PB.left-unit (PB.sym PB.right-unit)
lemma-CZᵏ-HH↑ {n} ₁ = lemma-semi-CZ-HH↑
  where
  open Lemmas-2Q 0
lemma-CZᵏ-HH↑ {n} ₂ = begin
  (CZ • CZ) • (H ↑) • (H ↑) ≈⟨ assoc ⟩
  CZ • CZ • (H ↑) • (H ↑) ≈⟨ cong refl (trans (lemma-semi-CZ-HH↑) assoc) ⟩
  CZ • (H ↑) • (H ↑) • CZ ^ 2 ≈⟨ by-assoc auto ⟩
  (CZ • (H ↑) • (H ↑)) • CZ ^ 2 ≈⟨ cong (trans (lemma-semi-CZ-HH↑) assoc) refl ⟩
  ((H ↑) • (H ↑) • CZ ^ 2) • CZ ^ 2 ≈⟨ ? ⟩
  ((H ↑) • (H ↑)) • CZ ∎
  where
  open PB ((₂₊ n) QRel,_===_)
  open PP ((₂₊ n) QRel,_===_)
  open SR word-setoid
  open Lemmas-2Q 0
-}



lemma-Ex-HᵏSˡ' : let open PB ((₂₊ n) QRel,_===_) in ∀ k l →

  Ex • (H ^ k • S ^ l) ↑ ≈ (H ^ k • S ^ l) • Ex

lemma-Ex-HᵏSˡ' {n} k l = begin
  Ex • ((H ^ k • S ^ l) ↑) ≈⟨ cong refl (sym right-unit) ⟩
  Ex • (H ^ k • S ^ l) ↑ • ε ≈⟨ cong refl (cong refl (sym lemma-order-Ex-n)) ⟩
  Ex • (H ^ k • S ^ l) ↑ • Ex • Ex ≈⟨ sym (cong refl assoc) ⟩
  Ex • ((H ^ k • S ^ l) ↑ • Ex) • Ex ≈⟨ cong refl (cong (sym (lemma-Ex-HᵏSˡ k l)) refl) ⟩
  Ex • (Ex • (H ^ k • S ^ l)) • Ex ≈⟨ cong refl assoc ⟩
  Ex • Ex • (H ^ k • S ^ l) • Ex ≈⟨ sym assoc ⟩
  (Ex • Ex) • (H ^ k • S ^ l) • Ex ≈⟨ cong (lemma-order-Ex-n) refl ⟩
  ε • (H ^ k • S ^ l) • Ex ≈⟨ left-unit ⟩
  (H ^ k • S ^ l) • Ex ∎
  where
  open PB ((₂₊ n) QRel,_===_)
  open PP ((₂₊ n) QRel,_===_)
  open SR word-setoid

lemma-Ex-Sᵏ↑ : ∀ k → let open PB ((₂₊ n) QRel,_===_) in 

  Ex • (S ^ k) ↑ ≈ (S ^ k) • Ex

lemma-Ex-Sᵏ↑ {n} k = begin
  Ex • ((S ^ k) ↑) ≈⟨ cong refl (sym right-unit) ⟩
  Ex • (S ^ k) ↑ • ε ≈⟨ cong refl (cong refl (sym lemma-order-Ex-n)) ⟩
  Ex • (S ^ k) ↑ • Ex • Ex ≈⟨ sym (cong refl assoc) ⟩
  Ex • ((S ^ k) ↑ • Ex) • Ex ≈⟨ (cright (cleft (cleft sym (refl' (lemma-^-↑ S k))))) ⟩
  Ex • ((S ↑ ^ k) • Ex) • Ex ≈⟨ cong refl (cong (sym (lemma-Ex-Sᵏ k)) refl) ⟩
  Ex • (Ex • (S ^ k)) • Ex ≈⟨ cong refl assoc ⟩
  Ex • Ex • (S ^ k) • Ex ≈⟨ sym assoc ⟩
  (Ex • Ex) • (S ^ k) • Ex ≈⟨ cong (lemma-order-Ex-n) refl ⟩
  ε • (S ^ k) • Ex ≈⟨ left-unit ⟩
  (S ^ k) • Ex ∎
  where
  open PB ((₂₊ n) QRel,_===_)
  open PP ((₂₊ n) QRel,_===_)
  open SR word-setoid


lemma-Ex-S↑ᵏ : ∀ k → let open PB ((₂₊ n) QRel,_===_) in 

  Ex • (S ↑ ^ k) ≈ (S ^ k) • Ex

lemma-Ex-S↑ᵏ {n} k = begin
  Ex • (S ↑ ^ k) ≈⟨ refl' (Eq.cong (\ xx -> Ex • xx) (lemma-^-↑ S k)) ⟩
  Ex • (S ^ k) ↑ ≈⟨ lemma-Ex-Sᵏ↑ k ⟩
  (S ^ k) • Ex ∎
  where
  open PB ((₂₊ n) QRel,_===_)
  open PP ((₂₊ n) QRel,_===_)
  open SR word-setoid




module Swap-Rewriting where

-- This module provides a complete rewrite system for 1-qubit
-- Swap operators. It is specialized toward relations on qubit 0
-- (but can also be applied to qubit 1 via duality).
open Symplectic
open Rewriting
open Lemmas0
open Lemmas2

lemma-comm-Ex-S↑↑ : let open PB ((₃₊ n) QRel,_===_) in
  Ex • S ↑ ↑ ≈ S ↑ ↑ • Ex
lemma-comm-Ex-S↑↑ {n} = general-comm auto
  where
  open Commuting-Symplectic (₁₊ n)

lemma-comm-Ex↑-S : let open PB ((₃₊ n) QRel,_===_) in
  Ex ↑ • S ≈ S • Ex ↑
lemma-comm-Ex↑-S {n} = general-comm auto
  where
  open Commuting-Symplectic (suc n)

lemma-comm-Ex-H↑↑ : let open PB ((₃₊ n) QRel,_===_) in
  Ex • H ↑ ↑ ≈ H ↑ ↑ • Ex
lemma-comm-Ex-H↑↑ {n} = general-comm auto
  where
  open PB ((₂₊ n) QRel,_===_)
  open PP ((₂₊ n) QRel,_===_)
  open Commuting-Symplectic (suc n)

lemma-comm-Ex↑-H : let open PB ((₃₊ n) QRel,_===_) in
  Ex ↑ • H ≈ H • Ex ↑
lemma-comm-Ex↑-H {n} = general-comm auto
  where
  open PB ((₂₊ n) QRel,_===_)
  open PP ((₂₊ n) QRel,_===_)
  open Commuting-Symplectic (suc n)



step-swap : ∀ {n} -> let open PB ((₁₊ n) QRel,_===_) hiding (_===_) in Step-Function (Gen (₁₊ n))  ((₁₊ n) QRel,_===_)

-- Order of generators.
step-swap ((H-gen) ∷ (H-gen) ∷ (H-gen) ∷ (H-gen) ∷ xs) = just (xs , at-head (PB.axiom order-H))
step-swap ((H-gen ↥) ∷ (H-gen ↥) ∷ (H-gen ↥) ∷ (H-gen ↥) ∷ xs) = just (xs , at-head (PB.axiom (cong↑ order-H)))
step-swap ((H-gen ↥ ↥) ∷ (H-gen ↥ ↥) ∷ (H-gen ↥ ↥) ∷ (H-gen ↥ ↥) ∷ xs) = just (xs , at-head (PB.axiom (cong↑ (cong↑ order-H))))

step-swap ((S-gen) ∷ (H-gen) ∷ (S-gen) ∷ (H-gen) ∷ (S-gen) ∷ (H-gen) ∷ xs) = just (xs , at-head (PB.axiom order-SH))
step-swap ((S-gen ↥) ∷ (H-gen ↥) ∷ (S-gen ↥) ∷ (H-gen ↥) ∷ (S-gen ↥) ∷ (H-gen ↥) ∷ xs) = just (xs , at-head (PB.axiom (cong↑ order-SH)))
step-swap ((S-gen ↥ ↥) ∷ (H-gen ↥ ↥) ∷ (S-gen ↥ ↥) ∷ (H-gen ↥ ↥) ∷ (S-gen ↥ ↥) ∷ (H-gen ↥ ↥) ∷ xs) = just (xs , at-head (PB.axiom (cong↑ (cong↑ order-SH))))

step-swap (CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ xs) = just (xs , at-head (lemma-order-Ex-n))
step-swap (CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ xs) = just (xs , at-head ( (lemma-cong↑ _ _ lemma-order-Ex-n)))



step-swap (CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ∷ xs) = just (CZ-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ xs , at-head ( (lemma-Ex-Ex↑-CZ)))
step-swap (CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ↥ ∷ xs) = just (CZ-gen ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ xs , at-head ( (lemma-Ex↑-Ex-CZ↑)))



step-swap (CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ xs) = just (CZ-gen ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ xs , at-head (PB.sym (lemma-comm-Ex-CZ-n)))
step-swap (CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ xs) = just (CZ-gen ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ xs , at-head (PB.sym ( (lemma-cong↑ _ _ lemma-comm-Ex-CZ-n))))

step-swap (CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ H-gen ∷ xs) = just (H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ xs , at-head (PB.sym (lemma-comm-Ex-H-n)))
step-swap (CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ H-gen ↥ ∷ xs) = just (H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ xs , at-head (PB.sym ( (lemma-cong↑ _ _ lemma-comm-Ex-H-n))))

step-swap (CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ S-gen ∷ xs) = just (S-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ xs , at-head (PB.sym (lemma-comm-Ex-S)))
step-swap (CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ S-gen ↥ ∷ xs) = just (S-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ xs , at-head (PB.sym ( (lemma-cong↑ _ _ lemma-comm-Ex-S))))

step-swap {suc n} (CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ S-gen ↥ ∷ xs) = just (S-gen ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ xs , at-head (((lemma-Ex-S↑-n {n}))))
step-swap (CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ S-gen ↥ ↥ ∷ xs) = just (S-gen ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ xs , at-head (lemma-cong↑ _ _ lemma-Ex-S↑-n))

step-swap {suc n} (CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ H-gen ↥ ∷ xs) = just (H-gen ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ xs , at-head (((lemma-Ex-H↑-n {n}))))
step-swap (CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ H-gen ↥ ↥ ∷ xs) = just (H-gen ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ xs , at-head (lemma-cong↑ _ _ lemma-Ex-H↑-n))


-- Trivial commutations.
step-swap (CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ S-gen ↥ ↥ ∷ xs) = just (S-gen ↥ ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ xs , at-head ( (lemma-comm-Ex-S↑↑)))
step-swap (CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ S-gen ∷ xs) = just (S-gen ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ xs , at-head ( ( (lemma-comm-Ex↑-S))))
step-swap (CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ xs) = just (H-gen ↥ ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ xs , at-head ( (lemma-comm-Ex-H↑↑)))
step-swap (CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ H-gen ∷ xs) = just (H-gen ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ xs , at-head ( ( (lemma-comm-Ex↑-H))))

-- Catch-all
step-swap _ = nothing


module Rewriting-Swap (m : ℕ) where
  open Symplectic
  open Rewriting
  open Swap-Rewriting
  open Rewriting.Step (step-cong (step-swap {m})) renaming (general-rewrite to rewrite-swap) public


module Swap0-Rewriting where


  open Symplectic
  open Rewriting
  open Lemmas0
  open Lemmas2

  -- ----------------------------------------------------------------------
  -- * Rewrite rules for 1-qubit Swap0 relations

  step-swap0 : let open PB ((₁₊ n) QRel,_===_) hiding (_===_) in Step-Function (Gen (₁₊ n))  ((₁₊ n) QRel,_===_)

  step-swap0 (CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ xs) = just (xs , at-head (lemma-order-Ex-n))
  step-swap0 (CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ xs) = just (xs , at-head ( (lemma-cong↑ _ _ lemma-order-Ex-n)))


  step-swap0 (CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ xs) = just (CZ-gen ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ xs , at-head (PB.sym (lemma-comm-Ex-CZ-n)))
  step-swap0 (CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ xs) = just (CZ-gen ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ xs , at-head (PB.sym ( (lemma-cong↑ _ _ lemma-comm-Ex-CZ-n))))

  step-swap0 (CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ H-gen ∷ xs) = just (H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ xs , at-head (PB.sym (lemma-comm-Ex-H-n)))
  step-swap0 (CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ H-gen ↥ ∷ xs) = just (H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ xs , at-head (PB.sym ( (lemma-cong↑ _ _ lemma-comm-Ex-H-n))))

  step-swap0 (CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ S-gen ∷ xs) = just (S-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ xs , at-head (PB.sym (lemma-comm-Ex-S)))
  step-swap0 (CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ S-gen ↥ ∷ xs) = just (S-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ xs , at-head (PB.sym ( (lemma-cong↑ _ _ lemma-comm-Ex-S))))

  step-swap0 {suc n} (CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ S-gen ↥ ∷ xs) = just (S-gen ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ xs , at-head (((lemma-Ex-S↑-n {n}))))
  step-swap0 (CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ S-gen ↥ ↥ ∷ xs) = just (S-gen ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ xs , at-head (lemma-cong↑ _ _ lemma-Ex-S↑-n))

  step-swap0 {suc n} (CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ H-gen ↥ ∷ xs) = just (H-gen ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ xs , at-head (((lemma-Ex-H↑-n {n}))))
  step-swap0 (CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ H-gen ↥ ↥ ∷ xs) = just (H-gen ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ xs , at-head (lemma-cong↑ _ _ lemma-Ex-H↑-n))


  -- Trivial commutations.
  step-swap0 (CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ S-gen ↥ ↥ ∷ xs) = just (S-gen ↥ ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ xs , at-head ( (lemma-comm-Ex-S↑↑)))
  step-swap0 (CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ S-gen ∷ xs) = just (S-gen ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ xs , at-head ( ( (lemma-comm-Ex↑-S))))
  step-swap0 (CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ xs) = just (H-gen ↥ ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ xs , at-head ( (lemma-comm-Ex-H↑↑)))
  step-swap0 (CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ H-gen ∷ xs) = just (H-gen ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ xs , at-head ( ( (lemma-comm-Ex↑-H))))

  -- Catch-all
  step-swap0 _ = nothing


module Rewriting-Swap0 (n : ℕ) where
  open Symplectic
  open Rewriting
  open Swap0-Rewriting
  open Rewriting.Step (step-cong (step-swap0 {n})) renaming (general-rewrite to rewrite-swap0) public



open Symplectic
open import Zp.ModularArithmetic
--  open Rewriting-Symplectic
open Rewriting


lemma-comm-Ex-w↑↑ : ∀ {n} w → let open PB ((₂₊ n) QRel,_===_) in

  Ex • w ↑ ↑ ≈ w ↑ ↑ • Ex

lemma-comm-Ex-w↑↑ {n} [ H-gen ]ʷ = rewrite-sym0 (suc n) 1000 auto
  where
  open Sym0-Rewriting
lemma-comm-Ex-w↑↑ {n} [ S-gen ]ʷ = rewrite-sym0 (suc n) 1000 auto
  where
  open Sym0-Rewriting
lemma-comm-Ex-w↑↑ {n} [ CZ-gen ]ʷ = rewrite-sym0 (suc n) 1000 auto
  where
  open Sym0-Rewriting
-- lemma-comm-Ex-w↑↑ {n} [ EX-gen ]ʷ = rewrite-sym0 (suc n) 1000 auto
--   where
--   open Sym0-Rewriting
lemma-comm-Ex-w↑↑ {n} [ x ↥ ]ʷ = begin
  (CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑) • (([ x ↥ ]ʷ ↑) ↑) ≈⟨ by-assoc auto ⟩
  (CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑ • CZ • H ↓) • H ↑ • [ x ↥ ]ʷ ↑ ↑ ≈⟨ cong refl (sym (axiom (cong↑ comm-H))) ⟩
  (CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑ • CZ • H ↓) • [ x ↥ ]ʷ ↑ ↑ • H ↑ ≈⟨ by-assoc auto ⟩
  ((CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑ • CZ) • H ↓ • [ x ↥ ]ʷ ↑ ↑) • H ↑ ≈⟨ cong (cong refl (sym (axiom comm-H))) refl ⟩
  ((CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑ • CZ) • [ x ↥ ]ʷ ↑ ↑ • H ↓) • H ↑ ≈⟨ by-assoc auto ⟩
  ((CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑) • CZ • [ x ↥ ]ʷ ↑ ↑) • (H ↓ • H ↑) ≈⟨ cong (cong refl (sym (axiom comm-CZ))) refl ⟩
  ((CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑) • [ x ↥ ]ʷ ↑ ↑ • CZ) • (H ↓ • H ↑) ≈⟨ by-assoc auto ⟩
  ((CZ • H ↓ • H ↑ • CZ • H ↓) • H ↑ • [ x ↥ ]ʷ ↑ ↑) • (CZ • H ↓ • H ↑) ≈⟨ cong (cong refl (sym (axiom (cong↑ comm-H)))) refl ⟩
  ((CZ • H ↓ • H ↑ • CZ • H ↓) • [ x ↥ ]ʷ ↑ ↑ • H ↑) • (CZ • H ↓ • H ↑) ≈⟨ by-assoc auto ⟩
  ((CZ • H ↓ • H ↑ • CZ) • H ↓ • [ x ↥ ]ʷ ↑ ↑) • (H ↑ • CZ • H ↓ • H ↑) ≈⟨ cong (cong refl (sym (axiom comm-H))) refl ⟩
  ((CZ • H ↓ • H ↑ • CZ) • [ x ↥ ]ʷ ↑ ↑ • H ↓) • (H ↑ • CZ • H ↓ • H ↑) ≈⟨ by-assoc auto ⟩
  ((CZ • H ↓ • H ↑) • CZ • [ x ↥ ]ʷ ↑ ↑) • (H ↓ • H ↑ • CZ • H ↓ • H ↑) ≈⟨ cong (cong refl (sym (axiom comm-CZ))) refl ⟩
  ((CZ • H ↓ • H ↑) • [ x ↥ ]ʷ ↑ ↑ • CZ) • (H ↓ • H ↑ • CZ • H ↓ • H ↑) ≈⟨ by-assoc auto ⟩
  ((CZ • H ↓) • H ↑ • [ x ↥ ]ʷ ↑ ↑) • (CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑) ≈⟨ cong (cong refl (sym (axiom (cong↑ comm-H)))) refl ⟩
  ((CZ • H ↓) • [ x ↥ ]ʷ ↑ ↑ • H ↑) • (CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑) ≈⟨ by-assoc auto ⟩
  (CZ • H ↓ • [ x ↥ ]ʷ ↑ ↑) • (H ↑ • CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑) ≈⟨ cong (cong refl (sym (axiom comm-H))) refl ⟩
  (CZ • [ x ↥ ]ʷ ↑ ↑ • H ↓) • (H ↑ • CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑) ≈⟨ by-assoc auto ⟩
  (CZ • [ x ↥ ]ʷ ↑ ↑) • (H ↓ • H ↑ • CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑) ≈⟨ cong ( (sym (axiom comm-CZ))) refl ⟩
  ([ x ↥ ]ʷ ↑ ↑ • CZ) • (H ↓ • H ↑ • CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑) ≈⟨ by-assoc auto ⟩
  [ x ↥ ]ʷ ↑ ↑ • (CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑) ≈⟨ refl ⟩
  (([ x ↥ ]ʷ ↑) ↑) • Ex ∎
  where
  open PB ((₂₊ n) QRel,_===_)
  open PP ((₂₊ n) QRel,_===_)
  open SR word-setoid
lemma-comm-Ex-w↑↑ {n} ε = PB.trans PB.right-unit (PB.sym PB.left-unit)
lemma-comm-Ex-w↑↑ {n} (w • v) = begin
  Ex • (((w • v) ↑) ↑) ≈⟨ refl ⟩
  Ex • w ↑ ↑ • v ↑ ↑ ≈⟨ sym assoc ⟩
  (Ex • w ↑ ↑) • v ↑ ↑ ≈⟨ cong (lemma-comm-Ex-w↑↑ w) refl ⟩
  (w ↑ ↑ • Ex) • v ↑ ↑ ≈⟨ assoc ⟩
  w ↑ ↑ • Ex • v ↑ ↑ ≈⟨ cong refl (lemma-comm-Ex-w↑↑ v) ⟩
  w ↑ ↑ • v ↑ ↑ • Ex ≈⟨ sym assoc ⟩
  (((w • v) ↑) ↑) • Ex ∎
  where
  open PB ((₂₊ n) QRel,_===_)
  open PP ((₂₊ n) QRel,_===_)
  open SR word-setoid


open import Algebra.Properties.Ring (+-*-ring p-2)

lemma-semi-CXCZ^ : let open PB ((₂₊ n) QRel,_===_) in ∀ (k : ℤ ₚ) ->

  CX • CZ^ k ≈ S^ (- k + - k) ↑ • CZ^ k • CX

lemma-semi-CXCZ^ {n} k@₀ = begin
  CX • CZ^ k ≈⟨ right-unit ⟩
  CX ≈⟨ sym left-unit ⟩
  S^ ₀ ↑ • CX ≡⟨ Eq.cong (\ xx -> S^ xx ↑ • CX) (Eq.sym (Eq.trans (Eq.cong₂ _+_ -0#≈0# -0#≈0#) auto)) ⟩
  S^ (- k + - k) ↑ • CX ≈⟨ sym (cong refl left-unit) ⟩
  S^ (- k + - k) ↑ • CZ^ k • CX ∎
  where
  open PB ((₂₊ n) QRel,_===_)
  open PP ((₂₊ n) QRel,_===_)
  open SR word-setoid
lemma-semi-CXCZ^ {n} k@(₁₊ k') = by-emb' (lemma-semi-CXCZ^k (k , (λ ()))) (cright lemma-f* CZ (toℕ k)) (cong (lemma-f*-Sᵏ↑ (toℕ (- k + - k))) (cleft lemma-f* CZ (toℕ k)))
  where
  open PB ((₂₊ n) QRel,_===_)
  open PP ((₂₊ n) QRel,_===_)
  open import N.Embeding-2n p-2 p-prime n



lemma-semi-CXCZ^-alt : let open PB ((₂₊ n) QRel,_===_) in ∀ (k : ℤ ₚ) ->

  CX • CZ^ k ≈ S^ k • CX • S^ (- k) • S^ (- k) ↑ 

lemma-semi-CXCZ^-alt {n} k@₀ = begin
  CX • CZ^ k ≈⟨ right-unit ⟩
  CX ≈⟨ by-assoc auto ⟩
  CX • S^ (₀) • S^ (₀) ↑ ≡⟨ Eq.cong (\ xx -> CX • S^ (xx) • S^ (xx) ↑) (Eq.sym -0#≈0#) ⟩
  CX • S^ (- k) • S^ (- k) ↑ ≈⟨ sym left-unit ⟩
  S^ k • CX • S^ (- k) • S^ (- k) ↑ ∎
  where
  open PB ((₂₊ n) QRel,_===_)
  open PP ((₂₊ n) QRel,_===_)
  open SR word-setoid
lemma-semi-CXCZ^-alt {n} k@(₁₊ k') = by-emb' (lemma-CXCZ^k (k , (λ ()))) (cright lemma-f* CZ (toℕ k)) (cong (lemma-f* S (toℕ k)) (cright cong (lemma-f* S (toℕ (- k))) (lemma-f*-Sᵏ↑ (toℕ (- k)))))
  where
  open PB ((₂₊ n) QRel,_===_)
  open PP ((₂₊ n) QRel,_===_)

  open import N.Embeding-2n p-2 p-prime n
