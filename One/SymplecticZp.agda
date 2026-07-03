{-# OPTIONS --safe #-}
open import Level using (0ℓ)

open import Relation.Binary using (Rel)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Binary.Morphism.Definitions using (Homomorphic₂)
open import Relation.Binary.PropositionalEquality using (_≡_ ; inspect ; setoid ; module ≡-Reasoning ; _≢_) renaming ([_] to [_]')
import Relation.Binary.Reasoning.Setoid as SR
import Relation.Binary.PropositionalEquality as Eq
open import Relation.Nullary.Decidable using (yes ; no)


open import Function using (_∘_ ; id)
open import Function.Definitions using (Injective)

open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂ ; map₁ ; ∃)
open import Data.Product.Relation.Binary.Pointwise.NonDependent as PW using (≡×≡⇒≡ ; Pointwise ; ≡⇒≡×≡)
open import Data.Nat hiding (_^_ ; _+_ ; _*_ ; _%_ ; _/_)
open import Agda.Builtin.Nat using ()
import Data.Nat as Nat
open import Data.Fin hiding (_+_ ; _-_)
open import Data.Bool
open import Data.List hiding ([_])

open import Data.Maybe
open import Data.Sum using (_⊎_ ; inj₁ ; inj₂ ; [_,_])
open import Data.Unit using (⊤ ; tt)
open import Data.Empty using (⊥ ; ⊥-elim)

open import Word.Base as WB hiding (wfoldl ; _* ; _^'_)
open import Word.Properties
import Presentation.Horizontal-Syntactics as PB
import Presentation.Properties as PP
open PP using (NFProperty ; NFProperty')
import Presentation.CosetNF as CA
import Presentation.Reidemeister-Schreier as RS
open import Notations
module RSF = RS.Star-Injective-Full.Reidemeister-Schreier-Full

open import Presentation.Construct.Base hiding (_*_)
import Presentation.Construct.Properties.SemiDirectProduct2 as SDP2
import Presentation.Construct.Properties.DirectProduct as DP
import Presentation.Groups.Cyclic as Cyclic
open import Presentation.Tactics hiding ([_])


open import Data.Fin.Properties using (suc-injective ; toℕ-inject₁ ; toℕ-fromℕ)
import Data.Nat.Properties as NP
open import Presentation.GroupLike

module One.SymplecticZp where

open import Data.Nat.Primality
open import Data.Nat.Coprimality hiding (sym)
open import Data.Nat.GCD
open Bézout
open import Data.Empty
open import Algebra.Properties.Group

pattern auto = Eq.refl
pattern ₀ = zero
pattern ₁ = ₁₊ ₀
pattern ₂ = ₁₊ ₁
pattern ₃ = ₁₊ ₂
pattern ₄ = ₁₊ ₃



module Symplectic (p-2 : ℕ) (p-prime : Prime (₂₊ p-2)) where

  p : ℕ
  p = ₂₊ p-2
  open import Zp.ModularArithmetic
  open PrimeModulus p-2 p-prime hiding (p ; 0ₚ ; 1ₚ ; 0ₚ≢1ₚ)

  data Gen : Set where
    H-gen : Gen
    S-gen : Gen

  H : Word Gen
  H = [ H-gen ]ʷ

  H⁻¹ : Word Gen
  H⁻¹ = H ^ 3

  HH : Word Gen
  HH = H • H

  S : Word Gen
  S = [ S-gen ]ʷ
  
  S⁻¹ : Word Gen
  S⁻¹ = S ^ p-1


  S' : Word Gen
  S' = HH • S • HH

  SS : Word Gen
  SS = S • S

  X : Word Gen
  X = H • S • HH • SS • H

  Z : Word Gen
  Z = HH • S • HH • SS

  H^ : ℤ ₄ -> Word Gen
  H^ k = H ^ toℕ k

  S^ : ℤ ₚ -> Word Gen
  S^ k = S ^ toℕ k

  M : ℤ* ₚ -> Word Gen
  M x' = S^ x • H • S^ x⁻¹ • H • S^ x • H
    where
    x = x' .proj₁
    x⁻¹ = ((x' ⁻¹) .proj₁ )
    
  infixr 9 _^2
  _^2 : ℤ* ₚ -> ℤ ₚ
  _^2 x' = let x = x' .proj₁ in x * x 

  infix 4 _===_
  data _===_ : WRel Gen where
  
    order-S : S ^ p === ε
    order-H : H ^ 4 === ε
    order-SH : (S • H) ^ 3 === ε
    comm-HHS : H • H • S === S • H • H
    
    M-mul : ∀ (x y : ℤ* ₚ) -> M x • M y === M (x *' y)
    semi-MS : ∀ (x : ℤ* ₚ) -> M x • S === S^ (x ^2) • M x


  open PP _===_
  open PB _===_ hiding (_===_)
  grouplike : Grouplike _===_
  grouplike (H-gen) = H ^ 3 , by-assoc-and (axiom order-H) auto auto
  grouplike (S-gen) = S ^ p-1 , claim
    where
    open SR word-setoid
    claim : S ^ p-1 • S ≈ ε
    claim = begin
      S ^ p-1 • S ≈⟨ sym (lemma-^-+ S p-1 1) ⟩
      S ^ (p-1 Nat.+ 1) ≡⟨ Eq.cong (S ^_) (NP.+-comm p-1 1) ⟩
      (S ^ p) ≈⟨ axiom order-S ⟩
      ε ∎

  aux-Mx=Mx' : ∀ y y' -> y .proj₁ ≡ y' .proj₁ -> M y ≡ M y'
  aux-Mx=Mx' y y' eq = begin
    M y ≡⟨ auto ⟩
    S^ x • H • S^ x⁻¹ • H • S^ x • H ≡⟨ Eq.cong₂ (\ xx yy -> S^ xx • H • S^ yy • H • S^ x • H) eq aux-eq ⟩
    S^ x' • H • S^ x'⁻¹ • H • S^ x • H ≡⟨ Eq.cong (\ xx -> S^ x' • H • S^ x'⁻¹ • H • S^ xx • H) eq ⟩
    S^ x' • H • S^ x'⁻¹ • H • S^ x' • H ≡⟨ auto ⟩
    M y' ∎
    where
    open ≡-Reasoning
    x = y .proj₁
    x⁻¹ = ((y ⁻¹) .proj₁ )
    x' = y' .proj₁
    x'⁻¹ = ((y' ⁻¹) .proj₁ )
    aux-eq : x⁻¹ ≡ x'⁻¹
    aux-eq  = begin
      x⁻¹ ≡⟨  Eq.sym  (*-identityʳ x⁻¹) ⟩
      x⁻¹ * ₁ ≡⟨ Eq.cong (x⁻¹ *_) (Eq.sym (lemma-⁻¹ʳ x' {{nztoℕ {y = x'} {neq0 = y' .proj₂} }})) ⟩
      x⁻¹ * (x' * x'⁻¹) ≡⟨ Eq.sym (*-assoc x⁻¹ x' x'⁻¹) ⟩
      (x⁻¹ * x') * x'⁻¹ ≡⟨ Eq.cong (\ xx -> (x⁻¹ * xx) * x'⁻¹) (Eq.sym eq) ⟩
      (x⁻¹ * x) * x'⁻¹ ≡⟨ Eq.cong (_* x'⁻¹) (lemma-⁻¹ˡ x {{nztoℕ {y = x} {neq0 = y .proj₂} }}) ⟩
      ₁ * x'⁻¹ ≡⟨ *-identityˡ x'⁻¹ ⟩
      x'⁻¹ ∎


  open Eq using (_≢_)

  ₁⁻¹ = ((₁ , λ ()) ⁻¹) .proj₁

  M₁ = M (₁ , λ ())
  
  lemma-M1 : ε ≈ M (₁ , λ ())
  lemma-M1 = begin
    ε ≈⟨ _≈_.sym (axiom order-SH) ⟩
    (S • H) ^ 3 ≈⟨ by-assoc auto ⟩
    S • H • S • H • S • H ≡⟨ auto ⟩
    S^ ₁ • H • S^ ₁ • H • S^ ₁ • H ≡⟨ Eq.cong (\ xx -> S^ ₁ • H • S^ xx • H • S^ ₁ • H) (Eq.sym inv-₁) ⟩
    S^ ₁ • H • S^ ₁⁻¹ • H • S^ ₁ • H ≈⟨ refl ⟩
    M (₁ , λ ()) ∎
    where
    open SR word-setoid

{-
  aux-Mx=Mx' : ∀ y y' -> y .proj₁ ≡ y' .proj₁ -> M y ≡ M y'
  aux-Mx=Mx' y y' eq = begin
    M y ≡⟨ auto ⟩
    S^ x • H • S^ x⁻¹ • H • S^ x • H ≡⟨ Eq.cong₂ (\ xx yy -> S^ xx • H • S^ yy • H • S^ x • H) eq aux-eq ⟩
    S^ x' • H • S^ x'⁻¹ • H • S^ x • H ≡⟨ Eq.cong (\ xx -> S^ x' • H • S^ x'⁻¹ • H • S^ xx • H) eq ⟩
    S^ x' • H • S^ x'⁻¹ • H • S^ x' • H ≡⟨ auto ⟩
    M y' ∎
    where
    open ≡-Reasoning
    x = y .proj₁
    x⁻¹ = ((y ⁻¹) .proj₁ )
    x' = y' .proj₁
    x'⁻¹ = ((y' ⁻¹) .proj₁ )
    aux-eq : x⁻¹ ≡ x'⁻¹
    aux-eq  = begin
      x⁻¹ ≡⟨  Eq.sym  (*-identityʳ x⁻¹) ⟩
      x⁻¹ * ₁ ≡⟨ Eq.cong (x⁻¹ *_) (Eq.sym (lemma-⁻¹ʳ x' {{nztoℕ {y = x'} {neq0 = y' .proj₂} }})) ⟩
      x⁻¹ * (x' * x'⁻¹) ≡⟨ Eq.sym (*-assoc x⁻¹ x' x'⁻¹) ⟩
      (x⁻¹ * x') * x'⁻¹ ≡⟨ Eq.cong (\ xx -> (x⁻¹ * xx) * x'⁻¹) (Eq.sym eq) ⟩
      (x⁻¹ * x) * x'⁻¹ ≡⟨ Eq.cong (_* x'⁻¹) (lemma-⁻¹ˡ x {{nztoℕ {y = x} {neq0 = y .proj₂} }}) ⟩
      ₁ * x'⁻¹ ≡⟨ *-identityˡ x'⁻¹ ⟩
      x'⁻¹ ∎
-}


  lemma-M-power : ∀ (x : ℤ* ₚ) k -> let x' = x .proj₁ in  M x ^ k ≈ M (x ^' k)
  lemma-M-power x k@0 = lemma-M1 
  lemma-M-power x k@1 = begin
    M x ^ 1 ≡⟨ aux-Mx=Mx' x (x ^' 1) (Eq.sym (lemma-x^′1=x (x .proj₁))) ⟩
    M (x ^' 1) ∎
    where
    open SR word-setoid
  lemma-M-power x k@(₂₊ k') = begin
    M x • M x ^ ₁₊ k' ≈⟨ (cright lemma-M-power x (₁₊ k')) ⟩
    M x • M (x ^' ₁₊ k') ≈⟨ axiom (M-mul x (x ^' ₁₊ k')) ⟩
    M (x *' (x ^' ₁₊ k')) ≡⟨ aux-Mx=Mx' (x *' (x ^' ₁₊ k')) (x ^' ₂₊ k') auto ⟩
    M (x ^' ₂₊ k') ∎
    where
    open SR word-setoid


  open SR word-setoid
  open Pattern-Assoc

  lemma-semi-MS^k : ∀ x k -> (nz : x ≢ ₀) -> let x⁻¹ = ((x , nz) ⁻¹) .proj₁ in let -x⁻¹ = - x⁻¹ in
    M (x , nz) • S ^ k ≈ S ^ (k Nat.* toℕ (x * x)) • M (x , nz)
  lemma-semi-MS^k x k@0 nz = trans right-unit (sym left-unit)
  lemma-semi-MS^k x k@1 nz = begin  
    M (x , nz) • S ^ k ≈⟨ refl ⟩
    M (x , nz) • S ≈⟨ axiom (semi-MS (x , nz)) ⟩
    S^ (x * x) • M (x , nz) ≈⟨ refl ⟩
    S ^ toℕ (x * x) • M (x , nz) ≈⟨ (cleft refl' (Eq.cong (S ^_) (Eq.sym ( NP.*-identityˡ (toℕ (x * x)))))) ⟩
    S ^ (k Nat.* toℕ (x * x)) • M (x , nz) ∎
  lemma-semi-MS^k x k@(₂₊ k') nz = begin  
    M (x , nz) • S ^ k ≈⟨ refl ⟩
    M (x , nz) • S • S ^ ₁₊ k' ≈⟨ sym assoc ⟩
    (M (x , nz) • S) • S ^ ₁₊ k' ≈⟨ (cleft lemma-semi-MS^k x 1 nz) ⟩
    (S ^ (1 Nat.* toℕ (x * x)) • M (x , nz)) • S ^ ₁₊ k' ≈⟨ assoc ⟩
    S ^ (1 Nat.* toℕ (x * x)) • M (x , nz) • S ^ ₁₊ k' ≈⟨ (cright lemma-semi-MS^k x (₁₊ k') nz) ⟩
    S ^ (1 Nat.* toℕ (x * x)) • S ^ (₁₊ k' Nat.* toℕ (x * x)) • M (x , nz) ≈⟨ sym assoc ⟩
    (S ^ (1 Nat.* toℕ (x * x)) • S ^ (₁₊ k' Nat.* toℕ (x * x))) • M (x , nz) ≈⟨ (cleft sym (lemma-^-+ S ((1 Nat.* toℕ (x * x))) ((₁₊ k' Nat.* toℕ (x * x))))) ⟩
    (S ^ ((1 Nat.* toℕ (x * x)) Nat.+ (₁₊ k' Nat.* toℕ (x * x)))) • M (x , nz) ≈⟨ (cleft refl' (Eq.cong (S ^_) (Eq.sym (NP.*-distribʳ-+ (toℕ (x * x)) ₁ (₁₊ k'))))) ⟩
    S ^ ((1 Nat.+ ₁₊ k') Nat.* toℕ (x * x) ) • M (x , nz) ≈⟨ refl ⟩
    S ^ (k Nat.* toℕ (x * x)) • M (x , nz) ∎


  lemma-[H⁻¹S⁻¹]^3 : (H⁻¹ • S⁻¹) ^ 3 ≈ ε
  lemma-[H⁻¹S⁻¹]^3 = begin
    (H⁻¹ • S⁻¹) ^ 3 ≈⟨ _≈_.sym assoc ⟩
    (H⁻¹ • S⁻¹) WB.^' 3 ≈⟨ lemma-cong-inv (axiom order-SH) ⟩
    winv ε ≈⟨ refl ⟩
    ε ∎
    where
    open Group-Lemmas _ _ grouplike renaming (_⁻¹ to winv)


  lemma-[S⁻¹H⁻¹]^3 : (S⁻¹ • H⁻¹) ^ 3 ≈ ε
  lemma-[S⁻¹H⁻¹]^3 = begin
    (S⁻¹ • H⁻¹) ^ 3 ≈⟨ sym (trans (cright lemma-left-inverse) right-unit) ⟩
    (S⁻¹ • H⁻¹) ^ 3 • (S⁻¹ • S) ≈⟨ special-assoc ((□ • □) ^ 3 • □ • □) (□ • (□ • □) ^ 3 • □) auto ⟩
    S⁻¹ • (H⁻¹ • S⁻¹) ^ 3 • S ≈⟨ cright cleft lemma-[H⁻¹S⁻¹]^3 ⟩
    S⁻¹ • ε • S ≈⟨ by-assoc auto ⟩
    S⁻¹ • S ≈⟨ lemma-left-inverse ⟩
    ε ∎
    where
    open Group-Lemmas _ _ grouplike renaming (_⁻¹ to winv)


  lemma-S⁻¹ : S⁻¹ ≈ S^ ₚ₋₁
  lemma-S⁻¹ = begin
    S⁻¹ ≈⟨ refl ⟩
    S ^ p-1 ≡⟨ Eq.cong (S ^_) (Eq.sym lemma-toℕ-ₚ₋₁) ⟩
    S ^ toℕ ₚ₋₁ ≈⟨ refl ⟩
    S^ ₚ₋₁ ∎

module Symplectic-Powers-noDerived (p-2 : ℕ) (p-prime : Prime (₂₊ p-2)) where

  open import Zp.ModularArithmetic
  open PrimeModulus p-2 p-prime hiding (p)
  open Symplectic p-2 p-prime 

  -- This module provides a rewrite system for reducing powers of
  -- Symplectic operators (for example, S⁴ → I). It also commutes
  -- generators on different qubits (for example, H1 H0 → H0 H1).
  -- Finally, it moves scalars to the end of the word. While this is
  -- not yet a very powerful rewrite system, it is a useful
  -- bootstrapping step.

  open Rewriting
  
  open PB _===_ hiding (_===_)
  open PP _===_ 

  -- ----------------------------------------------------------------------
  -- * Lemmas

  -- The following lemmas are needed to justify the rewrite steps.

  -- ----------------------------------------------------------------------
  -- * Rewrite rules for monoidal structure and order of generators

  step-order : Step-Function Gen _===_

  -- Order of generators.
  step-order (H-gen ∷ H-gen ∷ H-gen ∷ H-gen ∷ xs) = just (xs , at-head (axiom order-H))
  step-order (S-gen ∷ H-gen ∷ S-gen ∷ H-gen ∷ S-gen ∷ H-gen ∷ xs) = just (xs , at-head (axiom order-SH))

  -- Commuting of generators.

  -- Catch-all
  step-order _ = nothing

  -- From this rewrite relation, we extract a tactic 'general-powers'.
  open Rewriting.Step (step-cong step-order) renaming (general-rewrite to general-powers) public


module Lemmas-noDerived (p-2 : ℕ) (p-prime : Prime (₂₊ p-2)) where

  open import Zp.ModularArithmetic
  open PrimeModulus p-2 p-prime hiding (p)
  open Symplectic p-2 p-prime 
  open Symplectic-Powers-noDerived p-2 p-prime 

  -- This module provides a rewrite system for reducing powers of
  -- Symplectic operators (for example, S⁴ → I). It also commutes
  -- generators on different qubits (for example, H1 H0 → H0 H1).
  -- Finally, it moves scalars to the end of the word. While this is
  -- not yet a very powerful rewrite system, it is a useful
  -- bootstrapping step.

  open Rewriting
  
  open PB _===_ hiding (_===_)
  open PP _===_ 


  lemma-HH-M-1 : let -'₁ = -' ((₁ , λ ())) in HH ≈ M -'₁
  lemma-HH-M-1 = begin
    HH ≈⟨ trans (sym right-unit) (cright sym lemma-[S⁻¹H⁻¹]^3) ⟩
    HH • (S⁻¹ • H⁻¹) ^ 3 ≈⟨ (cright lemma-^-cong (S⁻¹ • H⁻¹) (S⁻¹ • H • HH) 3 refl) ⟩
    HH • (S⁻¹ • H • HH) ^ 3 ≈⟨ refl ⟩
    HH • (S⁻¹ • H • HH) • (S⁻¹ • H • HH) • (S⁻¹ • H • HH) ≈⟨ (cright cong (cright sym assoc) (special-assoc (□ ^ 3 • □ ^ 3) (□ ^ 2 • □ ^ 2 • □ ^ 2) auto)) ⟩
    HH • (S⁻¹ • HH • H) • (S⁻¹ • H) • (HH • S⁻¹) • H • HH ≈⟨ (cright cong (sym assoc) (cright cleft word-comm 1 p-1 (trans assoc (axiom comm-HHS)))) ⟩
    HH • ((S⁻¹ • HH) • H) • (S⁻¹ • H) • (S⁻¹ • HH) • H • HH ≈⟨ (cright cong (cleft word-comm p-1 1 (sym (trans assoc (axiom comm-HHS)))) (cright assoc)) ⟩
    HH • ((HH • S⁻¹) • H) • (S⁻¹ • H) • S⁻¹ • HH • H • HH ≈⟨ (cright cright cright cright general-powers 100 auto) ⟩
    HH • ((HH • S⁻¹) • H) • (S⁻¹ • H) • S⁻¹ • H ≈⟨ special-assoc (□ • (□ ^ 2 • □) • □) (□ ^ 2 • □ ^ 2 • □) auto ⟩
    (HH • HH) • (S⁻¹ • H) • (S⁻¹ • H) • S⁻¹ • H ≈⟨ (cleft general-powers 100 auto) ⟩
    ε • (S⁻¹ • H) • (S⁻¹ • H) • S⁻¹ • H ≈⟨ left-unit ⟩
    (S⁻¹ • H) • (S⁻¹ • H) • S⁻¹ • H ≈⟨ special-assoc ((□ ^ 2) ^ 3) (□ ^ 6) auto ⟩
    S⁻¹ • H • S⁻¹ • H • S⁻¹ • H ≈⟨ cong lemma-S⁻¹ (cright cong lemma-S⁻¹ (cright (cleft lemma-S⁻¹))) ⟩
    S^ ₚ₋₁ • H • S^ ₚ₋₁ • H • S^ ₚ₋₁ • H ≡⟨ Eq.cong (\ xx -> S^ ₚ₋₁ • H • S^ ₚ₋₁ • H • S^ xx • H) p-1=-1ₚ ⟩
    S^ ₚ₋₁ • H • S^ ₚ₋₁ • H • S^ -₁ • H ≡⟨ Eq.cong₂ (\ xx yy -> S^ xx • H • S^ yy • H • S^ -₁ • H) (p-1=-1ₚ) p-1=-1ₚ ⟩
    S^ -₁ • H • S^ -₁ • H • S^ -₁ • H ≡⟨ Eq.cong (\ xx -> S^ -₁ • H • S^ xx • H • S^ -₁ • H) (Eq.sym aux-₁⁻¹) ⟩
    S^ -₁ • H • S^ -₁⁻¹ • H • S^ -₁ • H ≈⟨ refl ⟩
    S^ x • H • S^ x⁻¹ • H • S^ x • H ≡⟨ Eq.refl ⟩
    M x' ∎
    where
    open SR word-setoid
    open Pattern-Assoc
    x' = -'₁
    -₁ = -'₁ .proj₁
    -₁⁻¹ = (-'₁ ⁻¹) .proj₁
    x = x' .proj₁
    x⁻¹ = (x' ⁻¹) .proj₁




module Symℕ (p-2 : ℕ) (p-prime : Prime (₂₊ p-2)) where

  p : ℕ
  p = ₂₊ p-2
  open import Zp.ModularArithmetic
  open PrimeModulus p-2 p-prime hiding (p ; 0ₚ ; 1ₚ ; 0ₚ≢1ₚ)

  data Gen : Set where
    H-gen : ℤ ₄ -> Gen
    S-gen : ℤ ₚ -> Gen

  H^ : ℤ ₄ -> Word Gen
  H^ k = [ H-gen k ]ʷ

  S^ : ℤ ₚ -> Word Gen
  S^ k = [ S-gen k ]ʷ

  H : Word Gen
  H = [ H-gen ₁ ]ʷ

  H⁻¹ : Word Gen
  H⁻¹ = H ^ 3

  HH : Word Gen
  HH = H • H

  S : Word Gen
  S = [ S-gen ₁ ]ʷ

  S⁻¹ : Word Gen
  S⁻¹ = S ^ p-1

  S' : Word Gen
  S' = HH • S • HH

  SS : Word Gen
  SS = S • S

  X : Word Gen
  X = H • S • HH • SS • H

  Z : Word Gen
  Z = HH • S • HH • SS

  M : ℤ* ₚ -> Word Gen
  M x' = S^ x • H • S^ x⁻¹ • H • S^ x • H
    where
    x = x' .proj₁
    x⁻¹ = ((x' ⁻¹) .proj₁ )

  infixr 9 _^2
  _^2 : ℤ* ₚ -> ℤ ₚ
  _^2 x' = let x = x' .proj₁ in x * x 

  open Eq using (_≢_)
  
  infix 4 _===_
  data _===_ : WRel Gen where
    order-S : S ^ p === ε
    order-H : H ^ 4 === ε
    order-SH : (S • H) ^ 3 === ε    
    comm-HHS : H • H • S === S • H • H
    
    M-mul : ∀ (x y : ℤ* ₚ) -> M x • M y === M (x *' y)
    semi-MS : ∀ (x : ℤ* ₚ) -> M x • S === S^ (x ^2) • M x

    derived-S : ∀ (k : ℤ ₚ) -> S^ k === S ^ toℕ k
    derived-H : ∀ (k : ℤ ₄) -> H^ k === H ^ toℕ k


  open PP _===_
  open PB _===_ hiding (_===_)
  grouplike : Grouplike _===_
  grouplike (H-gen k) = (H ^ toℕ k) ^ 3 , claim
    where
    open SR word-setoid
    claim : (H ^ toℕ k) ^ 3 • H^ k ≈ ε
    claim = begin
      (H ^ toℕ k) ^ 3 • H^ k ≈⟨ (cright axiom (derived-H k)) ⟩
      (H ^ toℕ k) ^ 3 • H ^ toℕ k ≈⟨ sym (lemma-^-+ (H ^ toℕ k) 3 1) ⟩
      (H ^ toℕ k) ^ 4 ≈⟨ lemma-^^' H (toℕ k) 4 ⟩
      (H ^ 4) ^ toℕ k ≈⟨ lemma-^-cong (H ^ 4) ε (toℕ k) (axiom order-H) ⟩
      (ε) ^ toℕ k ≈⟨ lemma-ε^k=ε (toℕ k) ⟩
      ε ∎
  grouplike (S-gen k) = (S ^ toℕ k) ^ p-1 ,  claim
    where
    open SR word-setoid
    claim : (S ^ toℕ k) ^ p-1 • S^ k ≈ ε
    claim = begin
      (S ^ toℕ k) ^ p-1 • S^ k ≈⟨ (cright axiom (derived-S k)) ⟩
      (S ^ toℕ k) ^ p-1 • S ^ toℕ k ≈⟨ sym (lemma-^-+ (S ^ toℕ k) p-1 1) ⟩
      (S ^ toℕ k) ^ (p-1 Nat.+ 1) ≈⟨ lemma-^^' S (toℕ k) (p-1 Nat.+ 1) ⟩
      (S ^ (p-1 Nat.+ 1)) ^ toℕ k ≈⟨ lemma-^-cong (S ^ (p-1 Nat.+ 1)) (S ^ p) (toℕ k) (refl' (Eq.cong (S ^_) (NP.+-comm p-1 1))) ⟩
      (S ^ p) ^ toℕ k ≈⟨ lemma-^-cong (S ^ p) ε (toℕ k) (axiom order-S) ⟩
      (ε) ^ toℕ k ≈⟨ lemma-ε^k=ε (toℕ k) ⟩
      ε ∎


  open Eq using (_≢_)

  ₁⁻¹ = ((₁ , λ ()) ⁻¹) .proj₁

  M₁ = M (₁ , λ ())
  
  lemma-M1 : ε ≈ M (₁ , λ ())
  lemma-M1 = begin
    ε ≈⟨ _≈_.sym (axiom order-SH) ⟩
    (S • H) ^ 3 ≈⟨ by-assoc auto ⟩
    S • H • S • H • S • H ≡⟨ auto ⟩
    S^ ₁ • H • S^ ₁ • H • S^ ₁ • H ≡⟨ Eq.cong (\ xx -> S^ ₁ • H • S^ xx • H • S^ ₁ • H) (Eq.sym inv-₁) ⟩
    S^ ₁ • H • S^ ₁⁻¹ • H • S^ ₁ • H ≈⟨ refl ⟩
    M (₁ , λ ()) ∎
    where
    open SR word-setoid

  aux-Mx=Mx' : ∀ y y' -> y .proj₁ ≡ y' .proj₁ -> M y ≡ M y'
  aux-Mx=Mx' y y' eq = begin
    M y ≡⟨ auto ⟩
    S^ x • H • S^ x⁻¹ • H • S^ x • H ≡⟨ Eq.cong₂ (\ xx yy -> S^ xx • H • S^ yy • H • S^ x • H) eq aux-eq ⟩
    S^ x' • H • S^ x'⁻¹ • H • S^ x • H ≡⟨ Eq.cong (\ xx -> S^ x' • H • S^ x'⁻¹ • H • S^ xx • H) eq ⟩
    S^ x' • H • S^ x'⁻¹ • H • S^ x' • H ≡⟨ auto ⟩
    M y' ∎
    where
    open ≡-Reasoning
    x = y .proj₁
    x⁻¹ = ((y ⁻¹) .proj₁ )
    x' = y' .proj₁
    x'⁻¹ = ((y' ⁻¹) .proj₁ )
    aux-eq : x⁻¹ ≡ x'⁻¹
    aux-eq  = begin
      x⁻¹ ≡⟨  Eq.sym  (*-identityʳ x⁻¹) ⟩
      x⁻¹ * ₁ ≡⟨ Eq.cong (x⁻¹ *_) (Eq.sym (lemma-⁻¹ʳ x' {{nztoℕ {y = x'} {neq0 = y' .proj₂} }})) ⟩
      x⁻¹ * (x' * x'⁻¹) ≡⟨ Eq.sym (*-assoc x⁻¹ x' x'⁻¹) ⟩
      (x⁻¹ * x') * x'⁻¹ ≡⟨ Eq.cong (\ xx -> (x⁻¹ * xx) * x'⁻¹) (Eq.sym eq) ⟩
      (x⁻¹ * x) * x'⁻¹ ≡⟨ Eq.cong (_* x'⁻¹) (lemma-⁻¹ˡ x {{nztoℕ {y = x} {neq0 = y .proj₂} }}) ⟩
      ₁ * x'⁻¹ ≡⟨ *-identityˡ x'⁻¹ ⟩
      x'⁻¹ ∎



  lemma-M-power : ∀ (x : ℤ* ₚ) k -> let x' = x .proj₁ in  M x ^ k ≈ M (x ^' k)
  lemma-M-power x k@0 = lemma-M1 
  lemma-M-power x k@1 = begin
    M x ^ 1 ≡⟨ aux-Mx=Mx' x (x ^' 1) (Eq.sym (lemma-x^′1=x (x .proj₁))) ⟩
    M (x ^' 1) ∎
    where
    open SR word-setoid
  lemma-M-power x k@(₂₊ k') = begin
    M x • M x ^ ₁₊ k' ≈⟨ (cright lemma-M-power x (₁₊ k')) ⟩
    M x • M (x ^' ₁₊ k') ≈⟨ axiom (M-mul x (x ^' ₁₊ k')) ⟩
    M (x *' (x ^' ₁₊ k')) ≡⟨ aux-Mx=Mx' (x *' (x ^' ₁₊ k')) (x ^' ₂₊ k') auto ⟩
    M (x ^' ₂₊ k') ∎
    where
    open SR word-setoid


-- ----------------------------------------------------------------------
-- * Data required for applying word tactics to Symplectic generators

module CommData (p-2 : ℕ) (p-prime : Prime (₂₊ p-2)) where

  open import Zp.ModularArithmetic
  open PrimeModulus p-2 p-prime hiding (p)
  open Symℕ p-2 p-prime renaming (M to Mz)

  open PB _===_
  
  -- Commutativity.
  comm~ : (x y : Gen) -> Maybe (([ x ]ʷ • [ y ]ʷ) ≈ ([ y ]ʷ • [ x ]ʷ))
  comm~ _ _ = nothing


  -- We number the generators for the purpose of ordering them.
  ord : Gen -> ℕ
  ord (S-gen k) = 0 Nat.+ toℕ k
  ord (H-gen k) = p Nat.+ toℕ k

  -- Ordering of generators.
  les : Gen -> Gen -> Bool
  les x y with ord x Nat.<? ord y
  les x y | yes _ = true
  les x y | no _ = false

module Commuting-Symplectic (p-2 : ℕ) (p-prime : Prime (₂₊ p-2)) where
 open Commuting (Symℕ._===_ p-2 p-prime) (CommData.comm~ p-2 p-prime) (CommData.les p-2 p-prime) public

-- ----------------------------------------------------------------------
-- * Lemmas

module Symplectic-Powers (p-2 : ℕ) (p-prime : Prime (₂₊ p-2)) where

  open import Zp.ModularArithmetic
  open PrimeModulus p-2 p-prime hiding (p)
  open Symℕ p-2 p-prime renaming (M to Mz)

  -- This module provides a rewrite system for reducing powers of
  -- Symplectic operators (for example, S⁴ → I). It also commutes
  -- generators on different qubits (for example, H1 H0 → H0 H1).
  -- Finally, it moves scalars to the end of the word. While this is
  -- not yet a very powerful rewrite system, it is a useful
  -- bootstrapping step.

  open Rewriting
  
  open PB _===_ hiding (_===_)

  -- ----------------------------------------------------------------------
  -- * Lemmas

  -- The following lemmas are needed to justify the rewrite steps.

  -- ----------------------------------------------------------------------
  -- * Rewrite rules for monoidal structure and order of generators

  step-order : Step-Function Gen _===_

  -- Order of generators.
  step-order (H-gen ₁ ∷ H-gen ₁ ∷ H-gen ₁ ∷ H-gen ₁ ∷ xs) = just (xs , at-head (axiom order-H))
  step-order (S-gen ₁ ∷ H-gen ₁ ∷ S-gen ₁ ∷ H-gen ₁ ∷ S-gen ₁ ∷ H-gen ₁ ∷ xs) = just (xs , at-head (axiom order-SH))

  -- Commuting of generators.

  -- Catch-all
  step-order _ = nothing

  -- From this rewrite relation, we extract a tactic 'general-powers'.
  open Rewriting.Step (step-cong step-order) renaming (general-rewrite to general-powers) public


module Symplectic-Rewriting-HH (p-2 : ℕ) (p-prime : Prime (₂₊ p-2)) where

  open import Zp.ModularArithmetic
  open PrimeModulus p-2 p-prime hiding (p)
  open Symℕ p-2 p-prime renaming (M to Mz)

  open Rewriting
  open Symplectic-Powers

  open PB _===_ hiding (_===_)
  open PP _===_
  open SR word-setoid


  -- ----------------------------------------------------------------------
  -- * Rewrite rules for 1-qubit Symplectic relations
  
  step-symplectic1 : Step-Function Gen _===_

  -- Rules for unary gates.
  -- Order of generators.
  
  step-symplectic1 (H-gen ₁ ∷ H-gen ₁ ∷ S-gen ₁ ∷ xs) = just (S-gen ₁ ∷ H-gen ₁ ∷ H-gen ₁ ∷ xs , at-head (axiom comm-HHS))

  -- Catch-all
  step-symplectic1 _ = nothing

  -- From this rewrite relation, we extract a tactic 'rewrite-symplectic1'.
  open Rewriting.Step (step-cong (step-order p-2 p-prime) then step-cong step-symplectic1) renaming (general-rewrite to rewrite-HH) public

module Lemmas (p-2 : ℕ) (p-prime : Prime (₂₊ p-2)) where

  open import Zp.ModularArithmetic
  open PrimeModulus p-2 p-prime hiding (p)
  open Symℕ p-2 p-prime

  open Symplectic-Rewriting-HH p-2 p-prime
  open Symplectic-Powers p-2 p-prime

  open PB _===_ hiding (_===_)
  open PP _===_
  open Pattern-Assoc
  open import Data.Nat.DivMod
  open import Data.Fin.Properties

  lemma-S^k+l : ∀ k l -> S^ k • S^ l ≈ S^ (k + l)
  lemma-S^k+l k l = begin
    S^ k • S^ l ≈⟨ cong (axiom (derived-S k)) (axiom (derived-S l)) ⟩
    S ^ toℕ k • S ^ toℕ l ≈⟨ sym (lemma-^-+ S (toℕ k) (toℕ l)) ⟩
    S ^ (toℕ k Nat.+ toℕ l) ≡⟨ Eq.cong (S ^_) (m≡m%n+[m/n]*n k+l p) ⟩
    S ^ (k+l Nat.% p Nat.+ (k+l Nat./ p) Nat.* p) ≈⟨ lemma-^-+ S (k+l Nat.% p) (((k+l Nat./ p) Nat.* p)) ⟩
    S ^ (k+l Nat.% p) • S ^ ((k+l Nat./ p) Nat.* p) ≈⟨ cong (refl' (Eq.cong (S ^_) (Eq.sym (toℕ-fromℕ< (m%n<n k+l p))))) (refl' (Eq.cong (S ^_) (NP.*-comm ((k+l Nat./ p)) p))) ⟩
    S ^ toℕ (fromℕ< (m%n<n k+l p)) • S ^ (p Nat.* (k+l Nat./ p) ) ≈⟨ cong (sym (axiom (derived-S (k + l)))) (sym (lemma-^^ S p (k+l Nat./ p))) ⟩
    S^ (k + l) • (S ^ p) ^ (k+l Nat./ p) ≈⟨ cright (lemma-^-cong (S ^ p) ε (k+l Nat./ p) (axiom order-S)) ⟩
    S^ (k + l) • ε ^ (k+l Nat./ p) ≈⟨ cright lemma-ε^k=ε (k+l Nat./ p) ⟩
    S^ (k + l) • ε ≈⟨ right-unit ⟩
    S^ (k + l) ∎
    where
    k+l = toℕ k Nat.+ toℕ l
    open SR word-setoid


  lemma-S^k-k : ∀ k -> S^ k • S^ (- k) ≈ ε
  lemma-S^k-k k = begin
    S^ k • S^ (- k) ≈⟨ lemma-S^k+l k (- k) ⟩
    S^ (k + - k) ≡⟨ Eq.cong S^ (+-inverseʳ k) ⟩
    S^ ₀ ≈⟨ axiom (derived-S ₀) ⟩
    ε ∎
    where
    open SR word-setoid
    k-k = toℕ k Nat.+ toℕ (- k)

  lemma-S^-k+k : ∀ k -> S^ (- k) • S^ k ≈ ε
  lemma-S^-k+k k = begin
    S^ (- k) • S^ k ≈⟨ cong (axiom (derived-S (- k))) (axiom (derived-S k)) ⟩
    S ^ toℕ (- k) • S ^ toℕ k ≈⟨ word-comm (toℕ (- k)) (toℕ ( k)) refl ⟩
    S ^ toℕ k • S ^ toℕ (- k) ≈⟨ cong (sym (axiom (derived-S k))) (sym (axiom (derived-S (- k)))) ⟩
    S^ k • S^ (- k) ≈⟨ lemma-S^k-k k ⟩
    ε ∎
    where
    open SR word-setoid

  open Eq using (_≢_)

  -- ₁⁻¹ = ((₁ , λ ()) ⁻¹) .proj₁

  -- M₁ = M (₁ , λ ())
  
  -- lemma-M1 : ε ≈ M (₁ , λ ())
  -- lemma-M1 = begin
  --   ε ≈⟨ _≈_.sym (axiom order-SH) ⟩
  --   (S • H) ^ 3 ≈⟨ by-assoc auto ⟩
  --   S • H • S • H • S • H ≡⟨ auto ⟩
  --   S^ ₁ • H • S^ ₁ • H • S^ ₁ • H ≡⟨ Eq.cong (\ xx -> S^ ₁ • H • S^ xx • H • S^ ₁ • H) (Eq.sym inv-₁) ⟩
  --   S^ ₁ • H • S^ ₁⁻¹ • H • S^ ₁ • H ≈⟨ refl ⟩
  --   M (₁ , λ ()) ∎
  --   where
  --   open SR word-setoid


  -- lemma-M-power : ∀ (x : ℤ* ₚ) k -> let x' = x .proj₁ in  M x ^ k ≈ M (x ^' k)
  -- lemma-M-power x k@0 = {!!} 
  -- lemma-M-power x k@1 = {!!} 
  -- lemma-M-power x k@(₂₊ k') = {!!} 



  lemma-[H⁻¹S⁻¹]^3 : (H⁻¹ • S⁻¹) ^ 3 ≈ ε
  lemma-[H⁻¹S⁻¹]^3 = begin
    (H⁻¹ • S⁻¹) ^ 3 ≈⟨ _≈_.sym assoc ⟩
    (H⁻¹ • S⁻¹) WB.^' 3 ≈⟨ lemma-cong-inv (axiom order-SH) ⟩
    winv ε ≈⟨ refl ⟩
    ε ∎
    where
    open Group-Lemmas _ _ grouplike renaming (_⁻¹ to winv)
    open SR word-setoid

  lemma-[S⁻¹H⁻¹]^3 : (S⁻¹ • H⁻¹) ^ 3 ≈ ε
  lemma-[S⁻¹H⁻¹]^3 = begin
    (S⁻¹ • H⁻¹) ^ 3 ≈⟨ sym (trans (cright lemma-left-inverse) right-unit) ⟩
    (S⁻¹ • H⁻¹) ^ 3 • (S⁻¹ • S) ≈⟨ special-assoc ((□ • □) ^ 3 • □ • □) (□ • (□ • □) ^ 3 • □) auto ⟩
    S⁻¹ • (H⁻¹ • S⁻¹) ^ 3 • S ≈⟨ cright cleft lemma-[H⁻¹S⁻¹]^3 ⟩
    S⁻¹ • ε • S ≈⟨ by-assoc auto ⟩
    S⁻¹ • S ≈⟨ lemma-left-inverse ⟩
    ε ∎
    where
    open Group-Lemmas _ _ grouplike renaming (_⁻¹ to winv)
    open SR word-setoid

  lemma-S⁻¹ : S⁻¹ ≈ S^ ₚ₋₁
  lemma-S⁻¹ = begin
    S⁻¹ ≈⟨ refl ⟩
    S ^ p-1 ≡⟨ Eq.cong (S ^_) (Eq.sym lemma-toℕ-ₚ₋₁) ⟩
    S ^ toℕ ₚ₋₁ ≈⟨ sym (axiom (derived-S ₚ₋₁)) ⟩
    S^ ₚ₋₁ ∎
    where
    open SR word-setoid

  lemma-HH-M-1 : let -'₁ = -' ((₁ , λ ())) in HH ≈ M -'₁
  lemma-HH-M-1 = begin
    HH ≈⟨ trans (sym right-unit) (cright sym lemma-[S⁻¹H⁻¹]^3) ⟩
    HH • (S⁻¹ • H⁻¹) ^ 3 ≈⟨ (cright lemma-^-cong (S⁻¹ • H⁻¹) (S⁻¹ • H • HH) 3 refl) ⟩
    HH • (S⁻¹ • H • HH) ^ 3 ≈⟨ refl ⟩
    HH • (S⁻¹ • H • HH) • (S⁻¹ • H • HH) • (S⁻¹ • H • HH) ≈⟨ (cright cong (cright sym assoc) (special-assoc (□ ^ 3 • □ ^ 3) (□ ^ 2 • □ ^ 2 • □ ^ 2) auto)) ⟩
    HH • (S⁻¹ • HH • H) • (S⁻¹ • H) • (HH • S⁻¹) • H • HH ≈⟨ (cright cong (sym assoc) (cright cleft word-comm 1 p-1 (trans assoc (axiom comm-HHS)))) ⟩
    HH • ((S⁻¹ • HH) • H) • (S⁻¹ • H) • (S⁻¹ • HH) • H • HH ≈⟨ (cright cong (cleft word-comm p-1 1 (sym (trans assoc (axiom comm-HHS)))) (cright assoc)) ⟩
    HH • ((HH • S⁻¹) • H) • (S⁻¹ • H) • S⁻¹ • HH • H • HH ≈⟨ (cright cright cright cright general-powers 100 auto) ⟩
    HH • ((HH • S⁻¹) • H) • (S⁻¹ • H) • S⁻¹ • H ≈⟨ special-assoc (□ • (□ ^ 2 • □) • □) (□ ^ 2 • □ ^ 2 • □) auto ⟩
    (HH • HH) • (S⁻¹ • H) • (S⁻¹ • H) • S⁻¹ • H ≈⟨ (cleft general-powers 100 auto) ⟩
    ε • (S⁻¹ • H) • (S⁻¹ • H) • S⁻¹ • H ≈⟨ left-unit ⟩
    (S⁻¹ • H) • (S⁻¹ • H) • S⁻¹ • H ≈⟨ special-assoc ((□ ^ 2) ^ 3) (□ ^ 6) auto ⟩
    S⁻¹ • H • S⁻¹ • H • S⁻¹ • H ≈⟨ cong lemma-S⁻¹ (cright cong lemma-S⁻¹ (cright (cleft lemma-S⁻¹))) ⟩
    S^ ₚ₋₁ • H • S^ ₚ₋₁ • H • S^ ₚ₋₁ • H ≡⟨ Eq.cong (\ xx -> S^ ₚ₋₁ • H • S^ ₚ₋₁ • H • S^ xx • H) p-1=-1ₚ ⟩
    S^ ₚ₋₁ • H • S^ ₚ₋₁ • H • S^ -₁ • H ≡⟨ Eq.cong₂ (\ xx yy -> S^ xx • H • S^ yy • H • S^ -₁ • H) (p-1=-1ₚ) p-1=-1ₚ ⟩
    S^ -₁ • H • S^ -₁ • H • S^ -₁ • H ≡⟨ Eq.cong (\ xx -> S^ -₁ • H • S^ xx • H • S^ -₁ • H) (Eq.sym aux-₁⁻¹) ⟩
    S^ -₁ • H • S^ -₁⁻¹ • H • S^ -₁ • H ≈⟨ refl ⟩
    S^ x • H • S^ x⁻¹ • H • S^ x • H ≡⟨ Eq.refl ⟩
    M x' ∎
    where

    x' = -'₁
    -₁ = -'₁ .proj₁
    -₁⁻¹ = (-'₁ ⁻¹) .proj₁
    x = x' .proj₁
    x⁻¹ = (x' ⁻¹) .proj₁
    open SR word-setoid



  derived-D : ∀ x -> (nz : x ≢ ₀) -> let x⁻¹ = ((x , nz) ⁻¹) .proj₁ in let -x⁻¹ = - x⁻¹ in
    H • S^ x • H ≈ H • S^ x • H • S^ x⁻¹ • H • H ^ 3 • S^ -x⁻¹
  derived-D  x nz = begin
    H • S^ x • H ≈⟨ (cright cright sym right-unit) ⟩
    H • S^ x • H • ε ≈⟨ cright cright cright sym (lemma-S^k-k x⁻¹) ⟩
    H • S^ x • H • S^ x⁻¹ • S^ -x⁻¹ ≈⟨ cright cright cright cright sym left-unit ⟩
    H • S^ x • H • S^ x⁻¹ • ε • S^ -x⁻¹ ≈⟨ cright cright cright cright sym (cong (axiom order-H) refl) ⟩
    H • S^ x • H • S^ x⁻¹ • H ^ 4 • S^ -x⁻¹ ≈⟨ (cright cright cright cright special-assoc (□ ^ 4 • □) (□ • □ ^ 3 • □) auto) ⟩
    H • S^ x • H • S^ x⁻¹ • H • H ^ 3 • S^ -x⁻¹ ∎
    where
    x⁻¹ = ((x , nz) ⁻¹) .proj₁
    -x⁻¹ = - x⁻¹ 
    open SR word-setoid

  derived-5 : ∀ x k -> (nz : x ≢ ₀) -> let x⁻¹ = ((x , nz) ⁻¹) .proj₁ in let -x⁻¹ = - x⁻¹ in
    M (x , nz) • S ^ k ≈ S ^ (k Nat.* toℕ (x * x)) • M (x , nz)
  derived-5 x k@0 nz = trans right-unit (sym left-unit)
  derived-5 x k@1 nz = begin  
    M (x , nz) • S ^ k ≈⟨ refl ⟩
    M (x , nz) • S ≈⟨ axiom (semi-MS (x , nz)) ⟩
    S^ (x * x) • M (x , nz) ≈⟨ cong (axiom (derived-S (x * x))) refl ⟩
    S ^ toℕ (x * x) • M (x , nz) ≈⟨ (cleft refl' (Eq.cong (S ^_) (Eq.sym ( NP.*-identityˡ (toℕ (x * x)))))) ⟩
    S ^ (k Nat.* toℕ (x * x)) • M (x , nz) ∎
    where
    open SR word-setoid
  derived-5 x k@(₂₊ k') nz = begin  
    M (x , nz) • S ^ k ≈⟨ refl ⟩
    M (x , nz) • S • S ^ ₁₊ k' ≈⟨ sym assoc ⟩
    (M (x , nz) • S) • S ^ ₁₊ k' ≈⟨ (cleft derived-5 x 1 nz) ⟩
    (S ^ (1 Nat.* toℕ (x * x)) • M (x , nz)) • S ^ ₁₊ k' ≈⟨ assoc ⟩
    S ^ (1 Nat.* toℕ (x * x)) • M (x , nz) • S ^ ₁₊ k' ≈⟨ (cright derived-5 x (₁₊ k') nz) ⟩
    S ^ (1 Nat.* toℕ (x * x)) • S ^ (₁₊ k' Nat.* toℕ (x * x)) • M (x , nz) ≈⟨ sym assoc ⟩
    (S ^ (1 Nat.* toℕ (x * x)) • S ^ (₁₊ k' Nat.* toℕ (x * x))) • M (x , nz) ≈⟨ (cleft sym (lemma-^-+ S ((1 Nat.* toℕ (x * x))) ((₁₊ k' Nat.* toℕ (x * x))))) ⟩
    (S ^ ((1 Nat.* toℕ (x * x)) Nat.+ (₁₊ k' Nat.* toℕ (x * x)))) • M (x , nz) ≈⟨ (cleft refl' (Eq.cong (S ^_) (Eq.sym (NP.*-distribʳ-+ (toℕ (x * x)) ₁ (₁₊ k'))))) ⟩
    S ^ ((1 Nat.+ ₁₊ k') Nat.* toℕ (x * x) ) • M (x , nz) ≈⟨ refl ⟩
    S ^ (k Nat.* toℕ (x * x)) • M (x , nz) ∎
    where
    open SR word-setoid

  lemma-S^k-% : ∀ k -> S ^ k ≈ S ^ (k % p)
  lemma-S^k-% k = begin
    S ^ k ≡⟨ Eq.cong (S ^_) (m≡m%n+[m/n]*n k p) ⟩
    S ^ (k Nat.% p Nat.+ k Nat./ p Nat.* p) ≈⟨ lemma-^-+ S (k Nat.% p) (k Nat./ p Nat.* p) ⟩
    S ^ (k Nat.% p) • S ^ (k Nat./ p Nat.* p) ≈⟨ (cright refl' (Eq.cong (S ^_) (NP.*-comm (k Nat./ p) p))) ⟩
    S ^ (k Nat.% p) • S ^ (p Nat.* (k Nat./ p)) ≈⟨ sym (cright lemma-^^ S p (k Nat./ p)) ⟩
    S ^ (k Nat.% p) • (S ^ p) ^ (k Nat./ p) ≈⟨ (cright lemma-^-cong (S ^ p) ε (k Nat./ p) (axiom order-S)) ⟩
    S ^ (k Nat.% p) • (ε) ^ (k Nat./ p) ≈⟨ (cright lemma-ε^k=ε (k Nat./ p)) ⟩
    S ^ (k Nat.% p) • ε ≈⟨ right-unit ⟩
    S ^ (k % p) ∎
    where
    open SR word-setoid

  lemma-MS^k : ∀ x k -> (nz : x ≢ ₀) -> let x⁻¹ = ((x , nz) ⁻¹) .proj₁ in let -x⁻¹ = - x⁻¹ in
    M (x , nz) • S^ k ≈ S^ (k * (x * x)) • M (x , nz)
  lemma-MS^k x k nz = begin 
    M (x , nz) • S^ k ≈⟨ cong refl (axiom (derived-S k)) ⟩
    M (x , nz) • S ^ toℕ k ≈⟨ derived-5 x (toℕ k) nz ⟩
    S ^ (toℕ k Nat.* toℕ (x * x)) • M (x , nz) ≈⟨ (cleft lemma-S^k-% (toℕ k Nat.* toℕ (x * x))) ⟩
    S ^ ((toℕ k Nat.* toℕ (x * x)) % p) • M (x , nz) ≈⟨ (cleft refl' (Eq.cong (S ^_) (lemma-toℕ-% k (x * x)))) ⟩
    S ^ toℕ (k * (x * x)) • M (x , nz) ≈⟨ cong (sym (axiom (derived-S (k * (x * x))))) refl ⟩
    S^ (k * (x * x)) • M (x , nz) ∎
    where
    open SR word-setoid
    x⁻¹ = ((x , nz) ⁻¹) .proj₁
    -x⁻¹ = - x⁻¹

  lemma-S^ab : ∀ (a b : ℤ ₚ) -> S ^ toℕ (a * b) ≈ S ^ (toℕ a Nat.* toℕ b)
  lemma-S^ab a b = begin
    S ^ toℕ (a * b) ≡⟨ auto ⟩
    S ^ toℕ (fromℕ< (m%n<n (toℕ a Nat.* toℕ b) p)) ≡⟨ Eq.cong (S ^_) (toℕ-fromℕ< (m%n<n (toℕ a Nat.* toℕ b) p)) ⟩
    S ^ ((toℕ a Nat.* toℕ b) % p) ≈⟨ sym right-unit ⟩
    S ^ (ab Nat.% p) • ε ≈⟨ (cright sym (lemma-ε^k=ε (ab Nat./ p))) ⟩
    S ^ (ab Nat.% p) • (ε) ^ (ab Nat./ p) ≈⟨ (cright sym (lemma-^-cong (S ^ p) ε (ab Nat./ p) (axiom order-S))) ⟩
    S ^ (ab Nat.% p) • (S ^ p) ^ (ab Nat./ p) ≈⟨ (cright lemma-^^ S p (ab Nat./ p)) ⟩
    S ^ (ab Nat.% p) • S ^ (p Nat.* (ab Nat./ p)) ≈⟨ (cright refl' (Eq.cong (S ^_) (NP.*-comm p (ab Nat./ p)))) ⟩
    S ^ (ab Nat.% p) • S ^ (ab Nat./ p Nat.* p) ≈⟨ sym (lemma-^-+ S (ab Nat.% p) (ab Nat./ p Nat.* p)) ⟩
    S ^ (ab Nat.% p Nat.+ ab Nat./ p Nat.* p) ≡⟨ Eq.cong (S ^_) (Eq.sym (m≡m%n+[m/n]*n ab p)) ⟩
    S ^ (toℕ a Nat.* toℕ b) ∎
    where
    ab = toℕ a Nat.* toℕ b
    open SR word-setoid


  derived-7 : ∀ x y -> (nz : x ≢ ₀) -> (nzy : y ≢ ₀) -> let -'₁ = -' ((₁ , λ ())) in let x⁻¹ = ((x , nz) ⁻¹) .proj₁ in let -x⁻¹ = - x⁻¹ in let -y/x' = (((y , nzy) *' ((x , nz) ⁻¹)) *' -'₁) in let -y/x = -y/x' .proj₁ in
  
    M (y , nzy) • H • S^ x • H ≈ S^ (-x⁻¹ * (y * y)) • M -y/x' • (H • S^ -x⁻¹)
    
  derived-7 x y nzx nzy = begin
    M (y , nzy) • H • S^ x • H ≈⟨ (cright derived-D x nzx) ⟩
    M (y , nzy) • H • S^ x • H • S^ x⁻¹ • H • H ^ 3 • S^ -x⁻¹ ≈⟨ (cright special-assoc (□ • □ • □ • □ • □ • □ • □) (□ ^ 5 • □ • □) auto) ⟩
    M (y , nzy) • (H • S^ x • H • S^ x⁻¹ • H) • H ^ 3 • S^ -x⁻¹ ≈⟨ (cright cleft sym left-unit) ⟩
    M (y , nzy) • (ε • H • S^ x • H • S^ x⁻¹ • H) • H ^ 3 • S^ -x⁻¹ ≈⟨ (cright cleft cleft sym (lemma-S^-k+k x⁻¹)) ⟩
    M (y , nzy) • ((S^ -x⁻¹ • S^ x⁻¹) • H • S^ x • H • S^ x⁻¹ • H) • H ^ 3 • S^ -x⁻¹ ≈⟨ special-assoc (□ • (□ ^ 2 • □ ^ 5) • □) (□ ^ 2 • □ ^ 6 • □) auto ⟩
    (M (y , nzy) • S^ -x⁻¹) • (S^ x⁻¹ • H • S^ x • H • S^ x⁻¹ • H) • H ^ 3 • S^ -x⁻¹ ≈⟨ (cleft (cright axiom (derived-S -x⁻¹))) ⟩
    (M (y , nzy) • S ^ toℕ -x⁻¹) • (S^ x⁻¹ • H • S^ x • H • S^ x⁻¹ • H) • H ^ 3 • S^ -x⁻¹ ≈⟨ (cleft derived-5 y (toℕ -x⁻¹) nzy) ⟩
    (S ^ (toℕ -x⁻¹ Nat.* toℕ (y * y)) • M (y , nzy)) • (S^ x⁻¹ • H • S^ x • H • S^ x⁻¹ • H) • H ^ 3 • S^ -x⁻¹ ≈⟨ special-assoc (□ ^ 2 • □ ^ 2) (□ • □ ^ 2 • □) auto ⟩
    S ^ (toℕ -x⁻¹ Nat.* toℕ (y * y)) • (M (y , nzy) • (S^ x⁻¹ • H • S^ x • H • S^ x⁻¹ • H)) • H ^ 3 • S^ -x⁻¹ ≈⟨ (cright cleft (cright (cright cright cleft refl' (Eq.cong S^ (Eq.sym (inv-involutive ((x , nz)))))))) ⟩
    S ^ (toℕ -x⁻¹ Nat.* toℕ (y * y)) • (M (y , nzy) • M ((x , nz) ⁻¹)) • H ^ 3 • S^ -x⁻¹ ≈⟨ (cright cleft axiom (M-mul (y , nzy) ((x , nz) ⁻¹))) ⟩
    S ^ (toℕ -x⁻¹ Nat.* toℕ (y * y)) • M ((y , nzy) *' ((x , nz) ⁻¹)) • H ^ 3 • S^ -x⁻¹ ≈⟨ (cright special-assoc (□ • □ ^ 3 • □) (□ ^ 3 • □ ^ 2) auto) ⟩
    S ^ (toℕ -x⁻¹ Nat.* toℕ (y * y)) • (M ((y , nzy) *' ((x , nz) ⁻¹)) • HH) • H • S^ -x⁻¹ ≈⟨ (cright cleft (cright lemma-HH-M-1)) ⟩
    S ^ (toℕ -x⁻¹ Nat.* toℕ (y * y)) • (M ((y , nzy) *' ((x , nz) ⁻¹)) • M -'₁) • H • S^ -x⁻¹ ≈⟨ (cright cleft axiom (M-mul (((y , nzy) *' ((x , nz) ⁻¹))) -'₁)) ⟩
    S ^ (toℕ -x⁻¹ Nat.* toℕ (y * y)) • (M (((y , nzy) *' ((x , nz) ⁻¹)) *' -'₁) ) • H • S^ -x⁻¹ ≈⟨ (cleft sym (lemma-S^ab -x⁻¹ (y * y))) ⟩
    S ^ toℕ (-x⁻¹ * (y * y)) • M -y/x' • (H • S^ -x⁻¹) ≈⟨ cong (sym (axiom (derived-S (-x⁻¹ * (y * y))))) refl ⟩
    S^ (-x⁻¹ * (y * y)) • M -y/x' • (H • S^ -x⁻¹) ∎
    where
    open SR word-setoid
    nz = nzx
    x⁻¹ = ((x , nz) ⁻¹) .proj₁
    x⁻¹⁻¹ = (((x , nz) ⁻¹) ⁻¹) .proj₁
    -x⁻¹ = - x⁻¹
    -y/x' = (((y , nzy) *' ((x , nz) ⁻¹)) *' -'₁)
    -y/x = -y/x' .proj₁

  aux-MM : ∀ {x y : ℤ ₚ} (nzx : x ≢ ₀) (nzy : y ≢ ₀) -> x ≡ y -> M (x , nzx) ≈ M (y , nzy)
  aux-MM {x} {y} nz1 nz2 eq rewrite eq = refl


  semi-HM : ∀ (x : ℤ* ₚ) -> H • M x ≈ M (x ⁻¹) • H
  semi-HM x' = begin
    H • (S^ x • H • S^ x⁻¹ • H • S^ x • H) ≈⟨ by-assoc auto ⟩
    (H • S^ x • H) • S^ x⁻¹ • H • S^ x • H ≈⟨ (trans (sym left-unit) (cong lemma-M1 refl)) ⟩
    M₁ • (H • S^ x • H) • S^ x⁻¹ • H • S^ x • H ≈⟨ sym assoc ⟩
    (M₁ • (H • S^ x • H)) • S^ x⁻¹ • H • S^ x • H ≈⟨ (cleft derived-7 x ₁ (x' .proj₂) λ ()) ⟩
    (S^ (-x⁻¹ * (₁ * ₁)) • M (((₁ , λ ()) *' x' ⁻¹) *' -'₁) • H • S^ -x⁻¹) • S^ x⁻¹ • H • S^ x • H ≈⟨ cleft (cright (cleft aux-MM ((((₁ , λ ()) *' x' ⁻¹) *' -'₁) .proj₂) ((-' (x' ⁻¹)) .proj₂) aux-a1)) ⟩
    (S^ (-x⁻¹ * ₁) • M (-' (x' ⁻¹)) • H • S^ -x⁻¹) • S^ x⁻¹ • H • S^ x • H ≈⟨ special-assoc (□ ^ 4 • □ ^ 4) (□ • □ ^ 4 • □ ^ 3) auto ⟩
    S^ (-x⁻¹ * ₁) • (M (-' (x' ⁻¹)) • H • S^ -x⁻¹ • S^ x⁻¹) • H • S^ x • H ≈⟨ cong (refl' (Eq.cong S^ (*-identityʳ -x⁻¹))) (cleft cright (cright lemma-S^-k+k x⁻¹)) ⟩
    S^ -x⁻¹ • (M (-' (x' ⁻¹)) • H • ε) • H • S^ x • H ≈⟨ (cright cleft (cright right-unit)) ⟩
    S^ -x⁻¹ • (M (-' (x' ⁻¹)) • H) • H • S^ x • H ≈⟨ (cright by-assoc auto) ⟩
    S^ -x⁻¹ • (M (-' (x' ⁻¹)) • H • H) • S^ x • H ≈⟨ (cright cleft cright lemma-HH-M-1) ⟩
    S^ -x⁻¹ • (M (-' (x' ⁻¹)) • M -'₁) • S^ x • H ≈⟨ (cright cleft axiom (M-mul (-' (x' ⁻¹)) -'₁)) ⟩
    S^ -x⁻¹ • M (-' (x' ⁻¹) *' -'₁) • S^ x • H ≈⟨ (cright cleft aux-MM ((-' (x' ⁻¹) *' -'₁) .proj₂) ((x' ⁻¹) .proj₂) aux-a2) ⟩
    S^ -x⁻¹ • M (x' ⁻¹) • S^ x • H ≈⟨ sym (cong refl assoc) ⟩
    S^ -x⁻¹ • (M (x' ⁻¹) • S^ x) • H ≈⟨ (cright cleft lemma-MS^k x⁻¹ x ((x' ⁻¹) .proj₂)) ⟩
    S^ -x⁻¹ • (S^ (x * (x⁻¹ * x⁻¹)) • M (x' ⁻¹)) • H ≈⟨ (cright cleft (cleft refl' (Eq.cong S^ aux-a3))) ⟩
    S^ -x⁻¹ • (S^ x⁻¹ • M (x' ⁻¹)) • H ≈⟨ by-assoc auto ⟩
    (S^ -x⁻¹ • S^ x⁻¹) • M (x' ⁻¹) • H ≈⟨ (cleft lemma-S^-k+k x⁻¹) ⟩
    ε • M (x' ⁻¹) • H ≈⟨ left-unit ⟩
    M (x' ⁻¹) • H ∎
    where
    x = x' .proj₁
    x⁻¹ = ((x' ⁻¹) .proj₁ )

    -x = - x
    -x⁻¹ = - x⁻¹
    aux-a1 : ₁ * x⁻¹ * (-'₁ .proj₁) ≡ -x⁻¹
    aux-a1 = begin
      ₁ * x⁻¹ * (-'₁ .proj₁) ≡⟨ Eq.cong (\ xx -> xx * (-'₁ .proj₁)) (*-identityˡ x⁻¹) ⟩
      x⁻¹ * (-'₁ .proj₁) ≡⟨ Eq.cong (x⁻¹ *_) (Eq.sym p-1=-1ₚ) ⟩
      x⁻¹ * ₋₁ ≡⟨ *-comm x⁻¹ ₋₁ ⟩
      ₋₁ * x⁻¹ ≡⟨ auto ⟩
      -x⁻¹ ∎
      where open ≡-Reasoning

    aux-a2 : -x⁻¹ * - ₁ ≡ x⁻¹
    aux-a2 = begin
      -x⁻¹ * - ₁ ≡⟨ *-comm -x⁻¹ (- ₁) ⟩
      - ₁ * -x⁻¹ ≡⟨ -1*x≈-x -x⁻¹ ⟩
      - -x⁻¹ ≡⟨ -‿involutive x⁻¹ ⟩
      x⁻¹ ∎
      where
      open ≡-Reasoning
      open import Algebra.Properties.Ring (+-*-ring p-2)


    aux-a3 : x * (x⁻¹ * x⁻¹) ≡ x⁻¹
    aux-a3 = begin
      x * (x⁻¹ * x⁻¹) ≡⟨ Eq.sym (*-assoc x x⁻¹ x⁻¹) ⟩
      x * x⁻¹ * x⁻¹ ≡⟨ Eq.cong (_* x⁻¹) (lemma-⁻¹ʳ x {{nztoℕ {y = x} {neq0 = x' .proj₂}}}) ⟩
      ₁ * x⁻¹ ≡⟨ *-identityˡ x⁻¹ ⟩
      x⁻¹ ∎
      where open ≡-Reasoning

    open SR word-setoid


module NF1 (p-2 : ℕ) (p-prime : Prime (₂₊ p-2)) where

  open import Zp.ModularArithmetic
  open PrimeModulus p-2 p-prime hiding (p)
  open Symℕ p-2 p-prime hiding (p) renaming (M to Mz)
  
  data C1 : Set where
    ε : C1
    HS : ℤ ₚ -> C1

  data ZMultiplier : Set where
    M : (x : ℤ* ₚ) -> ZMultiplier

  data Sᵏ : Set where
    𝕊 : ℤ ₚ -> Sᵏ

  NF1' = ℤ ₚ × ℤ* ₚ × (⊤ ⊎ ℤ ₚ)
  
  data NF1 : Set where
    _∙_∙_ : Sᵏ -> ZMultiplier -> C1 -> NF1

  ⟦_⟧₁ : C1 -> Word Gen
  ⟦ ε ⟧₁ = ε
  ⟦ HS x ⟧₁ = H • S^ x

  ⟦_⟧'₁ : ⊤ ⊎ ℤ ₚ -> Word Gen
  ⟦ inj₁ tt ⟧'₁ = ε
  ⟦ inj₂ x ⟧'₁ = H • S^ x

  ⟦_⟧↥ : Sᵏ -> Word Gen
  ⟦ 𝕊 x ⟧↥ = S^ x

  ⟦_⟧'↥ : Sᵏ -> Word Gen
  ⟦ 𝕊 x ⟧'↥ = S^ x

  ⟦_⟧ₘ : ZMultiplier -> Word Gen
  ⟦ M x' ⟧ₘ = Mz x'
    where
    x = toℕ (x' .proj₁)
    x⁻¹ = toℕ ((x' ⁻¹) .proj₁ )

  ⟦_⟧ : NF1 -> Word Gen
  ⟦ s ∙ m ∙ c ⟧ = ⟦ s ⟧↥ • ⟦ m ⟧ₘ • ⟦ c ⟧₁


  Pauli1 = ℤ ₚ × ℤ ₚ
  
  -- mod p equality
  p : ℕ
  p = (₂₊ p-2)
  𝕡 = p
  norm1 : Pauli1 → Pauli1 → ℤ ₚ
  norm1 (a , b) (c , d) = (- a) * d + c * b

  open import Algebra.Properties.Ring (+-*-ring p-2)
  
  norm1-antisym : ∀ (p q : Pauli1) -> norm1 p q ≡ - norm1 q p
  norm1-antisym p@(a , b) q@(c , d) = begin
    norm1 (a , b) (c , d) ≡⟨ auto ⟩
    (- a) * d + c * b ≡⟨ +-comm (- a * d) (c * b) ⟩
    (c * b) + - a * d ≡⟨ Eq.cong (_+ - a * d) (Eq.cong (_* b) (Eq.sym (-‿involutive c))) ⟩
    (- - c * b) + - a * d ≡⟨ Eq.cong₂ _+_ (Eq.sym (-‿distribˡ-* (- c) b)) (Eq.sym (-‿distribˡ-* a d)) ⟩
    - (- c * b) + - (a * d) ≡⟨ (-‿+-comm (- c * b) (a * d)) ⟩
    - ((- c) * b + a * d) ≡⟨ auto ⟩
    - norm1 (c , d) (a , b) ∎
    where
    open import Data.Integer.Tactic.RingSolver
    open ≡-Reasoning


  act1 : Gen → Pauli1 → Pauli1
  act1 (H-gen ₀) (a , b) = (a , b)
  act1 (H-gen ₁) (a , b) = (- b , a)
  act1 (H-gen ₂) (a , b) = (- a , - b)
  act1 (H-gen ₃) (a , b) = (b , - a)
  act1 (S-gen k) (a , b) = (a , b + a * k)

  act : Word Gen → Pauli1 → Pauli1
  act = word-act act1

  pI : Pauli1
  pI = (₀ , ₀)

  pZ : Pauli1
  pZ = (₀ , ₁)

  pX : Pauli1
  pX = (₁ , ₀)


  open Eq
  0≢1 : 0 ≢ 1
  0≢1 ()

  0≢1+n : ∀ n -> 0 ≢ ₁₊ n
  0≢1+n n ()

{-
  open import Data.Nat.DivMod using (m%n<n ; m*n%n≡0 ; m<n⇒m%n≡m)
  open import Data.Fin.Properties hiding (0≢1+n )
  open import Data.Empty
  open import Relation.Nullary.Negation.Core 
  open import Data.Integer.DivMod
  open import Data.Integer.Properties
  open import Data.Integer.Divisibility.Signed
  open import Data.Integer.Tactic.RingSolver

  +x*+x⁻¹=+1 : ∀ x' ->
    let +x = + toℕ (x' .proj₁) in
    let +x⁻¹ = + toℕ ((x' ⁻¹) .proj₁ ) in
    
    (+x * +x⁻¹) % 𝕡 ≡ ₁
  +x*+x⁻¹=+1 x' = begin
    (+x * +x⁻¹) % 𝕡 ≡⟨ auto ⟩
    (+ x * + x⁻¹) % 𝕡 ≡⟨ cong (_% 𝕡) (sym (pos-* x x⁻¹)) ⟩
    (+ (x Nat.* x⁻¹)) % 𝕡 ≡⟨ lemma-⁻¹ʳ' ( x' .proj₁) {{nztoℕ {y = x' .proj₁} {neq0 = x' .proj₂}}} ⟩
    ₁ ∎
    where
    open ≡-Reasoning
    x = toℕ (x' .proj₁)
    x⁻¹ = toℕ ((x' ⁻¹) .proj₁ )
    +x = + x
    +x⁻¹ = + x⁻¹

  +x⁻¹*+x=+1 : ∀ x' ->
    let +x = + toℕ (x' .proj₁) in
    let +x⁻¹ = + toℕ ((x' ⁻¹) .proj₁ ) in
    
    (+x⁻¹ * +x) % 𝕡 ≡ ₁
  +x⁻¹*+x=+1 x' = begin
    (+x⁻¹ * +x) % 𝕡 ≡⟨ auto ⟩
    (+ x⁻¹ * + x) % 𝕡 ≡⟨ cong (_% 𝕡) (sym (pos-* x⁻¹ x)) ⟩
    (+ (x⁻¹ Nat.* x)) % 𝕡 ≡⟨ lemma-⁻¹ˡ' ( x' .proj₁) {{nztoℕ {y = x' .proj₁} {neq0 = x' .proj₂}}} ⟩
    ₁ ∎
    where
    open ≡-Reasoning
    x = toℕ (x' .proj₁)
    x⁻¹ = toℕ ((x' ⁻¹) .proj₁ )
    +x = + x
    +x⁻¹ = + x⁻¹

-}

  lemma-HS : ∀ a b -> (neq0 : a ≢ ₀) -> let a⁻¹ = (a , neq0) ⁻¹ in let -b/a = - b * a⁻¹ .proj₁ in

    act (H • S^ -b/a) (a , b) ≡ (₀ , a)
    
  lemma-HS a b neq0 = begin
    act (H • S^ -b/a) (a , b) ≡⟨ auto ⟩
    act (H) (a , b + a * -b/a) ≡⟨ auto ⟩
    (- (b + a * -b/a) , a) ≡⟨ cong (_, a) (cong -_ aux-ba) ⟩
    (- ₀ , a) ≡⟨ cong (_, a) -0#≈0# ⟩
    (₀ , a) ∎
    where
    open ≡-Reasoning
    a⁻¹ = (a , neq0) ⁻¹
    -b/a = - b * a⁻¹ .proj₁
    aux-ba : b + a * -b/a ≡ ₀
    aux-ba = begin
      b + a * -b/a ≡⟨ cong (b +_) (cong (a *_) (*-comm (- b) (a⁻¹ .proj₁))) ⟩ -- cong (b +_) (sym (*-assoc a (- b) (a⁻¹ .proj₁))) ⟩
      b + a * (a⁻¹ .proj₁ * - b) ≡⟨ cong (b +_) (sym (*-assoc a (a⁻¹ .proj₁) (- b) )) ⟩
      b + a * a⁻¹ .proj₁ * - b ≡⟨ cong (b +_) (cong (_* - b) (lemma-⁻¹ʳ a {{nztoℕ {y = a} {neq0 = neq0}}})) ⟩
      b + 1ₚ * - b ≡⟨ cong (b +_) (*-identityˡ (- b)) ⟩
      b + - b ≡⟨  +-inverseʳ b ⟩
      ₀ ∎


  lemma-HS-x : ∀ k a b -> 

    act (H • S^ k) (a , b) ≡ (- (b + a * k) , a)
    
  lemma-HS-x a b neq0 = auto

  lemma-Mz : ∀ a b x' ->
    let x = (x' .proj₁) in
    let x⁻¹ = ((x' ⁻¹) .proj₁) in
    
    act (Mz x') (a , b) ≡ (a * x⁻¹ , b * x)
    
  lemma-Mz a b x' = begin
    act (Mz x') (a , b) ≡⟨ auto ⟩
    act (S^ x • H • S^ x⁻¹ • H • S^ x • H) (a , b) ≡⟨ auto ⟩
    act (S^ x • H • S^ x⁻¹ • H • S^ x) (- b , a) ≡⟨ auto ⟩
    act (S^ x • H • S^ x⁻¹ • H) (- b , a + (- b) * x) ≡⟨ auto ⟩
    act (S^ x • H • S^ x⁻¹) ( - (a + (- b) * x) , - b) ≡⟨ auto ⟩
    act (S^ x • H) ( - (a + (- b) * x) , - b + (- (a + (- b) * x)) * (x⁻¹)) ≡⟨ auto ⟩
    act (S^ x) ( - (- b + (- (a + (- b) * x)) * (x⁻¹)) , - (a + (- b) * x) ) ≡⟨ auto ⟩
    - (- b + - (a + - b * x) * x⁻¹) , - (a + - b * x) + - (- b + - (a + - b * x) * x⁻¹) * x ≡⟨ Eq.sym (≡×≡⇒≡ (-‿+-comm (- b) (- (a + - b * x) * x⁻¹) , Eq.cong₂ _+_ (-‿+-comm a (- b * x)) (Eq.cong (_* x) (-‿+-comm (- b) (- (a + - b * x) * x⁻¹))))) ⟩
    - - b + - ((- (a + - b * x)) * x⁻¹) , - a + - (- b * x) + (- - b + - (- (a + - b * x) * x⁻¹)) * x ≡⟨ ≡×≡⇒≡ (cong₂ _+_ (-‿involutive b) (-‿distribˡ-* ((- (a + - b * x))) x⁻¹) , cong₂ _+_ (cong (- a +_) (-‿distribˡ-* (- b) x)) (cong₂ (\ xx yy -> (xx + yy) * x) (-‿involutive b) (-‿distribˡ-* (- (a + - b * x)) x⁻¹))) ⟩
    b + - (- (a + - b * x)) * x⁻¹ , - a + - - b * x + (b + - - (a + - b * x) * x⁻¹) * x ≡⟨ ≡×≡⇒≡ (Eq.cong (\ xx -> b + xx * x⁻¹) (-‿involutive (a + - b * x)) ,  cong₂ _+_ (cong (\ xx -> - a + xx * x) (-‿involutive b)) (cong (\ xx -> (b + xx * x⁻¹) * x) (-‿involutive (a + - b * x)))) ⟩
    b + (a + - b * x) * x⁻¹ , - a + b * x + (b + (a + - b * x) * x⁻¹) * x ≡⟨ ≡×≡⇒≡ ((cong (b +_) (*-distribʳ-+ x⁻¹ a (- b * x))) , cong (\ xx -> - a + b * x + xx) (*-distribʳ-+ x b ((a + - b * x) * x⁻¹))) ⟩
    b + (a * x⁻¹ + - b * x * x⁻¹) , - a + b * x + (b * x + (a + - b * x) * x⁻¹ * x) ≡⟨ ≡×≡⇒≡ ((cong (\ xx -> b + (a * x⁻¹ + xx)) (*-assoc (- b) x x⁻¹)) , (cong (\ xx -> - a + b * x + (b * x + xx)) (*-assoc ((a + - b * x)) x⁻¹ x))) ⟩
    b + (a * x⁻¹ + - b * (x * x⁻¹)) , - a + b * x + (b * x + (a + - b * x) * (x⁻¹ * x)) ≡⟨ ≡×≡⇒≡ ((cong (\ xx -> b + (a * x⁻¹ + - b * xx)) (lemma-⁻¹ʳ x {{nztoℕ {y = x} {neq0 = x' .proj₂}}}) , (cong (\ xx -> - a + b * x + (b * x + (a + - b * x) * xx)) (lemma-⁻¹ˡ x {{nztoℕ {y = x} {neq0 = x' .proj₂}}})))) ⟩
    b + (a * x⁻¹ + - b * ₁) , - a + b * x + (b * x + (a + - b * x) * ₁) ≡⟨ ≡×≡⇒≡ ((cong (\ xx -> b + (a * x⁻¹ + xx)) (*-identityʳ (- b)) , (cong (\ xx -> - a + b * x + (b * x + xx)) (*-identityʳ (a + - b * x))))) ⟩
    b + (a * x⁻¹ + - b) , - a + b * x + (b * x + (a + - b * x)) ≡⟨ ≡×≡⇒≡ ((cong (b +_) (+-comm (a * x⁻¹) (- b))) , (cong (\ xx -> - a + b * x + xx) (+-comm (b * x) ((a + - b * x))))) ⟩
    b + (- b + a * x⁻¹) , - a + b * x + ((a + - b * x) + b * x) ≡⟨ sym (≡×≡⇒≡ ((+-assoc b (- b) (a * x⁻¹)) , (+-assoc (- a + b * x) ((a + - b * x)) (b * x)))) ⟩
    b + - b + a * x⁻¹ , - a + b * x + (a + - b * x) + b * x ≡⟨ ≡×≡⇒≡ ((cong (_+ a * x⁻¹) (+-inverseʳ b)) , (cong (_+ b * x) (+-assoc (- a) (b * x) ((a + - b * x))))) ⟩
    ₀ + a * x⁻¹ , - a + (b * x + (a + - b * x)) + b * x ≡⟨ ≡×≡⇒≡ ((+-identityˡ (a * x⁻¹)) , cong (\ xx -> - a + (b * x + xx) + b * x) (+-comm a (- b * x))) ⟩
    a * x⁻¹ , - a + (b * x + (- b * x + a)) + b * x ≡⟨ cong (\ xx -> a * x⁻¹ , - a + xx + b * x) (sym (+-assoc (b * x) (- b * x) a)) ⟩
    a * x⁻¹ , - a + (b * x + - b * x + a) + b * x ≡⟨ cong (\ xx -> a * x⁻¹ , - a + (b * x + xx + a) + b * x) (sym (-‿distribˡ-* b x)) ⟩
    a * x⁻¹ , - a + (b * x + - (b * x) + a) + b * x ≡⟨ cong (\ xx -> a * x⁻¹ , - a + (xx + a) + b * x) (+-inverseʳ (b * x)) ⟩
    a * x⁻¹ , - a + (₀ + a) + b * x ≡⟨ cong (\ xx -> a * x⁻¹ , - a + xx + b * x) (+-identityˡ a) ⟩
    a * x⁻¹ , - a + a + b * x ≡⟨ cong (\ xx -> a * x⁻¹ , xx + b * x) (+-inverseˡ a) ⟩
    a * x⁻¹ , ₀ + b * x ≡⟨ cong (\ xx -> a * x⁻¹ , xx) (+-identityˡ (b * x)) ⟩
    a * x⁻¹ , b * x ∎
    where
    open ≡-Reasoning
    x = (x' .proj₁)
    x⁻¹ = ((x' ⁻¹) .proj₁ )


  norm-pI-q=0 : ∀ (p : Pauli1) -> norm1 pI p ≡ ₀
  norm-pI-q=0 (c , d) = begin
    norm1 pI (c , d) ≡⟨ auto ⟩
    (- ₀) * d + c * ₀ ≡⟨ cong₂ _+_ (cong (_* d) -0#≈0#) (*-comm c ₀) ⟩
    ₀ * d + ₀ * c ≡⟨ auto ⟩
    ₀ ∎
    where open ≡-Reasoning

  norm-0b : ∀ b c d -> norm1 (₀ , b) (c , d) ≡ b * c
  norm-0b b c d = begin
    norm1 (₀ , b) (c , d) ≡⟨ auto ⟩
    (- ₀) * d + c * b ≡⟨ cong (\ xx -> xx * d + c * b) -0#≈0# ⟩
    ₀ * d + c * b ≡⟨ auto ⟩
    ₀ + c * b ≡⟨ +-identityˡ (c * b) ⟩
    c * b ≡⟨ *-comm c b ⟩
    b * c ∎
    where open ≡-Reasoning

  aux3 : ∀ (k c q : ℤ ₚ) -> k * q * c ≡ (k * c) * q
  aux3 k c q = begin
    (k * q) * c ≡⟨ (*-assoc k q c) ⟩
    k * (q * c) ≡⟨ cong (k *_) (*-comm q c) ⟩
    k * (c * q) ≡⟨ sym (*-assoc k c q) ⟩
    (k * c) * q ∎
    where
    open ≡-Reasoning
    open Sol p-2 renaming (solve to sol)

  aux4 : ∀ b k c p -> b ≡ k * p -> b * c ≡ (k * c) * p
  aux4 b k c p eq = begin
    b * c ≡⟨ cong (_* c) eq ⟩
    k * p * c ≡⟨ aux3 k c p ⟩
    (k * c) * p ∎
    where open ≡-Reasoning

{-
  aux6 : ∀ k p-2 -> let p = (₂₊ p-2) in (k * p) % p ≡ 0
  aux6 (+_ ₀) p-2 = auto
  aux6 +[1+ n ] p-2 = let p = + (₂₊ p-2) in m*n%n≡0 (₁₊ n)  ∣ p ∣
  aux6 k@(-[1+ n ]) p-2 with ((Nat.suc n) Nat.* (₂₊ p-2)) Nat.% (₂₊ p-2) | inspect ( Nat._% (₂₊ p-2)) ((Nat.suc n) Nat.* (₂₊ p-2))
  ... | ₀ | [ eqh ]' = auto
  ... | ₁₊ hyp | [ eqh ]' with 0≢1+n hyp (trans (Eq.sym (m*n%n≡0 ((Nat.suc n) ) ((₂₊ p-2)))) eqh)
  ... | ()
-}


  Theorem-NF1 :

    ∀ (p q : Pauli1) ->
    norm1 p q ≡ ₁ ->
    -------------------------------
    ∃ \ nf -> act ⟦ nf ⟧ p ≡ pZ ×
              act ⟦ nf ⟧ q ≡ pX

  Theorem-NF1 p@((₀ , ₀)) q@(q1) eq with 0ₚ≢1ₚ (Eq.trans (Eq.sym (norm-pI-q=0 q)) (eq))
  ... | ()


  Theorem-NF1 p@(₀ , b@(₁₊ b')) q@(c , d) eq = nf , claim1 , claim2
    where
    open ≡-Reasoning
    -b = - b

    -bnz : - b ≢ 0ₚ
    -bnz = (-' (b , λ ())) .proj₂

    b⁻¹ = (b , λ ()) ⁻¹
    -b⁻¹ = -' b⁻¹

    x⁻¹ = _⁻¹ b⁻¹ .proj₁
    x = b⁻¹ .proj₁

    -dx = - (d * x)

    nf = 𝕊 -dx ∙ M b⁻¹ ∙ ε
    claim1 : act ⟦ nf ⟧ p ≡ pZ
    claim1 = begin
      act ⟦ nf ⟧ p ≡⟨ auto ⟩
      act (S^ -dx • (S^ x • H • S^ x⁻¹ • H • S^ x • H) • ε) p ≡⟨ auto ⟩
      act (S^ -dx • (S^ x • H • S^ x⁻¹ • H • S^ x • H)) p ≡⟨ auto ⟩
      act (S^ -dx • (S^ x • H • S^ x⁻¹ • H • S^ x • H)) p ≡⟨ auto ⟩
      act (S^ -dx) (act (S^ x • H • S^ x⁻¹ • H • S^ x • H) p) ≡⟨ cong (act (S^ -dx)) (lemma-Mz (p .proj₁) (p .proj₂) b⁻¹) ⟩
      act (S^ -dx) (₀ * x⁻¹ , b * x ) ≡⟨ cong (\ xx -> act (S^ -dx) (₀ , xx )) (*-comm b x) ⟩
      act (S^ -dx) (₀ , x * b ) ≡⟨ cong (\ xx -> act (S^ -dx) (₀ , xx)) (lemma-⁻¹ˡ b {{nztoℕ {y = b} {neq0 = λ ()}}}) ⟩
      pZ ∎

    cb=1 : c * b ≡ 1ₚ
    cb=1 = begin
      c * b ≡⟨ *-comm c b ⟩
      b * c ≡⟨ sym (norm-0b b c d) ⟩
      norm1 p q ≡⟨ eq ⟩
      1ₚ ∎
      
    claim2 : act ⟦ nf ⟧ q ≡ pX
    claim2 = begin
      act ⟦ nf ⟧ q ≡⟨ cong (act (S^ -dx)) (lemma-Mz c d b⁻¹) ⟩
      act (S^ -dx) (c * x⁻¹ , d * x ) ≡⟨ cong (\ xx -> act (S^ -dx) (c * xx , d * x )) (inv-involutive ((b , λ ()))) ⟩
      act (S^ -dx) (c * b , d * x ) ≡⟨ cong (\ xx -> act (S^ -dx) (xx , d * x )) cb=1 ⟩
      act (S^ -dx) (1ₚ , d * x ) ≡⟨ auto ⟩
      (1ₚ , d * x + 1ₚ * -dx) ≡⟨ cong (\ xx -> 1ₚ , d * x + xx) (*-identityˡ -dx) ⟩
      (1ₚ , d * x + -dx) ≡⟨  cong (\ xx -> 1ₚ , xx) (+-inverseʳ (d * x)) ⟩
      pX ∎

  Theorem-NF1 p@(a@(₁₊ _) , b) q@(c , d) eq = nf , (claim1 , claim2)
    where
    open ≡-Reasoning
    
    a⁻¹ = (a , λ ()) ⁻¹
    1/a = a⁻¹ .proj₁
    -b/a = - b * 1/a
    x = 1/a
    x⁻¹ = (a⁻¹ ⁻¹) .proj₁
    -c/a = - c * 1/a

    nf = 𝕊 -c/a ∙ M a⁻¹ ∙ HS -b/a
    p' = act (H • S^ -b/a) p
    
    claim1 : act ⟦ nf ⟧ p ≡ pZ
    claim1 = begin
      act ⟦ nf ⟧ p ≡⟨ auto ⟩
      act (S^ -c/a • (S^ x • H • S^ x⁻¹ • H • S^ x • H) • (H • S^ -b/a)) p ≡⟨ auto ⟩
      act (S^ -c/a • (S^ x • H • S^ x⁻¹ • H • S^ x • H)) p' ≡⟨ auto ⟩
      act (S^ -c/a • (S^ x • H • S^ x⁻¹ • H • S^ x • H)) p' ≡⟨ auto ⟩
      act (S^ -c/a) (act (S^ x • H • S^ x⁻¹ • H • S^ x • H) p') ≡⟨ cong (\ xx -> act (S^ -c/a) (act (S^ x • H • S^ x⁻¹ • H • S^ x • H) xx)) (lemma-HS a b (λ ())) ⟩
      act (S^ -c/a) (act (S^ x • H • S^ x⁻¹ • H • S^ x • H) (₀ , a)) ≡⟨ cong (act (S^ -c/a)) (lemma-Mz (₀) (a) a⁻¹) ⟩
      act (S^ -c/a) (₀ * x⁻¹ , a * x ) ≡⟨ cong (\ xx -> act (S^ -c/a) (₀ , xx )) (lemma-⁻¹ʳ a {{nztoℕ {y = a} {neq0 = λ ()}}}) ⟩
      act (S^ -c/a) (₀ , ₁ ) ≡⟨ auto ⟩
      act (S^ -c/a) (₀ , ₁ + ₀ * -c/a ) ≡⟨ auto ⟩
      pZ ∎

    q' = act (H • S^ -b/a) q

    aux-dca : - (d + c * -b/a) * a ≡ ₁
    aux-dca = begin
      - (d + c * -b/a) * a ≡⟨ cong (_* a) (sym (-‿+-comm d (c * -b/a))) ⟩
      (- d + -(c * -b/a)) * a ≡⟨ cong (\ xx -> (- d + xx) * a ) (-‿distribˡ-* c -b/a) ⟩
      (- d + - c * -b/a) * a ≡⟨ *-distribʳ-+ a (- d) (- c * -b/a) ⟩
      - d * a + - c * -b/a * a ≡⟨ auto ⟩
      - d * a + - c * (- b * 1/a) * a ≡⟨ cong (\ xx -> - d * a + xx) (*-assoc (- c) (- b * 1/a) a) ⟩
      - d * a + - c * ((- b * 1/a) * a) ≡⟨  cong (\ xx -> - d * a + - c * xx) (*-assoc (- b) 1/a a) ⟩
      - d * a + - c * (- b * (1/a * a)) ≡⟨ cong (\ xx -> - d * a + - c * (- b * xx)) (lemma-⁻¹ˡ a {{nztoℕ {y = a} {neq0 = λ ()}}}) ⟩
      - d * a + - c * (- b * ₁) ≡⟨ cong (\ xx -> - d * a + - c * (xx)) (*-identityʳ (- b)) ⟩
      - d * a + - c * - b ≡⟨ cong (\ xx -> - d * a + xx) (sym (-‿distribʳ-* (- c) b)) ⟩
      - d * a + - (- c * b) ≡⟨ cong (\ xx -> - d * a + - xx) (sym (-‿distribˡ-* (c) b)) ⟩
      - d * a + - - (c * b) ≡⟨ cong₂ _+_ (*-comm (- d) a) (-‿involutive (c * b)) ⟩
      a * - d + (c * b) ≡⟨ cong (_+ (c * b)) (trans (sym (-‿distribʳ-* a d)) ((-‿distribˡ-* a d))) ⟩
      - a * d + (c * b) ≡⟨ eq ⟩
      ₁ ∎

    aux-dx : c * x + ₁ * -c/a ≡ ₀
    aux-dx = begin
      c * x + ₁ * -c/a ≡⟨ auto ⟩
      c * 1/a + ₁ * -c/a ≡⟨ cong (c * 1/a +_) (*-identityˡ -c/a) ⟩
      c * 1/a + -c/a ≡⟨ sym (*-distribʳ-+ 1/a c (- c)) ⟩
      (c + - c) * 1/a ≡⟨ cong (_* 1/a) (+-inverseʳ c) ⟩
      ₀ * 1/a ≡⟨ auto ⟩
      ₀ ∎

    claim2 : act ⟦ nf ⟧ q ≡ pX
    claim2 = begin
      act ⟦ nf ⟧ q ≡⟨ auto ⟩
      act (S^ -c/a • (S^ x • H • S^ x⁻¹ • H • S^ x • H)) (- (d + c * -b/a) , c) ≡⟨ cong (act (S^ -c/a)) (lemma-Mz (- (d + c * -b/a)) c a⁻¹) ⟩
      act (S^ -c/a) (- (d + c * -b/a) * x⁻¹ , c * x ) ≡⟨ cong (\ xx -> act (S^ -c/a) (- (d + c * -b/a) * xx , c * x )) (inv-involutive (a , (λ ()))) ⟩
      act (S^ -c/a) (- (d + c * -b/a) * a , c * x ) ≡⟨ cong (\ xx -> act (S^ -c/a) (xx , c * x )) aux-dca ⟩
      act (S^ -c/a) (₁ , c * x ) ≡⟨ auto ⟩
      (₁ , c * x + ₁ * -c/a ) ≡⟨ cong (₁ ,_) aux-dx ⟩
      pX ∎



  sbform = norm1

  Theorem-NF1' :

    ∀ (p q : Pauli1) -> sbform p q ≡ ₁ ->
    --------------------------------------
    ∃ \ nf -> act ⟦ nf ⟧ p ≡ pZ ×
              act ⟦ nf ⟧ q ≡ pX

  Theorem-NF1' = Theorem-NF1
