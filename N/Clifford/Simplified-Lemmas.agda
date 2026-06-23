{-# OPTIONS --termination-depth=20 #-}
{-# OPTIONS --inversion-max-depth=1000 #-}

------------------------------------------------------------------------
-- Re-derivation of the Clifford conjugation base-lemma subtree for the
-- *Simplified* presentation (route (B): fully machine-checked).
-- Every proof uses only the NON-selinger (shared) axioms, whose
-- constructor names are identical in both presentations, so the proofs
-- copy verbatim — the `axiom`s resolve to the Simplified relation.
------------------------------------------------------------------------

open import Level using (0ℓ)
open import Relation.Binary.PropositionalEquality using (_≡_ ; _≢_ ; module ≡-Reasoning) renaming ([_] to [_]')
import Relation.Binary.Reasoning.Setoid as SR
import Relation.Binary.PropositionalEquality as Eq
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂ ; ∃)
open import Data.Nat hiding (_^_ ; _+_ ; _*_ ; _%_ ; _/_)
import Data.Nat as Nat
open import Data.Fin hiding (_+_ ; _-_)
open import Word.Base as WB hiding (wfoldl ; _* ; _^'_)
import Presentation.Base as PB
import Presentation.Properties as PP
open import Presentation.Construct.Base hiding (_*_)
open import Presentation.GroupLike
open import Presentation.Tactics
import Data.Nat.Properties as NP
open import Data.Nat.DivMod
open import Data.Fin.Properties using (toℕ-inject₁ ; toℕ-fromℕ ; toℕ-fromℕ<)
open import Data.Nat.Primality
open import Zp.ModularArithmetic
open import Zp.Fermats-little-theorem

module N.Clifford.Simplified-Lemmas
  (p-3 : ℕ)
  (let p-2 = suc p-3)
  (p-prime : Prime (suc (suc p-2)))
  (let open PrimeModulus' p-2 p-prime)
  (g*@(g , g≠0) : ℤ* ₚ)
  (g-gen : ∀ ((x , _) : ℤ* ₚ) -> ∃ \ (k : ℤ ₚ-₁) -> x ≡ g ^′ toℕ k )
  where

pattern ₁₊ n = suc n
pattern ₂₊ n = suc (suc n)

open Primitive-Root-Modp' g* g-gen

open import N.Clifford.Clifford-Mod-Scalar p-3 p-prime g* g-gen
open Clifford-Relations hiding
  ( _QRel,_===_ ; order-S ; order-H ; M-power ; semi-M𝑠 ; order-SH ; comm-HHSHHS
  ; comm-X-Z ; semi-M↑CZ ; semi-M↓CZ ; rel-X↑-CZ ; rel-X↓-CZ ; order-CZ
  ; comm-CZ-S↓ ; comm-CZ-S↑ ; selinger-c10 ; selinger-c11 ; selinger-c12
  ; selinger-c13 ; selinger-c14 ; selinger-c15 ; comm-H ; comm-S ; comm-CZ ; cong↑ )
open import N.Clifford.Clifford-Mod-Scalars-Simplified p-3 p-prime g* g-gen
open Simplified-Relations


-- ====================================================================
-- Lemmas1-S : copy of Clifford-Mod-Scalar.Lemmas1 (order + M machinery)
-- ====================================================================
module Lemmas1-S (n : ℕ) where

  open PB ((₁₊ n) QRel,_===_) hiding (_===_)
  open PP ((₁₊ n) QRel,_===_)
  open Pattern-Assoc
  open import Data.Nat.DivMod
  open import Data.Fin.Properties


  aux-M≡M : ∀ y y' -> y .proj₁ ≡ y' .proj₁ -> M {n = n} y ≡ M y'
  aux-M≡M y y' eq = begin
    M y ≡⟨ auto ⟩
    𝑠^ x • H • 𝑠^ x⁻¹ • H • 𝑠^ x • H ≡⟨ Eq.cong₂ (\ xx yy -> 𝑠^ xx • H • 𝑠^ yy • H • 𝑠^ x • H) eq aux-eq ⟩
    𝑠^ x' • H • 𝑠^ x'⁻¹ • H • 𝑠^ x • H ≡⟨ Eq.cong (\ xx -> 𝑠^ x' • H • 𝑠^ x'⁻¹ • H • 𝑠^ xx • H) eq ⟩
    𝑠^ x' • H • 𝑠^ x'⁻¹ • H • 𝑠^ x' • H ≡⟨ auto ⟩
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


  lemma-M1 : M (₁ , λ ()) ≈ ε
  lemma-M1 = begin
    M (₁ , λ ()) ≡⟨ aux-M≡M ((₁ , λ ())) (g^ ₀) auto ⟩
    M (g^ ₀) ≈⟨ sym (axiom (M-power ₀)) ⟩
    Mg^ ₀ ≈⟨ refl ⟩
    ε ∎
    where
    open SR word-setoid




  lemma-S⁻¹ : S⁻¹ ≈ S^ ₚ₋₁
  lemma-S⁻¹ = begin
    S⁻¹ ≈⟨ refl ⟩
    S ^ p-1 ≡⟨ Eq.cong (S ^_) (Eq.sym lemma-toℕ-ₚ₋₁) ⟩
    S ^ toℕ ₚ₋₁ ≈⟨ refl ⟩
    S^ ₚ₋₁ ∎
    where
    open SR word-setoid



  lemma-Mg𝑠^k : ∀ k ->  let g⁻¹ = (g′ ⁻¹) .proj₁ in let -g⁻¹ = - g⁻¹ in
    Mg • 𝑠 ^ k ≈ 𝑠 ^ (k Nat.* toℕ (g * g)) • Mg
  lemma-Mg𝑠^k k@0 = trans right-unit (sym left-unit)
  lemma-Mg𝑠^k k@1 = begin  
    Mg • 𝑠 ^ k ≈⟨ refl ⟩
    Mg • 𝑠 ≈⟨ axiom semi-M𝑠 ⟩
    𝑠^ (g * g) • Mg ≈⟨ refl ⟩
    𝑠 ^ toℕ (g * g) • Mg ≈⟨ (cleft refl' (Eq.cong (𝑠 ^_) (Eq.sym ( NP.*-identityˡ (toℕ (g * g)))))) ⟩
    𝑠 ^ (k Nat.* toℕ (g * g)) • Mg ∎
    where
    open SR word-setoid
  lemma-Mg𝑠^k k@(₂₊ k') = begin  
    Mg • 𝑠 ^ k ≈⟨ refl ⟩
    Mg • 𝑠 • 𝑠 ^ ₁₊ k' ≈⟨ sym assoc ⟩
    (Mg • 𝑠) • 𝑠 ^ ₁₊ k' ≈⟨ (cleft lemma-Mg𝑠^k 1 ) ⟩
    (𝑠 ^ (1 Nat.* toℕ (g * g)) • Mg) • 𝑠 ^ ₁₊ k' ≈⟨ assoc ⟩
    𝑠 ^ (1 Nat.* toℕ (g * g)) • Mg • 𝑠 ^ ₁₊ k' ≈⟨ (cright lemma-Mg𝑠^k (₁₊ k')) ⟩
    𝑠 ^ (1 Nat.* toℕ (g * g)) • 𝑠 ^ (₁₊ k' Nat.* toℕ (g * g)) • Mg ≈⟨ sym assoc ⟩
    (𝑠 ^ (1 Nat.* toℕ (g * g)) • 𝑠 ^ (₁₊ k' Nat.* toℕ (g * g))) • Mg ≈⟨ (cleft sym (lemma-^-+ 𝑠 ((1 Nat.* toℕ (g * g))) ((₁₊ k' Nat.* toℕ (g * g))))) ⟩
    (𝑠 ^ ((1 Nat.* toℕ (g * g)) Nat.+ (₁₊ k' Nat.* toℕ (g * g)))) • Mg ≈⟨ (cleft refl' (Eq.cong (𝑠 ^_) (Eq.sym (NP.*-distribʳ-+ (toℕ (g * g)) ₁ (₁₊ k'))))) ⟩
    𝑠 ^ ((1 Nat.+ ₁₊ k') Nat.* toℕ (g * g) ) • Mg ≈⟨ refl ⟩
    𝑠 ^ (k Nat.* toℕ (g * g)) • Mg ∎
    where
    open SR word-setoid


  open import Data.Fin.Properties
  
  lemma-Mg^p-1=ε : Mg ^ p-1 ≈ ε
  lemma-Mg^p-1=ε = begin
    Mg ^ p-1 ≡⟨ Eq.cong (Mg ^_) (Eq.sym (toℕ-fromℕ< (NP.n<1+n p-1))) ⟩
    Mg^ (fromℕ< (NP.n<1+n p-1)) ≈⟨ axiom (M-power (₂₊ (fromℕ< _))) ⟩
    M (g^ p-1') ≡⟨ aux-M≡M (g^ p-1') ((g ^′ p-1 , lemma-g^′k≠0 p-1)) (Eq.cong (g ^′_) (toℕ-fromℕ< (NP.n<1+n p-1))) ⟩
    M (g ^′ p-1 , lemma-g^′k≠0 p-1) ≡⟨ aux-M≡M ((g ^′ p-1 , lemma-g^′k≠0 p-1)) (1ₚ , λ ()) Fermat's-little-theorem' ⟩
    M (1ₚ , λ ()) ≈⟨ sym (axiom (M-power ₀)) ⟩
    ε ∎
    where
    open SR word-setoid
    p-1' = fromℕ< (NP.n<1+n p-1)

  aux-Mg^[kp-1] : ∀ k -> Mg ^ (k Nat.* p-1) ≈ ε
  aux-Mg^[kp-1] k = begin
    Mg ^ (k Nat.* p-1) ≈⟨ refl' (Eq.cong (Mg ^_) (NP.*-comm k p-1)) ⟩
    Mg ^ (p-1 Nat.* k) ≈⟨ sym (lemma-^^ Mg p-1 k) ⟩
    (Mg ^ p-1) ^ k ≈⟨ lemma-^-cong (Mg ^ p-1) ε k lemma-Mg^p-1=ε ⟩
    ε ^ k ≈⟨ lemma-ε^k=ε k ⟩
    ε ∎
    where
    open SR word-setoid

  lemma-M-mul : ∀ x y -> M x • M y ≈ M (x *' y)
  lemma-M-mul x y = begin
    M x • M y ≈⟨ cong (refl' (aux-M≡M x (g^ k) eqk)) (refl' (aux-M≡M y (g^ l) eql)) ⟩
    M (g^ k) • M (g^ l) ≈⟨ cong (sym (axiom (M-power k))) (sym (axiom (M-power l))) ⟩
    Mg ^ toℕ k • Mg ^ toℕ l ≈⟨ sym (lemma-^-+ Mg (toℕ k) (toℕ l)) ⟩
    Mg ^ [k+l] ≡⟨ Eq.cong (Mg ^_) (m≡m%n+[m/n]*n [k+l] p-1) ⟩
    Mg ^ ([k+l]%p-1 Nat.+ [k+l]/p-1 Nat.* p-1) ≈⟨ lemma-^-+ Mg [k+l]%p-1 (([k+l]/p-1 Nat.* p-1)) ⟩
    Mg ^ [k+l]%p-1 • Mg ^ ([k+l]/p-1 Nat.* p-1) ≈⟨ (cright trans refl (aux-Mg^[kp-1] [k+l]/p-1)) ⟩
    Mg ^ [k+l]%p-1 • ε ≈⟨ right-unit ⟩
    Mg ^ [k+l]%p-1 ≡⟨ Eq.cong (Mg ^_) (Eq.sym (toℕ-fromℕ< (m%n<n [k+l] p-1))) ⟩
    Mg ^ toℕ ( (fromℕ< (m%n<n [k+l] p-1))) ≡⟨ Eq.cong (Mg ^_) (Eq.sym (toℕ-inject₁ ((fromℕ< (m%n<n [k+l] p-1))))) ⟩
    Mg ^ toℕ (inject₁ (fromℕ< (m%n<n [k+l] p-1))) ≈⟨ refl ⟩
    Mg^ (inject₁ (fromℕ< (m%n<n [k+l] p-1))) ≈⟨ axiom (M-power (inject₁ (fromℕ< (m%n<n [k+l] p-1)))) ⟩
    M (g^ (inject₁ (fromℕ< (m%n<n [k+l] p-1)))) ≡⟨ aux-M≡M (g^ (inject₁ (fromℕ< (m%n<n [k+l] p-1)))) (g^′ [k+l]) aux-2 ⟩
    M (g^′ [k+l]) ≡⟨ aux-M≡M (g^′ [k+l]) (g^′ toℕ k *' g^′ toℕ l) aux-1 ⟩
    M (g^′ toℕ k *' g^′ toℕ l) ≡⟨ aux-M≡M (g^′ toℕ k *' g^′ toℕ l) (x *' y) aux-0 ⟩
    M (x *' y) ∎
    where
    k = inject₁ (g-gen x .proj₁)
    l = inject₁ (g-gen y .proj₁)
    eqk : x .proj₁ ≡ (g^ k) .proj₁
    eqk = Eq.sym (lemma-log-inject x)
    eql : y .proj₁ ≡ (g^ l) .proj₁
    eql = Eq.sym (lemma-log-inject y)

    [k+l] = toℕ k Nat.+ toℕ l
    [k+l]%p-1 = [k+l] Nat.% p-1
    [k+l]/p-1 = [k+l] Nat./ p-1

    aux-0 : ((g^′ toℕ k) *' (g^′ toℕ l)) .proj₁ ≡ (x *' y) .proj₁
    aux-0 = begin
      ((g^′ toℕ k) *' (g^′ toℕ l)) .proj₁ ≡⟨ auto ⟩
      (g^′ toℕ k) .proj₁ * (g^′ toℕ l) .proj₁ ≡⟨ Eq.cong₂ (\ xx yy -> (xx * yy) ) (lemma-log-inject x) (lemma-log-inject y) ⟩
      x .proj₁ * y .proj₁ ≡⟨ auto ⟩
      (x *' y) .proj₁ ∎
      where
      open ≡-Reasoning

    aux-1 : (g^′ [k+l]) .proj₁ ≡ ((g^′ toℕ k) *' (g^′ toℕ l)) .proj₁
    aux-1 = begin
      (g^′ [k+l]) .proj₁ ≡⟨ auto ⟩
      (g ^′ [k+l]) ≡⟨ Eq.sym (+-^′-distribʳ g (toℕ k) (toℕ l)) ⟩
      ((g ^′ toℕ k) * (g ^′ toℕ l)) ≡⟨ auto ⟩
      ((g^′ toℕ k) *' (g^′ toℕ l)) .proj₁ ∎
      where
      open ≡-Reasoning

    aux-2 : g ^′ toℕ (inject₁ (fromℕ< (m%n<n [k+l] p-1))) ≡ g ^′ (toℕ k Nat.+ toℕ l)
    aux-2 = begin
      g ^′ toℕ (inject₁ (fromℕ< (m%n<n [k+l] p-1))) ≡⟨ Eq.cong (g ^′_) (toℕ-inject₁ ((fromℕ< (m%n<n [k+l] p-1)))) ⟩
      g ^′ toℕ ( (fromℕ< (m%n<n [k+l] p-1))) ≡⟨ Eq.cong (g ^′_) (toℕ-fromℕ< ((m%n<n [k+l] p-1))) ⟩
      g ^′ [k+l]%p-1 ≡⟨ Eq.sym (aux-g^′-% [k+l]) ⟩
      g ^′ (toℕ k Nat.+ toℕ l) ∎
      where
      open ≡-Reasoning

    open SR word-setoid


  lemma-M₋₁^2 : M₋₁ ^ 2 ≈ ε
  lemma-M₋₁^2 = begin
    M₋₁ ^ 2 ≈⟨ lemma-M-mul -'₁ -'₁ ⟩
    M (-'₁ *' -'₁) ≡⟨ aux-M≡M (-'₁ *' -'₁) (₁ , (λ ())) aux-0 ⟩
    M₁ ≈⟨ sym (sym lemma-M1) ⟩
    ε ∎
    where
    open import Algebra.Properties.Ring (+-*-ring p-2)
    
    aux-0 : (-'₁ *' -'₁) .proj₁ ≡ ₁
    aux-0 = begin
      (- ₁ * - ₁) ≡⟨ -1*x≈-x (- ₁) ⟩
      (- - ₁) ≡⟨ -‿involutive ₁ ⟩
      ₁ ∎
      where
      open ≡-Reasoning
    open SR word-setoid

  lemma-order-H : H ^ 4 ≈ ε
  lemma-order-H = begin
    H ^ 4 ≈⟨ sym assoc ⟩
    HH ^ 2 ≈⟨ cong (axiom order-H) (axiom order-H) ⟩
    M₋₁ ^ 2 ≈⟨ lemma-M₋₁^2 ⟩
    ε ∎
    where
    open SR word-setoid

  lemma-comm-SHHS^kHH : ∀ k  -> S • H • H • S ^ k • H • H ≈ (H • H • S ^ k • H • H) • S
  lemma-comm-SHHS^kHH k@0 = begin
    S • H • H • ε • H • H ≈⟨ by-assoc auto ⟩
    S • H • H • H • H ≈⟨ (cright lemma-order-H) ⟩
    S • ε ≈⟨ trans right-unit (sym left-unit) ⟩
    ε • S ≈⟨ (cleft sym lemma-order-H) ⟩
    (H • H • H • H) • S ≈⟨ by-assoc auto ⟩
    (H • H • ε • H • H) • S ∎
    where
    open SR word-setoid
    open Pattern-Assoc
  lemma-comm-SHHS^kHH k@1 = sym (by-assoc-and (axiom comm-HHSHHS) auto auto)
  lemma-comm-SHHS^kHH k@(₁₊ k'@(₁₊ k'')) = begin
    S • H • H • S ^ k • H • H ≈⟨ refl ⟩
    S • H • H • (S • S ^ k') • H • H ≈⟨ (cright cright cright cleft cright sym left-unit) ⟩
    S • H • H • (S • ε • S ^ k') • H • H ≈⟨ (cright cright cright cleft cright cleft sym lemma-order-H) ⟩
    S • H • H • (S • (H • H • H • H) • S ^ k') • H • H ≈⟨ special-assoc (□ • □ • □ • (□ • □ ^ 4 • □) • □ ^ 2 ) (□ ^ 6 • □ ^ 5 ) auto ⟩
    (S • H • H • S • H • H) • H • H • S ^ k' • H • H ≈⟨ (cleft sym (axiom comm-HHSHHS)) ⟩
    (H • H • S • H • H • S) • H • H • S ^ k' • H • H ≈⟨ special-assoc (□ ^ 6 • □ ^ 5) (□ ^ 5 • □ ^ 6) auto ⟩
    (H • H • S • H • H) • S • H • H • S ^ k' • H • H ≈⟨ (cright lemma-comm-SHHS^kHH k') ⟩
    (H • H • S • H • H) • (H • H • S ^ k' • H • H) • S ≈⟨ special-assoc (□ ^ 5 • □ ^ 5 • □) (□ ^ 7 • □ ^ 4) auto ⟩
    (H • H • S • H • H • H • H) • S ^ k' • H • H • S ≈⟨ (cleft (cright cright trans (cright lemma-order-H) right-unit)) ⟩
    (H • H • S) • S ^ k' • H • H • S ≈⟨ special-assoc (□ ^ 3 • □ ^ 4) (□ • □ • □ ^ 2 • □ ^ 3) auto ⟩
    H • H • (S • S ^ k') • H • H • S ≈⟨ special-assoc (□ ^ 6) (□ ^ 5 • □) auto ⟩
    (H • H • S ^ k • H • H) • S ∎
    where
    open SR word-setoid
    open Pattern-Assoc


  lemma-Z^k-ℕ : ∀ k -> Z ^ k ≈ H • H • S ^ k • H • H • S⁻¹ ^ k
  lemma-Z^k-ℕ k@0 = sym (by-assoc-and ((lemma-order-H)) auto auto)
  lemma-Z^k-ℕ k@1 = refl
  lemma-Z^k-ℕ k@(₁₊ k'@(₁₊ k'')) = begin
    Z • Z ^ k' ≈⟨ (cright lemma-Z^k-ℕ k') ⟩
    Z • H • H • S ^ k' • H • H • S⁻¹ ^ k' ≈⟨ refl ⟩
    (H • H • S • H • H • S⁻¹) • H • H • S ^ k' • H • H • S⁻¹ ^ k' ≈⟨ special-assoc (□ ^ 6 • □ ^ 6) (□ ^ 5 • □ ^ 6 • □) auto ⟩
    (H • H • S • H • H) • (S⁻¹ • H • H • S ^ k' • H • H) • S⁻¹ ^ k' ≈⟨ (cright cleft word-comm p-1 1 (lemma-comm-SHHS^kHH k')) ⟩
    (H • H • S • H • H) • ((H • H • S ^ k' • H • H) • S⁻¹) • S⁻¹ ^ k' ≈⟨ special-assoc (□ ^ 5 • (□ ^ 5 • □) • □) (□ ^ 7 • □ ^ 3 • □ ^ 2) auto ⟩
    (H • H • S • H • H • H • H) • (S ^ k' • H • H) • S⁻¹ • S⁻¹ ^ k' ≈⟨ (cleft (cright cright trans (cright lemma-order-H) right-unit)) ⟩
    (H • H • S) • (S ^ k' • H • H) • S⁻¹ ^ ₁₊ k' ≈⟨ special-assoc (□ ^ 3 • □ ^ 3 • □) (□ ^ 2 • □ ^ 2 • □ ^ 3) auto ⟩
    (H • H) • (S • S ^ k') • H • H • S⁻¹ ^ ₁₊ k' ≈⟨ refl ⟩
    (H • H) • S ^ ₁₊ k' • H • H • S⁻¹ ^ ₁₊ k' ≈⟨ assoc ⟩
    H • H • S ^ k • H • H • S⁻¹ ^ k ∎
    where
    open SR word-setoid
    open Pattern-Assoc


  lemma-X^k-ℕ : ∀ k -> X ^ k ≈ H • S ^ k • H • H • S⁻¹ ^ k • H
  lemma-X^k-ℕ k@0 = sym (by-assoc-and lemma-order-H auto auto)
  lemma-X^k-ℕ k@1 = refl
  lemma-X^k-ℕ k@(₁₊ k'@(₁₊ k'')) = begin
    X • X ^ k' ≈⟨ (cright lemma-X^k-ℕ k') ⟩
    X • H • S ^ k' • H • H • S⁻¹ ^ k' • H ≈⟨ refl ⟩
    (H • S • H • H • S⁻¹ • H) • H • S ^ k' • H • H • S⁻¹ ^ k' • H ≈⟨ special-assoc (□ ^ 6 • □ ^ 6) (□ ^ 4 • □ ^ 6 • □ ^ 2) auto ⟩
    (H • S • H • H) • (S⁻¹ • H • H • S ^ k' • H • H) • S⁻¹ ^ k' • H ≈⟨ (cright cleft word-comm p-1 1 (lemma-comm-SHHS^kHH k')) ⟩
    (H • S • H • H) • ((H • H • S ^ k' • H • H) • S⁻¹) • S⁻¹ ^ k' • H ≈⟨ special-assoc (□ ^ 4 • (□ ^ 5 • □) • □ ^ 2) (□ ^ 6 • □ ^ 3 • □ ^ 2 • □) auto ⟩
    (H • S • H • H • H • H) • (S ^ k' • H • H) • (S⁻¹ • S⁻¹ ^ k') • H ≈⟨ (cleft (cright trans (cright lemma-order-H) right-unit)) ⟩
    (H • S) • (S ^ k' • H • H) • S⁻¹ ^ k • H ≈⟨ special-assoc (□ ^ 2 • □ ^ 3 • □ ^ 2) (□ • □ ^ 2 • □ ^ 4) auto ⟩
    H • (S • S ^ k') • H • H • S⁻¹ ^ k • H ≈⟨ refl ⟩
    H • S ^ k • H • H • S⁻¹ ^ k • H ∎
    where
    open SR word-setoid
    open Pattern-Assoc


  lemma-order-w^k : ∀ (w : Word (Gen (₁₊ n))) o k -> w ^ o ≈ ε -> (w ^ k) ^ o ≈ ε
  lemma-order-w^k w o k eq = begin
    (w ^ k) ^ o ≈⟨ lemma-^^' w k o ⟩
    (w ^ o) ^ k ≈⟨ lemma-^-cong (w ^ o) ε k eq ⟩
    ε ^ k ≈⟨ lemma-ε^k=ε k ⟩
    ε ∎
    where
    open SR word-setoid
    open Pattern-Assoc


  lemma-order-Z : Z ^ p ≈ ε
  lemma-order-Z = begin
    Z ^ p ≈⟨ lemma-Z^k-ℕ p ⟩
    H • H • S ^ p • H • H • S⁻¹ ^ p ≈⟨ (cright cright cong (axiom order-S) (cright cright lemma-order-w^k S p p-1 (axiom order-S))) ⟩
    H • H • ε • H • H • ε ≈⟨ by-assoc auto ⟩
    H • H • H • H ≈⟨ lemma-order-H ⟩
    ε ∎
    where
    open SR word-setoid
    open Pattern-Assoc


  lemma-order-X : X ^ p ≈ ε
  lemma-order-X = begin
    X ^ p ≈⟨ lemma-X^k-ℕ p ⟩
    H • S ^ p • H • H • S⁻¹ ^ p • H ≈⟨ (cright  cong (axiom order-S) (cright cright cleft lemma-order-w^k S p p-1 (axiom order-S))) ⟩
    H • ε • H • H • ε • H ≈⟨ by-assoc auto ⟩
    H • H • H • H ≈⟨ lemma-order-H ⟩
    ε ∎
    where
    open SR word-setoid
    open Pattern-Assoc


  lemma-comm-Z-S : Z • S ≈ S • Z
  lemma-comm-Z-S = begin
    (H • H • S • H • H • S⁻¹) • S ≈⟨ special-assoc (□ ^ 6 • □) (□ ^ 5 • □ ^ 2 ) auto ⟩
    (H • H • S • H • H) • S⁻¹ • S ≈⟨ (cright word-comm p-1 1 refl) ⟩
    (H • H • S • H • H) • S • S⁻¹ ≈⟨ sym (special-assoc (□ ^ 6 • □) (□ ^ 5 • □ ^ 2 ) auto) ⟩
    (H • H • S • H • H • S) • S⁻¹ ≈⟨ (cleft axiom comm-HHSHHS) ⟩
    (S • H • H • S • H • H) • S⁻¹ ≈⟨ special-assoc (□ ^ 6 • □) (□ • □ ^ 6) auto ⟩
    S • (H • H • S • H • H • S⁻¹) ≈⟨ refl ⟩
    S • Z ∎
    where
    open SR word-setoid
    open Pattern-Assoc
  
  lemma-order-𝑠 : 𝑠 ^ p ≈ ε
  lemma-order-𝑠 = begin
    (S • Z^ 1/2) ^ p ≈⟨ lemma-^-cong (S • Z^ 1/2) (Z^ 1/2 • S) p (word-comm 1 (toℕ 1/2) (sym lemma-comm-Z-S)) ⟩
    (Z^ 1/2 • S) ^ p ≈⟨ lemma-^-• (Z^ 1/2) S p (word-comm (toℕ 1/2) 1 lemma-comm-Z-S) ⟩
    Z^ 1/2 ^ p • S ^ p ≈⟨ (cright axiom order-S) ⟩
    Z^ 1/2 ^ p • ε ≈⟨ right-unit ⟩
    Z^ 1/2 ^ p ≈⟨ lemma-order-w^k Z p (toℕ 1/2) lemma-order-Z ⟩
    ε ∎
    where
    open SR word-setoid
    
  lemma-𝑠^k-% : ∀ k -> 𝑠 ^ k ≈ 𝑠 ^ (k % p)
  lemma-𝑠^k-% k = begin
    𝑠 ^ k ≡⟨ Eq.cong (𝑠 ^_) (m≡m%n+[m/n]*n k p) ⟩
    𝑠 ^ (k Nat.% p Nat.+ k Nat./ p Nat.* p) ≈⟨ lemma-^-+ 𝑠 (k Nat.% p) (k Nat./ p Nat.* p) ⟩
    𝑠 ^ (k Nat.% p) • 𝑠 ^ (k Nat./ p Nat.* p) ≈⟨ (cright refl' (Eq.cong (𝑠 ^_) (NP.*-comm (k Nat./ p) p))) ⟩
    𝑠 ^ (k Nat.% p) • 𝑠 ^ (p Nat.* (k Nat./ p)) ≈⟨ sym (cright lemma-^^ 𝑠 p (k Nat./ p)) ⟩
    𝑠 ^ (k Nat.% p) • (𝑠 ^ p) ^ (k Nat./ p) ≈⟨ (cright lemma-^-cong (𝑠 ^ p) ε (k Nat./ p) (lemma-order-𝑠)) ⟩
    𝑠 ^ (k Nat.% p) • (ε) ^ (k Nat./ p) ≈⟨ (cright lemma-ε^k=ε (k Nat./ p)) ⟩
    𝑠 ^ (k Nat.% p) • ε ≈⟨ right-unit ⟩
    𝑠 ^ (k % p) ∎
    where
    open SR word-setoid






  lemma-Mg𝑠^k' : ∀ k -> let x⁻¹ = (g′ ⁻¹) .proj₁ in let -x⁻¹ = - x⁻¹ in
    Mg • 𝑠^ k ≈ 𝑠^ (k * (g * g)) • Mg
  lemma-Mg𝑠^k' k = begin 
    Mg • 𝑠^ k ≈⟨ refl ⟩
    Mg • 𝑠 ^ toℕ k ≈⟨ lemma-Mg𝑠^k (toℕ k) ⟩
    𝑠 ^ (toℕ k Nat.* toℕ (g * g)) • Mg ≈⟨ (cleft lemma-𝑠^k-% (toℕ k Nat.* toℕ (g * g))) ⟩
    𝑠 ^ ((toℕ k Nat.* toℕ (g * g)) % p) • Mg ≈⟨ (cleft refl' (Eq.cong (𝑠 ^_) (lemma-toℕ-% k (g * g)))) ⟩
    𝑠 ^ toℕ (k * (g * g)) • Mg ≈⟨ refl ⟩
    𝑠^ (k * (g * g)) • Mg ∎
    where
    open SR word-setoid
    x⁻¹ = (g′ ⁻¹) .proj₁
    -x⁻¹ = - x⁻¹

  lemma-Mg^k𝑠 : ∀ k -> Mg ^ k • 𝑠 ≈ 𝑠^ ((g * g) ^′ k) • Mg ^ k
  lemma-Mg^k𝑠 k@0 = trans left-unit (sym right-unit)
  lemma-Mg^k𝑠 k@1 = begin
    Mg ^ k • 𝑠 ≈⟨ axiom semi-M𝑠 ⟩
    𝑠^ ((g * g)) • Mg ^ k ≈⟨ (cleft refl' ( Eq.cong 𝑠^ (Eq.sym (lemma-x^′1=x (fromℕ< _))))) ⟩ -- 
    𝑠^ ((g * g) ^′ k) • Mg ^ k ∎
    where
    open SR word-setoid
  lemma-Mg^k𝑠 k@(₂₊ n) = begin
    (Mg • Mg ^ ₁₊ n) • 𝑠 ≈⟨ assoc ⟩
    Mg • Mg ^ ₁₊ n • 𝑠 ≈⟨ (cright lemma-Mg^k𝑠 (₁₊ n)) ⟩
    Mg • 𝑠^ ((g * g) ^′ (₁₊ n)) • Mg ^ (₁₊ n) ≈⟨ sym assoc ⟩
    (Mg • 𝑠^ ((g * g) ^′ (₁₊ n))) • Mg ^ (₁₊ n) ≈⟨ (cleft lemma-Mg𝑠^k' ((g * g) ^′ (₁₊ n))) ⟩
    (𝑠^ (((g * g) ^′ (₁₊ n)) * (g * g)) • Mg) • Mg ^ (₁₊ n) ≈⟨ refl' (Eq.cong (\ xx -> (𝑠^ xx • Mg) • Mg ^ (₁₊ n)) (*-comm ((g * g) ^′ (₁₊ n)) (g * g))) ⟩
    (𝑠^ ((g * g) * ((g * g) ^′ (₁₊ n))) • Mg) • Mg ^ (₁₊ n) ≈⟨ assoc ⟩
    𝑠^ ((g * g) ^′ k) • Mg • Mg ^ ₁₊ n ∎
    where
    open SR word-setoid


  lemma-semi-M𝑠 : ∀ x -> let x' = x .proj₁ in let k = g-gen x .proj₁ in M x • 𝑠 ≈ 𝑠^ ((x' * x')) • M x
  lemma-semi-M𝑠 x = begin
    M x • 𝑠 ≈⟨ (cleft refl' (aux-M≡M x (g^ k) (eqk))) ⟩
    M (g^ k) • 𝑠 ≈⟨ cong (sym (axiom (M-power (k)))) refl ⟩
    Mg^ k • 𝑠 ≈⟨ lemma-Mg^k𝑠 (toℕ k) ⟩
    𝑠^ ((g * g) ^′ toℕ k) • Mg^ k ≈⟨ (cright axiom (M-power (k))) ⟩
    𝑠^ ((g * g) ^′ toℕ k) • M (g^ k) ≈⟨ (cleft refl' (Eq.cong 𝑠^ (*-^′-distribʳ g g (toℕ k)))) ⟩
    𝑠^ ((g ^′ toℕ k) * (g ^′ toℕ k)) • M (g^ k) ≈⟨ sym (cleft refl' (Eq.cong₂ (\ xx yy -> 𝑠^ (xx * yy)) (eqk) (eqk))) ⟩
    𝑠^ (x' * x') • M (g^ k) ≈⟨ (cright refl' (aux-M≡M (g^ k) x (Eq.sym (eqk)))) ⟩
    𝑠^ (x' * x') • M x ∎
    where
    open SR word-setoid
    x' = x .proj₁
    k = inject₁ (g-gen x .proj₁)
    eqk : x .proj₁ ≡ (g^ k) .proj₁
    eqk = Eq.sym (lemma-log-inject x)





-- ====================================================================
-- Lemmas-Clifford-S : copy of Clifford-Mod-Scalar.Lemmas-Clifford
-- (lemma-cong↑, lemma-↑^, lemma-Induction, lemma-comm-*-w↑, …)
-- ====================================================================
module Lemmas-Clifford-S where

  lemma-cong↑ : ∀ {n} w v →
    let open PB (n QRel,_===_) using (_≈_) in
    let open PB ((suc n) QRel,_===_) renaming (_≈_ to _≈↑_) using () in
    w ≈ v → w ↑ ≈↑ v ↑
  lemma-cong↑ {n} w v PB.refl = PB.refl
  lemma-cong↑ {n} w v (PB.sym eq) = PB.sym (lemma-cong↑ v w eq)
  lemma-cong↑ {n} w v (PB.trans eq eq₁) = PB.trans (lemma-cong↑ _ _ eq) (lemma-cong↑ _ _ eq₁)
  lemma-cong↑ {n} w v (PB.cong eq eq₁) = PB.cong (lemma-cong↑ _ _ eq) (lemma-cong↑ _ _ eq₁)
  lemma-cong↑ {n} w v PB.assoc = PB.assoc
  lemma-cong↑ {n} w v PB.left-unit = PB.left-unit
  lemma-cong↑ {n} w v PB.right-unit = PB.right-unit
  lemma-cong↑ {n} w v (PB.axiom x) = PB.axiom (cong↑ x)


  lemma-^-↑ : ∀ {n} (w : Word (Gen n)) k → w ↑ ^ k ≡ (w ^ k) ↑
  lemma-^-↑ w ₀ = auto
  lemma-^-↑ w ₁ = auto
  lemma-^-↑ w (₂₊ k) = begin
    (w ↑) • (w ↑) ^ ₁₊ k ≡⟨ Eq.cong ((w ↑) •_) (lemma-^-↑ w (suc k)) ⟩
    (w ↑) • (w ^ ₁₊ k) ↑ ≡⟨ auto ⟩
    ((w • w ^ ₁₊ k) ↑) ∎
    where open ≡-Reasoning


  lemma-cong↓-S^ : ∀ {n} k -> let open PB ((₂₊ n) QRel,_===_) renaming (_≈_ to _≈↓_) using () in
    (S ^ k) ↓ ≈↓ S ^ k
  lemma-cong↓-S^ {n} ₀ = PB.refl
  lemma-cong↓-S^ {n} ₁ = PB.refl
  lemma-cong↓-S^ {n} (₂₊ k) = PB.cong PB.refl (lemma-cong↓-S^ {n} (₁₊ k))

  lemma-cong↑-S^ : ∀ {n} k -> let open PB ((₂₊ n) QRel,_===_) renaming (_≈_ to _≈↑_) using () in
    (S ^ k) ↑ ≈↑ S ↑ ^ k
  lemma-cong↑-S^ {n} ₀ = PB.refl
  lemma-cong↑-S^ {n} ₁ = PB.refl
  lemma-cong↑-S^ {n} (₂₊ k) = PB.cong PB.refl (lemma-cong↑-S^ {n} (₁₊ k))


  lemma-cong↓-S↓^ : ∀ {n} k -> let open PB ((₃₊ n) QRel,_===_) renaming (_≈_ to _≈↓_) using () in
    (S ↓ ^ k) ↓ ≈↓ S ↓ ^ k
  lemma-cong↓-S↓^ {n} ₀ = PB.refl
  lemma-cong↓-S↓^ {n} ₁ = PB.refl
  lemma-cong↓-S↓^ {n} (₂₊ k) = PB.cong PB.refl (lemma-cong↓-S↓^ {n} (₁₊ k))

  lemma-cong↓-S↑^ : ∀ {n} k -> let open PB ((₃₊ n) QRel,_===_) renaming (_≈_ to _≈↓_) using () in
    ((S ↑) ^ k) ↓ ≈↓ (S ↑) ^ k
  lemma-cong↓-S↑^ {n} ₀ = PB.refl
  lemma-cong↓-S↑^ {n} ₁ = PB.refl
  lemma-cong↓-S↑^ {n} (₂₊ k) = PB.cong PB.refl (lemma-cong↓-S↑^ {n} (₁₊ k))


  lemma-cong↓-S^↓ : ∀ {n} k -> let open PB ((₃₊ n) QRel,_===_) renaming (_≈_ to _≈↓_) using () in
    (S ^ k) ↓ ↓ ≈↓ (S ^ k) ↓
  lemma-cong↓-S^↓ {n} ₀ = PB.refl
  lemma-cong↓-S^↓ {n} ₁ = PB.refl
  lemma-cong↓-S^↓ {n} (₂₊ k) = PB.cong PB.refl (lemma-cong↓-S^↓ {n} (₁₊ k))

  lemma-cong↓-S^↑ : ∀ {n} k -> let open PB ((₃₊ n) QRel,_===_) renaming (_≈_ to _≈↓_) using () in
    (S ^ k) ↑ ↓ ≈↓ (S ^ k) ↑
  lemma-cong↓-S^↑ {n} ₀ = PB.refl
  lemma-cong↓-S^↑ {n} ₁ = PB.refl
  lemma-cong↓-S^↑ {n} (₂₊ k) = PB.cong PB.refl (lemma-cong↓-S^↑ {n} (₁₊ k))

  lemma-cong↓-H^ : ∀ {n} k -> let open PB ((₂₊ n) QRel,_===_) renaming (_≈_ to _≈↓_) using () in
    (H ^ k) ↓ ≈↓ H ^ k
  lemma-cong↓-H^ {n} ₀ = PB.refl
  lemma-cong↓-H^ {n} ₁ = PB.refl
  lemma-cong↓-H^ {n} (₂₊ k) = PB.cong PB.refl (lemma-cong↓-H^ {n} (₁₊ k))

  lemma-cong↓-CZ^ : ∀ {n} k -> let open PB ((₃₊ n) QRel,_===_) renaming (_≈_ to _≈↓_) using () in
    (CZ ^ k) ↓ ≈↓ CZ ^ k
  lemma-cong↓-CZ^ {n} ₀ = PB.refl
  lemma-cong↓-CZ^ {n} ₁ = PB.refl
  lemma-cong↓-CZ^ {n} (₂₊ k) = PB.cong PB.refl (lemma-cong↓-CZ^ {n} (₁₊ k))

  lemma-↑↓ : ∀ {n} (w : Word (Gen n)) → w ↑ ↓ ≡ w ↓ ↑
  lemma-↑↓ [ x ]ʷ = auto
  lemma-↑↓ ε = auto
  lemma-↑↓ (w • w₁) = Eq.cong₂ _•_ (lemma-↑↓ w) (lemma-↑↓ w₁)

  lemma-↑^ : ∀ {n} k (w : Word (Gen n)) → (w ^ k) ↑ ≡ w ↑ ^ k
  lemma-↑^ {n} ₀ w = auto
  lemma-↑^ {n} ₁ w = auto
  lemma-↑^ {n} (₂₊ k) w = Eq.cong₂ _•_ auto (lemma-↑^ {n} (₁₊ k) w)


  lemma-↓^ : ∀ {n} k (w : Word (Gen n)) → (w ^ k) ↓ ≡ w ↓ ^ k
  lemma-↓^ {n} ₀ w = auto
  lemma-↓^ {n} ₁ w = auto
  lemma-↓^ {n} (₂₊ k) w = Eq.cong₂ _•_ auto (lemma-↓^ {n} (₁₊ k) w)


  lemma-comm-S-w↑ : ∀ {n} w → let open PB ((₂₊ n) QRel,_===_) in
    
    S • w ↑ ≈ w ↑ • S
    
  lemma-comm-S-w↑ {n} [ x ]ʷ = sym (axiom comm-S)
    where
    open PB ((₂₊ n) QRel,_===_)
  lemma-comm-S-w↑ {n} ε = trans right-unit (sym left-unit)
    where
    open PB ((₂₊ n) QRel,_===_)
  lemma-comm-S-w↑ {n} (w • w₁) = begin
    S • ((w • w₁) ↑) ≈⟨ refl ⟩
    S • (w ↑ • w₁ ↑) ≈⟨ sym assoc ⟩
    (S • w ↑) • w₁ ↑ ≈⟨ cong (lemma-comm-S-w↑ w) refl ⟩
    (w ↑ • S) • w₁ ↑ ≈⟨ assoc ⟩
    w ↑ • S • w₁ ↑ ≈⟨ cong refl (lemma-comm-S-w↑ w₁) ⟩
    w ↑ • w₁ ↑ • S ≈⟨ sym assoc ⟩
    ((w • w₁) ↑) • S ∎
    where
    open PB ((₂₊ n) QRel,_===_)
    open PP ((₂₊ n) QRel,_===_)
    open SR word-setoid

  lemma-comm-Sᵏ-w↑ : ∀ {n} k w → let open PB ((₂₊ n) QRel,_===_) in
    
    S ^ k • w ↑ ≈ w ↑ • S ^ k
    
  lemma-comm-Sᵏ-w↑ {n} ₀ w = trans left-unit (sym right-unit)
    where
    open PB ((₂₊ n) QRel,_===_)
  lemma-comm-Sᵏ-w↑ {n} ₁ w = lemma-comm-S-w↑ w
    where
    open PB ((₂₊ n) QRel,_===_)
  lemma-comm-Sᵏ-w↑ {n} (₂₊ k) w = begin
    (S • S ^ ₁₊ k) • (w ↑) ≈⟨ assoc ⟩
    S • S ^ ₁₊ k • (w ↑) ≈⟨ cong refl (lemma-comm-Sᵏ-w↑ (₁₊ k) w) ⟩
    S • (w ↑) • S ^ ₁₊ k ≈⟨ sym assoc ⟩
    (S • w ↑) • S ^ ₁₊ k ≈⟨ cong (lemma-comm-S-w↑ w) refl ⟩
    (w ↑ • S) • S ^ ₁₊ k ≈⟨ assoc ⟩
    (w ↑) • S • S ^ ₁₊ k ∎
    where
    open PB ((₂₊ n) QRel,_===_)
    open PP ((₂₊ n) QRel,_===_)
    open SR word-setoid


  lemma-comm-H-w↑ : ∀ {n} w → let open PB ((₂₊ n) QRel,_===_) in
    
    H • w ↑ ≈ w ↑ • H
    
  lemma-comm-H-w↑ {n} [ x ]ʷ = sym (axiom comm-H)
    where
    open PB ((₂₊ n) QRel,_===_)
  lemma-comm-H-w↑ {n} ε = trans right-unit (sym left-unit)
    where
    open PB ((₂₊ n) QRel,_===_)
  lemma-comm-H-w↑ {n} (w • w₁) = begin
    H • ((w • w₁) ↑) ≈⟨ refl ⟩
    H • (w ↑ • w₁ ↑) ≈⟨ sym assoc ⟩
    (H • w ↑) • w₁ ↑ ≈⟨ cong (lemma-comm-H-w↑ w) refl ⟩
    (w ↑ • H) • w₁ ↑ ≈⟨ assoc ⟩
    w ↑ • H • w₁ ↑ ≈⟨ cong refl (lemma-comm-H-w↑ w₁) ⟩
    w ↑ • w₁ ↑ • H ≈⟨ sym assoc ⟩
    ((w • w₁) ↑) • H ∎
    where
    open PB ((₂₊ n) QRel,_===_)
    open PP ((₂₊ n) QRel,_===_)
    open SR word-setoid



  lemma-comm-Hᵏ-w↑ : ∀ {n} k w → let open PB ((₂₊ n) QRel,_===_) in
    
    H ^ k • w ↑ ≈ w ↑ • H ^ k
    
  lemma-comm-Hᵏ-w↑ {n} ₀ w = trans left-unit (sym right-unit)
    where
    open PB ((₂₊ n) QRel,_===_)
  lemma-comm-Hᵏ-w↑ {n} ₁ w = lemma-comm-H-w↑ w
    where
    open PB ((₂₊ n) QRel,_===_)
  lemma-comm-Hᵏ-w↑ {n} (₂₊ k) w = begin
    (H • H ^ ₁₊ k) • (w ↑) ≈⟨ assoc ⟩
    H • H ^ ₁₊ k • (w ↑) ≈⟨ cong refl (lemma-comm-Hᵏ-w↑ (₁₊ k) w) ⟩
    H • (w ↑) • H ^ ₁₊ k ≈⟨ sym assoc ⟩
    (H • w ↑) • H ^ ₁₊ k ≈⟨ cong (lemma-comm-H-w↑ w) refl ⟩
    (w ↑ • H) • H ^ ₁₊ k ≈⟨ assoc ⟩
    (w ↑) • H • H ^ ₁₊ k ∎
    where
    open PB ((₂₊ n) QRel,_===_)
    open PP ((₂₊ n) QRel,_===_)
    open SR word-setoid


  lemma-comm-Z-w↑ : ∀ {n} w → let open PB ((₂₊ n) QRel,_===_) in
    
    Z • w ↑ ≈ w ↑ • Z
    
  lemma-comm-Z-w↑ {n} w = begin
    (H • H • S • H • H • S⁻¹) • w ↑ ≈⟨ by-assoc auto ⟩
    (H • H • S • H • H) • S⁻¹ • w ↑ ≈⟨ (cright lemma-comm-Sᵏ-w↑ p-1 w) ⟩
    (H • H • S • H • H) • w ↑ • S⁻¹ ≈⟨ by-assoc auto ⟩
    (H • H • S) • (H ^ 2 • w ↑) • S⁻¹ ≈⟨ (cright cleft lemma-comm-Hᵏ-w↑ 2 w) ⟩
    (H • H • S) • (w ↑ • H ^ 2) • S⁻¹ ≈⟨ special-assoc (□ ^ 3 • □ ^ 2 • □) (□ ^ 2 • □ ^ 2 • □ ^ 2) auto ⟩
    H ^ 2 • (S • w ↑) • H ^ 2 • S⁻¹ ≈⟨ (cright cleft lemma-comm-Sᵏ-w↑ 1 w) ⟩
    H ^ 2 • (w ↑ • S) • H ^ 2 • S⁻¹ ≈⟨ trans (by-assoc auto) assoc ⟩
    (H ^ 2 • w ↑) • S • H ^ 2 • S⁻¹ ≈⟨ (cleft lemma-comm-Hᵏ-w↑ 2 w) ⟩
    (w ↑ • H ^ 2) • S • H ^ 2 • S⁻¹ ≈⟨ special-assoc (□ ^ 3 • □ • □ ^ 2 • □) (□ • □ ^ 6 ) auto ⟩
    w ↑ • Z ∎
    where
    open PB ((₂₊ n) QRel,_===_)
    open PP ((₂₊ n) QRel,_===_)
    open SR word-setoid
    open Pattern-Assoc


  lemma-comm-X-w↑ : ∀ {n} w → let open PB ((₂₊ n) QRel,_===_) in
    
    X • w ↑ ≈ w ↑ • X
    
  lemma-comm-X-w↑ {n} w = begin
    (H • S • H • H • S⁻¹ • H) • w ↑ ≈⟨ special-assoc (□ ^ 6 • □) (□ ^ 5 • □ ^ 2) auto ⟩
    (H • S • H • H • S⁻¹) • H • w ↑ ≈⟨ (cright lemma-comm-Hᵏ-w↑ 1 w) ⟩
    (H • S • H • H • S⁻¹) • w ↑ • H ≈⟨ special-assoc (□ ^ 5 • □ ^ 2) (□ ^ 4 • □ ^ 2 • □) auto ⟩
    (H • S • H • H) • (S⁻¹ • w ↑) • H ≈⟨ (cright cleft lemma-comm-Sᵏ-w↑ p-1 w) ⟩
    (H • S • H • H) • (w ↑ • S⁻¹) • H ≈⟨ special-assoc (□ ^ 4 • □ ^ 2 • □) (□ ^ 2 • (□ ^ 2 • □) • □ ^ 2) auto ⟩
    (H • S) • (H ^ 2 • w ↑) • S⁻¹ • H ≈⟨ (cright cleft lemma-comm-Hᵏ-w↑ 2 w) ⟩
    (H • S) • (w ↑ • H ^ 2) • S⁻¹ • H ≈⟨ special-assoc (□ ^ 2 • □ ^ 2 • □ ^ 2) (□ • □ ^ 2 • □ • □ ^ 2) auto ⟩
    H • (S • w ↑) • H ^ 2 • S⁻¹ • H ≈⟨ (cright cleft lemma-comm-Sᵏ-w↑ 1 w) ⟩
    H • (w ↑ • S) • H ^ 2 • S⁻¹ • H ≈⟨ trans (by-assoc auto) assoc ⟩
    (H • w ↑) • S • H ^ 2 • S⁻¹ • H ≈⟨ (cleft lemma-comm-Hᵏ-w↑ 1 w) ⟩
    (w ↑ • H) • S • H ^ 2 • S⁻¹ • H ≈⟨ special-assoc (□ ^ 2 • □ • □ ^ 2 • □ ^ 2) (□ • □ ^ 6) auto ⟩
    w ↑ • X ∎
    where
    open PB ((₂₊ n) QRel,_===_)
    open PP ((₂₊ n) QRel,_===_)
    open SR word-setoid
    open Pattern-Assoc



  lemma-comm-CZ-w↑ : ∀ {n} w → let open PB ((₃₊ n) QRel,_===_) in
    
    CZ • w ↑ ↑ ≈ w ↑ ↑ • CZ
    
  lemma-comm-CZ-w↑ {n} [ x ]ʷ = sym (axiom comm-CZ)
    where
    open PB ((₃₊ n) QRel,_===_)
  lemma-comm-CZ-w↑ {n} ε = trans right-unit (sym left-unit)
    where
    open PB ((₃₊ n) QRel,_===_)
  lemma-comm-CZ-w↑ {n} (w • w₁) = begin
    CZ • ((w • w₁) ↑ ↑) ≈⟨ refl ⟩
    CZ • (w ↑ ↑ • w₁ ↑ ↑) ≈⟨ sym assoc ⟩
    (CZ • w ↑ ↑) • w₁ ↑ ↑ ≈⟨ cong (lemma-comm-CZ-w↑ w) refl ⟩
    (w ↑ ↑ • CZ) • w₁ ↑ ↑ ≈⟨ assoc ⟩
    w ↑ ↑ • CZ • w₁ ↑ ↑ ≈⟨ cong refl (lemma-comm-CZ-w↑ w₁) ⟩
    w ↑ ↑ • w₁ ↑ ↑ • CZ ≈⟨ sym assoc ⟩
    ((w • w₁) ↑ ↑) • CZ ∎
    where
    open PB ((₃₊ n) QRel,_===_)
    open PP ((₃₊ n) QRel,_===_)
    open SR word-setoid

  aux-MM : ∀ {n} -> let open PB ((₁₊ n) QRel,_===_) in ∀ {x y : ℤ ₚ} (nzx : x ≢ ₀) (nzy : y ≢ ₀) -> x ≡ y -> M (x , nzx) ≈ M (y , nzy)
  aux-MM {n} {x} {y} nz1 nz2 eq rewrite eq = refl
    where
    open PB ((₁₊ n) QRel,_===_)



  lemma-Induction : ∀ {n} -> let open PB ((₁₊ n) QRel,_===_) in ∀ {w v v'} -> w • v ≈ v' • w -> ∀ k -> w • v ^ k ≈ v' ^ k • w
  lemma-Induction {n} {w} {v} {v'} eq k@0 = trans right-unit (sym left-unit)
    where open PB ((₁₊ n) QRel,_===_)
  lemma-Induction {n} {w} {v} {v'} eq k@1 = eq
  lemma-Induction {n} {w} {v} {v'} eq k@(₂₊ k') = begin
    w • v ^ k ≈⟨ sym assoc ⟩
    (w • v) • v ^ (₁₊ k') ≈⟨ (cleft eq) ⟩
    (v' • w) • v ^ (₁₊ k') ≈⟨ assoc ⟩
    v' • w • v ^ (₁₊ k') ≈⟨ (cright lemma-Induction eq (₁₊ k')) ⟩
    v' • v' ^ (₁₊ k') • w ≈⟨ sym assoc ⟩
    v' ^ k • w ∎
    where
    open PP ((₁₊ n) QRel,_===_)
    open PB ((₁₊ n) QRel,_===_)
    open SR word-setoid


  lemma-Inductionˡ : ∀ {n} -> let open PB ((₁₊ n) QRel,_===_) in ∀ {w w' v} -> w • v ≈ v • w' -> ∀ k -> w ^ k • v ≈ v • w' ^ k
  lemma-Inductionˡ {n} {w} {w'} {v} eq k@0 = trans left-unit (sym right-unit)
    where open PB ((₁₊ n) QRel,_===_)
  lemma-Inductionˡ {n} {w} {w'} {v} eq k@1 = eq
  lemma-Inductionˡ {n} {w} {w'} {v} eq k@(₁₊ k'@(₁₊ k'')) = begin
    w ^ k • v ≈⟨ assoc ⟩
    w • w ^ k' • v ≈⟨ (cright lemma-Inductionˡ eq k') ⟩
    w • v • w' ^ k' ≈⟨ sym assoc ⟩
    (w • v) • w' ^ k' ≈⟨ (cleft eq) ⟩
    (v • w') • w' ^ k' ≈⟨ assoc ⟩
    v • w' ^ k ∎
    where
    open PP ((₁₊ n) QRel,_===_)
    open PB ((₁₊ n) QRel,_===_)
    open SR word-setoid


-- ====================================================================
-- Simplified-GroupLike-S : copy of Clifford-GroupLike for Simplified.
-- ====================================================================
module Simplified-GroupLike-S where

  private
    variable
      n : ℕ

  open Lemmas-Clifford-S

  grouplike : Grouplike (n QRel,_===_)
  grouplike {₁₊ n} (H-gen) = (H ) ^ 3 , claim
    where
    open PB ((₁₊ n) QRel,_===_)
    open PP ((₁₊ n) QRel,_===_)
    open SR word-setoid
    open Lemmas1-S n
    claim : (H ) ^ 3 • H ≈ ε
    claim = begin
      (H) ^ 3 • H ≈⟨ by-assoc auto ⟩
      (H) ^ 4 ≈⟨ lemma-order-H ⟩
      ε ∎

  grouplike {₁₊ n} (S-gen) = (S) ^ p-1 ,  claim
    where
    open PB ((₁₊ n) QRel,_===_)
    open PP ((₁₊ n) QRel,_===_)
    open SR word-setoid
    claim : (S) ^ p-1 • S ≈ ε
    claim = begin
      (S) ^ p-1 • S ≈⟨ sym (lemma-^-+ (S) p-1 1) ⟩
      (S) ^ (p-1 Nat.+ 1) ≡⟨ Eq.cong (S ^_) ( NP.+-comm p-1 1) ⟩
      (S ^ p) ≈⟨ (axiom order-S) ⟩
      (ε) ∎

  grouplike {₂₊ n} (CZ-gen) = (CZ) ^ p-1 ,  claim
    where
    open PB ((₂₊ n) QRel,_===_)
    open PP ((₂₊ n) QRel,_===_)
    open SR word-setoid
    claim : (CZ) ^ p-1 • CZ ≈ ε
    claim = begin
      (CZ) ^ p-1 • CZ ≈⟨ sym (lemma-^-+ (CZ) p-1 1) ⟩
      (CZ) ^ (p-1 Nat.+ 1) ≡⟨ Eq.cong (CZ ^_) ( NP.+-comm p-1 1) ⟩
      (CZ ^ p) ≈⟨ (axiom order-CZ) ⟩
      (ε) ∎

  grouplike {₂₊ n} (g ↥) with grouplike g
  ... | ig , prf = (ig ↑) , lemma-cong↑ (ig • [ g ]ʷ) ε prf
    where
    open PB ((₂₊ n) QRel,_===_)
    open PP ((₂₊ n) QRel,_===_)



-- ----------------------------------------------------------------------
-- * Data required for applying word tactics to Symplectic generators


module Lemmas1b-S (n : ℕ) where


  open Lemmas-Clifford-S
  open Lemmas1-S n

  open PB ((₁₊ n) QRel,_===_) hiding (_===_)
  open PP ((₁₊ n) QRel,_===_)
  open SR word-setoid
  open Pattern-Assoc
  open Simplified-GroupLike-S
  open import Data.Nat.DivMod
  open import Data.Fin.Properties


  aux-S⁻¹⁻¹ : 
    S⁻¹ ^ p-1 ≈ S
  aux-S⁻¹⁻¹ = lemma-right-cancel {h = S⁻¹} aux00
    where
    open Basis-Change _ ((₁₊ n) QRel,_===_) grouplike
    open Group-Lemmas _ ((₁₊ n) QRel,_===_) grouplike renaming (_⁻¹ to _⁻¹′)
    aux00 : S⁻¹ ^ p-1 • S⁻¹ ≈ S • S⁻¹
    aux00 = begin
      S⁻¹ ^ p-1 • S⁻¹ ≈⟨ word-comm p-1 1 refl ⟩
      S⁻¹ • S⁻¹ ^ p-1 ≈⟨ refl ⟩
      S⁻¹ ^ p ≈⟨ lemma-^^ S p-1 p ⟩
      S ^ (p-1 Nat.* p) ≡⟨ Eq.cong (S ^_) (NP.*-comm p-1 p) ⟩
      S ^ (p Nat.* p-1) ≈⟨ sym (lemma-^^ S p p-1) ⟩
      (S ^ p) ^ p-1 ≈⟨ lemma-^-cong (S ^ p) ε p-1 (axiom order-S) ⟩
      ε ^ p-1 ≈⟨ lemma-ε^k=ε (₁₊ p-2) ⟩
      ε ≈⟨ sym (axiom order-S) ⟩
      S • S⁻¹ ∎

  aux-Z⁻¹⁻¹ : 
    Z⁻¹ ^ p-1 ≈ Z
  aux-Z⁻¹⁻¹ = lemma-right-cancel {h = Z⁻¹} aux00
    where
    open Basis-Change _ ((₁₊ n) QRel,_===_) grouplike
    open Group-Lemmas _ ((₁₊ n) QRel,_===_) grouplike renaming (_⁻¹ to _⁻¹′)
    aux00 : Z⁻¹ ^ p-1 • Z⁻¹ ≈ Z • Z⁻¹
    aux00 = begin
      Z⁻¹ ^ p-1 • Z⁻¹ ≈⟨ word-comm p-1 1 refl ⟩
      Z⁻¹ • Z⁻¹ ^ p-1 ≈⟨ refl ⟩
      Z⁻¹ ^ p ≈⟨ lemma-^^ Z p-1 p ⟩
      Z ^ (p-1 Nat.* p) ≡⟨ Eq.cong (Z ^_) (NP.*-comm p-1 p) ⟩
      Z ^ (p Nat.* p-1) ≈⟨ sym (lemma-^^ Z p p-1) ⟩
      (Z ^ p) ^ p-1 ≈⟨ lemma-^-cong (Z ^ p) ε p-1 (lemma-order-Z) ⟩
      ε ^ p-1 ≈⟨ lemma-ε^k=ε (₁₊ p-2) ⟩
      ε ≈⟨ sym (lemma-order-Z) ⟩
      Z • Z⁻¹ ∎



  aux-X⁻¹⁻¹ : 
    X⁻¹ ^ p-1 ≈ X
  aux-X⁻¹⁻¹ = lemma-right-cancel {h = X⁻¹} aux00
    where
    open Basis-Change _ ((₁₊ n) QRel,_===_) grouplike
    open Group-Lemmas _ ((₁₊ n) QRel,_===_) grouplike renaming (_⁻¹ to _⁻¹′)
    aux00 : X⁻¹ ^ p-1 • X⁻¹ ≈ X • X⁻¹
    aux00 = begin
      X⁻¹ ^ p-1 • X⁻¹ ≈⟨ word-comm p-1 1 refl ⟩
      X⁻¹ • X⁻¹ ^ p-1 ≈⟨ refl ⟩
      X⁻¹ ^ p ≈⟨ lemma-^^ X p-1 p ⟩
      X ^ (p-1 Nat.* p) ≡⟨ Eq.cong (X ^_) (NP.*-comm p-1 p) ⟩
      X ^ (p Nat.* p-1) ≈⟨ sym (lemma-^^ X p p-1) ⟩
      (X ^ p) ^ p-1 ≈⟨ lemma-^-cong (X ^ p) ε p-1 (lemma-order-X) ⟩
      ε ^ p-1 ≈⟨ lemma-ε^k=ε (₁₊ p-2) ⟩
      ε ≈⟨ sym (lemma-order-X) ⟩
      X • X⁻¹ ∎



  conj-H-X : H • X ≈ Z • H
  conj-H-X = begin
    H • X ≈⟨ by-assoc auto ⟩
    Z • H ∎

  conj-H-X^k : ∀ k -> H • X ^ k ≈ Z ^ k • H
  conj-H-X^k k@0 = by-assoc auto
  conj-H-X^k k@1 = conj-H-X
  conj-H-X^k k@(₁₊ k'@(₁₊ k'')) = begin
    H • X ^ k ≈⟨ sym assoc ⟩
    (H • X) • X ^ k' ≈⟨ (cleft conj-H-X) ⟩
    (Z • H) • X ^ k' ≈⟨ assoc ⟩
    Z • H • X ^ k' ≈⟨ (cright conj-H-X^k k') ⟩
    Z • Z ^ k' • H ≈⟨ sym assoc ⟩
    Z ^ k • H ∎


  lemma-HH-Z : HH • Z ≈ Z^ (- ₁) • HH
  lemma-HH-Z = begin
    HH • H • H • S • H • H • S⁻¹ ≈⟨ special-assoc (□ ^ 2 • □ ^ 6) (□ • □ • □ ^ 5 • □) auto ⟩
    H • H • (H • H • S • H • H) • S⁻¹ ≈⟨ (cright cright sym (word-comm p-1 1 (lemma-comm-SHHS^kHH 1))) ⟩
    H • H • S⁻¹ • (H • H • S • H • H) ≈⟨ special-assoc (□ ^ 8) (□ ^ 6 • □ ^ 2) auto ⟩
    (H • H • S⁻¹ • H • H • S) • H • H ≈⟨ (cleft (cright cright cong (refl' (Eq.cong (S ^_) (Eq.sym lemma-toℕ-1ₚ))) (cright cright sym aux-S⁻¹⁻¹))) ⟩
    (H • H • S ^ (toℕ (- 1ₚ)) • H • H • S⁻¹ ^ p-1) • HH ≈⟨ (cleft cright cright cright cright cright refl' (Eq.cong (S⁻¹ ^_) (Eq.sym lemma-toℕ-1ₚ))) ⟩
    (H • H • S ^ (toℕ (- 1ₚ)) • H • H • S⁻¹ ^ (toℕ (- 1ₚ))) • HH ≈⟨ (cleft sym (lemma-Z^k-ℕ (toℕ (- 1ₚ)))) ⟩
    Z^ (- ₁) • HH ∎


  lemma-HH-X : HH • X ≈ X^ (- ₁) • HH
  lemma-HH-X = bbc H ε claim
    where
    open Basis-Change _ ((₁₊ n) QRel,_===_) grouplike
    claim : H • (HH • X) • ε ≈ H • (X^ (- ₁) • HH) • ε
    claim = begin
      H • (HH • X) • ε ≈⟨ cong refl right-unit ⟩
      H • (HH • X) ≈⟨ special-assoc (□ • □ ^ 2 • □) (□ ^ 2 • □ ^ 2) auto ⟩
      HH • H • X ≈⟨ (cright conj-H-X) ⟩
      HH • Z • H ≈⟨ sym assoc ⟩
      (HH • Z) • H ≈⟨ (cleft lemma-HH-Z) ⟩
      (Z^ (- ₁) • HH) • H ≈⟨ special-assoc (□ ^ 3 • □) (□ ^ 2 • □ ^ 2) auto ⟩
      (Z^ (- ₁) • H) • HH ≈⟨ (cleft sym (conj-H-X^k (toℕ (- ₁)))) ⟩
      (H • X^ (- ₁)) • HH ≈⟨ assoc ⟩
      H • (X^ (- ₁) • HH) ≈⟨ sym (cong refl right-unit) ⟩
      H • (X^ (- ₁) • HH) • ε ∎

  conj-H-Z : H • Z ≈ X^ (- ₁) • H
  conj-H-Z = bbc (H ^ 3) H claim 
    where
    open Basis-Change _ ((₁₊ n) QRel,_===_) grouplike
    claim : H ^ 3 • (H • Z) • H ≈ H ^ 3 • (X^ (- ₁) • H) • H
    claim = begin
      H ^ 3 • (H • Z) • H ≈⟨ by-assoc auto ⟩
      (H ^ 4) • Z • H ≈⟨ trans (cleft lemma-order-H) left-unit ⟩
      Z • H ≈⟨ sym conj-H-X ⟩
      H • X ≈⟨ cleft (sym (trans (cright lemma-order-H) right-unit)) ⟩
      H ^ 5 • X ≈⟨ special-assoc (□ ^ 5 • □) (□ ^ 3 • □ ^ 2 • □) auto ⟩
      H ^ 3 • HH • X ≈⟨ (cright lemma-HH-X) ⟩
      H ^ 3 • X^ (- ₁) • H • H ≈⟨ special-assoc (□ ^ 4) (□ • □ ^ 2 • □) auto ⟩
      H ^ 3 • (X^ (- ₁) • H) • H ∎


  lemma-SHSH : S • H • S • H ≈ H ^ 3 • S⁻¹
  lemma-SHSH = bbc ε (S • H) claim
    where
    open Basis-Change _ ((₁₊ n) QRel,_===_) grouplike
    open Group-Lemmas _ _ (grouplike {₁₊ n}) renaming (_⁻¹ to _⁻¹ʷ)
    
    claim : ε • (S • H • S • H) • S • H ≈ ε • (H ^ 3 • S⁻¹) • S • H
    claim = begin
      ε • (S • H • S • H) • S • H ≈⟨ left-unit ⟩
      (S • H • S • H) • S • H ≈⟨ special-assoc (□ ^ 4 • □ ^ 2) ((□ ^ 2) ^ 3) auto ⟩
      (S • H) ^ 3 ≈⟨ axiom order-SH ⟩
      ε ≈⟨ sym lemma-left-inverse ⟩
      (H ^ 3 • S⁻¹) • S • H ≈⟨ sym left-unit ⟩
      ε • (H ^ 3 • S⁻¹) • S • H ∎


  lemma-HSHSH : H • S • H • S • H ≈ S⁻¹
  lemma-HSHSH = bbc S ε claim
    where
    open Basis-Change _ ((₁₊ n) QRel,_===_) grouplike
    open Group-Lemmas _ _ (grouplike {₁₊ n}) renaming (_⁻¹ to _⁻¹ʷ)
    
    claim : S • (H • S • H • S • H) • ε ≈ S • S⁻¹ • ε
    claim = begin
      S • (H • S • H • S • H) • ε ≈⟨ by-assoc auto ⟩
      (S • H) ^ 3 ≈⟨ axiom order-SH ⟩
      ε ≈⟨ sym (axiom order-S) ⟩
      S • S⁻¹ ≈⟨ sym (cong refl right-unit) ⟩
      S • S⁻¹ • ε ∎

  lemma-HSH : H • S • H ≈ S⁻¹ • H ^ 3 • S⁻¹
  lemma-HSH = bbc S ε claim
    where
    open Basis-Change _ ((₁₊ n) QRel,_===_) grouplike
    open Group-Lemmas _ _ (grouplike {₁₊ n}) renaming (_⁻¹ to _⁻¹ʷ)
    claim : S • (H • S • H) • ε ≈ S • (S⁻¹ • H ^ 3 • S⁻¹) • ε
    claim = begin
      S • (H • S • H) • ε ≈⟨ cong refl right-unit ⟩
      S • (H • S • H) ≈⟨ lemma-SHSH ⟩
      H ^ 3 • S⁻¹ ≈⟨ sym left-unit ⟩
      ε • H ^ 3 • S⁻¹ ≈⟨ (cleft sym (axiom order-S)) ⟩
      (S • S⁻¹) • H ^ 3 • S⁻¹ ≈⟨ assoc ⟩
      S • (S⁻¹ • H ^ 3 • S⁻¹) ≈⟨ sym (cong refl right-unit) ⟩
      S • (S⁻¹ • H ^ 3 • S⁻¹) • ε ∎
  
  lemma-SX : S • X ≈ X • Z • S
  lemma-SX = begin
    S • H • S • H • H • S⁻¹ • H ≈⟨ special-assoc (□ ^ 7) (□ ^ 4 • □ ^ 3) auto ⟩
    (S • H • S • H) • H • S⁻¹ • H ≈⟨ (cleft lemma-SHSH) ⟩
    (H ^ 3 • S⁻¹) • H • S⁻¹ • H ≈⟨ (cright cleft (sym (trans (by-assoc auto) (trans (cleft lemma-order-H) left-unit)))) ⟩
    (H ^ 3 • S⁻¹) • H ^ 5 • S⁻¹ • H ≈⟨ sym (special-assoc (□ ^ 5 • □ • □ ^ 3 • □ ^ 2) ((□ ^ 3 • □ )• □ ^ 5 • □ ^ 2) auto) ⟩
    (H • H • H • S⁻¹ • H) • (H • H ^ 3 • S⁻¹ • H) ≈⟨ (cleft (cright sym left-unit)) ⟩
    (H • ε • H • H • S⁻¹ • H) • (H • H ^ 3 • S⁻¹ • H) ≈⟨ (cleft cright cleft sym (axiom order-S)) ⟩
    (H • (S • S⁻¹) • H • H • S⁻¹ • H) • (H • H ^ 3 • S⁻¹ • H) ≈⟨ special-assoc ((□ • □ ^ 2 • □ ^ 4) • □ ^ 4) (□ ^ 2 • □ ^ 6 • □ ^ 3) auto ⟩
    (H • S) • (S⁻¹ • H • H • S⁻¹ • H • H) • H ^ 3 • S⁻¹ • H ≈⟨ (cright cleft word-comm p-1 1 (lemma-comm-SHHS^kHH p-1)) ⟩
    (H • S) • ((H • H • S⁻¹ • H • H) • S⁻¹) • H ^ 3 • S⁻¹ • H ≈⟨ special-assoc (□ ^ 2 • (□ ^ 5 • □) • □ ^ 3) (□ ^ 6 • □ • □ ^ 3 • □) auto ⟩
    (H • S • H • H • S⁻¹ • H) • H • (S⁻¹ • H ^ 3 • S⁻¹) • H ≈⟨ (cright cright cleft sym lemma-HSH) ⟩
    (H • S • H • H • S⁻¹ • H) • H • (H • S • H) • H ≈⟨ special-assoc (□ ^ 6 • □ • □ ^ 3 • □) (□ ^ 6 • □ ^ 5) auto ⟩

    (H • S • H • H • S⁻¹ • H) • (H • H • S • H • H) ≈⟨ (cright sym right-unit) ⟩
    (H • S • H • H • S⁻¹ • H) • (H • H • S • H • H) • ε ≈⟨ (cright cright sym (axiom order-S)) ⟩
    (H • S • H • H • S⁻¹ • H) • (H • H • S • H • H) • S • S⁻¹ ≈⟨ (cright cright word-comm 1 p-1 refl) ⟩
    (H • S • H • H • S⁻¹ • H) • (H • H • S • H • H) • S⁻¹ • S ≈⟨ (cright special-assoc (□ ^ 5 • □ ^ 2) (□ ^ 6 • □) auto) ⟩
    (H • S • H • H • S⁻¹ • H) • (H • H • S • H • H • S⁻¹) • S ∎
    where

  conj-S-X : S • X ≈ (X • Z) • S
  conj-S-X = begin
    S • X ≈⟨ lemma-SX ⟩
    X • Z • S ≈⟨ sym assoc ⟩
    (X • Z) • S ∎

  conj-S-X^k : ∀ k -> S • X ^ k ≈ (X • Z) ^ k • S
  conj-S-X^k k = lemma-Induction conj-S-X k

  conj-S^l-X : ∀ l -> S ^ l • X ≈ X • Z ^ l • S ^ l
  conj-S^l-X l = begin
    S ^ l • X ≈⟨ lemma-Inductionˡ lemma-SX l ⟩
    X • (Z • S) ^ l ≈⟨ (cright lemma-^-• Z S l lemma-comm-Z-S) ⟩
    X • Z ^ l • S ^ l ∎  

  conj-S^l-X' : ∀ l -> S ^ l • X ≈ (X • Z ^ l) • S ^ l
  conj-S^l-X' l = begin
    S ^ l • X ≈⟨ conj-S^l-X l ⟩
    X • Z ^ l • S ^ l ≈⟨ sym assoc ⟩
    (X • Z ^ l) • S ^ l ∎



-- ====================================================================
-- Clifford-Lemmas-S : copy of N.Clifford.Clifford-Lemmas (𝑠-conjugation,
-- Z↑-CZ, comm-𝑠-w↑, …) for the Simplified relation.
-- ====================================================================
open Lemmas-Clifford-S
open Simplified-GroupLike-S
module CL = Lemmas1-S
module CLb = Lemmas1b-S

lemma-comm-𝑠-w↑ : ∀ {n} w -> let open PB ((suc (suc n)) QRel,_===_) in
  𝑠 • w ↑ ≈ w ↑ • 𝑠
lemma-comm-𝑠-w↑ {n} w = begin
  𝑠 • w ↑ ≡⟨ auto ⟩
  (S • Z ^ toℕ 1/2) • w ↑ ≈⟨ assoc ⟩
  S • (Z ^ toℕ 1/2 • w ↑) ≈⟨ cong refl (word-comm (toℕ 1/2) 1 (lemma-comm-Z-w↑ w)) ⟩
  S • (w ↑ • Z ^ toℕ 1/2) ≈⟨ sym assoc ⟩
  (S • w ↑) • Z ^ toℕ 1/2 ≈⟨ cong (lemma-comm-S-w↑ w) refl ⟩
  (w ↑ • S) • Z ^ toℕ 1/2 ≈⟨ assoc ⟩
  w ↑ • (S • Z ^ toℕ 1/2) ≡⟨ auto ⟩
  w ↑ • 𝑠 ∎
  where
  open PB ((suc (suc n)) QRel,_===_)
  open PP ((suc (suc n)) QRel,_===_)
  open SR word-setoid

lemma-conj-𝑠-X : ∀ {n} -> let open PB ((suc n) QRel,_===_) in
  𝑠 • X ≈ (X • Z) • 𝑠
lemma-conj-𝑠-X {n} = begin
  𝑠 • X ≡⟨ auto ⟩
  (S • Z ^ toℕ 1/2) • X ≈⟨ assoc ⟩
  S • (Z ^ toℕ 1/2 • X) ≈⟨ cong refl (sym (word-comm 1 (toℕ 1/2) (_≈_.axiom _QRel,_===_.comm-X-Z))) ⟩
  S • (X • Z ^ toℕ 1/2) ≈⟨ sym assoc ⟩
  (S • X) • Z ^ toℕ 1/2 ≈⟨ cong (CLb.conj-S-X n) refl ⟩
  ((X • Z) • S) • Z ^ toℕ 1/2 ≈⟨ assoc ⟩
  (X • Z) • (S • Z ^ toℕ 1/2) ≡⟨ auto ⟩
  (X • Z) • 𝑠 ∎
  where
  open PB ((suc n) QRel,_===_)
  open PP ((suc n) QRel,_===_)
  open SR word-setoid

lemma-S^p-1•S : ∀ {n} -> let open PB ((suc n) QRel,_===_) in
  S ^ p-1 • S ≈ ε
lemma-S^p-1•S {n} = begin
  S ^ p-1 • S ≡⟨ auto ⟩
  S ^ p-1 • S ^ 1 ≈⟨ sym (lemma-^-+ S p-1 1) ⟩
  S ^ (p-1 Nat.+ 1) ≡⟨ Eq.cong (S ^_) (NP.+-comm p-1 1) ⟩
  S ^ (1 Nat.+ p-1) ≡⟨ auto ⟩
  S ^ p ≈⟨ axiom _QRel,_===_.order-S ⟩
  ε ∎
  where
  open PB ((suc n) QRel,_===_)
  open PP ((suc n) QRel,_===_)
  open SR word-setoid

lemma-S•S^p-1 : ∀ {n} -> let open PB ((suc n) QRel,_===_) in
  S • S ^ p-1 ≈ ε
lemma-S•S^p-1 {n} = begin
  S • S ^ p-1 ≡⟨ auto ⟩
  S ^ 1 • S ^ p-1 ≈⟨ sym (lemma-^-+ S 1 p-1) ⟩
  S ^ (1 Nat.+ p-1) ≡⟨ auto ⟩
  S ^ p ≈⟨ axiom _QRel,_===_.order-S ⟩
  ε ∎
  where
  open PB ((suc n) QRel,_===_)
  open PP ((suc n) QRel,_===_)
  open SR word-setoid

lemma-comm-S-Z : ∀ {n} -> let open PB ((suc n) QRel,_===_) in
  Z • S ≈ S • Z
lemma-comm-S-Z {n} = trans lhs (sym rhs)
  where
  open PB ((suc n) QRel,_===_)
  open PP ((suc n) QRel,_===_)
  open SR word-setoid
  open Pattern-Assoc

  lhs : Z • S ≈ H • H • S • H • H
  lhs = begin
    Z • S ≡⟨ auto ⟩
    (H • H • S • H • H • S ^ p-1) • S ≈⟨ special-assoc ((□ • □ • □ • □ • □ • □) • □) (□ • □ • □ • □ • □ • □ • □) auto ⟩
    H • H • S • H • H • (S ^ p-1 • S) ≈⟨ cong refl (cong refl (cong refl (cong refl (cong refl lemma-S^p-1•S)))) ⟩
    H • H • S • H • H • ε ≈⟨ cong refl (cong refl (cong refl (cong refl right-unit))) ⟩
    H • H • S • H • H ∎

  rhs : S • Z ≈ H • H • S • H • H
  rhs = begin
    S • Z ≡⟨ auto ⟩
    S • (H • H • S • H • H • S ^ p-1) ≈⟨ special-assoc (□ • □ • □ • □ • □ • □ • □) ((□ • □ • □ • □ • □ • □) • □) auto ⟩
    (S • H • H • S • H • H) • S ^ p-1 ≈⟨ cong (sym (axiom _QRel,_===_.comm-HHSHHS)) refl ⟩
    (H • H • S • H • H • S) • S ^ p-1 ≈⟨ special-assoc ((□ • □ • □ • □ • □ • □) • □) (□ • □ • □ • □ • □ • □ • □) auto ⟩
    H • H • S • H • H • (S • S ^ p-1) ≈⟨ cong refl (cong refl (cong refl (cong refl (cong refl lemma-S•S^p-1)))) ⟩
    H • H • S • H • H • ε ≈⟨ cong refl (cong refl (cong refl (cong refl right-unit))) ⟩
    H • H • S • H • H ∎

lemma-comm-𝑠-Z : ∀ {n} -> let open PB ((suc n) QRel,_===_) in
  𝑠 • Z ≈ Z • 𝑠
lemma-comm-𝑠-Z {n} = begin
  𝑠 • Z ≡⟨ auto ⟩
  (S • Z ^ toℕ 1/2) • Z ≈⟨ assoc ⟩
  S • (Z ^ toℕ 1/2 • Z) ≈⟨ cong refl (lemma-comm-wᵃwᵇ Z (toℕ 1/2) 1) ⟩
  S • (Z ^ 1 • Z ^ toℕ 1/2) ≡⟨ auto ⟩
  S • (Z • Z ^ toℕ 1/2) ≈⟨ sym assoc ⟩
  (S • Z) • Z ^ toℕ 1/2 ≈⟨ cong (sym lemma-comm-S-Z) refl ⟩
  (Z • S) • Z ^ toℕ 1/2 ≈⟨ assoc ⟩
  Z • (S • Z ^ toℕ 1/2) ≡⟨ auto ⟩
  Z • 𝑠 ∎
  where
  open PB ((suc n) QRel,_===_)
  open PP ((suc n) QRel,_===_)
  open SR word-setoid

lemma-CZ^k-% : ∀ {n} k -> let open PB ((suc (suc n)) QRel,_===_) in
  CZ ^ k ≈ CZ ^ (k Nat.% p)
lemma-CZ^k-% {n} k = begin
  CZ ^ k ≡⟨ Eq.cong (CZ ^_) (m≡m%n+[m/n]*n k p) ⟩
  CZ ^ (k Nat.% p Nat.+ k Nat./ p Nat.* p) ≈⟨ lemma-^-+ CZ (k Nat.% p) (k Nat./ p Nat.* p) ⟩
  CZ ^ (k Nat.% p) • CZ ^ (k Nat./ p Nat.* p) ≈⟨ cright refl' (Eq.cong (CZ ^_) (NP.*-comm (k Nat./ p) p)) ⟩
  CZ ^ (k Nat.% p) • CZ ^ (p Nat.* (k Nat./ p)) ≈⟨ sym (cright lemma-^^ CZ p (k Nat./ p)) ⟩
  CZ ^ (k Nat.% p) • (CZ ^ p) ^ (k Nat./ p) ≈⟨ cright lemma-^-cong (CZ ^ p) ε (k Nat./ p) (_≈_.axiom _QRel,_===_.order-CZ) ⟩
  CZ ^ (k Nat.% p) • ε ^ (k Nat./ p) ≈⟨ cright lemma-ε^k=ε (k Nat./ p) ⟩
  CZ ^ (k Nat.% p) • ε ≈⟨ right-unit ⟩
  CZ ^ (k % p) ∎
  where
  open PB ((suc (suc n)) QRel,_===_)
  open PP ((suc (suc n)) QRel,_===_)
  open SR word-setoid
  open import Data.Nat.DivMod using (m≡m%n+[m/n]*n)

lemma-Mg-CZ^k : ∀ {n} k -> let open PB ((suc (suc n)) QRel,_===_) in
  M g* • CZ ^ k ≈ CZ ^ (k Nat.* toℕ g) • M g*
lemma-Mg-CZ^k {n} k@0 = trans right-unit (sym left-unit)
  where
  open PB ((suc (suc n)) QRel,_===_)
lemma-Mg-CZ^k {n} k@1 = begin
  M g* • CZ ^ k ≈⟨ refl ⟩
  M g* • CZ ≈⟨ _≈_.axiom _QRel,_===_.semi-M↓CZ ⟩
  CZ^ g • M g* ≈⟨ refl ⟩
  CZ ^ toℕ g • M g* ≈⟨ cleft refl' (Eq.cong (CZ ^_) (Eq.sym (NP.*-identityˡ (toℕ g)))) ⟩
  CZ ^ (k Nat.* toℕ g) • M g* ∎
  where
  open PB ((suc (suc n)) QRel,_===_)
  open PP ((suc (suc n)) QRel,_===_)
  open SR word-setoid
lemma-Mg-CZ^k {n} k@(suc (suc k')) = begin
  M g* • CZ ^ k ≈⟨ refl ⟩
  M g* • CZ • CZ ^ (suc k') ≈⟨ sym assoc ⟩
  (M g* • CZ) • CZ ^ (suc k') ≈⟨ cleft lemma-Mg-CZ^k 1 ⟩
  (CZ ^ (1 Nat.* toℕ g) • M g*) • CZ ^ (suc k') ≈⟨ assoc ⟩
  CZ ^ (1 Nat.* toℕ g) • M g* • CZ ^ (suc k') ≈⟨ cright lemma-Mg-CZ^k (suc k') ⟩
  CZ ^ (1 Nat.* toℕ g) • CZ ^ (suc k' Nat.* toℕ g) • M g* ≈⟨ sym assoc ⟩
  (CZ ^ (1 Nat.* toℕ g) • CZ ^ (suc k' Nat.* toℕ g)) • M g* ≈⟨ cleft sym (lemma-^-+ CZ (1 Nat.* toℕ g) (suc k' Nat.* toℕ g)) ⟩
  (CZ ^ ((1 Nat.* toℕ g) Nat.+ (suc k' Nat.* toℕ g))) • M g* ≈⟨ cleft refl' (Eq.cong (CZ ^_) (Eq.sym (NP.*-distribʳ-+ (toℕ g) 1 (suc k')))) ⟩
  CZ ^ ((1 Nat.+ suc k') Nat.* toℕ g) • M g* ≈⟨ refl ⟩
  CZ ^ (k Nat.* toℕ g) • M g* ∎
  where
  open PB ((suc (suc n)) QRel,_===_)
  open PP ((suc (suc n)) QRel,_===_)
  open SR word-setoid

lemma-Mg^k-CZ : ∀ {n} k -> let open PB ((suc (suc n)) QRel,_===_) in
  M g* ^ k • CZ ≈ CZ^ (g ^′ k) • M g* ^ k
lemma-Mg^k-CZ {n} k@0 = begin
  M g* ^ k • CZ ≈⟨ left-unit ⟩
  CZ ≈⟨ sym right-unit ⟩
  CZ • ε ∎
  where
  open PB ((suc (suc n)) QRel,_===_)
  open PP ((suc (suc n)) QRel,_===_)
  open SR word-setoid
lemma-Mg^k-CZ {n} k@1 = begin
  M g* ^ k • CZ ≈⟨ refl ⟩
  M g* • CZ ≈⟨ _≈_.axiom _QRel,_===_.semi-M↓CZ ⟩
  CZ^ g • M g* ≈⟨ cleft refl' (Eq.cong CZ^ (Eq.sym (lemma-x^′1=x g))) ⟩
  CZ^ (g ^′ k) • M g* ^ k ∎
  where
  open PB ((suc (suc n)) QRel,_===_)
  open PP ((suc (suc n)) QRel,_===_)
  open SR word-setoid
lemma-Mg^k-CZ {n} k@(suc (suc k')) = begin
  M g* ^ k • CZ ≈⟨ refl ⟩
  (M g* • M g* ^ (suc k')) • CZ ≈⟨ assoc ⟩
  M g* • (M g* ^ (suc k') • CZ) ≈⟨ cright lemma-Mg^k-CZ (suc k') ⟩
  M g* • (CZ^ (g ^′ (suc k')) • M g* ^ (suc k')) ≈⟨ sym assoc ⟩
  (M g* • CZ^ (g ^′ (suc k'))) • M g* ^ (suc k') ≈⟨ cleft lemma-Mg-CZ^k (toℕ (g ^′ (suc k'))) ⟩
  (CZ ^ (toℕ (g ^′ (suc k')) Nat.* toℕ g) • M g*) • M g* ^ (suc k') ≈⟨ assoc ⟩
  CZ ^ (toℕ (g ^′ (suc k')) Nat.* toℕ g) • (M g* • M g* ^ (suc k')) ≈⟨ cleft lemma-CZ^k-% (toℕ (g ^′ (suc k')) Nat.* toℕ g) ⟩
  CZ ^ ((toℕ (g ^′ (suc k')) Nat.* toℕ g) % p) • (M g* • M g* ^ (suc k')) ≡⟨ Eq.cong (\ x -> CZ ^ x • (M g* • M g* ^ (suc k'))) (lemma-toℕ-% (g ^′ (suc k')) g) ⟩
  CZ ^ toℕ (g ^′ (suc k') * g) • (M g* • M g* ^ (suc k')) ≡⟨ Eq.cong (\ x -> CZ ^ toℕ x • (M g* • M g* ^ (suc k'))) (*-comm (g ^′ (suc k')) g) ⟩
  CZ ^ toℕ (g * g ^′ (suc k')) • (M g* • M g* ^ (suc k')) ≡⟨ auto ⟩
  CZ^ (g ^′ k) • M g* ^ k ∎
  where
  open PB ((suc (suc n)) QRel,_===_)
  open PP ((suc (suc n)) QRel,_===_)
  open SR word-setoid

lemma-M₋₁-CZ : ∀ {n} -> let open PB ((suc (suc n)) QRel,_===_) in
  M₋₁ • CZ ≈ CZ^ ((-'₁) .proj₁) • M₋₁
lemma-M₋₁-CZ {n} = begin
  M₋₁ • CZ ≈⟨ refl' (Eq.cong (_• CZ) (CL.aux-M≡M (suc n) -'₁ (g^ k₀) eqk)) ⟩
  M (g^ k₀) • CZ ≈⟨ cleft sym (_≈_.axiom (_QRel,_===_.M-power k₀)) ⟩
  M g* ^ (toℕ k₀) • CZ ≈⟨ lemma-Mg^k-CZ (toℕ k₀) ⟩
  CZ^ (g ^′ toℕ k₀) • M g* ^ (toℕ k₀) ≈⟨ cright _≈_.axiom (_QRel,_===_.M-power k₀) ⟩
  CZ^ (g ^′ toℕ k₀) • M (g^ k₀) ≈⟨ refl' (Eq.cong (CZ^ (g ^′ toℕ k₀) •_) (Eq.sym (CL.aux-M≡M (suc n) -'₁ (g^ k₀) eqk))) ⟩
  CZ^ (g ^′ toℕ k₀) • M₋₁ ≈⟨ cleft refl' (Eq.cong CZ^ (Eq.sym eqk)) ⟩
  CZ^ ((-'₁) .proj₁) • M₋₁ ∎
  where
  open PB ((suc (suc n)) QRel,_===_)
  open PP ((suc (suc n)) QRel,_===_)
  open SR word-setoid
--  open Primitive-Root-Modp' g* g-gen
  k₀ = inject₁ (log (-'₁))
  eqk : (-'₁) .proj₁ ≡ g ^′ toℕ k₀
  eqk = Eq.sym (lemma-log-inject (-'₁))

lemma-M₋₁CZM₋₁ : ∀ {n} -> let open PB ((suc (suc n)) QRel,_===_) in
  M₋₁ • CZ • M₋₁ ≈ CZ^ ((-'₁) .proj₁)
lemma-M₋₁CZM₋₁ {n} = begin
  M₋₁ • CZ • M₋₁ ≈⟨ sym assoc ⟩
  (M₋₁ • CZ) • M₋₁ ≈⟨ cong lemma-M₋₁-CZ refl ⟩
  (CZ^ ((-'₁) .proj₁) • M₋₁) • M₋₁ ≈⟨ assoc ⟩
  CZ^ ((-'₁) .proj₁) • (M₋₁ • M₋₁) ≈⟨ cong refl (CL.lemma-M₋₁^2 (suc n)) ⟩
  CZ^ ((-'₁) .proj₁) • ε ≈⟨ right-unit ⟩
  CZ^ ((-'₁) .proj₁) ∎
  where
  open PB ((suc (suc n)) QRel,_===_)
  open PP ((suc (suc n)) QRel,_===_)
  open SR word-setoid

lemma-M₋₁CZ⁻¹M₋₁ : ∀ {n} -> let open PB ((suc (suc n)) QRel,_===_) in
  M₋₁ • CZ^ ((-'₁) .proj₁) • M₋₁ ≈ CZ
lemma-M₋₁CZ⁻¹M₋₁ {n} = begin
  M₋₁ • CZ^ ((-'₁) .proj₁) • M₋₁ ≈⟨ cong refl (sym lemma-M₋₁-CZ) ⟩
  M₋₁ • (M₋₁ • CZ) ≈⟨ sym assoc ⟩
  (M₋₁ • M₋₁) • CZ ≈⟨ cong (CL.lemma-M₋₁^2 (suc n)) refl ⟩
  ε • CZ ≈⟨ left-unit ⟩
  CZ ∎
  where
  open PB ((suc (suc n)) QRel,_===_)
  open PP ((suc (suc n)) QRel,_===_)
  open SR word-setoid

lemma-HHCZHH : ∀ {n} -> let open PB ((suc (suc n)) QRel,_===_) in
  H • H • CZ • H • H ≈ CZ^ ((-'₁) .proj₁)
lemma-HHCZHH {n} = begin
  H • H • CZ • H • H ≈⟨ special-assoc (□ • □ • □ • □ • □) ((□ • □) • □ • (□ • □)) auto ⟩
  (H • H) • CZ • (H • H) ≈⟨ cong (_≈_.axiom _QRel,_===_.order-H) (cong refl (_≈_.axiom _QRel,_===_.order-H)) ⟩
  M₋₁ • CZ • M₋₁ ≈⟨ lemma-M₋₁CZM₋₁ ⟩
  CZ^ ((-'₁) .proj₁) ∎
  where
  open PB ((suc (suc n)) QRel,_===_)
  open PP ((suc (suc n)) QRel,_===_)
  open SR word-setoid
  open Pattern-Assoc

lemma-HHCZ⁻¹HH : ∀ {n} -> let open PB ((suc (suc n)) QRel,_===_) in
  H • H • CZ^ ((-'₁) .proj₁) • H • H ≈ CZ
lemma-HHCZ⁻¹HH {n} = begin
  H • H • CZ^ ((-'₁) .proj₁) • H • H ≈⟨ special-assoc (□ • □ • □ • □ • □) ((□ • □) • □ • (□ • □)) auto ⟩
  (H • H) • CZ^ ((-'₁) .proj₁) • (H • H) ≈⟨ cong (_≈_.axiom _QRel,_===_.order-H) (cong refl (_≈_.axiom _QRel,_===_.order-H)) ⟩
  M₋₁ • CZ^ ((-'₁) .proj₁) • M₋₁ ≈⟨ lemma-M₋₁CZ⁻¹M₋₁ ⟩
  CZ ∎
  where
  open PB ((suc (suc n)) QRel,_===_)
  open PP ((suc (suc n)) QRel,_===_)
  open SR word-setoid
  open Pattern-Assoc

lemma-S'CZS'⁻¹ : ∀ {n} -> let open PB ((suc (suc n)) QRel,_===_) in
  H • H • S • H • H • CZ • H • H • S ^ p-1 • H • H ≈ CZ
lemma-S'CZS'⁻¹ {n} = begin
  H • H • S • H • H • CZ • H • H • S ^ p-1 • H • H
    ≈⟨ special-assoc (□ • □ • □ • □ • □ • □ • □ • □ • □ • □ • □) (□ • □ • □ • (□ • □ • □ • □ • □) • □ • □ • □) auto ⟩
  H • H • S • (H • H • CZ • H • H) • S ^ p-1 • H • H
    ≈⟨ cong refl (cong refl (cong refl (cong lemma-HHCZHH refl))) ⟩
  H • H • S • CZ^ ((-'₁) .proj₁) • S ^ p-1 • H • H
    ≈⟨ cong refl (cong refl (trans (sym assoc) (trans (cong (word-comm 1 (toℕ ((-'₁) .proj₁)) (sym (_≈_.axiom _QRel,_===_.comm-CZ-S↓))) refl) assoc))) ⟩
  H • H • CZ^ ((-'₁) .proj₁) • S • S ^ p-1 • H • H
    ≈⟨ cong refl (cong refl (cong refl (trans (sym assoc) (cong lemma-S•S^p-1 refl)))) ⟩
  H • H • CZ^ ((-'₁) .proj₁) • ε • H • H
    ≈⟨ cong refl (cong refl (cong refl left-unit)) ⟩
  H • H • CZ^ ((-'₁) .proj₁) • H • H
    ≈⟨ lemma-HHCZ⁻¹HH ⟩
  CZ ∎
  where
  open PB ((suc (suc n)) QRel,_===_)
  open PP ((suc (suc n)) QRel,_===_)
  open SR word-setoid
  open Pattern-Assoc

lemma-S'⁻¹S' : ∀ {n} -> let open PB ((suc (suc n)) QRel,_===_) in
  H • H • S ^ p-1 • H • H • H • H • S • H • H ≈ ε
lemma-S'⁻¹S' {n} = begin
  H • H • S ^ p-1 • H • H • H • H • S • H • H
    ≈⟨ special-assoc (□ • □ • □ • □ • □ • □ • □ • □ • □ • □) (□ • □ • □ • (□ • □ • □ • □) • □ • □ • □) auto ⟩
  H • H • S ^ p-1 • (H • H • H • H) • S • H • H
    ≈⟨ cong refl (cong refl (cong refl (cong (CL.lemma-order-H (suc n)) refl))) ⟩
  H • H • S ^ p-1 • ε • S • H • H
    ≈⟨ cong refl (cong refl (cong refl left-unit)) ⟩
  H • H • S ^ p-1 • S • H • H
    ≈⟨ cong refl (cong refl (trans (sym assoc) (cong lemma-S^p-1•S refl))) ⟩
  H • H • ε • H • H
    ≈⟨ cong refl (cong refl left-unit) ⟩
  H • H • H • H
    ≈⟨ CL.lemma-order-H (suc n) ⟩
  ε ∎
  where
  open PB ((suc (suc n)) QRel,_===_)
  open PP ((suc (suc n)) QRel,_===_)
  open SR word-setoid
  open Pattern-Assoc

lemma-comm-S'-CZ : ∀ {n} -> let open PB ((suc (suc n)) QRel,_===_) in
  H • H • S • H • H • CZ ≈ CZ • H • H • S • H • H
lemma-comm-S'-CZ {n} = begin
  H • H • S • H • H • CZ
    ≈⟨ sym right-unit ⟩
  (H • H • S • H • H • CZ) • ε
    ≈⟨ cong refl (sym lemma-S'⁻¹S') ⟩
  (H • H • S • H • H • CZ) • (H • H • S ^ p-1 • H • H • H • H • S • H • H)
    ≈⟨ special-assoc ((□ • □ • □ • □ • □ • □) • (□ • □ • □ • □ • □ • □ • □ • □ • □ • □)) ((□ • □ • □ • □ • □ • □ • □ • □ • □ • □ • □) • □ • □ • □ • □ • □) auto ⟩
  (H • H • S • H • H • CZ • H • H • S ^ p-1 • H • H) • H • H • S • H • H
    ≈⟨ cong lemma-S'CZS'⁻¹ refl ⟩
  CZ • H • H • S • H • H ∎
  where
  open PB ((suc (suc n)) QRel,_===_)
  open PP ((suc (suc n)) QRel,_===_)
  open SR word-setoid
  open Pattern-Assoc

lemma-Mg↑-CZ^k : ∀ {n} k -> let open PB ((suc (suc n)) QRel,_===_) in
  M g* ↑ • CZ ^ k ≈ CZ ^ (k Nat.* toℕ g) • M g* ↑
lemma-Mg↑-CZ^k {n} k@0 = trans right-unit (sym left-unit)
  where
  open PB ((suc (suc n)) QRel,_===_)
lemma-Mg↑-CZ^k {n} k@1 = begin
  M g* ↑ • CZ ^ k ≈⟨ refl ⟩
  M g* ↑ • CZ ≈⟨ _≈_.axiom _QRel,_===_.semi-M↑CZ ⟩
  CZ^ g • M g* ↑ ≈⟨ refl ⟩
  CZ ^ toℕ g • M g* ↑ ≈⟨ cleft refl' (Eq.cong (CZ ^_) (Eq.sym (NP.*-identityˡ (toℕ g)))) ⟩
  CZ ^ (k Nat.* toℕ g) • M g* ↑ ∎
  where
  open PB ((suc (suc n)) QRel,_===_)
  open PP ((suc (suc n)) QRel,_===_)
  open SR word-setoid
lemma-Mg↑-CZ^k {n} k@(suc (suc k')) = begin
  M g* ↑ • CZ ^ k ≈⟨ refl ⟩
  M g* ↑ • CZ • CZ ^ (suc k') ≈⟨ sym assoc ⟩
  (M g* ↑ • CZ) • CZ ^ (suc k') ≈⟨ cleft lemma-Mg↑-CZ^k 1 ⟩
  (CZ ^ (1 Nat.* toℕ g) • M g* ↑) • CZ ^ (suc k') ≈⟨ assoc ⟩
  CZ ^ (1 Nat.* toℕ g) • M g* ↑ • CZ ^ (suc k') ≈⟨ cright lemma-Mg↑-CZ^k (suc k') ⟩
  CZ ^ (1 Nat.* toℕ g) • CZ ^ (suc k' Nat.* toℕ g) • M g* ↑ ≈⟨ sym assoc ⟩
  (CZ ^ (1 Nat.* toℕ g) • CZ ^ (suc k' Nat.* toℕ g)) • M g* ↑ ≈⟨ cleft sym (lemma-^-+ CZ (1 Nat.* toℕ g) (suc k' Nat.* toℕ g)) ⟩
  (CZ ^ ((1 Nat.* toℕ g) Nat.+ (suc k' Nat.* toℕ g))) • M g* ↑ ≈⟨ cleft refl' (Eq.cong (CZ ^_) (Eq.sym (NP.*-distribʳ-+ (toℕ g) 1 (suc k')))) ⟩
  CZ ^ ((1 Nat.+ suc k') Nat.* toℕ g) • M g* ↑ ≈⟨ refl ⟩
  CZ ^ (k Nat.* toℕ g) • M g* ↑ ∎
  where
  open PB ((suc (suc n)) QRel,_===_)
  open PP ((suc (suc n)) QRel,_===_)
  open SR word-setoid

lemma-Mg↑^k-CZ : ∀ {n} k -> let open PB ((suc (suc n)) QRel,_===_) in
  (M g* ↑) ^ k • CZ ≈ CZ^ (g ^′ k) • (M g* ↑) ^ k
lemma-Mg↑^k-CZ {n} k@0 = begin
  (M g* ↑) ^ k • CZ ≈⟨ left-unit ⟩
  CZ ≈⟨ sym right-unit ⟩
  CZ • ε ∎
  where
  open PB ((suc (suc n)) QRel,_===_)
  open PP ((suc (suc n)) QRel,_===_)
  open SR word-setoid
lemma-Mg↑^k-CZ {n} k@1 = begin
  (M g* ↑) ^ k • CZ ≈⟨ refl ⟩
  M g* ↑ • CZ ≈⟨ _≈_.axiom _QRel,_===_.semi-M↑CZ ⟩
  CZ^ g • M g* ↑ ≈⟨ cleft refl' (Eq.cong CZ^ (Eq.sym (lemma-x^′1=x g))) ⟩
  CZ^ (g ^′ k) • (M g* ↑) ^ k ∎
  where
  open PB ((suc (suc n)) QRel,_===_)
  open PP ((suc (suc n)) QRel,_===_)
  open SR word-setoid
lemma-Mg↑^k-CZ {n} k@(suc (suc k')) = begin
  (M g* ↑) ^ k • CZ ≈⟨ refl ⟩
  (M g* ↑ • (M g* ↑) ^ (suc k')) • CZ ≈⟨ assoc ⟩
  M g* ↑ • ((M g* ↑) ^ (suc k') • CZ) ≈⟨ cright lemma-Mg↑^k-CZ (suc k') ⟩
  M g* ↑ • (CZ^ (g ^′ (suc k')) • (M g* ↑) ^ (suc k')) ≈⟨ sym assoc ⟩
  (M g* ↑ • CZ^ (g ^′ (suc k'))) • (M g* ↑) ^ (suc k') ≈⟨ cleft lemma-Mg↑-CZ^k (toℕ (g ^′ (suc k'))) ⟩
  (CZ ^ (toℕ (g ^′ (suc k')) Nat.* toℕ g) • M g* ↑) • (M g* ↑) ^ (suc k') ≈⟨ assoc ⟩
  CZ ^ (toℕ (g ^′ (suc k')) Nat.* toℕ g) • (M g* ↑ • (M g* ↑) ^ (suc k')) ≈⟨ cleft lemma-CZ^k-% (toℕ (g ^′ (suc k')) Nat.* toℕ g) ⟩
  CZ ^ ((toℕ (g ^′ (suc k')) Nat.* toℕ g) % p) • (M g* ↑ • (M g* ↑) ^ (suc k')) ≡⟨ Eq.cong (\ x -> CZ ^ x • (M g* ↑ • (M g* ↑) ^ (suc k'))) (lemma-toℕ-% (g ^′ (suc k')) g) ⟩
  CZ ^ toℕ (g ^′ (suc k') * g) • (M g* ↑ • (M g* ↑) ^ (suc k')) ≡⟨ Eq.cong (\ x -> CZ ^ toℕ x • (M g* ↑ • (M g* ↑) ^ (suc k'))) (*-comm (g ^′ (suc k')) g) ⟩
  CZ ^ toℕ (g * g ^′ (suc k')) • (M g* ↑ • (M g* ↑) ^ (suc k')) ≡⟨ auto ⟩
  CZ^ (g ^′ k) • (M g* ↑) ^ k ∎
  where
  open PB ((suc (suc n)) QRel,_===_)
  open PP ((suc (suc n)) QRel,_===_)
  open SR word-setoid

lemma-M₋₁↑-CZ : ∀ {n} -> let open PB ((suc (suc n)) QRel,_===_) in
  M₋₁ ↑ • CZ ≈ CZ^ ((-'₁) .proj₁) • M₋₁ ↑
lemma-M₋₁↑-CZ {n} = begin
  M₋₁ ↑ • CZ ≈⟨ refl' (Eq.cong (\ x -> x ↑ • CZ) (CL.aux-M≡M n -'₁ (g^ k₀) eqk)) ⟩
  M (g^ k₀) ↑ • CZ ≈⟨ cleft sym bridge ⟩
  (M g* ^ (toℕ k₀)) ↑ • CZ ≈⟨ cleft refl' (lemma-↑^ (toℕ k₀) (M g*)) ⟩
  (M g* ↑) ^ (toℕ k₀) • CZ ≈⟨ lemma-Mg↑^k-CZ (toℕ k₀) ⟩
  CZ^ (g ^′ toℕ k₀) • (M g* ↑) ^ (toℕ k₀) ≈⟨ cright refl' (Eq.sym (lemma-↑^ (toℕ k₀) (M g*))) ⟩
  CZ^ (g ^′ toℕ k₀) • (M g* ^ (toℕ k₀)) ↑ ≈⟨ cright bridge ⟩
  CZ^ (g ^′ toℕ k₀) • M (g^ k₀) ↑ ≈⟨ refl' (Eq.cong (\ x -> CZ^ (g ^′ toℕ k₀) • x ↑) (Eq.sym (CL.aux-M≡M n -'₁ (g^ k₀) eqk))) ⟩
  CZ^ (g ^′ toℕ k₀) • M₋₁ ↑ ≈⟨ cleft refl' (Eq.cong CZ^ (Eq.sym eqk)) ⟩
  CZ^ ((-'₁) .proj₁) • M₋₁ ↑ ∎
  where
  open PB ((suc (suc n)) QRel,_===_)
  open PP ((suc (suc n)) QRel,_===_)
  open SR word-setoid
--  open Primitive-Root-Modp' g* g-gen
  k₀ = inject₁ (log (-'₁))
  eqk : (-'₁) .proj₁ ≡ g ^′ toℕ k₀
  eqk = Eq.sym (lemma-log-inject (-'₁))
  bridge : (M g* ^ toℕ k₀) ↑ ≈ M (g^ k₀) ↑
  bridge = lemma-cong↑ (M g* ^ toℕ k₀) (M (g^ k₀)) (PB.axiom (_QRel,_===_.M-power {n = n} k₀))

lemma-M₋₁↑CZM₋₁↑ : ∀ {n} -> let open PB ((suc (suc n)) QRel,_===_) in
  M₋₁ ↑ • CZ • M₋₁ ↑ ≈ CZ^ ((-'₁) .proj₁)
lemma-M₋₁↑CZM₋₁↑ {n} = begin
  M₋₁ ↑ • CZ • M₋₁ ↑ ≈⟨ sym assoc ⟩
  (M₋₁ ↑ • CZ) • M₋₁ ↑ ≈⟨ cong lemma-M₋₁↑-CZ refl ⟩
  (CZ^ ((-'₁) .proj₁) • M₋₁ ↑) • M₋₁ ↑ ≈⟨ assoc ⟩
  CZ^ ((-'₁) .proj₁) • (M₋₁ ↑ • M₋₁ ↑) ≈⟨ cong refl (lemma-cong↑ (M₋₁ • M₋₁) ε (CL.lemma-M₋₁^2 n)) ⟩
  CZ^ ((-'₁) .proj₁) • ε ≈⟨ right-unit ⟩
  CZ^ ((-'₁) .proj₁) ∎
  where
  open PB ((suc (suc n)) QRel,_===_)
  open PP ((suc (suc n)) QRel,_===_)
  open SR word-setoid

lemma-M₋₁↑CZ⁻¹M₋₁↑ : ∀ {n} -> let open PB ((suc (suc n)) QRel,_===_) in
  M₋₁ ↑ • CZ^ ((-'₁) .proj₁) • M₋₁ ↑ ≈ CZ
lemma-M₋₁↑CZ⁻¹M₋₁↑ {n} = begin
  M₋₁ ↑ • CZ^ ((-'₁) .proj₁) • M₋₁ ↑ ≈⟨ cong refl (sym lemma-M₋₁↑-CZ) ⟩
  M₋₁ ↑ • (M₋₁ ↑ • CZ) ≈⟨ sym assoc ⟩
  (M₋₁ ↑ • M₋₁ ↑) • CZ ≈⟨ cong (lemma-cong↑ (M₋₁ • M₋₁) ε (CL.lemma-M₋₁^2 n)) refl ⟩
  ε • CZ ≈⟨ left-unit ⟩
  CZ ∎
  where
  open PB ((suc (suc n)) QRel,_===_)
  open PP ((suc (suc n)) QRel,_===_)
  open SR word-setoid


lemma-HHCZHH↑ : ∀ {n} -> let open PB ((suc (suc n)) QRel,_===_) in
  H ↑ • H ↑ • CZ • H ↑ • H ↑ ≈ CZ^ ((-'₁) .proj₁)
lemma-HHCZHH↑ {n} = begin
  H ↑ • H ↑ • CZ • H ↑ • H ↑ ≈⟨ special-assoc (□ • □ • □ • □ • □) ((□ • □) • □ • (□ • □)) auto ⟩
  (H ↑ • H ↑) • CZ • (H ↑ • H ↑) ≈⟨ cong bridge (cong refl bridge) ⟩
  M₋₁ ↑ • CZ • M₋₁ ↑ ≈⟨ lemma-M₋₁↑CZM₋₁↑ ⟩
  CZ^ ((-'₁) .proj₁) ∎
  where
  open PB ((suc (suc n)) QRel,_===_)
  open PP ((suc (suc n)) QRel,_===_)
  open SR word-setoid
  open Pattern-Assoc
  bridge : H ↑ • H ↑ ≈ M₋₁ ↑
  bridge = lemma-cong↑ (H • H) M₋₁ (PB.axiom (_QRel,_===_.order-H {n = n}))

lemma-HHCZ⁻¹HH↑ : ∀ {n} -> let open PB ((suc (suc n)) QRel,_===_) in
  H ↑ • H ↑ • CZ^ ((-'₁) .proj₁) • H ↑ • H ↑ ≈ CZ
lemma-HHCZ⁻¹HH↑ {n} = begin
  H ↑ • H ↑ • CZ^ ((-'₁) .proj₁) • H ↑ • H ↑ ≈⟨ special-assoc (□ • □ • □ • □ • □) ((□ • □) • □ • (□ • □)) auto ⟩
  (H ↑ • H ↑) • CZ^ ((-'₁) .proj₁) • (H ↑ • H ↑) ≈⟨ cong bridge (cong refl bridge) ⟩
  M₋₁ ↑ • CZ^ ((-'₁) .proj₁) • M₋₁ ↑ ≈⟨ lemma-M₋₁↑CZ⁻¹M₋₁↑ ⟩
  CZ ∎
  where
  open PB ((suc (suc n)) QRel,_===_)
  open PP ((suc (suc n)) QRel,_===_)
  open SR word-setoid
  open Pattern-Assoc
  bridge : H ↑ • H ↑ ≈ M₋₁ ↑
  bridge = lemma-cong↑ (H • H) M₋₁ (PB.axiom (_QRel,_===_.order-H {n = n}))

lemma-S^p-1•S↑ : ∀ {n} -> let open PB ((suc (suc n)) QRel,_===_) in
  (S ↑) ^ p-1 • S ↑ ≈ ε
lemma-S^p-1•S↑ {n} = begin
  (S ↑) ^ p-1 • S ↑ ≈⟨ cleft refl' (Eq.sym (lemma-↑^ p-1 S)) ⟩
  (S ^ p-1) ↑ • S ↑ ≈⟨ bridge ⟩
  ε ∎
  where
  open PB ((suc (suc n)) QRel,_===_)
  open PP ((suc (suc n)) QRel,_===_)
  open SR word-setoid
  bridge : (S ^ p-1) ↑ • S ↑ ≈ ε
  bridge = lemma-cong↑ (S ^ p-1 • S) ε (lemma-S^p-1•S {n = n})
lemma-S•S^p-1↑ : ∀ {n} -> let open PB ((suc (suc n)) QRel,_===_) in
  S ↑ • (S ↑) ^ p-1 ≈ ε
lemma-S•S^p-1↑ {n} = begin
  S ↑ • (S ↑) ^ p-1 ≈⟨ cright refl' (Eq.sym (lemma-↑^ p-1 S)) ⟩
  S ↑ • (S ^ p-1) ↑ ≈⟨ lemma-cong↑ (S • S ^ p-1) ε (lemma-S•S^p-1 {n = n}) ⟩
  ε ∎
  where
  open PB ((suc (suc n)) QRel,_===_)
  open PP ((suc (suc n)) QRel,_===_)
  open SR word-setoid

lemma-S'CZS'⁻¹↑ : ∀ {n} -> let open PB ((suc (suc n)) QRel,_===_) in
  H ↑ • H ↑ • S ↑ • H ↑ • H ↑ • CZ • H ↑ • H ↑ • (S ↑) ^ p-1 • H ↑ • H ↑ ≈ CZ
lemma-S'CZS'⁻¹↑ {n} = begin
  H ↑ • H ↑ • S ↑ • H ↑ • H ↑ • CZ • H ↑ • H ↑ • (S ↑) ^ p-1 • H ↑ • H ↑
    ≈⟨ special-assoc (□ • □ • □ • □ • □ • □ • □ • □ • □ • □ • □) (□ • □ • □ • (□ • □ • □ • □ • □) • □ • □ • □) auto ⟩
  H ↑ • H ↑ • S ↑ • (H ↑ • H ↑ • CZ • H ↑ • H ↑) • (S ↑) ^ p-1 • H ↑ • H ↑
    ≈⟨ cong refl (cong refl (cong refl (cong lemma-HHCZHH↑ refl))) ⟩
  H ↑ • H ↑ • S ↑ • CZ^ ((-'₁) .proj₁) • (S ↑) ^ p-1 • H ↑ • H ↑
    ≈⟨ cong refl (cong refl (trans (sym assoc) (trans (cong (word-comm 1 (toℕ ((-'₁) .proj₁)) (sym (_≈_.axiom _QRel,_===_.comm-CZ-S↑))) refl) assoc))) ⟩
  H ↑ • H ↑ • CZ^ ((-'₁) .proj₁) • S ↑ • (S ↑) ^ p-1 • H ↑ • H ↑
    ≈⟨ cong refl (cong refl (cong refl (trans (sym assoc) (cong lemma-S•S^p-1↑ refl)))) ⟩
  H ↑ • H ↑ • CZ^ ((-'₁) .proj₁) • ε • H ↑ • H ↑
    ≈⟨ cong refl (cong refl (cong refl left-unit)) ⟩
  H ↑ • H ↑ • CZ^ ((-'₁) .proj₁) • H ↑ • H ↑
    ≈⟨ lemma-HHCZ⁻¹HH↑ ⟩
  CZ ∎
  where
  open PB ((suc (suc n)) QRel,_===_)
  open PP ((suc (suc n)) QRel,_===_)
  open SR word-setoid
  open Pattern-Assoc

lemma-S'⁻¹S'↑ : ∀ {n} -> let open PB ((suc (suc n)) QRel,_===_) in
  H ↑ • H ↑ • (S ↑) ^ p-1 • H ↑ • H ↑ • H ↑ • H ↑ • S ↑ • H ↑ • H ↑ ≈ ε
lemma-S'⁻¹S'↑ {n} = begin
  H ↑ • H ↑ • (S ↑) ^ p-1 • H ↑ • H ↑ • H ↑ • H ↑ • S ↑ • H ↑ • H ↑
    ≈⟨ special-assoc (□ • □ • □ • □ • □ • □ • □ • □ • □ • □) (□ • □ • □ • (□ • □ • □ • □) • □ • □ • □) auto ⟩
  H ↑ • H ↑ • (S ↑) ^ p-1 • (H ↑ • H ↑ • H ↑ • H ↑) • S ↑ • H ↑ • H ↑
    ≈⟨ cong refl (cong refl (cong refl (cong order-H↑ refl))) ⟩
  H ↑ • H ↑ • (S ↑) ^ p-1 • ε • S ↑ • H ↑ • H ↑
    ≈⟨ cong refl (cong refl (cong refl left-unit)) ⟩
  H ↑ • H ↑ • (S ↑) ^ p-1 • S ↑ • H ↑ • H ↑
    ≈⟨ cong refl (cong refl (trans (sym assoc) (cong lemma-S^p-1•S↑ refl))) ⟩
  H ↑ • H ↑ • ε • H ↑ • H ↑
    ≈⟨ cong refl (cong refl left-unit) ⟩
  H ↑ • H ↑ • H ↑ • H ↑
    ≈⟨ order-H↑ ⟩
  ε ∎
  where
  open PB ((suc (suc n)) QRel,_===_)
  open PP ((suc (suc n)) QRel,_===_)
  open SR word-setoid
  open Pattern-Assoc
  order-H↑ : H ↑ • H ↑ • H ↑ • H ↑ ≈ ε
  order-H↑ = begin
    H ↑ • H ↑ • H ↑ • H ↑ ≡⟨ Eq.cong _↑ auto ⟩
    (H • H • H • H) ↑ ≈⟨ lemma-cong↑ (H ^ 4) ε (CL.lemma-order-H n) ⟩
    ε ∎

lemma-comm-S'-CZ↑ : ∀ {n} -> let open PB ((suc (suc n)) QRel,_===_) in
  H ↑ • H ↑ • S ↑ • H ↑ • H ↑ • CZ ≈ CZ • H ↑ • H ↑ • S ↑ • H ↑ • H ↑
lemma-comm-S'-CZ↑ {n} = begin
  H ↑ • H ↑ • S ↑ • H ↑ • H ↑ • CZ
    ≈⟨ sym right-unit ⟩
  (H ↑ • H ↑ • S ↑ • H ↑ • H ↑ • CZ) • ε
    ≈⟨ cong refl (sym lemma-S'⁻¹S'↑) ⟩
  (H ↑ • H ↑ • S ↑ • H ↑ • H ↑ • CZ) • (H ↑ • H ↑ • (S ↑) ^ p-1 • H ↑ • H ↑ • H ↑ • H ↑ • S ↑ • H ↑ • H ↑)
    ≈⟨ special-assoc ((□ • □ • □ • □ • □ • □) • (□ • □ • □ • □ • □ • □ • □ • □ • □ • □)) ((□ • □ • □ • □ • □ • □ • □ • □ • □ • □ • □) • □ • □ • □ • □ • □) auto ⟩
  (H ↑ • H ↑ • S ↑ • H ↑ • H ↑ • CZ • H ↑ • H ↑ • (S ↑) ^ p-1 • H ↑ • H ↑) • H ↑ • H ↑ • S ↑ • H ↑ • H ↑
    ≈⟨ cong lemma-S'CZS'⁻¹↑ refl ⟩
  CZ • H ↑ • H ↑ • S ↑ • H ↑ • H ↑ ∎
  where
  open PB ((suc (suc n)) QRel,_===_)
  open PP ((suc (suc n)) QRel,_===_)
  open SR word-setoid
  open Pattern-Assoc

lemma-Z↑ : ∀ {n} -> Z {n} ↑ ≡ H ↑ • H ↑ • S ↑ • H ↑ • H ↑ • (S ↑) ^ p-1
lemma-Z↑ {n} = begin
  Z ↑ ≡⟨ auto ⟩
  (H • H • S • H • H • S ^ p-1) ↑ ≡⟨ auto ⟩
  H ↑ • H ↑ • S ↑ • H ↑ • H ↑ • (S ^ p-1) ↑ ≡⟨ Eq.cong (\ x -> H ↑ • H ↑ • S ↑ • H ↑ • H ↑ • x) (lemma-↑^ p-1 S) ⟩
  H ↑ • H ↑ • S ↑ • H ↑ • H ↑ • (S ↑) ^ p-1 ∎
  where open ≡-Reasoning

lemma-comm-Z↑-CZ : ∀ {n} -> let open PB ((suc (suc n)) QRel,_===_) in
  Z ↑ • CZ ≈ CZ • Z ↑
lemma-comm-Z↑-CZ {n} = begin
  Z ↑ • CZ ≈⟨ refl' (Eq.cong (_• CZ) lemma-Z↑) ⟩
  (H ↑ • H ↑ • S ↑ • H ↑ • H ↑ • (S ↑) ^ p-1) • CZ
    ≈⟨ special-assoc ((□ • □ • □ • □ • □ • □) • □) (□ • □ • □ • □ • □ • (□ • □)) auto ⟩
  H ↑ • H ↑ • S ↑ • H ↑ • H ↑ • ((S ↑) ^ p-1 • CZ)
    ≈⟨ cong refl (cong refl (cong refl (cong refl (cong refl (word-comm p-1 1 (sym (_≈_.axiom _QRel,_===_.comm-CZ-S↑))))))) ⟩
  H ↑ • H ↑ • S ↑ • H ↑ • H ↑ • (CZ • (S ↑) ^ p-1)
    ≈⟨ special-assoc (□ • □ • □ • □ • □ • (□ • □)) ((□ • □ • □ • □ • □ • □) • □) auto ⟩
  (H ↑ • H ↑ • S ↑ • H ↑ • H ↑ • CZ) • (S ↑) ^ p-1
    ≈⟨ cong lemma-comm-S'-CZ↑ refl ⟩
  (CZ • H ↑ • H ↑ • S ↑ • H ↑ • H ↑) • (S ↑) ^ p-1
    ≈⟨ by-assoc auto ⟩
  CZ • (H ↑ • H ↑ • S ↑ • H ↑ • H ↑ • (S ↑) ^ p-1)
    ≈⟨ refl' (Eq.cong (CZ •_) (Eq.sym lemma-Z↑)) ⟩
  CZ • Z ↑ ∎
  where
  open PB ((suc (suc n)) QRel,_===_)
  open PP ((suc (suc n)) QRel,_===_)
  open SR word-setoid
  open Pattern-Assoc

lemma-𝑠↑ : ∀ {n} -> 𝑠 {n} ↑ ≡ S ↑ • (Z ↑) ^ toℕ 1/2
lemma-𝑠↑ {n} = begin
  𝑠 ↑ ≡⟨ auto ⟩
  (S • Z ^ toℕ 1/2) ↑ ≡⟨ auto ⟩
  S ↑ • (Z ^ toℕ 1/2) ↑ ≡⟨ Eq.cong (S ↑ •_) (lemma-↑^ (toℕ 1/2) Z) ⟩
  S ↑ • (Z ↑) ^ toℕ 1/2 ∎
  where open ≡-Reasoning

lemma-comm-𝑠↑-CZ : ∀ {n} -> let open PB ((suc (suc n)) QRel,_===_) in
  𝑠 ↑ • CZ ≈ CZ • 𝑠 ↑
lemma-comm-𝑠↑-CZ {n} = begin
  𝑠 ↑ • CZ ≈⟨ refl' (Eq.cong (_• CZ) lemma-𝑠↑) ⟩
  (S ↑ • (Z ↑) ^ toℕ 1/2) • CZ ≈⟨ assoc ⟩
  S ↑ • ((Z ↑) ^ toℕ 1/2 • CZ) ≈⟨ cong refl (word-comm (toℕ 1/2) 1 lemma-comm-Z↑-CZ) ⟩
  S ↑ • (CZ ^ 1 • (Z ↑) ^ toℕ 1/2) ≡⟨ auto ⟩
  S ↑ • (CZ • (Z ↑) ^ toℕ 1/2) ≈⟨ sym assoc ⟩
  (S ↑ • CZ) • (Z ↑) ^ toℕ 1/2 ≈⟨ cong (sym (_≈_.axiom _QRel,_===_.comm-CZ-S↑)) refl ⟩
  (CZ • S ↑) • (Z ↑) ^ toℕ 1/2 ≈⟨ assoc ⟩
  CZ • (S ↑ • (Z ↑) ^ toℕ 1/2) ≈⟨ refl' (Eq.cong (CZ •_) (Eq.sym lemma-𝑠↑)) ⟩
  CZ • 𝑠 ↑ ∎
  where
  open PB ((suc (suc n)) QRel,_===_)
  open PP ((suc (suc n)) QRel,_===_)
  open SR word-setoid

lemma-comm-Z-CZ : ∀ {n} -> let open PB ((suc (suc n)) QRel,_===_) in
  Z • CZ ≈ CZ • Z
lemma-comm-Z-CZ {n} = begin
  Z • CZ ≡⟨ auto ⟩
  (H • H • S • H • H • S ^ p-1) • CZ ≈⟨ special-assoc ((□ • □ • □ • □ • □ • □) • □) (□ • □ • □ • □ • □ • (□ • □)) auto ⟩
  H • H • S • H • H • (S ^ p-1 • CZ) ≈⟨ cong refl (cong refl (cong refl (cong refl (cong refl (word-comm p-1 1 (sym (_≈_.axiom _QRel,_===_.comm-CZ-S↓))))))) ⟩
  H • H • S • H • H • (CZ • S ^ p-1) ≈⟨ special-assoc (□ • □ • □ • □ • □ • (□ • □)) ((□ • □ • □ • □ • □ • □) • □) auto ⟩
  (H • H • S • H • H • CZ) • S ^ p-1 ≈⟨ cong lemma-comm-S'-CZ refl ⟩
  (CZ • H • H • S • H • H) • S ^ p-1 ≈⟨ by-assoc auto ⟩
  CZ • (H • H • S • H • H • S ^ p-1) ≡⟨ auto ⟩
  CZ • Z ∎
  where
  open PB ((suc (suc n)) QRel,_===_)
  open PP ((suc (suc n)) QRel,_===_)
  open SR word-setoid
  open Pattern-Assoc

lemma-comm-𝑠-CZ : ∀ {n} -> let open PB ((suc (suc n)) QRel,_===_) in
  𝑠 • CZ ≈ CZ • 𝑠
lemma-comm-𝑠-CZ {n} = begin
  𝑠 • CZ ≡⟨ auto ⟩
  (S • Z ^ toℕ 1/2) • CZ ≈⟨ assoc ⟩
  S • (Z ^ toℕ 1/2 • CZ) ≈⟨ cong refl (word-comm (toℕ 1/2) 1 lemma-comm-Z-CZ) ⟩
  S • (CZ ^ 1 • Z ^ toℕ 1/2) ≡⟨ auto ⟩
  S • (CZ • Z ^ toℕ 1/2) ≈⟨ sym assoc ⟩
  (S • CZ) • Z ^ toℕ 1/2 ≈⟨ cong (sym (_≈_.axiom _QRel,_===_.comm-CZ-S↓)) refl ⟩
  (CZ • S) • Z ^ toℕ 1/2 ≈⟨ assoc ⟩
  CZ • (S • Z ^ toℕ 1/2) ≡⟨ auto ⟩
  CZ • 𝑠 ∎
  where
  open PB ((suc (suc n)) QRel,_===_)
  open PP ((suc (suc n)) QRel,_===_)
  open SR word-setoid



-- ====================================================================
-- Foundational lemma + cascade (tail-c10 / tail-c11) for the Simplified
-- presentation: a copy of the verified Clifford cascade, repointed to
-- the -S base lemmas.  These give RHS_simp ≈ RHS_orig·X·Z in Simplified.
-- ====================================================================
module _ (n : ℕ) where
  open PB ((₁₊ n) QRel,_===_)
  open PP ((₁₊ n) QRel,_===_)
  open SR word-setoid
  open Lemmas1-S n using (lemma-order-Z ; lemma-comm-Z-S)

  -- Z and S commute, hence Z and 𝑠 commute, and we can split powers.
  cZS : Z • S ≈ S • Z
  cZS = lemma-comm-Z-S

  -- (Z^½)^(p-1) · Z^½ = Z^(½·p) = ε
  zhalf-p : (Z^ 1/2) ^ p-1 • Z^ 1/2 ≈ ε
  zhalf-p = begin
    (Z ^ toℕ 1/2) ^ p-1 • Z ^ toℕ 1/2
      ≈⟨ cleft (lemma-^^ Z (toℕ 1/2) p-1) ⟩
    Z ^ (toℕ 1/2 Nat.* p-1) • Z ^ toℕ 1/2
      ≈⟨ sym (lemma-^-+ Z (toℕ 1/2 Nat.* p-1) (toℕ 1/2)) ⟩
    Z ^ (toℕ 1/2 Nat.* p-1 Nat.+ toℕ 1/2)
      ≡⟨ Eq.cong (Z ^_) lemma-arith ⟩
    Z ^ (p Nat.* toℕ 1/2)
      ≈⟨ sym (lemma-^^ Z p (toℕ 1/2)) ⟩
    (Z ^ p) ^ toℕ 1/2
      ≈⟨ lemma-^-cong (Z ^ p) ε (toℕ 1/2) lemma-order-Z ⟩
    ε ^ toℕ 1/2
      ≈⟨ lemma-ε^k=ε (toℕ 1/2) ⟩
    ε ∎
    where
    -- toℕ½·(p-1) + toℕ½ = p·toℕ½
    lemma-arith : toℕ 1/2 Nat.* p-1 Nat.+ toℕ 1/2 ≡ p Nat.* toℕ 1/2
    lemma-arith = Eq.trans (NP.+-comm (toℕ 1/2 Nat.* p-1) (toℕ 1/2))
                           (Eq.cong (toℕ 1/2 Nat.+_) (NP.*-comm (toℕ 1/2) p-1))

  -- the key lemma: S^(p-1) ≈ 𝑠^(p-1) • Z^½
  lemma-S⁻¹=𝑠⁻¹Z : S ^ p-1 ≈ 𝑠 ^ p-1 • Z^ 1/2
  lemma-S⁻¹=𝑠⁻¹Z = begin
    S ^ p-1
      ≈⟨ sym right-unit ⟩
    S ^ p-1 • ε
      ≈⟨ cright (sym zhalf-p) ⟩
    S ^ p-1 • ((Z^ 1/2) ^ p-1 • Z^ 1/2)
      ≈⟨ sym assoc ⟩
    (S ^ p-1 • (Z^ 1/2) ^ p-1) • Z^ 1/2
      ≈⟨ cleft (sym (lemma-^-• S (Z^ 1/2) p-1 (word-comm 1 (toℕ 1/2) (sym cZS)))) ⟩
    (S • Z^ 1/2) ^ p-1 • Z^ 1/2
      ≡⟨ Eq.refl ⟩
    𝑠 ^ p-1 • Z^ 1/2 ∎


-- Base-level (₁₊ m) X-conjugations, lifted into C10 afterwards.

module C10Base (m : ℕ) where
  open PB ((₁₊ m) QRel,_===_)
  open PP ((₁₊ m) QRel,_===_)
  open SR word-setoid
  open Lemmas1-S m using (lemma-order-𝑠 ; lemma-order-H)
  open Lemmas-Clifford-S using (lemma-Induction)
  open Lemmas1b-S m using (conj-H-X^k ; lemma-HH-Z)

  𝑠𝑠⁻¹ : 𝑠 • 𝑠 ^ p-1 ≈ ε
  𝑠𝑠⁻¹ = lemma-order-𝑠
  𝑠⁻¹𝑠 : 𝑠 ^ p-1 • 𝑠 ≈ ε
  𝑠⁻¹𝑠 = trans (word-comm p-1 1 refl) 𝑠𝑠⁻¹

  conj-𝑠-X^k : ∀ a → 𝑠 • X ^ a ≈ (X ^ a • Z ^ a) • 𝑠
  conj-𝑠-X^k a = trans (lemma-Induction lemma-conj-𝑠-X a)
                       (cleft (lemma-^-• X Z a (axiom comm-X-Z)))

  -- X^a • 𝑠⁻¹  ≈  𝑠⁻¹ • X^a • Z^a
  bX𝑠 : ∀ a → X ^ a • 𝑠 ^ p-1 ≈ 𝑠 ^ p-1 • X ^ a • Z ^ a
  bX𝑠 a = begin
    X ^ a • 𝑠 ^ p-1                            ≈⟨ sym left-unit ⟩
    ε • (X ^ a • 𝑠 ^ p-1)                      ≈⟨ cleft (sym 𝑠⁻¹𝑠) ⟩
    (𝑠 ^ p-1 • 𝑠) • (X ^ a • 𝑠 ^ p-1)          ≈⟨ assoc ⟩
    𝑠 ^ p-1 • (𝑠 • (X ^ a • 𝑠 ^ p-1))          ≈⟨ cright (sym assoc) ⟩
    𝑠 ^ p-1 • ((𝑠 • X ^ a) • 𝑠 ^ p-1)          ≈⟨ cright (cleft (conj-𝑠-X^k a)) ⟩
    𝑠 ^ p-1 • (((X ^ a • Z ^ a) • 𝑠) • 𝑠 ^ p-1) ≈⟨ cright assoc ⟩
    𝑠 ^ p-1 • ((X ^ a • Z ^ a) • (𝑠 • 𝑠 ^ p-1)) ≈⟨ cright (cright 𝑠𝑠⁻¹) ⟩
    𝑠 ^ p-1 • ((X ^ a • Z ^ a) • ε)            ≈⟨ cright right-unit ⟩
    𝑠 ^ p-1 • (X ^ a • Z ^ a) ∎

  -- X^a • H  ≈  H • (Z⁻¹)^a    (H-conjugation of X from the right)
  bXH : ∀ a → X ^ a • H ≈ H • (Z^ (- 1ₚ)) ^ a
  bXH a = begin
    X ^ a • H                              ≈⟨ sym left-unit ⟩
    ε • (X ^ a • H)                        ≈⟨ cleft (sym lemma-order-H) ⟩
    H ^ 4 • (X ^ a • H)                    ≈⟨ assoc ⟩
    H • (H ^ 3 • (X ^ a • H))              ≈⟨ cright claim ⟩
    H • (Z^ (- 1ₚ)) ^ a ∎
    where
    claim : H ^ 3 • (X ^ a • H) ≈ (Z^ (- 1ₚ)) ^ a
    claim = begin
      H ^ 3 • (X ^ a • H)                  ≈⟨ cleft (lemma-^-+ H 2 1) ⟩
      (H ^ 2 • H) • (X ^ a • H)            ≈⟨ assoc ⟩
      H ^ 2 • (H • (X ^ a • H))            ≈⟨ cright (sym assoc) ⟩
      H ^ 2 • ((H • X ^ a) • H)            ≈⟨ cright (cleft (conj-H-X^k a)) ⟩
      H ^ 2 • ((Z ^ a • H) • H)            ≈⟨ cright assoc ⟩
      H ^ 2 • (Z ^ a • (H • H))            ≈⟨ sym assoc ⟩
      (H ^ 2 • Z ^ a) • (H • H)            ≈⟨ cleft (lemma-Induction lemma-HH-Z a) ⟩
      ((Z^ (- 1ₚ)) ^ a • (H • H)) • (H • H) ≈⟨ assoc ⟩
      (Z^ (- 1ₚ)) ^ a • ((H • H) • (H • H)) ≈⟨ cright (by-assoc auto) ⟩
      (Z^ (- 1ₚ)) ^ a • H ^ 4               ≈⟨ cright lemma-order-H ⟩
      (Z^ (- 1ₚ)) ^ a • ε                   ≈⟨ right-unit ⟩
      (Z^ (- 1ₚ)) ^ a ∎


------------------------------------------------------------------------
-- Soundness of the simplified selinger-c10 in the Clifford presentation.
-- We work on the ↑ qubit at level (₂₊ m); base conjugation lemmas
-- (level ₁₊ m) are lifted via cong↑ / lemma-↑^.
------------------------------------------------------------------------

module C10 (m : ℕ) where
  open PB ((₂₊ m) QRel,_===_)
  open PP ((₂₊ m) QRel,_===_)
  open SR word-setoid
  open Pattern-Assoc
  open Lemmas-Clifford-S using (lemma-cong↑ ; lemma-↑^ ; lemma-Induction ; lemma-comm-Z-w↑)
  open Lemmas1b-S m using (conj-H-X^k ; conj-H-Z ; lemma-HH-Z ; lemma-HH-X)
  -- Z↓ lives at level ₂₊ m, i.e. the base Z of Lemmas1 (₁₊ m)
  order-Z↓ : (Z ↓) ^ p ≈ ε
  order-Z↓ = Lemmas1-S.lemma-order-Z (₁₊ m)

  z : ℕ
  z = toℕ 1/2

  -- foundational, lifted to the ↑ qubit:  (S↑)^(p-1) ≈ (𝑠↑)^(p-1) • (Z↑)^z
  fnd↑ : (S ↑) ^ p-1 ≈ (𝑠 ↑) ^ p-1 • (Z ↑) ^ z
  fnd↑ = trans (refl' (Eq.sym (lemma-↑^ p-1 S)))
         (trans (lemma-cong↑ _ _ (lemma-S⁻¹=𝑠⁻¹Z m))
                (refl' (Eq.cong₂ _•_ (lemma-↑^ p-1 𝑠) (lemma-↑^ z Z))))

  -- foundational on the ↓ qubit (↓ is the identity):  S^(p-1) ≈ 𝑠^(p-1) • Z^z
  fnd↓ : S ^ p-1 ≈ 𝑠 ^ p-1 • Z^ 1/2
  fnd↓ = lemma-S⁻¹=𝑠⁻¹Z (₁₊ m)

  -- Z↑ through H↑  (Z•H = H•X)
  qZH : ∀ a → (Z ↑) ^ a • (H ↑) ≈ (H ↑) • (X ↑) ^ a
  qZH a = trans (refl' (Eq.cong (_• (H ↑)) (Eq.sym (lemma-↑^ a Z))))
          (trans (lemma-cong↑ _ _ (PB.sym (conj-H-X^k a)))
                 (refl' (Eq.cong ((H ↑) •_) (lemma-↑^ a X))))

  -- Z↑ commutes with (𝑠↑)^(p-1)
  qZ𝑠 : ∀ a → (Z ↑) ^ a • (𝑠 ↑) ^ p-1 ≈ (𝑠 ↑) ^ p-1 • (Z ↑) ^ a
  qZ𝑠 a = word-comm a p-1 (lemma-cong↑ _ _ (PB.sym (lemma-comm-𝑠-Z {m})))

  -- Z↑ commutes with CZ
  qZCZ : ∀ a → (Z ↑) ^ a • CZ ≈ CZ • (Z ↑) ^ a
  qZCZ a = word-comm a 1 (lemma-comm-Z↑-CZ {m})

  -- X↑ through (𝑠↑)^(p-1)
  qX𝑠 : ∀ a → (X ↑) ^ a • (𝑠 ↑) ^ p-1 ≈ (𝑠 ↑) ^ p-1 • (X ↑) ^ a • (Z ↑) ^ a
  qX𝑠 a = trans (refl' (Eq.cong₂ _•_ (Eq.sym (lemma-↑^ a X)) (Eq.sym (lemma-↑^ p-1 𝑠))))
          (trans (lemma-cong↑ _ _ (C10Base.bX𝑠 m a))
                 (refl' (Eq.cong₂ _•_ (lemma-↑^ p-1 𝑠)
                                      (Eq.cong₂ _•_ (lemma-↑^ a X) (lemma-↑^ a Z)))))

  -- X↑ through H↑  (X•H = H•Z⁻¹), flat exponent
  qXH : ∀ a → (X ↑) ^ a • (H ↑) ≈ (H ↑) • (Z ↑) ^ (toℕ (- 1ₚ) Nat.* a)
  qXH a = trans (refl' (Eq.cong (_• (H ↑)) (Eq.sym (lemma-↑^ a X))))
          (trans (lemma-cong↑ _ _ (C10Base.bXH m a))
          (trans (refl' (Eq.cong ((H ↑) •_)
                                 (Eq.trans (lemma-↑^ a (Z^ (- 1ₚ)))
                                           (Eq.cong (_^ a) (lemma-↑^ (toℕ (- 1ₚ)) Z)))))
                 (cright (lemma-^^ (Z ↑) (toℕ (- 1ₚ)) a))))

  -- CZ • X↑^a ≈ X↑^a • Z↓^a • CZ
  relpow : ∀ a → CZ • (X ↑) ^ a ≈ (X ↑) ^ a • (Z ↓) ^ a • CZ
  relpow a = trans (lemma-Induction (trans (axiom rel-X↑-CZ) (sym assoc)) a)
                   (trans (cleft (lemma-^-• (X ↑) (Z ↓) a (sym (lemma-comm-Z-w↑ X)))) assoc)

  -- Z↓^a • Z↓^(-a) ≈ ε
  Z↓inv : ∀ a → (Z ↓) ^ a • ((Z ↓) ^ toℕ (- 1ₚ)) ^ a ≈ ε
  Z↓inv a = begin
    (Z ↓) ^ a • ((Z ↓) ^ toℕ (- 1ₚ)) ^ a    ≈⟨ cright (lemma-^^ (Z ↓) (toℕ (- 1ₚ)) a) ⟩
    (Z ↓) ^ a • (Z ↓) ^ (toℕ (- 1ₚ) Nat.* a) ≈⟨ sym (lemma-^-+ (Z ↓) a (toℕ (- 1ₚ) Nat.* a)) ⟩
    (Z ↓) ^ (a Nat.+ toℕ (- 1ₚ) Nat.* a)     ≡⟨ Eq.cong ((Z ↓) ^_) arith ⟩
    (Z ↓) ^ (p Nat.* a)                     ≈⟨ sym (lemma-^^ (Z ↓) p a) ⟩
    ((Z ↓) ^ p) ^ a                         ≈⟨ lemma-^-cong ((Z ↓) ^ p) ε a order-Z↓ ⟩
    ε ^ a                                   ≈⟨ lemma-ε^k=ε a ⟩
    ε ∎
    where
    arith : a Nat.+ toℕ (- 1ₚ) Nat.* a ≡ p Nat.* a
    arith = Eq.cong (λ t → a Nat.+ t Nat.* a) lemma-toℕ-1ₚ

  -- X↑ through CZ  (X↑•CZ ≈ CZ•X↑•Z↓⁻¹), flat exponent
  qXCZ : ∀ a → (X ↑) ^ a • CZ ≈ CZ • (X ↑) ^ a • (Z ↓) ^ (toℕ (- 1ₚ) Nat.* a)
  qXCZ a = begin
    (X ↑) ^ a • CZ
      ≈⟨ sym right-unit ⟩
    ((X ↑) ^ a • CZ) • ε
      ≈⟨ cright (sym (Z↓inv a)) ⟩
    ((X ↑) ^ a • CZ) • ((Z ↓) ^ a • ((Z ↓) ^ toℕ (- 1ₚ)) ^ a)
      ≈⟨ sym assoc ⟩
    (((X ↑) ^ a • CZ) • (Z ↓) ^ a) • ((Z ↓) ^ toℕ (- 1ₚ)) ^ a
      ≈⟨ cleft step ⟩
    (CZ • (X ↑) ^ a) • ((Z ↓) ^ toℕ (- 1ₚ)) ^ a
      ≈⟨ assoc ⟩
    CZ • (X ↑) ^ a • ((Z ↓) ^ toℕ (- 1ₚ)) ^ a
      ≈⟨ cright (cright (lemma-^^ (Z ↓) (toℕ (- 1ₚ)) a)) ⟩
    CZ • (X ↑) ^ a • (Z ↓) ^ (toℕ (- 1ₚ) Nat.* a) ∎
    where
    step : ((X ↑) ^ a • CZ) • (Z ↓) ^ a ≈ CZ • (X ↑) ^ a
    step = begin
      ((X ↑) ^ a • CZ) • (Z ↓) ^ a   ≈⟨ assoc ⟩
      (X ↑) ^ a • (CZ • (Z ↓) ^ a)   ≈⟨ cright (sym (word-comm a 1 (lemma-comm-Z-CZ {m}))) ⟩
      (X ↑) ^ a • ((Z ↓) ^ a • CZ)   ≈⟨ sym (relpow a) ⟩
      CZ • (X ↑) ^ a ∎

  ----------------------------------------------------------------------
  -- cross-qubit and Pauli commutations used by the cascade
  ----------------------------------------------------------------------
  cZ↑sd : ∀ a → (Z ↑) ^ a • (𝑠 ↓) ^ p-1 ≈ (𝑠 ↓) ^ p-1 • (Z ↑) ^ a
  cZ↑sd a = word-comm a p-1 (sym (lemma-comm-𝑠-w↑ {m} Z))
  cX↑sd : ∀ a → (X ↑) ^ a • (𝑠 ↓) ^ p-1 ≈ (𝑠 ↓) ^ p-1 • (X ↑) ^ a
  cX↑sd a = word-comm a p-1 (sym (lemma-comm-𝑠-w↑ {m} X))
  cZ↓H : ∀ a → (Z ↓) ^ a • H ↑ ≈ H ↑ • (Z ↓) ^ a
  cZ↓H a = word-comm a 1 (lemma-comm-Z-w↑ {m} H)
  cZ↓su : ∀ a → (Z ↓) ^ a • (𝑠 ↑) ^ p-1 ≈ (𝑠 ↑) ^ p-1 • (Z ↓) ^ a
  cZ↓su a = word-comm a p-1 (lemma-comm-Z-w↑ {m} 𝑠)
  cZ↓sd : ∀ a → (Z ↓) ^ a • (𝑠 ↓) ^ p-1 ≈ (𝑠 ↓) ^ p-1 • (Z ↓) ^ a
  cZ↓sd a = word-comm a p-1 (sym (lemma-comm-𝑠-Z {₁₊ m}))
  -- Pauli reorderings (mod scalars X,Z commute)
  cX↑Z↑ : ∀ a b → (X ↑) ^ a • (Z ↑) ^ b ≈ (Z ↑) ^ b • (X ↑) ^ a
  cX↑Z↑ a b = word-comm a b (lemma-cong↑ _ _ (PB.axiom (comm-X-Z {m})))
  cX↑Z↓ : ∀ a b → (X ↑) ^ a • (Z ↓) ^ b ≈ (Z ↓) ^ b • (X ↑) ^ a
  cX↑Z↓ a b = word-comm a b (sym (lemma-comm-Z-w↑ {m} X))
  cZ↑Z↓ : ∀ a b → (Z ↑) ^ a • (Z ↓) ^ b ≈ (Z ↓) ^ b • (Z ↑) ^ a
  cZ↑Z↓ a b = word-comm a b (sym (lemma-comm-Z-w↑ {m} Z))

  ----------------------------------------------------------------------
  -- order facts and mod-reduction for the ↑/↓ Paulis
  ----------------------------------------------------------------------
  order-X↑ : (X ↑) ^ p ≈ ε
  order-X↑ = trans (refl' (Eq.sym (lemma-↑^ p X))) (lemma-cong↑ _ _ (Lemmas1-S.lemma-order-X m))
  order-Z↑ : (Z ↑) ^ p ≈ ε
  order-Z↑ = trans (refl' (Eq.sym (lemma-↑^ p Z))) (lemma-cong↑ _ _ (Lemmas1-S.lemma-order-Z m))

  Xmod↑ : ∀ k → (X ↑) ^ k ≈ (X ↑) ^ (k % p)
  Xmod↑ k = begin
    (X ↑) ^ k                                   ≡⟨ Eq.cong ((X ↑) ^_) (m≡m%n+[m/n]*n k p) ⟩
    (X ↑) ^ (k % p Nat.+ k / p Nat.* p)         ≈⟨ lemma-^-+ (X ↑) (k % p) (k / p Nat.* p) ⟩
    (X ↑) ^ (k % p) • (X ↑) ^ (k / p Nat.* p)   ≈⟨ cright (refl' (Eq.cong ((X ↑) ^_) (NP.*-comm (k / p) p))) ⟩
    (X ↑) ^ (k % p) • (X ↑) ^ (p Nat.* (k / p)) ≈⟨ cright (sym (lemma-^^ (X ↑) p (k / p))) ⟩
    (X ↑) ^ (k % p) • ((X ↑) ^ p) ^ (k / p)     ≈⟨ cright (lemma-^-cong ((X ↑) ^ p) ε (k / p) order-X↑) ⟩
    (X ↑) ^ (k % p) • ε ^ (k / p)               ≈⟨ cright (lemma-ε^k=ε (k / p)) ⟩
    (X ↑) ^ (k % p) • ε                         ≈⟨ right-unit ⟩
    (X ↑) ^ (k % p) ∎
  Zmod↑ : ∀ k → (Z ↑) ^ k ≈ (Z ↑) ^ (k % p)
  Zmod↑ k = begin
    (Z ↑) ^ k                                   ≡⟨ Eq.cong ((Z ↑) ^_) (m≡m%n+[m/n]*n k p) ⟩
    (Z ↑) ^ (k % p Nat.+ k / p Nat.* p)         ≈⟨ lemma-^-+ (Z ↑) (k % p) (k / p Nat.* p) ⟩
    (Z ↑) ^ (k % p) • (Z ↑) ^ (k / p Nat.* p)   ≈⟨ cright (refl' (Eq.cong ((Z ↑) ^_) (NP.*-comm (k / p) p))) ⟩
    (Z ↑) ^ (k % p) • (Z ↑) ^ (p Nat.* (k / p)) ≈⟨ cright (sym (lemma-^^ (Z ↑) p (k / p))) ⟩
    (Z ↑) ^ (k % p) • ((Z ↑) ^ p) ^ (k / p)     ≈⟨ cright (lemma-^-cong ((Z ↑) ^ p) ε (k / p) order-Z↑) ⟩
    (Z ↑) ^ (k % p) • ε ^ (k / p)               ≈⟨ cright (lemma-ε^k=ε (k / p)) ⟩
    (Z ↑) ^ (k % p) • ε                         ≈⟨ right-unit ⟩
    (Z ↑) ^ (k % p) ∎
  Zmod↓ : ∀ k → (Z ↓) ^ k ≈ (Z ↓) ^ (k % p)
  Zmod↓ k = begin
    (Z ↓) ^ k                                   ≡⟨ Eq.cong ((Z ↓) ^_) (m≡m%n+[m/n]*n k p) ⟩
    (Z ↓) ^ (k % p Nat.+ k / p Nat.* p)         ≈⟨ lemma-^-+ (Z ↓) (k % p) (k / p Nat.* p) ⟩
    (Z ↓) ^ (k % p) • (Z ↓) ^ (k / p Nat.* p)   ≈⟨ cright (refl' (Eq.cong ((Z ↓) ^_) (NP.*-comm (k / p) p))) ⟩
    (Z ↓) ^ (k % p) • (Z ↓) ^ (p Nat.* (k / p)) ≈⟨ cright (sym (lemma-^^ (Z ↓) p (k / p))) ⟩
    (Z ↓) ^ (k % p) • ((Z ↓) ^ p) ^ (k / p)     ≈⟨ cright (lemma-^-cong ((Z ↓) ^ p) ε (k / p) order-Z↓) ⟩
    (Z ↓) ^ (k % p) • ε ^ (k / p)               ≈⟨ cright (lemma-ε^k=ε (k / p)) ⟩
    (Z ↓) ^ (k % p) • ε                         ≈⟨ right-unit ⟩
    (Z ↓) ^ (k % p) ∎

  -- 2·½ ≡ 1 (mod p): the heart of the X↑·Z↑ tail collapse
  2z%p≡1 : (z Nat.+ z) % p ≡ 1
  2z%p≡1 = Eq.trans (Eq.cong (Nat._% p) zz≡z2)
                    (Eq.trans (Eq.sym (toℕ-fromℕ< (m%n<n (toℕ 1/2 Nat.* toℕ two) p)))
                              (Eq.cong toℕ (lemma-⁻¹ˡ two)))
    where
    two : ℤ ₚ
    two = ₂
    zz≡z2 : z Nat.+ z ≡ toℕ 1/2 Nat.* toℕ two
    zz≡z2 = Eq.sym (Eq.trans (NP.*-comm (toℕ 1/2) (toℕ two))
                             (Eq.cong (toℕ 1/2 Nat.+_) (NP.+-identityʳ (toℕ 1/2))))

  -- (p-1)·z + z ≡ 0 (mod p):  the Pauli-pair cancellation
  dzz%p≡0 : (toℕ (- 1ₚ) Nat.* z Nat.+ z) % p ≡ 0
  dzz%p≡0 = Eq.trans (Eq.cong (Nat._% p) (Eq.trans arith-pz (NP.*-comm p z))) (m*n%n≡0 z p)
    where
    arith-pz : toℕ (- 1ₚ) Nat.* z Nat.+ z ≡ p Nat.* z
    arith-pz = Eq.trans (Eq.cong (λ t → t Nat.* z Nat.+ z) lemma-toℕ-1ₚ)
                        (NP.+-comm (p-1 Nat.* z) z)

  -- Pauli-collapse reductions
  Xred : (X ↑) ^ (z Nat.+ z) ≈ X ↑
  Xred = trans (Xmod↑ (z Nat.+ z)) (refl' (Eq.cong ((X ↑) ^_) 2z%p≡1))
  Zred↑ : (Z ↑) ^ (z Nat.+ z) ≈ Z ↑
  Zred↑ = trans (Zmod↑ (z Nat.+ z)) (refl' (Eq.cong ((Z ↑) ^_) 2z%p≡1))
  Zcancel↑ : (Z ↑) ^ (toℕ (- 1ₚ) Nat.* z Nat.+ z) ≈ ε
  Zcancel↑ = trans (Zmod↑ (toℕ (- 1ₚ) Nat.* z Nat.+ z)) (refl' (Eq.cong ((Z ↑) ^_) dzz%p≡0))
  Zcancel↓ : (Z ↓) ^ (toℕ (- 1ₚ) Nat.* z Nat.+ z) ≈ ε
  Zcancel↓ = trans (Zmod↓ (toℕ (- 1ₚ) Nat.* z Nat.+ z)) (refl' (Eq.cong ((Z ↓) ^_) dzz%p≡0))

  -- collect the 8-Pauli tail (all commute mod scalars) down to X↑·Z↑
  collect-tail :
    (Z ↓) ^ (toℕ (- 1ₚ) Nat.* z) • (X ↑) ^ z • (Z ↑) ^ z • (Z ↑) ^ (toℕ (- 1ₚ) Nat.* z)
      • (X ↑) ^ z • (Z ↑) ^ z • (Z ↑) ^ z • (Z ↓) ^ z
    ≈ X ↑ • Z ↑
  collect-tail = begin
    (Z ↓) ^ (toℕ (- 1ₚ) Nat.* z) • (X ↑) ^ z • (Z ↑) ^ z • (Z ↑) ^ (toℕ (- 1ₚ) Nat.* z) • (X ↑) ^ z • (Z ↑) ^ z • (Z ↑) ^ z • (Z ↓) ^ z
      -- move Zd⁻ rightward to meet Zd
      ≈⟨ trans (sym assoc) (trans (cleft (sym (cX↑Z↓ z (toℕ (- 1ₚ) Nat.* z)))) assoc) ⟩
    (X ↑) ^ z • (Z ↓) ^ (toℕ (- 1ₚ) Nat.* z) • (Z ↑) ^ z • (Z ↑) ^ (toℕ (- 1ₚ) Nat.* z) • (X ↑) ^ z • (Z ↑) ^ z • (Z ↑) ^ z • (Z ↓) ^ z
      ≈⟨ cright (trans (sym assoc) (trans (cleft (sym (cZ↑Z↓ z (toℕ (- 1ₚ) Nat.* z)))) assoc)) ⟩
    (X ↑) ^ z • (Z ↑) ^ z • (Z ↓) ^ (toℕ (- 1ₚ) Nat.* z) • (Z ↑) ^ (toℕ (- 1ₚ) Nat.* z) • (X ↑) ^ z • (Z ↑) ^ z • (Z ↑) ^ z • (Z ↓) ^ z
      ≈⟨ cright (cright (trans (sym assoc) (trans (cleft (sym (cZ↑Z↓ (toℕ (- 1ₚ) Nat.* z) (toℕ (- 1ₚ) Nat.* z)))) assoc))) ⟩
    (X ↑) ^ z • (Z ↑) ^ z • (Z ↑) ^ (toℕ (- 1ₚ) Nat.* z) • (Z ↓) ^ (toℕ (- 1ₚ) Nat.* z) • (X ↑) ^ z • (Z ↑) ^ z • (Z ↑) ^ z • (Z ↓) ^ z
      ≈⟨ cright (cright (cright (trans (sym assoc) (trans (cleft (sym (cX↑Z↓ z (toℕ (- 1ₚ) Nat.* z)))) assoc)))) ⟩
    (X ↑) ^ z • (Z ↑) ^ z • (Z ↑) ^ (toℕ (- 1ₚ) Nat.* z) • (X ↑) ^ z • (Z ↓) ^ (toℕ (- 1ₚ) Nat.* z) • (Z ↑) ^ z • (Z ↑) ^ z • (Z ↓) ^ z
      ≈⟨ cright (cright (cright (cright (trans (sym assoc) (trans (cleft (sym (cZ↑Z↓ z (toℕ (- 1ₚ) Nat.* z)))) assoc))))) ⟩
    (X ↑) ^ z • (Z ↑) ^ z • (Z ↑) ^ (toℕ (- 1ₚ) Nat.* z) • (X ↑) ^ z • (Z ↑) ^ z • (Z ↓) ^ (toℕ (- 1ₚ) Nat.* z) • (Z ↑) ^ z • (Z ↓) ^ z
      ≈⟨ cright (cright (cright (cright (cright (trans (sym assoc) (trans (cleft (sym (cZ↑Z↓ z (toℕ (- 1ₚ) Nat.* z)))) assoc)))))) ⟩
    (X ↑) ^ z • (Z ↑) ^ z • (Z ↑) ^ (toℕ (- 1ₚ) Nat.* z) • (X ↑) ^ z • (Z ↑) ^ z • (Z ↑) ^ z • (Z ↓) ^ (toℕ (- 1ₚ) Nat.* z) • (Z ↓) ^ z
      -- move the 2nd Xu left to join the 1st
      ≈⟨ cright (cright (trans (sym assoc) (trans (cleft (sym (cX↑Z↑ z (toℕ (- 1ₚ) Nat.* z)))) assoc))) ⟩
    (X ↑) ^ z • (Z ↑) ^ z • (X ↑) ^ z • (Z ↑) ^ (toℕ (- 1ₚ) Nat.* z) • (Z ↑) ^ z • (Z ↑) ^ z • (Z ↓) ^ (toℕ (- 1ₚ) Nat.* z) • (Z ↓) ^ z
      ≈⟨ cright (trans (sym assoc) (trans (cleft (sym (cX↑Z↑ z z))) assoc)) ⟩
    (X ↑) ^ z • (X ↑) ^ z • (Z ↑) ^ z • (Z ↑) ^ (toℕ (- 1ₚ) Nat.* z) • (Z ↑) ^ z • (Z ↑) ^ z • (Z ↓) ^ (toℕ (- 1ₚ) Nat.* z) • (Z ↓) ^ z
      -- reorder Z↑ block so the cancelling pair (Zu⁻·Zu) is adjacent
      ≈⟨ cright (cright (cright (trans (sym assoc) (trans (cleft (word-comm (toℕ (- 1ₚ) Nat.* z) z refl)) assoc)))) ⟩
    (X ↑) ^ z • (X ↑) ^ z • (Z ↑) ^ z • (Z ↑) ^ z • (Z ↑) ^ (toℕ (- 1ₚ) Nat.* z) • (Z ↑) ^ z • (Z ↓) ^ (toℕ (- 1ₚ) Nat.* z) • (Z ↓) ^ z
      -- combine & reduce:  Xu·Xu→X↑
      ≈⟨ trans (sym assoc) (cleft (trans (sym (lemma-^-+ (X ↑) z z)) Xred)) ⟩
    X ↑ • (Z ↑) ^ z • (Z ↑) ^ z • (Z ↑) ^ (toℕ (- 1ₚ) Nat.* z) • (Z ↑) ^ z • (Z ↓) ^ (toℕ (- 1ₚ) Nat.* z) • (Z ↓) ^ z
      -- Zu·Zu→Z↑
      ≈⟨ cright (trans (sym assoc) (cleft (trans (sym (lemma-^-+ (Z ↑) z z)) Zred↑))) ⟩
    X ↑ • Z ↑ • (Z ↑) ^ (toℕ (- 1ₚ) Nat.* z) • (Z ↑) ^ z • (Z ↓) ^ (toℕ (- 1ₚ) Nat.* z) • (Z ↓) ^ z
      -- Zu⁻·Zu→ε
      ≈⟨ cright (cright (trans (sym assoc) (cleft (trans (sym (lemma-^-+ (Z ↑) (toℕ (- 1ₚ) Nat.* z) z)) Zcancel↑)))) ⟩
    X ↑ • Z ↑ • ε • (Z ↓) ^ (toℕ (- 1ₚ) Nat.* z) • (Z ↓) ^ z
      ≈⟨ cright (cright left-unit) ⟩
    X ↑ • Z ↑ • (Z ↓) ^ (toℕ (- 1ₚ) Nat.* z) • (Z ↓) ^ z
      -- Zd⁻·Zd→ε
      ≈⟨ cright (cright (trans (sym (lemma-^-+ (Z ↓) (toℕ (- 1ₚ) Nat.* z) z)) Zcancel↓)) ⟩
    X ↑ • Z ↑ • ε
      ≈⟨ cright right-unit ⟩
    X ↑ • Z ↑ ∎

  ----------------------------------------------------------------------
  -- Soundness of the simplified selinger-c10 (basic-S form + Pauli tail)
  ----------------------------------------------------------------------
  RHS-orig : Word (Gen (₂₊ m))
  RHS-orig = (𝑠 ↑) ^ p-1 • H ↑ • (𝑠 ↑) ^ p-1 • CZ • H ↑ • (𝑠 ↑) ^ p-1 • (𝑠 ↓) ^ p-1

  tail-c10 : (S ↑) ^ p-1 • H ↑ • (S ↑) ^ p-1 • CZ • H ↑ • (S ↑) ^ p-1 • (S ↓) ^ p-1
       ≈ RHS-orig • (X ↑ • Z ↑)
  tail-c10 = begin
    (S ↑) ^ p-1 • H ↑ • (S ↑) ^ p-1 • CZ • H ↑ • (S ↑) ^ p-1 • (S ↓) ^ p-1
      ≈⟨ cong fnd↑ (cong refl (cong fnd↑ (cong refl (cong refl (cong fnd↑ fnd↓))))) ⟩
    ((𝑠 ↑) ^ p-1 • (Z ↑) ^ z) • H ↑ • ((𝑠 ↑) ^ p-1 • (Z ↑) ^ z) • CZ • H ↑
      • ((𝑠 ↑) ^ p-1 • (Z ↑) ^ z) • ((𝑠 ↓) ^ p-1 • (Z ↓) ^ z)
      ≈⟨ push ⟩
    RHS-orig • (X ↑ • Z ↑) ∎
    where
    push : ((𝑠 ↑) ^ p-1 • (Z ↑) ^ z) • H ↑ • ((𝑠 ↑) ^ p-1 • (Z ↑) ^ z) • CZ • H ↑
         • ((𝑠 ↑) ^ p-1 • (Z ↑) ^ z) • ((𝑠 ↓) ^ p-1 • (Z ↓) ^ z)
         ≈ RHS-orig • (X ↑ • Z ↑)
    push = begin
      ((𝑠 ↑) ^ p-1 • (Z ↑) ^ z) • H ↑ • ((𝑠 ↑) ^ p-1 • (Z ↑) ^ z) • CZ • H ↑
        • ((𝑠 ↑) ^ p-1 • (Z ↑) ^ z) • ((𝑠 ↓) ^ p-1 • (Z ↓) ^ z)
        ≈⟨ special-assoc ((□ • □) • (□ • ((□ • □) • (□ • (□ • ((□ • □) • (□ • □)))))))
                         (□ • □ • □ • □ • □ • □ • □ • □ • □ • □ • □) auto ⟩
      (𝑠 ↑) ^ p-1 • (Z ↑) ^ z • H ↑ • (𝑠 ↑) ^ p-1 • (Z ↑) ^ z • CZ • H ↑
        • (𝑠 ↑) ^ p-1 • (Z ↑) ^ z • (𝑠 ↓) ^ p-1 • (Z ↓) ^ z
        -- push Zu#3 past sd:  Zu·(sd·Zd) ≈ sd·(Zu·Zd)
        ≈⟨ cright (cright (cright (cright (cright (cright (cright (cright
             (trans (sym assoc) (trans (cleft (cZ↑sd z)) assoc))))))))) ⟩
      (𝑠 ↑) ^ p-1 • (Z ↑) ^ z • H ↑ • (𝑠 ↑) ^ p-1 • (Z ↑) ^ z • CZ • H ↑
        • (𝑠 ↑) ^ p-1 • (𝑠 ↓) ^ p-1 • (Z ↑) ^ z • (Z ↓) ^ z
        -- push Zu#2 through CZ:  Zu·CZ ≈ CZ·Zu
        ≈⟨ cright (cright (cright (cright
             (trans (sym assoc) (trans (cleft (qZCZ z)) assoc))))) ⟩
      (𝑠 ↑) ^ p-1 • (Z ↑) ^ z • H ↑ • (𝑠 ↑) ^ p-1 • CZ • (Z ↑) ^ z • H ↑
        • (𝑠 ↑) ^ p-1 • (𝑠 ↓) ^ p-1 • (Z ↑) ^ z • (Z ↓) ^ z
        -- push Zu#2 through H:  Zu·H ≈ H·Xu
        ≈⟨ cright (cright (cright (cright (cright
             (trans (sym assoc) (trans (cleft (qZH z)) assoc)))))) ⟩
      (𝑠 ↑) ^ p-1 • (Z ↑) ^ z • H ↑ • (𝑠 ↑) ^ p-1 • CZ • H ↑ • (X ↑) ^ z
        • (𝑠 ↑) ^ p-1 • (𝑠 ↓) ^ p-1 • (Z ↑) ^ z • (Z ↓) ^ z
        -- push Xu through su (spawns Zu):  Xu·su ≈ su·Xu·Zu
        ≈⟨ cright (cright (cright (cright (cright (cright
             (trans (sym assoc) (trans (cleft (qX𝑠 z)) (trans assoc (cright assoc)))))))) ) ⟩
      (𝑠 ↑) ^ p-1 • (Z ↑) ^ z • H ↑ • (𝑠 ↑) ^ p-1 • CZ • H ↑ • (𝑠 ↑) ^ p-1
        • (X ↑) ^ z • (Z ↑) ^ z • (𝑠 ↓) ^ p-1 • (Z ↑) ^ z • (Z ↓) ^ z
        -- push spawned Zu past sd:  Zu·sd ≈ sd·Zu
        ≈⟨ cright (cright (cright (cright (cright (cright (cright (cright
             (trans (sym assoc) (trans (cleft (cZ↑sd z)) assoc))))))))) ⟩
      (𝑠 ↑) ^ p-1 • (Z ↑) ^ z • H ↑ • (𝑠 ↑) ^ p-1 • CZ • H ↑ • (𝑠 ↑) ^ p-1
        • (X ↑) ^ z • (𝑠 ↓) ^ p-1 • (Z ↑) ^ z • (Z ↑) ^ z • (Z ↓) ^ z
        -- push Xu past sd:  Xu·sd ≈ sd·Xu
        ≈⟨ cright (cright (cright (cright (cright (cright (cright
             (trans (sym assoc) (trans (cleft (cX↑sd z)) assoc)))))))) ⟩
      (𝑠 ↑) ^ p-1 • (Z ↑) ^ z • H ↑ • (𝑠 ↑) ^ p-1 • CZ • H ↑ • (𝑠 ↑) ^ p-1
        • (𝑠 ↓) ^ p-1 • (X ↑) ^ z • (Z ↑) ^ z • (Z ↑) ^ z • (Z ↓) ^ z
        -- 3a: Zu#1 through H:  Zu·H ≈ H·Xu
        ≈⟨ cright (trans (sym assoc) (trans (cleft (qZH z)) assoc)) ⟩
      (𝑠 ↑) ^ p-1 • H ↑ • (X ↑) ^ z • (𝑠 ↑) ^ p-1 • CZ • H ↑ • (𝑠 ↑) ^ p-1
        • (𝑠 ↓) ^ p-1 • (X ↑) ^ z • (Z ↑) ^ z • (Z ↑) ^ z • (Z ↓) ^ z
        -- 3b: Xu through su (spawns Zu):  Xu·su ≈ su·Xu·Zu
        ≈⟨ cright (cright (trans (sym assoc) (trans (cleft (qX𝑠 z)) (trans assoc (cright assoc))))) ⟩
      (𝑠 ↑) ^ p-1 • H ↑ • (𝑠 ↑) ^ p-1 • (X ↑) ^ z • (Z ↑) ^ z • CZ • H ↑ • (𝑠 ↑) ^ p-1
        • (𝑠 ↓) ^ p-1 • (X ↑) ^ z • (Z ↑) ^ z • (Z ↑) ^ z • (Z ↓) ^ z
        -- 3c: Xu past spawned Zu:  Xu·Zu ≈ Zu·Xu
        ≈⟨ cright (cright (cright (trans (sym assoc) (trans (cleft (cX↑Z↑ z z)) assoc)))) ⟩
      (𝑠 ↑) ^ p-1 • H ↑ • (𝑠 ↑) ^ p-1 • (Z ↑) ^ z • (X ↑) ^ z • CZ • H ↑ • (𝑠 ↑) ^ p-1
        • (𝑠 ↓) ^ p-1 • (X ↑) ^ z • (Z ↑) ^ z • (Z ↑) ^ z • (Z ↓) ^ z
        -- 3d: Xu through CZ (spawns Z↓⁻):  Xu·CZ ≈ CZ·Xu·Z↓⁻
        ≈⟨ cright (cright (cright (cright (trans (sym assoc) (trans (cleft (qXCZ z)) (trans assoc (cright assoc))))))) ⟩
      (𝑠 ↑) ^ p-1 • H ↑ • (𝑠 ↑) ^ p-1 • (Z ↑) ^ z • CZ • (X ↑) ^ z • (Z ↓) ^ (toℕ (- 1ₚ) Nat.* z) • H ↑ • (𝑠 ↑) ^ p-1
        • (𝑠 ↓) ^ p-1 • (X ↑) ^ z • (Z ↑) ^ z • (Z ↑) ^ z • (Z ↓) ^ z
        -- 3e: Xu past Z↓⁻:  Xu·Z↓⁻ ≈ Z↓⁻·Xu
        ≈⟨ cright (cright (cright (cright (cright (trans (sym assoc) (trans (cleft (cX↑Z↓ z (toℕ (- 1ₚ) Nat.* z))) assoc)))))) ⟩
      (𝑠 ↑) ^ p-1 • H ↑ • (𝑠 ↑) ^ p-1 • (Z ↑) ^ z • CZ • (Z ↓) ^ (toℕ (- 1ₚ) Nat.* z) • (X ↑) ^ z • H ↑ • (𝑠 ↑) ^ p-1
        • (𝑠 ↓) ^ p-1 • (X ↑) ^ z • (Z ↑) ^ z • (Z ↑) ^ z • (Z ↓) ^ z
        -- 3f: Xu through H:  Xu·H ≈ H·Zu⁻
        ≈⟨ cright (cright (cright (cright (cright (cright (trans (sym assoc) (trans (cleft (qXH z)) assoc))))))) ⟩
      (𝑠 ↑) ^ p-1 • H ↑ • (𝑠 ↑) ^ p-1 • (Z ↑) ^ z • CZ • (Z ↓) ^ (toℕ (- 1ₚ) Nat.* z) • H ↑ • (Z ↑) ^ (toℕ (- 1ₚ) Nat.* z) • (𝑠 ↑) ^ p-1
        • (𝑠 ↓) ^ p-1 • (X ↑) ^ z • (Z ↑) ^ z • (Z ↑) ^ z • (Z ↓) ^ z
        -- 3g: Zu⁻ through su:  Zu⁻·su ≈ su·Zu⁻
        ≈⟨ cright (cright (cright (cright (cright (cright (cright (trans (sym assoc) (trans (cleft (qZ𝑠 (toℕ (- 1ₚ) Nat.* z))) assoc)))))))) ⟩
      (𝑠 ↑) ^ p-1 • H ↑ • (𝑠 ↑) ^ p-1 • (Z ↑) ^ z • CZ • (Z ↓) ^ (toℕ (- 1ₚ) Nat.* z) • H ↑ • (𝑠 ↑) ^ p-1 • (Z ↑) ^ (toℕ (- 1ₚ) Nat.* z)
        • (𝑠 ↓) ^ p-1 • (X ↑) ^ z • (Z ↑) ^ z • (Z ↑) ^ z • (Z ↓) ^ z
        -- 3h: Zu⁻ past sd:  Zu⁻·sd ≈ sd·Zu⁻
        ≈⟨ cright (cright (cright (cright (cright (cright (cright (cright (trans (sym assoc) (trans (cleft (cZ↑sd (toℕ (- 1ₚ) Nat.* z))) assoc))))))))) ⟩
      (𝑠 ↑) ^ p-1 • H ↑ • (𝑠 ↑) ^ p-1 • (Z ↑) ^ z • CZ • (Z ↓) ^ (toℕ (- 1ₚ) Nat.* z) • H ↑ • (𝑠 ↑) ^ p-1
        • (𝑠 ↓) ^ p-1 • (Z ↑) ^ (toℕ (- 1ₚ) Nat.* z) • (X ↑) ^ z • (Z ↑) ^ z • (Z ↑) ^ z • (Z ↓) ^ z
        -- 4a: leftover Zu through CZ
        ≈⟨ cright (cright (cright (trans (sym assoc) (trans (cleft (qZCZ z)) assoc)))) ⟩
      (𝑠 ↑) ^ p-1 • H ↑ • (𝑠 ↑) ^ p-1 • CZ • (Z ↑) ^ z • (Z ↓) ^ (toℕ (- 1ₚ) Nat.* z) • H ↑ • (𝑠 ↑) ^ p-1
        • (𝑠 ↓) ^ p-1 • (Z ↑) ^ (toℕ (- 1ₚ) Nat.* z) • (X ↑) ^ z • (Z ↑) ^ z • (Z ↑) ^ z • (Z ↓) ^ z
        -- 4b: leftover Zu past Z↓⁻
        ≈⟨ cright (cright (cright (cright (trans (sym assoc) (trans (cleft (cZ↑Z↓ z (toℕ (- 1ₚ) Nat.* z))) assoc))))) ⟩
      (𝑠 ↑) ^ p-1 • H ↑ • (𝑠 ↑) ^ p-1 • CZ • (Z ↓) ^ (toℕ (- 1ₚ) Nat.* z) • (Z ↑) ^ z • H ↑ • (𝑠 ↑) ^ p-1
        • (𝑠 ↓) ^ p-1 • (Z ↑) ^ (toℕ (- 1ₚ) Nat.* z) • (X ↑) ^ z • (Z ↑) ^ z • (Z ↑) ^ z • (Z ↓) ^ z
        -- 4c: leftover Zu through H
        ≈⟨ cright (cright (cright (cright (cright (trans (sym assoc) (trans (cleft (qZH z)) assoc)))))) ⟩
      (𝑠 ↑) ^ p-1 • H ↑ • (𝑠 ↑) ^ p-1 • CZ • (Z ↓) ^ (toℕ (- 1ₚ) Nat.* z) • H ↑ • (X ↑) ^ z • (𝑠 ↑) ^ p-1
        • (𝑠 ↓) ^ p-1 • (Z ↑) ^ (toℕ (- 1ₚ) Nat.* z) • (X ↑) ^ z • (Z ↑) ^ z • (Z ↑) ^ z • (Z ↓) ^ z
        -- 4d: leftover Xu through su (spawns Zu_b)
        ≈⟨ cright (cright (cright (cright (cright (cright (trans (sym assoc) (trans (cleft (qX𝑠 z)) (trans assoc (cright assoc)))))))) ) ⟩
      (𝑠 ↑) ^ p-1 • H ↑ • (𝑠 ↑) ^ p-1 • CZ • (Z ↓) ^ (toℕ (- 1ₚ) Nat.* z) • H ↑ • (𝑠 ↑) ^ p-1 • (X ↑) ^ z • (Z ↑) ^ z
        • (𝑠 ↓) ^ p-1 • (Z ↑) ^ (toℕ (- 1ₚ) Nat.* z) • (X ↑) ^ z • (Z ↑) ^ z • (Z ↑) ^ z • (Z ↓) ^ z
        -- 4e: spawned Zu_b past sd
        ≈⟨ cright (cright (cright (cright (cright (cright (cright (cright (trans (sym assoc) (trans (cleft (cZ↑sd z)) assoc))))))))) ⟩
      (𝑠 ↑) ^ p-1 • H ↑ • (𝑠 ↑) ^ p-1 • CZ • (Z ↓) ^ (toℕ (- 1ₚ) Nat.* z) • H ↑ • (𝑠 ↑) ^ p-1 • (X ↑) ^ z
        • (𝑠 ↓) ^ p-1 • (Z ↑) ^ z • (Z ↑) ^ (toℕ (- 1ₚ) Nat.* z) • (X ↑) ^ z • (Z ↑) ^ z • (Z ↑) ^ z • (Z ↓) ^ z
        -- 4f: leftover Xu past sd
        ≈⟨ cright (cright (cright (cright (cright (cright (cright (trans (sym assoc) (trans (cleft (cX↑sd z)) assoc)))))))) ⟩
      (𝑠 ↑) ^ p-1 • H ↑ • (𝑠 ↑) ^ p-1 • CZ • (Z ↓) ^ (toℕ (- 1ₚ) Nat.* z) • H ↑ • (𝑠 ↑) ^ p-1
        • (𝑠 ↓) ^ p-1 • (X ↑) ^ z • (Z ↑) ^ z • (Z ↑) ^ (toℕ (- 1ₚ) Nat.* z) • (X ↑) ^ z • (Z ↑) ^ z • (Z ↑) ^ z • (Z ↓) ^ z
        -- 5a: leftover Z↓⁻ through H
        ≈⟨ cright (cright (cright (cright (trans (sym assoc) (trans (cleft (cZ↓H (toℕ (- 1ₚ) Nat.* z))) assoc))))) ⟩
      (𝑠 ↑) ^ p-1 • H ↑ • (𝑠 ↑) ^ p-1 • CZ • H ↑ • (Z ↓) ^ (toℕ (- 1ₚ) Nat.* z) • (𝑠 ↑) ^ p-1
        • (𝑠 ↓) ^ p-1 • (X ↑) ^ z • (Z ↑) ^ z • (Z ↑) ^ (toℕ (- 1ₚ) Nat.* z) • (X ↑) ^ z • (Z ↑) ^ z • (Z ↑) ^ z • (Z ↓) ^ z
        -- 5b: leftover Z↓⁻ through su
        ≈⟨ cright (cright (cright (cright (cright (trans (sym assoc) (trans (cleft (cZ↓su (toℕ (- 1ₚ) Nat.* z))) assoc)))))) ⟩
      (𝑠 ↑) ^ p-1 • H ↑ • (𝑠 ↑) ^ p-1 • CZ • H ↑ • (𝑠 ↑) ^ p-1 • (Z ↓) ^ (toℕ (- 1ₚ) Nat.* z)
        • (𝑠 ↓) ^ p-1 • (X ↑) ^ z • (Z ↑) ^ z • (Z ↑) ^ (toℕ (- 1ₚ) Nat.* z) • (X ↑) ^ z • (Z ↑) ^ z • (Z ↑) ^ z • (Z ↓) ^ z
        -- 5c: leftover Z↓⁻ past sd
        ≈⟨ cright (cright (cright (cright (cright (cright (trans (sym assoc) (trans (cleft (cZ↓sd (toℕ (- 1ₚ) Nat.* z))) assoc))))))) ⟩
      (𝑠 ↑) ^ p-1 • H ↑ • (𝑠 ↑) ^ p-1 • CZ • H ↑ • (𝑠 ↑) ^ p-1 • (𝑠 ↓) ^ p-1
        • (Z ↓) ^ (toℕ (- 1ₚ) Nat.* z) • (X ↑) ^ z • (Z ↑) ^ z • (Z ↑) ^ (toℕ (- 1ₚ) Nat.* z) • (X ↑) ^ z • (Z ↑) ^ z • (Z ↑) ^ z • (Z ↓) ^ z
        -- collect the tail (depth 7) to X↑·Z↑, then regroup the frame as RHS-orig
        ≈⟨ trans (cright (cright (cright (cright (cright (cright (cright collect-tail)))))))
                 (special-assoc (□ • □ • □ • □ • □ • □ • □ • □ • □)
                                ((□ • □ • □ • □ • □ • □ • □) • (□ • □)) auto) ⟩
      RHS-orig • (X ↑ • Z ↑) ∎




module C11 (m : ℕ) where
  open PB ((₂₊ m) QRel,_===_)
  open PP ((₂₊ m) QRel,_===_)
  open SR word-setoid
  open Pattern-Assoc
  open Lemmas-Clifford-S using (lemma-cong↑ ; lemma-↑^ ; lemma-Induction
                            ; lemma-comm-Z-w↑ ; lemma-comm-X-w↑ ; lemma-comm-H-w↑)
  open Lemmas1b-S (₁₊ m) using (conj-H-X^k)   -- down (base) H-conjugation at ₂₊ m

  z : ℕ
  z = toℕ 1/2

  order-Z↓ : (Z ↓) ^ p ≈ ε
  order-Z↓ = Lemmas1-S.lemma-order-Z (₁₊ m)
  order-X↓ : (X ↓) ^ p ≈ ε
  order-X↓ = Lemmas1-S.lemma-order-X (₁₊ m)
  order-Z↑ : (Z ↑) ^ p ≈ ε
  order-Z↑ = trans (refl' (Eq.sym (lemma-↑^ p Z))) (lemma-cong↑ _ _ (Lemmas1-S.lemma-order-Z m))

  -- foundational, main (↓) and other (↑) qubits
  fnd↓ : (S ↓) ^ p-1 ≈ (𝑠 ↓) ^ p-1 • (Z ↓) ^ z
  fnd↓ = lemma-S⁻¹=𝑠⁻¹Z (₁₊ m)
  fnd↑ : (S ↑) ^ p-1 ≈ (𝑠 ↑) ^ p-1 • (Z ↑) ^ z
  fnd↑ = trans (refl' (Eq.sym (lemma-↑^ p-1 S)))
         (trans (lemma-cong↑ _ _ (lemma-S⁻¹=𝑠⁻¹Z m))
                (refl' (Eq.cong₂ _•_ (lemma-↑^ p-1 𝑠) (lemma-↑^ z Z))))

  -- down-qubit conjugations (↓ is identity, so these are base lemmas directly)
  qZH↓ : ∀ a → (Z ↓) ^ a • (H ↓) ≈ (H ↓) • (X ↓) ^ a
  qZH↓ a = PB.sym (conj-H-X^k a)
  qX𝑠↓ : ∀ a → (X ↓) ^ a • (𝑠 ↓) ^ p-1 ≈ (𝑠 ↓) ^ p-1 • (X ↓) ^ a • (Z ↓) ^ a
  qX𝑠↓ a = C10Base.bX𝑠 (₁₊ m) a
  qXH↓ : ∀ a → (X ↓) ^ a • (H ↓) ≈ (H ↓) • (Z ↓) ^ (toℕ (- 1ₚ) Nat.* a)
  qXH↓ a = trans (C10Base.bXH (₁₊ m) a) (cright (lemma-^^ Z (toℕ (- 1ₚ)) a))
  qZCZ↓ : ∀ a → (Z ↓) ^ a • CZ ≈ CZ • (Z ↓) ^ a
  qZCZ↓ a = word-comm a 1 (lemma-comm-Z-CZ {m})
  qZ𝑠↓ : ∀ a → (Z ↓) ^ a • (𝑠 ↓) ^ p-1 ≈ (𝑠 ↓) ^ p-1 • (Z ↓) ^ a
  qZ𝑠↓ a = word-comm a p-1 (sym (lemma-comm-𝑠-Z {₁₊ m}))

  -- cross-qubit commutations
  cZ↑s↓ : ∀ a → (Z ↑) ^ a • (𝑠 ↓) ^ p-1 ≈ (𝑠 ↓) ^ p-1 • (Z ↑) ^ a
  cZ↑s↓ a = word-comm a p-1 (sym (lemma-comm-𝑠-w↑ {m} Z))
  cX↓s↑ : ∀ a → (X ↓) ^ a • (𝑠 ↑) ^ p-1 ≈ (𝑠 ↑) ^ p-1 • (X ↓) ^ a
  cX↓s↑ a = word-comm a p-1 (lemma-comm-X-w↑ {m} 𝑠)
  cZ↓s↑ : ∀ a → (Z ↓) ^ a • (𝑠 ↑) ^ p-1 ≈ (𝑠 ↑) ^ p-1 • (Z ↓) ^ a
  cZ↓s↑ a = word-comm a p-1 (lemma-comm-Z-w↑ {m} 𝑠)
  cZ↑H↓ : ∀ a → (Z ↑) ^ a • H ↓ ≈ H ↓ • (Z ↑) ^ a
  cZ↑H↓ a = word-comm a 1 (sym (lemma-comm-H-w↑ {m} Z))
  -- Pauli reorderings
  cX↓Z↓ : ∀ a b → (X ↓) ^ a • (Z ↓) ^ b ≈ (Z ↓) ^ b • (X ↓) ^ a
  cX↓Z↓ a b = word-comm a b (axiom comm-X-Z)
  cX↓Z↑ : ∀ a b → (X ↓) ^ a • (Z ↑) ^ b ≈ (Z ↑) ^ b • (X ↓) ^ a
  cX↓Z↑ a b = word-comm a b (lemma-comm-X-w↑ {m} Z)
  cZ↓Z↑ : ∀ a b → (Z ↓) ^ a • (Z ↑) ^ b ≈ (Z ↑) ^ b • (Z ↓) ^ a
  cZ↓Z↑ a b = word-comm a b (lemma-comm-Z-w↑ {m} Z)

  -- mod-reductions
  Xmod↓ : ∀ k → (X ↓) ^ k ≈ (X ↓) ^ (k % p)
  Xmod↓ k = begin
    (X ↓) ^ k                                   ≡⟨ Eq.cong ((X ↓) ^_) (m≡m%n+[m/n]*n k p) ⟩
    (X ↓) ^ (k % p Nat.+ k / p Nat.* p)         ≈⟨ lemma-^-+ (X ↓) (k % p) (k / p Nat.* p) ⟩
    (X ↓) ^ (k % p) • (X ↓) ^ (k / p Nat.* p)   ≈⟨ cright (refl' (Eq.cong ((X ↓) ^_) (NP.*-comm (k / p) p))) ⟩
    (X ↓) ^ (k % p) • (X ↓) ^ (p Nat.* (k / p)) ≈⟨ cright (sym (lemma-^^ (X ↓) p (k / p))) ⟩
    (X ↓) ^ (k % p) • ((X ↓) ^ p) ^ (k / p)     ≈⟨ cright (lemma-^-cong ((X ↓) ^ p) ε (k / p) order-X↓) ⟩
    (X ↓) ^ (k % p) • ε ^ (k / p)               ≈⟨ cright (lemma-ε^k=ε (k / p)) ⟩
    (X ↓) ^ (k % p) • ε                         ≈⟨ right-unit ⟩
    (X ↓) ^ (k % p) ∎
  Zmod↓ : ∀ k → (Z ↓) ^ k ≈ (Z ↓) ^ (k % p)
  Zmod↓ k = begin
    (Z ↓) ^ k                                   ≡⟨ Eq.cong ((Z ↓) ^_) (m≡m%n+[m/n]*n k p) ⟩
    (Z ↓) ^ (k % p Nat.+ k / p Nat.* p)         ≈⟨ lemma-^-+ (Z ↓) (k % p) (k / p Nat.* p) ⟩
    (Z ↓) ^ (k % p) • (Z ↓) ^ (k / p Nat.* p)   ≈⟨ cright (refl' (Eq.cong ((Z ↓) ^_) (NP.*-comm (k / p) p))) ⟩
    (Z ↓) ^ (k % p) • (Z ↓) ^ (p Nat.* (k / p)) ≈⟨ cright (sym (lemma-^^ (Z ↓) p (k / p))) ⟩
    (Z ↓) ^ (k % p) • ((Z ↓) ^ p) ^ (k / p)     ≈⟨ cright (lemma-^-cong ((Z ↓) ^ p) ε (k / p) order-Z↓) ⟩
    (Z ↓) ^ (k % p) • ε ^ (k / p)               ≈⟨ cright (lemma-ε^k=ε (k / p)) ⟩
    (Z ↓) ^ (k % p) • ε                         ≈⟨ right-unit ⟩
    (Z ↓) ^ (k % p) ∎
  Zmod↑ : ∀ k → (Z ↑) ^ k ≈ (Z ↑) ^ (k % p)
  Zmod↑ k = begin
    (Z ↑) ^ k                                   ≡⟨ Eq.cong ((Z ↑) ^_) (m≡m%n+[m/n]*n k p) ⟩
    (Z ↑) ^ (k % p Nat.+ k / p Nat.* p)         ≈⟨ lemma-^-+ (Z ↑) (k % p) (k / p Nat.* p) ⟩
    (Z ↑) ^ (k % p) • (Z ↑) ^ (k / p Nat.* p)   ≈⟨ cright (refl' (Eq.cong ((Z ↑) ^_) (NP.*-comm (k / p) p))) ⟩
    (Z ↑) ^ (k % p) • (Z ↑) ^ (p Nat.* (k / p)) ≈⟨ cright (sym (lemma-^^ (Z ↑) p (k / p))) ⟩
    (Z ↑) ^ (k % p) • ((Z ↑) ^ p) ^ (k / p)     ≈⟨ cright (lemma-^-cong ((Z ↑) ^ p) ε (k / p) order-Z↑) ⟩
    (Z ↑) ^ (k % p) • ε ^ (k / p)               ≈⟨ cright (lemma-ε^k=ε (k / p)) ⟩
    (Z ↑) ^ (k % p) • ε                         ≈⟨ right-unit ⟩
    (Z ↑) ^ (k % p) ∎

  -- arithmetic
  2z%p≡1 : (z Nat.+ z) % p ≡ 1
  2z%p≡1 = Eq.trans (Eq.cong (Nat._% p) zz≡z2)
                    (Eq.trans (Eq.sym (toℕ-fromℕ< (m%n<n (toℕ 1/2 Nat.* toℕ two) p)))
                              (Eq.cong toℕ (lemma-⁻¹ˡ two)))
    where
    two : ℤ ₚ
    two = ₂
    zz≡z2 : z Nat.+ z ≡ toℕ 1/2 Nat.* toℕ two
    zz≡z2 = Eq.sym (Eq.trans (NP.*-comm (toℕ 1/2) (toℕ two))
                             (Eq.cong (toℕ 1/2 Nat.+_) (NP.+-identityʳ (toℕ 1/2))))
  dzz%p≡0 : (toℕ (- 1ₚ) Nat.* z Nat.+ z) % p ≡ 0
  dzz%p≡0 = Eq.trans (Eq.cong (Nat._% p) (Eq.trans arith-pz (NP.*-comm p z))) (m*n%n≡0 z p)
    where
    arith-pz : toℕ (- 1ₚ) Nat.* z Nat.+ z ≡ p Nat.* z
    arith-pz = Eq.trans (Eq.cong (λ t → t Nat.* z Nat.+ z) lemma-toℕ-1ₚ)
                        (NP.+-comm (p-1 Nat.* z) z)

  -- collapse reductions
  Xred↓ : (X ↓) ^ (z Nat.+ z) ≈ X ↓
  Xred↓ = trans (Xmod↓ (z Nat.+ z)) (refl' (Eq.cong ((X ↓) ^_) 2z%p≡1))
  Zred↓ : (Z ↓) ^ (z Nat.+ z) ≈ Z ↓
  Zred↓ = trans (Zmod↓ (z Nat.+ z)) (refl' (Eq.cong ((Z ↓) ^_) 2z%p≡1))
  Zcancel↓ : (Z ↓) ^ (toℕ (- 1ₚ) Nat.* z Nat.+ z) ≈ ε
  Zcancel↓ = trans (Zmod↓ (toℕ (- 1ₚ) Nat.* z Nat.+ z)) (refl' (Eq.cong ((Z ↓) ^_) dzz%p≡0))
  Zcancel↑ : (Z ↑) ^ (toℕ (- 1ₚ) Nat.* z Nat.+ z) ≈ ε
  Zcancel↑ = trans (Zmod↑ (toℕ (- 1ₚ) Nat.* z Nat.+ z)) (refl' (Eq.cong ((Z ↑) ^_) dzz%p≡0))

  -- CZ • X↓^a ≈ X↓^a • Z↑^a • CZ
  relpow↓ : ∀ a → CZ • (X ↓) ^ a ≈ (X ↓) ^ a • (Z ↑) ^ a • CZ
  relpow↓ a = trans (lemma-Induction (trans (axiom rel-X↓-CZ) (sym assoc)) a)
                    (trans (cleft (lemma-^-• (X ↓) (Z ↑) a (lemma-comm-X-w↑ {m} Z))) assoc)

  Z↑inv : ∀ a → (Z ↑) ^ a • ((Z ↑) ^ toℕ (- 1ₚ)) ^ a ≈ ε
  Z↑inv a = begin
    (Z ↑) ^ a • ((Z ↑) ^ toℕ (- 1ₚ)) ^ a    ≈⟨ cright (lemma-^^ (Z ↑) (toℕ (- 1ₚ)) a) ⟩
    (Z ↑) ^ a • (Z ↑) ^ (toℕ (- 1ₚ) Nat.* a) ≈⟨ sym (lemma-^-+ (Z ↑) a (toℕ (- 1ₚ) Nat.* a)) ⟩
    (Z ↑) ^ (a Nat.+ toℕ (- 1ₚ) Nat.* a)     ≡⟨ Eq.cong ((Z ↑) ^_) arith ⟩
    (Z ↑) ^ (p Nat.* a)                     ≈⟨ sym (lemma-^^ (Z ↑) p a) ⟩
    ((Z ↑) ^ p) ^ a                         ≈⟨ lemma-^-cong ((Z ↑) ^ p) ε a order-Z↑ ⟩
    ε ^ a                                   ≈⟨ lemma-ε^k=ε a ⟩
    ε ∎
    where
    arith : a Nat.+ toℕ (- 1ₚ) Nat.* a ≡ p Nat.* a
    arith = Eq.cong (λ t → a Nat.+ t Nat.* a) lemma-toℕ-1ₚ

  -- X↓ through CZ  (X↓•CZ ≈ CZ•X↓•Z↑⁻¹), flat exponent
  qXCZ↓ : ∀ a → (X ↓) ^ a • CZ ≈ CZ • (X ↓) ^ a • (Z ↑) ^ (toℕ (- 1ₚ) Nat.* a)
  qXCZ↓ a = begin
    (X ↓) ^ a • CZ
      ≈⟨ sym right-unit ⟩
    ((X ↓) ^ a • CZ) • ε
      ≈⟨ cright (sym (Z↑inv a)) ⟩
    ((X ↓) ^ a • CZ) • ((Z ↑) ^ a • ((Z ↑) ^ toℕ (- 1ₚ)) ^ a)
      ≈⟨ sym assoc ⟩
    (((X ↓) ^ a • CZ) • (Z ↑) ^ a) • ((Z ↑) ^ toℕ (- 1ₚ)) ^ a
      ≈⟨ cleft step ⟩
    (CZ • (X ↓) ^ a) • ((Z ↑) ^ toℕ (- 1ₚ)) ^ a
      ≈⟨ assoc ⟩
    CZ • (X ↓) ^ a • ((Z ↑) ^ toℕ (- 1ₚ)) ^ a
      ≈⟨ cright (cright (lemma-^^ (Z ↑) (toℕ (- 1ₚ)) a)) ⟩
    CZ • (X ↓) ^ a • (Z ↑) ^ (toℕ (- 1ₚ) Nat.* a) ∎
    where
    step : ((X ↓) ^ a • CZ) • (Z ↑) ^ a ≈ CZ • (X ↓) ^ a
    step = begin
      ((X ↓) ^ a • CZ) • (Z ↑) ^ a   ≈⟨ assoc ⟩
      (X ↓) ^ a • (CZ • (Z ↑) ^ a)   ≈⟨ cright (sym (word-comm a 1 (lemma-comm-Z↑-CZ {m}))) ⟩
      (X ↓) ^ a • ((Z ↑) ^ a • CZ)   ≈⟨ sym (relpow↓ a) ⟩
      CZ • (X ↓) ^ a ∎

  -- collect the 8-Pauli tail down to X↓·Z↓ (mirror of collect-tail)
  collect-tail↓ :
    (Z ↑) ^ (toℕ (- 1ₚ) Nat.* z) • (X ↓) ^ z • (Z ↓) ^ z • (Z ↓) ^ (toℕ (- 1ₚ) Nat.* z)
      • (X ↓) ^ z • (Z ↓) ^ z • (Z ↓) ^ z • (Z ↑) ^ z
    ≈ X ↓ • Z ↓
  collect-tail↓ = begin
    (Z ↑) ^ (toℕ (- 1ₚ) Nat.* z) • (X ↓) ^ z • (Z ↓) ^ z • (Z ↓) ^ (toℕ (- 1ₚ) Nat.* z) • (X ↓) ^ z • (Z ↓) ^ z • (Z ↓) ^ z • (Z ↑) ^ z
      ≈⟨ trans (sym assoc) (trans (cleft (sym (cX↓Z↑ z (toℕ (- 1ₚ) Nat.* z)))) assoc) ⟩
    (X ↓) ^ z • (Z ↑) ^ (toℕ (- 1ₚ) Nat.* z) • (Z ↓) ^ z • (Z ↓) ^ (toℕ (- 1ₚ) Nat.* z) • (X ↓) ^ z • (Z ↓) ^ z • (Z ↓) ^ z • (Z ↑) ^ z
      ≈⟨ cright (trans (sym assoc) (trans (cleft (sym (cZ↓Z↑ z (toℕ (- 1ₚ) Nat.* z)))) assoc)) ⟩
    (X ↓) ^ z • (Z ↓) ^ z • (Z ↑) ^ (toℕ (- 1ₚ) Nat.* z) • (Z ↓) ^ (toℕ (- 1ₚ) Nat.* z) • (X ↓) ^ z • (Z ↓) ^ z • (Z ↓) ^ z • (Z ↑) ^ z
      ≈⟨ cright (cright (trans (sym assoc) (trans (cleft (sym (cZ↓Z↑ (toℕ (- 1ₚ) Nat.* z) (toℕ (- 1ₚ) Nat.* z)))) assoc))) ⟩
    (X ↓) ^ z • (Z ↓) ^ z • (Z ↓) ^ (toℕ (- 1ₚ) Nat.* z) • (Z ↑) ^ (toℕ (- 1ₚ) Nat.* z) • (X ↓) ^ z • (Z ↓) ^ z • (Z ↓) ^ z • (Z ↑) ^ z
      ≈⟨ cright (cright (cright (trans (sym assoc) (trans (cleft (sym (cX↓Z↑ z (toℕ (- 1ₚ) Nat.* z)))) assoc)))) ⟩
    (X ↓) ^ z • (Z ↓) ^ z • (Z ↓) ^ (toℕ (- 1ₚ) Nat.* z) • (X ↓) ^ z • (Z ↑) ^ (toℕ (- 1ₚ) Nat.* z) • (Z ↓) ^ z • (Z ↓) ^ z • (Z ↑) ^ z
      ≈⟨ cright (cright (cright (cright (trans (sym assoc) (trans (cleft (sym (cZ↓Z↑ z (toℕ (- 1ₚ) Nat.* z)))) assoc))))) ⟩
    (X ↓) ^ z • (Z ↓) ^ z • (Z ↓) ^ (toℕ (- 1ₚ) Nat.* z) • (X ↓) ^ z • (Z ↓) ^ z • (Z ↑) ^ (toℕ (- 1ₚ) Nat.* z) • (Z ↓) ^ z • (Z ↑) ^ z
      ≈⟨ cright (cright (cright (cright (cright (trans (sym assoc) (trans (cleft (sym (cZ↓Z↑ z (toℕ (- 1ₚ) Nat.* z)))) assoc)))))) ⟩
    (X ↓) ^ z • (Z ↓) ^ z • (Z ↓) ^ (toℕ (- 1ₚ) Nat.* z) • (X ↓) ^ z • (Z ↓) ^ z • (Z ↓) ^ z • (Z ↑) ^ (toℕ (- 1ₚ) Nat.* z) • (Z ↑) ^ z
      ≈⟨ cright (cright (trans (sym assoc) (trans (cleft (sym (cX↓Z↓ z (toℕ (- 1ₚ) Nat.* z)))) assoc))) ⟩
    (X ↓) ^ z • (Z ↓) ^ z • (X ↓) ^ z • (Z ↓) ^ (toℕ (- 1ₚ) Nat.* z) • (Z ↓) ^ z • (Z ↓) ^ z • (Z ↑) ^ (toℕ (- 1ₚ) Nat.* z) • (Z ↑) ^ z
      ≈⟨ cright (trans (sym assoc) (trans (cleft (sym (cX↓Z↓ z z))) assoc)) ⟩
    (X ↓) ^ z • (X ↓) ^ z • (Z ↓) ^ z • (Z ↓) ^ (toℕ (- 1ₚ) Nat.* z) • (Z ↓) ^ z • (Z ↓) ^ z • (Z ↑) ^ (toℕ (- 1ₚ) Nat.* z) • (Z ↑) ^ z
      ≈⟨ cright (cright (cright (trans (sym assoc) (trans (cleft (word-comm (toℕ (- 1ₚ) Nat.* z) z refl)) assoc)))) ⟩
    (X ↓) ^ z • (X ↓) ^ z • (Z ↓) ^ z • (Z ↓) ^ z • (Z ↓) ^ (toℕ (- 1ₚ) Nat.* z) • (Z ↓) ^ z • (Z ↑) ^ (toℕ (- 1ₚ) Nat.* z) • (Z ↑) ^ z
      ≈⟨ trans (sym assoc) (cleft (trans (sym (lemma-^-+ (X ↓) z z)) Xred↓)) ⟩
    X ↓ • (Z ↓) ^ z • (Z ↓) ^ z • (Z ↓) ^ (toℕ (- 1ₚ) Nat.* z) • (Z ↓) ^ z • (Z ↑) ^ (toℕ (- 1ₚ) Nat.* z) • (Z ↑) ^ z
      ≈⟨ cright (trans (sym assoc) (cleft (trans (sym (lemma-^-+ (Z ↓) z z)) Zred↓))) ⟩
    X ↓ • Z ↓ • (Z ↓) ^ (toℕ (- 1ₚ) Nat.* z) • (Z ↓) ^ z • (Z ↑) ^ (toℕ (- 1ₚ) Nat.* z) • (Z ↑) ^ z
      ≈⟨ cright (cright (trans (sym assoc) (cleft (trans (sym (lemma-^-+ (Z ↓) (toℕ (- 1ₚ) Nat.* z) z)) Zcancel↓)))) ⟩
    X ↓ • Z ↓ • ε • (Z ↑) ^ (toℕ (- 1ₚ) Nat.* z) • (Z ↑) ^ z
      ≈⟨ cright (cright left-unit) ⟩
    X ↓ • Z ↓ • (Z ↑) ^ (toℕ (- 1ₚ) Nat.* z) • (Z ↑) ^ z
      ≈⟨ cright (cright (trans (sym (lemma-^-+ (Z ↑) (toℕ (- 1ₚ) Nat.* z) z)) Zcancel↑)) ⟩
    X ↓ • Z ↓ • ε
      ≈⟨ cright right-unit ⟩
    X ↓ • Z ↓ ∎

  -- cross Z↑ commuting with the (up) 𝑠↑ frame gate (mirror of c10's cZ↓sd)
  cZ↑s↑ : ∀ a → (Z ↑) ^ a • (𝑠 ↑) ^ p-1 ≈ (𝑠 ↑) ^ p-1 • (Z ↑) ^ a
  cZ↑s↑ a = word-comm a p-1 (lemma-cong↑ _ _ (PB.sym (lemma-comm-𝑠-Z {m})))

  RHS-orig : Word (Gen (₂₊ m))
  RHS-orig = (𝑠 ↓) ^ p-1 • H ↓ • (𝑠 ↓) ^ p-1 • CZ • H ↓ • (𝑠 ↓) ^ p-1 • (𝑠 ↑) ^ p-1

  tail-c11 : (S ↓) ^ p-1 • H ↓ • (S ↓) ^ p-1 • CZ • H ↓ • (S ↓) ^ p-1 • (S ↑) ^ p-1
       ≈ RHS-orig • (X ↓ • Z ↓)
  tail-c11 = begin
    (S ↓) ^ p-1 • H ↓ • (S ↓) ^ p-1 • CZ • H ↓ • (S ↓) ^ p-1 • (S ↑) ^ p-1
      ≈⟨ cong fnd↓ (cong refl (cong fnd↓ (cong refl (cong refl (cong fnd↓ fnd↑))))) ⟩
    ((𝑠 ↓) ^ p-1 • (Z ↓) ^ z) • H ↓ • ((𝑠 ↓) ^ p-1 • (Z ↓) ^ z) • CZ • H ↓
      • ((𝑠 ↓) ^ p-1 • (Z ↓) ^ z) • ((𝑠 ↑) ^ p-1 • (Z ↑) ^ z)
      ≈⟨ push ⟩
    RHS-orig • (X ↓ • Z ↓) ∎
    where
    push : ((𝑠 ↓) ^ p-1 • (Z ↓) ^ z) • H ↓ • ((𝑠 ↓) ^ p-1 • (Z ↓) ^ z) • CZ • H ↓
         • ((𝑠 ↓) ^ p-1 • (Z ↓) ^ z) • ((𝑠 ↑) ^ p-1 • (Z ↑) ^ z)
         ≈ RHS-orig • (X ↓ • Z ↓)
    push = begin
      ((𝑠 ↓) ^ p-1 • (Z ↓) ^ z) • H ↓ • ((𝑠 ↓) ^ p-1 • (Z ↓) ^ z) • CZ • H ↓
        • ((𝑠 ↓) ^ p-1 • (Z ↓) ^ z) • ((𝑠 ↑) ^ p-1 • (Z ↑) ^ z)
        ≈⟨ special-assoc ((□ • □) • (□ • ((□ • □) • (□ • (□ • ((□ • □) • (□ • □)))))))
                         (□ • □ • □ • □ • □ • □ • □ • □ • □ • □ • □) auto ⟩
      (𝑠 ↓) ^ p-1 • (Z ↓) ^ z • H ↓ • (𝑠 ↓) ^ p-1 • (Z ↓) ^ z • CZ • H ↓
        • (𝑠 ↓) ^ p-1 • (Z ↓) ^ z • (𝑠 ↑) ^ p-1 • (Z ↑) ^ z
        ≈⟨ cright (cright (cright (cright (cright (cright (cright (cright
             (trans (sym assoc) (trans (cleft (cZ↓s↑ z)) assoc))))))))) ⟩
      (𝑠 ↓) ^ p-1 • (Z ↓) ^ z • H ↓ • (𝑠 ↓) ^ p-1 • (Z ↓) ^ z • CZ • H ↓
        • (𝑠 ↓) ^ p-1 • (𝑠 ↑) ^ p-1 • (Z ↓) ^ z • (Z ↑) ^ z
        ≈⟨ cright (cright (cright (cright
             (trans (sym assoc) (trans (cleft (qZCZ↓ z)) assoc))))) ⟩
      (𝑠 ↓) ^ p-1 • (Z ↓) ^ z • H ↓ • (𝑠 ↓) ^ p-1 • CZ • (Z ↓) ^ z • H ↓
        • (𝑠 ↓) ^ p-1 • (𝑠 ↑) ^ p-1 • (Z ↓) ^ z • (Z ↑) ^ z
        ≈⟨ cright (cright (cright (cright (cright
             (trans (sym assoc) (trans (cleft (qZH↓ z)) assoc)))))) ⟩
      (𝑠 ↓) ^ p-1 • (Z ↓) ^ z • H ↓ • (𝑠 ↓) ^ p-1 • CZ • H ↓ • (X ↓) ^ z
        • (𝑠 ↓) ^ p-1 • (𝑠 ↑) ^ p-1 • (Z ↓) ^ z • (Z ↑) ^ z
        ≈⟨ cright (cright (cright (cright (cright (cright
             (trans (sym assoc) (trans (cleft (qX𝑠↓ z)) (trans assoc (cright assoc)))))))) ) ⟩
      (𝑠 ↓) ^ p-1 • (Z ↓) ^ z • H ↓ • (𝑠 ↓) ^ p-1 • CZ • H ↓ • (𝑠 ↓) ^ p-1
        • (X ↓) ^ z • (Z ↓) ^ z • (𝑠 ↑) ^ p-1 • (Z ↓) ^ z • (Z ↑) ^ z
        ≈⟨ cright (cright (cright (cright (cright (cright (cright (cright
             (trans (sym assoc) (trans (cleft (cZ↓s↑ z)) assoc))))))))) ⟩
      (𝑠 ↓) ^ p-1 • (Z ↓) ^ z • H ↓ • (𝑠 ↓) ^ p-1 • CZ • H ↓ • (𝑠 ↓) ^ p-1
        • (X ↓) ^ z • (𝑠 ↑) ^ p-1 • (Z ↓) ^ z • (Z ↓) ^ z • (Z ↑) ^ z
        ≈⟨ cright (cright (cright (cright (cright (cright (cright
             (trans (sym assoc) (trans (cleft (cX↓s↑ z)) assoc)))))))) ⟩
      (𝑠 ↓) ^ p-1 • (Z ↓) ^ z • H ↓ • (𝑠 ↓) ^ p-1 • CZ • H ↓ • (𝑠 ↓) ^ p-1
        • (𝑠 ↑) ^ p-1 • (X ↓) ^ z • (Z ↓) ^ z • (Z ↓) ^ z • (Z ↑) ^ z
        ≈⟨ cright (trans (sym assoc) (trans (cleft (qZH↓ z)) assoc)) ⟩
      (𝑠 ↓) ^ p-1 • H ↓ • (X ↓) ^ z • (𝑠 ↓) ^ p-1 • CZ • H ↓ • (𝑠 ↓) ^ p-1
        • (𝑠 ↑) ^ p-1 • (X ↓) ^ z • (Z ↓) ^ z • (Z ↓) ^ z • (Z ↑) ^ z
        ≈⟨ cright (cright (trans (sym assoc) (trans (cleft (qX𝑠↓ z)) (trans assoc (cright assoc))))) ⟩
      (𝑠 ↓) ^ p-1 • H ↓ • (𝑠 ↓) ^ p-1 • (X ↓) ^ z • (Z ↓) ^ z • CZ • H ↓ • (𝑠 ↓) ^ p-1
        • (𝑠 ↑) ^ p-1 • (X ↓) ^ z • (Z ↓) ^ z • (Z ↓) ^ z • (Z ↑) ^ z
        ≈⟨ cright (cright (cright (trans (sym assoc) (trans (cleft (cX↓Z↓ z z)) assoc)))) ⟩
      (𝑠 ↓) ^ p-1 • H ↓ • (𝑠 ↓) ^ p-1 • (Z ↓) ^ z • (X ↓) ^ z • CZ • H ↓ • (𝑠 ↓) ^ p-1
        • (𝑠 ↑) ^ p-1 • (X ↓) ^ z • (Z ↓) ^ z • (Z ↓) ^ z • (Z ↑) ^ z
        ≈⟨ cright (cright (cright (cright (trans (sym assoc) (trans (cleft (qXCZ↓ z)) (trans assoc (cright assoc))))))) ⟩
      (𝑠 ↓) ^ p-1 • H ↓ • (𝑠 ↓) ^ p-1 • (Z ↓) ^ z • CZ • (X ↓) ^ z • (Z ↑) ^ (toℕ (- 1ₚ) Nat.* z) • H ↓ • (𝑠 ↓) ^ p-1
        • (𝑠 ↑) ^ p-1 • (X ↓) ^ z • (Z ↓) ^ z • (Z ↓) ^ z • (Z ↑) ^ z
        ≈⟨ cright (cright (cright (cright (cright (trans (sym assoc) (trans (cleft (cX↓Z↑ z (toℕ (- 1ₚ) Nat.* z))) assoc)))))) ⟩
      (𝑠 ↓) ^ p-1 • H ↓ • (𝑠 ↓) ^ p-1 • (Z ↓) ^ z • CZ • (Z ↑) ^ (toℕ (- 1ₚ) Nat.* z) • (X ↓) ^ z • H ↓ • (𝑠 ↓) ^ p-1
        • (𝑠 ↑) ^ p-1 • (X ↓) ^ z • (Z ↓) ^ z • (Z ↓) ^ z • (Z ↑) ^ z
        ≈⟨ cright (cright (cright (cright (cright (cright (trans (sym assoc) (trans (cleft (qXH↓ z)) assoc))))))) ⟩
      (𝑠 ↓) ^ p-1 • H ↓ • (𝑠 ↓) ^ p-1 • (Z ↓) ^ z • CZ • (Z ↑) ^ (toℕ (- 1ₚ) Nat.* z) • H ↓ • (Z ↓) ^ (toℕ (- 1ₚ) Nat.* z) • (𝑠 ↓) ^ p-1
        • (𝑠 ↑) ^ p-1 • (X ↓) ^ z • (Z ↓) ^ z • (Z ↓) ^ z • (Z ↑) ^ z
        ≈⟨ cright (cright (cright (cright (cright (cright (cright (trans (sym assoc) (trans (cleft (qZ𝑠↓ (toℕ (- 1ₚ) Nat.* z))) assoc)))))))) ⟩
      (𝑠 ↓) ^ p-1 • H ↓ • (𝑠 ↓) ^ p-1 • (Z ↓) ^ z • CZ • (Z ↑) ^ (toℕ (- 1ₚ) Nat.* z) • H ↓ • (𝑠 ↓) ^ p-1 • (Z ↓) ^ (toℕ (- 1ₚ) Nat.* z)
        • (𝑠 ↑) ^ p-1 • (X ↓) ^ z • (Z ↓) ^ z • (Z ↓) ^ z • (Z ↑) ^ z
        ≈⟨ cright (cright (cright (cright (cright (cright (cright (cright (trans (sym assoc) (trans (cleft (cZ↓s↑ (toℕ (- 1ₚ) Nat.* z))) assoc))))))))) ⟩
      (𝑠 ↓) ^ p-1 • H ↓ • (𝑠 ↓) ^ p-1 • (Z ↓) ^ z • CZ • (Z ↑) ^ (toℕ (- 1ₚ) Nat.* z) • H ↓ • (𝑠 ↓) ^ p-1
        • (𝑠 ↑) ^ p-1 • (Z ↓) ^ (toℕ (- 1ₚ) Nat.* z) • (X ↓) ^ z • (Z ↓) ^ z • (Z ↓) ^ z • (Z ↑) ^ z
        ≈⟨ cright (cright (cright (trans (sym assoc) (trans (cleft (qZCZ↓ z)) assoc)))) ⟩
      (𝑠 ↓) ^ p-1 • H ↓ • (𝑠 ↓) ^ p-1 • CZ • (Z ↓) ^ z • (Z ↑) ^ (toℕ (- 1ₚ) Nat.* z) • H ↓ • (𝑠 ↓) ^ p-1
        • (𝑠 ↑) ^ p-1 • (Z ↓) ^ (toℕ (- 1ₚ) Nat.* z) • (X ↓) ^ z • (Z ↓) ^ z • (Z ↓) ^ z • (Z ↑) ^ z
        ≈⟨ cright (cright (cright (cright (trans (sym assoc) (trans (cleft (cZ↓Z↑ z (toℕ (- 1ₚ) Nat.* z))) assoc))))) ⟩
      (𝑠 ↓) ^ p-1 • H ↓ • (𝑠 ↓) ^ p-1 • CZ • (Z ↑) ^ (toℕ (- 1ₚ) Nat.* z) • (Z ↓) ^ z • H ↓ • (𝑠 ↓) ^ p-1
        • (𝑠 ↑) ^ p-1 • (Z ↓) ^ (toℕ (- 1ₚ) Nat.* z) • (X ↓) ^ z • (Z ↓) ^ z • (Z ↓) ^ z • (Z ↑) ^ z
        ≈⟨ cright (cright (cright (cright (cright (trans (sym assoc) (trans (cleft (qZH↓ z)) assoc)))))) ⟩
      (𝑠 ↓) ^ p-1 • H ↓ • (𝑠 ↓) ^ p-1 • CZ • (Z ↑) ^ (toℕ (- 1ₚ) Nat.* z) • H ↓ • (X ↓) ^ z • (𝑠 ↓) ^ p-1
        • (𝑠 ↑) ^ p-1 • (Z ↓) ^ (toℕ (- 1ₚ) Nat.* z) • (X ↓) ^ z • (Z ↓) ^ z • (Z ↓) ^ z • (Z ↑) ^ z
        ≈⟨ cright (cright (cright (cright (cright (cright (trans (sym assoc) (trans (cleft (qX𝑠↓ z)) (trans assoc (cright assoc)))))))) ) ⟩
      (𝑠 ↓) ^ p-1 • H ↓ • (𝑠 ↓) ^ p-1 • CZ • (Z ↑) ^ (toℕ (- 1ₚ) Nat.* z) • H ↓ • (𝑠 ↓) ^ p-1 • (X ↓) ^ z • (Z ↓) ^ z
        • (𝑠 ↑) ^ p-1 • (Z ↓) ^ (toℕ (- 1ₚ) Nat.* z) • (X ↓) ^ z • (Z ↓) ^ z • (Z ↓) ^ z • (Z ↑) ^ z
        ≈⟨ cright (cright (cright (cright (cright (cright (cright (cright (trans (sym assoc) (trans (cleft (cZ↓s↑ z)) assoc))))))))) ⟩
      (𝑠 ↓) ^ p-1 • H ↓ • (𝑠 ↓) ^ p-1 • CZ • (Z ↑) ^ (toℕ (- 1ₚ) Nat.* z) • H ↓ • (𝑠 ↓) ^ p-1 • (X ↓) ^ z
        • (𝑠 ↑) ^ p-1 • (Z ↓) ^ z • (Z ↓) ^ (toℕ (- 1ₚ) Nat.* z) • (X ↓) ^ z • (Z ↓) ^ z • (Z ↓) ^ z • (Z ↑) ^ z
        ≈⟨ cright (cright (cright (cright (cright (cright (cright (trans (sym assoc) (trans (cleft (cX↓s↑ z)) assoc)))))))) ⟩
      (𝑠 ↓) ^ p-1 • H ↓ • (𝑠 ↓) ^ p-1 • CZ • (Z ↑) ^ (toℕ (- 1ₚ) Nat.* z) • H ↓ • (𝑠 ↓) ^ p-1
        • (𝑠 ↑) ^ p-1 • (X ↓) ^ z • (Z ↓) ^ z • (Z ↓) ^ (toℕ (- 1ₚ) Nat.* z) • (X ↓) ^ z • (Z ↓) ^ z • (Z ↓) ^ z • (Z ↑) ^ z
        ≈⟨ cright (cright (cright (cright (trans (sym assoc) (trans (cleft (cZ↑H↓ (toℕ (- 1ₚ) Nat.* z))) assoc))))) ⟩
      (𝑠 ↓) ^ p-1 • H ↓ • (𝑠 ↓) ^ p-1 • CZ • H ↓ • (Z ↑) ^ (toℕ (- 1ₚ) Nat.* z) • (𝑠 ↓) ^ p-1
        • (𝑠 ↑) ^ p-1 • (X ↓) ^ z • (Z ↓) ^ z • (Z ↓) ^ (toℕ (- 1ₚ) Nat.* z) • (X ↓) ^ z • (Z ↓) ^ z • (Z ↓) ^ z • (Z ↑) ^ z
        ≈⟨ cright (cright (cright (cright (cright (trans (sym assoc) (trans (cleft (cZ↑s↓ (toℕ (- 1ₚ) Nat.* z))) assoc)))))) ⟩
      (𝑠 ↓) ^ p-1 • H ↓ • (𝑠 ↓) ^ p-1 • CZ • H ↓ • (𝑠 ↓) ^ p-1 • (Z ↑) ^ (toℕ (- 1ₚ) Nat.* z)
        • (𝑠 ↑) ^ p-1 • (X ↓) ^ z • (Z ↓) ^ z • (Z ↓) ^ (toℕ (- 1ₚ) Nat.* z) • (X ↓) ^ z • (Z ↓) ^ z • (Z ↓) ^ z • (Z ↑) ^ z
        ≈⟨ cright (cright (cright (cright (cright (cright (trans (sym assoc) (trans (cleft (cZ↑s↑ (toℕ (- 1ₚ) Nat.* z))) assoc))))))) ⟩
      (𝑠 ↓) ^ p-1 • H ↓ • (𝑠 ↓) ^ p-1 • CZ • H ↓ • (𝑠 ↓) ^ p-1 • (𝑠 ↑) ^ p-1
        • (Z ↑) ^ (toℕ (- 1ₚ) Nat.* z) • (X ↓) ^ z • (Z ↓) ^ z • (Z ↓) ^ (toℕ (- 1ₚ) Nat.* z) • (X ↓) ^ z • (Z ↓) ^ z • (Z ↓) ^ z • (Z ↑) ^ z
        ≈⟨ trans (cright (cright (cright (cright (cright (cright (cright collect-tail↓)))))))
                 (special-assoc (□ • □ • □ • □ • □ • □ • □ • □ • □)
                                ((□ • □ • □ • □ • □ • □ • □) • (□ • □)) auto) ⟩
      RHS-orig • (X ↓ • Z ↓) ∎



-- ====================================================================
-- Completeness: the original (𝑠-form) selinger relations hold in the
-- Simplified presentation.  From the Simplified selinger axiom + the
-- tail-lemma (RHS_simp ≈ RHS_orig·X·Z) by right-cancelling X·Z.
-- ====================================================================
module Completeness-S (m : ℕ) where
  open PB ((₂₊ m) QRel,_===_)
  open PP ((₂₊ m) QRel,_===_)
  open Pattern-Assoc
  open Group-Lemmas (Gen (₂₊ m)) ((₂₊ m) QRel,_===_) (Simplified-GroupLike-S.grouplike {₂₊ m})

  completeness-c10 : CZ • H ↑ • CZ ≈ C10.RHS-orig m
  completeness-c10 = lemma-right-cancel {h = X ↑ • Z ↑}
    (trans (by-assoc auto) (trans (axiom selinger-c10) (C10.tail-c10 m)))

  completeness-c11 : CZ • H ↓ • CZ ≈ C11.RHS-orig m
  completeness-c11 = lemma-right-cancel {h = X ↓ • Z ↓}
    (trans (by-assoc auto) (trans (axiom selinger-c11) (C11.tail-c11 m)))


