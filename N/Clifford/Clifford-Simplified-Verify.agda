{-# OPTIONS --allow-unsolved-metas #-}
{-# OPTIONS --termination-depth=20 #-}

-- Scratch file: verifying that the simplified `selinger` relations are
-- sound consequences of the original Clifford-Relations axioms.

open import Level using (0ℓ)
open import Relation.Binary.PropositionalEquality using (_≡_ ; _≢_)
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
import Data.Nat.Properties as NP
open import Data.Nat.Primality
open import Zp.ModularArithmetic
open import Zp.Fermats-little-theorem

module N.Clifford.Clifford-Simplified-Verify
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
open Clifford-Relations
open import N.Clifford.Clifford-Lemmas p-3 p-prime g* g-gen hiding (module CL ; module CLb)

-- Foundational fact: S⁻¹ = 𝑠⁻¹ · Z^½  (since 𝑠 = S · Z^½ and S,Z commute).
module _ (n : ℕ) where
  open PB ((₁₊ n) QRel,_===_)
  open PP ((₁₊ n) QRel,_===_)
  open SR word-setoid
  open Lemmas1 n using (lemma-order-Z ; lemma-comm-Z-S)

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
  open Lemmas1 m using (lemma-order-𝑠 ; lemma-order-H)
  open Lemmas-Clifford using (lemma-Induction)
  open Lemmas1b m using (conj-H-X^k ; lemma-HH-Z)

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
  bXH : ∀ a → X ^ a • H ≈ H • (Z^ (- ₁)) ^ a
  bXH a = begin
    X ^ a • H                              ≈⟨ sym left-unit ⟩
    ε • (X ^ a • H)                        ≈⟨ cleft (sym lemma-order-H) ⟩
    H ^ 4 • (X ^ a • H)                    ≈⟨ assoc ⟩
    H • (H ^ 3 • (X ^ a • H))              ≈⟨ cright claim ⟩
    H • (Z^ (- ₁)) ^ a ∎
    where
    claim : H ^ 3 • (X ^ a • H) ≈ (Z^ (- ₁)) ^ a
    claim = begin
      H ^ 3 • (X ^ a • H)                  ≈⟨ cleft (lemma-^-+ H 2 1) ⟩
      (H ^ 2 • H) • (X ^ a • H)            ≈⟨ assoc ⟩
      H ^ 2 • (H • (X ^ a • H))            ≈⟨ cright (sym assoc) ⟩
      H ^ 2 • ((H • X ^ a) • H)            ≈⟨ cright (cleft (conj-H-X^k a)) ⟩
      H ^ 2 • ((Z ^ a • H) • H)            ≈⟨ cright assoc ⟩
      H ^ 2 • (Z ^ a • (H • H))            ≈⟨ sym assoc ⟩
      (H ^ 2 • Z ^ a) • (H • H)            ≈⟨ cleft (lemma-Induction lemma-HH-Z a) ⟩
      ((Z^ (- ₁)) ^ a • (H • H)) • (H • H) ≈⟨ assoc ⟩
      (Z^ (- ₁)) ^ a • ((H • H) • (H • H)) ≈⟨ cright (by-assoc auto) ⟩
      (Z^ (- ₁)) ^ a • H ^ 4               ≈⟨ cright lemma-order-H ⟩
      (Z^ (- ₁)) ^ a • ε                   ≈⟨ right-unit ⟩
      (Z^ (- ₁)) ^ a ∎


------------------------------------------------------------------------
-- Soundness of the simplified selinger-c10 in the Clifford presentation.
-- We work on the ↑ qubit at level (₂₊ m); base conjugation lemmas
-- (level ₁₊ m) are lifted via cong↑ / lemma-↑^.
------------------------------------------------------------------------
module C10 (m : ℕ) where
  open PB ((₂₊ m) QRel,_===_)
  open PP ((₂₊ m) QRel,_===_)
  open SR word-setoid
  open Lemmas-Clifford using (lemma-cong↑ ; lemma-↑^ ; lemma-Induction ; lemma-comm-Z-w↑)
  open Lemmas1b m using (conj-H-X^k ; conj-H-Z ; lemma-HH-Z ; lemma-HH-X)
  -- Z↓ lives at level ₂₊ m, i.e. the base Z of Lemmas1 (₁₊ m)
  order-Z↓ : (Z ↓) ^ p ≈ ε
  order-Z↓ = Lemmas1.lemma-order-Z (₁₊ m)

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

  -- X↑ through H↑  (X•H = H•Z⁻¹)
  qXH : ∀ a → (X ↑) ^ a • (H ↑) ≈ (H ↑) • ((Z ↑) ^ toℕ (- ₁)) ^ a
  qXH a = trans (refl' (Eq.cong (_• (H ↑)) (Eq.sym (lemma-↑^ a X))))
          (trans (lemma-cong↑ _ _ (C10Base.bXH m a))
                 (refl' (Eq.cong ((H ↑) •_)
                                 (Eq.trans (lemma-↑^ a (Z^ (- ₁)))
                                           (Eq.cong (_^ a) (lemma-↑^ (toℕ (- ₁)) Z))))))

  -- CZ • X↑^a ≈ X↑^a • Z↓^a • CZ
  relpow : ∀ a → CZ • (X ↑) ^ a ≈ (X ↑) ^ a • (Z ↓) ^ a • CZ
  relpow a = trans (lemma-Induction (trans (axiom rel-X↑-CZ) (sym assoc)) a)
                   (trans (cleft (lemma-^-• (X ↑) (Z ↓) a (sym (lemma-comm-Z-w↑ X)))) assoc)

  -- Z↓^a • Z↓^(-a) ≈ ε
  Z↓inv : ∀ a → (Z ↓) ^ a • ((Z ↓) ^ toℕ (- ₁)) ^ a ≈ ε
  Z↓inv a = begin
    (Z ↓) ^ a • ((Z ↓) ^ toℕ (- ₁)) ^ a    ≈⟨ cright (lemma-^^ (Z ↓) (toℕ (- ₁)) a) ⟩
    (Z ↓) ^ a • (Z ↓) ^ (toℕ (- ₁) Nat.* a) ≈⟨ sym (lemma-^-+ (Z ↓) a (toℕ (- ₁) Nat.* a)) ⟩
    (Z ↓) ^ (a Nat.+ toℕ (- ₁) Nat.* a)     ≡⟨ Eq.cong ((Z ↓) ^_) arith ⟩
    (Z ↓) ^ (p Nat.* a)                     ≈⟨ sym (lemma-^^ (Z ↓) p a) ⟩
    ((Z ↓) ^ p) ^ a                         ≈⟨ lemma-^-cong ((Z ↓) ^ p) ε a order-Z↓ ⟩
    ε ^ a                                   ≈⟨ lemma-ε^k=ε a ⟩
    ε ∎
    where
    arith : a Nat.+ toℕ (- ₁) Nat.* a ≡ p Nat.* a
    arith = Eq.cong (λ t → a Nat.+ t Nat.* a) lemma-toℕ-1ₚ

  -- X↑ through CZ  (X↑•CZ ≈ CZ•X↑•Z↓⁻¹)
  qXCZ : ∀ a → (X ↑) ^ a • CZ ≈ CZ • (X ↑) ^ a • ((Z ↓) ^ toℕ (- ₁)) ^ a
  qXCZ a = begin
    (X ↑) ^ a • CZ
      ≈⟨ sym right-unit ⟩
    ((X ↑) ^ a • CZ) • ε
      ≈⟨ cright (sym (Z↓inv a)) ⟩
    ((X ↑) ^ a • CZ) • ((Z ↓) ^ a • ((Z ↓) ^ toℕ (- ₁)) ^ a)
      ≈⟨ sym assoc ⟩
    (((X ↑) ^ a • CZ) • (Z ↓) ^ a) • ((Z ↓) ^ toℕ (- ₁)) ^ a
      ≈⟨ cleft step ⟩
    (CZ • (X ↑) ^ a) • ((Z ↓) ^ toℕ (- ₁)) ^ a
      ≈⟨ assoc ⟩
    CZ • (X ↑) ^ a • ((Z ↓) ^ toℕ (- ₁)) ^ a ∎
    where
    step : ((X ↑) ^ a • CZ) • (Z ↓) ^ a ≈ CZ • (X ↑) ^ a
    step = begin
      ((X ↑) ^ a • CZ) • (Z ↓) ^ a   ≈⟨ assoc ⟩
      (X ↑) ^ a • (CZ • (Z ↓) ^ a)   ≈⟨ cright (sym (word-comm a 1 (lemma-comm-Z-CZ {m}))) ⟩
      (X ↑) ^ a • ((Z ↓) ^ a • CZ)   ≈⟨ sym (relpow a) ⟩
      CZ • (X ↑) ^ a ∎
