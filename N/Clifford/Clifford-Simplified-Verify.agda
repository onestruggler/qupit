{-# OPTIONS --termination-depth=20 #-}
{-# OPTIONS --inversion-max-depth=1000 #-}

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
import Presentation.Horizontal-Syntactics as PB
import Presentation.Properties as PP
open import Presentation.Construct.Base hiding (_*_)
open import Presentation.Tactics
import Data.Nat.Properties as NP
open import Data.Nat.DivMod using (_%_ ; _/_ ; m≡m%n+[m/n]*n ; m%n<n ; m*n%n≡0)
open import Data.Fin.Properties using (toℕ-fromℕ<)
open import Data.Nat.Primality
open import Zp.ModularArithmetic
open import Zp.Fermats-little-theorem
open import Notations

module N.Clifford.Clifford-Simplified-Verify
  (p-3 : ℕ)
  (let p-2 = ₁₊ p-3)
  (p-prime : Prime (suc (₁₊ p-2)))
  (let open PrimeModulus' p-2 p-prime)
  (g*@(g , g≠0) : ℤ* ₚ)
  (g-gen : ∀ ((x , _) : ℤ* ₚ) -> ∃ \ (k : ℤ ₚ-₁) -> x ≡ g ^′ toℕ k )
  where


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
  order-X↑ = trans (refl' (Eq.sym (lemma-↑^ p X))) (lemma-cong↑ _ _ (Lemmas1.lemma-order-X m))
  order-Z↑ : (Z ↑) ^ p ≈ ε
  order-Z↑ = trans (refl' (Eq.sym (lemma-↑^ p Z))) (lemma-cong↑ _ _ (Lemmas1.lemma-order-Z m))

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



  soundness-c10 : CZ • H ↑ • CZ • X ↑ • Z ↑
                ≈ (S ↑) ^ p-1 • H ↑ • (S ↑) ^ p-1 • CZ • H ↑ • (S ↑) ^ p-1 • (S ↓) ^ p-1
  soundness-c10 = begin
    CZ • H ↑ • CZ • X ↑ • Z ↑
      ≈⟨ by-assoc auto ⟩
    (CZ • H ↑ • CZ) • (X ↑ • Z ↑)
      ≈⟨ cleft (axiom selinger-c10) ⟩
    RHS-orig • (X ↑ • Z ↑)
      ≈⟨ sym tail-c10 ⟩
    (S ↑) ^ p-1 • H ↑ • (S ↑) ^ p-1 • CZ • H ↑ • (S ↑) ^ p-1 • (S ↓) ^ p-1 ∎
------------------------------------------------------------------------
-- Soundness of the simplified selinger-c11: the ↑↔↓ mirror of c10.
-- Main qubit is ↓ (the base, identity); other qubit is ↑ (the lift).
------------------------------------------------------------------------
module C11 (m : ℕ) where
  open PB ((₂₊ m) QRel,_===_)
  open PP ((₂₊ m) QRel,_===_)
  open SR word-setoid
  open Pattern-Assoc
  open Lemmas-Clifford using (lemma-cong↑ ; lemma-↑^ ; lemma-Induction
                            ; lemma-comm-Z-w↑ ; lemma-comm-X-w↑ ; lemma-comm-H-w↑)
  open Lemmas1b (₁₊ m) using (conj-H-X^k)   -- down (base) H-conjugation at ₂₊ m

  z : ℕ
  z = toℕ 1/2

  order-Z↓ : (Z ↓) ^ p ≈ ε
  order-Z↓ = Lemmas1.lemma-order-Z (₁₊ m)
  order-X↓ : (X ↓) ^ p ≈ ε
  order-X↓ = Lemmas1.lemma-order-X (₁₊ m)
  order-Z↑ : (Z ↑) ^ p ≈ ε
  order-Z↑ = trans (refl' (Eq.sym (lemma-↑^ p Z))) (lemma-cong↑ _ _ (Lemmas1.lemma-order-Z m))

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


  soundness-c11 : CZ • H ↓ • CZ • X ↓ • Z ↓
                ≈ (S ↓) ^ p-1 • H ↓ • (S ↓) ^ p-1 • CZ • H ↓ • (S ↓) ^ p-1 • (S ↑) ^ p-1
  soundness-c11 = begin
    CZ • H ↓ • CZ • X ↓ • Z ↓
      ≈⟨ by-assoc auto ⟩
    (CZ • H ↓ • CZ) • (X ↓ • Z ↓)
      ≈⟨ cleft (axiom selinger-c11) ⟩
    RHS-orig • (X ↓ • Z ↓)
      ≈⟨ sym tail-c11 ⟩
    (S ↓) ^ p-1 • H ↓ • (S ↓) ^ p-1 • CZ • H ↓ • (S ↓) ^ p-1 • (S ↑) ^ p-1 ∎