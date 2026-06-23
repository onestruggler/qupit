{-# OPTIONS --termination-depth=20 #-}
{-# OPTIONS --inversion-max-depth=1000 #-}

------------------------------------------------------------------------
-- Completeness for the *simplified* semi-M relations.
--
-- This is the Simplified-presentation twin of N.Clifford.Mg-Simplify.
-- It re-derives the Mg decomposition machinery (M-decomp + Pauli push)
-- against the Simplified axioms (every step uses only shared structural
-- axioms, so the proofs copy verbatim), and then runs that machinery in
-- reverse: from the simplified axioms (semi-M*, now Wg-based) it recovers
-- the *original* Mg-form relations as `completeness-semi-M*`:
--
--     completeness-semi-M𝑠   :  Mg  · 𝑠  ≈ 𝑠^(g²) · Mg
--     completeness-semi-M↑CZ :  Mg↑ · CZ ≈ CZ^g · Mg↑
--     completeness-semi-M↓CZ :  Mg  · CZ ≈ CZ^g · Mg
--
-- Together with the soundness twin (Mg-Simplify, in the Clifford
-- presentation) this bridges the two presentations for the iso.
------------------------------------------------------------------------

open import Level using (0ℓ)
open import Relation.Binary.PropositionalEquality using (_≡_ ; _≢_ ; module ≡-Reasoning) renaming ([_] to [_]')
import Relation.Binary.Reasoning.Setoid as SR
import Relation.Binary.PropositionalEquality as Eq
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂ ; ∃)
open import Data.Nat hiding (_^_ ; _+_ ; _*_ ; _%_ ; _/_)
import Data.Nat as Nat
open import Data.Nat.DivMod
open import Data.Fin hiding (_+_ ; _-_)
open import Data.Fin.Properties using (toℕ-inject₁ ; toℕ-fromℕ ; toℕ<n ; toℕ-fromℕ<)
import Data.Nat.Properties as NP
open import Word.Base as WB hiding (wfoldl)
import Presentation.Base as PB
import Presentation.Properties as PP
open import Presentation.Construct.Base hiding (_*_)
open import Presentation.GroupLike
open import Presentation.Tactics
open import Data.Nat.Primality
open import Zp.ModularArithmetic
open import Zp.Fermats-little-theorem

module N.Clifford.Mg-Simplify-S
  (p-3 : ℕ)
  (let p-2 = suc p-3)
  (p-prime : Prime (suc (suc p-2)))
  (let open PrimeModulus' p-2 p-prime)
  (g*@(g , g≠0) : ℤ* ₚ)
  (g-gen : ∀ ((x , _) : ℤ* ₚ) -> ∃ \ (k : ℤ ₚ-₁) -> x ≡ g ^′ toℕ k )
  where

pattern auto = Eq.refl
pattern ₁₊ n = suc n
pattern ₂₊ n = suc (suc n)

open Primitive-Root-Modp' g* g-gen
-- inherit the derived words (S,H,Z,𝑠,M,Mg,…) from Clifford-Relations,
-- but take the *relation* and axioms from the Simplified presentation.
open import N.Clifford.Clifford-Mod-Scalar p-3 p-prime g* g-gen
open Clifford-Relations hiding
  ( _QRel,_===_ ; order-S ; order-H ; M-power ; semi-M𝑠 ; order-SH ; comm-HHSHHS
  ; comm-X-Z ; semi-M↑CZ ; semi-M↓CZ ; rel-X↑-CZ ; rel-X↓-CZ ; order-CZ
  ; comm-CZ-S↓ ; comm-CZ-S↑ ; selinger-c10 ; selinger-c11 ; selinger-c12
  ; selinger-c13 ; selinger-c14 ; selinger-c15 ; comm-H ; comm-S ; comm-CZ ; cong↑ )
open import N.Clifford.Clifford-Mod-Scalars-Simplified p-3 p-prime g* g-gen
open Simplified-Relations
open import N.Clifford.Simplified-Lemmas p-3 p-prime g* g-gen
open Lemmas-Clifford-S
open Simplified-GroupLike-S
-- (CL = Lemmas1-S and CLb = Lemmas1b-S are re-exported by Simplified-Lemmas)

-- ── collect the Paulis out of an 𝑠-power: 𝑠^k = S^k · Z^(k·½) ──
𝑠-collect : ∀ {n} k -> let open PB ((₁₊ n) QRel,_===_) in
  𝑠 ^ k ≈ S ^ k • Z ^ (k Nat.* toℕ 1/2)
𝑠-collect {n} k = begin
  (S • Z ^ toℕ 1/2) ^ k          ≈⟨ lemma-^-• S (Z ^ toℕ 1/2) k commSZ ⟩
  S ^ k • (Z ^ toℕ 1/2) ^ k      ≈⟨ cright (lemma-^^ Z (toℕ 1/2) k) ⟩
  S ^ k • Z ^ (toℕ 1/2 Nat.* k)  ≈⟨ cright (refl' (Eq.cong (Z ^_) (NP.*-comm (toℕ 1/2) k))) ⟩
  S ^ k • Z ^ (k Nat.* toℕ 1/2) ∎
  where
  open PB ((₁₊ n) QRel,_===_)
  open PP ((₁₊ n) QRel,_===_)
  open SR word-setoid
  commSZ : S • Z ^ toℕ 1/2 ≈ Z ^ toℕ 1/2 • S
  commSZ = word-comm 1 (toℕ 1/2) (sym (CL.lemma-comm-Z-S n))

-- ── expand M x: collect Paulis out of all three 𝑠-powers ──
module _ (x : ℤ* ₚ) where
  private
    a = toℕ (x .proj₁)
    b = toℕ ((x ⁻¹) .proj₁)
    z = toℕ 1/2

  M-expand : ∀ {n} -> let open PB ((₁₊ n) QRel,_===_) in
    M x ≈ (S ^ a • Z ^ (a Nat.* z)) • H • (S ^ b • Z ^ (b Nat.* z)) • H • (S ^ a • Z ^ (a Nat.* z)) • H
  M-expand {n} = begin
    𝑠 ^ a • H • 𝑠 ^ b • H • 𝑠 ^ a • H
      ≈⟨ cong (𝑠-collect a) (cong refl (cong (𝑠-collect b) (cong refl (cong (𝑠-collect a) refl)))) ⟩
    (S ^ a • Z ^ (a Nat.* z)) • H • (S ^ b • Z ^ (b Nat.* z)) • H • (S ^ a • Z ^ (a Nat.* z)) • H ∎
    where
    open PB ((₁₊ n) QRel,_===_)
    open PP ((₁₊ n) QRel,_===_)
    open SR word-setoid

-- ── helper push-rules for the M decomposition cascade ──
Sᵏ : ℤ ₚ -> ∀ {n} -> Word (Gen (₁₊ n))
Sᵏ k = S ^ toℕ k

module Push (n : ℕ) where
  open PB ((₁₊ n) QRel,_===_)
  open PP ((₁₊ n) QRel,_===_)
  open SR word-setoid
  open Pattern-Assoc
  open import Algebra.Properties.Ring (+-*-ring p-2)

  Zmod : ∀ k -> Z ^ k ≈ Z ^ (k % p)
  Zmod k = begin
    Z ^ k                               ≡⟨ Eq.cong (Z ^_) (m≡m%n+[m/n]*n k p) ⟩
    Z ^ (k % p Nat.+ k / p Nat.* p)     ≈⟨ lemma-^-+ Z (k % p) (k / p Nat.* p) ⟩
    Z ^ (k % p) • Z ^ (k / p Nat.* p)   ≈⟨ cright (refl' (Eq.cong (Z ^_) (NP.*-comm (k / p) p))) ⟩
    Z ^ (k % p) • Z ^ (p Nat.* (k / p)) ≈⟨ cright (sym (lemma-^^ Z p (k / p))) ⟩
    Z ^ (k % p) • (Z ^ p) ^ (k / p)     ≈⟨ cright (lemma-^-cong (Z ^ p) ε (k / p) (CL.lemma-order-Z n)) ⟩
    Z ^ (k % p) • ε ^ (k / p)           ≈⟨ cright (lemma-ε^k=ε (k / p)) ⟩
    Z ^ (k % p) • ε                     ≈⟨ right-unit ⟩
    Z ^ (k % p) ∎

  Xmod : ∀ k -> X ^ k ≈ X ^ (k % p)
  Xmod k = begin
    X ^ k                               ≡⟨ Eq.cong (X ^_) (m≡m%n+[m/n]*n k p) ⟩
    X ^ (k % p Nat.+ k / p Nat.* p)     ≈⟨ lemma-^-+ X (k % p) (k / p Nat.* p) ⟩
    X ^ (k % p) • X ^ (k / p Nat.* p)   ≈⟨ cright (refl' (Eq.cong (X ^_) (NP.*-comm (k / p) p))) ⟩
    X ^ (k % p) • X ^ (p Nat.* (k / p)) ≈⟨ cright (sym (lemma-^^ X p (k / p))) ⟩
    X ^ (k % p) • (X ^ p) ^ (k / p)     ≈⟨ cright (lemma-^-cong (X ^ p) ε (k / p) (CL.lemma-order-X n)) ⟩
    X ^ (k % p) • ε ^ (k / p)           ≈⟨ cright (lemma-ε^k=ε (k / p)) ⟩
    X ^ (k % p) • ε                     ≈⟨ right-unit ⟩
    X ^ (k % p) ∎

  -- Z^j · H ≈ H · X^j
  R1 : ∀ (j : ℤ ₚ) -> Z ^ toℕ j • H ≈ H • X ^ toℕ j
  R1 j = sym (CLb.conj-H-X^k n (toℕ j))

  -- Z^j · S^m ≈ S^m · Z^j   (Z, S commute)
  ZcommS : ∀ (j : ℤ ₚ) (m : ℕ) -> Z ^ toℕ j • S ^ m ≈ S ^ m • Z ^ toℕ j
  ZcommS j m = word-comm (toℕ j) m (CL.lemma-comm-Z-S n)

  -- H · Z^k ≈ X^((p-1)·k) · H
  conjHZ1 : H • Z ≈ X ^ toℕ (- 1ₚ) • H
  conjHZ1 = CLb.conj-H-Z n
  conjHZk : ∀ k -> H • Z ^ k ≈ X ^ (p-1 Nat.* k) • H
  conjHZk k = trans (lemma-Induction conjHZ1 k)
              (cleft (trans (lemma-^^ X (toℕ (- 1ₚ)) k)
                      (refl' (Eq.cong (X ^_) (Eq.cong (Nat._* k) lemma-toℕ-1ₚ)))))

  -- X^j · H ≈ H · Z^(-j)
  R2 : ∀ (j : ℤ ₚ) -> X ^ toℕ j • H ≈ H • Z ^ toℕ (- j)
  R2 j = sym (trans (conjHZk (toℕ (- j))) (cleft xeq))
    where
    arith : (p-1 Nat.* toℕ (- j)) % p ≡ toℕ j
    arith = Eq.trans (Eq.cong (λ t → (t Nat.* toℕ (- j)) % p) (Eq.sym lemma-toℕ-1ₚ))
            (Eq.trans (lemma-toℕ-% (- 1ₚ) (- j)) (Eq.cong toℕ ring))
      where ring : (- 1ₚ) * (- j) ≡ j
            ring = Eq.trans (-1*x≈-x (- j)) (-‿involutive j)
    xeq : X ^ (p-1 Nat.* toℕ (- j)) ≈ X ^ toℕ j
    xeq = trans (Xmod (p-1 Nat.* toℕ (- j))) (refl' (Eq.cong (X ^_) arith))

  -- X · S ≈ S · X · Z^(p-1)
  Spush1 : X • S ≈ S • X • Z ^ p-1
  Spush1 = sym (begin
    S • X • Z ^ p-1          ≈⟨ sym assoc ⟩
    (S • X) • Z ^ p-1        ≈⟨ cleft (CLb.conj-S-X n) ⟩
    ((X • Z) • S) • Z ^ p-1  ≈⟨ assoc ⟩
    (X • Z) • (S • Z ^ p-1)  ≈⟨ cright (word-comm 1 p-1 (sym (CL.lemma-comm-Z-S n))) ⟩
    (X • Z) • (Z ^ p-1 • S)  ≈⟨ assoc ⟩
    X • (Z • (Z ^ p-1 • S))  ≈⟨ cright (sym assoc) ⟩
    X • ((Z • Z ^ p-1) • S)  ≈⟨ cright (cleft (sym (lemma-^-+ Z 1 p-1))) ⟩
    X • (Z ^ p • S)          ≈⟨ cright (cleft (CL.lemma-order-Z n)) ⟩
    X • (ε • S)              ≈⟨ cright left-unit ⟩
    X • S ∎)

  -- X^k · S ≈ S · X^k · Z^((p-1)·k)
  SpushK : ∀ k -> X ^ k • S ≈ S • X ^ k • Z ^ (p-1 Nat.* k)
  SpushK k = trans (lemma-Inductionˡ Spush1 k) (cright step)
    where
    commXZ : X • Z ^ p-1 ≈ Z ^ p-1 • X
    commXZ = word-comm 1 p-1 (axiom comm-X-Z)
    step : (X • Z ^ p-1) ^ k ≈ X ^ k • Z ^ (p-1 Nat.* k)
    step = trans (lemma-^-• X (Z ^ p-1) k commXZ) (cright (lemma-^^ Z p-1 k))

  -- X^k · S^m ≈ S^m · X^k · Z^(m·(p-1)·k)
  SpushKM : ∀ k m -> X ^ k • S ^ m ≈ S ^ m • X ^ k • Z ^ (m Nat.* (p-1 Nat.* k))
  SpushKM k 0 = begin
    X ^ k • ε                       ≈⟨ right-unit ⟩
    X ^ k                           ≈⟨ sym left-unit ⟩
    ε • X ^ k                       ≈⟨ sym right-unit ⟩
    (ε • X ^ k) • ε                 ≈⟨ assoc ⟩
    ε • X ^ k • ε ∎
  SpushKM k (suc m') = begin
    X ^ k • S ^ suc m'                       ≈⟨ cright (lemma-^-+ S 1 m') ⟩
    X ^ k • (S • S ^ m')                     ≈⟨ sym assoc ⟩
    (X ^ k • S) • S ^ m'                     ≈⟨ cleft (SpushK k) ⟩
    (S • X ^ k • Z ^ N) • S ^ m'             ≈⟨ assoc ⟩
    S • (X ^ k • Z ^ N) • S ^ m'             ≈⟨ cright assoc ⟩
    S • X ^ k • (Z ^ N • S ^ m')             ≈⟨ cright (cright (word-comm N m' (CL.lemma-comm-Z-S n))) ⟩
    S • X ^ k • (S ^ m' • Z ^ N)             ≈⟨ cright (sym assoc) ⟩
    S • (X ^ k • S ^ m') • Z ^ N             ≈⟨ cright (cleft (SpushKM k m')) ⟩
    S • (S ^ m' • X ^ k • Z ^ (m' Nat.* N)) • Z ^ N
                                             ≈⟨ cright assoc ⟩
    S • S ^ m' • (X ^ k • Z ^ (m' Nat.* N)) • Z ^ N
                                             ≈⟨ cright (cright assoc) ⟩
    S • S ^ m' • X ^ k • (Z ^ (m' Nat.* N) • Z ^ N)
                                             ≈⟨ cright (cright (cright (sym (lemma-^-+ Z (m' Nat.* N) N)))) ⟩
    S • S ^ m' • X ^ k • Z ^ (m' Nat.* N Nat.+ N)
                                             ≈⟨ cright (cright (cright (refl' (Eq.cong (Z ^_) (NP.+-comm (m' Nat.* N) N))))) ⟩
    S • S ^ m' • X ^ k • Z ^ (suc m' Nat.* N)
                                             ≈⟨ sym assoc ⟩
    (S • S ^ m') • (X ^ k • Z ^ (suc m' Nat.* N))
                                             ≈⟨ cleft (sym (lemma-^-+ S 1 m')) ⟩
    S ^ suc m' • X ^ k • Z ^ (suc m' Nat.* N) ∎
    where N = p-1 Nat.* k

  -- (p-1)² ≡ 1 (mod p)
  p-1²≡1 : ((p-1) Nat.* (p-1)) % p ≡ 1
  p-1²≡1 = Eq.trans (Eq.cong (λ t → (t Nat.* t) % p) (Eq.sym lemma-toℕ-1ₚ))
           (Eq.trans (lemma-toℕ-% (- 1ₚ) (- 1ₚ)) (Eq.cong toℕ ringfact))
    where ringfact : (- 1ₚ) * (- 1ₚ) ≡ 1ₚ
          ringfact = Eq.trans (-1*x≈-x (- 1ₚ)) (-‿involutive 1ₚ)

  -- X^e · H ≈ H · Z^((p-1)·e)
  XH : ∀ e -> X ^ e • H ≈ H • Z ^ ((p-1) Nat.* e)
  XH e = sym (trans (conjHZk ((p-1) Nat.* e)) (cleft xred))
    where
    arithXH : ((p-1) Nat.* ((p-1) Nat.* e)) % p ≡ e % p
    arithXH = Eq.trans (Eq.cong (Nat._% p) (Eq.sym (NP.*-assoc (p-1) (p-1) e)))
              (Eq.trans (%-distribˡ-* ((p-1) Nat.* (p-1)) e p)
              (Eq.trans (Eq.cong (λ t → (t Nat.* (e % p)) % p) p-1²≡1)
              (Eq.trans (Eq.cong (Nat._% p) (NP.*-identityˡ (e % p)))
              (m%n%n≡m%n e p))))
    xred : X ^ ((p-1) Nat.* ((p-1) Nat.* e)) ≈ X ^ e
    xred = trans (Xmod ((p-1) Nat.* ((p-1) Nat.* e)))
           (trans (refl' (Eq.cong (X ^_) arithXH)) (sym (Xmod e)))

  -- (S^e₁ · Z^e₂) · H ≈ S^e₁ · H · X^e₂
  blkrule : ∀ e₁ e₂ -> (S ^ e₁ • Z ^ e₂) • H ≈ S ^ e₁ • H • X ^ e₂
  blkrule e₁ e₂ = trans assoc (cright (sym (CLb.conj-H-X^k n e₂)))

-- ── the full decomposition: M x ≈ (pure S,H multiplier) · (leftover Pauli) ──

-- ── the full decomposition: M x ≈ (pure S,H multiplier) · (leftover Pauli) ──
module Decomp (n : ℕ) (x : ℤ* ₚ) where
  open PB ((₁₊ n) QRel,_===_)
  open PP ((₁₊ n) QRel,_===_)
  open SR word-setoid
  open Pattern-Assoc
  open Push n

  private
    a = toℕ (x .proj₁)
    b = toℕ ((x ⁻¹) .proj₁)
    z = toℕ 1/2

  -- push X^e past a block (S^k · H): produces a trailing Z·X pair
  pushXblk : ∀ e k -> X ^ e • (S ^ k • H) ≈ S ^ k • H • Z ^ (p-1 Nat.* e) • X ^ (k Nat.* (p-1 Nat.* e))
  pushXblk e k = begin
    X ^ e • (S ^ k • H)                              ≈⟨ sym assoc ⟩
    (X ^ e • S ^ k) • H                              ≈⟨ cleft (SpushKM e k) ⟩
    (S ^ k • X ^ e • Z ^ (k Nat.* (p-1 Nat.* e))) • H ≈⟨ assoc ⟩
    S ^ k • (X ^ e • Z ^ (k Nat.* (p-1 Nat.* e))) • H ≈⟨ cright assoc ⟩
    S ^ k • (X ^ e • (Z ^ (k Nat.* (p-1 Nat.* e)) • H)) ≈⟨ cright (cright (sym (CLb.conj-H-X^k n (k Nat.* (p-1 Nat.* e))))) ⟩
    S ^ k • (X ^ e • (H • X ^ (k Nat.* (p-1 Nat.* e)))) ≈⟨ cright (sym assoc) ⟩
    S ^ k • ((X ^ e • H) • X ^ (k Nat.* (p-1 Nat.* e))) ≈⟨ cright (cleft (XH e)) ⟩
    S ^ k • ((H • Z ^ (p-1 Nat.* e)) • X ^ (k Nat.* (p-1 Nat.* e))) ≈⟨ cright assoc ⟩
    S ^ k • H • Z ^ (p-1 Nat.* e) • X ^ (k Nat.* (p-1 Nat.* e)) ∎

  -- push Z^d · X^e past a block (S^k · H)
  pushZXblk : ∀ d e k -> Z ^ d • X ^ e • (S ^ k • H) ≈ S ^ k • H • Z ^ (p-1 Nat.* e) • X ^ (d Nat.+ k Nat.* (p-1 Nat.* e))
  pushZXblk d e k = begin
    Z ^ d • (X ^ e • (S ^ k • H))                    ≈⟨ cright (pushXblk e k) ⟩
    Z ^ d • (S ^ k • H • Z ^ N • X ^ F')             ≈⟨ sym assoc ⟩
    (Z ^ d • S ^ k) • (H • Z ^ N • X ^ F')           ≈⟨ cleft (word-comm d k (CL.lemma-comm-Z-S n)) ⟩
    (S ^ k • Z ^ d) • (H • Z ^ N • X ^ F')           ≈⟨ assoc ⟩
    S ^ k • (Z ^ d • (H • Z ^ N • X ^ F'))           ≈⟨ cright (sym assoc) ⟩
    S ^ k • ((Z ^ d • H) • (Z ^ N • X ^ F'))         ≈⟨ cright (cleft (sym (CLb.conj-H-X^k n d))) ⟩
    S ^ k • ((H • X ^ d) • (Z ^ N • X ^ F'))         ≈⟨ cright assoc ⟩
    S ^ k • (H • (X ^ d • (Z ^ N • X ^ F')))         ≈⟨ cright (cright (sym assoc)) ⟩
    S ^ k • (H • ((X ^ d • Z ^ N) • X ^ F'))         ≈⟨ cright (cright (cleft (word-comm d N (axiom comm-X-Z)))) ⟩
    S ^ k • (H • ((Z ^ N • X ^ d) • X ^ F'))         ≈⟨ cright (cright assoc) ⟩
    S ^ k • (H • (Z ^ N • (X ^ d • X ^ F')))         ≈⟨ cright (cright (cright (sym (lemma-^-+ X d F')))) ⟩
    S ^ k • H • Z ^ N • X ^ (d Nat.+ F') ∎
    where N = p-1 Nat.* e
          F' = k Nat.* (p-1 Nat.* e)

  -- the pure-S,H multiplier word
  Sₐ : Word (Gen (₁₊ n))
  Sₐ = S ^ a • H • S ^ b • H • S ^ a • H

  -- accumulated Pauli exponents from the cascade
  E = b Nat.* (p-1 Nat.* (a Nat.* z)) Nat.+ b Nat.* z
  F = (p-1 Nat.* (a Nat.* z)) Nat.+ a Nat.* (p-1 Nat.* E)

  -- convert M to block form  (S^a·H·X^(az))·(S^b·H·X^(bz))·(S^a·H·X^(az))
  M-blocks : M x ≈ (S ^ a • H • X ^ (a Nat.* z)) • (S ^ b • H • X ^ (b Nat.* z)) • (S ^ a • H • X ^ (a Nat.* z))
  M-blocks = begin
    M x ≈⟨ M-expand x ⟩
    (S ^ a • Z ^ (a Nat.* z)) • H • (S ^ b • Z ^ (b Nat.* z)) • H • (S ^ a • Z ^ (a Nat.* z)) • H
      ≈⟨ cright (cright (cright (cright (blkrule a (a Nat.* z))))) ⟩
    (S ^ a • Z ^ (a Nat.* z)) • H • (S ^ b • Z ^ (b Nat.* z)) • H • (S ^ a • H • X ^ (a Nat.* z))
      ≈⟨ cright (cright (sym assoc)) ⟩
    (S ^ a • Z ^ (a Nat.* z)) • H • ((S ^ b • Z ^ (b Nat.* z)) • H) • (S ^ a • H • X ^ (a Nat.* z))
      ≈⟨ cright (cright (cleft (blkrule b (b Nat.* z)))) ⟩
    (S ^ a • Z ^ (a Nat.* z)) • H • (S ^ b • H • X ^ (b Nat.* z)) • (S ^ a • H • X ^ (a Nat.* z))
      ≈⟨ sym assoc ⟩
    ((S ^ a • Z ^ (a Nat.* z)) • H) • (S ^ b • H • X ^ (b Nat.* z)) • (S ^ a • H • X ^ (a Nat.* z))
      ≈⟨ cleft (blkrule a (a Nat.* z)) ⟩
    (S ^ a • H • X ^ (a Nat.* z)) • (S ^ b • H • X ^ (b Nat.* z)) • (S ^ a • H • X ^ (a Nat.* z)) ∎


  -- tail-aware pushes (internalise the reassociation)
  pushXtail : ∀ e k W -> X ^ e • (S ^ k • (H • W)) ≈ S ^ k • H • Z ^ (p-1 Nat.* e) • X ^ (k Nat.* (p-1 Nat.* e)) • W
  pushXtail e k W = begin
    X ^ e • (S ^ k • (H • W))            ≈⟨ cright (sym assoc) ⟩
    X ^ e • ((S ^ k • H) • W)            ≈⟨ sym assoc ⟩
    (X ^ e • (S ^ k • H)) • W            ≈⟨ cleft (pushXblk e k) ⟩
    (S ^ k • H • Z ^ N • X ^ F') • W     ≈⟨ assoc ⟩
    S ^ k • ((H • Z ^ N • X ^ F') • W)   ≈⟨ cright assoc ⟩
    S ^ k • (H • ((Z ^ N • X ^ F') • W)) ≈⟨ cright (cright assoc) ⟩
    S ^ k • H • Z ^ N • X ^ F' • W ∎
    where N = p-1 Nat.* e
          F' = k Nat.* (p-1 Nat.* e)

  pushZXtail : ∀ d e k W -> Z ^ d • (X ^ e • (S ^ k • (H • W))) ≈ S ^ k • H • Z ^ (p-1 Nat.* e) • X ^ (d Nat.+ k Nat.* (p-1 Nat.* e)) • W
  pushZXtail d e k W = begin
    Z ^ d • (X ^ e • (S ^ k • (H • W)))  ≈⟨ cright (pushXtail e k W) ⟩
    Z ^ d • (S ^ k • H • Z ^ N • X ^ F' • W) ≈⟨ sym assoc ⟩
    (Z ^ d • S ^ k) • (H • Z ^ N • X ^ F' • W) ≈⟨ cleft (word-comm d k (CL.lemma-comm-Z-S n)) ⟩
    (S ^ k • Z ^ d) • (H • Z ^ N • X ^ F' • W) ≈⟨ assoc ⟩
    S ^ k • (Z ^ d • (H • Z ^ N • X ^ F' • W)) ≈⟨ cright (sym assoc) ⟩
    S ^ k • ((Z ^ d • H) • (Z ^ N • X ^ F' • W)) ≈⟨ cright (cleft (sym (CLb.conj-H-X^k n d))) ⟩
    S ^ k • ((H • X ^ d) • (Z ^ N • X ^ F' • W)) ≈⟨ cright assoc ⟩
    S ^ k • (H • (X ^ d • (Z ^ N • X ^ F' • W))) ≈⟨ cright (cright (sym assoc)) ⟩
    S ^ k • (H • ((X ^ d • Z ^ N) • (X ^ F' • W))) ≈⟨ cright (cright (cleft (word-comm d N (axiom comm-X-Z)))) ⟩
    S ^ k • (H • ((Z ^ N • X ^ d) • (X ^ F' • W))) ≈⟨ cright (cright assoc) ⟩
    S ^ k • (H • (Z ^ N • (X ^ d • (X ^ F' • W)))) ≈⟨ cright (cright (cright (sym assoc))) ⟩
    S ^ k • (H • (Z ^ N • ((X ^ d • X ^ F') • W))) ≈⟨ cright (cright (cright (cleft (sym (lemma-^-+ X d F'))))) ⟩
    S ^ k • H • Z ^ N • X ^ (d Nat.+ F') • W ∎
    where N = p-1 Nat.* e
          F' = k Nat.* (p-1 Nat.* e)

  -- THE DECOMPOSITION:  M x = (S^a·H·S^b·H·S^a·H) · Z^((p-1)·E) · X^(F + a·½)
  -- i.e. a pure S,H multiplier word times a leftover Pauli (Z then X).
  M-decomp : M x ≈ S ^ a • H • S ^ b • H • S ^ a • H • Z ^ (p-1 Nat.* E) • X ^ (F Nat.+ a Nat.* z)
  M-decomp = begin
    M x ≈⟨ M-blocks ⟩
    (S ^ a • H • X ^ (a Nat.* z)) • (S ^ b • H • X ^ (b Nat.* z)) • (S ^ a • H • X ^ (a Nat.* z))
      ≈⟨ trans assoc (cright (trans assoc (cright (cright (trans assoc (cright assoc)))))) ⟩
    S ^ a • H • (X ^ (a Nat.* z) • (S ^ b • (H • (X ^ (b Nat.* z) • (S ^ a • (H • X ^ (a Nat.* z)))))))
      ≈⟨ cright (cright (pushXtail (a Nat.* z) b (X ^ (b Nat.* z) • (S ^ a • (H • X ^ (a Nat.* z)))))) ⟩
    S ^ a • H • S ^ b • H • Z ^ (p-1 Nat.* (a Nat.* z)) • X ^ (b Nat.* (p-1 Nat.* (a Nat.* z))) • X ^ (b Nat.* z) • (S ^ a • (H • X ^ (a Nat.* z)))
      ≈⟨ cright (cright (cright (cright (cright (trans (sym assoc) (cleft (sym (lemma-^-+ X (b Nat.* (p-1 Nat.* (a Nat.* z))) (b Nat.* z))))))))) ⟩
    S ^ a • H • S ^ b • H • Z ^ (p-1 Nat.* (a Nat.* z)) • X ^ E • (S ^ a • (H • X ^ (a Nat.* z)))
      ≈⟨ cright (cright (cright (cright (pushZXtail (p-1 Nat.* (a Nat.* z)) E a (X ^ (a Nat.* z))))))  ⟩
    S ^ a • H • S ^ b • H • S ^ a • H • Z ^ (p-1 Nat.* E) • X ^ F • X ^ (a Nat.* z)
      ≈⟨ cright (cright (cright (cright (cright (cright (cright (sym (lemma-^-+ X F (a Nat.* z)))))))) ) ⟩
    S ^ a • H • S ^ b • H • S ^ a • H • Z ^ (p-1 Nat.* E) • X ^ (F Nat.+ a Nat.* z) ∎

  -- ════ closed form of the leftover Pauli ════
  open import Algebra.Properties.Ring (+-*-ring p-2)

  private
    α = x .proj₁
    β = (x ⁻¹) .proj₁
    hf = 1/2

  -- toℕ is an additive homomorphism mod p (from the ℤp _+_ definition)
  toℕ-+ : ∀ (c d : ℤ ₚ) -> (toℕ c Nat.+ toℕ d) % p ≡ toℕ (c + d)
  toℕ-+ c d = Eq.sym (toℕ-fromℕ< (m%n<n (toℕ c Nat.+ toℕ d) p))

  -- fold a ℕ-product whose right factor reduces to a ℤp value
  fold* : ∀ (c d : ℤ ₚ) m -> m % p ≡ toℕ d -> (toℕ c Nat.* m) % p ≡ toℕ (c * d)
  fold* c d m eq = Eq.trans (%-distribˡ-* (toℕ c) m p)
                   (Eq.trans (Eq.cong (λ t → (t Nat.* (m % p)) % p) (m<n⇒m%n≡m (toℕ<n c)))
                   (Eq.trans (Eq.cong (λ t → (toℕ c Nat.* t) % p) eq) (lemma-toℕ-% c d)))

  fold+ : ∀ (c d : ℤ ₚ) m₁ m₂ -> m₁ % p ≡ toℕ c -> m₂ % p ≡ toℕ d -> (m₁ Nat.+ m₂) % p ≡ toℕ (c + d)
  fold+ c d m₁ m₂ e1 e2 = Eq.trans (%-distribˡ-+ m₁ m₂ p)
                          (Eq.trans (Eq.cong₂ (λ s t → (s Nat.+ t) % p) e1 e2) (toℕ-+ c d))

  baseHf : z % p ≡ toℕ hf
  baseHf = m<n⇒m%n≡m (toℕ<n hf)

  -- p-1 = toℕ (-1ₚ), reduced
  base-1 : (p-1) % p ≡ toℕ (- 1ₚ)
  base-1 = Eq.trans (m<n⇒m%n≡m (NP.≤-reflexive Eq.refl)) (Eq.sym lemma-toℕ-1ₚ)

  -- ℤp ring facts
  negOne² : (- 1ₚ) * (- 1ₚ) ≡ 1ₚ
  negOne² = Eq.trans (-1*x≈-x (- 1ₚ)) (-‿involutive 1ₚ)
  βα≡1 : β * α ≡ 1ₚ
  βα≡1 = lemma-⁻¹ˡ α {{nztoℕ {y = α} {neq0 = x .proj₂}}}
  αβ≡1 : α * β ≡ 1ₚ
  αβ≡1 = Eq.trans (*-comm α β) βα≡1

  -- fold netZ = (p-1)·E to a ℤp value
  eAZ  : (a Nat.* z) % p ≡ toℕ (α * hf)
  eAZ  = fold* α hf z baseHf
  ePAZ : (p-1 Nat.* (a Nat.* z)) % p ≡ toℕ ((- 1ₚ) * (α * hf))
  ePAZ = Eq.trans (Eq.cong (λ t → (t Nat.* (a Nat.* z)) % p) (Eq.sym lemma-toℕ-1ₚ))
                  (fold* (- 1ₚ) (α * hf) (a Nat.* z) eAZ)
  eE1  : (b Nat.* (p-1 Nat.* (a Nat.* z))) % p ≡ toℕ (β * ((- 1ₚ) * (α * hf)))
  eE1  = fold* β ((- 1ₚ) * (α * hf)) (p-1 Nat.* (a Nat.* z)) ePAZ
  eE2  : (b Nat.* z) % p ≡ toℕ (β * hf)
  eE2  = fold* β hf z baseHf
  eE   : E % p ≡ toℕ (β * ((- 1ₚ) * (α * hf)) + β * hf)
  eE   = fold+ (β * ((- 1ₚ) * (α * hf))) (β * hf) (b Nat.* (p-1 Nat.* (a Nat.* z))) (b Nat.* z) eE1 eE2
  eNetZ : (p-1 Nat.* E) % p ≡ toℕ ((- 1ₚ) * (β * ((- 1ₚ) * (α * hf)) + β * hf))
  eNetZ = Eq.trans (Eq.cong (λ t → (t Nat.* E) % p) (Eq.sym lemma-toℕ-1ₚ))
                   (fold* (- 1ₚ) (β * ((- 1ₚ) * (α * hf)) + β * hf) E eE)

  -- ring-simplify the ℤp value to  (1ₚ - β)·½
  private
    lhs1 : ((- 1ₚ) * β) * (- 1ₚ) ≡ β
    lhs1 = Eq.trans (*-assoc (- 1ₚ) β (- 1ₚ))
           (Eq.trans (Eq.cong ((- 1ₚ) *_) (*-comm β (- 1ₚ)))
           (Eq.trans (Eq.sym (*-assoc (- 1ₚ) (- 1ₚ) β))
           (Eq.trans (Eq.cong (λ t → t * β) negOne²) (*-identityˡ β))))
    T1 : (- 1ₚ) * (β * ((- 1ₚ) * (α * hf))) ≡ hf
    T1 = Eq.trans (Eq.sym (*-assoc (- 1ₚ) β ((- 1ₚ) * (α * hf))))
         (Eq.trans (Eq.sym (*-assoc ((- 1ₚ) * β) (- 1ₚ) (α * hf)))
         (Eq.trans (Eq.cong (λ t → t * (α * hf)) lhs1)
         (Eq.trans (Eq.sym (*-assoc β α hf))
         (Eq.trans (Eq.cong (λ t → t * hf) βα≡1) (*-identityˡ hf)))))
    T2 : (- 1ₚ) * (β * hf) ≡ (- β) * hf
    T2 = Eq.trans (Eq.sym (*-assoc (- 1ₚ) β hf)) (Eq.cong (λ t → t * hf) (-1*x≈-x β))

  ringZ : (- 1ₚ) * (β * ((- 1ₚ) * (α * hf)) + β * hf) ≡ (1ₚ + (- β)) * hf
  ringZ = Eq.trans (*-distribˡ-+ (- 1ₚ) (β * ((- 1ₚ) * (α * hf))) (β * hf))
          (Eq.trans (Eq.cong₂ _+_ T1 T2)
          (Eq.trans (Eq.cong (λ t → t + ((- β) * hf)) (Eq.sym (*-identityˡ hf)))
          (Eq.sym (*-distribʳ-+ hf 1ₚ (- β)))))

  arithZ : (p-1 Nat.* E) % p ≡ toℕ ((1ₚ + (- β)) * hf)
  arithZ = Eq.trans eNetZ (Eq.cong toℕ ringZ)

  -- ── netX reduction ──
  private
    NetZval = (- 1ₚ) * (β * ((- 1ₚ) * (α * hf)) + β * hf)

  αNegβ : α * (- β) ≡ - 1ₚ
  αNegβ = Eq.trans (Eq.cong (α *_) (Eq.sym (-1*x≈-x β)))
          (Eq.trans (Eq.sym (*-assoc α (- 1ₚ) β))
          (Eq.trans (Eq.cong (λ t → t * β) (*-comm α (- 1ₚ)))
          (Eq.trans (*-assoc (- 1ₚ) α β)
          (Eq.trans (Eq.cong ((- 1ₚ) *_) αβ≡1) (*-identityʳ (- 1ₚ))))))

  αNetZ : α * NetZval ≡ (α + (- 1ₚ)) * hf
  αNetZ = Eq.trans (Eq.cong (α *_) ringZ)
          (Eq.trans (Eq.sym (*-assoc α (1ₚ + (- β)) hf))
          (Eq.cong (λ t → t * hf)
            (Eq.trans (*-distribˡ-+ α 1ₚ (- β))
            (Eq.cong₂ _+_ (*-identityʳ α) αNegβ))))

  negAlphaHf : (- 1ₚ) * (α * hf) ≡ (- α) * hf
  negAlphaHf = Eq.trans (Eq.sym (*-assoc (- 1ₚ) α hf)) (Eq.cong (λ t → t * hf) (-1*x≈-x α))

  eF2 : (a Nat.* (p-1 Nat.* E)) % p ≡ toℕ (α * NetZval)
  eF2 = fold* α NetZval (p-1 Nat.* E) eNetZ
  eF : F % p ≡ toℕ ((- 1ₚ) * (α * hf) + α * NetZval)
  eF = fold+ ((- 1ₚ) * (α * hf)) (α * NetZval) (p-1 Nat.* (a Nat.* z)) (a Nat.* (p-1 Nat.* E)) ePAZ eF2
  eNetX : (F Nat.+ a Nat.* z) % p ≡ toℕ (((- 1ₚ) * (α * hf) + α * NetZval) + α * hf)
  eNetX = fold+ ((- 1ₚ) * (α * hf) + α * NetZval) (α * hf) F (a Nat.* z) eF eAZ

  Wfact : (((- α) + (α + (- 1ₚ))) + α) ≡ α + (- 1ₚ)
  Wfact = Eq.trans (Eq.cong (λ t → t + α)
            (Eq.trans (Eq.sym (+-assoc (- α) α (- 1ₚ)))
            (Eq.trans (Eq.cong (λ t → t + (- 1ₚ)) (+-inverseˡ α)) (+-identityˡ (- 1ₚ)))))
          (+-comm (- 1ₚ) α)

  ringX : ((- 1ₚ) * (α * hf) + α * NetZval) + α * hf ≡ (α + (- 1ₚ)) * hf
  ringX = Eq.trans (Eq.cong (λ t → t + α * hf) (Eq.cong₂ _+_ negAlphaHf αNetZ))
          (Eq.trans (Eq.cong (λ t → t + α * hf) (Eq.sym (*-distribʳ-+ hf (- α) (α + (- 1ₚ)))))
          (Eq.trans (Eq.sym (*-distribʳ-+ hf ((- α) + (α + (- 1ₚ))) α))
          (Eq.cong (λ s → s * hf) Wfact)))

  arithX : (F Nat.+ a Nat.* z) % p ≡ toℕ ((α + (- 1ₚ)) * hf)
  arithX = Eq.trans eNetX (Eq.cong toℕ ringX)

  -- ════ CLOSED FORM:  Mg = (S^a·H·S^b·H·S^a·H) · Z^(½(1-a⁻¹)) · X^(½(a-1)) ════
  M-decomp-clean : M x ≈ S ^ a • H • S ^ b • H • S ^ a • H • Z ^ toℕ ((1ₚ + (- β)) * hf) • X ^ toℕ ((α + (- 1ₚ)) * hf)
  M-decomp-clean = begin
    M x ≈⟨ M-decomp ⟩
    S ^ a • H • S ^ b • H • S ^ a • H • Z ^ (p-1 Nat.* E) • X ^ (F Nat.+ a Nat.* z)
      ≈⟨ cright (cright (cright (cright (cright (cright (cleft (trans (Zmod (p-1 Nat.* E)) (refl' (Eq.cong (Z ^_) arithZ)))))))))  ⟩
    S ^ a • H • S ^ b • H • S ^ a • H • Z ^ toℕ ((1ₚ + (- β)) * hf) • X ^ (F Nat.+ a Nat.* z)
      ≈⟨ cright (cright (cright (cright (cright (cright (cright (trans (Xmod (F Nat.+ a Nat.* z)) (refl' (Eq.cong (X ^_) arithX))))))))) ⟩
    S ^ a • H • S ^ b • H • S ^ a • H • Z ^ toℕ ((1ₚ + (- β)) * hf) • X ^ toℕ ((α + (- 1ₚ)) * hf) ∎

-- ════════════════════════════════════════════════════════════════════
-- NOTE: the CZ analogues (SemiCZ / SemiCZ↓) are intentionally omitted.
-- semi-M↑CZ / semi-M↓CZ are kept as the *original* Mg-form axioms in the
-- Simplified presentation, because their completeness proofs would need
-- Z↔CZ commutation — which is not a consequence of the selinger + Pauli
-- relations (it requires the metaplectic relations themselves), so the
-- derivation would be circular.  Only the single-qudit semi-M𝑠 (below)
-- is demoted to derived.
-- ════════════════════════════════════════════════════════════════════
-- ════════════════════════════════════════════════════════════════════
-- semi-M𝑠 with the Paulis pushed out & cancelled (single-qudit; no lift).
-- The X-Pauli of Mg cancels, leaving an irreducible Z^(½(g-1)).
-- ════════════════════════════════════════════════════════════════════
module SemiS (n : ℕ) where
  open PB ((₁₊ n) QRel,_===_)
  open PP ((₁₊ n) QRel,_===_)
  open SR word-setoid
  open Pattern-Assoc
  open Push n using (SpushK)
  open Group-Lemmas (Gen (₁₊ n)) ((₁₊ n) QRel,_===_) (grouplike {₁₊ n}) using (lemma-right-cancel)
  module D = Decomp n g*
  private
    a  = toℕ (g* .proj₁)
    b  = toℕ ((g* ⁻¹) .proj₁)
    zZ = toℕ ((1ₚ + (- ((g* ⁻¹) .proj₁))) * 1/2)
    zX = toℕ ((g* .proj₁ + (- 1ₚ)) * 1/2)
    z½ = toℕ 1/2
    E' = zZ Nat.+ (p-1 Nat.* zX)
  Wg : Word (Gen (₁₊ n))
  Wg = S ^ a • H • S ^ b • H • S ^ a • H
  P : Word (Gen (₁₊ n))
  P = Z ^ zZ • X ^ zX

  decompWP : M g* ≈ Wg • P
  decompWP = trans D.M-decomp-clean (special-assoc (□ ^ 8) (□ ^ 6 • □ ^ 2) auto)

  -- push the Pauli P past 𝑠 (= S·Z^½):  P·𝑠 ≈ 𝑠·Z^(zZ+(p-1)zX)·X^zX
  Pstep : P • 𝑠 ≈ 𝑠 • (Z ^ E' • X ^ zX)
  Pstep = begin
    (Z ^ zZ • X ^ zX) • (S • Z ^ z½)                          ≈⟨ assoc ⟩
    Z ^ zZ • (X ^ zX • (S • Z ^ z½))                          ≈⟨ cright (sym assoc) ⟩
    Z ^ zZ • ((X ^ zX • S) • Z ^ z½)                          ≈⟨ cright (cleft (SpushK zX)) ⟩
    Z ^ zZ • ((S • X ^ zX • Z ^ (p-1 Nat.* zX)) • Z ^ z½)     ≈⟨ cright assoc ⟩
    Z ^ zZ • (S • (X ^ zX • Z ^ (p-1 Nat.* zX)) • Z ^ z½)     ≈⟨ cright (cright assoc) ⟩
    Z ^ zZ • (S • (X ^ zX • (Z ^ (p-1 Nat.* zX) • Z ^ z½)))   ≈⟨ cright (cright (cright (sym (lemma-^-+ Z (p-1 Nat.* zX) z½)))) ⟩
    Z ^ zZ • (S • (X ^ zX • Z ^ (p-1 Nat.* zX Nat.+ z½)))     ≈⟨ cright (cright (word-comm zX (p-1 Nat.* zX Nat.+ z½) (axiom comm-X-Z))) ⟩
    Z ^ zZ • (S • (Z ^ (p-1 Nat.* zX Nat.+ z½) • X ^ zX))     ≈⟨ sym assoc ⟩
    (Z ^ zZ • S) • (Z ^ (p-1 Nat.* zX Nat.+ z½) • X ^ zX)     ≈⟨ cleft (word-comm zZ 1 (CL.lemma-comm-Z-S n)) ⟩
    (S • Z ^ zZ) • (Z ^ (p-1 Nat.* zX Nat.+ z½) • X ^ zX)     ≈⟨ assoc ⟩
    S • (Z ^ zZ • (Z ^ (p-1 Nat.* zX Nat.+ z½) • X ^ zX))     ≈⟨ cright (sym assoc) ⟩
    S • ((Z ^ zZ • Z ^ (p-1 Nat.* zX Nat.+ z½)) • X ^ zX)     ≈⟨ cright (cleft (sym (lemma-^-+ Z zZ (p-1 Nat.* zX Nat.+ z½)))) ⟩
    S • (Z ^ (zZ Nat.+ (p-1 Nat.* zX Nat.+ z½)) • X ^ zX)     ≈⟨ cright (cleft (refl' (Eq.cong (Z ^_) arith2))) ⟩
    S • (Z ^ (z½ Nat.+ E') • X ^ zX)                          ≈⟨ cright (cleft (lemma-^-+ Z z½ E')) ⟩
    S • ((Z ^ z½ • Z ^ E') • X ^ zX)                          ≈⟨ cright assoc ⟩
    S • (Z ^ z½ • (Z ^ E' • X ^ zX))                          ≈⟨ sym assoc ⟩
    (S • Z ^ z½) • (Z ^ E' • X ^ zX) ∎
    where
    arith2 : zZ Nat.+ (p-1 Nat.* zX Nat.+ z½) ≡ z½ Nat.+ E'
    arith2 = Eq.trans (Eq.sym (NP.+-assoc zZ (p-1 Nat.* zX) z½)) (NP.+-comm E' z½)

  -- Z^(p·zX) ≈ ε  and  Z^(zX+E') ≈ Z^zZ
  Zpzx : Z ^ (p Nat.* zX) ≈ ε
  Zpzx = trans (sym (lemma-^^ Z p zX)) (trans (lemma-^-cong (Z ^ p) ε zX (CL.lemma-order-Z n)) (lemma-ε^k=ε zX))
  Zred : Z ^ (zX Nat.+ E') ≈ Z ^ zZ
  Zred = trans (refl' (Eq.cong (Z ^_) arith3)) (trans (lemma-^-+ Z zZ (p Nat.* zX)) (trans (cright Zpzx) right-unit))
    where
    arith3 : zX Nat.+ E' ≡ zZ Nat.+ (p Nat.* zX)
    arith3 = Eq.trans (Eq.sym (NP.+-assoc zX zZ (p-1 Nat.* zX)))
             (Eq.trans (Eq.cong (Nat._+ (p-1 Nat.* zX)) (NP.+-comm zX zZ)) (NP.+-assoc zZ zX (p-1 Nat.* zX)))

  -- COMPLETENESS: recover the original Mg-form from the simplified axiom.
  -- decompWP + Pstep expose Wg·𝑠, the simplified axiom semi-M𝑠 fires, and the
  -- trailing Z^E'·X^zX collapses (rhs) back to the Pauli P of the Mg decomp.
  completeness-semi-M𝑠 : M g* • 𝑠 ≈ 𝑠^ (g * g) • M g*
  completeness-semi-M𝑠 = begin
    M g* • 𝑠                                          ≈⟨ cleft decompWP ⟩
    (Wg • P) • 𝑠                                      ≈⟨ assoc ⟩
    Wg • (P • 𝑠)                                      ≈⟨ cright Pstep ⟩
    Wg • (𝑠 • (Z ^ E' • X ^ zX))                     ≈⟨ sym assoc ⟩
    (Wg • 𝑠) • (Z ^ E' • X ^ zX)                     ≈⟨ cleft (axiom semi-M𝑠) ⟩
    (𝑠^ (g * g) • Wg • Z ^ zX) • (Z ^ E' • X ^ zX)   ≈⟨ rhs ⟩
    𝑠^ (g * g) • (Wg • P)                            ≈⟨ cright (sym decompWP) ⟩
    𝑠^ (g * g) • M g* ∎
    where
    rhs : (𝑠^ (g * g) • Wg • Z ^ zX) • (Z ^ E' • X ^ zX) ≈ 𝑠^ (g * g) • (Wg • P)
    rhs = begin
      (𝑠^ (g * g) • Wg • Z ^ zX) • (Z ^ E' • X ^ zX)        ≈⟨ assoc ⟩
      𝑠^ (g * g) • ((Wg • Z ^ zX) • (Z ^ E' • X ^ zX))      ≈⟨ cright assoc ⟩
      𝑠^ (g * g) • (Wg • (Z ^ zX • (Z ^ E' • X ^ zX)))      ≈⟨ cright (cright (sym assoc)) ⟩
      𝑠^ (g * g) • (Wg • ((Z ^ zX • Z ^ E') • X ^ zX))      ≈⟨ cright (cright (cleft (sym (lemma-^-+ Z zX E')))) ⟩
      𝑠^ (g * g) • (Wg • (Z ^ (zX Nat.+ E') • X ^ zX))      ≈⟨ cright (cright (cleft Zred)) ⟩
      𝑠^ (g * g) • (Wg • (Z ^ zZ • X ^ zX)) ∎
