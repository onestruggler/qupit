{-# OPTIONS --termination-depth=20 #-}
{-# OPTIONS --inversion-max-depth=1000 #-}

open import Level using (0ℓ)
open import Relation.Binary.PropositionalEquality using (_≡_ ; _≢_ ; module ≡-Reasoning) renaming ([_] to [_]')
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
open import Presentation.GroupLike
open import Presentation.Tactics
import Data.Nat.Properties as NP
open import Data.Nat.DivMod
open import Data.Fin.Properties using (toℕ-inject₁ ; toℕ-fromℕ ; toℕ-fromℕ<)
open import Data.Nat.Primality
open import Zp.ModularArithmetic
open import Zp.Fermats-little-theorem
open import Notations

module N.Clifford.Simplified-Lemmas.Part3
  (p-3 : ℕ)
  (let p-2 = ₁₊ p-3)
  (p-prime : Prime (suc (₁₊ p-2)))
  (let open PrimeModulus' p-2 p-prime)
  (g*@(g , g≠0) : ℤ* ₚ)
  (g-gen : ∀ ((x , _) : ℤ* ₚ) -> ∃ \ (k : ℤ ₚ-₁) -> x ≡ g ^′ toℕ k )
  where


open Primitive-Root-Modp' g* g-gen

open import N.Clifford.Clifford-Mod-Scalar p-3 p-prime g* g-gen
open Clifford-Relations hiding
  ( _QRel,_===_ ; order-S ; order-H ; M-power ; semi-M𝑠 ; order-SH ; comm-HHSHHS
  ; comm-X-Z ; semi-M↑CZ ; semi-M↓CZ ; rel-X↑-CZ ; rel-X↓-CZ ; order-CZ
  ; comm-CZ-S↓ ; comm-CZ-S↑ ; selinger-c10 ; selinger-c11 ; selinger-c12
  ; selinger-c13 ; selinger-c14 ; selinger-c15 ; comm-H ; comm-S ; comm-CZ ; cong↑ )
open import N.Clifford.Clifford-Mod-Scalars-Simplified p-3 p-prime g* g-gen
open Simplified-Relations
open import N.Clifford.Simplified-Lemmas.Part2 p-3 p-prime g* g-gen public




-- ====================================================================
-- Clifford-Lemmas-S : copy of N.Clifford.Clifford-Lemmas (𝑠-conjugation,
-- Z↑-CZ, comm-𝑠-w↑, …) for the Simplified relation.
-- ====================================================================
open Lemmas-Clifford-S
open Simplified-GroupLike-S
module CL = Lemmas1-S
module CLb = Lemmas1b-S

lemma-comm-𝑠-w↑ : ∀ {n} w -> let open PB ((₂₊ n) QRel,_===_) in
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
  open PB ((₂₊ n) QRel,_===_)
  open PP ((₂₊ n) QRel,_===_)
  open SR word-setoid

lemma-conj-𝑠-X : ∀ {n} -> let open PB ((₁₊ n) QRel,_===_) in
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
  open PB ((₁₊ n) QRel,_===_)
  open PP ((₁₊ n) QRel,_===_)
  open SR word-setoid

lemma-S^p-1•S : ∀ {n} -> let open PB ((₁₊ n) QRel,_===_) in
  S ^ p-1 • S ≈ ε
lemma-S^p-1•S {n} = begin
  S ^ p-1 • S ≡⟨ auto ⟩
  S ^ p-1 • S ^ 1 ≈⟨ sym (lemma-^-+ S p-1 1) ⟩
  S ^ (p-1 Nat.+ 1) ≡⟨ Eq.cong (S ^_) (NP.+-comm p-1 1) ⟩
  S ^ (1 Nat.+ p-1) ≡⟨ auto ⟩
  S ^ p ≈⟨ axiom _QRel,_===_.order-S ⟩
  ε ∎
  where
  open PB ((₁₊ n) QRel,_===_)
  open PP ((₁₊ n) QRel,_===_)
  open SR word-setoid

lemma-S•S^p-1 : ∀ {n} -> let open PB ((₁₊ n) QRel,_===_) in
  S • S ^ p-1 ≈ ε
lemma-S•S^p-1 {n} = begin
  S • S ^ p-1 ≡⟨ auto ⟩
  S ^ 1 • S ^ p-1 ≈⟨ sym (lemma-^-+ S 1 p-1) ⟩
  S ^ (1 Nat.+ p-1) ≡⟨ auto ⟩
  S ^ p ≈⟨ axiom _QRel,_===_.order-S ⟩
  ε ∎
  where
  open PB ((₁₊ n) QRel,_===_)
  open PP ((₁₊ n) QRel,_===_)
  open SR word-setoid

lemma-comm-S-Z : ∀ {n} -> let open PB ((₁₊ n) QRel,_===_) in
  Z • S ≈ S • Z
lemma-comm-S-Z {n} = trans lhs (sym rhs)
  where
  open PB ((₁₊ n) QRel,_===_)
  open PP ((₁₊ n) QRel,_===_)
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

lemma-comm-𝑠-Z : ∀ {n} -> let open PB ((₁₊ n) QRel,_===_) in
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
  open PB ((₁₊ n) QRel,_===_)
  open PP ((₁₊ n) QRel,_===_)
  open SR word-setoid

lemma-CZ^k-% : ∀ {n} k -> let open PB ((₂₊ n) QRel,_===_) in
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
  open PB ((₂₊ n) QRel,_===_)
  open PP ((₂₊ n) QRel,_===_)
  open SR word-setoid
  open import Data.Nat.DivMod using (m≡m%n+[m/n]*n)

{- DEAD CLUSTER (parked): the Mg / M₋₁ / H²·CZ·H² CZ-conjugation family
   (lemma-Mg-CZ^k … lemma-comm-S'-CZ↑).  Routed through `axiom semi-M↓CZ`/
   `semi-M↑CZ`, now in simplified Wg-form, so it no longer type-checks here;
   its only live consumers (lemma-comm-Z-CZ / lemma-comm-Z↑-CZ) are now the
   comm-Z-CZ / comm-Z↑-CZ axioms.  Kept verbatim for reference.
lemma-Mg-CZ^k : ∀ {n} k -> let open PB ((₂₊ n) QRel,_===_) in
  M g* • CZ ^ k ≈ CZ ^ (k Nat.* toℕ g) • M g*
lemma-Mg-CZ^k {n} k@0 = trans right-unit (sym left-unit)
  where
  open PB ((₂₊ n) QRel,_===_)
lemma-Mg-CZ^k {n} k@1 = begin
  M g* • CZ ^ k ≈⟨ refl ⟩
  M g* • CZ ≈⟨ _≈_.axiom _QRel,_===_.semi-M↓CZ ⟩
  CZ^ g • M g* ≈⟨ refl ⟩
  CZ ^ toℕ g • M g* ≈⟨ cleft refl' (Eq.cong (CZ ^_) (Eq.sym (NP.*-identityˡ (toℕ g)))) ⟩
  CZ ^ (k Nat.* toℕ g) • M g* ∎
  where
  open PB ((₂₊ n) QRel,_===_)
  open PP ((₂₊ n) QRel,_===_)
  open SR word-setoid
lemma-Mg-CZ^k {n} k@(₂₊ k') = begin
  M g* • CZ ^ k ≈⟨ refl ⟩
  M g* • CZ • CZ ^ (₁₊ k') ≈⟨ sym assoc ⟩
  (M g* • CZ) • CZ ^ (₁₊ k') ≈⟨ cleft lemma-Mg-CZ^k 1 ⟩
  (CZ ^ (1 Nat.* toℕ g) • M g*) • CZ ^ (₁₊ k') ≈⟨ assoc ⟩
  CZ ^ (1 Nat.* toℕ g) • M g* • CZ ^ (₁₊ k') ≈⟨ cright lemma-Mg-CZ^k (₁₊ k') ⟩
  CZ ^ (1 Nat.* toℕ g) • CZ ^ (₁₊ k' Nat.* toℕ g) • M g* ≈⟨ sym assoc ⟩
  (CZ ^ (1 Nat.* toℕ g) • CZ ^ (₁₊ k' Nat.* toℕ g)) • M g* ≈⟨ cleft sym (lemma-^-+ CZ (1 Nat.* toℕ g) (₁₊ k' Nat.* toℕ g)) ⟩
  (CZ ^ ((1 Nat.* toℕ g) Nat.+ (₁₊ k' Nat.* toℕ g))) • M g* ≈⟨ cleft refl' (Eq.cong (CZ ^_) (Eq.sym (NP.*-distribʳ-+ (toℕ g) 1 (₁₊ k')))) ⟩
  CZ ^ ((1 Nat.+ ₁₊ k') Nat.* toℕ g) • M g* ≈⟨ refl ⟩
  CZ ^ (k Nat.* toℕ g) • M g* ∎
  where
  open PB ((₂₊ n) QRel,_===_)
  open PP ((₂₊ n) QRel,_===_)
  open SR word-setoid

lemma-Mg^k-CZ : ∀ {n} k -> let open PB ((₂₊ n) QRel,_===_) in
  M g* ^ k • CZ ≈ CZ^ (g ^′ k) • M g* ^ k
lemma-Mg^k-CZ {n} k@0 = begin
  M g* ^ k • CZ ≈⟨ left-unit ⟩
  CZ ≈⟨ sym right-unit ⟩
  CZ • ε ∎
  where
  open PB ((₂₊ n) QRel,_===_)
  open PP ((₂₊ n) QRel,_===_)
  open SR word-setoid
lemma-Mg^k-CZ {n} k@1 = begin
  M g* ^ k • CZ ≈⟨ refl ⟩
  M g* • CZ ≈⟨ _≈_.axiom _QRel,_===_.semi-M↓CZ ⟩
  CZ^ g • M g* ≈⟨ cleft refl' (Eq.cong CZ^ (Eq.sym (lemma-x^′1=x g))) ⟩
  CZ^ (g ^′ k) • M g* ^ k ∎
  where
  open PB ((₂₊ n) QRel,_===_)
  open PP ((₂₊ n) QRel,_===_)
  open SR word-setoid
lemma-Mg^k-CZ {n} k@(₂₊ k') = begin
  M g* ^ k • CZ ≈⟨ refl ⟩
  (M g* • M g* ^ (₁₊ k')) • CZ ≈⟨ assoc ⟩
  M g* • (M g* ^ (₁₊ k') • CZ) ≈⟨ cright lemma-Mg^k-CZ (₁₊ k') ⟩
  M g* • (CZ^ (g ^′ (₁₊ k')) • M g* ^ (₁₊ k')) ≈⟨ sym assoc ⟩
  (M g* • CZ^ (g ^′ (₁₊ k'))) • M g* ^ (₁₊ k') ≈⟨ cleft lemma-Mg-CZ^k (toℕ (g ^′ (₁₊ k'))) ⟩
  (CZ ^ (toℕ (g ^′ (₁₊ k')) Nat.* toℕ g) • M g*) • M g* ^ (₁₊ k') ≈⟨ assoc ⟩
  CZ ^ (toℕ (g ^′ (₁₊ k')) Nat.* toℕ g) • (M g* • M g* ^ (₁₊ k')) ≈⟨ cleft lemma-CZ^k-% (toℕ (g ^′ (₁₊ k')) Nat.* toℕ g) ⟩
  CZ ^ ((toℕ (g ^′ (₁₊ k')) Nat.* toℕ g) % p) • (M g* • M g* ^ (₁₊ k')) ≡⟨ Eq.cong (\ x -> CZ ^ x • (M g* • M g* ^ (₁₊ k'))) (lemma-toℕ-% (g ^′ (₁₊ k')) g) ⟩
  CZ ^ toℕ (g ^′ (₁₊ k') * g) • (M g* • M g* ^ (₁₊ k')) ≡⟨ Eq.cong (\ x -> CZ ^ toℕ x • (M g* • M g* ^ (₁₊ k'))) (*-comm (g ^′ (₁₊ k')) g) ⟩
  CZ ^ toℕ (g * g ^′ (₁₊ k')) • (M g* • M g* ^ (₁₊ k')) ≡⟨ auto ⟩
  CZ^ (g ^′ k) • M g* ^ k ∎
  where
  open PB ((₂₊ n) QRel,_===_)
  open PP ((₂₊ n) QRel,_===_)
  open SR word-setoid

lemma-M₋₁-CZ : ∀ {n} -> let open PB ((₂₊ n) QRel,_===_) in
  M₋₁ • CZ ≈ CZ^ ((-'₁) .proj₁) • M₋₁
lemma-M₋₁-CZ {n} = begin
  M₋₁ • CZ ≈⟨ refl' (Eq.cong (_• CZ) (CL.aux-M≡M (₁₊ n) -'₁ (g^ k₀) eqk)) ⟩
  M (g^ k₀) • CZ ≈⟨ cleft sym (_≈_.axiom (_QRel,_===_.M-power k₀)) ⟩
  M g* ^ (toℕ k₀) • CZ ≈⟨ lemma-Mg^k-CZ (toℕ k₀) ⟩
  CZ^ (g ^′ toℕ k₀) • M g* ^ (toℕ k₀) ≈⟨ cright _≈_.axiom (_QRel,_===_.M-power k₀) ⟩
  CZ^ (g ^′ toℕ k₀) • M (g^ k₀) ≈⟨ refl' (Eq.cong (CZ^ (g ^′ toℕ k₀) •_) (Eq.sym (CL.aux-M≡M (₁₊ n) -'₁ (g^ k₀) eqk))) ⟩
  CZ^ (g ^′ toℕ k₀) • M₋₁ ≈⟨ cleft refl' (Eq.cong CZ^ (Eq.sym eqk)) ⟩
  CZ^ ((-'₁) .proj₁) • M₋₁ ∎
  where
  open PB ((₂₊ n) QRel,_===_)
  open PP ((₂₊ n) QRel,_===_)
  open SR word-setoid
--  open Primitive-Root-Modp' g* g-gen
  k₀ = inject₁ (log (-'₁))
  eqk : (-'₁) .proj₁ ≡ g ^′ toℕ k₀
  eqk = Eq.sym (lemma-log-inject (-'₁))

lemma-M₋₁CZM₋₁ : ∀ {n} -> let open PB ((₂₊ n) QRel,_===_) in
  M₋₁ • CZ • M₋₁ ≈ CZ^ ((-'₁) .proj₁)
lemma-M₋₁CZM₋₁ {n} = begin
  M₋₁ • CZ • M₋₁ ≈⟨ sym assoc ⟩
  (M₋₁ • CZ) • M₋₁ ≈⟨ cong lemma-M₋₁-CZ refl ⟩
  (CZ^ ((-'₁) .proj₁) • M₋₁) • M₋₁ ≈⟨ assoc ⟩
  CZ^ ((-'₁) .proj₁) • (M₋₁ • M₋₁) ≈⟨ cong refl (CL.lemma-M₋₁^2 (₁₊ n)) ⟩
  CZ^ ((-'₁) .proj₁) • ε ≈⟨ right-unit ⟩
  CZ^ ((-'₁) .proj₁) ∎
  where
  open PB ((₂₊ n) QRel,_===_)
  open PP ((₂₊ n) QRel,_===_)
  open SR word-setoid

lemma-M₋₁CZ⁻¹M₋₁ : ∀ {n} -> let open PB ((₂₊ n) QRel,_===_) in
  M₋₁ • CZ^ ((-'₁) .proj₁) • M₋₁ ≈ CZ
lemma-M₋₁CZ⁻¹M₋₁ {n} = begin
  M₋₁ • CZ^ ((-'₁) .proj₁) • M₋₁ ≈⟨ cong refl (sym lemma-M₋₁-CZ) ⟩
  M₋₁ • (M₋₁ • CZ) ≈⟨ sym assoc ⟩
  (M₋₁ • M₋₁) • CZ ≈⟨ cong (CL.lemma-M₋₁^2 (₁₊ n)) refl ⟩
  ε • CZ ≈⟨ left-unit ⟩
  CZ ∎
  where
  open PB ((₂₊ n) QRel,_===_)
  open PP ((₂₊ n) QRel,_===_)
  open SR word-setoid

lemma-HHCZHH : ∀ {n} -> let open PB ((₂₊ n) QRel,_===_) in
  H • H • CZ • H • H ≈ CZ^ ((-'₁) .proj₁)
lemma-HHCZHH {n} = begin
  H • H • CZ • H • H ≈⟨ special-assoc (□ • □ • □ • □ • □) ((□ • □) • □ • (□ • □)) auto ⟩
  (H • H) • CZ • (H • H) ≈⟨ cong (_≈_.axiom _QRel,_===_.order-H) (cong refl (_≈_.axiom _QRel,_===_.order-H)) ⟩
  M₋₁ • CZ • M₋₁ ≈⟨ lemma-M₋₁CZM₋₁ ⟩
  CZ^ ((-'₁) .proj₁) ∎
  where
  open PB ((₂₊ n) QRel,_===_)
  open PP ((₂₊ n) QRel,_===_)
  open SR word-setoid
  open Pattern-Assoc

lemma-HHCZ⁻¹HH : ∀ {n} -> let open PB ((₂₊ n) QRel,_===_) in
  H • H • CZ^ ((-'₁) .proj₁) • H • H ≈ CZ
lemma-HHCZ⁻¹HH {n} = begin
  H • H • CZ^ ((-'₁) .proj₁) • H • H ≈⟨ special-assoc (□ • □ • □ • □ • □) ((□ • □) • □ • (□ • □)) auto ⟩
  (H • H) • CZ^ ((-'₁) .proj₁) • (H • H) ≈⟨ cong (_≈_.axiom _QRel,_===_.order-H) (cong refl (_≈_.axiom _QRel,_===_.order-H)) ⟩
  M₋₁ • CZ^ ((-'₁) .proj₁) • M₋₁ ≈⟨ lemma-M₋₁CZ⁻¹M₋₁ ⟩
  CZ ∎
  where
  open PB ((₂₊ n) QRel,_===_)
  open PP ((₂₊ n) QRel,_===_)
  open SR word-setoid
  open Pattern-Assoc

lemma-S'CZS'⁻¹ : ∀ {n} -> let open PB ((₂₊ n) QRel,_===_) in
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
  open PB ((₂₊ n) QRel,_===_)
  open PP ((₂₊ n) QRel,_===_)
  open SR word-setoid
  open Pattern-Assoc

lemma-S'⁻¹S' : ∀ {n} -> let open PB ((₂₊ n) QRel,_===_) in
  H • H • S ^ p-1 • H • H • H • H • S • H • H ≈ ε
lemma-S'⁻¹S' {n} = begin
  H • H • S ^ p-1 • H • H • H • H • S • H • H
    ≈⟨ special-assoc (□ • □ • □ • □ • □ • □ • □ • □ • □ • □) (□ • □ • □ • (□ • □ • □ • □) • □ • □ • □) auto ⟩
  H • H • S ^ p-1 • (H • H • H • H) • S • H • H
    ≈⟨ cong refl (cong refl (cong refl (cong (CL.lemma-order-H (₁₊ n)) refl))) ⟩
  H • H • S ^ p-1 • ε • S • H • H
    ≈⟨ cong refl (cong refl (cong refl left-unit)) ⟩
  H • H • S ^ p-1 • S • H • H
    ≈⟨ cong refl (cong refl (trans (sym assoc) (cong lemma-S^p-1•S refl))) ⟩
  H • H • ε • H • H
    ≈⟨ cong refl (cong refl left-unit) ⟩
  H • H • H • H
    ≈⟨ CL.lemma-order-H (₁₊ n) ⟩
  ε ∎
  where
  open PB ((₂₊ n) QRel,_===_)
  open PP ((₂₊ n) QRel,_===_)
  open SR word-setoid
  open Pattern-Assoc

lemma-comm-S'-CZ : ∀ {n} -> let open PB ((₂₊ n) QRel,_===_) in
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
  open PB ((₂₊ n) QRel,_===_)
  open PP ((₂₊ n) QRel,_===_)
  open SR word-setoid
  open Pattern-Assoc

lemma-Mg↑-CZ^k : ∀ {n} k -> let open PB ((₂₊ n) QRel,_===_) in
  M g* ↑ • CZ ^ k ≈ CZ ^ (k Nat.* toℕ g) • M g* ↑
lemma-Mg↑-CZ^k {n} k@0 = trans right-unit (sym left-unit)
  where
  open PB ((₂₊ n) QRel,_===_)
lemma-Mg↑-CZ^k {n} k@1 = begin
  M g* ↑ • CZ ^ k ≈⟨ refl ⟩
  M g* ↑ • CZ ≈⟨ _≈_.axiom _QRel,_===_.semi-M↑CZ ⟩
  CZ^ g • M g* ↑ ≈⟨ refl ⟩
  CZ ^ toℕ g • M g* ↑ ≈⟨ cleft refl' (Eq.cong (CZ ^_) (Eq.sym (NP.*-identityˡ (toℕ g)))) ⟩
  CZ ^ (k Nat.* toℕ g) • M g* ↑ ∎
  where
  open PB ((₂₊ n) QRel,_===_)
  open PP ((₂₊ n) QRel,_===_)
  open SR word-setoid
lemma-Mg↑-CZ^k {n} k@(₂₊ k') = begin
  M g* ↑ • CZ ^ k ≈⟨ refl ⟩
  M g* ↑ • CZ • CZ ^ (₁₊ k') ≈⟨ sym assoc ⟩
  (M g* ↑ • CZ) • CZ ^ (₁₊ k') ≈⟨ cleft lemma-Mg↑-CZ^k 1 ⟩
  (CZ ^ (1 Nat.* toℕ g) • M g* ↑) • CZ ^ (₁₊ k') ≈⟨ assoc ⟩
  CZ ^ (1 Nat.* toℕ g) • M g* ↑ • CZ ^ (₁₊ k') ≈⟨ cright lemma-Mg↑-CZ^k (₁₊ k') ⟩
  CZ ^ (1 Nat.* toℕ g) • CZ ^ (₁₊ k' Nat.* toℕ g) • M g* ↑ ≈⟨ sym assoc ⟩
  (CZ ^ (1 Nat.* toℕ g) • CZ ^ (₁₊ k' Nat.* toℕ g)) • M g* ↑ ≈⟨ cleft sym (lemma-^-+ CZ (1 Nat.* toℕ g) (₁₊ k' Nat.* toℕ g)) ⟩
  (CZ ^ ((1 Nat.* toℕ g) Nat.+ (₁₊ k' Nat.* toℕ g))) • M g* ↑ ≈⟨ cleft refl' (Eq.cong (CZ ^_) (Eq.sym (NP.*-distribʳ-+ (toℕ g) 1 (₁₊ k')))) ⟩
  CZ ^ ((1 Nat.+ ₁₊ k') Nat.* toℕ g) • M g* ↑ ≈⟨ refl ⟩
  CZ ^ (k Nat.* toℕ g) • M g* ↑ ∎
  where
  open PB ((₂₊ n) QRel,_===_)
  open PP ((₂₊ n) QRel,_===_)
  open SR word-setoid

lemma-Mg↑^k-CZ : ∀ {n} k -> let open PB ((₂₊ n) QRel,_===_) in
  (M g* ↑) ^ k • CZ ≈ CZ^ (g ^′ k) • (M g* ↑) ^ k
lemma-Mg↑^k-CZ {n} k@0 = begin
  (M g* ↑) ^ k • CZ ≈⟨ left-unit ⟩
  CZ ≈⟨ sym right-unit ⟩
  CZ • ε ∎
  where
  open PB ((₂₊ n) QRel,_===_)
  open PP ((₂₊ n) QRel,_===_)
  open SR word-setoid
lemma-Mg↑^k-CZ {n} k@1 = begin
  (M g* ↑) ^ k • CZ ≈⟨ refl ⟩
  M g* ↑ • CZ ≈⟨ _≈_.axiom _QRel,_===_.semi-M↑CZ ⟩
  CZ^ g • M g* ↑ ≈⟨ cleft refl' (Eq.cong CZ^ (Eq.sym (lemma-x^′1=x g))) ⟩
  CZ^ (g ^′ k) • (M g* ↑) ^ k ∎
  where
  open PB ((₂₊ n) QRel,_===_)
  open PP ((₂₊ n) QRel,_===_)
  open SR word-setoid
lemma-Mg↑^k-CZ {n} k@(₂₊ k') = begin
  (M g* ↑) ^ k • CZ ≈⟨ refl ⟩
  (M g* ↑ • (M g* ↑) ^ (₁₊ k')) • CZ ≈⟨ assoc ⟩
  M g* ↑ • ((M g* ↑) ^ (₁₊ k') • CZ) ≈⟨ cright lemma-Mg↑^k-CZ (₁₊ k') ⟩
  M g* ↑ • (CZ^ (g ^′ (₁₊ k')) • (M g* ↑) ^ (₁₊ k')) ≈⟨ sym assoc ⟩
  (M g* ↑ • CZ^ (g ^′ (₁₊ k'))) • (M g* ↑) ^ (₁₊ k') ≈⟨ cleft lemma-Mg↑-CZ^k (toℕ (g ^′ (₁₊ k'))) ⟩
  (CZ ^ (toℕ (g ^′ (₁₊ k')) Nat.* toℕ g) • M g* ↑) • (M g* ↑) ^ (₁₊ k') ≈⟨ assoc ⟩
  CZ ^ (toℕ (g ^′ (₁₊ k')) Nat.* toℕ g) • (M g* ↑ • (M g* ↑) ^ (₁₊ k')) ≈⟨ cleft lemma-CZ^k-% (toℕ (g ^′ (₁₊ k')) Nat.* toℕ g) ⟩
  CZ ^ ((toℕ (g ^′ (₁₊ k')) Nat.* toℕ g) % p) • (M g* ↑ • (M g* ↑) ^ (₁₊ k')) ≡⟨ Eq.cong (\ x -> CZ ^ x • (M g* ↑ • (M g* ↑) ^ (₁₊ k'))) (lemma-toℕ-% (g ^′ (₁₊ k')) g) ⟩
  CZ ^ toℕ (g ^′ (₁₊ k') * g) • (M g* ↑ • (M g* ↑) ^ (₁₊ k')) ≡⟨ Eq.cong (\ x -> CZ ^ toℕ x • (M g* ↑ • (M g* ↑) ^ (₁₊ k'))) (*-comm (g ^′ (₁₊ k')) g) ⟩
  CZ ^ toℕ (g * g ^′ (₁₊ k')) • (M g* ↑ • (M g* ↑) ^ (₁₊ k')) ≡⟨ auto ⟩
  CZ^ (g ^′ k) • (M g* ↑) ^ k ∎
  where
  open PB ((₂₊ n) QRel,_===_)
  open PP ((₂₊ n) QRel,_===_)
  open SR word-setoid

lemma-M₋₁↑-CZ : ∀ {n} -> let open PB ((₂₊ n) QRel,_===_) in
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
  open PB ((₂₊ n) QRel,_===_)
  open PP ((₂₊ n) QRel,_===_)
  open SR word-setoid
--  open Primitive-Root-Modp' g* g-gen
  k₀ = inject₁ (log (-'₁))
  eqk : (-'₁) .proj₁ ≡ g ^′ toℕ k₀
  eqk = Eq.sym (lemma-log-inject (-'₁))
  bridge : (M g* ^ toℕ k₀) ↑ ≈ M (g^ k₀) ↑
  bridge = lemma-cong↑ (M g* ^ toℕ k₀) (M (g^ k₀)) (PB.axiom (_QRel,_===_.M-power {n = n} k₀))

lemma-M₋₁↑CZM₋₁↑ : ∀ {n} -> let open PB ((₂₊ n) QRel,_===_) in
  M₋₁ ↑ • CZ • M₋₁ ↑ ≈ CZ^ ((-'₁) .proj₁)
lemma-M₋₁↑CZM₋₁↑ {n} = begin
  M₋₁ ↑ • CZ • M₋₁ ↑ ≈⟨ sym assoc ⟩
  (M₋₁ ↑ • CZ) • M₋₁ ↑ ≈⟨ cong lemma-M₋₁↑-CZ refl ⟩
  (CZ^ ((-'₁) .proj₁) • M₋₁ ↑) • M₋₁ ↑ ≈⟨ assoc ⟩
  CZ^ ((-'₁) .proj₁) • (M₋₁ ↑ • M₋₁ ↑) ≈⟨ cong refl (lemma-cong↑ (M₋₁ • M₋₁) ε (CL.lemma-M₋₁^2 n)) ⟩
  CZ^ ((-'₁) .proj₁) • ε ≈⟨ right-unit ⟩
  CZ^ ((-'₁) .proj₁) ∎
  where
  open PB ((₂₊ n) QRel,_===_)
  open PP ((₂₊ n) QRel,_===_)
  open SR word-setoid

lemma-M₋₁↑CZ⁻¹M₋₁↑ : ∀ {n} -> let open PB ((₂₊ n) QRel,_===_) in
  M₋₁ ↑ • CZ^ ((-'₁) .proj₁) • M₋₁ ↑ ≈ CZ
lemma-M₋₁↑CZ⁻¹M₋₁↑ {n} = begin
  M₋₁ ↑ • CZ^ ((-'₁) .proj₁) • M₋₁ ↑ ≈⟨ cong refl (sym lemma-M₋₁↑-CZ) ⟩
  M₋₁ ↑ • (M₋₁ ↑ • CZ) ≈⟨ sym assoc ⟩
  (M₋₁ ↑ • M₋₁ ↑) • CZ ≈⟨ cong (lemma-cong↑ (M₋₁ • M₋₁) ε (CL.lemma-M₋₁^2 n)) refl ⟩
  ε • CZ ≈⟨ left-unit ⟩
  CZ ∎
  where
  open PB ((₂₊ n) QRel,_===_)
  open PP ((₂₊ n) QRel,_===_)
  open SR word-setoid


lemma-HHCZHH↑ : ∀ {n} -> let open PB ((₂₊ n) QRel,_===_) in
  H ↑ • H ↑ • CZ • H ↑ • H ↑ ≈ CZ^ ((-'₁) .proj₁)
lemma-HHCZHH↑ {n} = begin
  H ↑ • H ↑ • CZ • H ↑ • H ↑ ≈⟨ special-assoc (□ • □ • □ • □ • □) ((□ • □) • □ • (□ • □)) auto ⟩
  (H ↑ • H ↑) • CZ • (H ↑ • H ↑) ≈⟨ cong bridge (cong refl bridge) ⟩
  M₋₁ ↑ • CZ • M₋₁ ↑ ≈⟨ lemma-M₋₁↑CZM₋₁↑ ⟩
  CZ^ ((-'₁) .proj₁) ∎
  where
  open PB ((₂₊ n) QRel,_===_)
  open PP ((₂₊ n) QRel,_===_)
  open SR word-setoid
  open Pattern-Assoc
  bridge : H ↑ • H ↑ ≈ M₋₁ ↑
  bridge = lemma-cong↑ (H • H) M₋₁ (PB.axiom (_QRel,_===_.order-H {n = n}))

lemma-HHCZ⁻¹HH↑ : ∀ {n} -> let open PB ((₂₊ n) QRel,_===_) in
  H ↑ • H ↑ • CZ^ ((-'₁) .proj₁) • H ↑ • H ↑ ≈ CZ
lemma-HHCZ⁻¹HH↑ {n} = begin
  H ↑ • H ↑ • CZ^ ((-'₁) .proj₁) • H ↑ • H ↑ ≈⟨ special-assoc (□ • □ • □ • □ • □) ((□ • □) • □ • (□ • □)) auto ⟩
  (H ↑ • H ↑) • CZ^ ((-'₁) .proj₁) • (H ↑ • H ↑) ≈⟨ cong bridge (cong refl bridge) ⟩
  M₋₁ ↑ • CZ^ ((-'₁) .proj₁) • M₋₁ ↑ ≈⟨ lemma-M₋₁↑CZ⁻¹M₋₁↑ ⟩
  CZ ∎
  where
  open PB ((₂₊ n) QRel,_===_)
  open PP ((₂₊ n) QRel,_===_)
  open SR word-setoid
  open Pattern-Assoc
  bridge : H ↑ • H ↑ ≈ M₋₁ ↑
  bridge = lemma-cong↑ (H • H) M₋₁ (PB.axiom (_QRel,_===_.order-H {n = n}))

lemma-S^p-1•S↑ : ∀ {n} -> let open PB ((₂₊ n) QRel,_===_) in
  (S ↑) ^ p-1 • S ↑ ≈ ε
lemma-S^p-1•S↑ {n} = begin
  (S ↑) ^ p-1 • S ↑ ≈⟨ cleft refl' (Eq.sym (lemma-↑^ p-1 S)) ⟩
  (S ^ p-1) ↑ • S ↑ ≈⟨ bridge ⟩
  ε ∎
  where
  open PB ((₂₊ n) QRel,_===_)
  open PP ((₂₊ n) QRel,_===_)
  open SR word-setoid
  bridge : (S ^ p-1) ↑ • S ↑ ≈ ε
  bridge = lemma-cong↑ (S ^ p-1 • S) ε (lemma-S^p-1•S {n = n})
lemma-S•S^p-1↑ : ∀ {n} -> let open PB ((₂₊ n) QRel,_===_) in
  S ↑ • (S ↑) ^ p-1 ≈ ε
lemma-S•S^p-1↑ {n} = begin
  S ↑ • (S ↑) ^ p-1 ≈⟨ cright refl' (Eq.sym (lemma-↑^ p-1 S)) ⟩
  S ↑ • (S ^ p-1) ↑ ≈⟨ lemma-cong↑ (S • S ^ p-1) ε (lemma-S•S^p-1 {n = n}) ⟩
  ε ∎
  where
  open PB ((₂₊ n) QRel,_===_)
  open PP ((₂₊ n) QRel,_===_)
  open SR word-setoid

lemma-S'CZS'⁻¹↑ : ∀ {n} -> let open PB ((₂₊ n) QRel,_===_) in
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
  open PB ((₂₊ n) QRel,_===_)
  open PP ((₂₊ n) QRel,_===_)
  open SR word-setoid
  open Pattern-Assoc

lemma-S'⁻¹S'↑ : ∀ {n} -> let open PB ((₂₊ n) QRel,_===_) in
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
  open PB ((₂₊ n) QRel,_===_)
  open PP ((₂₊ n) QRel,_===_)
  open SR word-setoid
  open Pattern-Assoc
  order-H↑ : H ↑ • H ↑ • H ↑ • H ↑ ≈ ε
  order-H↑ = begin
    H ↑ • H ↑ • H ↑ • H ↑ ≡⟨ Eq.cong _↑ auto ⟩
    (H • H • H • H) ↑ ≈⟨ lemma-cong↑ (H ^ 4) ε (CL.lemma-order-H n) ⟩
    ε ∎

lemma-comm-S'-CZ↑ : ∀ {n} -> let open PB ((₂₊ n) QRel,_===_) in
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
  open PB ((₂₊ n) QRel,_===_)
  open PP ((₂₊ n) QRel,_===_)
  open SR word-setoid
  open Pattern-Assoc
-}  -- end DEAD CZ-conjugation cluster

lemma-Z↑ : ∀ {n} -> Z {n} ↑ ≡ H ↑ • H ↑ • S ↑ • H ↑ • H ↑ • (S ↑) ^ p-1
lemma-Z↑ {n} = begin
  Z ↑ ≡⟨ auto ⟩
  (H • H • S • H • H • S ^ p-1) ↑ ≡⟨ auto ⟩
  H ↑ • H ↑ • S ↑ • H ↑ • H ↑ • (S ^ p-1) ↑ ≡⟨ Eq.cong (\ x -> H ↑ • H ↑ • S ↑ • H ↑ • H ↑ • x) (lemma-↑^ p-1 S) ⟩
  H ↑ • H ↑ • S ↑ • H ↑ • H ↑ • (S ↑) ^ p-1 ∎
  where open ≡-Reasoning

lemma-comm-Z↑-CZ : ∀ {n} -> let open PB ((₂₊ n) QRel,_===_) in
  Z ↑ • CZ ≈ CZ • Z ↑
-- Z↑ commutes with CZ: taken as the axiom comm-Z↑-CZ in the Simplified
-- presentation (the metaplectic-route proof would loop through the demoted
-- semi-M relations).
lemma-comm-Z↑-CZ {n} = _≈_.axiom _QRel,_===_.comm-Z↑-CZ
  where open PB ((₂₊ n) QRel,_===_)

lemma-𝑠↑ : ∀ {n} -> 𝑠 {n} ↑ ≡ S ↑ • (Z ↑) ^ toℕ 1/2
lemma-𝑠↑ {n} = begin
  𝑠 ↑ ≡⟨ auto ⟩
  (S • Z ^ toℕ 1/2) ↑ ≡⟨ auto ⟩
  S ↑ • (Z ^ toℕ 1/2) ↑ ≡⟨ Eq.cong (S ↑ •_) (lemma-↑^ (toℕ 1/2) Z) ⟩
  S ↑ • (Z ↑) ^ toℕ 1/2 ∎
  where open ≡-Reasoning

lemma-comm-𝑠↑-CZ : ∀ {n} -> let open PB ((₂₊ n) QRel,_===_) in
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
  open PB ((₂₊ n) QRel,_===_)
  open PP ((₂₊ n) QRel,_===_)
  open SR word-setoid

lemma-comm-Z-CZ : ∀ {n} -> let open PB ((₂₊ n) QRel,_===_) in
  Z • CZ ≈ CZ • Z
-- Z commutes with CZ: taken as the axiom comm-Z-CZ in the Simplified
-- presentation (see lemma-comm-Z↑-CZ for the rationale).
lemma-comm-Z-CZ {n} = _≈_.axiom _QRel,_===_.comm-Z-CZ
  where open PB ((₂₊ n) QRel,_===_)

lemma-comm-𝑠-CZ : ∀ {n} -> let open PB ((₂₊ n) QRel,_===_) in
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
  open PB ((₂₊ n) QRel,_===_)
  open PP ((₂₊ n) QRel,_===_)
  open SR word-setoid
