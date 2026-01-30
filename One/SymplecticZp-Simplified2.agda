{-# OPTIONS --safe #-}
{-# OPTIONS --termination-depth=20 #-}

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
open import Data.Nat.DivMod
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
import Presentation.Base as PB
import Presentation.Properties as PP
open PP using (NFProperty ; NFProperty')
import Presentation.CosetNF as CA
import Presentation.Reidemeister-Schreier as RS
module RSF = RS.Star-Injective-Full.Reidemeister-Schreier-Full
open import Presentation.Tactics

open import Presentation.Construct.Base hiding (_*_)
import Presentation.Construct.Properties.SemiDirectProduct2 as SDP2
import Presentation.Construct.Properties.DirectProduct as DP
import Presentation.Groups.Cyclic as Cyclic


open import Data.Fin.Properties as FP using (suc-injective ; toℕ-inject₁ ; toℕ-fromℕ)
import Data.Nat.Properties as NP
open import Presentation.GroupLike
open import Data.Nat.Primality
open import Data.Nat.Coprimality hiding (sym)
open import Data.Nat.GCD
open Bézout
open import Data.Empty
open import Algebra.Properties.Group
open import Zp.ModularArithmetic

module One.SymplecticZp-Simplified2
  (p-3 : ℕ)
  (p-prime : Prime (suc (suc (suc p-3))))
  (let open PrimeModulus' p-3 p-prime)
  (g : ℤ ₚ)
  (g-gen : ∀ ((x , _) : ℤ* ₚ) -> ∃ \ (k : ℤ ₚ-₁) -> x ≡ g ^′ toℕ k )
  (Zp.Fermats-little-theorem : g ^′ p-1 ≡ 1ₚ)
  where

pattern auto = Eq.refl
pattern ₀ = zero
pattern ₁ = suc ₀
pattern ₂ = suc ₁
pattern ₃ = suc ₂
pattern ₄ = suc ₃

pattern ₁₊ n = suc n
pattern ₂₊ n = suc (suc n)
pattern ₃₊ n = suc (₂₊ n)
pattern ₄₊ n = suc (₃₊ n)

open Primitive-Root-Modp g g-gen Zp.Fermats-little-theorem

module Symplectic-Simplified where
  
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

  S' : Word Gen
  S' = HH • S • HH

  S⁻¹ : Word Gen
  S⁻¹ = S ^ p-1

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

  ₁⁻¹ = ((₁ , λ ()) ⁻¹) .proj₁

  M₁ : Word Gen
  M₁ = M (₁ , λ ())

  M₋₁ : Word Gen
  M₋₁ = M -'₁

  Mg : Word Gen
  Mg = M g′

  Mg^ : ℤ ₚ -> Word Gen
  Mg^ k = Mg ^ toℕ k

  infix 4 _===_
  data _===_ : WRel Gen where
  
    order-S : S ^ p === ε
    order-H : H ^ 2 === M₋₁
    M-power : ∀ (k : ℤ ₚ) -> Mg^ k === M (g^ k)
    semi-MS : Mg • S === S^ (g * g) • Mg

  open PP _===_
  open PB _===_ hiding (_===_)

  import One.SymplecticZp as OS

  open OS.NF1 p-2 p-prime using (C1 ; ε) renaming (HS to HS^)
  
  ⟦_⟧ : ℤ ₚ × ℤ* ₚ × (⊤ ⊎ ℤ ₚ) -> Word Gen
  ⟦ s , m , inj₁ _ ⟧ = S^ s • M m • ε
  ⟦ s , m , inj₂ x ⟧ = S^ s • M m • H • S^ x



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


  
  lemma-M1 : M₁ ≈ ε
  lemma-M1 = begin
    M₁ ≡⟨ aux-Mx=Mx' ((₁ , λ ())) (g^ ₀) auto ⟩
    M (g^ ₀) ≈⟨ sym (axiom (M-power ₀)) ⟩
    Mg^ ₀ ≈⟨ refl ⟩
    ε ∎
    where
    open SR word-setoid

  lemma-order-SH : (S • H) ^ 3 ≈ ε
  lemma-order-SH = begin
    (S • H) ^ 3 ≈⟨ by-assoc auto ⟩
    S • H • S • H • S • H ≈⟨ (cright (cright cong aux-S refl)) ⟩
    S^ x • H • S^ x⁻¹ • H • S^ x • H ≈⟨ refl ⟩
    M₁ ≈⟨ lemma-M1 ⟩
    ε ∎
    where
    open SR word-setoid
    x' : ℤ* ₚ
    x' = (₁ , λ ())
    x = x' .proj₁
    x⁻¹ = ((x' ⁻¹) .proj₁ )
    aux-S : S ≈ S^ x⁻¹
    aux-S = begin
      S ≈⟨ refl ⟩
      S^ ₁ ≡⟨ Eq.cong S^ (Eq.sym aux₁⁻¹') ⟩
      S^ x⁻¹ ∎


  lemma-S⁻¹ : S⁻¹ ≈ S^ ₚ₋₁
  lemma-S⁻¹ = begin
    S⁻¹ ≈⟨ refl ⟩
    S ^ p-1 ≡⟨ Eq.cong (S ^_) (Eq.sym lemma-toℕ-ₚ₋₁) ⟩
    S ^ toℕ ₚ₋₁ ≈⟨ refl ⟩
    S^ ₚ₋₁ ∎
    where
    open SR word-setoid




  lemma-MgS^k : ∀ k ->  let g⁻¹ = (g′ ⁻¹) .proj₁ in let -g⁻¹ = - g⁻¹ in
    Mg • S ^ k ≈ S ^ (k Nat.* toℕ (g * g)) • Mg
  lemma-MgS^k k@0 = trans right-unit (sym left-unit)
  lemma-MgS^k k@1 = begin  
    Mg • S ^ k ≈⟨ refl ⟩
    Mg • S ≈⟨ axiom semi-MS ⟩
    S^ (g * g) • Mg ≈⟨ refl ⟩
    S ^ toℕ (g * g) • Mg ≈⟨ (cleft refl' (Eq.cong (S ^_) (Eq.sym ( NP.*-identityˡ (toℕ (g * g)))))) ⟩
    S ^ (k Nat.* toℕ (g * g)) • Mg ∎
    where
    open SR word-setoid
  lemma-MgS^k k@(₂₊ k') = begin  
    Mg • S ^ k ≈⟨ refl ⟩
    Mg • S • S ^ ₁₊ k' ≈⟨ sym assoc ⟩
    (Mg • S) • S ^ ₁₊ k' ≈⟨ (cleft lemma-MgS^k 1 ) ⟩
    (S ^ (1 Nat.* toℕ (g * g)) • Mg) • S ^ ₁₊ k' ≈⟨ assoc ⟩
    S ^ (1 Nat.* toℕ (g * g)) • Mg • S ^ ₁₊ k' ≈⟨ (cright lemma-MgS^k (₁₊ k')) ⟩
    S ^ (1 Nat.* toℕ (g * g)) • S ^ (₁₊ k' Nat.* toℕ (g * g)) • Mg ≈⟨ sym assoc ⟩
    (S ^ (1 Nat.* toℕ (g * g)) • S ^ (₁₊ k' Nat.* toℕ (g * g))) • Mg ≈⟨ (cleft sym (lemma-^-+ S ((1 Nat.* toℕ (g * g))) ((₁₊ k' Nat.* toℕ (g * g))))) ⟩
    (S ^ ((1 Nat.* toℕ (g * g)) Nat.+ (₁₊ k' Nat.* toℕ (g * g)))) • Mg ≈⟨ (cleft refl' (Eq.cong (S ^_) (Eq.sym (NP.*-distribʳ-+ (toℕ (g * g)) ₁ (₁₊ k'))))) ⟩
    S ^ ((1 Nat.+ ₁₊ k') Nat.* toℕ (g * g) ) • Mg ≈⟨ refl ⟩
    S ^ (k Nat.* toℕ (g * g)) • Mg ∎
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


  lemma-MgS^k' : ∀ k -> let x⁻¹ = (g′ ⁻¹) .proj₁ in let -x⁻¹ = - x⁻¹ in
    Mg • S^ k ≈ S^ (k * (g * g)) • Mg
  lemma-MgS^k' k = begin 
    Mg • S^ k ≈⟨ refl ⟩
    Mg • S ^ toℕ k ≈⟨ lemma-MgS^k (toℕ k) ⟩
    S ^ (toℕ k Nat.* toℕ (g * g)) • Mg ≈⟨ (cleft lemma-S^k-% (toℕ k Nat.* toℕ (g * g))) ⟩
    S ^ ((toℕ k Nat.* toℕ (g * g)) % p) • Mg ≈⟨ (cleft refl' (Eq.cong (S ^_) (lemma-toℕ-% k (g * g)))) ⟩
    S ^ toℕ (k * (g * g)) • Mg ≈⟨ refl ⟩
    S^ (k * (g * g)) • Mg ∎
    where
    open SR word-setoid
    x⁻¹ = (g′ ⁻¹) .proj₁
    -x⁻¹ = - x⁻¹

  lemma-Mg^kS : ∀ k -> Mg ^ k • S ≈ S^ ((g * g) ^′ k) • Mg ^ k
  lemma-Mg^kS k@0 = trans left-unit (sym right-unit)
  lemma-Mg^kS k@1 = begin
    Mg ^ k • S ≈⟨ axiom semi-MS ⟩
    S^ ((g * g)) • Mg ^ k ≈⟨ (cleft refl' (Eq.cong S^ (Eq.sym (lemma-x^′1=x (fromℕ< _))))) ⟩
    S^ ((g * g) ^′ k) • Mg ^ k ∎
    where
    open SR word-setoid
  lemma-Mg^kS k@(₂₊ n) = begin
    (Mg • Mg ^ ₁₊ n) • S ≈⟨ assoc ⟩
    Mg • Mg ^ ₁₊ n • S ≈⟨ (cright lemma-Mg^kS (₁₊ n)) ⟩
    Mg • S^ ((g * g) ^′ (₁₊ n)) • Mg ^ (₁₊ n) ≈⟨ sym assoc ⟩
    (Mg • S^ ((g * g) ^′ (₁₊ n))) • Mg ^ (₁₊ n) ≈⟨ (cleft lemma-MgS^k' ((g * g) ^′ (₁₊ n))) ⟩
    (S^ (((g * g) ^′ (₁₊ n)) * (g * g)) • Mg) • Mg ^ (₁₊ n) ≈⟨ refl' (Eq.cong (\ xx -> (S^ xx • Mg) • Mg ^ (₁₊ n)) (*-comm ((g * g) ^′ (₁₊ n)) (g * g))) ⟩
    (S^ ((g * g) * ((g * g) ^′ (₁₊ n))) • Mg) • Mg ^ (₁₊ n) ≈⟨ assoc ⟩
    S^ ((g * g) ^′ k) • Mg • Mg ^ ₁₊ n ∎
    where
    open SR word-setoid


  lemma-semi-MS : ∀ x -> let x' = x .proj₁ in let k = g-gen x .proj₁ in M x • S ≈ S^ ((x' * x')) • M x
  lemma-semi-MS x = begin
    M x • S ≈⟨ (cleft refl' (aux-Mx=Mx' x (g^ k) (eqk))) ⟩
    M (g^ k) • S ≈⟨ cong (sym (axiom (M-power (k)))) refl ⟩
    Mg^ k • S ≈⟨ lemma-Mg^kS (toℕ k) ⟩
    S^ ((g * g) ^′ toℕ k) • Mg^ k ≈⟨ (cright axiom (M-power (k))) ⟩
    S^ ((g * g) ^′ toℕ k) • M (g^ k) ≈⟨ (cleft refl' (Eq.cong S^ (*-^′-distribʳ g g (toℕ k)))) ⟩
    S^ ((g ^′ toℕ k) * (g ^′ toℕ k)) • M (g^ k) ≈⟨ sym (cleft refl' (Eq.cong₂ (\ xx yy -> S^ (xx * yy)) (eqk) (eqk))) ⟩
    S^ (x' * x') • M (g^ k) ≈⟨ (cright refl' (aux-Mx=Mx' (g^ k) x (Eq.sym (eqk)))) ⟩
    S^ (x' * x') • M x ∎
    where
    open SR word-setoid
    x' = x .proj₁
    k = inject₁ (g-gen x .proj₁)
    eqk : x .proj₁ ≡ (g^ k) .proj₁
    eqk = Eq.sym (lemma-log-inject x)

  open import Data.Fin.Properties
  
  lemma-Mg^p-1=ε : Mg ^ p-1 ≈ ε
  lemma-Mg^p-1=ε = begin
    Mg ^ p-1 ≡⟨ Eq.cong (Mg ^_) (Eq.sym (toℕ-fromℕ< (NP.n<1+n p-1))) ⟩
    Mg^ (fromℕ< (NP.n<1+n p-1)) ≈⟨ axiom (M-power (₂₊ (fromℕ< _))) ⟩
    M (g^ p-1') ≡⟨ aux-Mx=Mx' (g^ p-1') ((g ^′ p-1 , lemma-g^′k≠0 p-1)) (Eq.cong (g ^′_) (toℕ-fromℕ< (NP.n<1+n p-1))) ⟩
    M (g ^′ p-1 , lemma-g^′k≠0 p-1) ≡⟨ aux-Mx=Mx' ((g ^′ p-1 , lemma-g^′k≠0 p-1)) (1ₚ , λ ()) Zp.Fermats-little-theorem ⟩
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
    M x • M y ≈⟨ cong (refl' (aux-Mx=Mx' x (g^ k) eqk)) (refl' (aux-Mx=Mx' y (g^ l) eql)) ⟩
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
    M (g^ (inject₁ (fromℕ< (m%n<n [k+l] p-1)))) ≡⟨ aux-Mx=Mx' (g^ (inject₁ (fromℕ< (m%n<n [k+l] p-1)))) (g^′ [k+l]) aux-2 ⟩
    M (g^′ [k+l]) ≡⟨ aux-Mx=Mx' (g^′ [k+l]) (g^′ toℕ k *' g^′ toℕ l) aux-1 ⟩
    M (g^′ toℕ k *' g^′ toℕ l) ≡⟨ aux-Mx=Mx' (g^′ toℕ k *' g^′ toℕ l) (x *' y) aux-0 ⟩
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
    M (-'₁ *' -'₁) ≡⟨ aux-Mx=Mx' (-'₁ *' -'₁) (₁ , (λ ())) aux-0 ⟩
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


  grouplike : Grouplike _===_
  grouplike (H-gen) = H ^ 3 , by-assoc-and lemma-order-H auto auto
  grouplike (S-gen) = S ^ p-1 , claim
    where
    open SR word-setoid
    claim : S ^ p-1 • S ≈ ε
    claim = begin
      S ^ p-1 • S ≈⟨ sym (lemma-^-+ S p-1 1) ⟩
      S ^ (p-1 Nat.+ 1) ≡⟨ Eq.cong (S ^_) (NP.+-comm p-1 1) ⟩
      (S ^ p) ≈⟨ axiom order-S ⟩
      ε ∎


  lemma-[H⁻¹S⁻¹]^3 : (H⁻¹ • S⁻¹) ^ 3 ≈ ε
  lemma-[H⁻¹S⁻¹]^3 = begin
    (H⁻¹ • S⁻¹) ^ 3 ≈⟨ _≈_.sym assoc ⟩
    (H⁻¹ • S⁻¹) WB.^' 3 ≈⟨ lemma-cong-inv (lemma-order-SH) ⟩
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
    open Pattern-Assoc

  derived-5 : ∀ x k -> (nz : x ≢ ₀) -> let x⁻¹ = ((x , nz) ⁻¹) .proj₁ in let -x⁻¹ = - x⁻¹ in

    M (x , nz) • S ^ k ≈ S ^ (k Nat.* toℕ (x * x)) • M (x , nz)
  derived-5 x k@0 nz = trans right-unit (sym left-unit)
  derived-5 x k@1 nz = begin  
    M (x , nz) • S ^ k ≈⟨ refl ⟩
    M (x , nz) • S ≈⟨ lemma-semi-MS (x , nz) ⟩
    S^ (x * x) • M (x , nz) ≈⟨ refl ⟩
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


  lemma-MS^k : ∀ x k -> (nz : x ≢ ₀) -> let x⁻¹ = ((x , nz) ⁻¹) .proj₁ in let -x⁻¹ = - x⁻¹ in
    M (x , nz) • S^ k ≈ S^ (k * (x * x)) • M (x , nz)
  lemma-MS^k x k nz = begin 
    M (x , nz) • S^ k ≈⟨ refl ⟩
    M (x , nz) • S ^ toℕ k ≈⟨ derived-5 x (toℕ k) nz ⟩
    S ^ (toℕ k Nat.* toℕ (x * x)) • M (x , nz) ≈⟨ (cleft lemma-S^k-% (toℕ k Nat.* toℕ (x * x))) ⟩
    S ^ ((toℕ k Nat.* toℕ (x * x)) % p) • M (x , nz) ≈⟨ (cleft refl' (Eq.cong (S ^_) (lemma-toℕ-% k (x * x)))) ⟩
    S ^ toℕ (k * (x * x)) • M (x , nz) ≈⟨ refl ⟩
    S^ (k * (x * x)) • M (x , nz) ∎
    where
    open SR word-setoid
    x⁻¹ = ((x , nz) ⁻¹) .proj₁
    -x⁻¹ = - x⁻¹


  lemma-comm-HHS : H • H • S ≈ S • H • H
  lemma-comm-HHS = begin
    H • H • S ≈⟨ sym assoc ⟩
    HH • S ≈⟨ (cleft axiom order-H) ⟩
    M₋₁ • S ≈⟨ lemma-semi-MS -'₁ ⟩
    S^ (- ₁ * - ₁) • M₋₁ ≈⟨ (cleft refl' (Eq.cong S^ aux-0)) ⟩
    S^ ₁ • M₋₁ ≈⟨ refl ⟩
    S • M₋₁ ≈⟨ (cright sym (axiom order-H)) ⟩
    S • H • H ∎
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



-- ----------------------------------------------------------------------
-- * Lemmas

module Symplectic-Powers
  where

  -- This module provides a rewrite system for reducing powers of
  -- Symplectic operators (for example, S⁴ → I). It also commutes
  -- generators on different qubits (for example, H1 H0 → H0 H1).
  -- Finally, it moves scalars to the end of the word. While this is
  -- not yet a very powerful rewrite system, it is a useful
  -- bootstrapping step.

  open Symplectic-Simplified

  open Rewriting
  open PB _===_ hiding (_===_)

  -- ----------------------------------------------------------------------
  -- * Lemmas

  -- The following lemmas are needed to justify the rewrite steps.

  -- ----------------------------------------------------------------------
  -- * Rewrite rules for monoidal structure and order of generators

  step-order : Step-Function Gen _===_

  -- Order of generators.
  step-order (H-gen ∷ H-gen ∷ H-gen ∷ H-gen ∷ xs) = just (xs , at-head (lemma-order-H))
  step-order (S-gen ∷ H-gen ∷ S-gen ∷ H-gen ∷ S-gen ∷ H-gen ∷ xs) = just (xs , at-head (lemma-order-SH))

  -- Commuting of generators.

  -- Catch-all
  step-order _ = nothing

  -- From this rewrite relation, we extract a tactic 'general-powers'.
  open Rewriting.Step (step-cong step-order) renaming (general-rewrite to general-powers) public


module Symplectic-Rewriting-HH where

  open Symplectic-Simplified

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
  
  step-symplectic1 (H-gen ∷ H-gen ∷ S-gen ∷ xs) = just (S-gen ∷ H-gen ∷ H-gen ∷ xs , at-head (lemma-comm-HHS))

  -- Catch-all
  step-symplectic1 _ = nothing

  -- From this rewrite relation, we extract a tactic 'rewrite-symplectic1'.
  open Rewriting.Step (step-cong (step-order) then step-cong step-symplectic1) renaming (general-rewrite to rewrite-HH) public



module Lemmas where

  open Symplectic-Simplified

  -- open Symplectic-Rewriting-HH p-2 p-prime
  -- open Symplectic-Powers p-2 p-prime

  open PB _===_ hiding (_===_)
  open PP _===_
  open Pattern-Assoc
  open import Data.Fin.Properties

  lemma-S^k+l : ∀ k l -> S^ k • S^ l ≈ S^ (k + l)
  lemma-S^k+l k l = begin
    S^ k • S^ l ≈⟨ refl ⟩
    S ^ toℕ k • S ^ toℕ l ≈⟨ sym (lemma-^-+ S (toℕ k) (toℕ l)) ⟩
    S ^ (toℕ k Nat.+ toℕ l) ≡⟨ Eq.cong (S ^_) (m≡m%n+[m/n]*n k+l p) ⟩
    S ^ (k+l Nat.% p Nat.+ (k+l Nat./ p) Nat.* p) ≈⟨ lemma-^-+ S (k+l Nat.% p) (((k+l Nat./ p) Nat.* p)) ⟩
    S ^ (k+l Nat.% p) • S ^ ((k+l Nat./ p) Nat.* p) ≈⟨ cong (refl' (Eq.cong (S ^_) (Eq.sym (toℕ-fromℕ< (m%n<n k+l p))))) (refl' (Eq.cong (S ^_) (NP.*-comm ((k+l Nat./ p)) p))) ⟩
    S ^ toℕ (fromℕ< (m%n<n k+l p)) • S ^ (p Nat.* (k+l Nat./ p) ) ≈⟨ cong (sym (refl)) (sym (lemma-^^ S p (k+l Nat./ p))) ⟩
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
    S^ ₀ ≈⟨ (refl) ⟩
    ε ∎
    where
    open SR word-setoid
    k-k = toℕ k Nat.+ toℕ (- k)

  lemma-S^-k+k : ∀ k -> S^ (- k) • S^ k ≈ ε
  lemma-S^-k+k k = begin
    S^ (- k) • S^ k ≈⟨ refl ⟩
    S ^ toℕ (- k) • S ^ toℕ k ≈⟨ word-comm (toℕ (- k)) (toℕ ( k)) refl ⟩
    S ^ toℕ k • S ^ toℕ (- k) ≈⟨ refl ⟩
    S^ k • S^ (- k) ≈⟨ lemma-S^k-k k ⟩
    ε ∎
    where
    open SR word-setoid

  open Eq using (_≢_)



  derived-D : ∀ x -> (nz : x ≢ ₀) -> let x⁻¹ = ((x , nz) ⁻¹) .proj₁ in let -x⁻¹ = - x⁻¹ in
    H • S^ x • H ≈ H • S^ x • H • S^ x⁻¹ • H • H ^ 3 • S^ -x⁻¹
  derived-D  x nz = begin
    H • S^ x • H ≈⟨ (cright cright sym right-unit) ⟩
    H • S^ x • H • ε ≈⟨ cright cright cright sym (lemma-S^k-k x⁻¹) ⟩
    H • S^ x • H • S^ x⁻¹ • S^ -x⁻¹ ≈⟨ cright cright cright cright sym left-unit ⟩
    H • S^ x • H • S^ x⁻¹ • ε • S^ -x⁻¹ ≈⟨ cright cright cright cright sym (cong (lemma-order-H) refl) ⟩
    H • S^ x • H • S^ x⁻¹ • H ^ 4 • S^ -x⁻¹ ≈⟨ (cright cright cright cright special-assoc (□ ^ 4 • □) (□ • □ ^ 3 • □) auto) ⟩
    H • S^ x • H • S^ x⁻¹ • H • H ^ 3 • S^ -x⁻¹ ∎
    where
    x⁻¹ = ((x , nz) ⁻¹) .proj₁
    -x⁻¹ = - x⁻¹ 
    open SR word-setoid



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
    (M (y , nzy) • S^ -x⁻¹) • (S^ x⁻¹ • H • S^ x • H • S^ x⁻¹ • H) • H ^ 3 • S^ -x⁻¹ ≈⟨ (cleft (cright  (refl))) ⟩
    (M (y , nzy) • S ^ toℕ -x⁻¹) • (S^ x⁻¹ • H • S^ x • H • S^ x⁻¹ • H) • H ^ 3 • S^ -x⁻¹ ≈⟨ (cleft derived-5 y (toℕ -x⁻¹) nzy) ⟩
    (S ^ (toℕ -x⁻¹ Nat.* toℕ (y * y)) • M (y , nzy)) • (S^ x⁻¹ • H • S^ x • H • S^ x⁻¹ • H) • H ^ 3 • S^ -x⁻¹ ≈⟨ special-assoc (□ ^ 2 • □ ^ 2) (□ • □ ^ 2 • □) auto ⟩
    S ^ (toℕ -x⁻¹ Nat.* toℕ (y * y)) • (M (y , nzy) • (S^ x⁻¹ • H • S^ x • H • S^ x⁻¹ • H)) • H ^ 3 • S^ -x⁻¹ ≈⟨ (cright cleft (cright (cright cright cleft refl' (Eq.cong S^ (Eq.sym (inv-involutive ((x , nz)))))))) ⟩
    S ^ (toℕ -x⁻¹ Nat.* toℕ (y * y)) • (M (y , nzy) • M ((x , nz) ⁻¹)) • H ^ 3 • S^ -x⁻¹ ≈⟨ (cright cleft  (lemma-M-mul (y , nzy) ((x , nz) ⁻¹))) ⟩
    S ^ (toℕ -x⁻¹ Nat.* toℕ (y * y)) • M ((y , nzy) *' ((x , nz) ⁻¹)) • H ^ 3 • S^ -x⁻¹ ≈⟨ (cright special-assoc (□ • □ ^ 3 • □) (□ ^ 3 • □ ^ 2) auto) ⟩
    S ^ (toℕ -x⁻¹ Nat.* toℕ (y * y)) • (M ((y , nzy) *' ((x , nz) ⁻¹)) • HH) • H • S^ -x⁻¹ ≈⟨ (cright cleft (cright (axiom order-H))) ⟩
    S ^ (toℕ -x⁻¹ Nat.* toℕ (y * y)) • (M ((y , nzy) *' ((x , nz) ⁻¹)) • M -'₁) • H • S^ -x⁻¹ ≈⟨ (cright cleft (lemma-M-mul (((y , nzy) *' ((x , nz) ⁻¹))) -'₁)) ⟩
    S ^ (toℕ -x⁻¹ Nat.* toℕ (y * y)) • (M (((y , nzy) *' ((x , nz) ⁻¹)) *' -'₁) ) • H • S^ -x⁻¹ ≈⟨ (cleft sym (lemma-S^ab -x⁻¹ (y * y))) ⟩
    S ^ toℕ (-x⁻¹ * (y * y)) • M -y/x' • (H • S^ -x⁻¹) ≈⟨  refl ⟩
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
    H • (S^ x • H • S^ x⁻¹ • H • S^ x • H) ≈⟨ special-assoc (□ • □ ^ 6) (□ ^ 3 • □ ^ 4) auto ⟩
    (H • S^ x • H) • S^ x⁻¹ • H • S^ x • H ≈⟨ (trans (sym left-unit) (cong (sym lemma-M1) refl)) ⟩
    M₁ • (H • S^ x • H) • S^ x⁻¹ • H • S^ x • H ≈⟨ sym assoc ⟩
    (M₁ • (H • S^ x • H)) • S^ x⁻¹ • H • S^ x • H ≈⟨ (cleft derived-7 x ₁ (x' .proj₂) λ ()) ⟩
    (S^ (-x⁻¹ * (₁ * ₁)) • M (((₁ , λ ()) *' x' ⁻¹) *' -'₁) • H • S^ -x⁻¹) • S^ x⁻¹ • H • S^ x • H ≈⟨ cleft (cright (cleft aux-MM ((((₁ , λ ()) *' x' ⁻¹) *' -'₁) .proj₂) ((-' (x' ⁻¹)) .proj₂) aux-a1)) ⟩
    (S^ (-x⁻¹ * ₁) • M (-' (x' ⁻¹)) • H • S^ -x⁻¹) • S^ x⁻¹ • H • S^ x • H ≈⟨ special-assoc (□ ^ 4 • □ ^ 4) (□ • □ ^ 4 • □ ^ 3) auto ⟩
    S^ (-x⁻¹ * ₁) • (M (-' (x' ⁻¹)) • H • S^ -x⁻¹ • S^ x⁻¹) • H • S^ x • H ≈⟨ cong (refl' (Eq.cong S^ (*-identityʳ -x⁻¹))) (cleft cright (cright lemma-S^-k+k x⁻¹)) ⟩
    S^ -x⁻¹ • (M (-' (x' ⁻¹)) • H • ε) • H • S^ x • H ≈⟨ (cright cleft (cright right-unit)) ⟩
    S^ -x⁻¹ • (M (-' (x' ⁻¹)) • H) • H • S^ x • H ≈⟨ (cright special-assoc (□ ^ 2 • □ ^ 3) (□ ^ 3 • □ ^ 2) auto) ⟩
    S^ -x⁻¹ • (M (-' (x' ⁻¹)) • H • H) • S^ x • H ≈⟨ (cright cleft cright (axiom order-H)) ⟩
    S^ -x⁻¹ • (M (-' (x' ⁻¹)) • M -'₁) • S^ x • H ≈⟨ (cright cleft  (lemma-M-mul (-' (x' ⁻¹)) -'₁)) ⟩
    S^ -x⁻¹ • M (-' (x' ⁻¹) *' -'₁) • S^ x • H ≈⟨ (cright cleft aux-MM ((-' (x' ⁻¹) *' -'₁) .proj₂) ((x' ⁻¹) .proj₂) aux-a2) ⟩
    S^ -x⁻¹ • M (x' ⁻¹) • S^ x • H ≈⟨ sym (cong refl assoc) ⟩
    S^ -x⁻¹ • (M (x' ⁻¹) • S^ x) • H ≈⟨ (cright cleft lemma-MS^k x⁻¹ x ((x' ⁻¹) .proj₂)) ⟩
    S^ -x⁻¹ • (S^ (x * (x⁻¹ * x⁻¹)) • M (x' ⁻¹)) • H ≈⟨ (cright cleft (cleft refl' (Eq.cong S^ aux-a3))) ⟩
    S^ -x⁻¹ • (S^ x⁻¹ • M (x' ⁻¹)) • H ≈⟨  special-assoc (□ • □ ^ 2 • □) (□ ^ 2 • □ ^ 2) auto ⟩
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

  -- Just to collect all derived rules.
  module Derived where
  
    -- semi-HM : ∀ (x : ℤ* ₚ) -> H • M x ≈ M (x ⁻¹) • H
    -- M (y , nzy) • H • S^ x • H ≈ S^ (-x⁻¹ * (y * y)) • M -y/x' • (H • S^ -x⁻¹)
    -- M (x , nz) • S^ k ≈ S^ (k * (x * x)) • M (x , nz)
    -- lemma-M-mul : ∀ x y -> M x • M y ≈ M (x *' y)
    -- M x • S ≈ S^ ((x' * x')) • M x
    -- Mg ^ p-1 ≈ ε
    -- lemma-Mg^kS : ∀ k -> Mg ^ k • S ≈ S^ ((g * g) ^′ k) • Mg ^ k
    -- Mg • S^ k ≈ S^ (k * (g * g)) • Mg
    -- lemma-S^k-% : ∀ k -> S ^ k ≈ S ^ (k % p)
    -- HH ≈ M -'₁
    -- S⁻¹ ≈ S^ ₚ₋₁
    -- ε ≈ M (₁ , λ ())
    -- (H⁻¹ • S⁻¹) ^ 3 ≈ ε
    -- (S⁻¹ • H⁻¹) ^ 3 ≈ ε

module Iso
  where


  open import One.SymplecticZp hiding (module Lemmas)
  module Sym  = Symplectic p-2 p-prime
  module Sim  = Symplectic-Simplified
  open Lemmas
  open Sym renaming (grouplike to grouplike₁ ; Gen to Gen₁) using ()
  open Sim renaming (grouplike to grouplike₂ ; Gen to Gen₂) using ()

  f : Sym.Gen -> Sim.Gen
  f Symplectic.H-gen = Sim.H-gen
  f Symplectic.S-gen = Sim.S-gen


  h : Sim.Gen -> Word Sym.Gen
  h (Sim.H-gen) = Sym.H
  h (Sim.S-gen) = Sym.S
  

  open PB Sym._===_ renaming (_===_ to _===₁_ ; _≈_ to _≈₁_) using ()
  open PB Sim._===_ renaming (_===_ to _===₂_ ; _≈_ to _≈₂_) using ()

  open import Presentation.Morphism _===₁_ _===₂_
  open GroupMorphs grouplike₁ grouplike₂

  open PP Sym._===_ renaming (by-assoc-and to by-assoc-and₁ ; word-setoid to ws₁)
  open PP Sim._===_ renaming (by-assoc-and to by-assoc-and₂ ; word-setoid to ws₂ ; by-assoc to by-assoc₂) using ()

  open PB hiding (_===_)
  open Sim

  f* = wmap f
  f' = [_]ʷ ∘ f
  f'* = f' WB.*
  
  lemma-f* : ∀ k -> f* (Sym.S ^ k) ≈₂ Sim.S ^ k
  lemma-f* ₀ = _≈₂_.refl
  lemma-f* ₁ = _≈₂_.refl
  lemma-f* (₂₊ k) = cong _≈₂_.refl (lemma-f* (₁₊ k))

  lemma-f'* : ∀ k -> f'* (Sym.S ^ k) ≈₂ Sim.S ^ k
  lemma-f'* ₀ = _≈₂_.refl
  lemma-f'* ₁ = _≈₂_.refl
  lemma-f'* (₂₊ k) = cong _≈₂_.refl (lemma-f'* (₁₊ k))

  lemma-f'*-H : ∀ k -> f'* (Sym.H ^ k) ≈₂ Sim.H ^ k
  lemma-f'*-H ₀ = _≈₂_.refl
  lemma-f'*-H ₁ = _≈₂_.refl
  lemma-f'*-H (₂₊ k) = cong _≈₂_.refl (lemma-f'*-H (₁₊ k))

  lemma-f'*-M : ∀ x -> f'* (Sym.M x) ≈₂ Sim.M x
  lemma-f'*-M x' = begin
    f'* (Sym.M x') ≈⟨ cong (lemma-f'* (toℕ (x))) (cong _≈₂_.refl (cong (lemma-f'* (toℕ x⁻¹)) (cong refl (cong (lemma-f'* (toℕ x)) _≈₂_.refl)))) ⟩
    Sim.M x' ∎
    where
    open SR ws₂
    x = x' .proj₁
    x⁻¹ = ((x' ⁻¹) .proj₁ )

    
  lemma-f'*-Mg : ∀ x -> let (k' , eq) = g-gen x in let k = toℕ (inject₁ k') in f'* (Sym.M x) ≈₂ Sim.Mg ^ k
  lemma-f'*-Mg x = begin
    f'* (Sym.M x) ≡⟨ Eq.cong f'* (Sym.aux-Mx=Mx' x ((g ^′ k , lemma-g^′k≠0 k)) eqk) ⟩
    f'* (Sym.M (g ^′ k , lemma-g^′k≠0 k)) ≈⟨ lemma-f'*-M ((g ^′ k , lemma-g^′k≠0 k)) ⟩
    S^ z • H • S^ z⁻¹ • H • S^ z • H ≈⟨ _≈₂_.refl ⟩
    M z' ≈⟨ _≈₂_.refl ⟩
    M (g^ k') ≈⟨ sym (axiom (M-power k')) ⟩
    Sim.Mg ^ k ∎
    where
    open SR ws₂
    k' = inject₁ (g-gen x .proj₁)
    k = toℕ k'
    z' = (g ^′ k , lemma-g^′k≠0 k)
    z = z' .proj₁
    z⁻¹ = ((z' ⁻¹) .proj₁ )
    eqk : x .proj₁ ≡ (g^ k') .proj₁
    eqk = Eq.sym (lemma-log-inject x)


  f-well-defined : ∀ {w v} -> w ===₁ v -> f'* w ≈₂ f'* v
  f-well-defined Symplectic.order-S = begin
    f'* (Sym.S • Sym.S ^ ₁₊ p-2) ≡⟨ lemma-* ([ Sym.S-gen ]ʷ • Sym.S ^ ₁₊ p-2) ⟩
    (wmap f) (Sym.S • Sym.S ^ ₁₊ p-2) ≈⟨ lemma-f* (₂₊ p-2) ⟩
    Sim.S ^ p ≈⟨ _≈₂_.axiom order-S ⟩
    f'* ε ∎
    where
    open SR ws₂
  f-well-defined Symplectic.order-H = lemma-order-H
  f-well-defined Symplectic.order-SH = lemma-order-SH
  f-well-defined Symplectic.comm-HHS = lemma-comm-HHS
  f-well-defined (Symplectic.M-mul x y) = begin
    f'* (Sym.M x • Sym.M y) ≈⟨ _≈₂_.refl ⟩
    f'* (Sym.M x) • f'* (Sym.M y) ≈⟨ cong (lemma-f'*-M x) (lemma-f'*-M y) ⟩
    (Sim.M x) • (Sim.M y) ≡⟨ auto ⟩
    (Sim.M x) • (Sim.M y) ≈⟨ lemma-M-mul x y ⟩
    (Sim.M (x *' y)) ≈⟨ sym (lemma-f'*-M (x *' y)) ⟩
    f'* (Sym.M (x *' y)) ∎
    where
    open SR ws₂
  f-well-defined (Symplectic.semi-MS (x , nz)) = begin
    f'* (Sym.M (x , nz) • Sym.S) ≈⟨ cong (lemma-f'*-M ((x , nz))) (lemma-f'* 1) ⟩
    Sim.M (x , nz) • Sim.S ≈⟨ lemma-semi-MS ((x , nz)) ⟩
    (Sim.S^ ((x , nz) Sym.^2) • Sim.M (x , nz)) ≈⟨ sym (cong (lemma-f'* (toℕ ((x , nz) Sym.^2))) (lemma-f'*-M ((x , nz)))) ⟩
    f'* (Sym.S^ ((x , nz) Sym.^2) • Sym.M (x , nz)) ∎
    where
    open SR ws₂

  h* = h WB.*

  lemma-h* : ∀ k -> h* (S ^ k) ≈₁ Sym.S ^ k
  lemma-h* ₀ = refl
  lemma-h* ₁ = refl
  lemma-h* (₂₊ k) = cong refl (lemma-h* (₁₊ k))

  lemma-h*-H : ∀ k -> h* (H ^ k) ≈₁ Sym.H ^ k
  lemma-h*-H ₀ = refl
  lemma-h*-H ₁ = refl
  lemma-h*-H (₂₊ k) = cong refl (lemma-h*-H (₁₊ k))

  lemma-h*'-H : ∀ k -> h* (H^ k) ≈₁ Sym.H ^ toℕ k
  lemma-h*'-H ₀ = refl
  lemma-h*'-H ₁ = refl
  lemma-h*'-H ₂ = refl
  lemma-h*'-H ₃ = refl


  lemma-h*-w^k : ∀ w k -> h* (w ^ k) ≡ h* w ^ k
  lemma-h*-w^k w k@0 = auto
  lemma-h*-w^k w k@1 = auto
  lemma-h*-w^k w k@(₂₊ k') = begin
    h* (w ^ k) ≡⟨ auto ⟩
    h* w • h* (w ^ ₁₊ k') ≡⟨ Eq.cong₂ _•_ auto (lemma-h*-w^k w (₁₊ k')) ⟩
    h* w ^ k ∎
    where
    open ≡-Reasoning


  lemma-h*-M : ∀ x -> h* (M x) ≈₁ Sym.M x
  lemma-h*-M x' = begin
    h* (M x') ≈⟨ refl ⟩
    h* (S^ x • H • S^ x⁻¹ • H • S^ x • H) ≈⟨ refl ⟩
    h* (S^ x) • Sym.H • h* (S^ x⁻¹) • Sym.H • h* (S^ x) • Sym.H ≈⟨ (cong (lemma-h* (toℕ x)) (cong refl (cong (lemma-h* (toℕ x⁻¹)) (cong refl (cong (lemma-h* (toℕ x)) refl))))) ⟩
    (Sym.S^ x) • Sym.H • (Sym.S^ x⁻¹) • Sym.H • (Sym.S^ x) • (Sym.H) ≈⟨ refl ⟩
    Sym.M x' ∎
    where
    open SR ws₁
    x = x' .proj₁
    x⁻¹ = ((x' ⁻¹) .proj₁ )


  h-well-defined : ∀ {w v} -> w ===₂ v -> h* w ≈₁ h* v
  h-well-defined Sim.order-S = begin
    h* (S • S ^ ₁₊ p-2) ≈⟨ lemma-h* p ⟩
    (Sym.S ^ p) ≈⟨ axiom Sym.order-S ⟩
    h* ε ∎
    where open SR ws₁
  h-well-defined Sim.order-H = begin
    h* (H • H) ≈⟨ refl ⟩
    Sym.H • Sym.H ≈⟨ lemma-HH-M-1 ⟩
    Sym.M -'₁ ≈⟨ sym (lemma-h*-M -'₁) ⟩
    h* M₋₁ ∎
    where
    open import One.SymplecticZp
    open Lemmas-noDerived p-2 p-prime
    open SR ws₁
  h-well-defined (Sim.M-power k) = begin
    h* (Mg^ k) ≡⟨ lemma-h*-w^k Mg (toℕ k) ⟩
    h* Mg ^ toℕ k ≈⟨ lemma-^-cong (h* Mg) (Sym.M g′) (toℕ k) (lemma-h*-M g′) ⟩
    Sym.M g′ ^ toℕ k ≈⟨ Sym.lemma-M-power g′ (toℕ k) ⟩
    Sym.M (g^ k) ≈⟨ sym (lemma-h*-M (g^ k)) ⟩
    h* (M (g^ k)) ∎
    where
    open SR ws₁
  h-well-defined (Sim.semi-MS) = begin
    h* (Mg • S) ≈⟨ refl ⟩
    h* Mg • h* S ≈⟨ refl ⟩
    h* (S^ x • H • S^ x⁻¹ • H • S^ x • H) • h* S ≈⟨ refl ⟩
    (h* (S^ x) • Sym.H • h* (S^ x⁻¹) • Sym.H • h* (S^ x) • Sym.H) • Sym.S ≈⟨ (cleft Sym._===_) (lemma-h*-M x') ⟩
    ((Sym.S^ x) • Sym.H • (Sym.S^ x⁻¹) • Sym.H • (Sym.S^ x) • Sym.H) • Sym.S ≈⟨ axiom (Sym.semi-MS x') ⟩
    Sym.S^ (x' Sym.^2) • ((Sym.S^ x) • Sym.H • (Sym.S^ x⁻¹) • Sym.H • (Sym.S^ x) • Sym.H) ≈⟨ cong refl ( refl) ⟩
    Sym.S^ (x' Sym.^2) • Sym.M x' ≈⟨ cong (sym (lemma-h* (toℕ (g * g)))) (sym (lemma-h*-M x')) ⟩
    h* (S^ (g * g) • Mg) ∎
    where
    open SR ws₁
    x' = (g , g≠0)
    x = x' .proj₁
    x⁻¹ = ((x' ⁻¹) .proj₁ )


  f-left-inv-gen : ∀ x -> [ x ]ʷ ≈₂ (f'*) (h x)
  f-left-inv-gen (Sim.H-gen) = _≈₂_.refl
  f-left-inv-gen (Sim.S-gen) = _≈₂_.refl

  h-left-inv-gen : ∀ x -> [ x ]ʷ ≈₁ (h*) (f' x)
  h-left-inv-gen Sym.S-gen = refl
  h-left-inv-gen Sym.H-gen = refl

  open import Algebra.Bundles using (Group)
  open import Algebra.Morphism.Structures using (module GroupMorphisms)

  open import Presentation.Morphism
  open GroupMorphisms
  module G1 = Group-Lemmas Sym.Gen Sym._===_ Sym.grouplike
  module G2 = Group-Lemmas Sim.Gen Sim._===_ Sim.grouplike

  Theorem-Sym-iso-Sim : IsGroupIsomorphism (Group.rawGroup G1.•-ε-group) (Group.rawGroup G2.•-ε-group) (f'*)
  Theorem-Sym-iso-Sim = StarGroupIsomorphism.isGroupIsomorphism f' h f-well-defined  f-left-inv-gen h-well-defined  h-left-inv-gen




module Clifford where

  -- Clifford mod scalars is ℤₚ² ⋊ Sp(2,p), whose complete relations
  -- are:

  -- Semidirct product of relations:
  --   ℤₚ²:
  --     order-X  : X ^ p === ε
  --     order-Z  : Z ^ p === ε
  --     comm-Z-X : Z X === X Z
      
  --   Sp(2,p): 
  --     order-S : S ^ p === ε
  --     order-H : H ^ 2 === M₋₁
  --     M-power : ∀ (k : ℤ ₚ) -> Mg^ k === M (g^ k)
  --     semi-MS : Mg S === S^ (g * g) Mg
      
  --   conjugation:
  --     conj-H-X : H X H⁻¹ === Z ⇔ H X === Z H
  --     conj-H-Z : H Z === X⁻¹ H
  --     conj-S-X : S X === X Z S
  --     conj-S-Z : S Z === Z S

  -- NOTE: S in Sp(2,p) is Z⁻¹S in Clifford.


