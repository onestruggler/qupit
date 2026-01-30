{-# OPTIONS --safe #-}
open import Level using (0ℓ)

open import Relation.Binary using (Rel)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Binary.Morphism.Definitions using (Homomorphic₂)
open import Relation.Binary.PropositionalEquality using (_≡_ ; inspect ; setoid ; module ≡-Reasoning) renaming ([_] to [_]')
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

open import Word.Base hiding (wfoldl ; _*)
open import Word.Properties
import Presentation.Base as PB
import Presentation.Properties as PP
open PP using (NFProperty ; NFProperty')
import Presentation.CosetNF as CA
import Presentation.Reidemeister-Schreier as RS
module RSF = RS.Star-Injective-Full.Reidemeister-Schreier-Full

open import Presentation.Construct.Base hiding (_*_)
import Presentation.Construct.Properties.SemiDirectProduct2 as SDP2
import Presentation.Construct.Properties.DirectProduct as DP
import Presentation.Groups.Cyclic as Cyclic


open import Data.Fin.Properties using (suc-injective ; toℕ-inject₁ ; toℕ-fromℕ)
import Data.Nat.Properties as NP
open import Presentation.GroupLike

module One.Symplectic where

pattern auto = Eq.refl

module Symplectic where

  data Gen : Set where
    H-gen : Gen
    S-gen : Gen

  H : Word Gen
  H = [ H-gen ]ʷ

  HH : Word Gen
  HH = H • H

  S : Word Gen
  S = [ S-gen ]ʷ

  S' : Word Gen
  S' = HH • S • HH

  SS : Word Gen
  SS = S • S

  X : Word Gen
  X = H • S • HH • SS • H

  Z : Word Gen
  Z = HH • S • HH • SS

  infix 4 _===_
  data _===_ : WRel Gen where
    order-S : S ^ 3 === ε
    order-H : H ^ 4 === ε
    order-SH : (S • H) ^ 3 === ε
    
    comm-HHS : H • H • S === S • H • H



open import Data.Nat.Primality
open import Data.Nat.Coprimality hiding (sym)
open import Data.Nat.GCD
open Bézout
open import Data.Empty
open import Algebra.Properties.Group

pattern ₀ = zero
pattern ₁ = suc ₀
pattern ₂ = suc ₁
pattern ₃ = suc ₂

pattern ₁₊ n = suc n
pattern ₂₊ n = suc (suc n)
pattern ₃₊ n = suc (₂₊ n)
pattern ₄₊ n = suc (₃₊ n)

module Symℕ (p : ℕ) where

  data Gen : Set where
    H-gen : ℕ -> Gen
    S-gen : ℕ -> Gen

  H^ : ℕ -> Word Gen
  H^ k = [ H-gen k ]ʷ

  S^ : ℕ -> Word Gen
  S^ k = [ S-gen k ]ʷ

  H : Word Gen
  H = [ H-gen 1 ]ʷ

  HH : Word Gen
  HH = H • H

  S : Word Gen
  S = [ S-gen 1 ]ʷ

  S' : Word Gen
  S' = HH • S • HH

  SS : Word Gen
  SS = S • S

  X : Word Gen
  X = H • S • HH • SS • H

  Z : Word Gen
  Z = HH • S • HH • SS

  infix 4 _===_
  data _===_ : WRel Gen where
    order-S : S ^ p === ε
    order-H : H ^ 4 === ε
    order-SH : (S • H) ^ 3 === ε
    
    comm-HHS : H • H • S === S • H • H

module NF1 (p-2 : ℕ) (p-prime : Prime (₂₊ p-2)) where

  open import Zp.ModularArithmetic using (ℤ ; ℤ* ; module PrimeModulus)
  open PrimeModulus p-2 p-prime hiding (p ; 0ₚ ; 1ₚ ; 0ₚ≢1ₚ)
  open Symℕ ₚ
  
  data C1 : Set where
    ε : C1
    HS : ℤ ₚ -> C1

  data Multiplier : Set where
    M : (x : ℤ* ₚ) -> Multiplier

  data Sᵏ : Set where
    𝕊 : ℤ ₚ -> Sᵏ

  data NF1 : Set where
    _∙_∙_ : Sᵏ -> Multiplier -> C1 -> NF1

  ⟦_⟧₁ : C1 -> Word Gen
  ⟦ ε ⟧₁ = ε
  ⟦ HS x ⟧₁ = H • S ^ toℕ x

  ⟦_⟧↥ : Sᵏ -> Word Gen
  ⟦ 𝕊 x ⟧↥ = S ^ toℕ x

  Mz : ℤ* ₚ -> Word Gen
  Mz x' = S^ x • H • S^ x⁻¹ • H • S^ x • H
    where
    x = toℕ (x' .proj₁)
    x⁻¹ = toℕ ((x' ⁻¹) .proj₁ )
    
  ⟦_⟧ₘ : Multiplier -> Word Gen
  ⟦ M x' ⟧ₘ = Mz x' -- S ^ x • H • S ^ x⁻¹ • H • S ^ x • H
    where
    x = toℕ (x' .proj₁)
    x⁻¹ = toℕ ((x' ⁻¹) .proj₁ )

  ⟦_⟧ : NF1 -> Word Gen
  ⟦ s ∙ m ∙ c ⟧ = ⟦ s ⟧↥ • ⟦ m ⟧ₘ • ⟦ c ⟧₁

  open import Data.Integer as Int hiding (_^_)
  Pauli1 = Int.ℤ × Int.ℤ
  
  -- mod p equality
  p = + (₂₊ p-2)
  𝕡 = + (₂₊ p-2)
  infix 4 _≈ₚ_
  _≈ₚ_ : Pauli1 -> Pauli1 -> Set
  _≈ₚ_ (a , b) (c , d) = a % p ≡ c % p × b % p ≡ d % p

  open import Relation.Binary.Definitions
  reflₚ  : Reflexive _≈ₚ_
  reflₚ  = auto , auto
  symₚ   : Symmetric _≈ₚ_
  symₚ   (eql , eqr) = (Eq.sym eql) , (Eq.sym eqr)
  transₚ : Transitive _≈ₚ_
  transₚ (eql1 , eqr1) (eql2 , eqr2) = (Eq.trans eql1 eql2) , (Eq.trans eqr1 eqr2)
  
  open import Relation.Binary.Structures
  isEquivalenceₚ : IsEquivalence _≈ₚ_
  isEquivalenceₚ = record { refl = auto , auto ; sym = λ { (eql , eqr) → (Eq.sym eql) , (Eq.sym eqr)} ; trans = λ {(eql1 , eqr1) (eql2 , eqr2) → (Eq.trans eql1 eql2) , (Eq.trans eqr1 eqr2)} }

  open import Relation.Binary.Bundles
  
  Pauli1-setoid : Setoid 0ℓ 0ℓ
  Pauli1-setoid = record { Carrier = Pauli1 ; _≈_ = _≈ₚ_ ; isEquivalence = isEquivalenceₚ }

  norm1 : Pauli1 → Pauli1 → Int.ℤ
  norm1 (a , b) (c , d) = (- a) * d + c * b

  norm1-antisym : ∀ (p q : Pauli1) -> norm1 p q ≡ - norm1 q p
  norm1-antisym p@(a , b) q@(c , d) = begin
    norm1 (a , b) (c , d) ≡⟨ auto ⟩
    (- a) * d + c * b ≡⟨ solve (a ∷ b ∷ c ∷ d ∷ []) ⟩
    - ((- c) * b + a * d) ≡⟨ auto ⟩
    - norm1 (c , d) (a , b) ∎
    where
    open import Data.Integer.Tactic.RingSolver
    open ≡-Reasoning

  act1 : Gen → Pauli1 → Pauli1
  act1 (H-gen 0) (a , b) = (a , b)
  act1 (H-gen 1) (a , b) = ((- b , a))
  act1 (H-gen 2) (a , b) = ((- a , - b))
  act1 (H-gen 3) (a , b) = ((b , - a))
  act1 (H-gen (₄₊ k)) (a , b) = act1 (H-gen k) (a , b)
  act1 (S-gen k) (a , b) = ((a , b + a * + k))

  act : Word Gen → Pauli1 → Pauli1
  act = word-act act1

  pI : Pauli1
  pI = (+0 , +0)

  pZ : Pauli1
  pZ = (+0 , 1ℤ)

  pX : Pauli1
  pX = (1ℤ , +0)

  0ₚ = +0 % 𝕡
  1ₚ = 1ℤ % 𝕡

  open Eq
  0ₚ≢1ₚ : 0ₚ ≢ 1ₚ
  0ₚ≢1ₚ ()

  0≢1 : 0 ≢ 1
  0≢1 ()

  0≢1+n : ∀ n -> 0 ≢ ₁₊ n
  0≢1+n n ()


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


  lemma-Mz : ∀ a b x' ->
    let x = toℕ (x' .proj₁) in
    let x⁻¹ = toℕ ((x' ⁻¹) .proj₁) in
    act (Mz x') (a , b) ≈ₚ (a * + x⁻¹ , b * + x)
  lemma-Mz a b x' = begin
    act (Mz x') (a , b) ≈⟨ auto , auto ⟩
    act (S^ x • H • S^ x⁻¹ • H • S^ x • H) (a , b) ≈⟨ auto , auto ⟩
    act (S^ x • H • S^ x⁻¹ • H • S^ x) (- b , a) ≈⟨ auto , auto ⟩
    act (S^ x • H • S^ x⁻¹ • H) (- b , a + (- b) * +x) ≈⟨ auto , auto ⟩
    act (S^ x • H • S^ x⁻¹) ( - (a + (- b) * +x) , - b) ≈⟨ auto , auto ⟩
    act (S^ x • H) ( - (a + (- b) * +x) , - b + (- (a + (- b) * +x)) * (+x⁻¹)) ≈⟨ auto , auto ⟩
    act (S^ x) ( - (- b + (- (a + (- b) * +x)) * (+x⁻¹)) , - (a + (- b) * +x) ) ≈⟨ auto , auto ⟩
    ( - (- b + (- (a + (- b) * +x)) * (+x⁻¹)) , - (a + (- b) * +x) + (- (- b + (- (a + (- b) * +x)) * (+x⁻¹))) * (+x)) ≡⟨ ≡×≡⇒≡ (aux1 +x +x⁻¹ , aux2 +x +x⁻¹) ⟩
    (b + a * +x⁻¹) + (- b) * (+x * +x⁻¹) , - a + + 2 * b * +x + (a + (- b) * +x) * (+x⁻¹ * +x) ≈⟨ cong (\ □ -> (b + a * +x⁻¹ + - b * □) % p) {!+x*+x⁻¹=+1!} , {!!} ⟩
--    (b + a * +x⁻¹) % p + (- b) * (+x * +x⁻¹) % p , - a + + 2 * b * +x + (a + (- b) * +x) * (+x⁻¹ * +x) ≈⟨ cong (\ □ -> (b + a * +x⁻¹ + - b * □) % p) {!+x*+x⁻¹=+1!} , {!!} ⟩
    b + a * +x⁻¹ + (- b) * + 1 , - a + + 2 * b * +x + (a + (- b) * +x) * + 1 ≡⟨ ≡×≡⇒≡ (aux4 +x⁻¹ , aux3 +x) ⟩
    (a * +x⁻¹ , b * +x) ∎
    where
    open SR Pauli1-setoid
    x = toℕ (x' .proj₁)
    x⁻¹ = toℕ ((x' ⁻¹) .proj₁ )
    +x = + x
    +x⁻¹ = + x⁻¹
    aux1 : ∀ +x +x⁻¹ -> - (- b + (- (a + (- b) * +x)) * (+x⁻¹)) ≡ (b + a * +x⁻¹) + (- b) * (+x * +x⁻¹)
    aux1 +x +x⁻¹ = solve (b ∷ a ∷ +x⁻¹ ∷ +x ∷ [])
    aux2 : ∀ +x +x⁻¹ ->
      - (a + (- b) * +x) + (- (- b + (- (a + (- b) * +x)) * (+x⁻¹))) * (+x) ≡
      - a + + 2 * b * +x + (a + (- b) * +x) * (+x⁻¹ * +x)
    aux2 +x +x⁻¹ = solve (b ∷ a ∷ +x⁻¹ ∷ +x ∷ [])
    aux3 : ∀ +x -> - a + + 2 * b * +x + (a + (- b) * +x) * + 1 ≡ b * +x
    aux3 +x = solve (b ∷ a ∷ +x ∷ [])
    aux4 : ∀ +x⁻¹ -> b + a * +x⁻¹ + (- b) * + 1 ≡ a * +x⁻¹
    aux4 +x⁻¹ = solve (b ∷ a ∷ +x⁻¹ ∷ [])
    

  aux1 : ∀ (p : Pauli1) -> norm1 pI p ≡ +0
  aux1 (c , d) = begin
    norm1 pI (c , d) ≡⟨ auto ⟩
    (+0) * d + c * +0 ≡⟨ solve (d ∷ c ∷ []) ⟩
    +0 ∎
    where open ≡-Reasoning

  aux2 : ∀ b c d -> norm1 (+0 , b) (c , d) ≡ b * c
  aux2 b c d = begin
    norm1 (+0 , b) (c , d) ≡⟨ auto ⟩
    (- +0) * d + c * b ≡⟨ solve (b ∷ c ∷ d ∷ []) ⟩
    b * c ∎
    where open ≡-Reasoning

  aux3 : ∀ k c p -> (k * p) * c ≡ (k * c) * p
  aux3 = solve-∀
    where open ≡-Reasoning

  aux4 : ∀ b k c p -> b ≡ k * p -> b * c ≡ (k * c) * p
  aux4 b k c p eq = begin
    b * c ≡⟨ cong (_* c) eq ⟩
    k * p * c ≡⟨ solve (k ∷ p ∷ c ∷ []) ⟩
    (k * c) * p ∎
    where open ≡-Reasoning

  aux6 : ∀ k p-2 -> let p = + (₂₊ p-2) in (k * p) % p ≡ 0
  aux6 (+_ ₀) p-2 = auto
  aux6 +[1+ n ] p-2 = let p = + (₂₊ p-2) in m*n%n≡0 (₁₊ n)  ∣ p ∣
  aux6 k@(-[1+ n ]) p-2 with ((Nat.suc n) Nat.* (₂₊ p-2)) Nat.% (₂₊ p-2) | inspect ( Nat._% (₂₊ p-2)) ((Nat.suc n) Nat.* (₂₊ p-2))
  ... | ₀ | [ eqh ]' = auto
  ... | ₁₊ hyp | [ eqh ]' with 0≢1+n hyp (trans (Eq.sym (m*n%n≡0 ((Nat.suc n) ) ((₂₊ p-2)))) eqh)
  ... | ()

  
  negnegb=b : ∀ b -> - (- b) ≡ b
  negnegb=b = solve-∀
    where open ≡-Reasoning

--  n∣d⇒n%d≡0 : ∀ n d 

  Theorem-NF :

    ∀ (p q : Pauli1) ->
    norm1 p q % 𝕡 ≡ 1 ->
    -------------------------------
    ∃ \ nf -> act ⟦ nf ⟧ p ≡ pZ ×
              act ⟦ nf ⟧ q ≡ pX

  Theorem-NF p@((+0 , +0)) q@(q1) eq with 0≢1 (Eq.trans (Eq.sym (Eq.cong (_% 𝕡) (aux1 q))) (eq))
  ... | ()
  Theorem-NF p@(a@(+ 0) , b@(+[1+ n₁ ])) q@(c , d) eq = nf , {!!}
    where
    open ≡-Reasoning
    -b = - b
    b' = fromℕ< (n%d<d -b 𝕡)
    c1 : b' ≢ ₀
    c1 eq0 = 0≢1 (trans (sym bc=0) bc=1)
      where
      -b%p=0 : -b % 𝕡 ≡ 0
      -b%p=0 = fromℕ<-injective (-b % 𝕡) 0 (n%d<d -b 𝕡) (s≤s z≤n) eq0
      
      c2 : -b ≡ -b / 𝕡 * 𝕡
      c2 = begin
        -b ≡⟨ a≡a%n+[a/n]*n -b 𝕡 ⟩
        + (-b % 𝕡) + -b / 𝕡 * 𝕡 ≡⟨ cong (_+ -b / 𝕡 * 𝕡) (Eq.cong +_ -b%p=0) ⟩
        + 0 + -b / 𝕡 * 𝕡 ≡⟨ +-identityˡ (-b / 𝕡 * 𝕡) ⟩
        -b / 𝕡 * 𝕡 ∎

      p|-b : 𝕡 ∣ -b
      p|-b = divides (-b / 𝕡) c2

      c3 : b ≡ -(-b / 𝕡) * 𝕡
      c3 = begin
        b ≡⟨ Eq.sym (negnegb=b b) ⟩
        -(-b) ≡⟨ Eq.cong -_ c2 ⟩
        -(-b / 𝕡 * 𝕡) ≡⟨ neg-distribˡ-* (-b / 𝕡) 𝕡 ⟩
        -(-b / 𝕡) * 𝕡 ∎

      c3' : b * c ≡ -(-b / 𝕡) * c * 𝕡
      c3' = aux4 b (-(-b / 𝕡)) c 𝕡 c3

      bc=0 : (b * c) % 𝕡 ≡ 0
      bc=0 = begin
        (b * c) % 𝕡 ≡⟨ cong (_% 𝕡) c3' ⟩
        (-(-b / 𝕡) * c * 𝕡) % 𝕡 ≡⟨ aux6 (-(-b / 𝕡) * c) p-2 ⟩
        0 ∎

      bc=1 : (b * c) % 𝕡 ≡ 1
      bc=1 = begin
        (b * c) % 𝕡 ≡⟨ cong (_% 𝕡) (sym (aux2 b c d)) ⟩
        (norm1 p q) % 𝕡 ≡⟨ eq ⟩
        1 ∎

      p|b : 𝕡 ∣ b
      p|b = divides (-(-b / 𝕡)) c3

    nf = (𝕊 b' ∙ M (b' , c1) ∙ ε)

    claim1 : act ⟦ nf ⟧ p ≡ pZ
    claim1 = begin
      act ⟦ nf ⟧ (+0 , b) ≡⟨ auto ⟩
      act (S ^ toℕ b' • Mz (b' , c1) • ε) (+0 , b) ≡⟨ auto ⟩
      act (S ^ toℕ b' • Mz (b' , c1)) (+0 , b) ≡⟨ {!!} ⟩
      pZ ∎


      
  Theorem-NF (a@(+ 0) , b@(-[1+ n₁ ])) (c , d) eq = {!∣!}
    where
    b' = fromℕ< (n%d<d (- b) 𝕡)
  Theorem-NF (a@(+[1+ n ]) , b@(+ ₀)) (c , d) eq = {!!}
  Theorem-NF (a@(+[1+ n ]) , b@(+[1+ n₁ ])) (c , d) eq = {!!}
  Theorem-NF (+[1+ n ] , -[1+_] n₁) (c , d) eq = {!!}
  Theorem-NF (-[1+_] n , +_ n₁) (c , d) eq = {!!}
  Theorem-NF (-[1+_] n , -[1+_] n₁) (c , d) eq = {!!}


{-
-- ----------------------------------------------------------------------
-- * Data required for applying word tactics to Symplectic generators

module CommData where

  open Symplectic
  open PB _===_
  
  -- Commutativity.
  comm~ : (x y : Gen) -> Maybe (([ x ]ʷ • [ y ]ʷ) ≈ ([ y ]ʷ • [ x ]ʷ))
  comm~ _ _ = nothing


  -- We number the generators for the purpose of ordering them.
  ord : Gen -> ℕ
  ord S-gen = 1
  ord H-gen = 2

  -- Ordering of generators.
  les : Gen -> Gen -> Bool
  les x y with ord x Nat.<? ord y
  les x y | yes _ = true
  les x y | no _ = false

open import Presentation.Tactics hiding ([_])
module Commuting-Symplectic = Commuting Symplectic._===_ CommData.comm~ CommData.les

-- ----------------------------------------------------------------------
-- * Lemmas

module Symplectic-Powers where

  -- This module provides a rewrite system for reducing powers of
  -- Symplectic operators (for example, S⁴ → I). It also commutes
  -- generators on different qubits (for example, H1 H0 → H0 H1).
  -- Finally, it moves scalars to the end of the word. While this is
  -- not yet a very powerful rewrite system, it is a useful
  -- bootstrapping step.

  open Symplectic
  open Rewriting
  
  open PB _===_ hiding (_===_)

  -- ----------------------------------------------------------------------
  -- * Lemmas

  -- The following lemmas are needed to justify the rewrite steps.

  -- ----------------------------------------------------------------------
  -- * Rewrite rules for monoidal structure and order of generators

  step-order : Step-Function Gen _===_

  -- Order of generators.
  step-order (S-gen ∷ S-gen ∷ S-gen ∷ xs) = just (xs , at-head (axiom order-S))
  step-order (H-gen ∷ H-gen ∷ H-gen ∷ H-gen ∷ xs) = just (xs , at-head (axiom order-H))

  -- Commuting of generators.

  -- Catch-all
  step-order _ = nothing

  -- From this rewrite relation, we extract a tactic 'general-powers'.
  open Rewriting.Step (step-cong step-order) renaming (general-rewrite to general-powers) public


module Symplectic-Rewriting1 where

  -- This module provides a complete rewrite system for 1-qubit
  -- Symplectic operators. It is specialized toward relations on qubit 0
  -- (but can also be applied to qubit 1 via duality).

  open Commuting-Symplectic
  open Rewriting
  open Symplectic
  open Symplectic-Powers

  open PB _===_ hiding (_===_)
  open PP _===_
  open SR word-setoid


  -- ----------------------------------------------------------------------
  -- * Rewrite rules for 1-qubit Symplectic relations
  
  step-symplectic1 : Step-Function Gen _===_

  -- Rules for unary gates.
  -- Order of generators.
  step-symplectic1 (S-gen ∷ S-gen ∷ S-gen ∷ xs) = just (xs , at-head (axiom order-S))
  step-symplectic1 (H-gen ∷ H-gen ∷ H-gen ∷ H-gen ∷ xs) = just (xs , at-head (axiom order-H))
  step-symplectic1 (S-gen ∷ H-gen ∷ S-gen ∷ H-gen ∷ S-gen ∷ H-gen ∷ xs) = just (xs , at-head (axiom order-SH))
  
  step-symplectic1 (H-gen ∷ H-gen ∷ S-gen ∷ xs) = just (S-gen ∷ H-gen ∷ H-gen ∷ xs , at-head (axiom comm-HHS))

  -- Catch-all
  step-symplectic1 _ = nothing

  -- From this rewrite relation, we extract a tactic 'rewrite-symplectic1'.
  open Rewriting.Step (step-cong step-order then step-cong step-symplectic1) renaming (general-rewrite to rewrite-symplectic1) public

module Symplectic-Lemmas where

  open Symplectic
  open PP _===_
  open PB _===_ hiding (_===_)
  open SR word-setoid
  open Symplectic-Powers
  
  lemma-comm-HHSHHS : H • H • S • H • H • S ≈ S • H • H • S • H • H
  lemma-comm-HHSHHS = begin
    H • H • S • H • H • S ≈⟨ by-assoc auto ⟩
    (H • H • S) • (H • H • S) ≈⟨ cong (axiom comm-HHS) (axiom comm-HHS) ⟩
    (S • H • H) • (S • H • H) ≈⟨ by-assoc auto ⟩
    S • H • H • S • H • H ∎
    
  lemma-order-Z : Z ^ 2 • Z ≈ ε
  lemma-order-Z = begin
    Z ^ 2 • Z ≈⟨ by-assoc auto ⟩
    (H • H • S • H • H • S) • (S • H • H • S • H • H) • S ^ 2 • (H • H • S • H • H • S) • S ≈⟨ cong (lemma-comm-HHSHHS) (_≈_.cong (_≈_.sym (lemma-comm-HHSHHS)) _≈_.refl) ⟩
    (S • H • H • S • H • H) • (H • H • S • H • H • S) • S ^ 2 • (H • H • S • H • H • S) • S ≈⟨ by-assoc auto ⟩
    (S • H • H • S) • H ^ 4 • (S • H • H) • S ^ 3 • (H • H • S • H • H • S) • S ≈⟨ cong _≈_.refl (cong (_≈_.axiom order-H) (_≈_.cong _≈_.refl (_≈_.cong (_≈_.axiom order-S) _≈_.refl))) ⟩
    (S • H • H • S) • ε • (S • H • H) • ε • (H • H • S • H • H • S) • S ≈⟨ by-assoc auto ⟩
    (S • H • H • S • S) • H ^ 4 • S • H • H • S • S ≈⟨ _≈_.cong _≈_.refl (_≈_.cong (_≈_.axiom order-H) _≈_.refl) ⟩
    (S • H • H • S • S) • ε • S • H • H • S • S ≈⟨ by-assoc auto ⟩
    (S • H • H) • S ^ 3 • H • H • S • S ≈⟨ _≈_.cong _≈_.refl (_≈_.cong (_≈_.axiom order-S) _≈_.refl) ⟩
    (S • H • H) • ε • H • H • S • S ≈⟨ by-assoc auto ⟩
    S • H ^ 4 • S • S ≈⟨ _≈_.cong _≈_.refl (_≈_.cong (_≈_.axiom order-H) _≈_.refl) ⟩
    S • ε • S • S ≈⟨ _≈_.trans (_≈_.cong _≈_.refl _≈_.left-unit) (_≈_.axiom order-S) ⟩
    ε ∎

  lemma-order-X : X ^ 2 • X ≈ ε
  lemma-order-X = begin
    X ^ 2 • X ≈⟨ by-assoc auto ⟩
    (H • S • HH • S) • (S • H • H • S • H • H) • S ^ 2 • H • H • S • H • H • SS • H ≈⟨ cong refl (_≈_.cong (_≈_.sym (lemma-comm-HHSHHS)) _≈_.refl) ⟩
    (H • S • HH • S) • (H • H • S • H • H • S) • S ^ 2 • H • H • S • H • H • SS • H ≈⟨ by-assoc auto ⟩
    (H • S • HH • S • H • H • S • H • H) • S ^ 3 • H • H • S • H • H • SS • H ≈⟨ _≈_.cong _≈_.refl (_≈_.cong (_≈_.axiom order-S) _≈_.refl) ⟩
    (H • S • HH • S • H • H • S • H • H) • ε • H • H • S • H • H • SS • H ≈⟨ by-assoc auto ⟩
    (H • S • HH • S • H • H • S) • H ^ 4 • S • H • H • SS • H ≈⟨ _≈_.cong _≈_.refl (_≈_.cong (_≈_.axiom order-H) _≈_.refl) ⟩
    (H • S • HH • S • H • H • S) • ε • S • H • H • SS • H ≈⟨ by-assoc auto ⟩
    H • (S • H • H • S • H • H) • S ^ 2 • H • H • SS • H ≈⟨ cong refl (_≈_.cong (_≈_.sym (lemma-comm-HHSHHS)) _≈_.refl) ⟩
    H • (H • H • S • H • H • S) • S ^ 2 • H • H • SS • H ≈⟨ by-assoc auto ⟩
    (H • H • H • S • H • H) • S ^ 3 • H • H • SS • H ≈⟨ _≈_.cong _≈_.refl (_≈_.cong (_≈_.axiom order-S) _≈_.refl) ⟩
    (H • H • H • S • H • H) • ε • H • H • SS • H ≈⟨ by-assoc auto ⟩
    (H • H • H • S) • H ^ 4 • SS • H ≈⟨ _≈_.cong _≈_.refl (_≈_.cong (_≈_.axiom order-H) _≈_.refl) ⟩
    (H • H • H • S) • ε • SS • H ≈⟨ by-assoc auto ⟩
    (H • H • H) • S ^ 3 • H ≈⟨ _≈_.cong _≈_.refl (_≈_.cong (_≈_.axiom order-S) _≈_.refl) ⟩
    (H • H • H) • ε • H ≈⟨ by-assoc auto ⟩
    H • H • H • H ≈⟨ _≈_.axiom order-H ⟩
    ε ∎

  lemma-comm-Z-S : Z • S ≈ S • Z
  lemma-comm-Z-S = begin
    Z • S ≈⟨ by-assoc auto ⟩
    (H • H • S • H • H • S) • S • S ≈⟨ _≈_.cong (lemma-comm-HHSHHS) _≈_.refl ⟩
    (S • H • H • S • H • H) • S • S ≈⟨ by-assoc auto ⟩
    S • Z ∎

  lemma-SH^2 : (S • H) ^ 2 ≈ H ^ 3 • S ^ 2
  lemma-SH^2 = begin
    (S • H) ^ 2 ≈⟨ by-assoc auto ⟩
    (S • H • S • H) • ε ≈⟨ _≈_.sym (_≈_.cong _≈_.refl (_≈_.axiom order-S)) ⟩
    (S • H • S • H) • S ^ 3 ≈⟨ by-assoc auto ⟩
    (S • H • S • H • S) • ε • S ^ 2 ≈⟨ cong refl (_≈_.sym (_≈_.cong (_≈_.axiom order-H) _≈_.refl)) ⟩
    (S • H • S • H • S) • H ^ 4 • S ^ 2 ≈⟨ by-assoc auto ⟩
    (S • H) ^ 3 • H ^ 3 • S ^ 2 ≈⟨ cong (_≈_.axiom order-SH) refl ⟩
    ε • H ^ 3 • S ^ 2 ≈⟨ left-unit ⟩
    H ^ 3 • S ^ 2 ∎

  lemma-comm-HHSSHHS : H • H • S • S • H • H • S ≈ S • H • H • S • S • H • H
  lemma-comm-HHSSHHS = begin
    H • H • S • S • H • H • S ≈⟨ by-assoc Eq.refl ⟩
    (H • H • S) • S • H • H • S ≈⟨ cong refl (trans (sym left-unit) (sym (cong (axiom order-H) refl))) ⟩
    (H • H • S) • H ^ 4 • S • H • H • S ≈⟨ by-assoc Eq.refl ⟩
    (H • H • S • H  • H) • (H • H • S • H • H • S) ≈⟨ cong refl (lemma-comm-HHSHHS) ⟩
    (H • H • S • H  • H) • S • (H • H • S • H • H) ≈⟨ by-assoc Eq.refl ⟩
    (H • H • S • H  • H • S) • (H • H • S • H • H) ≈⟨ cong (lemma-comm-HHSHHS) refl ⟩
    (S • (H • H • S • H • H)) • (H • H • S • H • H) ≈⟨ by-assoc Eq.refl ⟩
    (S • H • H • S) • H ^ 4 • S • H • H ≈⟨ cong refl (cong (axiom order-H) refl) ⟩
    (S • H • H • S) • ε • S • H • H ≈⟨ by-assoc Eq.refl ⟩
    S • H • H • S • S • H • H ∎

  lemma-comm-HHSSHHSS : H ^ 2 • S ^ 2 • H ^ 2 • S ^ 2 ≈ S ^ 2 • H ^ 2 • S ^ 2 • H ^ 2
  lemma-comm-HHSSHHSS = begin
    H ^ 2 • S ^ 2 • H ^ 2 • S ^ 2 ≈⟨ by-assoc auto ⟩
    (H • H • S • S • H • H • S) • S ≈⟨ cong lemma-comm-HHSSHHS refl ⟩
    (S • H • H • S • S • H • H) • S ≈⟨ by-assoc auto ⟩
    S • (H • H • S • S • H • H • S) ≈⟨ cong refl lemma-comm-HHSSHHS ⟩
    S • (S • H • H • S • S • H • H) ≈⟨ by-assoc auto ⟩
    S ^ 2 • H ^ 2 • S ^ 2 • H ^ 2 ∎


  lemma-conj-HH-Z : HH • Z ≈ (Z • Z) • HH
  lemma-conj-HH-Z = begin
    HH • HH • S • HH • SS ≈⟨ by-assoc auto ⟩
    H ^ 4 • S • HH • SS ≈⟨ _≈_.trans (_≈_.cong (_≈_.axiom order-H) _≈_.refl) _≈_.left-unit ⟩
    S • HH • SS ≈⟨ by-assoc auto ⟩
    (ε • ε) • (S • H • H • S • S) • ε ≈⟨ cong (_≈_.sym (_≈_.cong (_≈_.axiom order-H) (_≈_.axiom order-S))) (_≈_.sym (_≈_.cong _≈_.refl (_≈_.axiom order-H))) ⟩
    (H ^ 4 • S ^ 3) • (S • H • H • S • S) • H ^ 4 ≈⟨ by-assoc auto ⟩
    (H ^ 4 • S ^ 3) • (S • H • H • S • S • H • H) • HH ≈⟨ cong refl (cong (_≈_.sym lemma-comm-HHSSHHS) refl) ⟩
    (H ^ 4 • S ^ 3) • (H • H • S • S • H • H • S) • HH ≈⟨ by-assoc auto ⟩
    (H ^ 4 • S • S) • (S • H • H • S • S • H • H) • S • HH ≈⟨ cong refl (cong (_≈_.sym lemma-comm-HHSSHHS) refl) ⟩
    (H ^ 4 • S • S) • (H • H • S • S • H • H • S) • S • HH ≈⟨ by-assoc auto ⟩
    HH • (H • H • S • S • H • H • S) • S • HH • SS • HH ≈⟨ cong refl (cong lemma-comm-HHSSHHS refl) ⟩
    HH • (S • H • H • S • S • H • H) • S • HH • SS • HH ≈⟨ by-assoc auto ⟩
    (Z • Z) • HH ∎


  lemma-def-XX : X • X ≈ (H • S • S • H) • (H • S • H)
  lemma-def-XX = begin
    X • X ≈⟨ by-assoc auto ⟩
    (H • S) • (H • H • S • S • H • H • S) • H • H • S • S • H ≈⟨ cong refl (cong lemma-comm-HHSSHHS refl) ⟩
    (H • S) • (S • H • H • S • S • H • H) • H • H • S • S • H ≈⟨ by-assoc Eq.refl ⟩
    (H • S • S • H • H • S • S) • H ^ 4 • S • S • H ≈⟨ general-powers 100 auto ⟩
    (H • S • S • H) • (H • S • H) ∎

  lemma-def-ZZ : Z • Z ≈ (HH • S • S • HH) • S
  lemma-def-ZZ = begin
    (HH • S • HH • SS) • (HH • S • HH • SS) ≈⟨ by-assoc auto ⟩
    (HH • S • HH • S) • (S • H • H • S • H • H) • SS ≈⟨ cong refl (sym (cong (lemma-comm-HHSHHS) refl)) ⟩
    (HH • S • HH • S) • (H • H • S • H • H • S) • SS ≈⟨ by-assoc auto ⟩
    (HH • S • HH) • (S • H • H • S • H • H) • S ^ 3 ≈⟨ cong refl (cong (sym (lemma-comm-HHSHHS)) (axiom order-S)) ⟩
    (HH • S • HH) • (H • H • S • H • H • S) • ε ≈⟨ general-powers 100 auto ⟩
    (HH • S • S • HH) • S ∎

  lemma-conj-HH-X : HH • X ≈ (X • X) • HH
  lemma-conj-HH-X = begin
    HH • X ≈⟨ general-powers 100 auto ⟩
    H • (H • H • S • H • H • S) • S • H ≈⟨ cong refl (cong (lemma-comm-HHSHHS) refl) ⟩
    H • (S • H • H • S • H • H) • S • H ≈⟨ by-assoc auto ⟩
    (H • S) • (H • H • S • H • H • S) • H ≈⟨ cong refl (cong (lemma-comm-HHSHHS) refl) ⟩
    (H • S) • (S • H • H • S • H • H) • H ≈⟨ by-assoc auto ⟩
    ((H • S • S • H) • (H • S • H)) • HH ≈⟨ cong (sym lemma-def-XX) refl ⟩
    (X • X) • HH ∎

  lemma-conj-HH-S : HH • S ≈ (S • Z) • HH
  lemma-conj-HH-S = begin
    HH • S ≈⟨ general-powers 100 auto ⟩
    (S • HH) • (H • H • S • S • H • H • S) ≈⟨ cong refl lemma-comm-HHSSHHS ⟩
    (S • HH) • (S • H • H • S • S • H • H) ≈⟨ by-assoc auto ⟩
    (S • HH • S • HH • SS) • HH ∎

  lemma-SHS : S • H • S ≈ H ^ 3 • S ^ 2 • H ^ 3
  lemma-SHS = begin
    S • H • S ≈⟨ general-powers 100 auto ⟩
    (S • H) ^ 3 • H ^ 3 • S ^ 2 • H ^ 3 ≈⟨ cong (axiom order-SH) refl ⟩
    ε • H ^ 3 • S ^ 2 • H ^ 3 ≈⟨ left-unit ⟩
    H ^ 3 • S ^ 2 • H ^ 3 ∎

  lemma-SHSH : S • H • S • H ≈ H ^ 3 • S ^ 2
  lemma-SHSH = begin
    S • H • S • H ≈⟨ general-powers 100 auto ⟩
    (S • H) ^ 3 • H ^ 3 • S ^ 2 ≈⟨ trans (cong (axiom order-SH) refl) left-unit ⟩
    H ^ 3 • S ^ 2 ∎

  lemma-HSH : H • S • H ≈ S ^ 2 • H ^ 3 • S ^ 2
  lemma-HSH = begin
    H • S • H ≈⟨ general-powers 100 auto ⟩
    S ^ 2 • (S • H) ^ 3 • H ^ 3 • S ^ 2 ≈⟨ cong refl (cong (axiom order-SH) refl) ⟩
    S ^ 2 • ε • H ^ 3 • S ^ 2 ≈⟨ general-powers 100 auto ⟩
    S ^ 2 • H ^ 3 • S ^ 2 ∎

  lemma-HSHS : H • S • H • S ≈ S ^ 2 • H ^ 3
  lemma-HSHS = begin
    H • S • H • S ≈⟨ general-powers 100 auto ⟩
    S ^ 2 • (S • H) ^ 3 • H ^ 3 ≈⟨ cong refl (cong (axiom order-SH) refl) ⟩
    S ^ 2 • ε • H ^ 3 ≈⟨ general-powers 100 auto ⟩
    S ^ 2 • H ^ 3 ∎

  lemma-SHSHS : S • H • S • H • S ≈ H ^ 3
  lemma-SHSHS = begin
    S • H • S • H • S ≈⟨ general-powers 100 auto ⟩
    (S • H) ^ 3 • H ^ 3 ≈⟨ trans (cong (axiom order-SH) refl) left-unit ⟩
    H ^ 3 ∎

  lemma-HSHSH : H • S • H • S • H ≈ S ^ 2
  lemma-HSHSH = begin
    H • S • H • S • H ≈⟨ general-powers 100 auto ⟩
    S ^ 2 • (S • H) ^ 3 ≈⟨ cong refl (axiom order-SH) ⟩
    S ^ 2 • ε  ≈⟨ general-powers 100 auto ⟩
    S ^ 2 ∎

  lemma-SSH^6 : (S • S • H) ^ 6 ≈ ε
  lemma-SSH^6 = begin
    (S • S • H) ^ 6 ≈⟨ by-assoc auto ⟩
    S • (S • H • S) • (S • H • S) • (S • H • S) • (S • H • S) • (S • H • S) • S • H ≈⟨ cong refl (cong lemma-SHS (cong lemma-SHS (cong lemma-SHS (cong lemma-SHS (cong lemma-SHS refl))))) ⟩
    S • (H ^ 3 • S ^ 2 • H ^ 3) • (H ^ 3 • S ^ 2 • H ^ 3) • (H ^ 3 • S ^ 2 • H ^ 3) • (H ^ 3 • S ^ 2 • H ^ 3) • (H ^ 3 • S ^ 2 • H ^ 3) • S • H ≈⟨ general-powers 100 auto ⟩
    S • H • (H • H • S • S • H • H • S) • (S • H • H • S • S • H • H) • S • S • H • H • S • S • H ^ 3 • S • H ≈⟨ cong refl (cong refl (cong lemma-comm-HHSSHHS (cong (sym lemma-comm-HHSSHHS) refl))) ⟩
    S • H • (S • H • H • S • S • H • H) • (H • H • S • S • H • H • S) • S • S • H • H • S • S • H ^ 3 • S • H ≈⟨ general-powers 1000 auto ⟩
    (S • H) ^ 3 ≈⟨ axiom order-SH ⟩
    ε ∎

  lemma-SSH^3 : (S • S • H) ^ 3 ≈ (H ^ 3 • S) ^ 3
  lemma-SSH^3 = begin
    (S • S • H) ^ 3 ≈⟨ general-powers 100 auto ⟩
    (S • S • H) ^ 6 • (H ^ 3 • S) ^ 3 ≈⟨ cong lemma-SSH^6 refl ⟩
    ε • (H ^ 3 • S) ^ 3 ≈⟨ left-unit ⟩
    (H ^ 3 • S) ^ 3 ∎

  lemma-conj-XZXXZZ : X • Z • X ^ 2 • Z ^ 2 ≈ ε
  lemma-conj-XZXXZZ = begin
    X • Z • X ^ 2 • Z ^ 2 ≈⟨ cong refl (cong refl (cong lemma-def-XX lemma-def-ZZ)) ⟩
    (H • S • HH • SS • H) • (HH • S • HH • SS) • ((H • S • S • H) • (H • S • H)) • (HH • S • S • HH) • S ≈⟨ by-assoc auto ⟩
    (H • S • HH • SS • H • HH • S • HH • SS • H • S • S • H • H • S • H) • (H • H • S • S • H • H • S) ≈⟨ cong refl lemma-comm-HHSSHHS ⟩
    (H • S • HH • SS • H • HH • S • HH • SS • H • S • S • H • H • S • H) • (S • H • H • S • S • H • H) ≈⟨ by-assoc auto ⟩
    (H • S • HH • SS • H • HH • S • HH • SS • H • S • S • H) • (H • S • H • S • H) • H • S • S • H • H ≈⟨ cong refl (cong lemma-HSHSH refl) ⟩
    (H • S • HH • SS • H • HH • S • HH • SS • H • S • S • H) • (S • S) • H • S • S • H • H ≈⟨ general-powers 100 auto ⟩
    (H • S • HH • SS • H • HH • S • HH • SS • H) • (S • S • H) ^ 3 • H ≈⟨ cong refl (cong lemma-SSH^3 refl) ⟩
    (H • S • HH • SS • H • HH • S • HH • SS • H) • (H ^ 3 • S) ^ 3 • H ≈⟨ general-powers 100 auto ⟩
    (H • S • HH • SS • H • HH • S • H • S) • (H ^ 3 • S) • H ≈⟨ by-assoc auto ⟩
    (H • S • HH • SS • H • HH) • (S • H • S • H) • H ^ 2 • S • H ≈⟨ cong refl (cong lemma-SHSH refl) ⟩
    (H • S • HH • SS • H • HH) • (H ^ 3 • S ^ 2) • H ^ 2 • S • H ≈⟨ general-powers 100 auto ⟩
    H • (S • H • H • S • S • H • H) • S ^ 2 • H ^ 2 • S • H ≈⟨ cong refl (sym (cong lemma-comm-HHSSHHS refl)) ⟩
    H • (H • H • S • S • H • H • S) • S ^ 2 • H ^ 2 • S • H ≈⟨  general-powers 100 auto ⟩
    ε ∎

  lemma-conj-X-S : X • S ≈ (S • Z • Z) • X
  lemma-conj-X-S = begin
    X • S ≈⟨ by-assoc auto ⟩
    H • (S • H • H • S • S • H • S) ≈⟨ general-powers 100 auto ⟩
    H • (S • H • H • S • S • H • H) • (H ^ 3 • S) ≈⟨ cong refl (sym (cong lemma-comm-HHSSHHS refl)) ⟩
    H • (H • H • S • S • H • H • S) • (H ^ 3 • S) ≈⟨ general-powers 100 auto ⟩
    (H ^ 3 • S ^ 2) • H ^ 2 • S • (H ^ 3 • S) ≈⟨ (sym (cong lemma-SHSH refl)) ⟩
    (S • H • S • H) • H ^ 2 • S • (H ^ 3 • S) ≈⟨ general-powers 100 auto ⟩
    (S • H • H) • (H ^ 3 • S) ^ 3 ≈⟨ cong refl (sym lemma-SSH^3) ⟩
    (S • H • H) • (S • S • H) ^ 3 ≈⟨ by-assoc auto ⟩
    S • H • H • S • S • H • S • S • H • S • S • H ≈⟨ by-assoc auto ⟩
    ε • S • H • H • S • S • H • S ^ 2 • H • SS • H ≈⟨ (sym (cong (axiom order-H) refl)) ⟩
    H ^ 4 • S • H • H • S • S • H • S ^ 2 • H • SS • H ≈⟨ by-assoc auto ⟩
    (H • H) • (H • H • S • H • H • S) • S • H • S ^ 2 • H • SS • H ≈⟨ cong refl (_≈_.cong (lemma-comm-HHSHHS) _≈_.refl) ⟩
    (H • H) • (S • H • H • S • H • H) • S • H • S ^ 2 • H • SS • H ≈⟨ by-assoc auto ⟩
    (H • H • S) • (H • H • S • H • H • S) • H • S ^ 2 • H • SS • H ≈⟨ cong refl (_≈_.cong (lemma-comm-HHSHHS) _≈_.refl) ⟩
    (H • H • S) • (S • H • H • S • H • H) • H • S ^ 2 • H • SS • H ≈⟨ by-assoc auto ⟩
    (H • H • SS • HH • S) • (H ^ 3 • S ^ 2) • H • SS • H ≈⟨ general-powers 100 auto ⟩
    (H • H • SS • HH • S) • (H ^ 3 • S ^ 2) • H • SS • H ≈⟨ cong refl (sym (cong lemma-SH^2 refl)) ⟩
    (H • H • SS • HH • S) • ((S • H) ^ 2) • H • SS • H ≈⟨ by-assoc auto ⟩
    (H • H • S) • ε • S • HH • SS • H • S • HH • SS • H ≈⟨ cong refl (_≈_.sym (_≈_.cong (_≈_.axiom order-H) _≈_.refl)) ⟩
    (H • H • S) • H ^ 4 • S • HH • SS • H • S • HH • SS • H ≈⟨ by-assoc auto ⟩
    (H • H • S • H • H) • ε • HH • S • HH • SS • H • S • HH • SS • H ≈⟨ cong refl (_≈_.sym (_≈_.cong (_≈_.axiom order-S) _≈_.refl)) ⟩
    (H • H • S • H • H) • S ^ 3 • HH • S • HH • SS • H • S • HH • SS • H ≈⟨ by-assoc auto ⟩
    (H • H • S • H • H • S) • SS • HH • S • HH • SS • H • S • HH • SS • H ≈⟨ (_≈_.cong (lemma-comm-HHSHHS) _≈_.refl) ⟩
    (S • H • H • S • H • H) • SS • HH • S • HH • SS • H • S • HH • SS • H ≈⟨ by-assoc auto ⟩
    S • HH • S • HH • SS • HH • S • HH • SS • H • S • HH • SS • H ≈⟨ by-assoc auto ⟩
    (S • Z • Z) • X ∎

  lemma-conj-X-Z : X • Z ≈ (Z) • X
  lemma-conj-X-Z = begin
    X • Z ≈⟨ by-assoc auto ⟩
    X • Z • ε ≈⟨ cong refl (sym (cong refl lemma-order-X)) ⟩
    X • Z • X ^ 2 • X ≈⟨ by-assoc auto ⟩
    (X • Z • X ^ 2) • ε • X ≈⟨ cong refl (cong (sym lemma-order-Z) refl) ⟩
    (X • Z • X ^ 2) • (Z ^ 2 • Z) • X ≈⟨ by-assoc auto ⟩
    ((X • Z • X ^ 2 • Z ^ 2) • Z) • X ≈⟨ cong (cong lemma-conj-XZXXZZ refl) refl ⟩
    (ε • Z) • X ≈⟨ trans assoc left-unit ⟩
    (Z) • X ∎

  lemma-X^3 : X ^ 3 ≈ ε
  lemma-X^3 = begin
    X ^ 3 ≈⟨ sym assoc ⟩
    X ^ 2 • X ≈⟨ lemma-order-X ⟩
    ε ∎

  lemma-HX : H • X ≈ Z • H
  lemma-HX = begin
    H • X ≈⟨ by-assoc auto ⟩
    Z • H ∎

  lemma-HSSH : (H • S • S) • H ≈ (S • Z • X • X) • H • S
  lemma-HSSH = begin
    (H • S • S) • H ≈⟨ general-powers 100 auto ⟩
    (H) • (S ^ 2) • H ≈⟨ cong refl (sym (cong lemma-HSHSH refl)) ⟩
    (H) • (H • S • H • S • H) • H ≈⟨ general-powers 100 auto ⟩
    (S • H • H) • (H • H • S • S • H • H • S) • H • S • H • H ≈⟨ cong refl (cong lemma-comm-HHSSHHS refl ) ⟩
    (S • H • H) • (S • H • H • S • S • H • H) • H • S • H • H ≈⟨ general-powers 100 auto ⟩
    (S) • (H • X) • H • H • S • H • H ≈⟨ cong refl (cong lemma-HX refl) ⟩
    (S) • (Z • H) • H • H • S • H • H ≈⟨ general-powers 100 auto ⟩
    (S • Z • H • S • S) • (S • H • H • S • H • H) ≈⟨ cong refl (sym (lemma-comm-HHSHHS)) ⟩
    (S • Z • H • S • S) • (H • H • S • H • H • S) ≈⟨ general-powers 100 auto ⟩
    (S • Z) • ((H • S • S • H) • (H • S • H)) • H • S ≈⟨ cong refl (cong (sym lemma-def-XX) refl) ⟩
    (S • Z) • (X • X) • H • S ≈⟨ by-assoc auto ⟩
    (S • Z • X • X) • H • S ∎


module PhaseX where

  Gen = Cyclic.X ⊎ Cyclic.X

  infix 4 _===_
  _===_ : WRel Gen
  _===_ = (Cyclic.pres 3 ⸲ Cyclic.pres 3 ⸲ Γₓ)

  pattern ω-gen = inj₁ tt
  pattern X-gen = inj₂ tt

  pattern order-ω = left Cyclic.order
  pattern order-X = right Cyclic.order
  pattern comm-X-ω = mid (comm tt tt)

  ω : Word Gen
  ω = [ ω-gen ]ʷ

  X : Word Gen
  X = [ X-gen ]ʷ

  nfp' : NFProperty' _===_
  nfp' = DP.NFP'.nfp' (Cyclic.pres 3) (Cyclic.pres 3) (Cyclic.nfp' 3) (Cyclic.nfp' 3)
  
module Z where

  Gen = Cyclic.X

  infix 4 _===_
  _===_ : WRel Gen
  _===_ = Cyclic.pres 3

  pattern Z-gen = tt
  pattern order-Z = Cyclic.order

  Z : Word Gen
  Z = [ Z-gen ]ʷ

  nfp' : NFProperty' _===_
  nfp' = Cyclic.nfp' 3

module PhaseXZ where

  Gen = PhaseX.Gen ⊎ Z.Gen
  
  pattern ω-gen = inj₁ PhaseX.ω-gen
  pattern X-gen = inj₁ PhaseX.X-gen
  pattern Z-gen = inj₂ tt
  
  ω : Word Gen
  ω = [ ω-gen ]ʷ
  Z : Word Gen
  Z = [ Z-gen ]ʷ
  X : Word Gen
  X = [ X-gen ]ʷ

  conj : Z.Gen -> PhaseX.Gen -> Word PhaseX.Gen
  conj Z.Z-gen PhaseX.X-gen = PhaseX.ω • PhaseX.X
  conj Z.Z-gen PhaseX.ω-gen = PhaseX.ω

  pattern order-ω = left PhaseX.order-ω
  pattern order-X = left PhaseX.order-X
  pattern comm-X-ω = left PhaseX.comm-X-ω
  pattern order-Z = right Z.order-Z
  pattern conj-Z-X = mid (comm PhaseX.X-gen tt)
  pattern comm-Z-ω = mid (comm PhaseX.ω-gen tt)

  infix 4 _===_
  _===_ : WRel Gen
  _===_ = (PhaseX._===_ ⸲ Z._===_ ⸲ Γⱼ' conj)
  
  open PB Z._===_ renaming (_===_ to _===₂_ ; _≈_ to _≈₂_) using ()
  open PP Z._===_ renaming (•-ε-monoid to m₂ ; word-setoid to ws₂) using ()
  
  open PB PhaseX._===_ renaming (_===_ to _===₁_ ; _≈_ to _≈₁_) using ()
  open PP PhaseX._===_ renaming (•-ε-monoid to m₁ ; word-setoid to ws₁ ; by-assoc-and to by-assoc-and₁ ; by-assoc to by-assoc₁) using ()

  open PB hiding (_===_)
  
  module SDP2A = SDP2 PhaseX._===_ Z._===_ conj

  pattern auto = Eq.refl
  open NFProperty' (PhaseX.nfp') renaming (by-equal-nf to by-equal-nf₁)

  hyph : ∀ {c d} n -> c ===₂ d -> (conj ʰ') c n ≈₁ (conj ʰ') d n
  hyph {c} {d} [ PhaseX.ω-gen ]ʷ Z.order-Z = refl
  hyph {c} {d} [ PhaseX.X-gen ]ʷ Z.order-Z = by-equal-nf₁ auto
  hyph {c} {d} ε Z.order-Z = refl
  hyph {c} {d} (n • n₁) eq@Z.order-Z = cong (hyph n eq) (hyph n₁ eq)

  hypn : ∀ c {w v} -> w ===₁ v -> (conj ⁿ') c w ≈₁ (conj ⁿ') c v
  hypn c {w} {v} (left Cyclic.order) = by-equal-nf₁ auto
  hypn c {w} {v} (right Cyclic.order) = by-equal-nf₁ auto
  hypn c {w} {v} (mid (comm tt tt)) = by-equal-nf₁ auto
  
  nfp' : NFProperty' _===_
  nfp' = SDP2A.NFP'.nfp' hyph hypn PhaseX.nfp' Z.nfp'


module S where

  Gen = Cyclic.X

  infix 4 _===_
  _===_ : WRel Gen
  _===_ = Cyclic.pres 3

  pattern S-gen = tt
  pattern order-S = Cyclic.order

  S : Word Gen
  S = [ S-gen ]ʷ

  nfp' : NFProperty' _===_
  nfp' = Cyclic.nfp' 3


module HH where

  Gen = Cyclic.X

  infix 4 _===_
  _===_ : WRel Gen
  _===_ = Cyclic.pres 2

  pattern HH-gen = tt
  pattern order-HH = Cyclic.order

  HH : Word Gen
  HH = [ HH-gen ]ʷ

  nfp' : NFProperty' _===_
  nfp' = Cyclic.nfp' 2


module SHH where

  Gen = S.Gen ⊎ HH.Gen
  
  pattern S-gen = inj₁ S.S-gen
  pattern HH-gen = inj₂ tt

  pattern order-S = left S.order-S
  pattern order-HH = right HH.order-HH
  
  S : Word Gen
  S = [ S-gen ]ʷ

  HH : Word Gen
  HH = [ HH-gen ]ʷ

  conj : HH.Gen -> S.Gen -> Word S.Gen
  conj HH.HH-gen S.S-gen = S.S -- HHS = SZHH

  pattern conj-HH-S = mid (comm S.S-gen HH.HH-gen)

  infix 4 _===_
  _===_ : WRel Gen
  _===_ = (S._===_ ⸲ HH._===_ ⸲ Γⱼ' conj)
  

  open PB HH._===_ renaming (_===_ to _===₂_ ; _≈_ to _≈₂_) using ()
  open PP HH._===_ renaming (•-ε-monoid to m₂ ; word-setoid to ws₂) using ()
  
  open PB S._===_ renaming (_===_ to _===₁_ ; _≈_ to _≈₁_) using ()
  open PP S._===_ renaming (•-ε-monoid to m₁ ; word-setoid to ws₁ ; by-assoc-and to by-assoc-and₁ ; by-assoc to by-assoc₁) using ()

  open PB hiding (_===_)
  
  pattern auto = Eq.refl
  open NFProperty' (S.nfp') renaming (by-equal-nf to by-equal-nf₁)

  hyph : ∀ {c d} n -> c ===₂ d -> (conj ʰ') c n ≈₁ (conj ʰ') d n
  hyph {c} {d} [ S.S-gen ]ʷ HH.order-HH = by-equal-nf₁ auto
  hyph {c} {d} ε Cyclic.order = by-equal-nf₁ auto
  hyph {c} {d} (n • n₁) eq@Cyclic.order = cong (hyph n eq) (hyph n₁ eq)

  hypn : ∀ c {w v} -> w ===₁ v -> (conj ⁿ') c w ≈₁ (conj ⁿ') c v
  hypn HH.HH-gen {w} {v} S.order-S = by-equal-nf₁ auto

  nfp' : NFProperty' _===_
  nfp' = SDP2.NFP'.nfp' S._===_ HH._===_ conj hyph hypn S.nfp' HH.nfp'


module Symplectic-NFP' where

  open Symplectic
  open Symplectic-Lemmas
  
  f : SHH.Gen -> Word Gen
  f SHH.HH-gen = HH
  f SHH.S-gen = S

  
  open PB (SHH._===_) renaming (Alphabet to M ; _===_ to _===₀_ ; _≈_ to _≈₀_) using ()
  open NFProperty' SHH.nfp' using (by-equal-nf)
  
  open PB _===_ renaming (Alphabet to MB) using (_≈_)
  open SHH renaming (S to Sₘ ; HH to HHₘ) using ()

  open PB hiding (_===_ ; _≈_)
  
  data C : Set where
    cHSS : C
    cHS : C
    cH : C

  CT = C ⊎ ⊤

  pattern •ε = inj₂ tt
  pattern •H = inj₁ cH
  pattern •HS = inj₁ cHS
  pattern •HSS = inj₁ cHSS

  h : CT -> MB -> Word M × CT

  h •ε S-gen = Sₘ , •ε
  h •H S-gen = ε , •HS
  h •HS S-gen = ε , •HSS
  h •HSS S-gen = ε , •H
  h •ε H-gen = ε , •H
  h •H H-gen = HHₘ , •ε
  h •HS H-gen = Sₘ • Sₘ • HHₘ , •HSS
  h •HSS H-gen = Sₘ , •HS

  infix 4 _~_
  _~_ = Pointwise _≈₀_ (_≡_ {A = CT})

  h=⁻¹f-gen : ∀ x -> ([ x ]ʷ , •ε) ~ ((h **) •ε (f x)) 
  h=⁻¹f-gen SHH.S-gen = refl , auto
  h=⁻¹f-gen SHH.HH-gen = sym left-unit , auto

  h-wd-ax : ∀ c {u t} -> u === t -> (h **) c u ~ (h **) c t
  h-wd-ax •ε order-S = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax •H order-S = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax •HS order-S = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax •HSS order-S = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax •ε order-H = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax •H order-H = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax •HS order-H = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax •HSS order-H = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax •ε order-SH = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax •H order-SH = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax •HS order-SH = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax •HSS order-SH = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax •ε comm-HHS = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax •H comm-HHS = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax •HS comm-HHS = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax •HSS comm-HHS = by-equal-nf Eq.refl , Eq.refl

  open PP _===_
  open SR word-setoid

{-
  f-wd-ax : ∀ {w v} -> w ===₀ v -> (f *) w ≈ (f *) v
  f-wd-ax SHH.order-S = _≈_.trans _≈_.assoc (_≈_.axiom order-S)
  f-wd-ax SHH.order-HH = _≈_.trans _≈_.assoc (_≈_.axiom order-H)
  f-wd-ax SHH.conj-HH-S = _≈_.trans _≈_.assoc (_≈_.axiom comm-HHS)

  by-sub-nf : ∀ {w v} -> w ≈₀ v -> (f *) w ≈ (f *) v
  by-sub-nf {w} {v} eq = RS.Star-Congruence.lemma-f*-cong SHH._===_ _===_ f f-wd-ax eq 

  [_]ₒ : C -> Word MB
  [ cHSS ]ₒ = H • S • S
  [ cHS ]ₒ = H • S
  [ cH ]ₒ = H

  [_] : C ⊎ ⊤ -> Word MB
  [_] = [_,_] [_]ₒ (λ v → ε)

  open PP.NFProperty' SHH.nfp' renaming (by-equal-nf to by-equal-nfₘ)
  open Symplectic-Powers
  open CommData

  lemma-SSHH : S ^ 2 • H ^ 2 ≈ H ^ 2 • S ^ 2
  lemma-SSHH = begin
    S ^ 2 • H ^ 2 ≈⟨ _≈_.assoc ⟩
    S • S • H • H ≈⟨ _≈_.cong _≈_.refl (_≈_.sym (_≈_.axiom comm-HHS)) ⟩
    S • H • H • S ≈⟨ _≈_.sym (_≈_.trans _≈_.assoc (_≈_.cong _≈_.refl _≈_.assoc)) ⟩
    (S • H • H) • S ≈⟨ _≈_.sym (_≈_.cong (_≈_.axiom comm-HHS) _≈_.refl) ⟩
    (H • H • S) • S ≈⟨ _≈_.trans (_≈_.cong (_≈_.sym _≈_.assoc) _≈_.refl) _≈_.assoc ⟩
    H ^ 2 • S ^ 2 ∎
    
  h-hyp : ∀ c b -> [ c ] • [ b ]ʷ ≈ (f *) (h c b .proj₁) • [ h c b .proj₂ ]
  h-hyp •HSS H-gen = begin
    (H • S • S) • H ≈⟨ general-powers 100 auto ⟩
    H • (S ^ 2 • H ^ 2) • H ^ 3 ≈⟨ cong refl (cong lemma-SSHH refl) ⟩
    H • (H ^ 2 • S ^ 2) • H ^ 3 ≈⟨ by-assoc auto ⟩
    H ^ 3 • S ^ 2 • H ^ 3 ≈⟨ _≈_.sym lemma-SHS ⟩
    S • H • S ∎
  h-hyp •HS H-gen = by-assoc-and lemma-HSH auto auto
  h-hyp •H H-gen = general-powers 100 auto
  h-hyp •HSS S-gen = general-powers 100 auto
  h-hyp •HS S-gen = general-powers 100 auto
  h-hyp •H S-gen = general-powers 100 auto
  h-hyp •ε H-gen = general-powers 100 auto
  h-hyp •ε S-gen = general-powers 100 auto
  
  module ca = CA.Data (SHH._===_) _===_ CT (inj₂ tt) f h [_]
  module aat = ca.Assumptions-And-Theorems h=⁻¹f-gen h-wd-ax f-wd-ax _≈_.refl h-hyp

  nfp' = aat.nfp' SHH.nfp'

module XZ where

  Gen = Cyclic.X ⊎ Cyclic.X

  infix 4 _===_
  _===_ : WRel Gen
  _===_ = (Cyclic.pres 3 ⸲ Cyclic.pres 3 ⸲ Γₓ)

  pattern X-gen = inj₁ tt
  pattern Z-gen = inj₂ tt

  pattern order-X = left Cyclic.order
  pattern order-Z = right Cyclic.order
  pattern comm-Z-X = mid (comm tt tt)

  X : Word Gen
  X = [ X-gen ]ʷ

  Z : Word Gen
  Z = [ Z-gen ]ʷ

  nfp' : NFProperty' _===_
  nfp' = DP.NFP'.nfp' (Cyclic.pres 3) (Cyclic.pres 3) (Cyclic.nfp' 3) (Cyclic.nfp' 3)


module Semidirect where

  open import Presentation.Construct.Base

  Gen = XZ.Gen ⊎ Symplectic.Gen

  pattern X-gen = inj₁ XZ.X-gen
  pattern Z-gen = inj₁ XZ.Z-gen
  pattern H-gen = inj₂ Symplectic.H-gen
  pattern S-gen = inj₂ Symplectic.S-gen

  S : Word Gen
  S = [ S-gen ]ʷ
  Z : Word Gen
  Z = [ Z-gen ]ʷ
  X : Word Gen
  X = [ X-gen ]ʷ
  H : Word Gen
  H = [ H-gen ]ʷ

  conj : Symplectic.Gen -> XZ.Gen -> Word XZ.Gen
  conj Symplectic.H-gen XZ.X-gen = XZ.Z
  conj Symplectic.H-gen XZ.Z-gen = XZ.X ^ 2
  conj Symplectic.S-gen XZ.X-gen = XZ.X • XZ.Z
  conj s w = [ w ]ʷ

  pattern order-X = left XZ.order-X
  pattern order-Z = left XZ.order-Z
  pattern comm-Z-X = left XZ.comm-Z-X
  pattern order-H = right Symplectic.order-H
  pattern order-S = right Symplectic.order-S
  pattern order-SH = right Symplectic.order-SH
  pattern comm-HHS = right Symplectic.comm-HHS
  pattern conj-H-X = mid (comm XZ.X-gen Symplectic.H-gen)
  pattern conj-H-Z = mid (comm XZ.Z-gen Symplectic.H-gen)
  pattern conj-S-X = mid (comm XZ.X-gen Symplectic.S-gen)
  pattern conj-S-Z = mid (comm XZ.Z-gen Symplectic.S-gen)

  infix 4 _===_
  _===_ = (XZ._===_ ⸲ Symplectic._===_ ⸲ Γⱼ' conj)

  open PB Symplectic._===_ renaming (_===_ to _===₂_ ; _≈_ to _≈₂_) using ()
  open PP Symplectic._===_ renaming (•-ε-monoid to m₂ ; word-setoid to ws₂) using ()
  
  open PB XZ._===_ renaming (_===_ to _===₁_ ; _≈_ to _≈₁_) using ()
  open PP XZ._===_ renaming (•-ε-monoid to m₁ ; word-setoid to ws₁ ; by-assoc-and to by-assoc-and₁ ; by-assoc to by-assoc₁) using ()

  open PB hiding (_===_)
  
  open NFProperty' (XZ.nfp') renaming (by-equal-nf to by-equal-nf₁)

  hyph : ∀ {c d} n -> c ===₂ d -> (conj ʰ') c n ≈₁ (conj ʰ') d n
  hyph {c} {d} [ XZ.X-gen ]ʷ Symplectic.order-H = by-equal-nf₁ auto
  hyph {c} {d} [ XZ.X-gen ]ʷ Symplectic.order-S = by-equal-nf₁ auto
  hyph {c} {d} [ XZ.X-gen ]ʷ Symplectic.order-SH = by-equal-nf₁ auto
  hyph {c} {d} [ XZ.X-gen ]ʷ Symplectic.comm-HHS = by-equal-nf₁ auto
  hyph {c} {d} [ XZ.Z-gen ]ʷ Symplectic.order-H = by-equal-nf₁ auto
  hyph {c} {d} [ XZ.Z-gen ]ʷ Symplectic.order-S = by-equal-nf₁ auto
  hyph {c} {d} [ XZ.Z-gen ]ʷ Symplectic.order-SH = by-equal-nf₁ auto
  hyph {c} {d} [ XZ.Z-gen ]ʷ Symplectic.comm-HHS = by-equal-nf₁ auto
  hyph {c} {d} ε Symplectic.order-H = by-equal-nf₁ auto
  hyph {c} {d} ε Symplectic.order-S = by-equal-nf₁ auto
  hyph {c} {d} ε Symplectic.order-SH = by-equal-nf₁ auto
  hyph {c} {d} ε Symplectic.comm-HHS = by-equal-nf₁ auto
  hyph {c} {d} (n • n₁) eq@Symplectic.order-H = cong (hyph n eq) (hyph n₁ eq)
  hyph {c} {d} (n • n₁) eq@Symplectic.order-S = cong (hyph n eq) (hyph n₁ eq)
  hyph {c} {d} (n • n₁) eq@Symplectic.order-SH = cong (hyph n eq) (hyph n₁ eq)
  hyph {c} {d} (n • n₁) eq@Symplectic.comm-HHS = cong (hyph n eq) (hyph n₁ eq)

  hypn : ∀ c {w v} -> w ===₁ v -> (conj ⁿ') c w ≈₁ (conj ⁿ') c v
  hypn Symplectic.H-gen XZ.order-X = by-equal-nf₁ auto
  hypn Symplectic.H-gen XZ.order-Z = by-equal-nf₁ auto
  hypn Symplectic.H-gen XZ.comm-Z-X = by-equal-nf₁ auto
  hypn Symplectic.S-gen XZ.order-X = by-equal-nf₁ auto
  hypn Symplectic.S-gen XZ.order-Z = by-equal-nf₁ auto
  hypn Symplectic.S-gen XZ.comm-Z-X = by-equal-nf₁ auto

  nfp' : NFProperty' _===_
  nfp' = SDP2.NFP'.nfp' XZ._===_ Symplectic._===_ conj hyph hypn XZ.nfp' Symplectic-NFP'.nfp'

  open NFProperty' nfp'

  grouplike : Grouplike _===_
  grouplike H-gen = H ^ 3 , by-equal-nf auto
  grouplike S-gen = S ^ 2 , by-equal-nf auto
  grouplike X-gen = X ^ 2 , by-equal-nf auto
  grouplike Z-gen = Z ^ 2 , by-equal-nf auto


{-
module Iso where

  open import One.Clifford-Mod-Scalar
  open Clifford-Lemmas

  open import Presentation.Morphism Semidirect._===_ Clifford._===_
  open GroupMorphs Semidirect.grouplike Clifford-GroupLike.grouplike

  f : Semidirect.Gen -> Word Clifford.Gen
  f Semidirect.X-gen = Clifford.X
  f Semidirect.Z-gen = Clifford.Z
  f Semidirect.H-gen = Clifford.H
  f Semidirect.S-gen = Clifford.𝑠 -- Clifford.Z ^ 2 • Clifford.S

  g : Clifford.Gen -> Word Semidirect.Gen
  g Clifford.H-gen = Semidirect.H
  g Clifford.S-gen = Semidirect.Z • Semidirect.S
  

  open PB Semidirect._===_ renaming (_===_ to _===₁_ ; _≈_ to _≈₁_) using ()
  open NFProperty' Semidirect.nfp' renaming (by-equal-nf to by-equal-nf₁) using ()
  
  open PB Clifford._===_ renaming (_===_ to _===₂_ ; _≈_ to _≈₂_) using ()
  open Clifford-Powers renaming (general-powers to general-powers₂)

  open PP Semidirect._===_ renaming (by-assoc-and to by-assoc-and₁)
  open PP Clifford._===_ renaming (by-assoc-and to by-assoc-and₂ ; word-setoid to ws₂ ; by-assoc to by-assoc₂)

  open PB hiding (_===_)
  open Clifford
  open PP.NFProperty' Clifford-NFP'.nfp' renaming (by-equal-nf to by-equal-nf₂)

    
  f-well-defined : ∀ {w v} -> w ===₁ v -> (f *) w ≈₂ (f *) v
  f-well-defined Semidirect.order-X = _≈₂_.trans _≈₂_.assoc lemma-X^3
  f-well-defined Semidirect.order-Z = lemma-order-Z
  f-well-defined Semidirect.comm-Z-X = lemma-conj-X-Z
  f-well-defined Semidirect.order-H = by-equal-nf₂ auto
  f-well-defined Semidirect.order-S = by-equal-nf₂ auto
  f-well-defined Semidirect.order-SH = by-equal-nf₂ auto
  f-well-defined Semidirect.comm-HHS = by-equal-nf₂ auto
  f-well-defined Semidirect.conj-H-X = general-powers₂ 100 auto
  f-well-defined Semidirect.conj-H-Z = by-equal-nf₂ auto
  f-well-defined Semidirect.conj-S-X = by-equal-nf₂ auto
  f-well-defined Semidirect.conj-S-Z = by-equal-nf₂ auto


  g-well-defined : ∀ {w v} -> w ===₂ v -> (g *) w ≈₁ (g *) v
  g-well-defined {w} {v} Clifford.order-S = by-equal-nf₁ auto
  g-well-defined {w} {v} Clifford.order-H = by-equal-nf₁ auto
  g-well-defined {w} {v} Clifford.order-SH = by-equal-nf₁ auto
  g-well-defined comm-HHSHHS = by-equal-nf₁ auto

  f-left-inv-gen : ∀ x -> [ x ]ʷ ≈₂ (f *) (g x)
  f-left-inv-gen Clifford.H-gen = by-equal-nf₂ auto
  f-left-inv-gen Clifford.S-gen = by-equal-nf₂ auto

  g-left-inv-gen : ∀ x -> [ x ]ʷ ≈₁ (g *) (f x)
  g-left-inv-gen Semidirect.S-gen = by-equal-nf₁ auto
  g-left-inv-gen Semidirect.H-gen = by-equal-nf₁ auto
  g-left-inv-gen Semidirect.X-gen = by-equal-nf₁ auto
  g-left-inv-gen Semidirect.Z-gen = by-equal-nf₁ auto


  open import Algebra.Bundles using (Group)
  open import Algebra.Morphism.Structures using (module GroupMorphisms)

  open import Presentation.Morphism
  open GroupMorphisms
  module G1 = Group-Lemmas Semidirect.Gen Semidirect._===_ Semidirect.grouplike
  module G2 = Group-Lemmas Clifford.Gen Clifford._===_ Clifford-GroupLike.grouplike

  Theorem-Semidirect-iso-Clifford : IsGroupIsomorphism (Group.rawGroup G1.•-ε-group) (Group.rawGroup G2.•-ε-group) (f *)
  Theorem-Semidirect-iso-Clifford = StarGroupIsomorphism.isGroupIsomorphism f g f-well-defined  f-left-inv-gen g-well-defined  g-left-inv-gen

  -- This theorem says 1 qutrit Clifford mod scalars is isomorphic to
  -- ℤ₃² ⋊ Sp(2,3). The presentations are:
  
  -- Clifford:
  --   order-S : S ^ 3 === ε
  --   order-H : H ^ 4 === ε
  --   order-SH : (S • H) ^ 3 === ε
  --   comm-HHSHHS : H • H • S • H • H • S === S • H • H • S • H • H

  -- Semidirct product:
  --   ℤ₃²:
  --     order-X 
  --     order-Z 
  --     comm-Z-X
      
  --   Sp(2,3): 
  --     order-S : S ^ 3 === ε
  --     order-H : H ^ 4 === ε
  --     order-SH : (S • H) ^ 3 === ε
  --     comm-HHS : H • H • S === S • H • H
      
  --   conjugation:
  --     conj-H-X 
  --     conj-H-Z 
  --     conj-S-X 
  --     conj-S-Z 

  -- NOTE: S in Sp(2,3) is ZZS in Clifford.
-}
-}
-}
