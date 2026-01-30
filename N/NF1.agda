{-# OPTIONS  --safe #-}
{-# OPTIONS  --call-by-name #-}
{-# OPTIONS --termination-depth=2 #-}
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



module N.NF1 (p-2 : ℕ) (p-prime : Prime (2+ p-2))  where

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


open import Zp.ModularArithmetic
open PrimeModulus p-2 p-prime
open import N.Symplectic-Derived p-2 p-prime
open import N.Lemmas-2Qupit p-2 p-prime
open Lemmas-2Q 2
open Symplectic-Derived-Gen
open import N.Action p-2 p-prime

module Normal-Form1 where

  private
    variable
      n : ℕ
  open import N.Cosets p-2 p-prime
  
  ⟦_⟧ₕₛ : Cosets1 -> Word (Gen (₁₊ n))
  ⟦ ε ⟧ₕₛ = ε
  ⟦ HS^ x ⟧ₕₛ = H • S^ x

  ⟦_⟧'ₕₛ : Cosets1-noε -> Word (Gen (₁₊ n))
  ⟦ HS^ x ⟧'ₕₛ = H • S^ x

  ⟦_⟧ₛ : SPowers -> Word (Gen (₁₊ n))
  ⟦ x ⟧ₛ = S^ x

  ⟦_⟧ₘ : ZMultiplier -> Word (Gen (₁₊ n))
  ⟦ x ⟧ₘ = M x

  ⟦_⟧ₘ₊ : MC -> Word (Gen (₁₊ n))
  ⟦ m , c ⟧ₘ₊ = ⟦ m ⟧ₘ • ⟦ c ⟧ₕₛ

  ⟦_⟧ₘₕₛ : MC' -> Word (Gen (₁₊ n))
  ⟦ m , c ⟧ₘₕₛ = ⟦ m ⟧ₘ • ⟦ c ⟧'ₕₛ

  ⟦_⟧₁ : NF1 -> Word (Gen (₁₊ n))
  ⟦ s , m , c ⟧₁ =  ⟦ s ⟧ₛ • ⟦ m ⟧ₘ • ⟦ c ⟧ₕₛ

  open Eq
  open import Algebra.Properties.Ring (+-*-ring p-2)
  
  
  lemma-HS : ∀ a b t -> (neq0 : a ≢ ₀) -> let a⁻¹ = (a , neq0) ⁻¹ in let -b/a = - b * a⁻¹ .proj₁ in

    act {₁₊ n} (H • S^ -b/a) ((a , b) ∷ t) ≡ (₀ , a) ∷ t
    
  lemma-HS a b t neq0 = begin
    act (H • S^ -b/a) ((a , b) ∷ t) ≡⟨ auto ⟩
    act (H) ((a , b + a * -b/a) ∷ t) ≡⟨ auto ⟩
    ((- (b + a * -b/a) , a) ∷ t) ≡⟨ cong (\ xx -> ( xx , a) ∷ t) (cong -_ aux-ba) ⟩
    ((- ₀ , a) ∷ t) ≡⟨ cong (\ xx -> ( xx , a) ∷ t) -0#≈0# ⟩
    ((₀ , a) ∷ t) ∎
    where
    open ≡-Reasoning
    a⁻¹ = (a , neq0) ⁻¹
    -b/a = - b * a⁻¹ .proj₁
    aux-ba : b + a * -b/a ≡ ₀
    aux-ba = begin
      b + a * -b/a ≡⟨ cong (b +_) (cong (a *_) (*-comm (- b) (a⁻¹ .proj₁))) ⟩ 
      b + a * (a⁻¹ .proj₁ * - b) ≡⟨ cong (b +_) (sym (*-assoc a (a⁻¹ .proj₁) (- b) )) ⟩
      b + a * a⁻¹ .proj₁ * - b ≡⟨ cong (b +_) (cong (_* - b) (lemma-⁻¹ʳ a {{nztoℕ {y = a} {neq0 = neq0}}})) ⟩
      b + 1ₚ * - b ≡⟨ Eq.cong (b +_) (*-identityˡ (- b)) ⟩
      b + - b ≡⟨  +-inverseʳ b ⟩
      ₀ ∎


  lemma-HS-x : ∀ k a b t -> 

    act {₁₊ n} (H • S^ k) ((a , b) ∷ t) ≡ (- (b + a * k) , a) ∷ t
    
  lemma-HS-x a b t neq0 = auto


  lemma-M : ∀ a b t x' ->
    let x = (x' .proj₁) in
    let x⁻¹ = ((x' ⁻¹) .proj₁) in
    
    act {₁₊ n} (M x') ((a , b) ∷ t) ≡ (a * x⁻¹ , b * x) ∷ t
    
  lemma-M a b t x' = begin
    act (M x') ((a , b) ∷ t) ≡⟨ auto ⟩
    act (S^ x • H • S^ x⁻¹ • H • S^ x • H) ((a , b) ∷ t) ≡⟨ auto ⟩
    act (S^ x • H • S^ x⁻¹ • H • S^ x) ((- b , a) ∷ t) ≡⟨ auto ⟩
    act (S^ x • H • S^ x⁻¹ • H) ((- b , a + (- b) * x) ∷ t) ≡⟨ auto ⟩
    act (S^ x • H • S^ x⁻¹) (( - (a + (- b) * x) , - b) ∷ t) ≡⟨ auto ⟩
    act (S^ x • H) (( - (a + (- b) * x) , - b + (- (a + (- b) * x)) * (x⁻¹)) ∷ t) ≡⟨ auto ⟩
    act (S^ x) ((- (- b + (- (a + (- b) * x)) * (x⁻¹)) , - (a + (- b) * x) ) ∷ t) ≡⟨ auto ⟩
    (- (- b + - (a + - b * x) * x⁻¹) , - (a + - b * x) + - (- b + - (a + - b * x) * x⁻¹) * x) ∷ t ≡⟨ Eq.cong (_∷ t) (Eq.sym (≡×≡⇒≡ (-‿+-comm (- b) (- (a + - b * x) * x⁻¹) , Eq.cong₂ _+_ (-‿+-comm a (- b * x)) (Eq.cong (_* x) (-‿+-comm (- b) (- (a + - b * x) * x⁻¹)))))) ⟩
    (- - b + - ((- (a + - b * x)) * x⁻¹) , - a + - (- b * x) + (- - b + - (- (a + - b * x) * x⁻¹)) * x) ∷ t ≡⟨ Eq.cong (_∷ t) (≡×≡⇒≡ (cong₂ _+_ (-‿involutive b) (-‿distribˡ-* ((- (a + - b * x))) x⁻¹) , cong₂ _+_ (cong (- a +_) (-‿distribˡ-* (- b) x)) (cong₂ (\ xx yy -> (xx + yy) * x) (-‿involutive b) (-‿distribˡ-* (- (a + - b * x)) x⁻¹)))) ⟩
    (b + - (- (a + - b * x)) * x⁻¹ , - a + - - b * x + (b + - - (a + - b * x) * x⁻¹) * x) ∷ t ≡⟨ Eq.cong (_∷ t) (≡×≡⇒≡ (Eq.cong (\ xx -> b + xx * x⁻¹) (-‿involutive (a + - b * x)) ,  cong₂ _+_ (cong (\ xx -> - a + xx * x) (-‿involutive b)) (cong (\ xx -> (b + xx * x⁻¹) * x) (-‿involutive (a + - b * x))))) ⟩
    (b + (a + - b * x) * x⁻¹ , - a + b * x + (b + (a + - b * x) * x⁻¹) * x) ∷ t ≡⟨ Eq.cong (_∷ t) (≡×≡⇒≡ ((cong (b +_) (*-distribʳ-+ x⁻¹ a (- b * x))) , cong (\ xx -> - a + b * x + xx) (*-distribʳ-+ x b ((a + - b * x) * x⁻¹)))) ⟩
    (b + (a * x⁻¹ + - b * x * x⁻¹) , - a + b * x + (b * x + (a + - b * x) * x⁻¹ * x)) ∷ t ≡⟨ Eq.cong (_∷ t) (≡×≡⇒≡ ((cong (\ xx -> b + (a * x⁻¹ + xx)) (*-assoc (- b) x x⁻¹)) , (cong (\ xx -> - a + b * x + (b * x + xx)) (*-assoc ((a + - b * x)) x⁻¹ x)))) ⟩
    (b + (a * x⁻¹ + - b * (x * x⁻¹)) , - a + b * x + (b * x + (a + - b * x) * (x⁻¹ * x))) ∷ t ≡⟨ Eq.cong (_∷ t) (≡×≡⇒≡ ((cong (\ xx -> b + (a * x⁻¹ + - b * xx)) (lemma-⁻¹ʳ x {{nztoℕ {y = x} {neq0 = x' .proj₂}}}) , (cong (\ xx -> - a + b * x + (b * x + (a + - b * x) * xx)) (lemma-⁻¹ˡ x {{nztoℕ {y = x} {neq0 = x' .proj₂}}}))))) ⟩
    (b + (a * x⁻¹ + - b * ₁) , - a + b * x + (b * x + (a + - b * x) * ₁)) ∷ t ≡⟨ Eq.cong (_∷ t) (≡×≡⇒≡ ((cong (\ xx -> b + (a * x⁻¹ + xx)) (*-identityʳ (- b)) , (cong (\ xx -> - a + b * x + (b * x + xx)) (*-identityʳ (a + - b * x)))))) ⟩
    (b + (a * x⁻¹ + - b) , - a + b * x + (b * x + (a + - b * x))) ∷ t ≡⟨ Eq.cong (_∷ t) (≡×≡⇒≡ ((cong (b +_) (+-comm (a * x⁻¹) (- b))) , (cong (\ xx -> - a + b * x + xx) (+-comm (b * x) ((a + - b * x)))))) ⟩
    (b + (- b + a * x⁻¹) , - a + b * x + ((a + - b * x) + b * x)) ∷ t ≡⟨ Eq.cong (_∷ t) (sym (≡×≡⇒≡ ((+-assoc b (- b) (a * x⁻¹)) , (+-assoc (- a + b * x) ((a + - b * x)) (b * x))))) ⟩
    (b + - b + a * x⁻¹ , - a + b * x + (a + - b * x) + b * x) ∷ t ≡⟨ Eq.cong (_∷ t) (≡×≡⇒≡ ((cong (_+ a * x⁻¹) (+-inverseʳ b)) , (cong (_+ b * x) (+-assoc (- a) (b * x) ((a + - b * x)))))) ⟩
    (₀ + a * x⁻¹ , - a + (b * x + (a + - b * x)) + b * x) ∷ t ≡⟨ Eq.cong (_∷ t) (≡×≡⇒≡ ((+-identityˡ (a * x⁻¹)) , cong (\ xx -> - a + (b * x + xx) + b * x) (+-comm a (- b * x)))) ⟩
    (a * x⁻¹ , - a + (b * x + (- b * x + a)) + b * x) ∷ t ≡⟨ cong (\ xx -> (a * x⁻¹ , - a + xx + b * x) ∷ t) (sym (+-assoc (b * x) (- b * x) a)) ⟩
    (a * x⁻¹ , - a + (b * x + - b * x + a) + b * x) ∷ t ≡⟨ cong (\ xx -> (a * x⁻¹ , - a + (b * x + xx + a) + b * x) ∷ t) (sym (-‿distribˡ-* b x)) ⟩
    (a * x⁻¹ , - a + (b * x + - (b * x) + a) + b * x) ∷ t ≡⟨ cong (\ xx -> (a * x⁻¹ , - a + (xx + a) + b * x) ∷ t) (+-inverseʳ (b * x)) ⟩
    (a * x⁻¹ , - a + (₀ + a) + b * x) ∷ t ≡⟨ cong (\ xx -> (a * x⁻¹ , - a + xx + b * x) ∷ t) (+-identityˡ a) ⟩
    (a * x⁻¹ , - a + a + b * x) ∷ t ≡⟨ cong (\ xx -> (a * x⁻¹ , xx + b * x) ∷ t) (+-inverseˡ a) ⟩
    (a * x⁻¹ , ₀ + b * x) ∷ t ≡⟨ cong (\ xx -> (a * x⁻¹ , xx) ∷ t) (+-identityˡ (b * x)) ⟩
    (a * x⁻¹ , b * x) ∷ t ∎
    where
    open ≡-Reasoning
    x = (x' .proj₁)
    x⁻¹ = ((x' ⁻¹) .proj₁ )



  sform-pI-q=0 : ∀ (p : Pauli1) -> sform1 pI p ≡ ₀
  sform-pI-q=0 (c , d) = begin
    sform1 pI (c , d) ≡⟨ auto ⟩
    (- ₀) * d + c * ₀ ≡⟨ cong₂ _+_ (cong (_* d) -0#≈0#) (*-comm c ₀) ⟩
    ₀ * d + ₀ * c ≡⟨ auto ⟩
    ₀ ∎
    where open ≡-Reasoning

  sform-pIₙ-q=0' : ∀ (p : Pauli 1) -> sform pIₙ p ≡ ₀
  sform-pIₙ-q=0' ((c , d) ∷ []) = begin
    sform1 pI (c , d) + ₀ ≡⟨ +-identityʳ (sform1 pI (c , d)) ⟩
    sform1 pI (c , d) ≡⟨ sform-pI-q=0 (c , d) ⟩
    ₀ ≡⟨ auto ⟩
    ₀ + ₀ ∎
    where open ≡-Reasoning


  sform-0b : ∀ b c d -> sform1 (₀ , b) (c , d) ≡ b * c
  sform-0b b c d = begin
    sform1 (₀ , b) (c , d) ≡⟨ auto ⟩
    (- ₀) * d + c * b ≡⟨ cong (\ xx -> xx * d + c * b) -0#≈0# ⟩
    ₀ * d + c * b ≡⟨ auto ⟩
    ₀ + c * b ≡⟨ +-identityˡ (c * b) ⟩
    c * b ≡⟨ *-comm c b ⟩
    b * c ∎
    where open ≡-Reasoning

  sform-0b' : ∀ b c d -> sform ((₀ , b) ∷ []) ((c , d) ∷ []) ≡ b * c
  sform-0b' b c d = begin
    sform1 (₀ , b) (c , d) + ₀ ≡⟨  +-identityʳ  (sform1 (₀ , b) (c , d)) ⟩
    sform1 (₀ , b) (c , d) ≡⟨ sform-0b b c d ⟩
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

  Theorem-NF1 :

    ∀ (p q : Pauli1) (t : Pauli n) ->
    sform1 p q ≡ ₁ ->
    -------------------------------
    ∃ \ nf -> act {₁₊ n} ⟦ nf ⟧₁ (p ∷ t) ≡ pZ ∷ t ×
              act {₁₊ n} ⟦ nf ⟧₁ (q ∷ t) ≡ pX ∷ t

  Theorem-NF1 {n} p@((₀ , ₀)) q@(q1) t eq with 0ₚ≢1ₚ (Eq.trans (Eq.sym (sform-pI-q=0 q)) (eq))
  ... | ()


  Theorem-NF1 {n} p@((₀ , b@(₁₊ b'))) q@((c , d)) t eq = nf , claim1 , claim2
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

    nf = -dx , b⁻¹ , ε
    
    claim1 : act ⟦ nf ⟧₁ (p ∷ t) ≡ pZ ∷ t
    claim1 = begin
      act ⟦ nf ⟧₁ (p ∷ t) ≡⟨ auto ⟩
      act (S^ -dx • (S^ x • H • S^ x⁻¹ • H • S^ x • H) • ε) (p ∷ t) ≡⟨ auto ⟩
      act (S^ -dx • (S^ x • H • S^ x⁻¹ • H • S^ x • H)) (p ∷ t) ≡⟨ auto ⟩
      act (S^ -dx • (S^ x • H • S^ x⁻¹ • H • S^ x • H)) (p ∷ t) ≡⟨ auto ⟩
      act (S^ -dx) (act (S^ x • H • S^ x⁻¹ • H • S^ x • H) (p ∷ t)) ≡⟨ cong (act (S^ -dx)) (lemma-M (p .proj₁) (p .proj₂) t b⁻¹) ⟩
      act (S^ -dx) ((₀ * x⁻¹ , b * x) ∷ t) ≡⟨ cong (\ xx -> act (S^ -dx) ((₀ , xx) ∷ t)) (*-comm b x) ⟩
      act (S^ -dx) ((₀ , x * b ) ∷ t) ≡⟨ cong (\ xx -> act (S^ -dx) ((₀ , xx) ∷ t)) (lemma-⁻¹ˡ b {{nztoℕ {y = b} {neq0 = λ ()}}}) ⟩
      pZ ∷ t ∎

    cb=1 : c * b ≡ 1ₚ
    cb=1 = begin
      c * b ≡⟨ *-comm c b ⟩
      b * c ≡⟨ sym (sform-0b b c d) ⟩
      sform1 p q ≡⟨ eq ⟩
      1ₚ ∎
      
    claim2 : act {₁₊ n} ⟦ nf ⟧₁ (q ∷ t) ≡ pX ∷ t
    claim2 = begin
      act ⟦ nf ⟧₁ (q ∷ t) ≡⟨ cong (act (S^ -dx)) (lemma-M c d t b⁻¹) ⟩ 
      act (S^ -dx) ((c * x⁻¹ , d * x ) ∷ t) ≡⟨ cong (\ xx -> act (S^ -dx) ((c * xx , d * x ) ∷ t)) (inv-involutive ((b , λ ()))) ⟩
      act (S^ -dx) ((c * b , d * x ) ∷ t) ≡⟨ cong (\ xx -> act (S^ -dx) ((xx , d * x ) ∷ t)) cb=1 ⟩
      act (S^ -dx) ((1ₚ , d * x ) ∷ t) ≡⟨ auto ⟩
      ((1ₚ , d * x + 1ₚ * -dx) ∷ t) ≡⟨ cong (\ xx -> ((1ₚ , d * x + xx) ∷ t)) (*-identityˡ -dx) ⟩
      ((1ₚ , d * x + -dx) ∷ t) ≡⟨  cong (\ xx -> ((1ₚ , xx) ∷ t)) (+-inverseʳ (d * x)) ⟩
      pX ∷ t ∎

  Theorem-NF1 p@(a@(₁₊ _) , b) q@(c , d) t eq = nf , (claim1 , claim2)
    where
    open ≡-Reasoning
    
    a⁻¹ = (a , λ ()) ⁻¹
    1/a = a⁻¹ .proj₁
    -b/a = - b * 1/a
    x = 1/a
    x⁻¹ = (a⁻¹ ⁻¹) .proj₁
    -c/a = - c * 1/a

    nf = -c/a , a⁻¹ , HS^ -b/a
    p' = act (H • S^ -b/a) (p ∷ t)
    
    claim1 : act ⟦ nf ⟧₁ (p ∷ t) ≡ pZ ∷ t
    claim1 = begin
      act ⟦ nf ⟧₁ (p ∷ t) ≡⟨ auto ⟩
      act (S^ -c/a • (S^ x • H • S^ x⁻¹ • H • S^ x • H) • (H • S^ -b/a)) (p ∷ t) ≡⟨ auto ⟩
      act (S^ -c/a • (S^ x • H • S^ x⁻¹ • H • S^ x • H)) p' ≡⟨ auto ⟩
      act (S^ -c/a • (S^ x • H • S^ x⁻¹ • H • S^ x • H)) p' ≡⟨ auto ⟩
      act (S^ -c/a) (act (S^ x • H • S^ x⁻¹ • H • S^ x • H) p') ≡⟨ cong (\ xx -> act (S^ -c/a) (act (S^ x • H • S^ x⁻¹ • H • S^ x • H) xx)) (lemma-HS a b t (λ ())) ⟩
      act (S^ -c/a) (act (S^ x • H • S^ x⁻¹ • H • S^ x • H) ((₀ , a) ∷ t)) ≡⟨ cong (act (S^ -c/a)) (lemma-M (₀) (a) t a⁻¹) ⟩
      act (S^ -c/a) ((₀ * x⁻¹ , a * x ) ∷ t) ≡⟨ cong (\ xx -> act (S^ -c/a) ((₀ , xx ) ∷ t)) (lemma-⁻¹ʳ a {{nztoℕ {y = a} {neq0 = λ ()}}}) ⟩
      act (S^ -c/a) ((₀ , ₁ ) ∷ t) ≡⟨ auto ⟩
      act (S^ -c/a) ((₀ , ₁ + ₀ * -c/a ) ∷ t) ≡⟨ auto ⟩
      pZ ∷ t ∎


    q' = act (H • S^ -b/a) (q ∷ t)

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

    claim2 : act ⟦ nf ⟧₁ (q ∷ t) ≡ pX ∷ t
    claim2 = begin
      act ⟦ nf ⟧₁ (q ∷ t) ≡⟨ auto ⟩
      act (S^ -c/a • (S^ x • H • S^ x⁻¹ • H • S^ x • H)) ((- (d + c * -b/a) , c) ∷ t) ≡⟨ cong (act (S^ -c/a)) (lemma-M (- (d + c * -b/a)) c t a⁻¹) ⟩
      act (S^ -c/a) ((- (d + c * -b/a) * x⁻¹ , c * x ) ∷ t) ≡⟨ cong (\ xx -> act (S^ -c/a) ((- (d + c * -b/a) * xx , c * x ) ∷ t)) (inv-involutive (a , (λ ()))) ⟩
      act (S^ -c/a) ((- (d + c * -b/a) * a , c * x ) ∷ t) ≡⟨ cong (\ xx -> act (S^ -c/a) ((xx , c * x ) ∷ t)) aux-dca ⟩
      act (S^ -c/a) ((₁ , c * x) ∷ t) ≡⟨ auto ⟩
      ((₁ , c * x + ₁ * -c/a ) ∷ t) ≡⟨ cong (\ xx -> (₁ , xx) ∷ t) aux-dx ⟩
      pX ∷ t ∎


  Theorem-MC :

    ∀ (p q : Pauli1) (t : Pauli n) ->
    sform1 p q ≡ ₁ ->
    -------------------------------
    ∃ \ mc -> ∃ \ e ->
      act {₁₊ n} ⟦ mc ⟧ₘ₊ (p ∷ t) ≡ pZ ∷ t ×
      act {₁₊ n} ⟦ mc ⟧ₘ₊ (q ∷ t) ≡ (₁ , e) ∷ t

  Theorem-MC {n} p@((₀ , ₀)) q@(q1) t eq with 0ₚ≢1ₚ (Eq.trans (Eq.sym (sform-pI-q=0 q)) (eq))
  ... | ()


  Theorem-MC {n} p@((₀ , b@(₁₊ b'))) q@((c , d)) t eq = mc , (d * x) , (claim1 , claim2)
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

    mc = b⁻¹ , ε
    
    claim1 : act ⟦ mc ⟧ₘ₊ (p ∷ t) ≡ pZ ∷ t
    claim1 = begin
      act ⟦ mc ⟧ₘ₊ (p ∷ t) ≡⟨ auto ⟩
      act ((S^ x • H • S^ x⁻¹ • H • S^ x • H) • ε) (p ∷ t) ≡⟨ auto ⟩
      act ((S^ x • H • S^ x⁻¹ • H • S^ x • H)) (p ∷ t) ≡⟨ auto ⟩
      act ((S^ x • H • S^ x⁻¹ • H • S^ x • H)) (p ∷ t) ≡⟨ auto ⟩
       (act (S^ x • H • S^ x⁻¹ • H • S^ x • H) (p ∷ t)) ≡⟨ (lemma-M (p .proj₁) (p .proj₂) t b⁻¹) ⟩
       ((₀ * x⁻¹ , b * x) ∷ t) ≡⟨ cong (\ xx ->  ((₀ , xx) ∷ t)) (*-comm b x) ⟩
       ((₀ , x * b ) ∷ t) ≡⟨ cong (\ xx ->  ((₀ , xx) ∷ t)) (lemma-⁻¹ˡ b {{nztoℕ {y = b} {neq0 = λ ()}}}) ⟩
      pZ ∷ t ∎

    cb=1 : c * b ≡ 1ₚ
    cb=1 = begin
      c * b ≡⟨ *-comm c b ⟩
      b * c ≡⟨ sym (sform-0b b c d) ⟩
      sform1 p q ≡⟨ eq ⟩
      1ₚ ∎
      
    claim2 : act {₁₊ n} ⟦ mc ⟧ₘ₊ (q ∷ t) ≡ ((1ₚ , d * x ) ∷ t)
    claim2 = begin
      act ⟦ mc ⟧ₘ₊ (q ∷ t) ≡⟨ (lemma-M c d t b⁻¹) ⟩ 
       ((c * x⁻¹ , d * x ) ∷ t) ≡⟨ cong (\ xx ->  ((c * xx , d * x ) ∷ t)) (inv-involutive ((b , λ ()))) ⟩
       ((c * b , d * x ) ∷ t) ≡⟨ cong (\ xx ->  ((xx , d * x ) ∷ t)) cb=1 ⟩
       ((1ₚ , d * x ) ∷ t) ∎

  Theorem-MC p@(a@(₁₊ _) , b) q@(c , d) t eq = mc , c * x , claim1 , claim2
    where
    open ≡-Reasoning
    
    a⁻¹ = (a , λ ()) ⁻¹
    1/a = a⁻¹ .proj₁
    -b/a = - b * 1/a
    x = 1/a
    x⁻¹ = (a⁻¹ ⁻¹) .proj₁
    -c/a = - c * 1/a

    mc = a⁻¹ , HS^ -b/a
    p' = act (H • S^ -b/a) (p ∷ t)
    
    claim1 : act ⟦ mc ⟧ₘ₊ (p ∷ t) ≡ pZ ∷ t
    claim1 = begin
      act ⟦ mc ⟧ₘ₊ (p ∷ t) ≡⟨ auto ⟩
      act ((S^ x • H • S^ x⁻¹ • H • S^ x • H) • (H • S^ -b/a)) (p ∷ t) ≡⟨ auto ⟩
      act ((S^ x • H • S^ x⁻¹ • H • S^ x • H)) p' ≡⟨ auto ⟩
      act ((S^ x • H • S^ x⁻¹ • H • S^ x • H)) p' ≡⟨ auto ⟩
      (act (S^ x • H • S^ x⁻¹ • H • S^ x • H) p') ≡⟨ cong (\ xx -> (act (S^ x • H • S^ x⁻¹ • H • S^ x • H) xx)) (lemma-HS a b t (λ ())) ⟩
      (act (S^ x • H • S^ x⁻¹ • H • S^ x • H) ((₀ , a) ∷ t)) ≡⟨ (lemma-M (₀) (a) t a⁻¹) ⟩
      ((₀ * x⁻¹ , a * x ) ∷ t) ≡⟨ cong (\ xx -> ((₀ , xx ) ∷ t)) (lemma-⁻¹ʳ a {{nztoℕ {y = a} {neq0 = λ ()}}}) ⟩
      ((₀ , ₁ ) ∷ t) ≡⟨ auto ⟩
      ((₀ , ₁ + ₀ * -c/a ) ∷ t) ≡⟨ auto ⟩
      pZ ∷ t ∎


    q' = act (H • S^ -b/a) (q ∷ t)

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

    claim2 : act ⟦ mc ⟧ₘ₊ (q ∷ t) ≡ ((₁ , c * x)) ∷ t
    claim2 = begin
      act ⟦ mc ⟧ₘ₊ (q ∷ t) ≡⟨ auto ⟩
      act ((S^ x • H • S^ x⁻¹ • H • S^ x • H)) ((- (d + c * -b/a) , c) ∷ t) ≡⟨ (lemma-M (- (d + c * -b/a)) c t a⁻¹) ⟩
      ((- (d + c * -b/a) * x⁻¹ , c * x ) ∷ t) ≡⟨ cong (\ xx -> ((- (d + c * -b/a) * xx , c * x ) ∷ t)) (inv-involutive (a , (λ ()))) ⟩
      ((- (d + c * -b/a) * a , c * x ) ∷ t) ≡⟨ cong (\ xx -> ((xx , c * x ) ∷ t)) aux-dca ⟩
      ((₁ , c * x) ∷ t) ∎




  Theorem-MC' :

    ∀ (p : Pauli1) (t : Pauli n) ->
    p ≢ (₀ , ₀) ->
    -------------------------------
    ∃ \ mc -> act {₁₊ n} ⟦ mc ⟧ₘ₊ (p ∷ t) ≡ pZ ∷ t


  Theorem-MC' {n} p@((₀ , ₀)) t eq with eq Eq.refl
  ... | ()
  
  Theorem-MC' {n} p@((₀ , b@(₁₊ b'))) t eq = mc , claim1
    where
    open ≡-Reasoning
    -b = - b

    -bnz : - b ≢ 0ₚ
    -bnz = (-' (b , λ ())) .proj₂

    b⁻¹ = (b , λ ()) ⁻¹
    -b⁻¹ = -' b⁻¹

    x⁻¹ = _⁻¹ b⁻¹ .proj₁
    x = b⁻¹ .proj₁

    mc = b⁻¹ , ε
    
    claim1 : act ⟦ mc ⟧ₘ₊ (p ∷ t) ≡ pZ ∷ t
    claim1 = begin
      act ⟦ mc ⟧ₘ₊ (p ∷ t) ≡⟨ auto ⟩
      act ((S^ x • H • S^ x⁻¹ • H • S^ x • H) • ε) (p ∷ t) ≡⟨ auto ⟩
      act ((S^ x • H • S^ x⁻¹ • H • S^ x • H)) (p ∷ t) ≡⟨ auto ⟩
      act ((S^ x • H • S^ x⁻¹ • H • S^ x • H)) (p ∷ t) ≡⟨ auto ⟩
       (act (S^ x • H • S^ x⁻¹ • H • S^ x • H) (p ∷ t)) ≡⟨ (lemma-M (p .proj₁) (p .proj₂) t b⁻¹) ⟩
       ((₀ * x⁻¹ , b * x) ∷ t) ≡⟨ cong (\ xx ->  ((₀ , xx) ∷ t)) (*-comm b x) ⟩
       ((₀ , x * b ) ∷ t) ≡⟨ cong (\ xx ->  ((₀ , xx) ∷ t)) (lemma-⁻¹ˡ b {{nztoℕ {y = b} {neq0 = λ ()}}}) ⟩
      pZ ∷ t ∎


  Theorem-MC' p@(a@(₁₊ _) , b) t eq = mc , claim1
    where
    open ≡-Reasoning
    
    a⁻¹ = (a , λ ()) ⁻¹
    1/a = a⁻¹ .proj₁
    -b/a = - b * 1/a
    x = 1/a
    x⁻¹ = (a⁻¹ ⁻¹) .proj₁

    mc = a⁻¹ , HS^ -b/a
    p' = act (H • S^ -b/a) (p ∷ t)
    
    claim1 : act ⟦ mc ⟧ₘ₊ (p ∷ t) ≡ pZ ∷ t
    claim1 = begin
      act ⟦ mc ⟧ₘ₊ (p ∷ t) ≡⟨ auto ⟩
      act ((S^ x • H • S^ x⁻¹ • H • S^ x • H) • (H • S^ -b/a)) (p ∷ t) ≡⟨ auto ⟩
      act ((S^ x • H • S^ x⁻¹ • H • S^ x • H)) p' ≡⟨ auto ⟩
      act ((S^ x • H • S^ x⁻¹ • H • S^ x • H)) p' ≡⟨ auto ⟩
      (act (S^ x • H • S^ x⁻¹ • H • S^ x • H) p') ≡⟨ cong (\ xx -> (act (S^ x • H • S^ x⁻¹ • H • S^ x • H) xx)) (lemma-HS a b t (λ ())) ⟩
      (act (S^ x • H • S^ x⁻¹ • H • S^ x • H) ((₀ , a) ∷ t)) ≡⟨ (lemma-M (₀) (a) t a⁻¹) ⟩
      ((₀ * x⁻¹ , a * x ) ∷ t) ≡⟨ cong (\ xx -> ((₀ , xx ) ∷ t)) (lemma-⁻¹ʳ a {{nztoℕ {y = a} {neq0 = λ ()}}}) ⟩
      ((₀ , ₁ ) ∷ t) ≡⟨ auto ⟩
      pZ ∷ t ∎

  -pZ : Pauli1
  -pZ = (₀ , - ₁)

  Theorem-MC-pZ :

    ∀ (p : Pauli1) (t : Pauli n) ->
    p ≢ (₀ , ₀) ->
    -------------------------------
    ∃ \ mc -> act {₁₊ n} ⟦ mc ⟧ₘ₊ (p ∷ t) ≡ -pZ ∷ t


  Theorem-MC-pZ {n} p@((₀ , ₀)) t eq with eq Eq.refl
  ... | ()
  
  Theorem-MC-pZ {n} p@((₀ , b@(₁₊ b'))) t eq = mc , claim1
    where
    open ≡-Reasoning
    -b = - b

    -bnz : - b ≢ 0ₚ
    -bnz = (-' (b , λ ())) .proj₂

    b⁻¹ = (b , λ ()) ⁻¹
    -b⁻¹ = -' b⁻¹

    x = -b⁻¹ .proj₁
    -x = b⁻¹ .proj₁
    x⁻¹ =  _⁻¹ -b⁻¹ .proj₁

    mc = -b⁻¹ , ε
    
    claim1 : act ⟦ mc ⟧ₘ₊ (p ∷ t) ≡ -pZ ∷ t
    claim1 = begin
      act ⟦ mc ⟧ₘ₊ (p ∷ t) ≡⟨ auto ⟩
      act ((S^ x • H • S^ x⁻¹ • H • S^ x • H) • ε) (p ∷ t) ≡⟨ auto ⟩
      act ((S^ x • H • S^ x⁻¹ • H • S^ x • H)) (p ∷ t) ≡⟨ auto ⟩
      act ((S^ x • H • S^ x⁻¹ • H • S^ x • H)) (p ∷ t) ≡⟨ auto ⟩
      (act (S^ x • H • S^ x⁻¹ • H • S^ x • H) (p ∷ t)) ≡⟨ (lemma-M (p .proj₁) (p .proj₂) t (-' b⁻¹)) ⟩
      ((₀ * x⁻¹ , b * x) ∷ t) ≡⟨ cong (\ xx ->  ((₀ , xx) ∷ t)) (*-comm b x) ⟩
      ((₀ , x * b) ∷ t) ≡⟨ cong (\ xx ->  ((₀ , xx * b) ∷ t)) (aux-'x=-x b⁻¹) ⟩
      ((₀ , - (-x) * b) ∷ t) ≡⟨ cong (\ xx ->  ((₀ , xx) ∷ t)) (sym (-‿distribˡ-* -x b)) ⟩
      ((₀ , - (-x * b)) ∷ t) ≡⟨ cong (\ xx ->  ((₀ , - xx) ∷ t)) ((lemma-⁻¹ˡ b {{nztoℕ {y = b} {neq0 = λ ()}}})) ⟩
      -pZ ∷ t ∎


  Theorem-MC-pZ p@(a@(₁₊ _) , b) t eq = mc , claim1
    where
    open ≡-Reasoning
    
    a⁻¹ = (a , λ ()) ⁻¹
    1/a = a⁻¹ .proj₁
    -b/a = - b * 1/a
    x = (-' a⁻¹) .proj₁
    x⁻¹ = ((-' a⁻¹) ⁻¹) .proj₁

    mc = -' a⁻¹ , HS^ -b/a
    p' = act (H • S^ -b/a) (p ∷ t)
    
    claim1 : act ⟦ mc ⟧ₘ₊ (p ∷ t) ≡ -pZ ∷ t
    claim1 = begin
      act ⟦ mc ⟧ₘ₊ (p ∷ t) ≡⟨ auto ⟩
      act ((S^ x • H • S^ x⁻¹ • H • S^ x • H) • (H • S^ -b/a)) (p ∷ t) ≡⟨ auto ⟩
      act ((S^ x • H • S^ x⁻¹ • H • S^ x • H)) p' ≡⟨ auto ⟩
      act ((S^ x • H • S^ x⁻¹ • H • S^ x • H)) p' ≡⟨ auto ⟩
      (act (S^ x • H • S^ x⁻¹ • H • S^ x • H) p') ≡⟨ cong (\ xx -> (act (S^ x • H • S^ x⁻¹ • H • S^ x • H) xx)) (lemma-HS a b t (λ ())) ⟩
      (act (S^ x • H • S^ x⁻¹ • H • S^ x • H) ((₀ , a) ∷ t)) ≡⟨ (lemma-M (₀) (a) t (-' a⁻¹)) ⟩
      ((₀ * x⁻¹ , a * x ) ∷ t) ≡⟨ cong (\ xx -> ((₀ , a * xx ) ∷ t)) (aux-'x=-x a⁻¹) ⟩
      ((₀ * x⁻¹ , a * - 1/a ) ∷ t) ≡⟨ cong (\ xx -> ((₀ , xx ) ∷ t)) (Eq.sym (-‿distribʳ-* a 1/a)) ⟩
      ((₀ * x⁻¹ , - (a * 1/a) ) ∷ t) ≡⟨ cong (\ xx -> ((₀ , - xx ) ∷ t)) ((lemma-⁻¹ʳ a {{nztoℕ {y = a} {neq0 = λ ()}}}) ) ⟩
      ((₀ * x⁻¹ , - ₁ ) ∷ t) ≡⟨ auto ⟩
      ((₀ , - ₁ ) ∷ t) ≡⟨ auto ⟩
      -pZ ∷ t ∎
      
 --(lemma-⁻¹ʳ a {{nztoℕ {y = a} {neq0 = λ ()}}}) ⟩


  aux-NF1 :

    ∀ (p q : Pauli1) (t t' : Pauli n) ->
    (eq : sform1 p q ≡ ₁) ->
    -----------------------------------------------------
    Theorem-NF1 p q t eq .proj₁ ≡ Theorem-NF1 p q t' eq .proj₁

  aux-NF1 (₀ , ₀) q t t' eq with 0ₚ≢1ₚ (Eq.trans (Eq.sym (sform-pI-q=0 q)) (eq))
  ... | ()
  aux-NF1 (₀ , ₁₊ snd) q t t' eq = auto
  aux-NF1 (₁₊ fst , snd) q t t' eq = auto





  Theorem-MC-+pZp :

    ∀ (p q : Pauli1) (t : Pauli n) ->
    p ≢ (₀ , ₀) ->
    -------------------------------
    ∃ \ mc -> ∃ \ e ->
      act {₁₊ n} ⟦ mc ⟧ₘ₊ (p ∷ t) ≡ pZ ∷ t ×
      act {₁₊ n} ⟦ mc ⟧ₘ₊ (q ∷ t) ≡ (sform1 p q , e) ∷ t

  Theorem-MC-+pZp {n} p@((₀ , ₀)) q@(q1) t eq with eq Eq.refl
  ... | ()


  Theorem-MC-+pZp {n} p@((₀ , b@(₁₊ b'))) q@((c , d)) t eq = mc , (d * x) , (claim1 , claim2)
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

    mc = b⁻¹ , ε
    
    claim1 : act ⟦ mc ⟧ₘ₊ (p ∷ t) ≡ pZ ∷ t
    claim1 = begin
      act ⟦ mc ⟧ₘ₊ (p ∷ t) ≡⟨ auto ⟩
      act ((S^ x • H • S^ x⁻¹ • H • S^ x • H) • ε) (p ∷ t) ≡⟨ auto ⟩
      act ((S^ x • H • S^ x⁻¹ • H • S^ x • H)) (p ∷ t) ≡⟨ auto ⟩
      act ((S^ x • H • S^ x⁻¹ • H • S^ x • H)) (p ∷ t) ≡⟨ auto ⟩
       (act (S^ x • H • S^ x⁻¹ • H • S^ x • H) (p ∷ t)) ≡⟨ (lemma-M (p .proj₁) (p .proj₂) t b⁻¹) ⟩
       ((₀ * x⁻¹ , b * x) ∷ t) ≡⟨ cong (\ xx ->  ((₀ , xx) ∷ t)) (*-comm b x) ⟩
       ((₀ , x * b ) ∷ t) ≡⟨ cong (\ xx ->  ((₀ , xx) ∷ t)) (lemma-⁻¹ˡ b {{nztoℕ {y = b} {neq0 = λ ()}}}) ⟩
      pZ ∷ t ∎

    cb=1 : c * b ≡ sform1 p q
    cb=1 = begin
      c * b ≡⟨ *-comm c b ⟩
      b * c ≡⟨ sym (sform-0b b c d) ⟩
      sform1 p q ∎
      
    claim2 : act {₁₊ n} ⟦ mc ⟧ₘ₊ (q ∷ t) ≡ ((sform1 p q , d * x ) ∷ t)
    claim2 = begin
      act ⟦ mc ⟧ₘ₊ (q ∷ t) ≡⟨ (lemma-M c d t b⁻¹) ⟩ 
       ((c * x⁻¹ , d * x ) ∷ t) ≡⟨ cong (\ xx ->  ((c * xx , d * x ) ∷ t)) (inv-involutive ((b , λ ()))) ⟩
       ((c * b , d * x ) ∷ t) ≡⟨ cong (\ xx ->  ((xx , d * x ) ∷ t)) cb=1 ⟩
       ((sform1 p q , d * x ) ∷ t) ∎

  Theorem-MC-+pZp p@(a@(₁₊ _) , b) q@(c , d) t eq = mc , c * x , claim1 , claim2
    where
    open ≡-Reasoning
    
    a⁻¹ = (a , λ ()) ⁻¹
    1/a = a⁻¹ .proj₁
    -b/a = - b * 1/a
    x = 1/a
    x⁻¹ = (a⁻¹ ⁻¹) .proj₁
    -c/a = - c * 1/a

    mc = a⁻¹ , HS^ -b/a
    p' = act (H • S^ -b/a) (p ∷ t)
    
    claim1 : act ⟦ mc ⟧ₘ₊ (p ∷ t) ≡ pZ ∷ t
    claim1 = begin
      act ⟦ mc ⟧ₘ₊ (p ∷ t) ≡⟨ auto ⟩
      act ((S^ x • H • S^ x⁻¹ • H • S^ x • H) • (H • S^ -b/a)) (p ∷ t) ≡⟨ auto ⟩
      act ((S^ x • H • S^ x⁻¹ • H • S^ x • H)) p' ≡⟨ auto ⟩
      act ((S^ x • H • S^ x⁻¹ • H • S^ x • H)) p' ≡⟨ auto ⟩
      (act (S^ x • H • S^ x⁻¹ • H • S^ x • H) p') ≡⟨ cong (\ xx -> (act (S^ x • H • S^ x⁻¹ • H • S^ x • H) xx)) (lemma-HS a b t (λ ())) ⟩
      (act (S^ x • H • S^ x⁻¹ • H • S^ x • H) ((₀ , a) ∷ t)) ≡⟨ (lemma-M (₀) (a) t a⁻¹) ⟩
      ((₀ * x⁻¹ , a * x ) ∷ t) ≡⟨ cong (\ xx -> ((₀ , xx ) ∷ t)) (lemma-⁻¹ʳ a {{nztoℕ {y = a} {neq0 = λ ()}}}) ⟩
      ((₀ , ₁ ) ∷ t) ≡⟨ auto ⟩
      ((₀ , ₁ + ₀ * -c/a ) ∷ t) ≡⟨ auto ⟩
      pZ ∷ t ∎


    q' = act (H • S^ -b/a) (q ∷ t)

    aux-dca : - (d + c * -b/a) * a ≡ sform1 p q
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
      - a * d + (c * b) ∎

    claim2 : act ⟦ mc ⟧ₘ₊ (q ∷ t) ≡ ((sform1 p q , c * x)) ∷ t
    claim2 = begin
      act ⟦ mc ⟧ₘ₊ (q ∷ t) ≡⟨ auto ⟩
      act ((S^ x • H • S^ x⁻¹ • H • S^ x • H)) ((- (d + c * -b/a) , c) ∷ t) ≡⟨ (lemma-M (- (d + c * -b/a)) c t a⁻¹) ⟩
      ((- (d + c * -b/a) * x⁻¹ , c * x ) ∷ t) ≡⟨ cong (\ xx -> ((- (d + c * -b/a) * xx , c * x ) ∷ t)) (inv-involutive (a , (λ ()))) ⟩
      ((- (d + c * -b/a) * a , c * x ) ∷ t) ≡⟨ cong (\ xx -> ((xx , c * x ) ∷ t)) aux-dca ⟩
      ((sform1 p q , c * x) ∷ t) ∎


  aux-MC :

    ∀ (p q : Pauli1) (t t' : Pauli n) ->
    (eq : p ≢ (₀ , ₀)) ->
    ------------------------------------------------------------------
    Theorem-MC-+pZp p q t eq .proj₁ ≡ Theorem-MC-+pZp p q t' eq .proj₁

  aux-MC (₀ , ₀) q t t' eq with eq Eq.refl
  ... | ()
  aux-MC (₀ , ₁₊ snd) q t t' eq = auto
  aux-MC (₁₊ fst , snd) q t t' eq = auto


