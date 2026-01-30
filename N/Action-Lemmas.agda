{-# OPTIONS  --safe #-}
{-# OPTIONS  --call-by-name #-}
{-# OPTIONS --termination-depth=3 #-}
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
open import Data.Fin.Properties as FP using (suc-injective ; toℕ-inject₁ ; toℕ-fromℕ)
import Data.Nat.Properties as NP
open import Presentation.GroupLike
open import Presentation.Tactics hiding ([_])
open import Data.Nat.Primality



module N.Action-Lemmas (p-2 : ℕ) (p-prime : Prime (2+ p-2))  where

pattern auto = Eq.refl

pattern ₀ = zero
pattern ₁ = suc ₀
pattern ₂ = suc ₁
pattern ₃ = suc ₂
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
open import N.Action p-2 p-prime 
open import N.NF1 p-2 p-prime
open Normal-Form1


open Symplectic-Derived-Gen
open import N.Pauli p-2 p-prime hiding (cong₃)
open import Data.Nat.DivMod
open import Data.Fin.Properties
open import Algebra.Properties.Ring (+-*-ring p-2)
open Eq

--     - (- (- b + (b' + a'')) + (- b + a''))
aux2o : ∀ a' a'' -> - (- (- a' + - a'') + - a') + - (- a' + - a'') ≡ a'
aux2o a' a'' = begin
  - (- (- a' + - a'') + - a') + - (- a' + - a'') ≡⟨ cong (_+ - (- a' + - a'')) (sym (-‿+-comm (- (- a' + - a'')) (- a'))) ⟩
  (- - (- a' + - a'') + - - a') + - (- a' + - a'') ≡⟨ cong (_+ - (- a' + - a'')) (+-comm (- - (- a' + - a'')) (- - a')) ⟩
  (- - a' + - - (- a' + - a'')) + - (- a' + - a'') ≡⟨ +-assoc (- - a') (- - (- a' + - a'')) (- (- a' + - a'')) ⟩
  - - a' + (- - (- a' + - a'') + - (- a' + - a'')) ≡⟨ cong (- - a' +_) (+-inverseˡ (- (- a' + - a''))) ⟩
  - - a' + ₀ ≡⟨ +-identityʳ (- - a') ⟩
  - - a' ≡⟨ -‿involutive a' ⟩
  a' ∎
  where
  open ≡-Reasoning



 -- --- - (- (- a' + - a) + - a') + - (- a' + - a)
aux30 : ∀ b'' b' a ->  - (- (- b'' + (b' + a)) + (- b'' + a)) ≡ b'
aux30 b'' b' a = begin
  - (- (- b'' + (b' + a)) + (- b'' + a)) ≡⟨ (sym (-‿+-comm (- (- b'' + (b' + a))) ((- b'' + a)))) ⟩
  - - (- b'' + (b' + a)) + - (- b'' + a) ≡⟨ cong (_+ - (- b'' + a)) (-‿involutive ((- b'' + (b' + a)))) ⟩
  (- b'' + (b' + a)) + - (- b'' + a) ≡⟨ cong (_+ - (- b'' + a)) (sym (+-assoc (- b'') b' a)) ⟩
  (- b'' + b' + a) + - (- b'' + a) ≡⟨ cong (_+ - (- b'' + a)) (trans (cong (_+ a)  (+-comm (- b'') b')) (+-assoc b' (- b'') a)) ⟩
  b' + (- b'' + a) + - (- b'' + a) ≡⟨ +-assoc b' ((- b'' + a)) (- (- b'' + a)) ⟩
  b' + ((- b'' + a) + - (- b'' + a)) ≡⟨ cong (b' +_) (+-inverseʳ ((- b'' + a))) ⟩
  b' + ₀ ≡⟨ +-identityʳ b' ⟩
  b' ∎
  where
  open ≡-Reasoning
  
    -- -              - (- (- b + (b' + a'')) + (- b + a'')) + (- (- b + (b' + a'')) + a'')
aux5o : ∀ b'' b' a -> - (- (- b'' + (b' + a)) + (- b'' + a)) + (- (- b'' + (b' + a)) + a) ≡ b''
aux5o b'' b' a = begin
  - (- (- b'' + (b' + a)) + (- b'' + a)) + (- (- b'' + (b' + a)) + a) ≡⟨ cong (_+ (- (- b'' + (b' + a)) + a)) (sym (-‿+-comm (- (- b'' + (b' + a))) ((- b'' + a)))) ⟩
  (- - (- b'' + (b' + a)) + - (- b'' + a)) + (- (- b'' + (b' + a)) + a) ≡⟨ cong (_+ (- (- b'' + (b' + a)) + a)) (+-comm (- - (- b'' + (b' + a))) (- (- b'' + a))) ⟩
  (- (- b'' + a) + - - (- b'' + (b' + a))) + (- (- b'' + (b' + a)) + a) ≡⟨ trans (+-assoc (- (- b'' + a)) (- - (- b'' + (b' + a))) ((- (- b'' + (b' + a)) + a))) (cong (- (- b'' + a) +_) (sym (+-assoc (- - (- b'' + (b' + a))) (- (- b'' + (b' + a))) a))) ⟩
  - (- b'' + a) + ((- - (- b'' + (b' + a)) + - (- b'' + (b' + a))) + a) ≡⟨ cong (\ xx -> - (- b'' + a) + (xx + a)) (+-inverseˡ (- (- b'' + (b' + a)))) ⟩
  - (- b'' + a) + (₀ + a) ≡⟨ cong₂ _+_ (sym (-‿+-comm (- b'') a)) (+-identityˡ a) ⟩
  - - b'' + - a + a ≡⟨ +-assoc (- - b'') (- a) a ⟩
  - - b'' + (- a + a) ≡⟨ cong₂ _+_ (-‿involutive b'') (+-inverseˡ a) ⟩
  b'' + ₀ ≡⟨ +-identityʳ b'' ⟩
  b'' ∎
  where
  open ≡-Reasoning


aux40b : ∀ a' a'' -> - (- a' + - a'') + - a' ≡ a''
aux40b a' a'' = begin
  - (- a' + - a'') + - a' ≡⟨ cong (_+ - a') (sym (-‿+-comm (- a') (- a''))) ⟩
  (- - a' + - - a'') + - a' ≡⟨ cong (_+ - a') (+-comm (- - a') (- - a'')) ⟩
  (- - a'' + - - a') + - a' ≡⟨ +-assoc (- - a'') (- - a') (- a') ⟩
  - - a'' + (- - a' + - a') ≡⟨ cong (- - a'' +_) (+-inverseˡ (- a')) ⟩
  - - a'' + ₀ ≡⟨ +-identityʳ (- - a'') ⟩
  - - a'' ≡⟨ -‿involutive a'' ⟩
  a'' ∎
  where
  open ≡-Reasoning


aux4ag : ∀ b a b' a' -> (b + a * - ₁) + - (b' + a' * - ₁) ≡ (b + a') + - (b' + a) * ₁
aux4ag b a b' a' = begin
  (b + a * - ₁) + - (b' + a' * - ₁) ≡⟨ Eq.cong₂ _+_ (Eq.cong (b +_) (Eq.trans (*-comm a (- ₁)) (-1*x≈-x a))) (Eq.sym (-‿+-comm b' (a' * - ₁))) ⟩
  (b + - a) + (- b' + - (a' * - ₁)) ≡⟨ Eq.cong (\ xx -> (b + - a) + (- b' + xx)) (-‿distribʳ-* a' (- ₁)) ⟩
  (b + - a) + (- b' + (a' * - - ₁)) ≡⟨ Eq.cong (λ xx → b + - a + (- b' + a' * xx)) (-‿involutive ₁) ⟩
  (b + - a) + (- b' + (a' * ₁)) ≡⟨ Eq.cong (λ xx → b + - a + (- b' + xx)) (*-identityʳ a') ⟩
  (b + - a) + (- b' + (a')) ≡⟨ Eq.cong ((b + - a) +_) (+-comm (- b') a') ⟩
  b + - a + (a' + - b') ≡⟨ +-assoc b (- a) ((a' + - b')) ⟩
  b + (- a + (a' + - b')) ≡⟨ Eq.cong (b +_) (Eq.sym (+-assoc (- a) a' (- b'))) ⟩
  b + (- a + a' + - b') ≡⟨ Eq.cong (b +_) (Eq.cong (_+ - b') (+-comm (- a) a')) ⟩
  b + (a' + - a + - b') ≡⟨ Eq.cong (b +_) (+-assoc a' (- a) (- b')) ⟩
  b + (a' + (- a + - b')) ≡⟨ Eq.sym (+-assoc b a' (- a + - b')) ⟩
  (b + a') + (- a + - b') ≡⟨ Eq.cong ((b + a') +_) (+-comm (- a) (- b')) ⟩
  (b + a') + (- b' + - a) ≡⟨ Eq.cong (b + a' +_) (-‿+-comm b' a) ⟩
  (b + a') + - (b' + a) ≡⟨ Eq.cong (b + a' +_) (Eq.sym (*-identityʳ (- (b' + a)))) ⟩
  (b + a') + - (b' + a) * ₁ ∎
  where
  open ≡-Reasoning


aux4c : ∀ b' a' a ->  - (b' + a' * - ₁) + - ((a' + a) + - (b' + a' * - ₁) * - ₁) * - ₁ ≡ a' + a * ₁
aux4c b' a' a = begin
  - (b' + a' * - ₁) + - ((a' + a) + - (b' + a' * - ₁) * - ₁) * - ₁ ≡⟨ cong (- (b' + a' * - ₁) +_) (Eq.trans (*-comm (- ((a' + a) + - (b' + a' * - ₁) * - ₁)) (- ₁)) (-1*x≈-x (- ((a' + a) + - (b' + a' * - ₁) * - ₁)))) ⟩
  - (b' + a' * - ₁) + - - ((a' + a) + - (b' + a' * - ₁) * - ₁) ≡⟨ cong (- (b' + a' * - ₁) +_) (-‿involutive (((a' + a) + - (b' + a' * - ₁) * - ₁))) ⟩
  - (b' + a' * - ₁) + ((a' + a) + - (b' + a' * - ₁) * - ₁) ≡⟨ cong (- (b' + a' * - ₁) +_) (cong ((a' + a) +_) (Eq.trans (*-comm (- (b' + a' * - ₁)) (- ₁)) (-1*x≈-x (- (b' + a' * - ₁))))) ⟩
  - (b' + a' * - ₁) + ((a' + a) + - - (b' + a' * - ₁)) ≡⟨ cong (- (b' + a' * - ₁) +_) (cong ((a' + a) +_) (-‿involutive ((b' + a' * - ₁)))) ⟩
  - (b' + a' * - ₁) + ((a' + a) + (b' + a' * - ₁)) ≡⟨ cong (- (b' + a' * - ₁) +_) (+-comm (a' + a) (b' + a' * - ₁)) ⟩
  - (b' + a' * - ₁) + ((b' + a' * - ₁) + (a' + a)) ≡⟨ sym (+-assoc (- (b' + a' * - ₁)) ((b' + a' * - ₁)) (a' + a)) ⟩
  - (b' + a' * - ₁) + (b' + a' * - ₁) + (a' + a) ≡⟨ cong (_+ (a' + a)) (+-inverseˡ ((b' + a' * - ₁))) ⟩
  ₀ + (a' + a) ≡⟨ +-identityˡ (a' + a) ⟩
  (a' + a) ≡⟨ Eq.cong (a' +_) (Eq.sym (*-identityʳ a)) ⟩
  a' + a * ₁ ∎
  where
  open ≡-Reasoning


--      - (- (- b + (b' + a'')) + (- b + a''))
aux30o : ∀ b'' b' a ->  - (- (- b'' + (b' + a)) + (- b'' + a)) ≡ b'
aux30o b'' b' a = begin
  - (- (- b'' + (b' + a)) + (- b'' + a)) ≡⟨ (sym (-‿+-comm (- (- b'' + (b' + a))) ((- b'' + a)))) ⟩
  - - (- b'' + (b' + a)) + - (- b'' + a) ≡⟨ cong (_+ - (- b'' + a)) (-‿involutive ((- b'' + (b' + a)))) ⟩
  (- b'' + (b' + a)) + - (- b'' + a) ≡⟨ cong (_+ - (- b'' + a)) (sym (+-assoc (- b'') b' a)) ⟩
  (- b'' + b' + a) + - (- b'' + a) ≡⟨ cong (_+ - (- b'' + a)) (trans (cong (_+ a)  (+-comm (- b'') b')) (+-assoc b' (- b'') a)) ⟩
  b' + (- b'' + a) + - (- b'' + a) ≡⟨ +-assoc b' ((- b'' + a)) (- (- b'' + a)) ⟩
  b' + ((- b'' + a) + - (- b'' + a)) ≡⟨ cong (b' +_) (+-inverseʳ ((- b'' + a))) ⟩
  b' + ₀ ≡⟨ +-identityʳ b' ⟩
  b' ∎
  where
  open ≡-Reasoning

--      ((b'' + a') + (- a' + - a)) + (- (- a' + - a) + - a')
aux1o : ∀ b a' a'' -> ((b + a') + (- a' + - a'')) + (- (- a' + - a'') + - a') ≡ b
aux1o b a' a''  = begin
  ((b + a') + (- a' + - a'')) + (- (- a' + - a'') + - a') ≡⟨ +-assoc ((b + a')) ((- a' + - a'')) (- (- a' + - a'') + - a') ⟩
  (b + a') + ((- a' + - a'') + (- (- a' + - a'') + - a')) ≡⟨ cong (b + a' +_) (sym (+-assoc ((- a' + - a'')) (- (- a' + - a'')) (- a'))) ⟩
  (b + a') + (((- a' + - a'') + - (- a' + - a'')) + - a') ≡⟨ cong ((b + a') +_) (cong (_+ - a') (+-inverseʳ ((- a' + - a'')))) ⟩
  (b + a') + (₀ + - a') ≡⟨ cong ((b + a') +_) (+-identityˡ (- a')) ⟩
  (b + a') + (- a') ≡⟨ +-assoc b a' (- a') ⟩
  b + (a' + - a') ≡⟨ cong (b +_) (+-inverseʳ {n = p} a') ⟩
  b + ₀ ≡⟨ +-identityʳ b ⟩
  b ∎
  where
  open ≡-Reasoning


lemma-act-cong-ax : ∀ {n} w v -> let open PB (n QRel,_===_) in

  w === v ->
  ----------------------------
  ∀ c -> act {n} w c ≡ act v c

lemma-act-cong-ax {n} w v order-S (x@(a , b) ∷ t) = begin
  act (S ^ p) ((a , b) ∷ t) ≡⟨ lemma-act-Sᵏ p ((a , b) ∷ t) ⟩
  act (S^ (fromℕ< (m%n<n p p))) ((a , b) ∷ t) ≡⟨ Eq.cong (\ xx -> act (S^ xx) ((a , b) ∷ t)) (FP.fromℕ<-cong (p Nat.% p) 0 (n%n≡0 p) (m%n<n p p) NP.0<1+n) ⟩
  act (S^ ₀) ((a , b) ∷ t) ≡⟨ auto ⟩
  ((a , b + a * ₀) ∷ t) ≡⟨ Eq.sym (Eq.cong (\ xx -> (a , xx) ∷ t) (Eq.sym (Eq.trans (Eq.cong (b +_) (*-zeroʳ a)) (+-identityʳ b)))) ⟩
  act ε ((a , b) ∷ t) ∎
  where
  open ≡-Reasoning

lemma-act-cong-ax {n} w v order-H (x@(a , b) ∷ t) = begin
  act (H • H • H • H) ((a , b) ∷ t) ≡⟨ auto ⟩
  act H (act H (act H (act H ((a , b) ∷ t)))) ≡⟨ auto ⟩
  act H (act H (act H (((- b , a) ∷ t)))) ≡⟨ auto ⟩
  act H (act H ((((- a , - b) ∷ t)))) ≡⟨ auto ⟩
  act H (((((- - b , - a) ∷ t)))) ≡⟨ auto ⟩
  (((((- - a , - - b) ∷ t)))) ≡⟨ Eq.cong₂ (\ xx yy -> (xx , yy) ∷ t) (-‿involutive a) (-‿involutive b) ⟩
  (((((a , b) ∷ t)))) ≡⟨ auto ⟩
  act ε ((a , b) ∷ t) ∎
  where
  open ≡-Reasoning

lemma-act-cong-ax {n} w v order-SH (x@(a , b) ∷ t) = begin
  act ((S • H) • (S • H) • S • H) ((a , b) ∷ t) ≡⟨ auto ⟩
  act (S • H) (act (S • H) (act (S • H) ((a , b) ∷ t))) ≡⟨ auto ⟩
  act (S • H) (act (S • H) (((- b , a + - b * ₁) ∷ t))) ≡⟨ Eq.cong (\ xx -> act (S • H) (act (S • H) (((- b , a + xx) ∷ t)))) (*-identityʳ (- b)) ⟩
  act (S • H) (act (S • H) (((- b , a + - b) ∷ t))) ≡⟨ auto ⟩
  act (S • H) ((((- (a + - b) , - b + - (a + - b) * ₁) ∷ t))) ≡⟨ Eq.cong₂ (\ xx yy -> act (S • H) ((((xx , yy) ∷ t)))) (aux-ab a b) (aux-ab1 a b) ⟩
  act (S • H) ((((- a + b , - a) ∷ t))) ≡⟨ auto ⟩
  (((( - - a , - a + b + - - a * ₁) ∷ t))) ≡⟨ Eq.cong₂ (\ xx yy -> ((xx , yy) ∷ t)) (-‿involutive a) (aux-aba a b) ⟩
  ((a , b) ∷ t) ≡⟨ auto ⟩
  act ε ((a , b) ∷ t) ∎
  where
  open ≡-Reasoning
  aux-ab : ∀ a b -> - (a + - b) ≡ - a + b
  aux-ab a b = Eq.trans (Eq.sym (-‿+-comm a (- b))) (Eq.cong (- a +_) (-‿involutive b))
  aux-ab1 : ∀ a b -> - b + - (a + - b) * 1ₚ ≡ - a
  aux-ab1 a b = begin
    - b + - (a + - b) * ₁ ≡⟨ Eq.cong (- b +_) (*-identityʳ (- (a + - b))) ⟩
    - b + - (a + - b) ≡⟨ Eq.cong (- b +_) (aux-ab a b) ⟩
    - b + (- a + b) ≡⟨ Eq.cong (- b +_) (+-comm (- a) b) ⟩
    - b + (b + - a) ≡⟨ Eq.sym (+-assoc (- b) b (- a)) ⟩
    - b + b + - a ≡⟨ Eq.cong (_+ - a) (+-inverseˡ b) ⟩
    ₀ + - a ≡⟨ +-identityˡ (- a) ⟩
    - a ∎
  aux-aba : ∀ a b -> - a + b + - - a * 1ₚ ≡ b
  aux-aba a b = begin
    - a + b + - - a * ₁ ≡⟨ Eq.cong (- a + b +_) (*-identityʳ (- - a)) ⟩
    - a + b + - - a ≡⟨ Eq.cong (- a + b +_) (-‿involutive a) ⟩
    - a + b + a ≡⟨ Eq.cong (_+ a) (+-comm (- a) b) ⟩
    b + - a + a ≡⟨ +-assoc b (- a) a ⟩
    b + (- a + a) ≡⟨ Eq.cong (b +_) (+-inverseˡ a) ⟩
    b + ₀ ≡⟨ +-identityʳ b ⟩
    b ∎


lemma-act-cong-ax {n} w v comm-HHS (x@(a , b) ∷ t) = begin
  act (H • H • S) ((a , b) ∷ t) ≡⟨ auto ⟩
  act H (act H (act S ((a , b) ∷ t))) ≡⟨ auto ⟩
  act H (act H (((a , b + a * ₁) ∷ t))) ≡⟨ Eq.cong (\ xx -> act H (act H (((a , b + xx) ∷ t)))) (*-identityʳ a) ⟩
  act H (act H (((a , b + a) ∷ t))) ≡⟨ auto ⟩
  act H ((((- (b + a) , a) ∷ t))) ≡⟨ auto ⟩
  ((((- a , - (b + a)) ∷ t))) ≡⟨ Eq.cong (\ xx -> ((- a , xx) ∷ t)) ((Eq.trans (Eq.sym (-‿+-comm b a)) (Eq.cong (- b +_) (Eq.sym (*-identityʳ (- a)))))) ⟩
  ((- a , - b + - a * ₁) ∷ t) ≡⟨ auto ⟩
  act S ((- a , - b) ∷ t) ≡⟨ auto ⟩
  act (S • H • H) ((a , b) ∷ t) ∎
  where
  open ≡-Reasoning



lemma-act-cong-ax {n} w v (M-mul z y) (x@(a , b) ∷ t) = begin
  act (M z • M y) ((a , b) ∷ t) ≡⟨ Eq.cong (act (M z)) (lemma-M a b t y) ⟩
  act (M z) ((a * y⁻¹ , b * y') ∷ t) ≡⟨ lemma-M (a * y⁻¹) (b * y') t z ⟩
  ((a * y⁻¹ * z⁻¹ , b * y' * z') ∷ t) ≡⟨ Eq.cong₂ (\ xx yy -> (xx , yy) ∷ t) (*-assoc a y⁻¹ z⁻¹) (*-assoc b y' z') ⟩
  ((a * (y⁻¹ * z⁻¹) , b * (y' * z')) ∷ t) ≡⟨ Eq.cong₂ (\ xx yy -> (xx , yy) ∷ t) (Eq.cong (a *_) (Eq.sym (Eq.trans (inv-distrib z y) (*-comm z⁻¹ y⁻¹)))) (Eq.cong (b *_) (*-comm y' z')) ⟩
  ((a * ((z *' y) ⁻¹).proj₁ , b * (z' * y')) ∷ t) ≡⟨ Eq.sym (lemma-M a b t (z *' y)) ⟩
  act (M (z *' y)) ((a , b) ∷ t) ∎
  where
  open ≡-Reasoning
  z' = z .proj₁
  z⁻¹ = (z ⁻¹) .proj₁
  y' = y .proj₁
  y⁻¹ = (y ⁻¹) .proj₁
lemma-act-cong-ax {n} w v (semi-MS y) (x@(a , b) ∷ t) = begin
  act (M y • S) ((a , b) ∷ t) ≡⟨ auto ⟩
  act (M y) ((a , b + a * ₁) ∷ t) ≡⟨ Eq.cong (\ xx -> act (M y) ((a , b + xx) ∷ t)) (*-identityʳ a) ⟩
  act (M y) ((a , b + a) ∷ t) ≡⟨ lemma-M a (b + a) t y ⟩
  ((a * y⁻¹ , (b + a) * y') ∷ t) ≡⟨ Eq.cong (\ xx -> ((a * y⁻¹ , xx) ∷ t)) (Eq.sym aux) ⟩
  ((a * y⁻¹ , (b * y') + (a * y⁻¹) * y²) ∷ t) ≡⟨ auto ⟩
  act (S^ (y ^2)) ((a * y⁻¹ , b * y') ∷ t) ≡⟨ Eq.sym (Eq.cong (\ xx -> act (S^ (y ^2)) xx) (lemma-M a b t y)) ⟩
  act (S^ (y ^2) • M y) ((a , b) ∷ t) ∎
  where
  open ≡-Reasoning
  y' = y .proj₁
  y⁻¹ = (y ⁻¹) .proj₁
  y² = y ^2
  aux : (b * y') + (a * y⁻¹) * y² ≡ (b + a) * y'
  aux = begin
    (b * y') + (a * y⁻¹) * y² ≡⟨ Eq.cong ((b * y') +_) (*-assoc a y⁻¹ y²) ⟩
    (b * y') + a * (y⁻¹ * y²) ≡⟨ Eq.cong (b * y' +_) (Eq.cong (a *_) (Eq.sym (*-assoc y⁻¹ y' y'))) ⟩
    (b * y') + a * (y⁻¹ * y' * y') ≡⟨ Eq.cong (b * y' +_) (Eq.cong (a *_) (Eq.cong (_* y') (lemma-⁻¹ˡ y' {{nztoℕ {y = y'} {neq0 = y .proj₂}}}))) ⟩
    (b * y') + a * (₁ * y') ≡⟨ Eq.cong (b * y' +_) (Eq.cong (a *_) (*-identityˡ y')) ⟩
    (b * y') + a * y' ≡⟨ Eq.sym (*-distribʳ-+ y' b a) ⟩
    (b + a) * y' ∎
  
lemma-act-cong-ax {n} w v (semi-M↑CZ y) (x@(a , b) ∷ (a' , b') ∷ t) = begin
  act ((M y ↑) • CZ) ((a , b) ∷ (a' , b') ∷ t) ≡⟨ auto ⟩
  act (M y ↑) ((a , b + a' * ₁) ∷ (a' , b' + a * ₁) ∷ t) ≡⟨ Eq.cong₂ (\ xx yy -> act (M y ↑) ((a , b + xx) ∷ (a' , b' + yy) ∷ t))  (*-identityʳ a') (*-identityʳ a) ⟩
  act (M y ↑) ((a , b + a') ∷ (a' , b' + a) ∷ t) ≡⟨ Eq.cong (\ xx -> ((a , b + a') ∷ xx)) (lemma-M a' (b' + a) t y) ⟩
  ((a , b + a') ∷ (a' * y⁻¹ , (b' + a) * y') ∷ t) ≡⟨ Eq.cong₂ (\ xx yy -> ((a , b + xx) ∷ (a' * y⁻¹ , yy) ∷ t)) (Eq.sym aux) (*-distribʳ-+ y' b' a) ⟩
  ((a , b + (a' * y⁻¹) * y') ∷ (a' * y⁻¹ , b' * y' + a * y') ∷ t) ≡⟨ auto ⟩
  act (CZ^ (y ^1)) ((a , b) ∷ (a' * y⁻¹ , b' * y') ∷ t) ≡⟨ Eq.cong (act (CZ^ (y ^1)) ) (Eq.sym (Eq.cong (\ xx -> (a , b) ∷ xx) (lemma-M a' b' t y))) ⟩
  act (CZ^ (y ^1) • (M y ↑)) ((a , b) ∷ (a' , b') ∷ t) ∎
  where
  open ≡-Reasoning
  y' = y .proj₁
  y⁻¹ = (y ⁻¹) .proj₁
  aux : (a' * y⁻¹) * y' ≡ a'
  aux = Eq.trans (Eq.trans (*-assoc a' y⁻¹ y') (Eq.cong (a' *_) (lemma-⁻¹ˡ y' {{nztoℕ {y = y'} {neq0 = y .proj₂}}}))) (*-identityʳ a')
  
lemma-act-cong-ax {n} w v (semi-M↓CZ y) (x@(a , b) ∷ (a' , b') ∷ t) = begin
  act ((M y ↓) • CZ) ((a , b) ∷ (a' , b') ∷ t) ≡⟨ auto ⟩
  act (M y ↓) ((a , b + a' * ₁) ∷ (a' , b' + a * ₁) ∷ t) ≡⟨ Eq.cong₂ (\ xx yy -> act (M y ↓) ((a , b + xx) ∷ (a' , b' + yy) ∷ t))  (*-identityʳ a') (*-identityʳ a) ⟩
  act (M y ↓) ((a , b + a') ∷ (a' , b' + a) ∷ t) ≡⟨ (lemma-M a (b + a') ((a' , b' + a) ∷ t) y) ⟩
  ((a * y⁻¹ , (b + a') * y') ∷ (a' , (b' + a)) ∷ t) ≡⟨ Eq.cong₂ (\ xx yy -> ((a * y⁻¹ , xx) ∷ (a' , (b' + yy)) ∷ t)) (*-distribʳ-+ y' b a') (Eq.sym aux) ⟩
  ((a * y⁻¹ , b * y' + a' * y') ∷ (a' , b' + (a * y⁻¹) * y') ∷ t) ≡⟨ auto ⟩
  act (CZ^ (y ^1)) ((a * y⁻¹ , b * y') ∷ (a' , b') ∷ t) ≡⟨ Eq.cong (act (CZ^ (y ^1)) ) (Eq.sym (lemma-M a b ((a' , b') ∷ t) y)) ⟩
  act (CZ^ (y ^1) • (M y ↓)) ((a , b) ∷ (a' , b') ∷ t) ∎
  where
  open ≡-Reasoning
  y' = y .proj₁
  y⁻¹ = (y ⁻¹) .proj₁
  aux : (a * y⁻¹) * y' ≡ a
  aux = Eq.trans (Eq.trans (*-assoc a y⁻¹ y') (Eq.cong (a *_) (lemma-⁻¹ˡ y' {{nztoℕ {y = y'} {neq0 = y .proj₂}}}))) (*-identityʳ a)


lemma-act-cong-ax {n} w v order-CZ (x@(a , b) ∷ (a' , b') ∷ t) = begin
  act (CZ ^ p) ((a , b) ∷ (a' , b') ∷ t) ≡⟨ lemma-act-CZᵏ p ((a , b) ∷ (a' , b') ∷ t) ⟩
  act (CZ^ (fromℕ< (m%n<n p p))) ((a , b) ∷ (a' , b') ∷ t) ≡⟨ Eq.cong (\ xx -> act (CZ^ xx) ((a , b) ∷ (a' , b') ∷ t)) (FP.fromℕ<-cong (p Nat.% p) 0 (n%n≡0 p) (m%n<n p p) NP.0<1+n) ⟩
  act (CZ^ ₀) ((a , b) ∷ (a' , b') ∷ t) ≡⟨ auto ⟩
  ((a , b + a' * ₀) ∷ (a' , b' + a * ₀) ∷ t) ≡⟨ Eq.sym (Eq.cong₂ (\ xx yy -> (a , xx) ∷ (a' , yy) ∷ t) (Eq.sym (Eq.trans (Eq.cong (b +_) (*-zeroʳ a')) (+-identityʳ b)))  (Eq.sym (Eq.trans (Eq.cong (b' +_) (*-zeroʳ a)) (+-identityʳ b')))) ⟩
  act ε ((a , b) ∷ (a' , b') ∷ t) ∎
  where
  open ≡-Reasoning


lemma-act-cong-ax {n} w v comm-CZ-S↓ (x@(a , b) ∷ (a' , b') ∷ t) = begin
  act (CZ • (S ↓)) ((a , b) ∷ (a' , b') ∷ t) ≡⟨ auto ⟩
  act (CZ) ((a , b + a * ₁) ∷ (a' , b') ∷ t) ≡⟨ Eq.cong (\ xx -> act (CZ) ((a , b + xx) ∷ (a' , b') ∷ t)) (*-identityʳ a) ⟩
  act (CZ) ((a , b + a) ∷ (a' , b') ∷ t) ≡⟨ auto ⟩
  ((a , (b + a) + a' * ₁) ∷ (a' , b' + a * ₁) ∷ t) ≡⟨ Eq.cong₂ (\ xx yy -> ((a , xx) ∷ (a' , b' + yy) ∷ t)) aux (*-identityʳ a) ⟩
  ((a , (b + a') + a * ₁) ∷ (a' , b' + a) ∷ t) ≡⟨ auto ⟩
  act (S ↓) ((a , b + a') ∷ (a' , b' + a) ∷ t) ≡⟨ Eq.cong₂ (\ xx yy -> act (S ↓) ((a , b + xx) ∷ (a' , b' + yy) ∷ t)) (Eq.sym (*-identityʳ a'))  (Eq.sym (*-identityʳ a)) ⟩
  act ((S ↓)) ((a , b + a' * ₁) ∷ (a' , b' + a * ₁) ∷ t) ≡⟨ auto ⟩
  act ((S ↓) • CZ) ((a , b) ∷ (a' , b') ∷ t) ∎
  where
  open ≡-Reasoning
  aux : (b + a) + a' * ₁ ≡ (b + a') + a * ₁
  aux = begin
    (b + a) + a' * ₁ ≡⟨ Eq.cong ((b + a) +_) (*-identityʳ a') ⟩
    (b + a) + a' ≡⟨ +-assoc b a a' ⟩
    b + (a + a') ≡⟨ Eq.cong (b +_) (+-comm a a') ⟩
    b + (a' + a) ≡⟨ Eq.sym (+-assoc b a' a) ⟩
    (b + a') + a ≡⟨ Eq.cong ((b + a') +_) (Eq.sym (*-identityʳ a)) ⟩
    (b + a') + a * ₁ ∎
lemma-act-cong-ax {n} w v comm-CZ-S↑ (x@(a , b) ∷ (a' , b') ∷ t) = begin
  act (CZ • (S ↑)) ((a , b) ∷ (a' , b') ∷ t) ≡⟨ auto ⟩
  act (CZ) ((a , b) ∷ (a' , b' + a' * ₁) ∷ t) ≡⟨ Eq.cong (\ xx -> act (CZ) ((a , b) ∷ (a' , b' + xx) ∷ t)) (*-identityʳ a') ⟩
  act (CZ) ((a , b) ∷ (a' , b' + a') ∷ t) ≡⟨ auto ⟩
  ((a , b + a' * ₁) ∷ (a' , (b' + a') + a * ₁) ∷ t) ≡⟨ Eq.cong₂ (\ xx yy -> ((a , b + xx) ∷ (a' , yy) ∷ t)) (*-identityʳ a') aux ⟩
  ((a , b + a') ∷ (a' , (b' + a) + a' * ₁) ∷ t) ≡⟨ auto ⟩
  act (S ↑) ((a , b + a') ∷ (a' , b' + a) ∷ t) ≡⟨ Eq.cong₂ (\ xx yy -> act (S ↑) ((a , b + xx) ∷ (a' , b' + yy) ∷ t)) (Eq.sym (*-identityʳ a'))  (Eq.sym (*-identityʳ a)) ⟩
  act ((S ↑)) ((a , b + a' * ₁) ∷ (a' , b' + a * ₁) ∷ t) ≡⟨ auto ⟩
  act ((S ↑) • CZ) ((a , b) ∷ (a' , b') ∷ t) ∎
  where
  open ≡-Reasoning
  aux : (b' + a') + a * ₁ ≡ (b' + a) + a' * ₁
  aux = begin
    (b' + a') + a * ₁ ≡⟨ Eq.cong ((b' + a') +_) (*-identityʳ a) ⟩
    (b' + a') + a ≡⟨ +-assoc b' a' a ⟩
    b' + (a' + a) ≡⟨ Eq.cong (b' +_) (+-comm a' a) ⟩
    b' + (a + a') ≡⟨ Eq.sym (+-assoc b' a a') ⟩
    (b' + a) + a' ≡⟨ Eq.cong ((b' + a) +_) (Eq.sym (*-identityʳ a')) ⟩
    (b' + a) + a' * ₁ ∎



lemma-act-cong-ax {n} w v selinger-c10 (x@(a , b) ∷ (a' , b') ∷ t) = begin
  act (CZ • (H ↑) • CZ) ((a , b) ∷ (a' , b') ∷ t) ≡⟨ auto ⟩
  act (CZ • (H ↑)) ((a , b + a' * ₁) ∷ (a' , b' + a * ₁) ∷ t) ≡⟨ Eq.cong₂ (\ xx yy -> act (CZ • (H ↑)) ((a , b + xx) ∷ (a' , b' + yy) ∷ t)) (*-identityʳ a') (*-identityʳ a) ⟩
  act (CZ • (H ↑)) ((a , b + a') ∷ (a' , b' + a) ∷ t) ≡⟨ auto ⟩
  act (CZ) ((a , b + a') ∷ (- (b' + a) , a') ∷ t) ≡⟨ auto ⟩
  ((a , (b + a') + - (b' + a) * ₁) ∷ (- (b' + a) , a' + a * ₁) ∷ t) ≡⟨ cong₃ (\ xx yy zz -> ((a , xx) ∷ (yy , zz) ∷ t)) (Eq.sym (aux4ag b a b' a')) (Eq.cong -_ (Eq.sym aux4b)) (Eq.sym (aux4c b' a' a)) ⟩
  ((a , (b + a * - ₁) + - (b' + a' * - ₁)) ∷ (- ((a' + a) + - (b' + a' * - ₁) * - ₁) , - (b' + a' * - ₁) + - ((a' + a) + - (b' + a' * - ₁) * - ₁) * - ₁ ) ∷ t) ≡⟨ cong₃ (\ xx yy zz -> ((a , (b + a * - ₁) + xx) ∷ (- ((a' + yy) + - (b' + a' * - ₁) * - ₁) , - (b' + a' * - ₁) + - ((a' + zz) + - (b' + a' * - ₁) * - ₁) * - ₁ ) ∷ t)) (Eq.sym (*-identityʳ (- (b' + a' * - ₁)))) (Eq.sym (*-identityʳ a)) (Eq.sym (*-identityʳ a)) ⟩
  ((a , (b + a * - ₁) + - (b' + a' * - ₁) * ₁) ∷ (- ((a' + a * ₁) + - (b' + a' * - ₁) * - ₁) , - (b' + a' * - ₁) + - ((a' + a * ₁) + - (b' + a' * - ₁) * - ₁) * - ₁ ) ∷ t) ≡⟨ Eq.cong (\ xx -> ((a , (b + a * xx) + - (b' + a' * xx) * ₁) ∷ (- ((a' + a * ₁) + - (b' + a' * xx) * xx) , - (b' + a' * xx) + - ((a' + a * ₁) + - (b' + a' * xx) * xx) * xx ) ∷ t)) (Eq.sym aux2) ⟩
  ((a , (b + a * p-1') + - (b' + a' * p-1') * ₁) ∷ (- ((a' + a * ₁) + - (b' + a' * p-1') * p-1') , - (b' + a' * p-1') + - ((a' + a * ₁) + - (b' + a' * p-1') * p-1') * p-1' ) ∷ t) ≡⟨ Eq.sym (Eq.trans (lemma-act-↑ S⁻¹ ((a , (b + a * p-1') + - (b' + a' * p-1') * ₁)) ((- ((a' + a * ₁) + - (b' + a' * p-1') * p-1') , - (b' + a' * p-1') ) ∷ t)) (Eq.cong ((a , (b + a * p-1') + - (b' + a' * p-1') * ₁) ∷_) (lemma-act-Sᵏ p-1 ((- (a' + a * ₁ + - (b' + a' * p-1') * p-1') , - (b' + a' * p-1')) ∷ t)))) ⟩
  act (S⁻¹ ↑) ((a , (b + a * p-1') + - (b' + a' * p-1') * ₁) ∷ (- ((a' + a * ₁) + - (b' + a' * p-1') * p-1') , - (b' + a' * p-1') ) ∷ t) ≡⟨ auto ⟩
  act ((S⁻¹ ↑) • (H ↑)) ((a , (b + a * p-1') + - (b' + a' * p-1') * ₁) ∷ (- (b' + a' * p-1') , (a' + a * ₁) + - (b' + a' * p-1') * p-1') ∷ t) ≡⟨ Eq.sym (Eq.cong (act ((S⁻¹ ↑) • (H ↑))) (Eq.trans (lemma-act-↑ S⁻¹ ((a , (b + a * p-1') + - (b' + a' * p-1') * ₁)) ((- (b' + a' * p-1') , a' + a * ₁) ∷ t)) (Eq.cong ((a , (b + a * p-1') + - (b' + a' * p-1') * ₁) ∷_) (lemma-act-Sᵏ p-1 ((- (b' + a' * p-1') , a' + a * ₁) ∷ t))))) ⟩
  act ((S⁻¹ ↑) • (H ↑) • (S⁻¹ ↑)) ((a , (b + a * p-1') + - (b' + a' * p-1') * ₁) ∷ (- (b' + a' * p-1') , a' + a * ₁) ∷ t) ≡⟨ auto ⟩
  act ((S⁻¹ ↑) • (H ↑) • (S⁻¹ ↑) • CZ) ((a , b + a * p-1') ∷ (- (b' + a' * p-1') , a') ∷ t) ≡⟨ auto ⟩
  act ((S⁻¹ ↑) • (H ↑) • (S⁻¹ ↑) • CZ • (H ↑)) ((a , b + a * p-1') ∷ (a' , b' + a' * p-1') ∷ t) ≡⟨ Eq.cong (act ((S⁻¹ ↑) • (H ↑) • (S⁻¹ ↑) • CZ • (H ↑))) (Eq.sym (Eq.trans (lemma-act-↑ S⁻¹ ((a , b + a * p-1')) ((a' , b') ∷ t)) (Eq.cong ((a , b + a * p-1') ∷_) (lemma-act-Sᵏ p-1 ((a' , b') ∷ t))))) ⟩
  act ((S⁻¹ ↑) • (H ↑) • (S⁻¹ ↑) • CZ • (H ↑) • (S⁻¹ ↑)) ((a , b + a * p-1') ∷ (a' , b') ∷ t) ≡⟨ Eq.cong (act ((S⁻¹ ↑) • (H ↑) • (S⁻¹ ↑) • CZ • (H ↑) • (S⁻¹ ↑))) (Eq.sym (lemma-act-Sᵏ p-1 ((a , b) ∷ (a' , b') ∷ t))) ⟩
  act ((S⁻¹ ↑) • (H ↑) • (S⁻¹ ↑) • CZ • (H ↑) • (S⁻¹ ↑) • (S⁻¹ ↓)) ((a , b) ∷ (a' , b') ∷ t) ∎
  where
  open ≡-Reasoning
  p-1' = fromℕ< (m%n<n (p-1) p)
  aux1 : p-1' ≡ ₚ₋₁
  aux1 = fromℕ<-cong ((p-1) Nat.% p) p-1 (m<n⇒m%n≡m (NP.≤-refl {p})) (m%n<n (p-1) p) (NP.≤-refl {p})
  aux2 : p-1' ≡ - ₁
  aux2 = Eq.trans aux1 p-1=-1ₚ

  aux4b : ((a' + a) + - (b' + a' * - ₁) * - ₁) ≡ (b' + a)
  aux4b = begin
    ((a' + a) + - (b' + a' * - ₁) * - ₁) ≡⟨ Eq.cong ((a' + a) +_) (Eq.trans (*-comm (- (b' + a' * - ₁)) (- ₁)) (-1*x≈-x (- (b' + a' * - ₁)))) ⟩
    ((a' + a) + - - (b' + a' * - ₁)) ≡⟨ Eq.cong ((a' + a) +_) (-‿involutive ((b' + a' * - ₁))) ⟩
    ((a' + a) + (b' + a' * - ₁)) ≡⟨ Eq.cong (\ xx -> (a' + a) + (b' + xx)) (Eq.trans (*-comm a' (- ₁)) (-1*x≈-x a')) ⟩
    ((a' + a) + (b' + - a')) ≡⟨ Eq.cong (a' + a +_) (+-comm b' (- a')) ⟩
    ((a' + a) + (- a' + b')) ≡⟨ Eq.trans (+-assoc a' a (- a' + b')) (Eq.cong (a' +_) (Eq.sym (+-assoc a (- a') b'))) ⟩
    a' + ((a + - a') + b') ≡⟨ Eq.cong (a' +_) (Eq.cong (_+ b') (+-comm a  (- a'))) ⟩
    a' + ((- a' + a) + b') ≡⟨ Eq.trans (Eq.cong (a' +_) (+-assoc (- a') a b')) (Eq.sym (+-assoc a' (- a') (a + b'))) ⟩
    a' + - a' + (a + b') ≡⟨ Eq.cong (_+ (a + b')) (+-inverseʳ a') ⟩
    ₀ + (a + b') ≡⟨ +-identityˡ (a + b') ⟩
    (a + b') ≡⟨ +-comm a b' ⟩
    (b' + a) ∎



lemma-act-cong-ax {n} w v selinger-c11 (x@(a , b) ∷ (a' , b') ∷ t) = begin
  act (CZ • (H ↓) • CZ) ((a , b) ∷ (a' , b') ∷ t) ≡⟨ auto ⟩
  act (CZ • (H ↓)) ((a , b + a' * ₁) ∷ (a' , b' + a * ₁) ∷ t) ≡⟨ Eq.cong₂ (\ xx yy -> act (CZ • (H ↓)) ((a , b + xx) ∷ (a' , b' + yy) ∷ t)) (*-identityʳ a') (*-identityʳ a) ⟩
  act (CZ • (H ↓)) ((a , b + a') ∷ (a' , b' + a) ∷ t) ≡⟨ auto ⟩
  act (CZ) ((- (b + a') , a) ∷ (a' , b' + a) ∷ t) ≡⟨ auto ⟩
  ((- (b + a') , a + a' * ₁) ∷ (a' , (b' + a) + - (b + a') * ₁) ∷ t) ≡⟨ cong₃ (\ xx yy zz -> ((xx , yy) ∷ (a' , zz) ∷ t)) (cong -_ (sym aux4a)) (sym aux4b) (sym aux4d) ⟩
  ((- ((a + a' * ₁) + - (b + a * - ₁) * - ₁) , - (b + a * - ₁) + - ((a + a' * ₁) + - (b + a * - ₁) * - ₁) * - ₁) ∷ (a' , (b' + a' * - ₁) + - (b + a * - ₁) * ₁) ∷ t) ≡⟨ cong (\ xx -> ((- ((a + a' * ₁) + - (b + a * xx) * xx) , - (b + a * xx) + - ((a + a' * ₁) + - (b + a * xx) * xx) * xx) ∷ (a' , (b' + a' * xx) + - (b + a * xx) * ₁) ∷ t)) (sym aux2) ⟩
  ((- ((a + a' * ₁) + - (b + a * p-1') * p-1') , - (b + a * p-1') + - ((a + a' * ₁) + - (b + a * p-1') * p-1') * p-1') ∷ (a' , (b' + a' * p-1') + - (b + a * p-1') * ₁) ∷ t) ≡⟨ sym (lemma-act-Sᵏ p-1 ((- (a + a' * ₁ + - (b + a * p-1') * p-1') , - (b + a * p-1')) ∷ (a' , b' + a' * p-1' + - (b + a * p-1') * ₁) ∷ t)) ⟩
  act ((S⁻¹ ↓)) ((- ((a + a' * ₁) + - (b + a * p-1') * p-1') , - (b + a * p-1')) ∷ (a' , (b' + a' * p-1') + - (b + a * p-1') * ₁) ∷ t) ≡⟨ auto ⟩
  act ((S⁻¹ ↓) • (H ↓)) ((- (b + a * p-1') , (a + a' * ₁) + - (b + a * p-1') * p-1') ∷ (a' , (b' + a' * p-1') + - (b + a * p-1') * ₁) ∷ t) ≡⟨ sym (cong (act ((S⁻¹ ↓) • (H ↓))) (lemma-act-Sᵏ p-1 ((- (b + a * p-1') , a + a' * ₁) ∷ (a' , b' + a' * p-1' + - (b + a * p-1') * ₁) ∷ t))) ⟩
  act ((S⁻¹ ↓) • (H ↓) • (S⁻¹ ↓)) ((- (b + a * p-1') , a + a' * ₁) ∷ (a' , (b' + a' * p-1') + - (b + a * p-1') * ₁) ∷ t) ≡⟨ auto ⟩
  act ((S⁻¹ ↓) • (H ↓) • (S⁻¹ ↓) • CZ) ((- (b + a * p-1') , a) ∷ (a' , b' + a' * p-1') ∷ t) ≡⟨ auto ⟩
  act ((S⁻¹ ↓) • (H ↓) • (S⁻¹ ↓) • CZ • (H ↓)) ((a , b + a * p-1') ∷ (a' , b' + a' * p-1') ∷ t) ≡⟨ cong (act ((S⁻¹ ↓) • (H ↓) • (S⁻¹ ↓) • CZ • (H ↓))) (sym (lemma-act-Sᵏ p-1 ((a , b) ∷ (a' , b' + a' * p-1') ∷ t))) ⟩
  act ((S⁻¹ ↓) • (H ↓) • (S⁻¹ ↓) • CZ • (H ↓) • (S⁻¹ ↓)) ((a , b) ∷ (a' , b' + a' * p-1') ∷ t) ≡⟨ cong (act ((S⁻¹ ↓) • (H ↓) • (S⁻¹ ↓) • CZ • (H ↓) • (S⁻¹ ↓))) (sym (trans (lemma-act-↑ S⁻¹ ((a , b)) ((a' , b') ∷ t)) (Eq.cong ((a , b) ∷_) (lemma-act-Sᵏ p-1 ((a' , b') ∷ t))))) ⟩
  act ((S⁻¹ ↓) • (H ↓) • (S⁻¹ ↓) • CZ • (H ↓) • (S⁻¹ ↓) • (S⁻¹ ↑)) ((a , b) ∷ (a' , b') ∷ t) ∎
  where
  open ≡-Reasoning
  p-1' = fromℕ< (m%n<n (p-1) p)
  aux1 : p-1' ≡ ₚ₋₁
  aux1 = fromℕ<-cong ((p-1) Nat.% p) p-1 (m<n⇒m%n≡m (NP.≤-refl {p})) (m%n<n (p-1) p) (NP.≤-refl {p})
  aux2 : p-1' ≡ - ₁
  aux2 = Eq.trans aux1 p-1=-1ₚ
  aux3a : ∀ x -> - x * - 1ₚ ≡ x
  aux3a x = trans (*-comm (- x) (- 1ₚ)) (trans (-1*x≈-x (- x)) (-‿involutive x))
  aux4a : ((a + a' * ₁) + - (b + a * - ₁) * - ₁) ≡ (b + a')
  aux4a = begin
    ((a + a' * ₁) + - (b + a * - ₁) * - ₁) ≡⟨ cong (\ xx -> ((a + a' * ₁) + xx)) (aux3a ((b + a * - ₁))) ⟩
    ((a + a' * ₁) + (b + a * - ₁)) ≡⟨ cong₂ _+_ (cong (a +_) (*-identityʳ a')) (cong (b +_) (trans (*-comm a (- ₁)) (-1*x≈-x a))) ⟩
    ((a + a') + (b + - a)) ≡⟨ cong₂ _+_ (+-comm a a') (+-comm b  (- a)) ⟩
    ((a' + a) + (- a + b)) ≡⟨ trans (+-assoc a' a (- a + b)) (cong (a' +_) (sym (+-assoc a (- a) b))) ⟩
    a' + ((a + - a) + b) ≡⟨ cong (a' +_) (cong (_+ b) (+-inverseʳ a)) ⟩
    a' + (₀ + b) ≡⟨ cong (a' +_) (+-identityˡ b) ⟩
    a' + b ≡⟨ +-comm a' b ⟩
    (b + a') ∎
  aux4b : - (b + a * - ₁) + - ((a + a' * ₁) + - (b + a * - ₁) * - ₁) * - ₁ ≡ a + a' * ₁
  aux4b = begin
    - (b + a * - ₁) + - ((a + a' * ₁) + - (b + a * - ₁) * - ₁) * - ₁ ≡⟨ cong (\ xx -> - (b + a * - ₁) + - ((a + xx) + - (b + a * - ₁) * - ₁) * - ₁ ) (*-identityʳ a') ⟩
    - (b + a * - ₁) + - ((a + a') + - (b + a * - ₁) * - ₁) * - ₁ ≡⟨ aux4c b a a' ⟩
    a + a' * ₁ ∎

  aux4d : (b' + a' * - ₁) + - (b + a * - ₁) * ₁ ≡ (b' + a) + - (b + a') * ₁
  aux4d = begin
    (b' + a' * - ₁) + - (b + a * - ₁) * ₁ ≡⟨ cong ((b' + a' * - ₁) +_) (*-identityʳ (- (b + a * - ₁))) ⟩
    (b' + a' * - ₁) + - (b + a * - ₁) ≡⟨ aux4ag b' a' b a ⟩
    (b' + a) + - (b + a') * ₁ ∎

lemma-act-cong-ax {n} w v selinger-c12 (x@(a , b) ∷ (a' , b') ∷ (a'' , b'') ∷ t) = begin
  act ((CZ ↑) • CZ) ((a , b) ∷ (a' , b') ∷ (a'' , b'') ∷ t) ≡⟨ auto ⟩
  act (CZ ↑) ((a , b + a' * ₁) ∷ (a' , b' + a * ₁) ∷ (a'' , b'') ∷ t) ≡⟨ Eq.cong₂ (\ xx yy -> act (CZ ↑) ((a , b + xx) ∷ (a' , b' + yy) ∷ (a'' , b'') ∷ t)) (*-identityʳ a') (*-identityʳ a) ⟩
  act (CZ ↑) ((a , b + a') ∷ (a' , b' + a) ∷ (a'' , b'') ∷ t) ≡⟨ auto ⟩
  ((a , b + a') ∷ (a' , (b' + a) + a'' * ₁) ∷ (a'' , b'' + a' * ₁) ∷ t) ≡⟨ cong₃ (\ xx yy zz -> ((a , b + xx) ∷ (a' , yy) ∷ (a'' , b'' + zz) ∷ t)) (Eq.sym (*-identityʳ a')) aux (*-identityʳ a') ⟩
  ((a , b + a' * ₁) ∷ (a' , (b' + a'') + a * ₁) ∷ (a'' , b'' + a') ∷ t) ≡⟨ auto ⟩
  act (CZ) ((a , b) ∷ (a' , b' + a'') ∷ (a'' , b'' + a') ∷ t) ≡⟨ Eq.sym (Eq.cong₂ (\ xx yy -> act (CZ) ((a , b) ∷ (a' , b' + xx) ∷ (a'' , b'' + yy) ∷ t)) (*-identityʳ a'') (*-identityʳ a')) ⟩
  act (CZ) ((a , b) ∷ (a' , b' + a'' * ₁) ∷ (a'' , b''  + a' * ₁) ∷ t) ≡⟨ auto ⟩
  act (CZ • (CZ ↑)) ((a , b) ∷ (a' , b') ∷ (a'' , b'') ∷ t) ∎
  where
  open ≡-Reasoning
  aux : (b' + a) + a'' * ₁ ≡ (b' + a'') + a * ₁
  aux = begin
    (b' + a) + a'' * ₁ ≡⟨ Eq.cong ((b' + a) +_) (*-identityʳ a'') ⟩
    (b' + a) + a'' ≡⟨ +-assoc b' a a'' ⟩
    b' + (a + a'') ≡⟨ Eq.cong (b' +_) (+-comm a a'') ⟩
    b' + (a'' + a) ≡⟨ Eq.sym (+-assoc b' a'' a) ⟩
    (b' + a'') + a ≡⟨ Eq.cong ((b' + a'') +_) (Eq.sym (*-identityʳ a)) ⟩
    (b' + a'') + a * ₁ ∎

    
lemma-act-cong-ax {n} w v selinger-c13 ((a , b) ∷ (a' , b') ∷ (a'' , b'') ∷ t) = begin
  act ((⊤⊥ ↑) • (CZ ↓) • (⊥⊤ ↑)) ((a , b) ∷ (a' , b') ∷ (a'' , b'') ∷ t) ≡⟨ cong (act ((⊤⊥ ↑) • (CZ ↓))) (Eq.trans (lemma-act-↑ ⊥⊤ (a , b) ((a' , b') ∷ (a'' , b'') ∷ t)) (Eq.cong ((a , b) ∷_) (lemma-act-⊥⊤ a' b' a'' b'' t))) ⟩
  act ((⊤⊥ ↑) • (CZ ↓)) ((a , b) ∷ (a'' , - b' + b'') ∷ (- a'' + - a' , - b') ∷ t) ≡⟨ auto ⟩
  act ((⊤⊥ ↑)) ((a , b + a'' * ₁) ∷ (a'' , (- b' + b'') + a * ₁) ∷ (- a'' + - a' , - b') ∷ t) ≡⟨ Eq.trans (lemma-act-↑ ⊤⊥ (a , b + a'' * ₁) ((a'' , (- b' + b'') + a * ₁) ∷ (- a'' + - a' , - b') ∷ t)) (cong ((a , b + a'' * ₁) ∷_) (lemma-act-⊤⊥ a'' ((- b' + b'') + a * ₁) (- a'' + - a') (- b') t)) ⟩
  ((a , b + a'' * ₁) ∷ (- a'' + - (- a'' + - a') , - - b') ∷ (a'' , - - b' + ((- b' + b'') + a * ₁)) ∷ t) ≡⟨ cong₃ (\ xx yy zz -> (a , xx) ∷ (yy , - - b') ∷ (a'' , zz) ∷ t) (sym aux) aux2 aux30c ⟩
  ((a , - - b' + ((- b' + b) + a'' * ₁)) ∷ (- a + - (- a + - a') , - - b') ∷ (a'' , b'' + a * ₁) ∷ t) ≡⟨ sym (lemma-act-⊥⊤ (- a + - a') (- b') a ((- b' + b) + a'' * ₁) ((a'' , b'' + a * ₁) ∷ t)) ⟩
  act ((⊥⊤ ↓)) ((- a + - a' , - b') ∷ (a , (- b' + b) + a'' * ₁) ∷ (a'' , b'' + a * ₁) ∷ t) ≡⟨ sym (cong (act ((⊥⊤ ↓))) (lemma-act-↑ CZ ((- a + - a' , - b')) ((a , - b' + b) ∷ (a'' , b'') ∷ t))) ⟩
  act ((⊥⊤ ↓) • (CZ ↑)) ((- a + - a' , - b') ∷ (a , - b' + b) ∷ (a'' , b'') ∷ t) ≡⟨ cong (act ((⊥⊤ ↓) • (CZ ↑))) (sym (lemma-act-⊤⊥ a b a' b' ((a'' , b'') ∷ t))) ⟩
  act ((⊥⊤ ↓) • (CZ ↑) • (⊤⊥ ↓)) ((a , b) ∷ (a' , b') ∷ (a'' , b'') ∷ t) ∎
  where
  open ≡-Reasoning
  aux30c : - - b' + ((- b' + b'') + a * ₁) ≡ b'' + a * ₁
  aux30c = begin
    - - b' + ((- b' + b'') + a * ₁) ≡⟨ sym (+-assoc (- - b') ((- b' + b'')) (a * ₁)) ⟩
    - - b' + (- b' + b'') + a * ₁ ≡⟨ cong (_+ a * ₁) (sym (+-assoc (- - b') (- b') b'')) ⟩
    - - b' + - b' + b'' + a * ₁ ≡⟨ cong (\ xx -> xx + b'' + a * ₁) (+-inverseˡ (- b')) ⟩
    ₀ + b'' + a * ₁ ≡⟨ cong (_+ a * ₁) (+-identityˡ b'') ⟩
    b'' + a * ₁ ∎
  aux2 : - a'' + - (- a'' + - a') ≡ - a + - (- a + - a')
  aux2 = begin
    - a'' + - (- a'' + - a') ≡⟨ trans (cong (- a'' +_) ( sym (-‿+-comm (- a'') (- a')))) (sym (+-assoc (- a'') (- - a'') (- - a'))) ⟩
    - a'' + - - a'' + - - a' ≡⟨ trans (cong (_+ - - a') (+-inverseʳ (- a''))) (+-identityˡ (- - a')) ⟩
    - - a' ≡⟨ sym (trans (cong (_+ - - a') (+-inverseʳ (- a))) (+-identityˡ (- - a'))) ⟩
    - a + - - a + - - a' ≡⟨ sym (trans (cong (- a +_) ( sym (-‿+-comm (- a) (- a')))) (sym (+-assoc (- a) (- - a) (- - a')))) ⟩
    - a + - (- a + - a') ∎
  
  aux : - - b' + ((- b' + b) + a'' * ₁) ≡ b + a'' * ₁
  aux = begin
    - - b' + ((- b' + b) + a'' * ₁) ≡⟨ sym (+-assoc (- - b') ((- b' + b)) (a'' * ₁)) ⟩
    - - b' + (- b' + b) + a'' * ₁ ≡⟨ cong (_+ a'' * ₁) (sym (+-assoc (- - b') (- b') b)) ⟩
    - - b' + - b' + b + a'' * ₁ ≡⟨ cong (\ xx -> xx + b + a'' * ₁) (+-inverseˡ (- b')) ⟩
    ₀ + b + a'' * ₁ ≡⟨ cong (_+ a'' * ₁) (+-identityˡ b) ⟩
    b + a'' * ₁ ∎

    
lemma-act-cong-ax {n} w v selinger-c14 ((a , b) ∷ (a' , b') ∷ (a'' , b'') ∷ t) = begin
  act (((⊤⊥ ↑) • (CZ ↓)) • ((⊤⊥ ↑) • (CZ ↓)) • (⊤⊥ ↑) • (CZ ↓)) ((a , b) ∷ (a' , b') ∷ (a'' , b'') ∷ t) ≡⟨ cong (act (((⊤⊥ ↑) • (CZ ↓)) • ((⊤⊥ ↑) • (CZ ↓)))) (lemma-act-⊤⊥↑CZ↓ a b a' b' a'' b'' t) ⟩
  act (((⊤⊥ ↑) • (CZ ↓)) • ((⊤⊥ ↑) • (CZ ↓))) ((a , b + a') ∷ (- a' + - a'' , - b'') ∷ (a' , - b'' + (b' + a)) ∷ t) ≡⟨ cong (act (⊤⊥ ↑ • CZ ↓)) (lemma-act-⊤⊥↑CZ↓ a (b + a') (- a' + - a'') (- b'') a' (- b'' + (b' + a)) t) ⟩
  act (((⊤⊥ ↑) • (CZ ↓))) ((a , (b + a') + (- a' + - a'')) ∷ (- (- a' + - a'') + - a' , - (- b'' + (b' + a))) ∷ (- a' + - a'' , - (- b'' + (b' + a)) + (- b'' + a)) ∷ t) ≡⟨ lemma-act-⊤⊥↑CZ↓ a ((b + a') + (- a' + - a'')) (- (- a' + - a'') + - a') (- (- b'' + (b' + a))) (- a' + - a'') (- (- b'' + (b' + a)) + (- b'' + a)) t ⟩
  ((a , ((b + a') + (- a' + - a'')) + (- (- a' + - a'') + - a')) ∷ (- (- (- a' + - a'') + - a') + - (- a' + - a'') , - (- (- b'' + (b' + a)) + (- b'' + a))) ∷ (- (- a' + - a'') + - a' , - (- (- b'' + (b' + a)) + (- b'' + a)) + (- (- b'' + (b' + a)) + a)) ∷ t) ≡⟨ cong₃ (\ xx yy zz -> ((a , xx) ∷ (yy , zz) ∷ (- (- a' + - a'') + - a' , - (- (- b'' + (b' + a)) + (- b'' + a)) + (- (- b'' + (b' + a)) + a)) ∷ t)) aux1 aux2 (aux30 b'' b' a) ⟩
  ((a , b) ∷ (a' , b') ∷ (- (- a' + - a'') + - a' , - (- (- b'' + (b' + a)) + (- b'' + a)) + (- (- b'' + (b' + a)) + a)) ∷ t) ≡⟨ cong₂ (\ xx yy -> ((a , b) ∷ (a' , b') ∷ (xx , yy) ∷ t)) aux40 aux5 ⟩
  (a , b) ∷ (a' , b') ∷ (a'' , b'') ∷ t ≡⟨ auto ⟩
  act ε ((a , b) ∷ (a' , b') ∷ (a'' , b'') ∷ t) ∎
  where
  open ≡-Reasoning
  aux5 : - (- (- b'' + (b' + a)) + (- b'' + a)) + (- (- b'' + (b' + a)) + a) ≡ b''
  aux5 = begin
    - (- (- b'' + (b' + a)) + (- b'' + a)) + (- (- b'' + (b' + a)) + a) ≡⟨ cong (_+ (- (- b'' + (b' + a)) + a)) (sym (-‿+-comm (- (- b'' + (b' + a))) ((- b'' + a)))) ⟩
    (- - (- b'' + (b' + a)) + - (- b'' + a)) + (- (- b'' + (b' + a)) + a) ≡⟨ cong (_+ (- (- b'' + (b' + a)) + a)) (+-comm (- - (- b'' + (b' + a))) (- (- b'' + a))) ⟩
    (- (- b'' + a) + - - (- b'' + (b' + a))) + (- (- b'' + (b' + a)) + a) ≡⟨ trans (+-assoc (- (- b'' + a)) (- - (- b'' + (b' + a))) ((- (- b'' + (b' + a)) + a))) (cong (- (- b'' + a) +_) (sym (+-assoc (- - (- b'' + (b' + a))) (- (- b'' + (b' + a))) a))) ⟩
    - (- b'' + a) + ((- - (- b'' + (b' + a)) + - (- b'' + (b' + a))) + a) ≡⟨ cong (\ xx -> - (- b'' + a) + (xx + a)) (+-inverseˡ (- (- b'' + (b' + a)))) ⟩
    - (- b'' + a) + (₀ + a) ≡⟨ cong₂ _+_ (sym (-‿+-comm (- b'') a)) (+-identityˡ a) ⟩
    - - b'' + - a + a ≡⟨ +-assoc (- - b'') (- a) a ⟩
    - - b'' + (- a + a) ≡⟨ cong₂ _+_ (-‿involutive b'') (+-inverseˡ a) ⟩
    b'' + ₀ ≡⟨ +-identityʳ b'' ⟩
    b'' ∎
    
  aux40 : - (- a' + - a'') + - a' ≡ a''
  aux40 = begin
    - (- a' + - a'') + - a' ≡⟨ cong (_+ - a') (sym (-‿+-comm (- a') (- a''))) ⟩
    (- - a' + - - a'') + - a' ≡⟨ cong (_+ - a') (+-comm (- - a') (- - a'')) ⟩
    (- - a'' + - - a') + - a' ≡⟨ +-assoc (- - a'') (- - a') (- a') ⟩
    - - a'' + (- - a' + - a') ≡⟨ cong (- - a'' +_) (+-inverseˡ (- a')) ⟩
    - - a'' + ₀ ≡⟨ +-identityʳ (- - a'') ⟩
    - - a'' ≡⟨ -‿involutive a'' ⟩
    a'' ∎
  --      - (- (- b + (b' + a'')) + (- b + a''))
  aux30b : - (- (- b'' + (b' + a)) + (- b'' + a)) ≡ b'
  aux30b = begin
    - (- (- b'' + (b' + a)) + (- b'' + a)) ≡⟨ (sym (-‿+-comm (- (- b'' + (b' + a))) ((- b'' + a)))) ⟩
    - - (- b'' + (b' + a)) + - (- b'' + a) ≡⟨ cong (_+ - (- b'' + a)) (-‿involutive ((- b'' + (b' + a)))) ⟩
    (- b'' + (b' + a)) + - (- b'' + a) ≡⟨ cong (_+ - (- b'' + a)) (sym (+-assoc (- b'') b' a)) ⟩
    (- b'' + b' + a) + - (- b'' + a) ≡⟨ cong (_+ - (- b'' + a)) (trans (cong (_+ a)  (+-comm (- b'') b')) (+-assoc b' (- b'') a)) ⟩
    b' + (- b'' + a) + - (- b'' + a) ≡⟨ +-assoc b' ((- b'' + a)) (- (- b'' + a)) ⟩
    b' + ((- b'' + a) + - (- b'' + a)) ≡⟨ cong (b' +_) (+-inverseʳ ((- b'' + a))) ⟩
    b' + ₀ ≡⟨ +-identityʳ b' ⟩
    b' ∎
  
  aux2 : - (- (- a' + - a'') + - a') + - (- a' + - a'') ≡ a'
  aux2 = begin
    - (- (- a' + - a'') + - a') + - (- a' + - a'') ≡⟨ cong (_+ - (- a' + - a'')) (sym (-‿+-comm (- (- a' + - a'')) (- a'))) ⟩
    (- - (- a' + - a'') + - - a') + - (- a' + - a'') ≡⟨ cong (_+ - (- a' + - a'')) (+-comm (- - (- a' + - a'')) (- - a')) ⟩
    (- - a' + - - (- a' + - a'')) + - (- a' + - a'') ≡⟨ +-assoc (- - a') (- - (- a' + - a'')) (- (- a' + - a'')) ⟩
    - - a' + (- - (- a' + - a'') + - (- a' + - a'')) ≡⟨ cong (- - a' +_) (+-inverseˡ (- (- a' + - a''))) ⟩
    - - a' + ₀ ≡⟨ +-identityʳ (- - a') ⟩
    - - a' ≡⟨ -‿involutive a' ⟩
    a' ∎
    
  aux1 : ((b + a') + (- a' + - a'')) + (- (- a' + - a'') + - a') ≡ b
  aux1 = begin
    ((b + a') + (- a' + - a'')) + (- (- a' + - a'') + - a') ≡⟨ +-assoc ((b + a')) ((- a' + - a'')) (- (- a' + - a'') + - a') ⟩
    (b + a') + ((- a' + - a'') + (- (- a' + - a'') + - a')) ≡⟨ cong (b + a' +_) (sym (+-assoc ((- a' + - a'')) (- (- a' + - a'')) (- a'))) ⟩
    (b + a') + (((- a' + - a'') + - (- a' + - a'')) + - a') ≡⟨ cong ((b + a') +_) (cong (_+ - a') (+-inverseʳ ((- a' + - a'')))) ⟩
    (b + a') + (₀ + - a') ≡⟨ cong ((b + a') +_) (+-identityˡ (- a')) ⟩
    (b + a') + (- a') ≡⟨ +-assoc b a' (- a') ⟩
    b + (a' + - a') ≡⟨ cong (b +_) (+-inverseʳ a') ⟩
    b + ₀ ≡⟨ +-identityʳ b ⟩
    b ∎

    
lemma-act-cong-ax {n} w v selinger-c15 ((a , b) ∷ (a' , b') ∷ (a'' , b'') ∷ t) = begin
  act (((⊥⊤ ↓) • (CZ ↑)) • ((⊥⊤ ↓) • (CZ ↑)) • (⊥⊤ ↓) • (CZ ↑)) ((a , b) ∷ (a' , b') ∷ (a'' , b'') ∷ t) ≡⟨ cong (act (((⊥⊤ ↓) • (CZ ↑)) • ((⊥⊤ ↓) • (CZ ↑)))) (lemma-act-⊥⊤↓CZ↑ a b a' b' a'' b'' t) ⟩
  act (((⊥⊤ ↓) • (CZ ↑)) • ((⊥⊤ ↓) • (CZ ↑))) ((a' , - b + (b' + a'')) ∷ (- a' + - a , - b) ∷ (a'' , b'' + a') ∷ t) ≡⟨ cong (act (((⊥⊤ ↓) • (CZ ↑)))) (lemma-act-⊥⊤↓CZ↑ a' (- b + (b' + a'')) (- a' + - a) (- b) a'' (b'' + a') t) ⟩
  act (((⊥⊤ ↓) • (CZ ↑))) ((- a' + - a , - (- b + (b' + a'')) + (- b + a'')) ∷ (- (- a' + - a) + - a' , - (- b + (b' + a''))) ∷ (a'' , (b'' + a') + (- a' + - a)) ∷ t) ≡⟨ lemma-act-⊥⊤↓CZ↑ (- a' + - a) (- (- b + (b' + a'')) + (- b + a'')) (- (- a' + - a) + - a') (- (- b + (b' + a''))) a'' ((b'' + a') + (- a' + - a)) t ⟩
  ((- (- a' + - a) + - a' , - (- (- b + (b' + a'')) + (- b + a'')) + (- (- b + (b' + a'')) + a'')) ∷ (- (- (- a' + - a) + - a') + - (- a' + - a) , - (- (- b + (b' + a'')) + (- b + a''))) ∷ (a'' , ((b'' + a') + (- a' + - a)) + (- (- a' + - a) + - a')) ∷ t) ≡⟨ cong₃ (\ xx yy zz -> (xx , yy) ∷ (zz , - (- (- b + (b' + a'')) + (- b + a''))) ∷ (a'' , ((b'' + a') + (- a' + - a)) + (- (- a' + - a) + - a')) ∷ t) (aux40b a' a) (aux5o b b' a'') (aux2o a' a) ⟩
  (a , b) ∷ (a' , - (- (- b + (b' + a'')) + (- b + a''))) ∷ (a'' , ((b'' + a') + (- a' + - a)) + (- (- a' + - a) + - a')) ∷ t ≡⟨ cong₂ (\ xx yy -> (a , b) ∷ (a' , xx) ∷ (a'' , yy) ∷ t ) (aux30o b b' a'') (aux1o') ⟩
  act ε ((a , b) ∷ (a' ,  b') ∷ (a'' , b'') ∷ t) ∎
  where
  open ≡-Reasoning

  aux1o' : ((b'' + a') + (- a' + - a)) + (- (- a' + - a) + - a') ≡ b''
  aux1o'  = begin
    ((b'' + a') + (- a' + - a)) + (- (- a' + - a) + - a') ≡⟨ +-assoc ((b'' + a')) ((- a' + - a)) (- (- a' + - a) + - a') ⟩
    (b'' + a') + ((- a' + - a) + (- (- a' + - a) + - a')) ≡⟨ cong (b'' + a' +_) (sym (+-assoc ((- a' + - a)) (- (- a' + - a)) (- a'))) ⟩
    (b'' + a') + (((- a' + - a) + - (- a' + - a)) + - a') ≡⟨ cong ((b'' + a') +_) (cong (_+ - a') (+-inverseʳ ((- a' + - a)))) ⟩
    (b'' + a') + (₀ + - a') ≡⟨ cong ((b'' + a') +_) (+-identityˡ (- a')) ⟩
    (b'' + a') + (- a') ≡⟨ +-assoc b'' a' (- a') ⟩
    b'' + (a' + - a') ≡⟨ cong (b'' +_) (+-inverseʳ a') ⟩
    b'' + ₀ ≡⟨ +-identityʳ b'' ⟩
    b'' ∎
    where
    open ≡-Reasoning


lemma-act-cong-ax {n} w v comm-H ((a , b) ∷ (a' , b') ∷ t) = auto
lemma-act-cong-ax {n} w v comm-S ((a , b) ∷ (a' , b') ∷ t) = auto
lemma-act-cong-ax {n} w v comm-CZ ((a , b) ∷ (a' , b') ∷ t) = auto



lemma-act-cong-ax {n} w v (derived-S k) (x@(a , b) ∷ t) = begin
  act [ S-gen k ]ʷ ((a , b) ∷ t) ≡⟨ Eq.cong (\ xx ->  act (S^ xx) ((a , b) ∷ t)) (Eq.sym aux) ⟩
  act (S^ k') ((a , b) ∷ t) ≡⟨ Eq.sym (lemma-act-Sᵏ (toℕ k) (((a , b) ∷ t))) ⟩
  act (S ^ toℕ k) ((a , b) ∷ t) ∎
  where
  open ≡-Reasoning
  k' = fromℕ< (m%n<n (toℕ k) p)
  aux : k' ≡ k
  aux = begin
    fromℕ< (m%n<n (toℕ k) p) ≡⟨ fromℕ<-cong ((toℕ k) Nat.% p) (toℕ k) (m<n⇒m%n≡m (toℕ<n k)) (m%n<n (toℕ k) p) (toℕ<n k) ⟩
    fromℕ< (toℕ<n k) ≡⟨ fromℕ<-toℕ k (toℕ<n k) ⟩
    k ∎
lemma-act-cong-ax {n} w v (derived-H ₀) (x@(a , b) ∷ t) = auto
lemma-act-cong-ax {n} w v (derived-H ₁) (x@(a , b) ∷ t) = auto
lemma-act-cong-ax {n} w v (derived-H ₂) (x@(a , b) ∷ t) = auto
lemma-act-cong-ax {n} w v (derived-H ₃) (x@(a , b) ∷ t) = begin
  act [ H-gen ₃ ]ʷ ((a , b) ∷ t) ≡⟨ auto ⟩
  ((b , - a) ∷ t) ≡⟨ Eq.cong (\ xx -> ((xx , - a) ∷ t)) (Eq.sym (-‿involutive b)) ⟩
  ((- - b , - a) ∷ t) ≡⟨ auto ⟩
  act (H) ((- a , - b) ∷ t) ≡⟨ auto ⟩
  act (H • H • H) ((a , b) ∷ t) ∎
  where open ≡-Reasoning
lemma-act-cong-ax {n} w v (derived-CZ k) (x@(a , b) ∷ t) = begin
  act [ CZ-gen k ]ʷ ((a , b) ∷ t) ≡⟨ Eq.cong (\ xx ->  act (CZ^ xx) ((a , b) ∷ t)) (Eq.sym aux) ⟩
  act (CZ^ k') ((a , b) ∷ t) ≡⟨ Eq.sym (lemma-act-CZᵏ (toℕ k) (((a , b) ∷ t))) ⟩
  act (CZ ^ toℕ k) ((a , b) ∷ t) ∎
  where
  open ≡-Reasoning
  k' = fromℕ< (m%n<n (toℕ k) p)
  aux : k' ≡ k
  aux = begin
    fromℕ< (m%n<n (toℕ k) p) ≡⟨ fromℕ<-cong ((toℕ k) Nat.% p) (toℕ k) (m<n⇒m%n≡m (toℕ<n k)) (m%n<n (toℕ k) p) (toℕ<n k) ⟩
    fromℕ< (toℕ<n k) ≡⟨ fromℕ<-toℕ k (toℕ<n k) ⟩
    k ∎

lemma-act-cong-ax {₁₊ n} w v (cong↑ {n}{w₁} {v₁} eq) (a ∷ ps) = begin
  act (w₁ ↑) (a ∷ ps) ≡⟨ lemma-act-↑ w₁ a ps ⟩
  a ∷ act (w₁) (ps) ≡⟨ Eq.cong (a ∷_) (lemma-act-cong-ax _ _ eq ps) ⟩
  a ∷ act (v₁) (ps) ≡⟨ Eq.sym (lemma-act-↑ v₁ a ps) ⟩
  act (v₁ ↑) (a ∷ ps) ∎
  where open ≡-Reasoning

lemma-act-cong : ∀ {n} w v -> let open PB (n QRel,_===_) in w ≈ v -> ∀ c -> act {n} w c ≡ act v c
lemma-act-cong {n} w v PB.refl ps = auto
lemma-act-cong {n} w v (PB.sym eq) ps = Eq.sym (lemma-act-cong v w eq ps)
lemma-act-cong {n} w v (PB.trans eq eq₁) ps = Eq.trans (lemma-act-cong w _ eq ps) (lemma-act-cong _ v eq₁ ps)
lemma-act-cong {n} w v (PB.cong {w₁} {w'} {v₁} {v'} eq eq₁) ps = begin
  act (w₁ • v₁) ps ≡⟨ auto ⟩
  act w₁ (act v₁ ps) ≡⟨ Eq.cong (act w₁) (lemma-act-cong _ _ eq₁ ps) ⟩
  act w₁ (act v' ps) ≡⟨ lemma-act-cong _ _ eq (act v' ps) ⟩
  act (w' • v') ps ∎
  where open ≡-Reasoning
lemma-act-cong {n} w v PB.assoc ps = auto
lemma-act-cong {n} w v PB.left-unit ps = auto
lemma-act-cong {n} w v PB.right-unit ps = auto
lemma-act-cong {n} w v (PB.axiom x) ps = lemma-act-cong-ax _ _ x ps



