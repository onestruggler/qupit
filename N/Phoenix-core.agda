{-# OPTIONS  --safe #-}
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
open import Data.Nat renaming (_^_ to _^́ ; _+_ to _＋_ ; _*_ to _⋆_)
open import Agda.Builtin.Nat using (_-_)
import Data.Nat as Nat
open import Data.Bool hiding (_<_ ; _≤_)
open import Data.List hiding ([_] ; _++_ ; last ; head ; tail ; _∷ʳ_)
open import Data.Vec hiding ([_])
import Data.Vec as V
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



module N.Phoenix-core  where

p-2 : ℕ
p-2 = 0

p-prime : (Prime (2+ p-2))
p-prime = prime[2]

pattern auto = Eq.refl

pattern ₀ = zero
pattern ₁ = suc ₀
pattern ₂ = suc ₁
pattern ₃ = suc ₂

pattern ₁₊ ⱼ = suc ⱼ
pattern ₂₊ ⱼ = suc (suc ⱼ)
pattern ₃₊ ⱼ = suc (suc (suc ⱼ))


open import Zp.ModularArithmetic
open PrimeModulus p-2 p-prime
open import N.Symplectic-Derived p-2 p-prime


open Symplectic-Derived-Gen
open import N.Action p-2 p-prime

open import Data.List as L

variable
  n : ℕ
  A : Set
  
data Choice-eqn5 : Set where
  CXX : Choice-eqn5
  CYY : Choice-eqn5
  CZZ : Choice-eqn5
  CXY : Choice-eqn5
  CYZ : Choice-eqn5
  CZX : Choice-eqn5

Clifford : ℕ -> Set
Clifford n = Word (Gen n)

⟦_⟧ : Choice-eqn5 -> Clifford (₂₊ n)
⟦_⟧ {n} CXX = {!!}
⟦_⟧ {n} CYY = {!!}
⟦_⟧ {n} CZZ = {!!}
⟦_⟧ {n} CXY = H • S • CX • H • S
⟦_⟧ {n} CYZ = {!!}
⟦_⟧ {n} CZX = CX


BSF : ℕ -> Set
BSF n = List (Pauli n)

infixl 6 _V_

_V_ : ℤ ₂ -> ℤ ₂ -> ℕ
a V b = toℕ (a + b + a * b)

Vᵢ : Pauli n -> ℕ
Vᵢ = V.sum ∘ V.map (\ (a , b) -> a V b)

w-tot : List (Pauli n) -> ℕ
w-tot = L.foldr Nat._+_ 0 ∘ L.map Vᵢ

#-local : List (Pauli n) -> ℕ
#-local xs = {!!}

#-nl : List (Pauli n) -> ℕ
#-nl xs = {!!}

n-choose-2 : List A -> List (A × A)
n-choose-2 [] = []
n-choose-2 (x ∷ xs) = (generate-pairs-with-head x xs) L.++ (n-choose-2 xs)
  where
    -- Helper function to pair the head element 'x' with every element in the tail 'ys'
    generate-pairs-with-head : A → List A → List (A × A)
    generate-pairs-with-head _ [] = []
    generate-pairs-with-head x (y ∷ ys) = (x , y) ∷ (generate-pairs-with-head x ys)

cost-bsf : List (Pauli n) -> ℕ
cost-bsf {n} bsf = 2 ⋆ (w-tot bsf ⋆ #-nl bsf ⋆ #-nl bsf ＋ {!!})

CFG : ℕ -> Set
CFG n = BSF n × List (Clifford n × BSF n)


algo1 : BSF n -> CFG n
algo1 bsf with w-tot bsf
... | 0 = bsf , []
... | 1 = bsf , []
... | 2 = bsf , []
... | w = {!(n-choose-2 {ℕ} (1 ∷ 2 ∷ 3 ∷ 4 ∷ []) )!}
