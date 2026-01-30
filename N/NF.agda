{-# OPTIONS  --safe #-}
{-# OPTIONS  --call-by-name #-}
{-# OPTIONS --termination-depth=4 #-}
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
--open import Data.List using () hiding ([_] ; _++_ ; last ; head ; tail ; _∷ʳ_)
open import Data.Vec hiding ([_])
open import Data.Vec as V
open import Data.Fin hiding (_+_ ; _-_ ; _≤_ ; _<_)

open import Data.Maybe hiding (zipWith ; map)
open import Data.Sum using (_⊎_ ; inj₁ ; inj₂ ; [_,_] ; [_,_]′)
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

open import Presentation.Construct.Base hiding (_*_ ; _⊕_)
import Presentation.Construct.Properties.SemiDirectProduct2 as SDP2
import Presentation.Construct.Properties.DirectProduct as DP
import Presentation.Groups.Cyclic as Cyclic


open import Data.Fin using (Fin ; toℕ ; suc ; zero ; fromℕ)
open import Data.Fin.Properties using (suc-injective ; toℕ-inject₁ ; toℕ-fromℕ)
import Data.Nat.Properties as NP
open import Presentation.GroupLike
open import Presentation.Tactics using ()
open import Data.Nat.Primality



module N.NF (p-2 : ℕ) (p-prime : Prime (2+ p-2))  where

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
pattern ₄₊ ⱼ = suc (suc (suc (suc ⱼ)))


open import Zp.ModularArithmetic
open PrimeModulus p-2 p-prime
open import N.Cosets p-2 p-prime
open import N.Symplectic-Derived p-2 p-prime
open Symplectic-Derived-Gen renaming (M to ZM)
open import N.NF1 p-2 p-prime
open import N.LM p-2 p-prime
open import N.LM-Lemmas p-2 p-prime
open import N.LM-Lemmas2 p-2 p-prime
open Normal-Form1

private
  variable
    n : ℕ
    
open import N.Action p-2 p-prime
open import N.Action-Lemmas p-2 p-prime
open import Algebra.Properties.Ring (+-*-ring p-2)
open import N.NF2 p-2 p-prime
open LM2
open ≡-Reasoning
open Eq

lemma-sform-ZX1 : sform1 pZ pX ≡ ₁
lemma-sform-ZX1 = begin
  sform1 pZ pX ≡⟨ auto ⟩
  (- ₀ * ₀ + ₁ * ₁) ≡⟨ cong₂ _+_ (*-zeroʳ (- ₀)) (*-identityˡ ₁) ⟩
  (₀ + ₁) ≡⟨ auto ⟩
  ₁ ∎

lemma-sform-pIₙ-q=0 : ∀ (p : Pauli n) -> sform pIₙ p ≡ ₀
lemma-sform-pIₙ-q=0 [] = auto
lemma-sform-pIₙ-q=0 (q ∷ ps) = begin
  sform pIₙ (q ∷ ps) ≡⟨ auto ⟩
  sform1 pI q + sform pIₙ ps ≡⟨ cong₂ _+_ (sform-pI-q=0 q) (lemma-sform-pIₙ-q=0 ps) ⟩
  ₀ + ₀ ≡⟨ auto ⟩
  ₀ ∎
  where open ≡-Reasoning

lemma-sform-ZX : ∀ {n} → sform (pZ₀ {₁₊ n}) pX₀ ≡ ₁
lemma-sform-ZX {₀} = begin
  sform (pZ₀ {₁}) pX₀ ≡⟨ auto ⟩
  sform1 pZ pX + ₀ ≡⟨ +-identityʳ (sform1 pZ pX) ⟩
  sform1 pZ pX ≡⟨ lemma-sform-ZX1 ⟩
  ₁ ∎
lemma-sform-ZX {₁₊ n} = begin
  sform1 pZ pX + sform (pIₙ {₁₊ n}) pIₙ ≡⟨ cong₂ _+_ lemma-sform-ZX1 (lemma-sform-pIₙ-q=0 (pIₙ {₁₊ n})) ⟩
  ₁ + ₀ ≡⟨ auto ⟩
  ₁ ∎
  where open ≡-Reasoning


infixl 7 _+₁_ _+ₚ_
infixl 8 _*₁_ _*ₚ_
infix 9 -₁_ -ₚ_

_+₁_ : ℤ ₚ × ℤ ₚ → ℤ ₚ × ℤ ₚ → ℤ ₚ × ℤ ₚ
_+₁_ (a , b) (c , d) = (a + c , b + d)

-₁_ : ℤ ₚ × ℤ ₚ → ℤ ₚ × ℤ ₚ
-₁_ (a , b) = (- a , - b)

_*₁_ : ℤ ₚ → ℤ ₚ × ℤ ₚ → ℤ ₚ × ℤ ₚ
_*₁_ a (c , d) = (a * c , a * d)

-ₚ_ : ∀ {n} → Pauli n → Pauli n
-ₚ_ {n} = map -₁_ 

_+ₚ_ : ∀ {n} → Pauli n → Pauli n → Pauli n
_+ₚ_ {n} = zipWith _+₁_ 

_*ₚ_ : ∀ {n} → ℤ ₚ → Pauli n → Pauli n
_*ₚ_ {n} k = map (k *₁_)



pasXZ : ∀ (p : Pauli1) → ∃ \ a → ∃ \ b → p ≡ (a *₁ pX +₁ b *₁ pZ)
pasXZ (x , y) = x , y , claim
  where
  claim : (x , y) ≡ x *₁ pX +₁ y *₁ pZ
  claim = begin
    (x , y) ≡⟨ sym (cong₂ _,_ (*-identityʳ x) (*-identityʳ y)) ⟩
    (x * ₁ , y * ₁) ≡⟨ sym (cong₂ _,_ (+-identityʳ (x * ₁)) (+-identityˡ (y * ₁))) ⟩
    (x * ₁ + ₀ , ₀ + y * ₁) ≡⟨ sym (cong₂ (\ xx yy -> (x * ₁ + xx , yy + y * ₁) ) (*-zeroʳ y) (*-zeroʳ x)) ⟩
    (x * ₁ + y * ₀ , x * ₀ + y * ₁) ≡⟨ auto ⟩
    x *₁ pX +₁ y *₁ pZ ∎


+ₚ-idˡ : ∀ {n} ps → pIₙ {n} +ₚ ps ≡ ps
+ₚ-idˡ {₀} [] = auto
+ₚ-idˡ {₁₊ n} (x ∷ ps) = Eq.cong₂ _∷_ (cong₂ _,_ (+-identityˡ (x .proj₁)) (+-identityˡ (x .proj₂))) (+ₚ-idˡ ps)


aux-b+a*k : ∀ (b d a c k : ℤ ₚ) -> (b + d) + (a + c) * k ≡ (b + a * k) + (d + c * k)
aux-b+a*k b d a c k = begin
  (b + d) + (a + c) * k ≡⟨ cong ((b + d) +_) (*-distribʳ-+ k a c) ⟩
  (b + d) + (a * k + c * k) ≡⟨ +-assoc b d (a * k + c * k) ⟩
  b + (d + (a * k + c * k)) ≡⟨ cong (b +_) (sym (+-assoc d (a * k) (c * k))) ⟩
  b + ((d + a * k) + c * k) ≡⟨ cong (b +_) (cong (_+ c * k) (+-comm d (a * k))) ⟩
  b + ((a * k + d) + c * k) ≡⟨ cong (b +_) (+-assoc (a * k) d (c * k)) ⟩
  b + (a * k + (d + c * k)) ≡⟨ sym (+-assoc b (a * k) (d + c * k)) ⟩
  (b + a * k) + (d + c * k) ∎

aux-kbas : ∀ (k b a s : ℤ ₚ) -> k * (b + a * s) ≡ k * b + k * a * s
aux-kbas k b a s = trans (*-distribˡ-+ k b (a * s)) (cong (k * b +_) (sym (*-assoc k a s)))


lemma-actw-linear-+-gen : ∀ {n} (w : Gen (₁₊ n)) → 
  ∀ ps qs → act1 w (ps +ₚ qs) ≡ act1 w ps +ₚ act1 w qs
lemma-actw-linear-+-gen {n} (H-gen ₁) (x@(a , b) ∷ ps) (x₁@(c , d) ∷ qs) = Eq.cong₂ _∷_ (≡×≡⇒≡ (sym (-‿+-comm b d) , auto)) auto
lemma-actw-linear-+-gen {n} (H-gen ₀) (x ∷ ps) (x₁ ∷ qs) = auto
lemma-actw-linear-+-gen {n} (H-gen ₂) (x@(a , b) ∷ ps) (x₁@(c , d) ∷ qs) = Eq.cong₂ _∷_ (≡×≡⇒≡ (sym (-‿+-comm a c) , sym (-‿+-comm b d))) auto
lemma-actw-linear-+-gen {n} (H-gen ₃) (x@(a , b) ∷ ps) (x₁@(c , d) ∷ qs) = Eq.cong₂ _∷_ (≡×≡⇒≡ (auto , sym (-‿+-comm a c))) auto
lemma-actw-linear-+-gen {n} (S-gen k) (x@(a , b) ∷ ps) (x₁@(c , d) ∷ qs) = Eq.cong₂ _∷_ (≡×≡⇒≡ (auto , aux-b+a*k b d a c k)) auto
lemma-actw-linear-+-gen {n} (CZ-gen k) (x@(a1 , b1) ∷ y@(a2 , b2) ∷ ps) (z@(c1 , d1) ∷ w@(c2 , d2) ∷ qs) = Eq.cong₂ _∷_ (≡×≡⇒≡ (auto , aux-b+a*k b1 d1 a2 c2 k)) (Eq.cong₂ _∷_ (≡×≡⇒≡ (auto , aux-b+a*k b2 d2 a1 c1 k)) auto)

lemma-actw-linear-+-gen {₁₊ n} (w ↥) (x ∷ ps) (x₁ ∷ qs) = Eq.cong₂ _∷_ auto ( lemma-actw-linear-+-gen  w ps qs)



lemma-actw-linear-+ : ∀ {n} (w : Word (Gen (n))) → 
  ∀ ps qs → act w (ps +ₚ qs) ≡ act w ps +ₚ act w qs
lemma-actw-linear-+ {₀} ε ps qs = auto
lemma-actw-linear-+ {₀} (w • w₁) ps qs = begin
   act w (act w₁ (ps +ₚ qs)) ≡⟨ Eq.cong (act w) (lemma-actw-linear-+ w₁ ps qs) ⟩
   act w (act w₁ ps +ₚ act w₁ qs) ≡⟨ lemma-actw-linear-+ w (act w₁ ps) (act w₁ qs) ⟩
   act w (act w₁ ps) +ₚ act w (act w₁ qs) ∎
   where open ≡-Reasoning
lemma-actw-linear-+ {suc n} [ x ]ʷ ps qs = lemma-actw-linear-+-gen x ps qs
lemma-actw-linear-+ {suc n} ε ps qs = auto
lemma-actw-linear-+ {suc n} (w • w₁) ps qs = begin
  act w (act w₁ (ps +ₚ qs)) ≡⟨ Eq.cong (act w) (lemma-actw-linear-+ w₁ ps qs) ⟩
  act w (act w₁ ps +ₚ act w₁ qs) ≡⟨ lemma-actw-linear-+ w (act w₁ ps) (act w₁ qs) ⟩
  act w (act w₁ ps) +ₚ act w (act w₁ qs) ∎
  where
  open ≡-Reasoning

lemma-actw-linear-*-gen : ∀ {n} (w : Gen (₁₊ n)) → 
  ∀ k ps → act1 w (k *ₚ ps) ≡ k *ₚ act1 w ps
lemma-actw-linear-*-gen {n} (H-gen ₀) k (x ∷ ps) = Eq.cong₂ _∷_ (≡×≡⇒≡ (auto , auto)) auto
lemma-actw-linear-*-gen {n} (H-gen ₁) k (x@(a , b) ∷ ps) = Eq.cong₂ _∷_ (≡×≡⇒≡ (-‿distribʳ-* k b , auto)) auto
lemma-actw-linear-*-gen {n} (H-gen ₂) k (x@(a , b) ∷ ps) = Eq.cong₂ _∷_ (≡×≡⇒≡ (-‿distribʳ-* k a , -‿distribʳ-* k b)) auto
lemma-actw-linear-*-gen {n} (H-gen ₃) k (x@(a , b) ∷ ps) = Eq.cong₂ _∷_ (≡×≡⇒≡ (auto , -‿distribʳ-* k a)) auto
lemma-actw-linear-*-gen {n} (S-gen s) k (x@(a , b) ∷ ps) = Eq.cong₂ _∷_ (≡×≡⇒≡ (auto , sym (aux-kbas k b a s))) auto
lemma-actw-linear-*-gen {n} (CZ-gen cz) k (x@(a1 , b1) ∷ y@(a2 , b2) ∷ ps) = Eq.cong₂ _∷_ (≡×≡⇒≡ (auto , sym (aux-kbas k b1 a2 cz))) (Eq.cong₂ _∷_ (≡×≡⇒≡ (auto , Eq.sym (aux-kbas k b2 a1 cz))) auto)
lemma-actw-linear-*-gen {₁₊ n} (w ↥) k (x ∷ ps) = Eq.cong₂ _∷_ auto ( lemma-actw-linear-*-gen  w k ps)

lemma-actw-linear-* : ∀ {n} (w : Word (Gen (n))) → 
  ∀ k ps → act w (k *ₚ ps) ≡ k *ₚ act w ps
lemma-actw-linear-* {₀} ε k ps = auto
lemma-actw-linear-* {₀} (w • w₁) k ps = begin
   act w (act w₁ (k *ₚ ps)) ≡⟨ Eq.cong (act w) (lemma-actw-linear-* w₁ k ps) ⟩
   act w (k *ₚ act w₁ ps) ≡⟨ lemma-actw-linear-* w k (act w₁ ps)  ⟩
   k *ₚ act w (act w₁ ps) ∎
   where open ≡-Reasoning
lemma-actw-linear-* {suc n} [ x ]ʷ ps qs = lemma-actw-linear-*-gen x ps qs
lemma-actw-linear-* {suc n} ε ps qs = auto
lemma-actw-linear-* {suc n} (w • w₁) k qs = begin
  act w (act w₁ (k *ₚ qs)) ≡⟨ Eq.cong (act w) (lemma-actw-linear-* w₁ k qs) ⟩
  act w (k *ₚ act w₁ (qs)) ≡⟨ lemma-actw-linear-* w k (act w₁ qs) ⟩
  k *ₚ act w (act w₁ qs) ∎
  where
  open ≡-Reasoning


lemma-aux-px : ∀ {n} → pX ∷ pIₙ {n} ≡ pX₀
lemma-aux-px {₀} = auto
lemma-aux-px {₁₊ n} = auto

lemma-aux-pz : ∀ {n} → pZ ∷ pIₙ {n} ≡ pZ₀
lemma-aux-pz {₀} = auto
lemma-aux-pz {₁₊ n} = auto


+₁-idˡ : ∀ ps → ps +₁ (₀ , ₀) ≡ ps
+₁-idˡ (a , b) = cong₂ _,_ (+-identityʳ a) (+-identityʳ b)


*₁-zeroʳ : ∀ k → k *₁ (₀ , ₀) ≡ (₀ , ₀)
*₁-zeroʳ k = cong₂ _,_ (*-zeroʳ k) (*-zeroʳ k)

*₁-zeroˡ : ∀ p → ₀ *₁ p ≡ (₀ , ₀)
*₁-zeroˡ p = auto


+ₚ-idʳ : ∀ {n} ps → ps +ₚ pIₙ {n} ≡ ps
+ₚ-idʳ {₀} [] = auto
+ₚ-idʳ {₁₊ n} (x ∷ ps) = Eq.cong₂ _∷_ (+₁-idˡ x) (+ₚ-idʳ ps)


lemma-pauli-zero : ∀ {n} b → b *ₚ pIₙ {n} ≡ pIₙ {n}
lemma-pauli-zero {₀} b = auto
lemma-pauli-zero {₁₊ n} b = Eq.cong₂ _∷_ (*₁-zeroʳ b) (lemma-pauli-zero b)

lemma-actw-pIₙ : ∀ {n} w → act w pIₙ ≡ pIₙ {n}
lemma-actw-pIₙ {n} [ H-gen ₀ ]ʷ = auto
lemma-actw-pIₙ {n} [ H-gen ₁ ]ʷ = Eq.cong₂ _∷_ (≡×≡⇒≡ (-0#≈0# , auto)) auto
lemma-actw-pIₙ {n} [ H-gen ₂ ]ʷ = Eq.cong₂ _∷_ (≡×≡⇒≡ (-0#≈0# , -0#≈0#)) auto
lemma-actw-pIₙ {n} [ H-gen ₃ ]ʷ = Eq.cong₂ _∷_ (≡×≡⇒≡ (auto , -0#≈0#)) auto
lemma-actw-pIₙ {n} [ S-gen k ]ʷ = auto
lemma-actw-pIₙ {n} [ CZ-gen k ]ʷ = auto
lemma-actw-pIₙ {n} [ x ↥ ]ʷ = Eq.cong₂ _∷_ auto (lemma-actw-pIₙ [ x ]ʷ)
lemma-actw-pIₙ {n} ε = auto
lemma-actw-pIₙ {n} (w • w₁) = begin
  act w (act w₁ pIₙ) ≡⟨ Eq.cong (act w) (lemma-actw-pIₙ w₁) ⟩
  act w (pIₙ) ≡⟨ lemma-actw-pIₙ w ⟩
  pIₙ ∎
  where
  open ≡-Reasoning

lemma-aux-kx : ∀ {n} k → k *₁ pX ∷ pIₙ {n} ≡ k *ₚ pX₀
lemma-aux-kx {₀} k = auto
lemma-aux-kx {₁₊ n} k = Eq.cong₂ _∷_ auto (Eq.sym (lemma-pauli-zero k))

lemma-aux-kz : ∀ {n} k → k *₁ pZ ∷ pIₙ {n} ≡ k *ₚ pZ₀
lemma-aux-kz {₀} k = auto
lemma-aux-kz {₁₊ n} k = Eq.cong₂ _∷_ auto (Eq.sym (lemma-pauli-zero k))


lemma-actw-linear0 : ∀ {n} (w : Word (Gen (₁₊ n))) → let f = act w in
  f pZ₀ ≡ pZ₀ × f pX₀ ≡ pX₀ →
  ∀ p → (f (p ∷ pIₙ)) ≡ p ∷ pIₙ
lemma-actw-linear0 w (eqz , eqx) p = let ps = pIₙ in begin
  act w (p ∷ ps) ≡⟨ Eq.cong (\ □ → act w (□ ∷ ps)) eq ⟩
  act w (a *₁ pX +₁ b *₁ pZ ∷ ps) ≡⟨ Eq.cong (act w) (Eq.cong₂ _∷_ auto (Eq.sym (+ₚ-idˡ pIₙ))) ⟩
  act w ((a *₁ pX ∷ pIₙ) +ₚ (b *₁ pZ ∷ ps)) ≡⟨ lemma-actw-linear-+ w ((a *₁ pX ∷ pIₙ)) ((b *₁ pZ ∷ ps)) ⟩
  act w (a *₁ pX ∷ pIₙ) +ₚ act w (b *₁ pZ ∷ ps) ≡⟨ Eq.cong₂ (\ s1 s2 →  act w (s1) +ₚ act w (s2)) (lemma-aux-kx a) (lemma-aux-kz b) ⟩
  act w (a *ₚ (pX₀)) +ₚ act w (b *ₚ (pZ₀)) ≡⟨ Eq.cong₂ _+ₚ_ (lemma-actw-linear-* w a pX₀) (lemma-actw-linear-* w b pZ₀) ⟩
  a *ₚ act w (pX₀) +ₚ b *ₚ act w (pZ₀) ≡⟨ Eq.cong₂ _+ₚ_ (Eq.cong (a *ₚ_) eqx) ((Eq.cong (b *ₚ_) eqz)) ⟩
  a *ₚ pX₀ +ₚ b *ₚ pZ₀ ≡⟨ Eq.cong₂ (\ s1 s2 → a *ₚ s1 +ₚ b *ₚ s2) (Eq.sym lemma-aux-px) (Eq.sym lemma-aux-pz) ⟩
  (a *ₚ (pX ∷ pIₙ) +ₚ b *ₚ (pZ ∷ pIₙ)) ≡⟨ auto ⟩
  (a *₁ pX +₁ b *₁ pZ ∷ a *ₚ pIₙ +ₚ b *ₚ pIₙ) ≡⟨ Eq.cong (\ □ → (□ ∷ a *ₚ pIₙ +ₚ b *ₚ pIₙ)) (Eq.sym eq) ⟩
  (p ∷ a *ₚ pIₙ +ₚ b *ₚ pIₙ) ≡⟨ Eq.cong₂ (\ s1 s2 → p ∷ s1 +ₚ s2) (lemma-pauli-zero a) (lemma-pauli-zero b) ⟩
  (p ∷ pIₙ +ₚ pIₙ) ≡⟨ auto ⟩
  p ∷ (pIₙ +ₚ pIₙ) ≡⟨ Eq.cong (p ∷_) (+ₚ-idˡ pIₙ) ⟩
  p ∷  pIₙ ∎
  where
  open ≡-Reasoning
  pab = pasXZ p
  a = pab .proj₁
  b = pab .proj₂ .proj₁
  eq = pab .proj₂ .proj₂


lemma-sform1-XZ : ∀ p → sform1 pZ p ≡ ₀ × sform1 pX p ≡ ₀ → p ≡ pI
lemma-sform1-XZ (c , d) (eq1 , eq2) = ≡×≡⇒≡ (aux , aux3a)
  where
  aux : c ≡ ₀
  aux = begin
    c ≡⟨ sym (*-identityʳ c) ⟩
    c * ₁ ≡⟨ sym (+-identityˡ (c * ₁)) ⟩
    ₀ + c * ₁ ≡⟨ cong (_+ c * ₁) (sym (*-zeroˡ d)) ⟩
    ₀ * d + c * ₁ ≡⟨ cong (\ xx -> xx * d + c * ₁) (sym -0#≈0#) ⟩
    - ₀ * d + c * ₁ ≡⟨ eq1 ⟩
    ₀ ∎

  aux2 : - d ≡ ₀
  aux2 = begin
    - d ≡⟨ sym (-1*x≈-x d) ⟩
    - ₁ * d  ≡⟨ sym (+-identityʳ (- ₁ * d))  ⟩
    - ₁ * d + ₀  ≡⟨ cong (- ₁ * d +_) (sym (*-zeroʳ c)) ⟩
    - ₁ * d + c * ₀  ≡⟨ eq2 ⟩
    ₀ ∎

  aux3a : d ≡ ₀
  aux3a = trans (sym (-‿involutive d)) (trans (cong -_ aux2) -0#≈0#)


lemma-alt : ∀ p → sform1 p p ≡ ₀
lemma-alt (a , b) = begin
  - a * b + a * b ≡⟨ cong (_+ a * b) (sym (-‿distribˡ-* a b)) ⟩
  - (a * b) + a * b ≡⟨ +-inverseˡ (a * b) ⟩
  ₀ ∎


lemma-actw-linear-aux : ∀ {n} p (ps : Pauli n) → sform (p ∷ pIₙ) (p ∷ ps) ≡ ₀
lemma-actw-linear-aux {₀} p [] = Eq.cong₂ _+_ (lemma-alt p) auto
lemma-actw-linear-aux {₁₊ n} p ps = Eq.cong₂ _+_ (lemma-alt p) (lemma-sform-pIₙ-q=0  ps)


lemma-aux-vec : ∀ {A : Set} n (v : Vec A (₁₊ n)) → head v ∷ tail v ≡ v
lemma-aux-vec {A} ₀ (x ∷ v) = auto
lemma-aux-vec {A} (₁₊ n) (x ∷ v) = auto

lemma-sform1-pIʳ : ∀ x → sform1 x pI ≡ ₀
lemma-sform1-pIʳ (a , b) = begin
  - a * ₀ + ₀ * b ≡⟨ cong₂ _+_ (*-zeroʳ (- a)) (*-zeroˡ b) ⟩
  ₀ + ₀ ≡⟨ auto ⟩
  ₀ ∎


lemma-sform-aux-h : (a b c d : ℤ ₚ) -> (- a) * d + c * b ≡  (- (- b)) * c + (- d) * a
lemma-sform-aux-h a b c d = begin
  (- a) * d + c * b ≡⟨ cong (_+ c * b) (sym (-‿distribˡ-* a d)) ⟩
  - (a * d) + c * b ≡⟨ +-comm (- (a * d) ) (c * b) ⟩
  c * b + - (a * d) ≡⟨ cong₂ _+_ (*-comm c b) (cong -_ (*-comm a d)) ⟩
  b * c + - (d * a) ≡⟨ cong₂ _+_ (cong (_* c) (sym (-‿involutive b))) (-‿distribˡ-* d a) ⟩
  (- (- b)) * c + (- d) * a ∎


aux-[x-b]+[b+y] : ∀ (x b y : ℤ ₚ) -> (x + - b) + (b + y) ≡ x + y
aux-[x-b]+[b+y] x b y = begin
  (x + - b) + (b + y) ≡⟨ +-assoc x (- b) (b + y) ⟩
  x + (- b + (b + y)) ≡⟨ cong (x +_) (sym (+-assoc (- b) b y)) ⟩
  x + (- b + b + y) ≡⟨ cong (x +_) (cong (_+ y) (+-inverseˡ b)) ⟩
  x + (₀ + y) ≡⟨ cong (x +_) (+-identityˡ y) ⟩
  x + y ∎

aux-[x+b]+[-b+y] : ∀ (x b y : ℤ ₚ) -> (x + b) + (- b + y) ≡ x + y
aux-[x+b]+[-b+y] x b y = begin
  (x + b) + (- b + y) ≡⟨ +-assoc x (b) (- b + y) ⟩
  x + (b + (- b + y)) ≡⟨ cong (x +_) (sym (+-assoc b (- b) y)) ⟩
  x + (b + - b + y) ≡⟨ cong (x +_) (cong (_+ y) (+-inverseʳ b)) ⟩
  x + (₀ + y) ≡⟨ cong (x +_) (+-identityˡ y) ⟩
  x + y ∎


aux-cak : ∀ (c a k : ℤ ₚ) -> c * (a * k) ≡ a * (c * k)
aux-cak c a k = trans (sym (*-assoc c a k)) (trans (cong (_* k) (*-comm c a)) (*-assoc a c k))

lemma-sform-aux-s'k : (a b c d k : ℤ ₚ) -> (- a) * d + c * b ≡ (- a) * (d + c * k) + c * (b + a * k )
lemma-sform-aux-s'k a b c d k = sym ( begin
  (- a) * (d + c * k) + c * (b + a * k ) ≡⟨ cong₂ _+_ (*-distribˡ-+ (- a) d (c * k) ) (*-distribˡ-+ c b (a * k)) ⟩
  (- a * d + - a * (c * k)) + (c * b + c * (a * k) ) ≡⟨ cong₂ _+_ (sym (cong (- a * d +_) (-‿distribˡ-* a (c * k)))) (+-comm (c * b) (c * (a * k) )) ⟩
  (- a * d + - (a * (c * k))) + (c * (a * k) + c * b ) ≡⟨ cong ((- a * d + - (a * (c * k))) +_) (cong (_+ c * b) (aux-cak c a k)) ⟩
  (- a * d + - (a * (c * k))) + (a * (c * k) + c * b ) ≡⟨ aux-[x-b]+[b+y] (- a * d) ((a * (c * k))) (c * b) ⟩
  (- a) * d + c * b ∎
  )


aux-[x-a+[y+b]]+[z-b+[w+a]] : ∀ (x a y b z w : ℤ ₚ) -> (x + - a + (y + b)) + (z + - b + (w + a)) ≡ (x + y + (z + w))
aux-[x-a+[y+b]]+[z-b+[w+a]] x a y b z w = begin
  (x + - a + (y + b)) + (z + - b + (w + a)) ≡⟨ cong₂ _+_ (sym (+-assoc (x + - a) y b)) (cong (_+ (w + a)) (+-comm z (- b))) ⟩
  (x + - a + y + b) + (- b + z + (w + a)) ≡⟨ cong ((x + - a + y + b) +_) (+-assoc (- b) z (w + a)) ⟩
  (x + - a + y + b) + (- b + (z + (w + a))) ≡⟨ aux-[x+b]+[-b+y] (x + - a + y) b (z + (w + a)) ⟩
  (x + - a + y) + (z + (w + a)) ≡⟨ cong (_+ (z + (w + a))) (+-assoc x (- a) y) ⟩
  (x + (- a + y)) + (z + (w + a)) ≡⟨ cong₂ _+_ (cong (x +_) (+-comm (- a) y)) (cong (z +_) (+-comm w a)) ⟩
  (x + (y + - a)) + (z + (a + w)) ≡⟨ cong₂ _+_ (sym (+-assoc x y (- a))) (sym (+-assoc z a w)) ⟩
  (x + y + - a) + (z + a + w) ≡⟨ cong (x + y + - a +_) (cong (_+ w) (+-comm z a)) ⟩
  (x + y + - a) + (a + z + w) ≡⟨ cong ((x + y + - a) +_) (+-assoc a z w) ⟩
  (x + y + - a) + (a + (z + w)) ≡⟨ aux-[x-b]+[b+y] (x + y) a (z + w) ⟩
  (x + y + (z + w)) ∎
  

lemma-sform-aux-cz'k : (a b a' b' c d c' d' k : ℤ ₚ) ->
  ( - a * (d + c' * k) + c * (b + a' * k) ) + ( - a' * (d' + c * k) + c' * (b' + a * k)) ≡ (- a * d + c * b) + (- a' * d' + c' * b')
lemma-sform-aux-cz'k a b a' b' c d c' d' k = begin
  ( - a * (d + c' * k) + c * (b + a' * k) ) + ( - a' * (d' + c * k) + c' * (b' + a * k)) ≡⟨ (cong₂ _+_ (cong₂ _+_ (*-distribˡ-+ (- a) d (c' * k)) (*-distribˡ-+ c b (a' * k))) (cong₂ _+_ (*-distribˡ-+ (- a') d' (c * k)) (*-distribˡ-+ c' b' (a * k)))) ⟩
  ( (- a * d + - a * (c' * k)) + (c * b + c *(a' * k)) ) + ( (- a' * d' + - a' * (c * k)) + (c' * b' + c' * (a * k))) ≡⟨ cong₂ (\ xx yy -> ( (- a * d + - a * (c' * k)) + (c * b + xx) ) + ( (- a' * d' + yy) + (c' * b' + c' * (a * k)))) (aux-cak c a' k) (sym (-‿distribˡ-* a' (c * k))) ⟩
  ( (- a * d + - a * (c' * k)) + (c * b + a' *(c * k)) ) + ( (- a' * d' + - (a' * (c * k))) + (c' * b' + c' * (a * k))) ≡⟨ cong₂ (\ xx yy -> ( (- a * d + xx) + (c * b + a' *(c * k)) ) + ( (- a' * d' + - (a' * (c * k))) + (c' * b' + yy))) (sym (-‿distribˡ-* a (c' * k))) (aux-cak c' a k) ⟩
  ( (- a * d + - (a * (c' * k))) + (c * b + a' *(c * k)) ) + ( (- a' * d' + - (a' * (c * k))) + (c' * b' + a * (c' * k))) ≡⟨ aux-[x-a+[y+b]]+[z-b+[w+a]] (- a * d) ((a * (c' * k))) (c * b) (a' *(c * k)) (- a' * d') (c' * b') ⟩
  - a * d + c * b + (- a' * d' + c' * b') ∎

lemma-sform-aux-sk : ∀ a b c d k → sform1 (a , b) (c , d) ≡ sform1 (a , b + a * k) (c , d + c * k)
lemma-sform-aux-sk a b c d k = lemma-sform-aux-s'k a b c d k

lemma-sform-aux : ∀ a b c d → sform1  (a , b) (c , d) ≡ sform1 (- b , a) (- d , c)
lemma-sform-aux a b c d = lemma-sform-aux-h a b c d

lemma-sform-aux-h2 : (a b c d : ℤ ₚ) -> (- - a) * - d + - c * - b ≡ (- a) * d + c * b
lemma-sform-aux-h2 a b c d = begin
  (- - a) * - d + - c * - b ≡⟨ cong₂ _+_ (cong (_* - d) (-‿involutive a)) (sym (-‿distribʳ-* (- c) b)) ⟩
  a * - d + - (- c * b) ≡⟨ cong₂ _+_ (sym (-‿distribʳ-* a d)) (cong -_ (sym (-‿distribˡ-* c b))) ⟩
  - (a * d) + - - (c * b) ≡⟨ cong₂ _+_ (-‿distribˡ-* a d) (-‿involutive (c * b)) ⟩
  (- a) * d + c * b ∎


aux-mx*my : ∀ (x y : ℤ ₚ) -> - x * - y ≡ x * y
aux-mx*my x y = begin
  - x * - y ≡⟨ sym (-‿distribˡ-* x (- y)) ⟩
  - (x * - y) ≡⟨ sym (cong -_ (-‿distribʳ-* x y)) ⟩
  - - (x * y) ≡⟨ -‿involutive (x * y) ⟩
  x * y ∎


lemma-sform-aux-h3 : (a b c d : ℤ ₚ) -> (- b) * - c + d * - a ≡ (- a) * d + c * b
lemma-sform-aux-h3 a b c d = begin
  (- b) * - c + d * - a ≡⟨ cong₂ _+_ (*-comm (- b) (- c)) (*-comm d (- a)) ⟩
  - c * - b + - a * d ≡⟨ cong (_+ - a * d) (aux-mx*my c b) ⟩
  c * b + - a * d ≡⟨ +-comm (c * b) (- a * d) ⟩
  (- a) * d + c * b ∎


sform-preserving-gen : ∀ {n} g ps qs → sform {n} (act1 g ps) (act1 g qs) ≡ sform ps qs
sform-preserving-gen {n} (H-gen ₀) (x ∷ ps) (x₁ ∷ qs) = auto
sform-preserving-gen {n} (H-gen ₂) (x@(a , b) ∷ ps) (x₁@(c , d) ∷ qs) =  Eq.cong₂ _+_ (lemma-sform-aux-h2 a b c d) auto
sform-preserving-gen {n} (H-gen ₃) (x@(a , b) ∷ ps) (x₁@(c , d) ∷ qs) = Eq.cong₂ _+_ (lemma-sform-aux-h3 a b c d) auto
sform-preserving-gen {n} (H-gen ₁) (x@(a , b) ∷ ps) (x₁@(c , d) ∷ qs) = Eq.cong₂ _+_ (Eq.sym (lemma-sform-aux a b c d)) Eq.refl
sform-preserving-gen {n} (S-gen k) (x@(a , b) ∷ ps) (x₁@(c , d) ∷ qs) = Eq.cong₂ _+_ (Eq.sym (lemma-sform-aux-sk a b c d k)) Eq.refl
sform-preserving-gen {n} (CZ-gen k) (x@(a , b) ∷ x₂@(a' , b') ∷ ps) (x₁@(c , d) ∷ x₃@(c' , d') ∷ qs) = begin
  sform1 (a , b + a' * k) (c , d + c' * k) + (sform1 (a' , b' + a * k) (c' , d' + c * k) + sform ps qs) ≡⟨ sym (+-assoc (sform1 (a , b + a' * k) (c , d + c' * k)) (sform1 (a' , b' + a * k) (c' , d' + c * k)) (sform ps qs)) ⟩
  sform1 (a , b + a' * k) (c , d + c' * k) + sform1 (a' , b' + a * k) (c' , d' + c * k) + sform ps qs ≡⟨ cong (_+ sform ps qs) (lemma-sform-aux-cz'k a b a' b' c d c' d' k) ⟩
  (sform1 x x₁ + sform1 x₂ x₃) + sform ps qs ≡⟨ +-assoc (sform1 x x₁) (sform1 x₂ x₃)  (sform ps qs) ⟩
  sform1 x x₁ + (sform1 x₂ x₃ + sform ps qs) ∎
sform-preserving-gen {n} (g ↥) (x ∷ ps) (x₁ ∷ qs) = Eq.cong₂ _+_ (Eq.refl {x = sform1 x x₁})  (sform-preserving-gen g ps qs)


sform-preserving : ∀ {n} w ps qs → sform {n} (act w ps) (act w qs) ≡ sform ps qs
sform-preserving {n} [ x ]ʷ ps qs = sform-preserving-gen x ps qs
sform-preserving {n} ε ps qs = auto
sform-preserving {n} (w • w₁) ps qs = begin
  sform (act w (act w₁ ps)) (act w (act w₁ qs)) ≡⟨ sform-preserving w (act w₁ ps) (act w₁ qs) ⟩
  sform ((act w₁ ps)) ((act w₁ qs)) ≡⟨ sform-preserving w₁ ps qs ⟩
  sform ps qs ∎
  where open ≡-Reasoning



lemma-actw-fix-p0 : ∀ {n} (w : Word (Gen (₁₊ n))) → let f = act w in
  f pZ₀ ≡ pZ₀ × f pX₀ ≡ pX₀ →
  ∀ p ps → (f (p ∷ ps)) ≡ p ∷ tail (f (pI ∷ ps))
lemma-actw-fix-p0 {n} w (eqz , eqx) p ps = begin
  act w (p ∷ ps) ≡⟨ Eq.cong (act w) (Eq.sym (+ₚ-idˡ (p ∷ ps))) ⟩
  act w (pIₙ +ₚ (p ∷ ps)) ≡⟨ Eq.cong (act w) (Eq.cong₂ _∷_ (Eq.sym (cong₂ _,_ (+-comm (p .proj₁) ₀) (+-comm (p .proj₂) ₀))) auto) ⟩ -- (+₁-idˡ (₀ + p .proj₁ , ₀ + p .proj₂)
  act w ((p ∷ pIₙ) +ₚ (pI ∷ ps)) ≡⟨ lemma-actw-linear-+ w (p ∷ pIₙ) (pI ∷ ps) ⟩
  act w (p ∷ pIₙ) +ₚ act w (pI ∷ ps) ≡⟨ Eq.cong (_+ₚ act w (pI ∷ ps)) (lemma-actw-linear0 w (eqz , eqx) p) ⟩
  (p ∷ pIₙ) +ₚ act w (pI ∷ ps) ≡⟨ Eq.cong ((p ∷ pIₙ) +ₚ_) (Eq.sym (lemma-aux-vec n (act w (pI ∷ ps)))) ⟩
  (p ∷ pIₙ) +ₚ (head (act w (pI ∷ ps)) ∷ tail (act w (pI ∷ ps))) ≡⟨ Eq.cong (\ □ → (p ∷ pIₙ) +ₚ (□ ∷ tail (act w (pI ∷ ps)))) aux9 ⟩
  (p ∷ pIₙ) +ₚ (pI ∷ tail (act w (pI ∷ ps))) ≡⟨ auto ⟩
  (p +₁ pI) ∷ (pIₙ +ₚ tail (act w (pI ∷ ps))) ≡⟨ Eq.cong₂ _∷_ (+₁-idˡ p) (+ₚ-idˡ (tail (act w (pI ∷ ps)))) ⟩
  p ∷ tail (act w (pI ∷ ps)) ∎
  where
  open ≡-Reasoning
  pab = pasXZ p
  a = pab .proj₁
  b = pab .proj₂ .proj₁
  eq = pab .proj₂ .proj₂

  aux2a : ∀ p → sform (p ∷ pIₙ) (act w (pI ∷ ps)) ≡ ₀
  aux2a p = begin
    sform (p ∷ pIₙ) (act w (pI ∷ ps)) ≡⟨ Eq.cong (\ □ → sform □ (act w (pI ∷ ps))) (Eq.sym (lemma-actw-linear0 w (eqz , eqx) p)) ⟩
    sform (act w (p ∷ pIₙ)) (act w (pI ∷ ps)) ≡⟨ sform-preserving w (p ∷ pIₙ) ((pI ∷ ps)) ⟩
    sform ((p ∷ pIₙ)) ((pI ∷ ps)) ≡⟨ Eq.cong₂ _+_ (lemma-sform1-pIʳ p) (lemma-sform-pIₙ-q=0 ps) ⟩
    ₀ ∎

  aux5 : ∀ p → let ps' = act w (pI ∷ ps) in sform (p ∷ pIₙ) (head ps' ∷ tail ps') ≡ ₀
  aux5 p = let ps' = act w (pI ∷ ps) in begin
    sform (p ∷ pIₙ) (head ps' ∷ tail ps') ≡⟨ Eq.cong (sform (p ∷ pIₙ)) (lemma-aux-vec n ps') ⟩
    sform (p ∷ pIₙ) ps' ≡⟨ aux2a p ⟩
    ₀ ∎

  aux7 : let ps' = act w (pI ∷ ps) in sform1 pX (head ps') ≡ ₀
  aux7 = let ps' = act w (pI ∷ ps) in begin
    sform1 pX (head ps') ≡⟨ Eq.sym (+-identityʳ (sform1 pX (head ps'))) ⟩
    sform1 pX (head ps') + ₀ ≡⟨ Eq.cong (sform1 pX (head ps') +_) (Eq.sym (lemma-sform-pIₙ-q=0 (tail ps'))) ⟩
    sform1 pX (head ps') + sform (pIₙ) (tail ps') ≡⟨ auto ⟩
    sform (pX ∷ pIₙ) (head ps' ∷ tail ps') ≡⟨ Eq.cong (sform (pX ∷ pIₙ)) (lemma-aux-vec n ps') ⟩
    sform (pX ∷ pIₙ) (ps') ≡⟨ aux2a pX ⟩
    ₀ ∎

  aux8 : let ps' = act w (pI ∷ ps) in sform1 pZ (head ps') ≡ ₀
  aux8 = let ps' = act w (pI ∷ ps) in begin
    sform1 pZ (head ps') ≡⟨ Eq.sym (+-identityʳ (sform1 pZ (head ps'))) ⟩
    sform1 pZ (head ps') + ₀ ≡⟨ Eq.cong (sform1 pZ (head ps') +_) (Eq.sym (lemma-sform-pIₙ-q=0 (tail ps'))) ⟩
    sform1 pZ (head ps') + sform (pIₙ) (tail ps') ≡⟨ auto ⟩
    sform (pZ ∷ pIₙ) (head ps' ∷ tail ps') ≡⟨ Eq.cong (sform (pZ ∷ pIₙ)) (lemma-aux-vec n ps') ⟩
    sform (pZ ∷ pIₙ) (ps') ≡⟨ aux2a pZ ⟩
    ₀ ∎

  aux9 : let ps' = act w (pI ∷ ps) in (head ps') ≡ pI
  aux9 = let ps' = act w (pI ∷ ps) in lemma-sform1-XZ (head ps') (aux8 , aux7)

lemma-fix1 : ∀ {n} w → let f = act {₁₊ n} w in
  f pZ₀ ≡ pZ₀ × f pX₀ ≡ pX₀ →
  ∀ ps qs → sform (f (pI ∷ ps)) (f (pI ∷ qs)) ≡ sform {n} (tail (f (pI ∷ ps))) (tail (f (pI ∷ qs)))
lemma-fix1 {n} w (eqz , eqx) ps qs = begin
  sform (act w (pI ∷ ps)) (act w (pI ∷ qs)) ≡⟨ Eq.cong₂ (\ s1 s2 → sform (s1) (s2)) (lemma-actw-fix-p0 w (eqz , eqx) pI ps) (lemma-actw-fix-p0 w (eqz , eqx) pI qs) ⟩
  sform (pI ∷ tail (act w (pI ∷ ps))) (pI ∷ tail (act w (pI ∷ qs))) ≡⟨ auto ⟩
  sform1 pI pI + sform (tail (act w (pI ∷ ps))) (tail (act w (pI ∷ qs))) ≡⟨ cong (_+ sform (tail (act w (pI ∷ ps))) (tail (act w (pI ∷ qs)))) (sform-pI-q=0 pI) ⟩
  ₀ + sform (tail (act w (pI ∷ ps))) (tail (act w (pI ∷ qs))) ≡⟨ +-identityˡ (sform (tail (act w (pI ∷ ps))) (tail (act w (pI ∷ qs)))) ⟩
  sform (tail (act w (pI ∷ ps))) (tail (act w (pI ∷ qs))) ∎
  where
  open ≡-Reasoning


lemma-aux-sformXZ : ∀ {n} → sform {₁₊ n} pZ₀ pX₀ ≡ ₁ 
lemma-aux-sformXZ {n} = begin
  sform {₁₊ n} pZ₀ pX₀ ≡⟨ auto ⟩
  sform1 pZ pX + sform {n} pIₙ pIₙ ≡⟨ Eq.cong (sform1 pZ pX +_) (lemma-sform-pIₙ-q=0 {n} pIₙ) ⟩
  sform1 pZ pX + ₀ ≡⟨ +-identityʳ (sform1 pZ pX) ⟩
  sform1 pZ pX ≡⟨ lemma-sform-ZX1 ⟩
  ₁ ∎
  where
  open ≡-Reasoning

lemma-aux-act-[] : ∀ w → act w [] ≡ []
lemma-aux-act-[] ε = auto
lemma-aux-act-[] (w • w₁) rewrite lemma-aux-act-[] w₁ = lemma-aux-act-[] w


lemma-fundamental : ∀ {n} (w : Word (Gen (₁₊ n))) → let f = act w in 
  ∃ \ lm → act ([ lm ]ˡᵐ • w) pZ₀ ≡ pZ₀ × act ([ lm ]ˡᵐ • w) pX₀ ≡ pX₀
lemma-fundamental {n} w  = lm
  where
  open ≡-Reasoning
  f = act w
  aux : sform (f pZ₀) (f pX₀) ≡ ₁    
  aux = begin
    sform (f pZ₀) (f pX₀) ≡⟨ sform-preserving w pZ₀ pX₀ ⟩
    sform {₁₊ n} pZ₀ pX₀ ≡⟨ lemma-aux-sformXZ {n} ⟩
    ₁ ∎

  lm = Theorem-LM (f pZ₀) (f pX₀) aux

lemma-fundamental' : ∀ {n} (f : Pauli (₁₊ n) → Pauli (₁₊ n)) →
  (hyp : ∀ ps qs → sform (f ps) (f qs) ≡ sform ps qs) → 
  ∃ \ lm → act [ lm ]ˡᵐ (f pZ₀) ≡ pZ₀ × act [ lm ]ˡᵐ (f pX₀) ≡ pX₀
lemma-fundamental' {n} f hyp  = lm
  where
  open ≡-Reasoning

  aux : sform (f pZ₀) (f pX₀) ≡ ₁    
  aux = begin
    sform (f pZ₀) (f pX₀) ≡⟨ hyp pZ₀ pX₀ ⟩
    sform {₁₊ n} pZ₀ pX₀ ≡⟨ lemma-aux-sformXZ {n} ⟩
    ₁ ∎

  lm = Theorem-LM (f pZ₀) (f pX₀) aux


IsLinear : ∀ {n} (f : Pauli n → Pauli n) → Set
IsLinear f =
  (∀ ps qs → f (ps +ₚ qs) ≡ f ps +ₚ f qs) ×
  (∀ k ps → f (k *ₚ ps) ≡ k *ₚ f ps)

Symplectic : ∀ {n} (f : Pauli n → Pauli n) → Set
Symplectic {n} f = ∀ ps qs → sform (f ps) (f qs) ≡ sform ps qs


Fix-P₀ : ∀ {n} (f : Pauli (suc n) → Pauli (suc n)) → Set
Fix-P₀ {n} f = ∀ p ps → f (p ∷ ps) ≡ p ∷ tail (f (pI ∷ ps))

Fix-Z₀-X₀ : ∀ {n} (f : Pauli (suc n) → Pauli (suc n)) → Set
Fix-Z₀-X₀ {n} f = f pZ₀ ≡ pZ₀ × f pX₀ ≡ pX₀

lemma-symplectic-compose : ∀ {n} (f h : Pauli n → Pauli n) → Symplectic f → Symplectic h → Symplectic (h ∘ f)
lemma-symplectic-compose f h fs hs ps qs = begin
  sform ((h ∘ f) ps) ((h ∘ f) qs) ≡⟨ hs (f ps) (f qs) ⟩
  sform ((f) ps) ((f) qs) ≡⟨ fs ps qs ⟩
  sform ps qs ∎
  where open ≡-Reasoning


lemma-linear-compose : ∀ {n} (f h : Pauli n → Pauli n) → IsLinear f → IsLinear h → IsLinear (h ∘ f)
lemma-linear-compose f h (p , m) (gp , gm) = c1 , c2
  where
  open ≡-Reasoning
  g = h ∘ f
  c1 : ∀ ps qs → g (ps +ₚ qs) ≡ g ps +ₚ g qs
  c1 ps qs = begin
    g (ps +ₚ qs) ≡⟨ Eq.cong h (p ps qs) ⟩
    h (f (ps) +ₚ f (qs)) ≡⟨ gp (f (ps)) (f (qs)) ⟩
    h (f (ps)) +ₚ h (f (qs)) ≡⟨ auto ⟩
    g ps +ₚ g qs ∎

  c2 : ∀ k ps → g (k *ₚ ps) ≡ k *ₚ g ps
  c2 k ps = begin
    g (k *ₚ ps) ≡⟨ auto ⟩
    h (f (k *ₚ (ps))) ≡⟨ Eq.cong h (m k (ps)) ⟩
    h (k *ₚ (f (ps))) ≡⟨ gm k (f (ps)) ⟩
    (k *ₚ h (f (ps))) ≡⟨ auto ⟩
    k *ₚ g ps ∎

lemma-tail-linear-+ : ∀ {n} → (ps qs : Pauli (suc n)) → tail (ps +ₚ qs) ≡ tail ps +ₚ tail qs
lemma-tail-linear-+ {n} (x ∷ ps) (x₁ ∷ qs) = auto

lemma-tail-linear-* : ∀ {n} k → (ps : Pauli (suc n)) → tail (k *ₚ ps) ≡ k *ₚ tail ps
lemma-tail-linear-* {n} k (x ∷ ps) = auto

lemma-actw-linear : ∀ {n} (w : Word (Gen n)) → IsLinear (act w)
lemma-actw-linear {n} w = lemma-actw-linear-+ w , lemma-actw-linear-* w

lemma-sub :  ∀ {n} (f : Pauli (₁₊ n) → Pauli (suc n)) →
  IsLinear f → let g = \ ps → tail (f (pI ∷ ps)) in IsLinear g
lemma-sub {n} f (p , m) = c1 , c2
  where
  open ≡-Reasoning
  g = \ ps → tail (f (pI ∷ ps))
  c1 : ∀ ps qs → g (ps +ₚ qs) ≡ g ps +ₚ g qs
  c1 ps qs = begin
    g (ps +ₚ qs) ≡⟨ auto ⟩
    tail (f (pI ∷ (ps +ₚ qs))) ≡⟨ Eq.cong tail (p ((₀ , ₀) ∷ ps) (pI ∷ qs)) ⟩
    tail (f (pI ∷ ps) +ₚ f (pI ∷ qs)) ≡⟨ lemma-tail-linear-+ (f (pI ∷ ps)) (f (pI ∷ qs)) ⟩
    tail (f (pI ∷ ps)) +ₚ tail (f (pI ∷ qs)) ≡⟨ auto ⟩
    g ps +ₚ g qs ∎

  lemma-aux : ∀ {n} k (ps : Pauli n) → pI ∷ (k *ₚ ps) ≡ k *ₚ (pI ∷ ps)
  lemma-aux k ps = Eq.cong₂ _∷_ (Eq.sym (*₁-zeroʳ k)) auto

  c2 : ∀ k ps → g (k *ₚ ps) ≡ k *ₚ g ps
  c2 k ps = begin
    g (k *ₚ ps) ≡⟨ auto ⟩
    tail (f (pI ∷ (k *ₚ ps))) ≡⟨ Eq.cong (\ □ → tail (f □)) (lemma-aux k ps) ⟩
    tail (f (k *ₚ (pI ∷ ps))) ≡⟨ Eq.cong tail (m k (pI ∷ ps)) ⟩
    tail (k *ₚ (f (pI ∷ ps))) ≡⟨ lemma-tail-linear-* k (f (pI ∷ ps)) ⟩
    (k *ₚ tail (f (pI ∷ ps))) ≡⟨ auto ⟩
    k *ₚ g ps ∎

lemma-actw-linear0' : ∀ {n} (f : Pauli (suc n) → Pauli (suc n)) →
  IsLinear f → 
  Fix-Z₀-X₀ f →
  ∀ p → (f (p ∷ pIₙ)) ≡ p ∷ pIₙ
lemma-actw-linear0' f (fp , fm) (eqz , eqx) p = let ps = pIₙ in begin
  f (p ∷ ps) ≡⟨ Eq.cong (\ □ → f (□ ∷ ps)) eq ⟩
  f (a *₁ pX +₁ b *₁ pZ ∷ ps) ≡⟨ Eq.cong (f) (Eq.cong₂ _∷_ auto (Eq.sym (+ₚ-idˡ pIₙ))) ⟩
  f ((a *₁ pX ∷ pIₙ) +ₚ (b *₁ pZ ∷ ps)) ≡⟨ fp ((a *₁ pX ∷ pIₙ)) ((b *₁ pZ ∷ ps)) ⟩
  f (a *₁ pX ∷ pIₙ) +ₚ f (b *₁ pZ ∷ ps) ≡⟨ Eq.cong₂ (\ s1 s2 →  f (s1) +ₚ f (s2)) (lemma-aux-kx a) (lemma-aux-kz b) ⟩
  f (a *ₚ (pX₀)) +ₚ f (b *ₚ (pZ₀)) ≡⟨ Eq.cong₂ _+ₚ_ (fm a pX₀) (fm b pZ₀) ⟩
  a *ₚ f (pX₀) +ₚ b *ₚ f (pZ₀) ≡⟨ Eq.cong₂ _+ₚ_ (Eq.cong (a *ₚ_) eqx) ((Eq.cong (b *ₚ_) eqz)) ⟩
  a *ₚ pX₀ +ₚ b *ₚ pZ₀ ≡⟨ Eq.cong₂ (\ s1 s2 → a *ₚ s1 +ₚ b *ₚ s2) (Eq.sym lemma-aux-px) (Eq.sym lemma-aux-pz) ⟩
  (a *ₚ (pX ∷ pIₙ) +ₚ b *ₚ (pZ ∷ pIₙ)) ≡⟨ auto ⟩
  (a *₁ pX +₁ b *₁ pZ ∷ a *ₚ pIₙ +ₚ b *ₚ pIₙ) ≡⟨ Eq.cong (\ □ → (□ ∷ a *ₚ pIₙ +ₚ b *ₚ pIₙ)) (Eq.sym eq) ⟩
  (p ∷ a *ₚ pIₙ +ₚ b *ₚ pIₙ) ≡⟨ Eq.cong₂ (\ s1 s2 → p ∷ s1 +ₚ s2) (lemma-pauli-zero a) (lemma-pauli-zero b) ⟩
  (p ∷ pIₙ +ₚ pIₙ) ≡⟨ auto ⟩
  p ∷ (pIₙ +ₚ pIₙ) ≡⟨ Eq.cong (p ∷_) (+ₚ-idˡ pIₙ) ⟩
  p ∷  pIₙ ∎
  where
  open ≡-Reasoning
  pab = pasXZ p
  a = pab .proj₁
  b = pab .proj₂ .proj₁
  eq = pab .proj₂ .proj₂


Linear-Symp-FixZX⇒FixP : ∀ {n} (f : Pauli (suc n) → Pauli (suc n)) →

  IsLinear f →
  Symplectic f →
  Fix-Z₀-X₀ f →
  ------------------
  Fix-P₀ f

Linear-Symp-FixZX⇒FixP {n} f (fp , fm) symp (eqz , eqx) p ps = begin
  f (p ∷ ps) ≡⟨ Eq.cong (f) (Eq.sym (+ₚ-idˡ (p ∷ ps))) ⟩
  f (pIₙ +ₚ (p ∷ ps)) ≡⟨ Eq.cong (f) (Eq.cong₂ _∷_ (Eq.sym (cong₂ _,_ (+-comm (p .proj₁) ₀) (+-comm (p .proj₂) ₀))) auto) ⟩
  f ((p ∷ pIₙ) +ₚ (pI ∷ ps)) ≡⟨ fp (p ∷ pIₙ) (pI ∷ ps) ⟩
  f (p ∷ pIₙ) +ₚ f (pI ∷ ps) ≡⟨ Eq.cong (_+ₚ f (pI ∷ ps)) (lemma-actw-linear0' f (fp , fm) (eqz , eqx) p ) ⟩
  (p ∷ pIₙ) +ₚ f (pI ∷ ps) ≡⟨ Eq.cong ((p ∷ pIₙ) +ₚ_) (Eq.sym (lemma-aux-vec n (f (pI ∷ ps)))) ⟩
  (p ∷ pIₙ) +ₚ (head (f (pI ∷ ps)) ∷ tail (f (pI ∷ ps))) ≡⟨ Eq.cong (\ □ → (p ∷ pIₙ) +ₚ (□ ∷ tail (f (pI ∷ ps)))) aux9 ⟩
  (p ∷ pIₙ) +ₚ (pI ∷ tail (f (pI ∷ ps))) ≡⟨ auto ⟩
  (p +₁ pI) ∷ (pIₙ +ₚ tail (f (pI ∷ ps))) ≡⟨ Eq.cong₂ _∷_ (+₁-idˡ p) (+ₚ-idˡ (tail (f (pI ∷ ps)))) ⟩
  p ∷ tail (f (pI ∷ ps)) ∎
  where

  open ≡-Reasoning
  pab = pasXZ p
  a = pab .proj₁
  b = pab .proj₂ .proj₁
  eq = pab .proj₂ .proj₂

  aux2a : ∀ p → sform (p ∷ pIₙ) (f (pI ∷ ps)) ≡ ₀
  aux2a p = begin
    sform (p ∷ pIₙ) (f (pI ∷ ps)) ≡⟨ Eq.cong (\ □ → sform □ (f (pI ∷ ps))) (Eq.sym (lemma-actw-linear0' f (fp , fm) (eqz , eqx) p )) ⟩
    sform (f (p ∷ pIₙ)) (f (pI ∷ ps)) ≡⟨ symp (p ∷ pIₙ) (pI ∷ ps) ⟩
    sform ((p ∷ pIₙ)) ((pI ∷ ps)) ≡⟨ Eq.cong₂ _+_ (lemma-sform1-pIʳ p) (lemma-sform-pIₙ-q=0 ps) ⟩
    ₀ ∎

  aux5 : ∀ p → let ps' = f (pI ∷ ps) in sform (p ∷ pIₙ) (head ps' ∷ tail ps') ≡ ₀
  aux5 p = let ps' = f (pI ∷ ps) in begin
    sform (p ∷ pIₙ) (head ps' ∷ tail ps') ≡⟨ Eq.cong (sform (p ∷ pIₙ)) (lemma-aux-vec n ps') ⟩
    sform (p ∷ pIₙ) ps' ≡⟨ aux2a p ⟩
    ₀ ∎

  aux7 : let ps' = f (pI ∷ ps) in sform1 pX (head ps') ≡ ₀
  aux7 = let ps' = f (pI ∷ ps) in begin
    sform1 pX (head ps') ≡⟨ Eq.sym (+-identityʳ (sform1 pX (head ps'))) ⟩
    sform1 pX (head ps') + ₀ ≡⟨ Eq.cong (sform1 pX (head ps') +_) (Eq.sym (lemma-sform-pIₙ-q=0 (tail ps'))) ⟩
    sform1 pX (head ps') + sform (pIₙ) (tail ps') ≡⟨ auto ⟩
    sform (pX ∷ pIₙ) (head ps' ∷ tail ps') ≡⟨ Eq.cong (sform (pX ∷ pIₙ)) (lemma-aux-vec n ps') ⟩
    sform (pX ∷ pIₙ) (ps') ≡⟨ aux2a pX ⟩
    ₀ ∎

  aux8 : let ps' = f (pI ∷ ps) in sform1 pZ (head ps') ≡ ₀
  aux8 = let ps' = f (pI ∷ ps) in begin
    sform1 pZ (head ps') ≡⟨ Eq.sym (+-identityʳ (sform1 pZ (head ps'))) ⟩
    sform1 pZ (head ps') + ₀ ≡⟨ Eq.cong (sform1 pZ (head ps') +_) (Eq.sym (lemma-sform-pIₙ-q=0 (tail ps'))) ⟩
    sform1 pZ (head ps') + sform (pIₙ) (tail ps') ≡⟨ auto ⟩
    sform (pZ ∷ pIₙ) (head ps' ∷ tail ps') ≡⟨ Eq.cong (sform (pZ ∷ pIₙ)) (lemma-aux-vec n ps') ⟩
    sform (pZ ∷ pIₙ) (ps') ≡⟨ aux2a pZ ⟩
    ₀ ∎

  aux9 : let ps' = f (pI ∷ ps) in (head ps') ≡ pI
  aux9 = let ps' = f (pI ∷ ps) in lemma-sform1-XZ (head ps') (aux8 , aux7)

-- lemma-fix-subform : ∀ {n} (f : Pauli (suc n) → Pauli (suc n)) → IsLinear f → Symplectic f →
--   f pZ₀ ≡ pZ₀ × f pX₀ ≡ pX₀ →
--   ∀ ps qs → sform (f (pI ∷ ps)) (f (pI ∷ qs)) ≡ sform {n} (tail (f (pI ∷ ps))) (tail (f (pI ∷ qs)))
-- lemma-fix1' {n} w (eqz , eqx) ps qs = begin
--   sform (act w (pI ∷ ps)) (act w (pI ∷ qs)) ≡⟨ Eq.cong₂ (\ s1 s2 → sform (s1) (s2)) (lemma-actw-fix-p0 w (eqz , eqx) pI ps) (lemma-actw-fix-p0 w (eqz , eqx) pI qs) ⟩
--   sform (pI ∷ tail (act w (pI ∷ ps))) (pI ∷ tail (act w (pI ∷ qs))) ≡⟨ auto ⟩
--   sform (tail (act w (pI ∷ ps))) (tail (act w (pI ∷ qs))) ∎
--   where
--   open ≡-Reasoning


Linear-Symp-⇒FixP⇒ : ∀ {n} (f : Pauli (suc n) → Pauli (suc n)) → let g = \ ps → tail (f (pI ∷ ps)) in

  IsLinear f →
  Symplectic f →
  Fix-P₀ f → 
  -------------------------
  IsLinear g × Symplectic g

Linear-Symp-⇒FixP⇒ {n} f fl@(fa , fm) symp fp0 = (lemma-sub f fl) , claim
  where
  open ≡-Reasoning
  claim : Symplectic (λ ps → tail (f (pI ∷ ps)))
  claim ps qs = begin
    sform (tail (f (pI ∷ ps))) (tail (f (pI ∷ qs))) ≡⟨ Eq.sym (+-identityˡ (sform (tail (f (pI ∷ ps))) (tail (f (pI ∷ qs))))) ⟩
    ₀ + sform (tail (f (pI ∷ ps))) (tail (f (pI ∷ qs))) ≡⟨ cong (_+ sform (tail (f (pI ∷ ps))) (tail (f (pI ∷ qs)))) (sym (sform-pI-q=0 pI)) ⟩
    sform (pI ∷ tail (f (pI ∷ ps))) (pI ∷ tail (f (pI ∷ qs))) ≡⟨ Eq.cong₂ sform (Eq.sym (fp0 pI ps)) (Eq.sym (fp0 pI qs)) ⟩
    sform ((f (pI ∷ ps))) ((f (pI ∷ qs))) ≡⟨ symp (pI ∷ ps) (pI ∷ qs) ⟩ 
    sform (((pI ∷ ps))) (((pI ∷ qs))) ≡⟨ cong (_+ sform ps qs) (sform-pI-q=0 pI) ⟩ 
    ₀ + sform ps qs ≡⟨ +-identityˡ _ ⟩ 
    sform ps qs ∎


act-nf : ∀ {n} → NF n → Pauli n → Pauli n
act-nf {₀} nf [] = []
act-nf {₁₊ n} (ih , lm) ps = let s1 = (act [ lm ]ˡᵐ ps) in head s1 ∷ act-nf ih (tail s1)



-- This lemma says any linear symplectic fuction f betwen 2n-dim ℤₚ
-- vector spaces has a normal form that is an inverse of f. Normal
-- forms are the box normal forms in our paper and webpage.

lemma-invnf : ∀ {n : ℕ} →

  ∀ (f : Pauli n → Pauli n) →
  IsLinear f →
  Symplectic f →
  -----------------------------
  ∃ \ nf → (act-nf nf) ∘ f ≗ id

-- Here, Pauli n = ℤₚ²ⁿ, IsLinear f means f is linear, Symplectic f
-- means f is symplectic, i.e. f preserves symplectic form.

lemma-invnf {₀} f fl symp = tt , claim
  where
  claim : (p : Pauli ₀) → act-nf tt (f p) ≡ p
  claim [] with f []
  ... | [] = auto
lemma-invnf {₁₊ n} f fl symp = (ih , lm) , claim
  where
  open ≡-Reasoning

  lmp = lemma-fundamental' f symp
  lm = lmp .proj₁

  lmf = act [ lm ]ˡᵐ ∘ f

  lmfl : IsLinear lmf
  lmfl = lemma-linear-compose f (act [ lm ]ˡᵐ) fl (lemma-actw-linear [ lm ]ˡᵐ)

  lmf-symp : Symplectic lmf
  lmf-symp = lemma-symplectic-compose f (act [ lm ]ˡᵐ) symp (sform-preserving [ lm ]ˡᵐ)

  lmf-fp0 : Fix-P₀ lmf
  lmf-fp0 = Linear-Symp-FixZX⇒FixP lmf lmfl lmf-symp (lmp .proj₂)

  g : Pauli n → Pauli n
  g ps = tail (lmf (pI ∷ ps))

  gls = Linear-Symp-⇒FixP⇒ lmf lmfl lmf-symp lmf-fp0

  ihp = lemma-invnf g (gls .proj₁) (gls .proj₂)
  ih = ihp .proj₁


  claim : ∀ p → act-nf (ih , lm) (f p) ≡ p
  claim qs@(p ∷ ps) = let s1 = act [ lm ]ˡᵐ (f qs) in begin
    act-nf (ih , lm) (f qs) ≡⟨ auto ⟩
    head s1 ∷ act-nf ih (tail s1) ≡⟨ Eq.cong₂ _∷_ auto (Eq.cong (act-nf ih) (Eq.cong tail (lmf-fp0 p ps))) ⟩
    head s1 ∷ act-nf ih (g ps) ≡⟨ Eq.cong₂ _∷_ auto (ihp .proj₂ ps) ⟩
    head s1 ∷ ps ≡⟨ Eq.cong (_∷ ps) (Eq.cong head (lmf-fp0 p ps)) ⟩
    head (p ∷ tail (f (pI ∷ ps))) ∷ ps ≡⟨ auto ⟩
    p ∷ ps ≡⟨ auto ⟩
    qs ∎

sform1-antisym' : ∀ (p q : Pauli1) -> sform1 p q ≡ - sform1 q p
sform1-antisym' p@(a , b) q@(c , d) = begin
  sform1 (a , b) (c , d) ≡⟨ auto ⟩
  (- a) * d + c * b ≡⟨ +-comm (- a * d) (c * b) ⟩
  c * b + - a * d ≡⟨ Eq.cong₂ _+_ (Eq.cong (_* b) (Eq.sym (-‿involutive c))) auto ⟩
  - - c * b + - a * d ≡⟨ Eq.cong₂ _+_ (Eq.sym (-‿distribˡ-* (- c) b)) (Eq.sym (-‿distribˡ-* a d)) ⟩
  - (- c * b) + - (a * d) ≡⟨ -‿+-comm (- c * b) (a * d) ⟩
  - ((- c) * b + a * d) ≡⟨ auto ⟩
  - sform1 (c , d) (a , b) ∎
  where
  open ≡-Reasoning


open Symplectic-Derived-GroupLike


-- This lemma says that for any word in Gen n, there exist a normal
-- form that has the same action on Paulis.

lemma-nf : ∀ {n : ℕ} → 

  ∀ (w : Word (Gen n)) → 
  -----------------------------
  ∃ \ nf → (act-nf nf) ≗ act w

lemma-nf {n} w = nf , claim
  where
  open ≡-Reasoning
  open Group-Lemmas (Gen n) (n QRel,_===_) grouplike renaming (_⁻¹ to _⁻¹ʷ)
  open Group-Action (Pauli n) (Gen n) (n QRel,_===_) grouplike act1 (lemma-act-cong-ax {n} _ _)

  invnf = lemma-invnf (act (w ⁻¹ʷ)) (lemma-actw-linear (w ⁻¹ʷ)) (sform-preserving ( w ⁻¹ʷ))
  nf = invnf .proj₁

  claim : (act-nf nf) ≗ act w
  claim p = begin
    act-nf nf p ≡⟨ auto ⟩
    act-nf nf (act ε p) ≡⟨ Eq.sym (Eq.cong (act-nf nf) (act-cong (w ⁻¹ʷ • w) ε p  lemma-left-inverse)) ⟩
    act-nf nf (act (w ⁻¹ʷ • w) p) ≡⟨ auto ⟩
    act-nf nf (act (w ⁻¹ʷ) (act w p)) ≡⟨ invnf .proj₂ (act w p) ⟩
    act w p ∎


