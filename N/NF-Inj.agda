-- NOTE: --safe is intentionally omitted: lemma-nf1-head-inj, lemma-cosets2-head-inj,
-- lemma-ml-head-inj and lemma-lm-inj₁≁inj₂ remain postulated (head-injectivity of the
-- normal-form action — research-level). Restore {-# OPTIONS --safe #-} once they are proven.
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
import Data.Vec as V
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



module N.NF-Inj (p-2 : ℕ) (p-prime : Prime (2+ p-2))  where

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
open Eq hiding ([_])

open import N.NF p-2 p-prime using (act-nf ; lemma-aux-vec ; lemma-actw-pIₙ ; _+₁_)
open Symplectic-Derived-GroupLike

-- The NF circuit word gives the same Pauli action as act-nf.
-- Proof: structural induction on NF n, using lemma-act-↑ for the lifting step.
lemma-act-nf : ∀ {n} (nf : NF n) → act [ nf ] ≗ act-nf nf
lemma-act-nf {₀} tt [] = auto
lemma-act-nf {₁₊ n} (ih , lm) ps =
  let s = act [ lm ]ˡᵐ ps in
  begin
    act [ (ih , lm) ] ps                          ≡⟨ auto ⟩
    act ([ ih ] ↑) (act [ lm ]ˡᵐ ps)             ≡⟨ Eq.cong (act ([ ih ] ↑)) (Eq.sym (lemma-aux-vec n s)) ⟩
    act ([ ih ] ↑) (head s ∷ tail s)              ≡⟨ lemma-act-↑ [ ih ] (head s) (tail s) ⟩
    head s ∷ act [ ih ] (tail s)                   ≡⟨ Eq.cong (head s ∷_) (lemma-act-nf ih (tail s)) ⟩
    head s ∷ act-nf ih (tail s)                    ≡⟨ auto ⟩
    act-nf (ih , lm) ps                            ∎


-- Sub-postulates for lemma-lm-head-inj.
postulate
  -- n=1: NF1 elements are distinguished by head of Pauli action.
  lemma-nf1-head-inj : ∀ (lm₁ lm₂ : NF1) →
    (∀ ps → head (act [ lm₁ ]ˡᵐ ps) ≡ head (act [ lm₂ ]ˡᵐ ps)) → lm₁ ≡ lm₂

  -- n=2: Cosets2 elements are distinguished by head of Pauli action.
  lemma-cosets2-head-inj : ∀ (lm₁ lm₂ : Cosets2) →
    (∀ ps → head (act [ lm₁ ]ˡᵐ ps) ≡ head (act [ lm₂ ]ˡᵐ ps)) → lm₁ ≡ lm₂

  -- The M×L' branch (inj₁) and D×LM branch (inj₂) produce distinct head outputs.
  lemma-lm-inj₁≁inj₂ : ∀ {n} (m : M (₃₊ n)) (l : L' (₃₊ n)) (d : D) (lm' : LM (₂₊ n)) →
    (∀ ps → head (act ([ m ]ᵐ • [ l ]ˡ') ps) ≡ head (act ([ d ]ᵈ • [ lm' ]ˡᵐ ↑) ps)) → ⊥

  -- M×L' action is head-injective.
  lemma-ml-head-inj : ∀ {n} (m₁ m₂ : M (₃₊ n)) (l₁ l₂ : L' (₃₊ n)) →
    (∀ ps → head (act ([ m₁ ]ᵐ • [ l₁ ]ˡ') ps) ≡ head (act ([ m₂ ]ᵐ • [ l₂ ]ˡ') ps)) →
    m₁ ≡ m₂ × l₁ ≡ l₂

-- D-box pZ-prefix with pI second entry: head(act [d]ᵈ (pZ ∷ pI ∷ t)) = (₀, d.proj₁).
lemma-dbox-pZ-pI : ∀ {n} (d : D) (t : Pauli n) →
  head (act [ d ]ᵈ (pZ ∷ pI ∷ t)) ≡ (₀ , d .proj₁)
lemma-dbox-pZ-pI {n} (₀ , dv) t = begin
  head (act [ ₀ , dv ]ᵈ (pZ ∷ pI ∷ t))
    ≡⟨ Eq.cong head (lemma-act-Ex (₀ , ₁ + ₀ * (- dv)) (₀ , ₀ + ₀ * (- dv)) t) ⟩
  (₀ , ₀ + ₀ * (- dv))
    ≡⟨ Eq.cong (₀ ,_) (Eq.trans (Eq.cong (₀ +_) (*-zeroˡ (- dv))) (+-identityʳ ₀)) ⟩
  (₀ , ₀) ∎
lemma-dbox-pZ-pI {n} (c@(₁₊ c') , dv) t = begin
  head (act [ c , dv ]ᵈ (pZ ∷ pI ∷ t)) ≡⟨ auto ⟩
  head (act ([ ₀ , ₁ ]ᵈ • ⟦ (c , λ ()) ⁻¹ , HS^ -dv/c ⟧ₘ₊) (pZ ∷ pI ∷ t))
    ≡⟨ Eq.cong (λ z → head (act ([ ₀ , ₁ ]ᵈ • ⟦ (c , λ ()) ⁻¹ ⟧ₘ) z)) (lemma-HS-x -dv/c ₀ ₁ (pI ∷ t)) ⟩
  head (act ([ ₀ , ₁ ]ᵈ • ⟦ (c , λ ()) ⁻¹ ⟧ₘ) ((- (₁ + ₀ * -dv/c) , ₀) ∷ pI ∷ t))
    ≡⟨ Eq.cong (λ z → head (act ([ ₀ , ₁ ]ᵈ • ⟦ (c , λ ()) ⁻¹ ⟧ₘ) ((z , ₀) ∷ pI ∷ t))) eq1 ⟩
  head (act ([ ₀ , ₁ ]ᵈ • ⟦ (c , λ ()) ⁻¹ ⟧ₘ) ((- ₁ , ₀) ∷ pI ∷ t))
    ≡⟨ Eq.cong (λ z → head (act [ ₀ , ₁ ]ᵈ z)) (lemma-M (- ₁) ₀ (pI ∷ t) ((c , λ ()) ⁻¹)) ⟩
  head (act [ ₀ , ₁ ]ᵈ ((- ₁ * c⁻¹⁻¹ , ₀ * c⁻¹) ∷ pI ∷ t))
    ≡⟨ Eq.cong (λ z → head (act [ ₀ , ₁ ]ᵈ ((z , ₀ * c⁻¹) ∷ pI ∷ t))) eq2 ⟩
  head (act [ ₀ , ₁ ]ᵈ ((- c , ₀ * c⁻¹) ∷ pI ∷ t))
    ≡⟨ Eq.cong (λ z → head (act [ ₀ , ₁ ]ᵈ ((- c , z) ∷ pI ∷ t))) (*-zeroˡ c⁻¹) ⟩
  head (act [ ₀ , ₁ ]ᵈ ((- c , ₀) ∷ (₀ , ₀) ∷ t))
    ≡⟨ Eq.cong head (lemma-act-Ex (- c , ₀ + ₀ * (- ₁)) (₀ , ₀ + (- c) * (- ₁)) t) ⟩
  (₀ , ₀ + (- c) * (- ₁))
    ≡⟨ Eq.cong (₀ ,_) eq3 ⟩
  (₀ , c) ∎
  where
  c⁻¹ = ((c , λ ()) ⁻¹) .proj₁
  c⁻¹⁻¹ = (((c , λ ()) ⁻¹) ⁻¹) .proj₁
  -dv/c = - dv * c⁻¹
  eq1 : - (₁ + ₀ * -dv/c) ≡ - ₁
  eq1 = Eq.cong -_ (Eq.trans (Eq.cong (₁ +_) (*-zeroˡ -dv/c)) (+-identityʳ ₁))
  eq2 : - ₁ * c⁻¹⁻¹ ≡ - c
  eq2 = Eq.trans (-1*x≈-x c⁻¹⁻¹) (Eq.cong -_ (inv-involutive (c , λ ())))
  eq3 : ₀ + (- c) * (- ₁) ≡ c
  eq3 = Eq.trans (+-identityˡ ((- c) * (- ₁)))
        (Eq.trans (*-comm (- c) (- ₁)) (Eq.trans (-1*x≈-x (- c)) (-‿involutive c)))

-- D-box pX-prefix with pI second entry: head(act [d]ᵈ (pX ∷ pI ∷ t)) = (₀, -d.proj₂).
lemma-dbox-pX-pI : ∀ {n} (d : D) (t : Pauli n) →
  head (act [ d ]ᵈ (pX ∷ pI ∷ t)) ≡ (₀ , - d .proj₂)
lemma-dbox-pX-pI {n} (₀ , dv) t = begin
  head (act [ ₀ , dv ]ᵈ (pX ∷ pI ∷ t))
    ≡⟨ Eq.cong head (lemma-act-Ex (₁ , ₀ + ₀ * (- dv)) (₀ , ₀ + ₁ * (- dv)) t) ⟩
  (₀ , ₀ + ₁ * (- dv))
    ≡⟨ Eq.cong (₀ ,_) (Eq.trans (+-identityˡ (₁ * (- dv))) (*-identityˡ (- dv))) ⟩
  (₀ , - dv) ∎
lemma-dbox-pX-pI {n} (c@(₁₊ c') , dv) t = begin
  head (act [ c , dv ]ᵈ (pX ∷ pI ∷ t)) ≡⟨ auto ⟩
  head (act ([ ₀ , ₁ ]ᵈ • ⟦ (c , λ ()) ⁻¹ , HS^ -dv/c ⟧ₘ₊) (pX ∷ pI ∷ t))
    ≡⟨ Eq.cong (λ z → head (act ([ ₀ , ₁ ]ᵈ • ⟦ (c , λ ()) ⁻¹ ⟧ₘ) z)) (lemma-HS-x -dv/c ₁ ₀ (pI ∷ t)) ⟩
  head (act ([ ₀ , ₁ ]ᵈ • ⟦ (c , λ ()) ⁻¹ ⟧ₘ) ((- (₀ + ₁ * -dv/c) , ₁) ∷ pI ∷ t))
    ≡⟨ Eq.cong (λ z → head (act [ ₀ , ₁ ]ᵈ z)) (lemma-M (- (₀ + ₁ * -dv/c)) ₁ (pI ∷ t) ((c , λ ()) ⁻¹)) ⟩
  head (act [ ₀ , ₁ ]ᵈ ((- (₀ + ₁ * -dv/c) * c⁻¹⁻¹ , ₁ * c⁻¹) ∷ pI ∷ t))
    ≡⟨ Eq.cong (λ z → head (act [ ₀ , ₁ ]ᵈ ((z , ₁ * c⁻¹) ∷ pI ∷ t))) eqA ⟩
  head (act [ ₀ , ₁ ]ᵈ ((dv , ₁ * c⁻¹) ∷ pI ∷ t))
    ≡⟨ Eq.cong head (lemma-act-Ex (dv , ₁ * c⁻¹ + ₀ * (- ₁)) (₀ , ₀ + dv * (- ₁)) t) ⟩
  (₀ , ₀ + dv * (- ₁))
    ≡⟨ Eq.cong (₀ ,_) eqB ⟩
  (₀ , - dv) ∎
  where
  c⁻¹ = ((c , λ ()) ⁻¹) .proj₁
  c⁻¹⁻¹ = (((c , λ ()) ⁻¹) ⁻¹) .proj₁
  -dv/c = - dv * c⁻¹
  eqA : - (₀ + ₁ * -dv/c) * c⁻¹⁻¹ ≡ dv
  eqA = Eq.trans (Eq.cong (λ w → - w * c⁻¹⁻¹) (Eq.trans (+-identityˡ (₁ * -dv/c)) (*-identityˡ -dv/c)))
        (Eq.trans (Eq.cong (_* c⁻¹⁻¹) (Eq.trans (Eq.cong -_ (Eq.sym (-‿distribˡ-* dv c⁻¹))) (-‿involutive (dv * c⁻¹))))
        (Eq.trans (Eq.cong (dv * c⁻¹ *_) (inv-involutive (c , λ ())))
        (Eq.trans (*-assoc dv c⁻¹ c)
        (Eq.trans (Eq.cong (dv *_) (Eq.trans (*-comm c⁻¹ c) (lemma-⁻¹ʳ c {{nztoℕ {y = c} {neq0 = λ ()}}})))
        (*-identityʳ dv)))))
  eqB : ₀ + dv * (- ₁) ≡ - dv
  eqB = Eq.trans (+-identityˡ (dv * (- ₁))) (Eq.trans (*-comm dv (- ₁)) (-1*x≈-x dv))

-- D-box pZ-transparency: head(act [d]ᵈ (pZ ∷ q ∷ t)) = q +₁ (₀, d.proj₁).
lemma-dbox-pZ-head : ∀ {n} (d : D) (q : Pauli1) (t : Pauli n) →
  head (act [ d ]ᵈ (pZ ∷ q ∷ t)) ≡ q +₁ (₀ , d .proj₁)
lemma-dbox-pZ-head {n} (₀ , dv) (qa , qb) t = begin
  head (act [ ₀ , dv ]ᵈ (pZ ∷ (qa , qb) ∷ t))
    ≡⟨ Eq.cong head (lemma-act-Ex (₀ , ₁ + qa * (- dv)) (qa , qb + ₀ * (- dv)) t) ⟩
  (qa , qb + ₀ * (- dv))
    ≡⟨ ≡×≡⇒≡ (Eq.sym (+-identityʳ qa) , Eq.cong (qb +_) (*-zeroˡ (- dv))) ⟩
  (qa + ₀ , qb + ₀) ∎
lemma-dbox-pZ-head {n} (c@(₁₊ c') , dv) (qa , qb) t = begin
  head (act [ c , dv ]ᵈ (pZ ∷ (qa , qb) ∷ t)) ≡⟨ auto ⟩
  head (act ([ ₀ , ₁ ]ᵈ • ⟦ (c , λ ()) ⁻¹ , HS^ -dv/c ⟧ₘ₊) (pZ ∷ (qa , qb) ∷ t))
    ≡⟨ Eq.cong (λ z → head (act ([ ₀ , ₁ ]ᵈ • ⟦ (c , λ ()) ⁻¹ ⟧ₘ) z)) (lemma-HS-x -dv/c ₀ ₁ ((qa , qb) ∷ t)) ⟩
  head (act ([ ₀ , ₁ ]ᵈ • ⟦ (c , λ ()) ⁻¹ ⟧ₘ) ((- (₁ + ₀ * -dv/c) , ₀) ∷ (qa , qb) ∷ t))
    ≡⟨ Eq.cong (λ z → head (act ([ ₀ , ₁ ]ᵈ • ⟦ (c , λ ()) ⁻¹ ⟧ₘ) ((z , ₀) ∷ (qa , qb) ∷ t))) eq1 ⟩
  head (act ([ ₀ , ₁ ]ᵈ • ⟦ (c , λ ()) ⁻¹ ⟧ₘ) ((- ₁ , ₀) ∷ (qa , qb) ∷ t))
    ≡⟨ Eq.cong (λ z → head (act [ ₀ , ₁ ]ᵈ z)) (lemma-M (- ₁) ₀ ((qa , qb) ∷ t) ((c , λ ()) ⁻¹)) ⟩
  head (act [ ₀ , ₁ ]ᵈ ((- ₁ * c⁻¹⁻¹ , ₀ * c⁻¹) ∷ (qa , qb) ∷ t))
    ≡⟨ Eq.cong (λ z → head (act [ ₀ , ₁ ]ᵈ ((z , ₀ * c⁻¹) ∷ (qa , qb) ∷ t))) eq2 ⟩
  head (act [ ₀ , ₁ ]ᵈ ((- c , ₀ * c⁻¹) ∷ (qa , qb) ∷ t))
    ≡⟨ Eq.cong (λ z → head (act [ ₀ , ₁ ]ᵈ ((- c , z) ∷ (qa , qb) ∷ t))) (*-zeroˡ c⁻¹) ⟩
  head (act [ ₀ , ₁ ]ᵈ ((- c , ₀) ∷ (qa , qb) ∷ t))
    ≡⟨ Eq.cong head (lemma-act-Ex (- c , ₀ + qa * (- ₁)) (qa , qb + (- c) * (- ₁)) t) ⟩
  (qa , qb + (- c) * (- ₁))
    ≡⟨ ≡×≡⇒≡ (Eq.sym (+-identityʳ qa) , Eq.cong (qb +_) eq3) ⟩
  (qa + ₀ , qb + c) ∎
  where
  c⁻¹ = ((c , λ ()) ⁻¹) .proj₁
  c⁻¹⁻¹ = (((c , λ ()) ⁻¹) ⁻¹) .proj₁
  -dv/c = - dv * c⁻¹
  eq1 : - (₁ + ₀ * -dv/c) ≡ - ₁
  eq1 = Eq.cong -_ (Eq.trans (Eq.cong (₁ +_) (*-zeroˡ -dv/c)) (+-identityʳ ₁))
  eq2 : - ₁ * c⁻¹⁻¹ ≡ - c
  eq2 = Eq.trans (-1*x≈-x c⁻¹⁻¹) (Eq.cong -_ (inv-involutive (c , λ ())))
  eq3 : (- c) * (- ₁) ≡ c
  eq3 = Eq.trans (*-comm (- c) (- ₁)) (Eq.trans (-1*x≈-x (- c)) (-‿involutive c))

-- Right cancellation for componentwise addition on Pauli1.
+₁-cancelʳ : ∀ (x y c : Pauli1) → x +₁ c ≡ y +₁ c → x ≡ y
+₁-cancelʳ (a₁ , b₁) (a₂ , b₂) (c₁ , c₂) eq =
  ≡×≡⇒≡ (aux (cong proj₁ eq) , aux (cong proj₂ eq))
  where
  aux : ∀ {a b c : ℤ ₚ} → a + c ≡ b + c → a ≡ b
  aux {a} {b} {c} h = begin
    a             ≡⟨ sym (+-identityʳ a) ⟩
    a + ₀         ≡⟨ cong (a +_) (sym (+-inverseʳ c)) ⟩
    a + (c + - c) ≡⟨ sym (+-assoc a c (- c)) ⟩
    (a + c) + - c ≡⟨ cong (_+ - c) h ⟩
    (b + c) + - c ≡⟨ +-assoc b c (- c) ⟩
    b + (c + - c) ≡⟨ cong (b +_) (+-inverseʳ c) ⟩
    b + ₀         ≡⟨ +-identityʳ b ⟩
    b             ∎

private
  -- Negation is injective: -a ≡ -b → a ≡ b.
  neg-inj : ∀ (a b : ℤ ₚ) → - a ≡ - b → a ≡ b
  neg-inj a b h = begin
    a     ≡⟨ sym (-‿involutive a) ⟩
    - - a ≡⟨ cong -_ h ⟩
    - - b ≡⟨ -‿involutive b ⟩
    b     ∎

-- LM head-injectivity: if two LM coset representatives agree on every head output,
-- they are equal.  Proof by structural induction on n:
-- • n=0 (NF1), n=1 (Cosets2): sub-postulates.
-- • n=2+n' with inj₁/inj₂ tags: use lemma-ml-head-inj and lemma-lm-inj₁≁inj₂.
-- • inj₂/inj₂: recover d₁=d₂ from head at pZ∷pIₙ and pX∷pIₙ, then lm'
--   equality by IH using head at pZ-prefixed inputs after canceling d via +₁-cancelʳ.
lemma-lm-head-inj : ∀ {n} (lm₁ lm₂ : LM (₁₊ n)) →
  (∀ ps → head (act [ lm₁ ]ˡᵐ ps) ≡ head (act [ lm₂ ]ˡᵐ ps)) → lm₁ ≡ lm₂
lemma-lm-head-inj {₀} lm₁ lm₂ h = lemma-nf1-head-inj lm₁ lm₂ h
lemma-lm-head-inj {₁} lm₁ lm₂ h = lemma-cosets2-head-inj lm₁ lm₂ h
lemma-lm-head-inj {₁₊ (₁₊ n)} (inj₁ (m₁ , l₁)) (inj₁ (m₂ , l₂)) h =
  Eq.cong inj₁ (≡×≡⇒≡ (lemma-ml-head-inj m₁ m₂ l₁ l₂ h))
lemma-lm-head-inj {₁₊ (₁₊ n)} (inj₁ (m , l)) (inj₂ (d , lm')) h =
  ⊥-elim (lemma-lm-inj₁≁inj₂ m l d lm' h)
lemma-lm-head-inj {₁₊ (₁₊ n)} (inj₂ (d , lm')) (inj₁ (m , l)) h =
  ⊥-elim (lemma-lm-inj₁≁inj₂ m l d lm' (λ ps → sym (h ps)))
lemma-lm-head-inj {₁₊ (₁₊ n)} (inj₂ (d₁ , lm₁')) (inj₂ (d₂ , lm₂')) h =
  Eq.cong inj₂ (≡×≡⇒≡ (d-eq , lm'-eq))
  where
  -- act [inj₂(d,lm')]ˡᵐ (p ∷ ps') = act [d]ᵈ (p ∷ act [lm']ˡᵐ ps').
  unfold-act : ∀ d lm' p₀ (ps' : Pauli (₂₊ n)) →
    act [ inj₂ (d , lm') ]ˡᵐ (p₀ ∷ ps') ≡ act [ d ]ᵈ (p₀ ∷ act [ lm' ]ˡᵐ ps')
  unfold-act d lm' p₀ ps' = begin
    act [ inj₂ (d , lm') ]ˡᵐ (p₀ ∷ ps')
      ≡⟨ auto ⟩
    act [ d ]ᵈ (act ([ lm' ]ˡᵐ ↑) (p₀ ∷ ps'))
      ≡⟨ Eq.cong (act [ d ]ᵈ) (lemma-act-↑ [ lm' ]ˡᵐ p₀ ps') ⟩
    act [ d ]ᵈ (p₀ ∷ act [ lm' ]ˡᵐ ps') ∎

  -- Head agreement after canceling lm' by act [lm']ˡᵐ pIₙ = pIₙ.
  head-at-pI : ∀ p₀ → head (act [ d₁ ]ᵈ (p₀ ∷ pIₙ)) ≡ head (act [ d₂ ]ᵈ (p₀ ∷ pIₙ))
  head-at-pI p₀ = begin
    head (act [ d₁ ]ᵈ (p₀ ∷ pIₙ))
      ≡⟨ cong (λ v → head (act [ d₁ ]ᵈ (p₀ ∷ v))) (sym (lemma-actw-pIₙ [ lm₁' ]ˡᵐ)) ⟩
    head (act [ d₁ ]ᵈ (p₀ ∷ act [ lm₁' ]ˡᵐ pIₙ))
      ≡⟨ cong head (sym (unfold-act d₁ lm₁' p₀ pIₙ)) ⟩
    head (act [ inj₂ (d₁ , lm₁') ]ˡᵐ (p₀ ∷ pIₙ))
      ≡⟨ h (p₀ ∷ pIₙ) ⟩
    head (act [ inj₂ (d₂ , lm₂') ]ˡᵐ (p₀ ∷ pIₙ))
      ≡⟨ cong head (unfold-act d₂ lm₂' p₀ pIₙ) ⟩
    head (act [ d₂ ]ᵈ (p₀ ∷ act [ lm₂' ]ˡᵐ pIₙ))
      ≡⟨ cong (λ v → head (act [ d₂ ]ᵈ (p₀ ∷ v))) (lemma-actw-pIₙ [ lm₂' ]ˡᵐ) ⟩
    head (act [ d₂ ]ᵈ (p₀ ∷ pIₙ)) ∎

  -- d.proj₁ extracted via pZ-prefix: head(act [d]ᵈ (pZ ∷ pI ∷ t)) = (₀, d.proj₁).
  d-eq-fst : d₁ .proj₁ ≡ d₂ .proj₁
  d-eq-fst = cong proj₂
    (trans (sym (lemma-dbox-pZ-pI d₁ pIₙ))
    (trans (head-at-pI pZ)
           (lemma-dbox-pZ-pI d₂ pIₙ)))

  -- d.proj₂ extracted via pX-prefix: head(act [d]ᵈ (pX ∷ pI ∷ t)) = (₀, -d.proj₂).
  d-eq-snd : d₁ .proj₂ ≡ d₂ .proj₂
  d-eq-snd = neg-inj _ _
    (cong proj₂
      (trans (sym (lemma-dbox-pX-pI d₁ pIₙ))
      (trans (head-at-pI pX)
             (lemma-dbox-pX-pI d₂ pIₙ))))

  d-eq : d₁ ≡ d₂
  d-eq = ≡×≡⇒≡ (d-eq-fst , d-eq-snd)

  -- Head equality at arbitrary ps', using pZ-prefix and canceling d via d-eq.
  lm'-head-eq : ∀ ps' → head (act [ lm₁' ]ˡᵐ ps') ≡ head (act [ lm₂' ]ˡᵐ ps')
  lm'-head-eq ps' =
    let
      raw : head (act [ d₁ ]ᵈ (pZ ∷ act [ lm₁' ]ˡᵐ ps'))
           ≡ head (act [ d₂ ]ᵈ (pZ ∷ act [ lm₂' ]ˡᵐ ps'))
      raw = trans
        (cong head (sym (unfold-act d₁ lm₁' pZ ps')))
        (trans (h (pZ ∷ ps'))
               (cong head (unfold-act d₂ lm₂' pZ ps')))
      lhs : head (act [ d₁ ]ᵈ (pZ ∷ act [ lm₁' ]ˡᵐ ps'))
           ≡ head (act [ lm₁' ]ˡᵐ ps') +₁ (₀ , d₁ .proj₁)
      lhs = trans
        (cong (λ v → head (act [ d₁ ]ᵈ (pZ ∷ v))) (sym (lemma-aux-vec (₁₊ n) _)))
        (lemma-dbox-pZ-head d₁ _ _)
      rhs : head (act [ d₂ ]ᵈ (pZ ∷ act [ lm₂' ]ˡᵐ ps'))
           ≡ head (act [ lm₂' ]ˡᵐ ps') +₁ (₀ , d₂ .proj₁)
      rhs = trans
        (cong (λ v → head (act [ d₂ ]ᵈ (pZ ∷ v))) (sym (lemma-aux-vec (₁₊ n) _)))
        (lemma-dbox-pZ-head d₂ _ _)
      combined : head (act [ lm₁' ]ˡᵐ ps') +₁ (₀ , d₁ .proj₁)
                ≡ head (act [ lm₂' ]ˡᵐ ps') +₁ (₀ , d₂ .proj₁)
      combined = trans (sym lhs) (trans raw rhs)
      combined' : head (act [ lm₁' ]ˡᵐ ps') +₁ (₀ , d₁ .proj₁)
                 ≡ head (act [ lm₂' ]ˡᵐ ps') +₁ (₀ , d₁ .proj₁)
      combined' = subst
        (λ c → head (act [ lm₁' ]ˡᵐ ps') +₁ (₀ , d₁ .proj₁)
              ≡ head (act [ lm₂' ]ˡᵐ ps') +₁ (₀ , c))
        (sym d-eq-fst) combined
    in +₁-cancelʳ _ _ _ combined'

  lm'-eq : lm₁' ≡ lm₂'
  lm'-eq = lemma-lm-head-inj lm₁' lm₂' lm'-head-eq

-- Full-action injectivity follows from head-injectivity (head equality implies full equality).
lemma-lm-inj : ∀ {n} (lm₁ lm₂ : LM n) →
  act [ lm₁ ]ˡᵐ ≗ act [ lm₂ ]ˡᵐ → lm₁ ≡ lm₂
lemma-lm-inj {₀} tt tt _ = auto
lemma-lm-inj {₁₊ n} lm₁ lm₂ h = lemma-lm-head-inj lm₁ lm₂ (λ ps → Eq.cong head (h ps))

-- Surjectivity of tail ∘ act [lm]ˡᵐ: the preimage of (pI ∷ qs) under act [lm]ˡᵐ
-- is act ([lm]ˡᵐ ⁻¹ʷ) (pI ∷ qs), and its image under act [lm]ˡᵐ is pI ∷ qs
-- by the right-inverse law, so its tail equals qs.
lemma-lm-tail-surj : ∀ {n} (lm : LM (₁₊ n)) (qs : Pauli n) →
  ∃ λ ps → tail (act [ lm ]ˡᵐ ps) ≡ qs
lemma-lm-tail-surj {n} lm qs = ps , proof
  where
  open Group-Lemmas (Gen (₁₊ n)) ((₁₊ n) QRel,_===_) grouplike renaming (_⁻¹ to _⁻¹ʷ)
  open Group-Action (Pauli (₁₊ n)) (Gen (₁₊ n)) ((₁₊ n) QRel,_===_) grouplike act1
         (lemma-act-cong-ax {₁₊ n} _ _)

  ps = act ([ lm ]ˡᵐ ⁻¹ʷ) (pI ∷ qs)

  proof : tail (act [ lm ]ˡᵐ ps) ≡ qs
  proof = Eq.cong tail
    (act-cong ([ lm ]ˡᵐ • [ lm ]ˡᵐ ⁻¹ʷ) ε (pI ∷ qs) lemma-right-inverse)


-- Distinct NFs have distinct Pauli actions.
--
-- Proof (structural induction on n):
--   Base (n=0): NF 0 = ⊤, trivial.
--   Step (n = 1+n'): Given (ih₁,lm₁) and (ih₂,lm₂) with act-nf (ih₁,lm₁) = act-nf (ih₂,lm₂).
--   Write G_i = act [lm_i]ˡᵐ and M_i = act-nf ih_i.  The hypothesis expands to
--     head(G_i ps) ∷ M_i(tail(G_i ps)) equal for i=1,2 at every ps.
--
--   Step 1 – lm₁ = lm₂: head(act-nf (ih,lm) ps) = head(act [lm]ˡᵐ ps) by computation,
--   so Eq.cong head (hyp ps) gives head(G₁ ps) = head(G₂ ps) for all ps.
--   lemma-lm-head-inj then yields lm₁ = lm₂.
--
--   Step 2 – ih₁ = ih₂ via IH: substitute lm₁ = lm₂ into hyp to get
--   M₁(tail(G ps)) = M₂(tail(G ps)) for all ps (where G = act [lm₁]ˡᵐ).
--   By surjectivity of tail ∘ G (lemma-lm-tail-surj), this holds on all of Pauli n',
--   so the IH gives ih₁ = ih₂.
lemma-nf-inj : ∀ {n} (nf₁ nf₂ : NF n) → act-nf nf₁ ≗ act-nf nf₂ → nf₁ ≡ nf₂
lemma-nf-inj {₀} tt tt _ = auto
lemma-nf-inj {₁₊ n} (ih₁ , lm₁) (ih₂ , lm₂) hyp = ≡×≡⇒≡ (ih-eq , lm-eq)
  where
  open ≡-Reasoning

  head-eq : ∀ ps → head (act [ lm₁ ]ˡᵐ ps) ≡ head (act [ lm₂ ]ˡᵐ ps)
  head-eq ps = Eq.cong head (hyp ps)

  lm-eq : lm₁ ≡ lm₂
  lm-eq = lemma-lm-head-inj lm₁ lm₂ head-eq

  -- Substitute lm₁ = lm₂ into hyp: RHS uses lm₂, Eq.sym lm-eq rewrites it to lm₁,
  -- giving M₁(tail(G ps)) ≡ M₂(tail(G ps)) on the tail component.
  tail-agree : ∀ ps → act-nf ih₁ (tail (act [ lm₁ ]ˡᵐ ps))
                     ≡ act-nf ih₂ (tail (act [ lm₁ ]ˡᵐ ps))
  tail-agree ps = Eq.cong tail
    (subst (λ lm' → head (act [ lm₁ ]ˡᵐ ps) ∷ act-nf ih₁ (tail (act [ lm₁ ]ˡᵐ ps))
                   ≡ head (act [ lm' ]ˡᵐ ps) ∷ act-nf ih₂ (tail (act [ lm' ]ˡᵐ ps)))
      (Eq.sym lm-eq) (hyp ps))

  ih-act-eq : act-nf ih₁ ≗ act-nf ih₂
  ih-act-eq qs =
    let (ps , eq) = lemma-lm-tail-surj lm₁ qs in begin
      act-nf ih₁ qs                           ≡⟨ Eq.cong (act-nf ih₁) (Eq.sym eq) ⟩
      act-nf ih₁ (tail (act [ lm₁ ]ˡᵐ ps))   ≡⟨ tail-agree ps ⟩
      act-nf ih₂ (tail (act [ lm₁ ]ˡᵐ ps))   ≡⟨ Eq.cong (act-nf ih₂) eq ⟩
      act-nf ih₂ qs                           ∎

  ih-eq : ih₁ ≡ ih₂
  ih-eq = lemma-nf-inj ih₁ ih₂ ih-act-eq

