-- {-# OPTIONS  --safe #-}  -- re-enable when all postulates are proved
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



module N.NF4 (p-2 : ℕ) (p-prime : Prime (2+ p-2))  where

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
open Symplectic-Derived-GroupLike
open import N.NF1 p-2 p-prime
open import N.LM p-2 p-prime
open import N.LM-Lemmas p-2 p-prime
open import N.LM-Lemmas2 p-2 p-prime
open Normal-Form1
open import N.NF p-2 p-prime

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


-- Helpers for NF1 and future head-injectivity lemmas.
private
  -- ZMultiplier equality from proj₁ equality.
  ZM-≡ : ∀ (m₁ m₂ : ZMultiplier) → m₁ .proj₁ ≡ m₂ .proj₁ → m₁ ≡ m₂
  ZM-≡ (a , nza) (b , nzb) eq =
    HE.≅-to-≡ (HE.cong₂ _,_ (HE.reflexive eq)
      (HE.≡-subst-removable (λ x → x ≢ ₀) (sym eq) nzb))
    where import Relation.Binary.HeterogeneousEquality as HE

  -- Negation is injective: -a ≡ -b → a ≡ b.
  neg-inj : ∀ (a b : ℤ ₚ) → - a ≡ - b → a ≡ b
  neg-inj a b eq = begin
    a     ≡⟨ sym (-‿involutive a) ⟩
    - - a ≡⟨ cong -_ eq ⟩
    - - b ≡⟨ -‿involutive b ⟩
    b     ∎

  -- Negation preserves nonzero: a ≢ 0 → -a ≢ 0.
  neg-nz : ∀ (a : ℤ ₚ) → a ≢ ₀ → - a ≢ ₀
  neg-nz a nza eq = nza (trans (sym (-‿involutive a)) (trans (cong -_ eq) -0#≈0#))

  -- Left cancellation: a ≢ 0 → a*b ≡ a*c → b ≡ c.
  *-cancelˡ : ∀ (a b c : ℤ ₚ) → a ≢ ₀ → a * b ≡ a * c → b ≡ c
  *-cancelˡ a b c nza eq =
    let a⁻¹ = _⁻¹' a {{nztoℕ {y = a} {neq0 = nza}}} in
    begin
    b               ≡⟨ sym (*-identityˡ b) ⟩
    ₁ * b           ≡⟨ cong (_* b) (sym (lemma-⁻¹ˡ a {{nztoℕ {y = a} {neq0 = nza}}})) ⟩
    (a⁻¹ * a) * b   ≡⟨ *-assoc a⁻¹ a b ⟩
    a⁻¹ * (a * b)   ≡⟨ cong (a⁻¹ *_) eq ⟩
    a⁻¹ * (a * c)   ≡⟨ sym (*-assoc a⁻¹ a c) ⟩
    (a⁻¹ * a) * c   ≡⟨ cong (_* c) (lemma-⁻¹ˡ a {{nztoℕ {y = a} {neq0 = nza}}}) ⟩
    ₁ * c           ≡⟨ *-identityˡ c ⟩
    c ∎

  -- Right cancellation: c ≢ 0 → a*c ≡ b*c → a ≡ b.
  *-cancelʳ : ∀ (a b c : ℤ ₚ) → c ≢ ₀ → a * c ≡ b * c → a ≡ b
  *-cancelʳ a b c nzc eq = *-cancelˡ c a b nzc
    (trans (*-comm c a) (trans eq (*-comm b c)))

  -- Inverse injectivity on proj₁: (m₁⁻¹).proj₁ ≡ (m₂⁻¹).proj₁ → m₁.proj₁ ≡ m₂.proj₁.
  inv-inj-proj₁ : ∀ (m₁ m₂ : ZMultiplier) → (m₁ ⁻¹) .proj₁ ≡ (m₂ ⁻¹) .proj₁ → m₁ .proj₁ ≡ m₂ .proj₁
  inv-inj-proj₁ m₁ m₂ eq =
    trans (sym (inv-involutive m₁)) (trans (inv-cong (m₁ ⁻¹) (m₂ ⁻¹) eq) (inv-involutive m₂))

  -- Head of ⟦(s,m,ε)⟧₁ at pZ=(₀,₁) is (₀, m.proj₁).
  nf1ε-pZ : ∀ s (m : ZMultiplier) →
    head (act [ (s , m , ε) ]ˡᵐ (pZ ∷ [])) ≡ (₀ , m .proj₁)
  nf1ε-pZ s m =
    let x = m .proj₁ ; x⁻¹ = (m ⁻¹) .proj₁ in begin
    head (act [ (s , m , ε) ]ˡᵐ (pZ ∷ []))
      ≡⟨ cong (λ v → head (act (S^ s) v)) (lemma-M ₀ ₁ [] m) ⟩
    head (act (S^ s) ((₀ * x⁻¹ , ₁ * x) ∷ []))
      ≡⟨ cong₂ (λ a b → head (act (S^ s) ((a , b) ∷ []))) (*-zeroˡ x⁻¹) (*-identityˡ x) ⟩
    head (act (S^ s) ((₀ , x) ∷ []))
      ≡⟨ auto ⟩
    (₀ , x + ₀ * s)
      ≡⟨ cong (₀ ,_) (trans (cong (x +_) (*-zeroˡ s)) (+-identityʳ x)) ⟩
    (₀ , x) ∎

  -- Head of ⟦(s,m,ε)⟧₁ at pX=(₁,₀) is ((m⁻¹).proj₁, (m⁻¹).proj₁ * s).
  nf1ε-pX : ∀ s (m : ZMultiplier) →
    head (act [ (s , m , ε) ]ˡᵐ (pX ∷ [])) ≡ ((m ⁻¹) .proj₁ , (m ⁻¹) .proj₁ * s)
  nf1ε-pX s m =
    let x = m .proj₁ ; x⁻¹ = (m ⁻¹) .proj₁ in begin
    head (act [ (s , m , ε) ]ˡᵐ (pX ∷ []))
      ≡⟨ cong (λ v → head (act (S^ s) v)) (lemma-M ₁ ₀ [] m) ⟩
    head (act (S^ s) ((₁ * x⁻¹ , ₀ * x) ∷ []))
      ≡⟨ cong₂ (λ a b → head (act (S^ s) ((a , b) ∷ []))) (*-identityˡ x⁻¹) (*-zeroˡ x) ⟩
    head (act (S^ s) ((x⁻¹ , ₀) ∷ []))
      ≡⟨ auto ⟩
    (x⁻¹ , ₀ + x⁻¹ * s)
      ≡⟨ cong (x⁻¹ ,_) (+-identityˡ (x⁻¹ * s)) ⟩
    (x⁻¹ , x⁻¹ * s) ∎

  -- Head of ⟦(s,m,HS^k)⟧₁ at pZ=(₀,₁) is (-(m⁻¹).proj₁, -(m⁻¹).proj₁ * s).
  nf1HS-pZ : ∀ s k (m : ZMultiplier) →
    head (act [ (s , m , HS^ k) ]ˡᵐ (pZ ∷ [])) ≡ (- (m ⁻¹) .proj₁ , - (m ⁻¹) .proj₁ * s)
  nf1HS-pZ s k m =
    let x = m .proj₁ ; x⁻¹ = (m ⁻¹) .proj₁ in begin
    head (act [ (s , m , HS^ k) ]ˡᵐ (pZ ∷ []))
      ≡⟨ cong (λ v → head (act (S^ s • ⟦ m ⟧ₘ) v)) (lemma-HS-x k ₀ ₁ []) ⟩
    head (act (S^ s • ⟦ m ⟧ₘ) ((- (₁ + ₀ * k) , ₀) ∷ []))
      ≡⟨ cong (λ a → head (act (S^ s • ⟦ m ⟧ₘ) ((- a , ₀) ∷ [])))
              (trans (cong (₁ +_) (*-zeroˡ k)) (+-identityʳ ₁)) ⟩
    head (act (S^ s • ⟦ m ⟧ₘ) ((- ₁ , ₀) ∷ []))
      ≡⟨ cong (λ v → head (act (S^ s) v)) (lemma-M (- ₁) ₀ [] m) ⟩
    head (act (S^ s) ((- ₁ * x⁻¹ , ₀ * x) ∷ []))
      ≡⟨ cong₂ (λ a b → head (act (S^ s) ((a , b) ∷ []))) (-1*x≈-x x⁻¹) (*-zeroˡ x) ⟩
    head (act (S^ s) ((- x⁻¹ , ₀) ∷ []))
      ≡⟨ auto ⟩
    (- x⁻¹ , ₀ + - x⁻¹ * s)
      ≡⟨ cong (- x⁻¹ ,_) (+-identityˡ (- x⁻¹ * s)) ⟩
    (- x⁻¹ , - x⁻¹ * s) ∎

  -- Head of ⟦(s,m,HS^k)⟧₁ at pX=(₁,₀) is (-k*(m⁻¹).proj₁, m.proj₁ + -k*(m⁻¹).proj₁*s).
  nf1HS-pX : ∀ s k (m : ZMultiplier) →
    head (act [ (s , m , HS^ k) ]ˡᵐ (pX ∷ [])) ≡
      (- k * (m ⁻¹) .proj₁ , m .proj₁ + - k * (m ⁻¹) .proj₁ * s)
  nf1HS-pX s k m =
    let x = m .proj₁ ; x⁻¹ = (m ⁻¹) .proj₁ in begin
    head (act [ (s , m , HS^ k) ]ˡᵐ (pX ∷ []))
      ≡⟨ cong (λ v → head (act (S^ s • ⟦ m ⟧ₘ) v)) (lemma-HS-x k ₁ ₀ []) ⟩
    head (act (S^ s • ⟦ m ⟧ₘ) ((- (₀ + ₁ * k) , ₁) ∷ []))
      ≡⟨ cong (λ a → head (act (S^ s • ⟦ m ⟧ₘ) ((- a , ₁) ∷ [])))
              (trans (cong (₀ +_) (*-identityˡ k)) (+-identityˡ k)) ⟩
    head (act (S^ s • ⟦ m ⟧ₘ) ((- k , ₁) ∷ []))
      ≡⟨ cong (λ v → head (act (S^ s) v)) (lemma-M (- k) ₁ [] m) ⟩
    head (act (S^ s) ((- k * x⁻¹ , ₁ * x) ∷ []))
      ≡⟨ cong (λ b → head (act (S^ s) ((- k * x⁻¹ , b) ∷ []))) (*-identityˡ x) ⟩
    head (act (S^ s) ((- k * x⁻¹ , x) ∷ []))
      ≡⟨ auto ⟩
    (- k * x⁻¹ , x + - k * x⁻¹ * s) ∎

abstract
  -- n=1: NF1 elements are distinguished by head of Pauli action.
  lemma-nf1-head-inj : ∀ (lm₁ lm₂ : NF1) →
    (∀ ps → head (act [ lm₁ ]ˡᵐ ps) ≡ head (act [ lm₂ ]ˡᵐ ps)) → lm₁ ≡ lm₂
  -- Case (ε,ε): pZ gives m₁=m₂ (via proj₂); pX gives s₁=s₂ (via *-cancelˡ).
  lemma-nf1-head-inj (s₁ , m₁ , ε) (s₂ , m₂ , ε) h =
    let
      x₁⁻¹ = (m₁ ⁻¹) .proj₁ ; x₂⁻¹ = (m₂ ⁻¹) .proj₁
      pZ-eq = trans (sym (nf1ε-pZ s₁ m₁)) (trans (h (pZ ∷ [])) (nf1ε-pZ s₂ m₂))
      pX-eq = trans (sym (nf1ε-pX s₁ m₁)) (trans (h (pX ∷ [])) (nf1ε-pX s₂ m₂))
      x₁=x₂ : m₁ .proj₁ ≡ m₂ .proj₁
      x₁=x₂ = cong proj₂ pZ-eq
      m₁=m₂ = ZM-≡ m₁ m₂ x₁=x₂
      xinv-eq : x₁⁻¹ ≡ x₂⁻¹
      xinv-eq = inv-cong m₁ m₂ x₁=x₂
      eq-snd : x₁⁻¹ * s₁ ≡ x₁⁻¹ * s₂
      eq-snd = trans (cong proj₂ pX-eq) (cong (_* s₂) (sym xinv-eq))
      s₁=s₂ = *-cancelˡ x₁⁻¹ s₁ s₂ ((m₁ ⁻¹) .proj₂) eq-snd
    in cong₂ _,_ s₁=s₂ (cong₂ _,_ m₁=m₂ refl)
  -- Cross case (ε, HS^k₂): proj₁ at pZ gives ₀ = -(m₂⁻¹).proj₁, contradicting nz.
  lemma-nf1-head-inj (s₁ , m₁ , ε) (s₂ , m₂ , HS^ k₂) h =
    ⊥-elim (neg-nz ((m₂ ⁻¹) .proj₁) ((m₂ ⁻¹) .proj₂)
      (sym (cong proj₁
        (trans (sym (nf1ε-pZ s₁ m₁)) (trans (h (pZ ∷ [])) (nf1HS-pZ s₂ k₂ m₂))))))
  -- Cross case (HS^k₁, ε): symmetric contradiction.
  lemma-nf1-head-inj (s₁ , m₁ , HS^ k₁) (s₂ , m₂ , ε) h =
    ⊥-elim (neg-nz ((m₁ ⁻¹) .proj₁) ((m₁ ⁻¹) .proj₂)
      (cong proj₁
        (trans (sym (nf1HS-pZ s₁ k₁ m₁)) (trans (h (pZ ∷ [])) (nf1ε-pZ s₂ m₂)))))
  -- Case (HS^k₁, HS^k₂): pZ gives m₁=m₂,s₁=s₂; pX gives k₁=k₂.
  lemma-nf1-head-inj (s₁ , m₁ , HS^ k₁) (s₂ , m₂ , HS^ k₂) h =
    let
      x₁⁻¹ = (m₁ ⁻¹) .proj₁ ; x₂⁻¹ = (m₂ ⁻¹) .proj₁
      pZ-eq = trans (sym (nf1HS-pZ s₁ k₁ m₁)) (trans (h (pZ ∷ [])) (nf1HS-pZ s₂ k₂ m₂))
      pX-eq = trans (sym (nf1HS-pX s₁ k₁ m₁)) (trans (h (pX ∷ [])) (nf1HS-pX s₂ k₂ m₂))
      xinv-eq : x₁⁻¹ ≡ x₂⁻¹
      xinv-eq = neg-inj x₁⁻¹ x₂⁻¹ (cong proj₁ pZ-eq)
      x₁=x₂ = inv-inj-proj₁ m₁ m₂ xinv-eq
      m₁=m₂ = ZM-≡ m₁ m₂ x₁=x₂
      eq-snd : - x₁⁻¹ * s₁ ≡ - x₁⁻¹ * s₂
      eq-snd = trans (cong proj₂ pZ-eq) (cong (λ v → - v * s₂) (sym xinv-eq))
      s₁=s₂ = *-cancelˡ (- x₁⁻¹) s₁ s₂ (neg-nz x₁⁻¹ ((m₁ ⁻¹) .proj₂)) eq-snd
      eq-fst : - k₁ * x₁⁻¹ ≡ - k₂ * x₁⁻¹
      eq-fst = trans (cong proj₁ pX-eq) (cong (λ v → - k₂ * v) (sym xinv-eq))
      neg-k₁=neg-k₂ = *-cancelʳ (- k₁) (- k₂) x₁⁻¹ ((m₁ ⁻¹) .proj₂) eq-fst
      k₁=k₂ = neg-inj k₁ k₂ neg-k₁=neg-k₂
    in cong₂ _,_ s₁=s₂ (cong₂ _,_ m₁=m₂ (cong HS^ k₁=k₂))

-- Sub-postulate still to be proved.
postulate
  -- n=2: Cosets2 elements are distinguished by head of Pauli action.
  lemma-cosets2-head-inj : ∀ (lm₁ lm₂ : Cosets2) →
    (∀ ps → head (act [ lm₁ ]ˡᵐ ps) ≡ head (act [ lm₂ ]ˡᵐ ps)) → lm₁ ≡ lm₂

-- Private helpers for lemma-ml-head-inj.
private
  -- sform1 p pZ = - p.proj₁.
  sform1-left-pZ : ∀ (p : Pauli1) → sform1 p pZ ≡ - p .proj₁
  sform1-left-pZ (a , b) = begin
    sform1 (a , b) pZ    ≡⟨ auto ⟩
    (- a) * ₁ + ₀ * b   ≡⟨ cong₂ _+_ (*-identityʳ (- a)) (*-zeroˡ b) ⟩
    (- a) + ₀            ≡⟨ +-identityʳ (- a) ⟩
    - a ∎
    where open ≡-Reasoning

  -- sform1 p pX = p.proj₂.
  sform1-left-pX : ∀ (p : Pauli1) → sform1 p pX ≡ p .proj₂
  sform1-left-pX (a , b) = begin
    sform1 (a , b) pX    ≡⟨ auto ⟩
    (- a) * ₀ + ₁ * b   ≡⟨ cong₂ _+_ (*-zeroʳ (- a)) (*-identityˡ b) ⟩
    ₀ + b                ≡⟨ +-identityˡ b ⟩
    b ∎
    where open ≡-Reasoning

  -- sform1 pX p = - p.proj₂  (pX as first arg).
  sform1-pX : ∀ (p : Pauli1) → sform1 pX p ≡ - p .proj₂
  sform1-pX (c , d) = begin
    sform1 pX (c , d)    ≡⟨ auto ⟩
    (- ₁) * d + c * ₀   ≡⟨ cong₂ _+_ (-1*x≈-x d) (*-zeroʳ c) ⟩
    (- d) + ₀            ≡⟨ +-identityʳ (- d) ⟩
    - d ∎
    where open ≡-Reasoning

  -- sform pX₀ v = - (head v).proj₂.
  sform-pX0 : ∀ {n} (v : Pauli (₁₊ n)) → sform pX₀ v ≡ - (head v) .proj₂
  sform-pX0 ((c , d) ∷ vs) = begin
    sform pX₀ ((c , d) ∷ vs)          ≡⟨ auto ⟩
    sform1 pX (c , d) + sform pIₙ vs  ≡⟨ cong₂ _+_ (sform1-pX (c , d)) (lemma-sform-pIₙ-q=0 vs) ⟩
    (- d) + ₀                          ≡⟨ +-identityʳ (- d) ⟩
    - d ∎
    where open ≡-Reasoning

  -- sform v pIₙ = 0  (pIₙ as second argument).
  sform-q-pIₙ=0 : ∀ {n} (v : Pauli n) → sform v pIₙ ≡ ₀
  sform-q-pIₙ=0 [] = auto
  sform-q-pIₙ=0 (x ∷ vs) = begin
    sform1 x pI + sform vs pIₙ  ≡⟨ cong₂ _+_ (lemma-sform1-pIʳ x) (sform-q-pIₙ=0 vs) ⟩
    ₀ + ₀                        ≡⟨ auto ⟩
    ₀ ∎
    where open ≡-Reasoning

  -- sform is injective in its first argument.
  sform-inj : ∀ {n} (v w : Pauli n) → (∀ u → sform v u ≡ sform w u) → v ≡ w
  sform-inj {₀} [] [] h = auto
  sform-inj {₁₊ n} ((a , b) ∷ vs) ((c , d) ∷ ws) h = cong₂ _∷_ head-eq vs-eq
    where
    open ≡-Reasoning
    a=c : a ≡ c
    a=c = neg-inj a c (begin
      - a
        ≡⟨ sym (trans (cong₂ _+_ (sform1-left-pZ (a , b)) (sform-q-pIₙ=0 vs)) (+-identityʳ (- a))) ⟩
      sform ((a , b) ∷ vs) pZ₀
        ≡⟨ h pZ₀ ⟩
      sform ((c , d) ∷ ws) pZ₀
        ≡⟨ trans (cong₂ _+_ (sform1-left-pZ (c , d)) (sform-q-pIₙ=0 ws)) (+-identityʳ (- c)) ⟩
      - c ∎)
    b=d : b ≡ d
    b=d = begin
      b
        ≡⟨ sym (trans (cong₂ _+_ (sform1-left-pX (a , b)) (sform-q-pIₙ=0 vs)) (+-identityʳ b)) ⟩
      sform ((a , b) ∷ vs) pX₀
        ≡⟨ h pX₀ ⟩
      sform ((c , d) ∷ ws) pX₀
        ≡⟨ trans (cong₂ _+_ (sform1-left-pX (c , d)) (sform-q-pIₙ=0 ws)) (+-identityʳ d) ⟩
      d ∎
    head-eq : (a , b) ≡ (c , d)
    head-eq = ≡×≡⇒≡ (a=c , b=d)
    h-tail : ∀ u' → sform vs u' ≡ sform ws u'
    h-tail u' = begin
      sform vs u'
        ≡⟨ sym (trans (cong₂ _+_ (lemma-sform1-pIʳ (a , b)) refl) (+-identityˡ (sform vs u'))) ⟩
      sform ((a , b) ∷ vs) (pI ∷ u')
        ≡⟨ h (pI ∷ u') ⟩
      sform ((c , d) ∷ ws) (pI ∷ u')
        ≡⟨ trans (cong₂ _+_ (lemma-sform1-pIʳ (c , d)) refl) (+-identityˡ (sform ws u')) ⟩
      sform ws u' ∎
    vs-eq : vs ≡ ws
    vs-eq = sform-inj vs ws h-tail

  -- A-≡: A elements with equal first component are equal.
  A-≡ : ∀ (a₁ a₂ : A) → a₁ .proj₁ ≡ a₂ .proj₁ → a₁ ≡ a₂
  A-≡ (p1 , nz1) (p2 , nz2) eq =
    HE.≅-to-≡ (HE.cong₂ _,_ (HE.reflexive eq)
      (HE.≡-subst-removable (λ ab → ab ≢ (₀ , ₀)) (sym eq) nz2))
    where import Relation.Binary.HeterogeneousEquality as HE

  -- last (v ∷ʳ x) = x.
  last-snoc : ∀ {A : Set} {n} (v : Vec A n) (x : A) → last (v ∷ʳ x) ≡ x
  last-snoc [] x = auto
  last-snoc (y ∷ v) x = last-snoc v x

  -- init (v ∷ʳ x) = v.
  init-snoc : ∀ {A : Set} {n} (v : Vec A n) (x : A) → init (v ∷ʳ x) ≡ v
  init-snoc [] x = auto
  init-snoc (y ∷ v) x = cong (y ∷_) (init-snoc v x)

  -- act [m]ᵐ (m.proj₂ ∷ʳ pXZ m.proj₁) = pX₀.
  claim2-M : ∀ {n} (m : M (₃₊ n)) → act [ m ]ᵐ (m .proj₂ ∷ʳ pXZ (m .proj₁)) ≡ pX₀
  claim2-M {n} (e , vd) = begin
    act [ (e , vd) ]ᵐ (vd ∷ʳ pXZ e)           ≡⟨ auto ⟩
    act [ e ]ᵉ (act [ vd ]ᵛᵈ (vd ∷ʳ pXZ e))  ≡⟨ cong (act [ e ]ᵉ) (lemma-dboxes-XZ e vd) ⟩
    act [ e ]ᵉ (pX₀Z₀ e)                       ≡⟨ lemma-ebox-XZ e ⟩
    pX₀ ∎
    where open ≡-Reasoning


  -- Helper: sform1 pZ p = p.proj₁.
  lemma-sform1-pZ : ∀ (p : Pauli1) → sform1 pZ p ≡ p .proj₁
  lemma-sform1-pZ (c , d) = begin
    sform1 pZ (c , d)         ≡⟨ auto ⟩
    (- ₀) * d + c * ₁         ≡⟨ cong₂ _+_ (cong (_* d) -0#≈0#) (*-identityʳ c) ⟩
    ₀ * d + c                  ≡⟨ cong (_+ c) (*-zeroˡ d) ⟩
    ₀ + c                      ≡⟨ +-identityˡ c ⟩
    c ∎
    where open ≡-Reasoning

  -- Helper: sform pZ₀ v = (head v).proj₁.
  lemma-sform-pZ0 : ∀ {n} (v : Pauli (₁₊ n)) → sform pZ₀ v ≡ (head v) .proj₁
  lemma-sform-pZ0 ((c , d) ∷ vs) = begin
    sform pZ₀ ((c , d) ∷ vs)          ≡⟨ auto ⟩
    sform1 pZ (c , d) + sform pIₙ vs  ≡⟨ cong₂ _+_ (lemma-sform1-pZ (c , d)) (lemma-sform-pIₙ-q=0 vs) ⟩
    c + ₀                              ≡⟨ +-identityʳ c ⟩
    c ∎
    where open ≡-Reasoning

-- M×L' action is head-injective.
lemma-ml-head-inj : ∀ {n} (m₁ m₂ : M (₃₊ n)) (l₁ l₂ : L' (₃₊ n)) →
  (∀ ps → head (act ([ m₁ ]ᵐ • [ l₁ ]ˡ') ps) ≡ head (act ([ m₂ ]ᵐ • [ l₂ ]ˡ') ps)) →
  m₁ ≡ m₂ × l₁ ≡ l₂
lemma-ml-head-inj {n} m₁ m₂ l₁ l₂ h = m-eq , l-eq
  where
  open ≡-Reasoning
  open Group-Lemmas (Gen (₃₊ n)) ((₃₊ n) QRel,_===_) grouplike renaming (_⁻¹ to _⁻¹ʷ)
  open Group-Action (Pauli (₃₊ n)) (Gen (₃₊ n)) ((₃₊ n) QRel,_===_) grouplike act1
       (lemma-act-cong-ax {₃₊ n} _ _)
  vb₁ = l₁ .proj₁ ; a₁ = l₁ .proj₂ ; p1₁ = a₁ .proj₁ ; nz₁ = a₁ .proj₂
  vb₂ = l₂ .proj₁ ; a₂ = l₂ .proj₂ ; p1₂ = a₂ .proj₁ ; nz₂ = a₂ .proj₂
  e₁ = m₁ .proj₁ ; vd₁ = m₁ .proj₂
  e₂ = m₂ .proj₁ ; vd₂ = m₂ .proj₂
  act-ml₁ : act ([ m₁ ]ᵐ • [ l₁ ]ˡ') (p1₁ ∷ vb₁) ≡ pZ₀
  act-ml₁ = begin
    act ([ m₁ ]ᵐ • [ l₁ ]ˡ') (p1₁ ∷ vb₁)
      ≡⟨ auto ⟩
    act ([ m₁ ]ᵐ • [ vb₁ ]ᵛᵇ • [ (p1₁ , nz₁) ]ᵃ) (p1₁ ∷ vb₁)
      ≡⟨ Eq.cong (act ([ m₁ ]ᵐ • [ vb₁ ]ᵛᵇ)) (lemma-abox p1₁ nz₁ vb₁) ⟩
    act ([ m₁ ]ᵐ • [ vb₁ ]ᵛᵇ) (pZ ∷ vb₁)
      ≡⟨ Eq.cong (act ([ m₁ ]ᵐ)) (lemma-bboxes vb₁) ⟩
    act ([ m₁ ]ᵐ) pZₙ
      ≡⟨ auto ⟩
    act ([ e₁ ]ᵉ • [ vd₁ ]ᵛᵈ) pZₙ
      ≡⟨ Eq.cong (act ([ e₁ ]ᵉ • [ vd₁ ]ᵛᵈ)) lemma-pZₙ-pIₙ∷ʳpZ ⟩
    act ([ e₁ ]ᵉ • [ vd₁ ]ᵛᵈ) (pIₙ ∷ʳ pZ)
      ≡⟨ Eq.cong (act ([ e₁ ]ᵉ)) (lemma-dboxes-Z vd₁) ⟩
    pZ₀ ∎
  act-ml₂ : act ([ m₂ ]ᵐ • [ l₂ ]ˡ') (p1₂ ∷ vb₂) ≡ pZ₀
  act-ml₂ = begin
    act ([ m₂ ]ᵐ • [ l₂ ]ˡ') (p1₂ ∷ vb₂)
      ≡⟨ auto ⟩
    act ([ m₂ ]ᵐ • [ vb₂ ]ᵛᵇ • [ (p1₂ , nz₂) ]ᵃ) (p1₂ ∷ vb₂)
      ≡⟨ Eq.cong (act ([ m₂ ]ᵐ • [ vb₂ ]ᵛᵇ)) (lemma-abox p1₂ nz₂ vb₂) ⟩
    act ([ m₂ ]ᵐ • [ vb₂ ]ᵛᵇ) (pZ ∷ vb₂)
      ≡⟨ Eq.cong (act ([ m₂ ]ᵐ)) (lemma-bboxes vb₂) ⟩
    act ([ m₂ ]ᵐ) pZₙ
      ≡⟨ auto ⟩
    act ([ e₂ ]ᵉ • [ vd₂ ]ᵛᵈ) pZₙ
      ≡⟨ Eq.cong (act ([ e₂ ]ᵉ • [ vd₂ ]ᵛᵈ)) lemma-pZₙ-pIₙ∷ʳpZ ⟩
    act ([ e₂ ]ᵉ • [ vd₂ ]ᵛᵈ) (pIₙ ∷ʳ pZ)
      ≡⟨ Eq.cong (act ([ e₂ ]ᵉ)) (lemma-dboxes-Z vd₂) ⟩
    pZ₀ ∎
  sform-eq : ∀ q → sform (p1₁ ∷ vb₁) q ≡ sform (p1₂ ∷ vb₂) q
  sform-eq q = begin
    sform (p1₁ ∷ vb₁) q
      ≡⟨ sym (sform-preserving ([ m₁ ]ᵐ • [ l₁ ]ˡ') (p1₁ ∷ vb₁) q) ⟩
    sform (act ([ m₁ ]ᵐ • [ l₁ ]ˡ') (p1₁ ∷ vb₁)) (act ([ m₁ ]ᵐ • [ l₁ ]ˡ') q)
      ≡⟨ cong (λ v → sform v (act ([ m₁ ]ᵐ • [ l₁ ]ˡ') q)) act-ml₁ ⟩
    sform pZ₀ (act ([ m₁ ]ᵐ • [ l₁ ]ˡ') q)
      ≡⟨ lemma-sform-pZ0 (act ([ m₁ ]ᵐ • [ l₁ ]ˡ') q) ⟩
    head (act ([ m₁ ]ᵐ • [ l₁ ]ˡ') q) .proj₁
      ≡⟨ cong proj₁ (h q) ⟩
    head (act ([ m₂ ]ᵐ • [ l₂ ]ˡ') q) .proj₁
      ≡⟨ sym (lemma-sform-pZ0 (act ([ m₂ ]ᵐ • [ l₂ ]ˡ') q)) ⟩
    sform pZ₀ (act ([ m₂ ]ᵐ • [ l₂ ]ˡ') q)
      ≡⟨ cong (λ v → sform v (act ([ m₂ ]ᵐ • [ l₂ ]ˡ') q)) (sym act-ml₂) ⟩
    sform (act ([ m₂ ]ᵐ • [ l₂ ]ˡ') (p1₂ ∷ vb₂)) (act ([ m₂ ]ᵐ • [ l₂ ]ˡ') q)
      ≡⟨ sform-preserving ([ m₂ ]ᵐ • [ l₂ ]ˡ') (p1₂ ∷ vb₂) q ⟩
    sform (p1₂ ∷ vb₂) q ∎
  vec-eq : p1₁ ∷ vb₁ ≡ p1₂ ∷ vb₂
  vec-eq = sform-inj _ _ sform-eq
  p1-eq : p1₁ ≡ p1₂
  p1-eq = cong head vec-eq
  vb-eq : vb₁ ≡ vb₂
  vb-eq = cong tail vec-eq
  l-eq : l₁ ≡ l₂
  l-eq = ≡×≡⇒≡ (vb-eq , A-≡ a₁ a₂ p1-eq)
  q₀₁ = act ([ l₁ ]ˡ' ⁻¹ʷ) (vd₁ ∷ʳ pXZ e₁)
  q₀₂ = act ([ l₁ ]ˡ' ⁻¹ʷ) (vd₂ ∷ʳ pXZ e₂)
  l-q₀₁ : act [ l₁ ]ˡ' q₀₁ ≡ vd₁ ∷ʳ pXZ e₁
  l-q₀₁ = begin
    act [ l₁ ]ˡ' q₀₁
      ≡⟨ auto ⟩
    act ([ l₁ ]ˡ' • [ l₁ ]ˡ' ⁻¹ʷ) (vd₁ ∷ʳ pXZ e₁)
      ≡⟨ act-cong ([ l₁ ]ˡ' • [ l₁ ]ˡ' ⁻¹ʷ) ε _ lemma-right-inverse ⟩
    act ε (vd₁ ∷ʳ pXZ e₁)
      ≡⟨ auto ⟩
    vd₁ ∷ʳ pXZ e₁ ∎
  l-q₀₂ : act [ l₁ ]ˡ' q₀₂ ≡ vd₂ ∷ʳ pXZ e₂
  l-q₀₂ = begin
    act [ l₁ ]ˡ' q₀₂
      ≡⟨ auto ⟩
    act ([ l₁ ]ˡ' • [ l₁ ]ˡ' ⁻¹ʷ) (vd₂ ∷ʳ pXZ e₂)
      ≡⟨ act-cong ([ l₁ ]ˡ' • [ l₁ ]ˡ' ⁻¹ʷ) ε _ lemma-right-inverse ⟩
    act ε (vd₂ ∷ʳ pXZ e₂)
      ≡⟨ auto ⟩
    vd₂ ∷ʳ pXZ e₂ ∎
  g₁-q₀₁ : act ([ m₁ ]ᵐ • [ l₁ ]ˡ') q₀₁ ≡ pX₀
  g₁-q₀₁ = begin
    act ([ m₁ ]ᵐ • [ l₁ ]ˡ') q₀₁
      ≡⟨ auto ⟩
    act [ m₁ ]ᵐ (act [ l₁ ]ˡ' q₀₁)
      ≡⟨ cong (act [ m₁ ]ᵐ) l-q₀₁ ⟩
    act [ m₁ ]ᵐ (vd₁ ∷ʳ pXZ e₁)
      ≡⟨ claim2-M m₁ ⟩
    pX₀ ∎
  g₂-q₀₂ : act ([ m₂ ]ᵐ • [ l₁ ]ˡ') q₀₂ ≡ pX₀
  g₂-q₀₂ = begin
    act ([ m₂ ]ᵐ • [ l₁ ]ˡ') q₀₂
      ≡⟨ auto ⟩
    act [ m₂ ]ᵐ (act [ l₁ ]ˡ' q₀₂)
      ≡⟨ cong (act [ m₂ ]ᵐ) l-q₀₂ ⟩
    act [ m₂ ]ᵐ (vd₂ ∷ʳ pXZ e₂)
      ≡⟨ claim2-M m₂ ⟩
    pX₀ ∎
  h' : ∀ ps → head (act ([ m₁ ]ᵐ • [ l₁ ]ˡ') ps) ≡ head (act ([ m₂ ]ᵐ • [ l₁ ]ˡ') ps)
  h' ps = trans (h ps) (Eq.cong (λ l' → head (act ([ m₂ ]ᵐ • [ l' ]ˡ') ps)) (Eq.sym l-eq))
  sform2₁ : ∀ ps → (head (act ([ m₁ ]ᵐ • [ l₁ ]ˡ') ps)) .proj₂ ≡ - sform q₀₁ ps
  sform2₁ ps = begin
    (head (act ([ m₁ ]ᵐ • [ l₁ ]ˡ') ps)) .proj₂
      ≡⟨ sym (-‿involutive _) ⟩
    - - (head (act ([ m₁ ]ᵐ • [ l₁ ]ˡ') ps)) .proj₂
      ≡⟨ cong -_ (sym (sform-pX0 (act ([ m₁ ]ᵐ • [ l₁ ]ˡ') ps))) ⟩
    - sform pX₀ (act ([ m₁ ]ᵐ • [ l₁ ]ˡ') ps)
      ≡⟨ cong (λ v → - sform v (act ([ m₁ ]ᵐ • [ l₁ ]ˡ') ps)) (sym g₁-q₀₁) ⟩
    - sform (act ([ m₁ ]ᵐ • [ l₁ ]ˡ') q₀₁) (act ([ m₁ ]ᵐ • [ l₁ ]ˡ') ps)
      ≡⟨ cong -_ (sform-preserving ([ m₁ ]ᵐ • [ l₁ ]ˡ') q₀₁ ps) ⟩
    - sform q₀₁ ps ∎
  sform2₂ : ∀ ps → (head (act ([ m₂ ]ᵐ • [ l₁ ]ˡ') ps)) .proj₂ ≡ - sform q₀₂ ps
  sform2₂ ps = begin
    (head (act ([ m₂ ]ᵐ • [ l₁ ]ˡ') ps)) .proj₂
      ≡⟨ sym (-‿involutive _) ⟩
    - - (head (act ([ m₂ ]ᵐ • [ l₁ ]ˡ') ps)) .proj₂
      ≡⟨ cong -_ (sym (sform-pX0 (act ([ m₂ ]ᵐ • [ l₁ ]ˡ') ps))) ⟩
    - sform pX₀ (act ([ m₂ ]ᵐ • [ l₁ ]ˡ') ps)
      ≡⟨ cong (λ v → - sform v (act ([ m₂ ]ᵐ • [ l₁ ]ˡ') ps)) (sym g₂-q₀₂) ⟩
    - sform (act ([ m₂ ]ᵐ • [ l₁ ]ˡ') q₀₂) (act ([ m₂ ]ᵐ • [ l₁ ]ˡ') ps)
      ≡⟨ cong -_ (sform-preserving ([ m₂ ]ᵐ • [ l₁ ]ˡ') q₀₂ ps) ⟩
    - sform q₀₂ ps ∎
  sform-q0-eq : ∀ ps → sform q₀₁ ps ≡ sform q₀₂ ps
  sform-q0-eq ps = neg-inj _ _ (begin
    - sform q₀₁ ps
      ≡⟨ sym (sform2₁ ps) ⟩
    (head (act ([ m₁ ]ᵐ • [ l₁ ]ˡ') ps)) .proj₂
      ≡⟨ cong proj₂ (h' ps) ⟩
    (head (act ([ m₂ ]ᵐ • [ l₁ ]ˡ') ps)) .proj₂
      ≡⟨ sform2₂ ps ⟩
    - sform q₀₂ ps ∎)
  q0-eq : q₀₁ ≡ q₀₂
  q0-eq = sform-inj q₀₁ q₀₂ sform-q0-eq
  vd-e-eq : vd₁ ∷ʳ pXZ e₁ ≡ vd₂ ∷ʳ pXZ e₂
  vd-e-eq = trans (sym l-q₀₁) (trans (cong (act [ l₁ ]ˡ') q0-eq) l-q₀₂)
  e-eq : e₁ ≡ e₂
  e-eq = cong proj₂
    (trans (sym (last-snoc vd₁ (pXZ e₁)))
    (trans (cong last vd-e-eq)
           (last-snoc vd₂ (pXZ e₂))))
  vd-eq : vd₁ ≡ vd₂
  vd-eq = trans (sym (init-snoc vd₁ (pXZ e₁)))
    (trans (cong init vd-e-eq)
           (init-snoc vd₂ (pXZ e₂)))
  m-eq : m₁ ≡ m₂
  m-eq = ≡×≡⇒≡ (e-eq , vd-eq)

-- D-box pZ-prefix with pI second entry: head(act [d]ᵈ (pZ ∷ pI ∷ t)) = (₀, d.proj₁).
lemma-dbox-pZ-pI : ∀ {n} (d : D) (t : Pauli n) →
  head (act [ d ]ᵈ (pZ ∷ pI ∷ t)) ≡ (₀ , d .proj₁)
lemma-dbox-pZ-pI {n} (₀ , d₂) t = begin
  head (act [ ₀ , d₂ ]ᵈ (pZ ∷ pI ∷ t))            ≡⟨ auto ⟩
  head (act (Ex • CZ^ (- d₂)) (pZ ∷ pI ∷ t))       ≡⟨ auto ⟩
  head (act Ex (act (CZ^ (- d₂)) (pZ ∷ pI ∷ t)))   ≡⟨ auto ⟩
  head (act Ex ((₀ , ₁ + ₀ * (- d₂)) ∷ (₀ , ₀ + ₀ * (- d₂)) ∷ t))
    ≡⟨ cong (λ xx → head (act Ex ((₀ , ₁ + xx) ∷ (₀ , ₀ + xx) ∷ t))) (*-zeroˡ (- d₂)) ⟩
  head (act Ex ((₀ , ₁ + ₀) ∷ (₀ , ₀ + ₀) ∷ t))
    ≡⟨ cong head (lemma-act-Ex pZ pI t) ⟩
  head (pI ∷ pZ ∷ t) ≡⟨ auto ⟩
  (₀ , ₀) ∎
lemma-dbox-pZ-pI {n} (c@(₁₊ c') , d₂) t = begin
  head (act [ c , d₂ ]ᵈ (pZ ∷ pI ∷ t))               ≡⟨ auto ⟩
  head (act ([ ₀ , ₁ ]ᵈ • [ (c , d₂) , (λ ()) ]ᵃ) (pZ ∷ pI ∷ t))
    ≡⟨ cong (λ xx → head (act [ ₀ , ₁ ]ᵈ xx))
            (lemma-abox-X (c , d₂) pZ (λ ()) (pI ∷ t)) ⟩
  head (act [ ₀ , ₁ ]ᵈ ((sform1 (c , d₂) pZ , ₀ * c⁻¹) ∷ pI ∷ t))
    ≡⟨ cong₂ (λ xx yy → head (act [ ₀ , ₁ ]ᵈ ((xx , yy) ∷ pI ∷ t)))
             sform-simp (*-zeroˡ c⁻¹) ⟩
  head (act [ ₀ , ₁ ]ᵈ ((- c , ₀) ∷ pI ∷ t))          ≡⟨ auto ⟩
  head (act (Ex • CZ^ (- ₁)) ((- c , ₀) ∷ pI ∷ t))     ≡⟨ auto ⟩
  head (act Ex (act (CZ^ (- ₁)) ((- c , ₀) ∷ pI ∷ t))) ≡⟨ auto ⟩
  head (act Ex ((- c , ₀ + ₀ * (- ₁)) ∷ (₀ , ₀ + (- c) * (- ₁)) ∷ t))
    ≡⟨ cong₂ (λ xx yy → head (act Ex ((- c , ₀ + xx) ∷ (₀ , ₀ + yy) ∷ t)))
             (*-zeroˡ (- ₁)) neg-neg-c ⟩
  head (act Ex ((- c , ₀ + ₀) ∷ (₀ , ₀ + c) ∷ t))
    ≡⟨ cong₂ (λ xx yy → head (act Ex ((- c , xx) ∷ (₀ , yy) ∷ t)))
             (+-identityʳ ₀) (+-identityˡ c) ⟩
  head (act Ex ((- c , ₀) ∷ (₀ , c) ∷ t))
    ≡⟨ cong head (lemma-act-Ex (- c , ₀) (₀ , c) t) ⟩
  head ((₀ , c) ∷ (- c , ₀) ∷ t) ≡⟨ auto ⟩
  (₀ , c) ∎
  where
  c⁻¹ = ((c , λ ()) ⁻¹) .proj₁
  sform-simp : sform1 (c , d₂) pZ ≡ - c
  sform-simp = begin
    - c * ₁ + ₀ * d₂  ≡⟨ cong (- c * ₁ +_) (*-zeroˡ d₂) ⟩
    - c * ₁ + ₀        ≡⟨ +-identityʳ (- c * ₁) ⟩
    - c * ₁            ≡⟨ *-identityʳ (- c) ⟩
    - c ∎
  neg-neg-c : (- c) * (- ₁) ≡ c
  neg-neg-c = trans ([-x][-y]≈xy c ₁) (*-identityʳ c)

-- D-box pX-prefix with pI second entry: head(act [d]ᵈ (pX ∷ pI ∷ t)) = (₀, -d.proj₂).
lemma-dbox-pX-pI : ∀ {n} (d : D) (t : Pauli n) →
  head (act [ d ]ᵈ (pX ∷ pI ∷ t)) ≡ (₀ , - d .proj₂)
lemma-dbox-pX-pI {n} (₀ , d₂) t = begin
  head (act [ ₀ , d₂ ]ᵈ (pX ∷ pI ∷ t))            ≡⟨ auto ⟩
  head (act (Ex • CZ^ (- d₂)) (pX ∷ pI ∷ t))       ≡⟨ auto ⟩
  head (act Ex (act (CZ^ (- d₂)) (pX ∷ pI ∷ t)))   ≡⟨ auto ⟩
  head (act Ex ((₁ , ₀ + ₀ * (- d₂)) ∷ (₀ , ₀ + ₁ * (- d₂)) ∷ t))
    ≡⟨ cong₂ (λ xx yy → head (act Ex ((₁ , ₀ + xx) ∷ (₀ , ₀ + yy) ∷ t)))
             (*-zeroˡ (- d₂)) (*-identityˡ (- d₂)) ⟩
  head (act Ex ((₁ , ₀ + ₀) ∷ (₀ , ₀ + (- d₂)) ∷ t))
    ≡⟨ cong₂ (λ xx yy → head (act Ex ((₁ , xx) ∷ (₀ , yy) ∷ t)))
             (+-identityʳ ₀) (+-identityˡ (- d₂)) ⟩
  head (act Ex (pX ∷ (₀ , - d₂) ∷ t))
    ≡⟨ cong head (lemma-act-Ex pX (₀ , - d₂) t) ⟩
  head ((₀ , - d₂) ∷ pX ∷ t) ≡⟨ auto ⟩
  (₀ , - d₂) ∎
lemma-dbox-pX-pI {n} (c@(₁₊ c') , d₂) t = begin
  head (act [ c , d₂ ]ᵈ (pX ∷ pI ∷ t))               ≡⟨ auto ⟩
  head (act ([ ₀ , ₁ ]ᵈ • [ (c , d₂) , (λ ()) ]ᵃ) (pX ∷ pI ∷ t))
    ≡⟨ cong (λ xx → head (act [ ₀ , ₁ ]ᵈ xx))
            (lemma-abox-X (c , d₂) pX (λ ()) (pI ∷ t)) ⟩
  head (act [ ₀ , ₁ ]ᵈ ((sform1 (c , d₂) pX , ₁ * c⁻¹) ∷ pI ∷ t))
    ≡⟨ cong₂ (λ xx yy → head (act [ ₀ , ₁ ]ᵈ ((xx , yy) ∷ pI ∷ t)))
             sform-pX-simp (*-identityˡ c⁻¹) ⟩
  head (act [ ₀ , ₁ ]ᵈ ((d₂ , c⁻¹) ∷ pI ∷ t))          ≡⟨ auto ⟩
  head (act (Ex • CZ^ (- ₁)) ((d₂ , c⁻¹) ∷ pI ∷ t))     ≡⟨ auto ⟩
  head (act Ex (act (CZ^ (- ₁)) ((d₂ , c⁻¹) ∷ pI ∷ t))) ≡⟨ auto ⟩
  head (act Ex ((d₂ , c⁻¹ + ₀ * (- ₁)) ∷ (₀ , ₀ + d₂ * (- ₁)) ∷ t))
    ≡⟨ cong₂ (λ xx yy → head (act Ex ((d₂ , c⁻¹ + xx) ∷ (₀ , ₀ + yy) ∷ t)))
             (*-zeroˡ (- ₁)) neg-d₂-simp ⟩
  head (act Ex ((d₂ , c⁻¹ + ₀) ∷ (₀ , ₀ + (- d₂)) ∷ t))
    ≡⟨ cong₂ (λ xx yy → head (act Ex ((d₂ , xx) ∷ (₀ , yy) ∷ t)))
             (+-identityʳ c⁻¹) (+-identityˡ (- d₂)) ⟩
  head (act Ex ((d₂ , c⁻¹) ∷ (₀ , - d₂) ∷ t))
    ≡⟨ cong head (lemma-act-Ex (d₂ , c⁻¹) (₀ , - d₂) t) ⟩
  head ((₀ , - d₂) ∷ (d₂ , c⁻¹) ∷ t) ≡⟨ auto ⟩
  (₀ , - d₂) ∎
  where
  c⁻¹ = ((c , λ ()) ⁻¹) .proj₁
  sform-pX-simp : sform1 (c , d₂) pX ≡ d₂
  sform-pX-simp = begin
    - c * ₀ + ₁ * d₂  ≡⟨ cong₂ _+_ (*-zeroʳ (- c)) (*-identityˡ d₂) ⟩
    ₀ + d₂             ≡⟨ +-identityˡ d₂ ⟩
    d₂ ∎
  neg-d₂-simp : d₂ * (- ₁) ≡ - d₂
  neg-d₂-simp = trans (sym (-‿distribʳ-* d₂ ₁)) (cong -_ (*-identityʳ d₂))

-- D-box pZ-transparency: head(act [d]ᵈ (pZ ∷ q ∷ t)) = q +₁ (₀, d.proj₁).
lemma-dbox-pZ-head : ∀ {n} (d : D) (q : Pauli1) (t : Pauli n) →
  head (act [ d ]ᵈ (pZ ∷ q ∷ t)) ≡ q +₁ (₀ , d .proj₁)
lemma-dbox-pZ-head {n} (₀ , d₂) q@(qa , qb) t = begin
  head (act [ ₀ , d₂ ]ᵈ (pZ ∷ q ∷ t))            ≡⟨ auto ⟩
  head (act (Ex • CZ^ (- d₂)) (pZ ∷ q ∷ t))       ≡⟨ auto ⟩
  head (act Ex (act (CZ^ (- d₂)) (pZ ∷ q ∷ t)))   ≡⟨ auto ⟩
  head (act Ex ((₀ , ₁ + qa * (- d₂)) ∷ (qa , qb + ₀ * (- d₂)) ∷ t))
    ≡⟨ cong (λ xx → head (act Ex ((₀ , ₁ + qa * (- d₂)) ∷ (qa , qb + xx) ∷ t)))
            (*-zeroˡ (- d₂)) ⟩
  head (act Ex ((₀ , ₁ + qa * (- d₂)) ∷ (qa , qb + ₀) ∷ t))
    ≡⟨ cong head (lemma-act-Ex (₀ , ₁ + qa * (- d₂)) (qa , qb + ₀) t) ⟩
  head ((qa , qb + ₀) ∷ (₀ , ₁ + qa * (- d₂)) ∷ t) ≡⟨ auto ⟩
  (qa , qb + ₀)
    ≡⟨ cong (_, qb + ₀) (sym (+-identityʳ qa)) ⟩
  (qa + ₀ , qb + ₀) ∎
lemma-dbox-pZ-head {n} (c@(₁₊ c') , d₂) q@(qa , qb) t = begin
  head (act [ c , d₂ ]ᵈ (pZ ∷ q ∷ t))               ≡⟨ auto ⟩
  head (act ([ ₀ , ₁ ]ᵈ • [ (c , d₂) , (λ ()) ]ᵃ) (pZ ∷ q ∷ t))
    ≡⟨ cong (λ xx → head (act [ ₀ , ₁ ]ᵈ xx))
            (lemma-abox-X (c , d₂) pZ (λ ()) (q ∷ t)) ⟩
  head (act [ ₀ , ₁ ]ᵈ ((sform1 (c , d₂) pZ , ₀ * c⁻¹) ∷ q ∷ t))
    ≡⟨ cong₂ (λ xx yy → head (act [ ₀ , ₁ ]ᵈ ((xx , yy) ∷ q ∷ t)))
             sform-simp (*-zeroˡ c⁻¹) ⟩
  head (act [ ₀ , ₁ ]ᵈ ((- c , ₀) ∷ q ∷ t))          ≡⟨ auto ⟩
  head (act (Ex • CZ^ (- ₁)) ((- c , ₀) ∷ q ∷ t))     ≡⟨ auto ⟩
  head (act Ex (act (CZ^ (- ₁)) ((- c , ₀) ∷ q ∷ t))) ≡⟨ auto ⟩
  head (act Ex ((- c , ₀ + qa * (- ₁)) ∷ (qa , qb + (- c) * (- ₁)) ∷ t))
    ≡⟨ cong₂ (λ xx yy → head (act Ex ((- c , ₀ + xx) ∷ (qa , qb + yy) ∷ t)))
             neg-qa-simp neg-neg-c ⟩
  head (act Ex ((- c , ₀ + (- qa)) ∷ (qa , qb + c) ∷ t))
    ≡⟨ cong head (lemma-act-Ex (- c , ₀ + (- qa)) (qa , qb + c) t) ⟩
  head ((qa , qb + c) ∷ (- c , ₀ + (- qa)) ∷ t) ≡⟨ auto ⟩
  (qa , qb + c)
    ≡⟨ cong (_, qb + c) (sym (+-identityʳ qa)) ⟩
  (qa + ₀ , qb + c) ∎
  where
  c⁻¹ = ((c , λ ()) ⁻¹) .proj₁
  sform-simp : sform1 (c , d₂) pZ ≡ - c
  sform-simp = begin
    - c * ₁ + ₀ * d₂  ≡⟨ cong (- c * ₁ +_) (*-zeroˡ d₂) ⟩
    - c * ₁ + ₀        ≡⟨ +-identityʳ (- c * ₁) ⟩
    - c * ₁            ≡⟨ *-identityʳ (- c) ⟩
    - c ∎
  neg-neg-c : (- c) * (- ₁) ≡ c
  neg-neg-c = trans ([-x][-y]≈xy c ₁) (*-identityʳ c)
  neg-qa-simp : qa * (- ₁) ≡ - qa
  neg-qa-simp = trans (sym (-‿distribʳ-* qa ₁)) (cong -_ (*-identityʳ qa))

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

-- Helper: head(act [d]ᵈ (q ∷ r)).proj₁ = head r .proj₁ for any q.
-- The D-box action on (q ∷ r) leaves the first component of head r unchanged.
lemma-dbox-head-fst : ∀ {n} (d : D) (q : Pauli1) (r : Pauli (₁₊ n)) →
  head (act [ d ]ᵈ (q ∷ r)) .proj₁ ≡ head r .proj₁
lemma-dbox-head-fst (₀ , d₂) (a , b) ((c , e) ∷ rs) =
  cong (λ v → head v .proj₁) (lemma-act-Ex (a , b + c * (- d₂)) (c , e + a * (- d₂)) rs)
lemma-dbox-head-fst (₁₊ a' , b') q ((c , e) ∷ rs) =
  trans
    (cong (λ v → head (act [ ₀ , ₁ ]ᵈ v) .proj₁) (lemma-abox-X (₁₊ a' , b') q (λ ()) ((c , e) ∷ rs)))
    (lemma-dbox-head-fst (₀ , ₁) (sform1 (₁₊ a' , b') q , e-after-abox-q (₁₊ a' , b') q (λ ())) ((c , e) ∷ rs))

-- The M×L' branch (inj₁) and D×LM branch (inj₂) produce distinct head outputs.
-- Proof: the inj₁ action on (q ∷ vb) has a first-component that varies with q
-- (via the symplectic form), while inj₂ keeps it constant. Contradiction via
-- evaluating at q = pI, pZ, pX and using lemma-sform1-XZ.
lemma-lm-inj₁≁inj₂ : ∀ {n} (m : M (₃₊ n)) (l : L' (₃₊ n)) (d : D) (lm' : LM (₂₊ n)) →
  (∀ ps → head (act ([ m ]ᵐ • [ l ]ˡ') ps) ≡ head (act ([ d ]ᵈ • [ lm' ]ˡᵐ ↑) ps)) → ⊥
lemma-lm-inj₁≁inj₂ {n} m l d lm' h = nz p1=pI
  where
  open ≡-Reasoning
  vb = l .proj₁
  p1 = l .proj₂ .proj₁
  nz = l .proj₂ .proj₂
  e  = m .proj₁
  vd = m .proj₂
  r  = act [ lm' ]ˡᵐ vb

  -- act ([m]ᵐ • [l]ˡ') (p1 ∷ vb) = pZ₀  (copied from Theorem-LM claim1 pattern)
  act-ml : act ([ m ]ᵐ • [ l ]ˡ') (p1 ∷ vb) ≡ pZ₀
  act-ml = begin
    act ([ m ]ᵐ • [ l ]ˡ') (p1 ∷ vb)
      ≡⟨ auto ⟩
    act ([ m ]ᵐ • [ vb ]ᵛᵇ • [ (p1 , nz) ]ᵃ) (p1 ∷ vb)
      ≡⟨ Eq.cong (act ([ m ]ᵐ • [ vb ]ᵛᵇ)) (lemma-abox p1 nz vb) ⟩
    act ([ m ]ᵐ • [ vb ]ᵛᵇ) (pZ ∷ vb)
      ≡⟨ Eq.cong (act ([ m ]ᵐ)) (lemma-bboxes vb) ⟩
    act ([ m ]ᵐ) pZₙ
      ≡⟨ auto ⟩
    act ([ e ]ᵉ • [ vd ]ᵛᵈ) pZₙ
      ≡⟨ Eq.cong (act ([ e ]ᵉ • [ vd ]ᵛᵈ)) lemma-pZₙ-pIₙ∷ʳpZ ⟩
    act ([ e ]ᵉ • [ vd ]ᵛᵈ) (pIₙ ∷ʳ pZ)
      ≡⟨ Eq.cong (act ([ e ]ᵉ)) (lemma-dboxes-Z vd) ⟩
    pZ₀ ∎

  -- For any q, sform (p1 ∷ vb) (q ∷ vb) = head r .proj₁.
  -- LHS uses symplecticity of [m]ᵐ • [l]ˡ'; RHS uses lemma-dbox-head-fst.
  h-sform : ∀ (q : Pauli1) → sform (p1 ∷ vb) (q ∷ vb) ≡ head r .proj₁
  h-sform q = begin
    sform (p1 ∷ vb) (q ∷ vb)
      ≡⟨ sym (sform-preserving ([ m ]ᵐ • [ l ]ˡ') (p1 ∷ vb) (q ∷ vb)) ⟩
    sform (act ([ m ]ᵐ • [ l ]ˡ') (p1 ∷ vb)) (act ([ m ]ᵐ • [ l ]ˡ') (q ∷ vb))
      ≡⟨ cong (λ v → sform v (act ([ m ]ᵐ • [ l ]ˡ') (q ∷ vb))) act-ml ⟩
    sform pZ₀ (act ([ m ]ᵐ • [ l ]ˡ') (q ∷ vb))
      ≡⟨ lemma-sform-pZ0 (act ([ m ]ᵐ • [ l ]ˡ') (q ∷ vb)) ⟩
    head (act ([ m ]ᵐ • [ l ]ˡ') (q ∷ vb)) .proj₁
      ≡⟨ cong proj₁ (h (q ∷ vb)) ⟩
    head (act ([ d ]ᵈ • [ lm' ]ˡᵐ ↑) (q ∷ vb)) .proj₁
      ≡⟨ auto ⟩
    head (act [ d ]ᵈ (act ([ lm' ]ˡᵐ ↑) (q ∷ vb))) .proj₁
      ≡⟨ cong (λ v → head (act [ d ]ᵈ v) .proj₁) (lemma-act-↑ [ lm' ]ˡᵐ q vb) ⟩
    head (act [ d ]ᵈ (q ∷ r)) .proj₁
      ≡⟨ lemma-dbox-head-fst d q r ⟩
    head r .proj₁ ∎

  -- Right-cancellation: a + c = c → a = 0.
  cancel-add : ∀ {a c : ℤ ₚ} → a + c ≡ c → a ≡ ₀
  cancel-add {a} {c} eq = begin
    a             ≡⟨ sym (+-identityʳ a) ⟩
    a + ₀         ≡⟨ cong (a +_) (sym (+-inverseʳ c)) ⟩
    a + (c + - c) ≡⟨ sym (+-assoc a c (- c)) ⟩
    (a + c) + - c ≡⟨ cong (_+ - c) eq ⟩
    c + - c       ≡⟨ +-inverseʳ c ⟩
    ₀ ∎

  -- h-sform pI gives sform vb vb = head r .proj₁.
  hC : sform vb vb ≡ head r .proj₁
  hC = begin
    sform vb vb                   ≡⟨ sym (+-identityˡ (sform vb vb)) ⟩
    ₀ + sform vb vb               ≡⟨ cong (_+ sform vb vb) (sym (lemma-sform1-pIʳ p1)) ⟩
    sform1 p1 pI + sform vb vb   ≡⟨ h-sform pI ⟩
    head r .proj₁ ∎

  sf1-pZ-0 : sform1 p1 pZ ≡ ₀
  sf1-pZ-0 = cancel-add (trans (h-sform pZ) (sym hC))

  sf1-pX-0 : sform1 p1 pX ≡ ₀
  sf1-pX-0 = cancel-add (trans (h-sform pX) (sym hC))

  sf1pZ-p1 : sform1 pZ p1 ≡ ₀
  sf1pZ-p1 = trans (sform1-antisym' pZ p1) (trans (cong -_ sf1-pZ-0) -0#≈0#)

  sf1pX-p1 : sform1 pX p1 ≡ ₀
  sf1pX-p1 = trans (sform1-antisym' pX p1) (trans (cong -_ sf1-pX-0) -0#≈0#)

  p1=pI : p1 ≡ pI
  p1=pI = lemma-sform1-XZ p1 (sf1pZ-p1 , sf1pX-p1)

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

