-- Part of the N.NF-Inj split (memory-reduced typechecking).
-- --safe omitted while the 4 head-injectivity lemmas remain postulated.
-- (call-by-need: --call-by-name omitted; these proof-heavy modules typecheck
--  far faster and with less memory under the default sharing strategy.)
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

open import N.NF p-2 p-prime using (act-nf)
open import N.NF-Inj-Base p-2 p-prime using (lemma-aux-vec)
open import N.NF-Inj-LM p-2 p-prime using (lemma-lm-head-inj ; lemma-lm-tail-surj)

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

