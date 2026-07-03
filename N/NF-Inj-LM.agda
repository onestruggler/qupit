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
import Presentation.Horizontal-Syntactics as PB
import Presentation.Properties as PP
open PP using (NFProperty ; NFProperty')
import Presentation.CosetNF as CA
import Presentation.Reidemeister-Schreier as RS
open import Notations
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



module N.NF-Inj-LM (p-2 : ℕ) (p-prime : Prime (2+ p-2))  where

pattern auto = Eq.refl

pattern ₀ = zero
pattern ₁ = ₁₊ ₀
pattern ₂ = ₁₊ ₁
pattern ₃ = ₁₊ ₂
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

open import N.NF-Inj-Base p-2 p-prime
open Symplectic-Derived-GroupLike

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


