------------------------------------------------------------------------
-- Presentations of groups
--
-- Unique normal form for the loose (endofunction) semantics of Sₙ.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}

open import Level using (0ℓ)
open import Relation.Binary using (Setoid)
open import Data.Nat using (ℕ ; zero ; suc)
open import Data.Fin using (Fin) renaming (zero to fzero ; suc to fsuc)
import Data.Fin.Properties as FP
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_)
open import Data.Unit using (⊤ ; tt)
open import Data.Product using (_,_ ; proj₁ ; proj₂)
open import Data.Product.Relation.Binary.Pointwise.NonDependent using (≡×≡⇒≡)
import Presentation.Properties as PP
import Presentation.Normalization
open import Notations

module Examples.Groups.Symmetric.Loose.Uniqueness where

open import Examples.Groups.Symmetric.Syntactics
open import Examples.Groups.Symmetric.NormalForm
open import Examples.Groups.Symmetric.Loose.Semantics
open import Examples.Groups.Symmetric.Normalization
  using (nf-of ; lemma-nf-cong ; lemma-inv-nf)

private variable n : ℕ

------------------------------------------------------------------------
-- Encoding coset descriptors as Fin indices

private
  depth : ∀ {n} → C n → Fin (₁₊ n)
  depth ε      = fzero
  depth (σ• c) = fsuc (depth c)

  depth-inj : ∀ {n} {r r' : C n} → depth r ≡ depth r' → r ≡ r'
  depth-inj {r = ε}    {r' = ε}     _  = Eq.refl
  depth-inj {r = ε}    {r' = σ• _}  ()
  depth-inj {r = σ• _} {r' = ε}     ()
  depth-inj {r = σ• c} {r' = σ• c'} eq =
    Eq.cong σ•_ (depth-inj (FP.suc-injective eq))

  -- ⟦ [r]ᶜ ⟧ fzero ≡ depth r
  lemma-⟦[r]ᶜ⟧-zero : ∀ {n} (r : C n) → ⟦ [ r ]ᶜ ⟧ fzero ≡ depth r
  lemma-⟦[r]ᶜ⟧-zero ε      = Eq.refl
  lemma-⟦[r]ᶜ⟧-zero (σ• c) =
    Eq.trans (⟦↑⟧ ([ c ]ᶜ) (fsuc fzero))
             (Eq.cong fsuc (lemma-⟦[r]ᶜ⟧-zero c))

  -- ⟦ [r]ᶜ ⟧ is injective on fsuc-values
  lemma-[r]ᶜ-suc-inj : ∀ {n} (r : C n) {j₁ j₂ : Fin n}
    → ⟦ [ r ]ᶜ ⟧ (fsuc j₁) ≡ ⟦ [ r ]ᶜ ⟧ (fsuc j₂) → j₁ ≡ j₂
  lemma-[r]ᶜ-suc-inj ε {j₁} {j₂} eq with eq
  ... | Eq.refl = Eq.refl
  lemma-[r]ᶜ-suc-inj (σ• c) {fzero}    {fzero}    _   = Eq.refl
  lemma-[r]ᶜ-suc-inj (σ• c) {fzero}    {fsuc j₂'} eq
    with Eq.trans (Eq.sym (⟦↑⟧ ([ c ]ᶜ) fzero))
                  (Eq.trans eq (⟦↑⟧ ([ c ]ᶜ) (fsuc (fsuc j₂'))))
  ... | ()
  lemma-[r]ᶜ-suc-inj (σ• c) {fsuc j₁'} {fzero}    eq
    with Eq.trans (Eq.trans (Eq.sym (⟦↑⟧ ([ c ]ᶜ) (fsuc (fsuc j₁')))) eq)
                  (⟦↑⟧ ([ c ]ᶜ) fzero)
  ... | ()
  lemma-[r]ᶜ-suc-inj (σ• c) {fsuc j₁'} {fsuc j₂'} eq =
    Eq.cong fsuc (lemma-[r]ᶜ-suc-inj c step)
    where
    step : ⟦ [ c ]ᶜ ⟧ (fsuc j₁') ≡ ⟦ [ c ]ᶜ ⟧ (fsuc j₂')
    step = FP.suc-injective
      (Eq.trans (Eq.sym (⟦↑⟧ ([ c ]ᶜ) (fsuc (fsuc j₁'))))
      (Eq.trans eq      (⟦↑⟧ ([ c ]ᶜ) (fsuc (fsuc j₂')))))

------------------------------------------------------------------------
-- Helpers for unique-impl

private
  make-r≡r' : ∀ n (l l' : NF (₁₊ n)) (r r' : C (₁₊ n))
    → (eq : ∀ k → ⟦ inv-nf {(₂₊ n)} (l , r) ⟧ k ≡ ⟦ inv-nf {(₂₊ n)} (l' , r') ⟧ k)
    → r ≡ r'
  make-r≡r' n l l' r r' eq =
    depth-inj
      (Eq.trans (Eq.sym (lemma-⟦[r]ᶜ⟧-zero r))
      (Eq.trans
        (Eq.trans
          (Eq.cong (⟦ [ r ]ᶜ ⟧) (Eq.sym (⟦↑⟧ (inv-nf {(₁₊ n)} l) fzero)))
          (Eq.trans (eq fzero)
          (Eq.cong (⟦ [ r' ]ᶜ ⟧) (⟦↑⟧ (inv-nf {(₁₊ n)} l') fzero))))
        (lemma-⟦[r]ᶜ⟧-zero r')))

  make-eqj : ∀ n (l l' : NF (₁₊ n)) (r r' : C (₁₊ n))
    → r ≡ r'
    → (eq : ∀ k → ⟦ inv-nf {(₂₊ n)} (l , r) ⟧ k ≡ ⟦ inv-nf {(₂₊ n)} (l' , r') ⟧ k)
    → ∀ j → ⟦ inv-nf {(₁₊ n)} l ⟧ j ≡ ⟦ inv-nf {(₁₊ n)} l' ⟧ j
  make-eqj n l l' r r' r≡r' eq j =
    lemma-[r]ᶜ-suc-inj r
      (Eq.trans
        (Eq.cong (⟦ [ r ]ᶜ ⟧) (Eq.sym (⟦↑⟧ (inv-nf {(₁₊ n)} l) (fsuc j))))
        (Eq.trans
          (Eq.subst
            (λ s → ⟦ [ r ]ᶜ ⟧ (⟦ inv-nf {(₁₊ n)} l ↑ ⟧ (fsuc j))
                 ≡ ⟦ [ s ]ᶜ ⟧ (⟦ inv-nf {(₁₊ n)} l' ↑ ⟧ (fsuc j)))
            (Eq.sym r≡r')
            (eq (fsuc j)))
          (Eq.cong (⟦ [ r ]ᶜ ⟧) (⟦↑⟧ (inv-nf {(₁₊ n)} l') (fsuc j)))))

------------------------------------------------------------------------
-- Semantic injectivity of inv-nf: pointwise-equal denotations imply equal NFs

private
  unique-impl : ∀ n {u v : NF n}
    → (∀ k → ⟦ inv-nf {n} u ⟧ k ≡ ⟦ inv-nf {n} v ⟧ k)
    → u ≡ v
  unique-impl 0       {tt}     {tt}      _   = Eq.refl
  unique-impl 1       {tt}     {tt}      _   = Eq.refl
  unique-impl (₂₊ n') {l , r} {l' , r'} eq  =
    ≡×≡⇒≡ (unique-impl (₁₊ n') (make-eqj n' l l' r r' r≡r' eq) , r≡r')
    where r≡r' = make-r≡r' n' l l' r r' eq

------------------------------------------------------------------------
-- Unique normal form for the loose semantics

unique-nf : ∀ n →
  Presentation.Normalization.UniqueNormalForm
    (PP.word-setoid (_VRel,_===_ n)) (NF n) (nf-of {n}) (inv-nf {n})
    (Endo-setoid n) (⟦_⟧ {n})
unique-nf n = record
  { nf     = record { f-cong = lemma-nf-cong ; g∘f=id = lemma-inv-nf n }
  ; unique = unique-impl n
  }
