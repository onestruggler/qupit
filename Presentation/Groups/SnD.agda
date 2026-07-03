------------------------------------------------------------------------
-- Presentations of groups
--
-- The wreath product ℤ/Nℤ ≀ Sₙ as a group presentation, together with
-- its normal-form property.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}

open import Relation.Binary.PropositionalEquality using (_≡_)
import Relation.Binary.PropositionalEquality as Eq

open import Data.Nat using (ℕ ; zero ; suc)
open import Data.Sum using (_⊎_ ; inj₁ ; inj₂)
open import Data.Unit using (⊤ ; tt)

open import Word.Base hiding (wfoldl)
open import Word.Properties
import Presentation.Horizontal-Syntactics as PB
import Presentation.Properties as PP
open PP using (NFProperty ; NFProperty')

import Presentation.Groups.Cyclic as Cyclic
import Presentation.Groups.Sn as Sn
open Sn hiding (nfp ; nfp')
open import Presentation.Construct.Base
import Presentation.Construct.Properties.NDirectProduct as NDP
open import Notations

module Presentation.Groups.SnD where

  N = 4

  C^n : (n : ℕ) → WRel (Cyclic.X ⊎^ n)
  C^n n = Cyclic.pres N ⊕^ n

  -- examples:
--  S2 = Sn.pres 2
--  D3 = C^n 3


  conj : ∀ n → (Sn.X n) → (Cyclic.X ⊎^ (₁₊ n)) → (Cyclic.X ⊎^ (₁₊ n))
  conj zero () n
  conj (₁₊ zero) swap (inj₁ tt) = inj₂ tt
  conj (₁₊ zero) swap (inj₂ tt) = inj₁ tt
  conj (₂₊ n) swap (inj₁ tt) = inj₂ (inj₁ tt)
  conj (₂₊ n) swap (inj₂ (inj₁ x)) = inj₁ x
  conj (₂₊ n) swap y'@(inj₂ (inj₂ y)) = y'
  conj (₂₊ n) (h ₛ) x'@(inj₁ x) = x'
  conj (₂₊ n) (h ₛ) (inj₂ y) = inj₂ (conj (₁₊ n) h y)


  [_⇑]′ : ∀ {n} → Word ((Cyclic.X ⊎^ (₁₊ n))) → Word ((Cyclic.X ⊎^ (₂₊ n)))
  [_⇑]′ {n} = wmap inj₂ 

  aux-conj0 : ∀ k' → let k = ₂₊ k' in ∀ h x → ((conj k) ⁿ) (h ₛ) ([_⇑]′ {₁₊ k'} x) ≡ [_⇑]′ {₁₊ k'} ( ((conj (₁₊ k')) ⁿ) h x)
  aux-conj0 k' h [ x ]ʷ = Eq.refl
  aux-conj0 k' h ε = Eq.refl
  aux-conj0 k' h (x • x₁) rewrite aux-conj0 k' h x | aux-conj0 k' h x₁ = Eq.refl


  aux-conj : ∀ k' → let k = ₂₊ k' in ∀ h x → ((conj k) ʰ) [ h ⇑] (inj₂ x) ≡ inj₂ ( ((conj (₁₊ k')) ʰ) h x)
  aux-conj zero [ x₁ ]ʷ x = Eq.refl
  aux-conj zero ε x = Eq.refl
  aux-conj zero (h • h₁) x with aux-conj zero h₁ x
  ... | ih rewrite ih with aux-conj zero h ((conj 1 ʰ) h₁ x)
  ... | ih2 = ih2
  aux-conj (₁₊ k') [ x₁ ]ʷ x = Eq.refl
  aux-conj (₁₊ k') ε x = Eq.refl
  aux-conj (₁₊ k') (h • h₁) x with aux-conj (₁₊ k') h₁ x
  ... | ih rewrite ih with aux-conj (₁₊ k') h ((conj (₂₊ k') ʰ) h₁ x)
  ... | ih2 = ih2

  
  aux-conj1 : ∀ k' → let k = ₂₊ k' in ∀ h x → ((conj k) ʰ) [ h ⇑] (inj₁ x) ≡ inj₁ x
  aux-conj1 k' [ x₁ ]ʷ x = Eq.refl
  aux-conj1 k' ε x = Eq.refl
  aux-conj1 k' (h • h₁) x with aux-conj1 ( k') h₁ ( x)
  ... | ih with ((conj (₂₊ k') ʰ) [ h₁ ⇑] (inj₁ x))
  ... | inj₁ x₁ rewrite ih with aux-conj1 k' h x
  ... | ih2 = ih2

  aux-conj3 : ∀ k' → let k = ₂₊ k' in ∀ (x : Word ((Cyclic.X ⊎^ (₁₊ k')))) → ((conj k) ⁿ) (X.swap) ([_⇑]′{₁₊ k'} ([_⇑]′ {k'} x)) ≡ ([_⇑]′ {₁₊ k'}([_⇑]′ {k'} x))
  aux-conj3 k' [ x ]ʷ = Eq.refl
  aux-conj3 k' ε = Eq.refl
  aux-conj3 k' (x • x₁) rewrite aux-conj3 k' x | aux-conj3 k' x₁ = Eq.refl


  conj-hyph : ∀ k → let _===₂_ = (Sn.rel k) in ∀ {c d} n → c ===₂ d → ((conj k) ʰ) c n ≡ ((conj k) ʰ) d n
  conj-hyph zero {c} {d} n ()
  conj-hyph (₁₊ zero) {c} {d} (inj₁ tt) order = Eq.refl
  conj-hyph (₁₊ zero) {c} {d} (inj₂ tt) order = Eq.refl
  conj-hyph (₂₊ k) {c} {d} (inj₁ tt) order = Eq.refl
  conj-hyph (₃₊ k) {c} {d} (inj₁ tt) comm = Eq.refl
  conj-hyph (₂₊ zero) {c} {d} (inj₁ tt) yang-baxter = Eq.refl
  conj-hyph (₃₊ k) {c} {d} (inj₁ tt) yang-baxter = Eq.refl
  conj-hyph (₂₊ k) {c} {d} (inj₁ tt) (congₛ {w = w} {v} eqv) rewrite aux-conj1 k w tt |  aux-conj1 k v tt = Eq.refl
  conj-hyph (₂₊ k) {c} {d} (inj₂ (inj₁ x)) order = Eq.refl
  conj-hyph (₂₊ k) {c} {d} (inj₂ (inj₂ y)) order = Eq.refl
  conj-hyph (₃₊ k) {c} {d} (inj₂ (inj₁ x)) comm = Eq.refl
  conj-hyph (₃₊ k) {c} {d} (inj₂ (inj₂ y)) comm = Eq.refl
  conj-hyph (₂₊ zero) {c} {d} (inj₂ (inj₁ x)) yang-baxter = Eq.refl
  conj-hyph (₂₊ zero) {c} {d} (inj₂ (inj₂ y)) yang-baxter = Eq.refl
  conj-hyph (₃₊ k) {c} {d} (inj₂ (inj₁ x)) yang-baxter = Eq.refl
  conj-hyph (₃₊ k) {c} {d} (inj₂ (inj₂ (inj₁ x))) yang-baxter = Eq.refl
  conj-hyph (₃₊ k) {c} {d} (inj₂ (inj₂ (inj₂ y))) yang-baxter = Eq.refl
  conj-hyph (₂₊ zero) {c} {d} (inj₂ y) (congₛ {w = w} {v} eqv) with conj-hyph 1 y eqv
  ... | ih rewrite aux-conj 0 w y | aux-conj 0 v y = Eq.cong inj₂ ih
  conj-hyph (₃₊ k) {c} {d} (inj₂ y) (congₛ {w = w} {v} eqv) with conj-hyph (₂₊ k) y eqv
  ... | ih rewrite aux-conj (₁₊ k) w y | aux-conj (₁₊ k) v y = Eq.cong inj₂ ih

  conj-hypn : ∀ k → let _===₁_ = PB._===_ (C^n (₁₊ k)) in let _≈₁_ = PB._≈_ (C^n (₁₊ k)) in ∀ c {w v} → w ===₁ v → (((conj k) ⁿ) c w) ≈₁ (((conj k) ⁿ) c v)
  conj-hypn (₁₊ zero) X.swap {w} {v} (left Cyclic.order) = PB.axiom (right Cyclic.order)
  conj-hypn (₂₊ k) X.swap {w} {v} (left Cyclic.order) = PB.axiom (right (left Cyclic.order))
  conj-hypn (₁₊ k) (X.swap ₛ) {w} {v} (left Cyclic.order) = PB.axiom (left Cyclic.order)
  conj-hypn (₁₊ k) ((c ₛ) ₛ) {w} {v} (left Cyclic.order) = PB.axiom (left Cyclic.order)
  conj-hypn (₁₊ zero) X.swap {w} {v} (right {u} {v₁} Cyclic.order) = PB.axiom (left Cyclic.order)
  conj-hypn (₂₊ k) X.swap {w} {v} (right {u} {v₁} (left {u₁} {v₂} Cyclic.order)) = PB.axiom (left Cyclic.order)
  conj-hypn (₂₊ k) X.swap {w} {v} (right {u} {v₁} (right {u₁} {v₂} x)) rewrite aux-conj3 ( ( k)) u₁ | aux-conj3 ( ( k)) v₂ = PB.axiom (right (right x))
  conj-hypn (₂₊ k) X.swap {w} {v} (right {u} {v₁} (mid (comm a b))) = PB.axiom (mid (comm tt (inj₂ b)))
  conj-hypn (₂₊ k) (c ₛ) {w} {v} (right {w'} {v'} x) with conj-hypn (₁₊ k) c x
  ... | ih rewrite aux-conj0 (k) c w' | aux-conj0 (k) c v' = rights ih
    where open LeftRightCongruence (C^n 1) (C^n (₂₊ k)) Γₓ
  conj-hypn (₁₊ zero) X.swap {w} {v} (mid (comm a b)) = PB.sym (PB.axiom (mid (comm tt tt)))
  conj-hypn (₂₊ k) X.swap {w} {v} (mid (comm tt (inj₁ x))) = PB.sym (PB.axiom (mid (comm tt (inj₁ tt))))
  conj-hypn (₂₊ k) X.swap {w} {v} (mid (comm tt (inj₂ y))) = PB.axiom (right (mid (comm tt y)))
  conj-hypn (₂₊ k) (c ₛ) {w} {v} (mid (comm a b)) = PB.axiom (mid (comm tt (conj (₁₊ k) c b)))


  pres-SnD : (k : ℕ) → WRel (⊤ ⊎^ ₁₊ k ⊎ X k)
  pres-SnD k = C^n (₁₊ k) ⋊ Sn.rel k ⋆ conj k

  nfp : (k : ℕ) → NFProperty (C^n (₁₊ k) ⋊ Sn.rel k ⋆ conj k)
  nfp k = NFP0.nfp (NDP.nfp (Cyclic.pres N) (₁₊ k) (Cyclic.nfp N)) (Sn.nfp k)
    where
    import Presentation.Construct.Properties.SemiDirectProduct as SDP0
    module SDP = SDP0 (C^n (₁₊ k)) (Sn.rel k) (conj k)
    module NFP0 = SDP.NFP (conj-hyph k) (conj-hypn k)


  nfp' : (k : ℕ) → NFProperty' (C^n (₁₊ k) ⋊ Sn.rel k ⋆ conj k)
  nfp' k = NFP'0.nfp' (NDP.nfp' (Cyclic.pres N) (₁₊ k) (Cyclic.nfp' N)) (Sn.nfp' k)
    where
    import Presentation.Construct.Properties.SemiDirectProduct as SDP0
    module SDP = SDP0 (C^n (₁₊ k)) (Sn.rel k) (conj k)
    module NFP'0 = SDP.NFP' (conj-hyph k) (conj-hypn k)

  module Detail (k : ℕ) where
    import Presentation.Construct.Properties.SemiDirectProduct as SDP0
    module SDP = SDP0 (C^n (₁₊ k)) (Sn.rel k) (conj k)
    module NFP0 = SDP.NFP (conj-hyph k) (conj-hypn k)
    open SDP
    open NFP0
