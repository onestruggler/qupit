open import Level using (0ℓ)

open import Relation.Binary using (Rel)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Binary.Morphism.Definitions using (Homomorphic₂)
open import Relation.Binary.PropositionalEquality using (_≡_ ; inspect ; setoid ; module ≡-Reasoning) renaming ([_] to [_]')
import Relation.Binary.Reasoning.Setoid as SR
import Relation.Binary.PropositionalEquality as Eq
open import Relation.Nullary.Decidable using (yes ; no)


open import Function using (_∘_ ; id)
open import Function.Definitions using (Injective)

open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂ ; map₁)
open import Data.Product.Relation.Binary.Pointwise.NonDependent using (≡×≡⇒≡ ; Pointwise ; ≡⇒≡×≡)
open import Data.Nat using (ℕ ; zero ; suc)
import Data.Nat as Nat
open import Data.Fin
open import Data.Fin.Induction
open import Data.Sum using (_⊎_ ; inj₁ ; inj₂)
open import Data.Unit using (⊤ ; tt)
open import Data.Empty using (⊥ ; ⊥-elim)

open import Word.Base hiding (wfoldl)
open import Word.Properties
import Presentation.Base as PB
import Presentation.Properties as PP
open PP using (NFProperty ; NFProperty')
import Presentation.CosetNF as CA
import Presentation.Reidemeister-Schreier as RS
module RSF = RS.Star-Injective-Full.Reidemeister-Schreier-Full


open import Data.Fin.Properties using (suc-injective ; toℕ-inject₁ ; toℕ-fromℕ)
import Data.Nat.Properties as NP

import Presentation.Groups.Cyclic as Cyclic
import Presentation.Groups.Sn as Sn
open Sn hiding (nfp ; nfp')
open import Presentation.Construct.Base
import Presentation.Construct.Properties.NDirectProduct as NDP

module Presentation.Groups.SnD where

  N = 4

  C^n : (n : ℕ) -> WRel (Cyclic.X ⊎^ n)
  C^n n = Cyclic.pres N ⊕^ n

  -- examples:
--  S2 = Sn.pres 2
--  D3 = C^n 3


  conj : ∀ n -> (Sn.X n) -> (Cyclic.X ⊎^ (suc n)) -> (Cyclic.X ⊎^ (suc n))
  conj zero () n
  conj (suc zero) swap (inj₁ tt) = inj₂ tt
  conj (suc zero) swap (inj₂ tt) = inj₁ tt
  conj (suc (suc n)) swap (inj₁ tt) = inj₂ (inj₁ tt)
  conj (suc (suc n)) swap (inj₂ (inj₁ x)) = inj₁ x
  conj (suc (suc n)) swap y'@(inj₂ (inj₂ y)) = y'
  conj (suc (suc n)) (h ₛ) x'@(inj₁ x) = x'
  conj (suc (suc n)) (h ₛ) (inj₂ y) = inj₂ (conj (suc n) h y)


  [_⇑]′ : ∀ {n} -> Word ((Cyclic.X ⊎^ (suc n))) -> Word ((Cyclic.X ⊎^ (suc (suc n))))
  [_⇑]′ {n} = wmap inj₂ 

  aux-conj0 : ∀ k' -> let k = suc (suc k') in ∀ h x -> ((conj k) ⁿ) (h ₛ) ([_⇑]′ {suc k'} x) ≡ [_⇑]′ {suc k'} ( ((conj (suc k')) ⁿ) h x)
  aux-conj0 k' h [ x ]ʷ = Eq.refl
  aux-conj0 k' h ε = Eq.refl
  aux-conj0 k' h (x • x₁) rewrite aux-conj0 k' h x | aux-conj0 k' h x₁ = Eq.refl


  aux-conj : ∀ k' -> let k = suc (suc k') in ∀ h x -> ((conj k) ʰ) [ h ⇑] (inj₂ x) ≡ inj₂ ( ((conj (suc k')) ʰ) h x)
  aux-conj zero [ x₁ ]ʷ x = Eq.refl
  aux-conj zero ε x = Eq.refl
  aux-conj zero (h • h₁) x with aux-conj zero h₁ x
  ... | ih rewrite ih with aux-conj zero h ((conj 1 ʰ) h₁ x)
  ... | ih2 = ih2
  aux-conj (suc k') [ x₁ ]ʷ x = Eq.refl
  aux-conj (suc k') ε x = Eq.refl
  aux-conj (suc k') (h • h₁) x with aux-conj (suc k') h₁ x
  ... | ih rewrite ih with aux-conj (suc k') h ((conj (suc (suc k')) ʰ) h₁ x)
  ... | ih2 = ih2

  
  aux-conj1 : ∀ k' -> let k = suc (suc k') in ∀ h x -> ((conj k) ʰ) [ h ⇑] (inj₁ x) ≡ inj₁ x
  aux-conj1 k' [ x₁ ]ʷ x = Eq.refl
  aux-conj1 k' ε x = Eq.refl
  aux-conj1 k' (h • h₁) x with aux-conj1 ( k') h₁ ( x)
  ... | ih with ((conj (suc (suc k')) ʰ) [ h₁ ⇑] (inj₁ x))
  ... | inj₁ x₁ rewrite ih with aux-conj1 k' h x
  ... | ih2 = ih2

  aux-conj3 : ∀ k' -> let k = suc (suc k') in ∀ (x : Word ((Cyclic.X ⊎^ (suc k')))) -> ((conj k) ⁿ) (X.swap) ([_⇑]′{suc k'} ([_⇑]′ {k'} x)) ≡ ([_⇑]′ {suc k'}([_⇑]′ {k'} x))
  aux-conj3 k' [ x ]ʷ = Eq.refl
  aux-conj3 k' ε = Eq.refl
  aux-conj3 k' (x • x₁) rewrite aux-conj3 k' x | aux-conj3 k' x₁ = Eq.refl


  conj-hyph : ∀ k -> let _===₂_ = (Sn.rel k) in ∀ {c d} n -> c ===₂ d -> ((conj k) ʰ) c n ≡ ((conj k) ʰ) d n
  conj-hyph zero {c} {d} n ()
  conj-hyph (suc zero) {c} {d} (inj₁ tt) order = Eq.refl
  conj-hyph (suc zero) {c} {d} (inj₂ tt) order = Eq.refl
  conj-hyph (suc (suc k)) {c} {d} (inj₁ tt) order = Eq.refl
  conj-hyph (suc (suc (suc k))) {c} {d} (inj₁ tt) comm = Eq.refl
  conj-hyph (suc (suc zero)) {c} {d} (inj₁ tt) yang-baxter = Eq.refl
  conj-hyph (suc (suc (suc k))) {c} {d} (inj₁ tt) yang-baxter = Eq.refl
  conj-hyph (suc (suc k)) {c} {d} (inj₁ tt) (congₛ {w = w} {v} eqv) rewrite aux-conj1 k w tt |  aux-conj1 k v tt = Eq.refl
  conj-hyph (suc (suc k)) {c} {d} (inj₂ (inj₁ x)) order = Eq.refl
  conj-hyph (suc (suc k)) {c} {d} (inj₂ (inj₂ y)) order = Eq.refl
  conj-hyph (suc (suc (suc k))) {c} {d} (inj₂ (inj₁ x)) comm = Eq.refl
  conj-hyph (suc (suc (suc k))) {c} {d} (inj₂ (inj₂ y)) comm = Eq.refl
  conj-hyph (suc (suc zero)) {c} {d} (inj₂ (inj₁ x)) yang-baxter = Eq.refl
  conj-hyph (suc (suc zero)) {c} {d} (inj₂ (inj₂ y)) yang-baxter = Eq.refl
  conj-hyph (suc (suc (suc k))) {c} {d} (inj₂ (inj₁ x)) yang-baxter = Eq.refl
  conj-hyph (suc (suc (suc k))) {c} {d} (inj₂ (inj₂ (inj₁ x))) yang-baxter = Eq.refl
  conj-hyph (suc (suc (suc k))) {c} {d} (inj₂ (inj₂ (inj₂ y))) yang-baxter = Eq.refl
  conj-hyph (suc (suc zero)) {c} {d} (inj₂ y) (congₛ {w = w} {v} eqv) with conj-hyph 1 y eqv
  ... | ih rewrite aux-conj 0 w y | aux-conj 0 v y = Eq.cong inj₂ ih
  conj-hyph (suc (suc (suc k))) {c} {d} (inj₂ y) (congₛ {w = w} {v} eqv) with conj-hyph (suc (suc k)) y eqv
  ... | ih rewrite aux-conj (suc k) w y | aux-conj (suc k) v y = Eq.cong inj₂ ih

  conj-hypn : ∀ k -> let _===₁_ = PB._===_ (C^n (suc k)) in let _≈₁_ = PB._≈_ (C^n (suc k)) in ∀ c {w v} -> w ===₁ v -> (((conj k) ⁿ) c w) ≈₁ (((conj k) ⁿ) c v)
  conj-hypn (suc zero) X.swap {w} {v} (left Cyclic.order) = PB.axiom (right Cyclic.order)
  conj-hypn (suc (suc k)) X.swap {w} {v} (left Cyclic.order) = PB.axiom (right (left Cyclic.order))
  conj-hypn (suc k) (X.swap ₛ) {w} {v} (left Cyclic.order) = PB.axiom (left Cyclic.order)
  conj-hypn (suc k) ((c ₛ) ₛ) {w} {v} (left Cyclic.order) = PB.axiom (left Cyclic.order)
  conj-hypn (suc zero) X.swap {w} {v} (right {u} {v₁} Cyclic.order) = PB.axiom (left Cyclic.order)
  conj-hypn (suc (suc k)) X.swap {w} {v} (right {u} {v₁} (left {u₁} {v₂} Cyclic.order)) = PB.axiom (left Cyclic.order)
  conj-hypn (suc (suc k)) X.swap {w} {v} (right {u} {v₁} (right {u₁} {v₂} x)) rewrite aux-conj3 ( ( k)) u₁ | aux-conj3 ( ( k)) v₂ = PB.axiom (right (right x))
  conj-hypn (suc (suc k)) X.swap {w} {v} (right {u} {v₁} (mid (comm a b))) = PB.axiom (mid (comm tt (inj₂ b)))
  conj-hypn (suc (suc k)) (c ₛ) {w} {v} (right {w'} {v'} x) with conj-hypn (suc k) c x
  ... | ih rewrite aux-conj0 (k) c w' | aux-conj0 (k) c v' = rights ih
    where open LeftRightCongruence (C^n 1) (C^n (suc (suc k))) Γₓ
  conj-hypn (suc zero) X.swap {w} {v} (mid (comm a b)) = PB.sym (PB.axiom (mid (comm tt tt)))
  conj-hypn (suc (suc k)) X.swap {w} {v} (mid (comm tt (inj₁ x))) = PB.sym (PB.axiom (mid (comm tt (inj₁ tt))))
  conj-hypn (suc (suc k)) X.swap {w} {v} (mid (comm tt (inj₂ y))) = PB.axiom (right (mid (comm tt y)))
  conj-hypn (suc (suc k)) (c ₛ) {w} {v} (mid (comm a b)) = PB.axiom (mid (comm tt (conj (suc k) c b)))


  pres-SnD : (k : ℕ) -> WRel (⊤ ⊎^ suc k ⊎ X k)
  pres-SnD k = C^n (suc k) ⋊ Sn.rel k ⋆ conj k

  nfp : (k : ℕ) -> NFProperty (C^n (suc k) ⋊ Sn.rel k ⋆ conj k)
  nfp k = NFP0.nfp (NDP.nfp (Cyclic.pres N) (suc k) (Cyclic.nfp N)) (Sn.nfp k)
    where
    import Presentation.Construct.Properties.SemiDirectProduct as SDP0
    module SDP = SDP0 (C^n (suc k)) (Sn.rel k) (conj k)
    module NFP0 = SDP.NFP (conj-hyph k) (conj-hypn k)


  nfp' : (k : ℕ) -> NFProperty' (C^n (suc k) ⋊ Sn.rel k ⋆ conj k)
  nfp' k = NFP'0.nfp' (NDP.nfp' (Cyclic.pres N) (suc k) (Cyclic.nfp' N)) (Sn.nfp' k)
    where
    import Presentation.Construct.Properties.SemiDirectProduct as SDP0
    module SDP = SDP0 (C^n (suc k)) (Sn.rel k) (conj k)
    module NFP'0 = SDP.NFP' (conj-hyph k) (conj-hypn k)

  module Detail (k : ℕ) where
    import Presentation.Construct.Properties.SemiDirectProduct as SDP0
    module SDP = SDP0 (C^n (suc k)) (Sn.rel k) (conj k)
    module NFP0 = SDP.NFP (conj-hyph k) (conj-hypn k)
    open SDP
    open NFP0
