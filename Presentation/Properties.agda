------------------------------------------------------------------------
-- Presentations of groups
--
-- Basic algebraic structures and normal-form records for presented monoids
------------------------------------------------------------------------

{-# OPTIONS --safe #-}

open import Level using (0ℓ)
open import Relation.Binary using (IsEquivalence ; Setoid)
open import Data.Product using (_,_ ; proj₁ ; proj₂)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
import Relation.Binary.Reasoning.Setoid as SR

open import Word.Base
open import Notations

module Presentation.Properties {X : Set} (Γ : WRel X) where

import Presentation.Base as PB
open import Presentation.Base Γ

open import Relation.Binary.Definitions using (DecidableEquality ; Decidable)
open import Relation.Binary.PropositionalEquality using (setoid)
open import Relation.Nullary.Decidable using (via-injection)
open import Function.Bundles using (Injection)
open import Data.Nat as Nat using (ℕ ; zero ; suc)
import Data.Nat.Properties as NP
import Relation.Binary.Reasoning.Setoid as Eqv
open import Data.Product.Relation.Binary.Pointwise.NonDependent as PW
open import Data.Product using (_×_ ; ∃)
open import Data.List using (_++_ ; [] ; _∷_ ; List)

------------------------------------------------------------------------
-- Algebraic structures

≈-isEquivalence : IsEquivalence {A = Word X} _≈_
≈-isEquivalence = record
  { refl  = refl
  ; sym   = sym
  ; trans = trans
  }

word-setoid : Setoid 0ℓ 0ℓ
word-setoid = record
  { Carrier       = Word X
  ; _≈_           = _≈_
  ; isEquivalence = ≈-isEquivalence
  }

open import Algebra.Structures {A = Word X} _≈_

•-isMagma : IsMagma _•_
•-isMagma = record
  { isEquivalence = ≈-isEquivalence
  ; ∙-cong        = cong
  }

•-isSemigroup : IsSemigroup _•_
•-isSemigroup = record
  { isMagma = •-isMagma
  ; assoc   = λ x y z → assoc
  }

•-ε-isMonoid : IsMonoid _•_ ε
•-ε-isMonoid = record
  { isSemigroup = •-isSemigroup
  ; identity    = (λ x → left-unit) , (λ x → right-unit)
  }

------------------------------------------------------------------------
-- Algebraic bundles

open import Algebra.Bundles

•-magma : Magma 0ℓ 0ℓ
•-magma = record { isMagma = •-isMagma }

•-semigroup : Semigroup 0ℓ 0ℓ
•-semigroup = record { isSemigroup = •-isSemigroup }

•-ε-monoid : Monoid 0ℓ 0ℓ
•-ε-monoid = record { isMonoid = •-ε-isMonoid }

------------------------------------------------------------------------
-- Associativity solver
--
-- Converts a word to a flat list of generators, then compares the lists
-- to decide associativity.

to-list : ∀ {X} → Word X → List X
to-list [ x ]ʷ  = x ∷ []
to-list ε        = []
to-list (w • w₁) = to-list w ++ to-list w₁

from-list : ∀ {X} → List X → Word X
from-list []       = ε
from-list (x ∷ xs) = [ x ]ʷ • from-list xs

from-list-homo : ∀ {X} {R : WRel X} (xs ys : List X) →
  let open PB R renaming (_≈_ to _≈₁_) in
  from-list (xs ++ ys) ≈₁ from-list xs • from-list ys
from-list-homo {R = R} [] ys = _≈₁_.sym _≈₁_.left-unit
  where open PB R renaming (_≈_ to _≈₁_)
from-list-homo {R = R} (x ∷ xs) ys =
    _≈₁_.trans
      (_≈₁_.cong _≈₁_.refl (from-list-homo xs ys))
      (_≈₁_.sym _≈₁_.assoc)
  where open PB R renaming (_≈_ to _≈₁_)

lemma-from-to : ∀ {w} → from-list (to-list w) ≈ w
lemma-from-to {[ x ]ʷ}  = right-unit
lemma-from-to {ε}        = refl
lemma-from-to {w • w₁}  with lemma-from-to {w} | lemma-from-to {w₁}
... | ih1 | ih2 = trans (from-list-homo (to-list w) (to-list w₁)) (cong ih1 ih2)

mod-assoc : ∀ w → Word X
mod-assoc w = from-list (to-list w)

by-assoc : ∀ {w} {v} → to-list w ≡ to-list v → w ≈ v
by-assoc {w} {v} eq =
  trans (sym lemma-from-to) (trans (refl' (Eq.cong from-list eq)) lemma-from-to)

by-assoc-and : ∀ {w} {v} {a} {b} →
  a ≈ b → to-list w ≡ to-list a → to-list b ≡ to-list v → w ≈ v
by-assoc-and {w} {v} {a} {b} eq eq1 eq2 =
  trans (by-assoc eq1) (trans eq (by-assoc eq2))

-- Translate w₁ • w₂ • … • wₙ to the list [w₁, w₂, …, wₙ] without
-- flattening inner words.
to-list2 : ∀ {X} → Word X → List (Word X)
to-list2 ([ x ]ʷ) = [ x ]ʷ ∷ []
to-list2 ε         = ε ∷ []
to-list2 (u • w)   = u ∷ to-list2 w

from-list2 : ∀ {X} → List (Word X) → Word X
from-list2 []           = ε
from-list2 (u ∷ [])     = u
from-list2 (u ∷ v ∷ us) = u • from-list2 (v ∷ us)

lemma-from-to2 : ∀ {X} → (u : Word X) → from-list2 (to-list2 u) ≡ u
lemma-from-to2 ([ x ]ʷ)   = Eq.refl
lemma-from-to2 ε            = Eq.refl
lemma-from-to2 (u • [ x ]ʷ) = Eq.refl
lemma-from-to2 (u • ε)     = Eq.refl
lemma-from-to2 (u • (w • v)) = Eq.cong (λ □ → u • □) (lemma-from-to2 (w • v))

split : ∀ {l} {X : Set l} → ℕ → List X → List X × List X
split n       []       = [] , []
split zero    (x ∷ xs) = [] , x ∷ xs
split (₁₊ n) (x ∷ xs) with split n xs
... | xs1 , xs2 = x ∷ xs1 , xs2

lemma-split : ∀ {l} {X : Set l} → (n : ℕ) → (xs : List X) →
  ∀ {ys zs} → split n xs ≡ (ys , zs) → ys ++ zs ≡ xs
lemma-split n       []       Eq.refl = Eq.refl
lemma-split zero    (x ∷ xs) Eq.refl = Eq.refl
lemma-split (₁₊ n) (x ∷ xs) eq with split n xs | lemma-split n xs
lemma-split (₁₊ n) (x ∷ xs) Eq.refl | xs1 , xs2 | ih =
  begin (x ∷ xs1) ++ xs2
      ≡⟨ Eq.refl ⟩
    x ∷ (xs1 ++ xs2)
      ≡⟨ Eq.cong (λ □ → x ∷ □) (ih Eq.refl) ⟩
    x ∷ xs ∎
  where open Eq.≡-Reasoning

split3 : ∀ {l} {X : Set l} → ℕ → ℕ → List X → List X × List X × List X
split3 n m xs with split n xs
... | x , ys with split m ys
... | y , z = x , y , z

lemma-split3 : ∀ {l} {X : Set l} → (n m : ℕ) → (xs : List X) →
  ∀ {x y z} → split3 n m xs ≡ (x , y , z) → x ++ y ++ z ≡ xs
lemma-split3 n m xs hyp with split n xs | Eq.inspect (split n) xs
lemma-split3 n m xs hyp | x , ys | Eq.[ eq1 ] with split m ys | Eq.inspect (split m) ys
lemma-split3 n m xs Eq.refl | x , ys | Eq.[ eq1 ] | y , z | Eq.[ eq2 ] =
  begin x ++ y ++ z
      ≡⟨ Eq.cong (λ □ → x ++ □) hyp2 ⟩
    x ++ ys
      ≡⟨ hyp1 ⟩
    xs ∎
  where
    open Eq.≡-Reasoning
    hyp1 : x ++ ys ≡ xs
    hyp1 = lemma-split n xs eq1
    hyp2 : y ++ z ≡ ys
    hyp2 = lemma-split m ys eq2

mysplit : ∀ {X : Set} → ℕ → ℕ → List (Word X) → List X × Word X × List X
mysplit n m us with split3 n m us
... | xs , ys , zs = to-list (from-list2 xs) , from-list2 ys , to-list (from-list2 zs)

lemma-append2 : ∀ (us ws : List (Word X)) →
  from-list2 us • from-list2 ws ≈ from-list2 (us ++ ws)
lemma-append2 []           ws = left-unit
lemma-append2 (u ∷ [])     [] = right-unit
lemma-append2 (u ∷ [])     (w ∷ ws) = refl
lemma-append2 (u ∷ u' ∷ us) ws =
  begin (u • from-list2 (u' ∷ us)) • from-list2 ws
      ≈⟨ assoc ⟩
    u • (from-list2 (u' ∷ us) • from-list2 ws)
      ≈⟨ cright lemma-append2 (u' ∷ us) ws ⟩
    u • from-list2 (u' ∷ (us ++ ws)) ∎
  where open SR word-setoid

lemma-mysplit : ∀ n m us {x y z} →
  mysplit n m us ≡ (x , y , z) →
  from-list x • y • from-list z ≈ from-list2 us
lemma-mysplit n m us {x} {y} {z} hyp with split3 n m us | Eq.inspect (split3 n m) us
... | xs , ys , zs | Eq.[ eq ]
  rewrite Eq.cong proj₁ eq
        | Eq.cong proj₁ (Eq.cong proj₂ eq)
        | Eq.cong proj₂ (Eq.cong proj₂ eq) =
  let hyp1 = Eq.cong proj₁ hyp
      hyp2 = Eq.cong proj₁ (Eq.cong proj₂ hyp)
      hyp3 = Eq.cong proj₂ (Eq.cong proj₂ hyp)
  in
  begin from-list x • y • from-list z
      ≈⟨ cleft refl' (Eq.cong from-list hyp1) reversed ⟩
    from-list (to-list (from-list2 xs)) • y • from-list z
      ≈⟨ cleft lemma-from-to {from-list2 xs} ⟩
    from-list2 xs • y • from-list z
      ≈⟨ cright cright refl' (Eq.cong from-list hyp3) reversed ⟩
    from-list2 xs • y • from-list (to-list (from-list2 zs))
      ≈⟨ cright cright lemma-from-to {from-list2 zs} ⟩
    from-list2 xs • y • from-list2 zs
      ≈⟨ cright cleft refl' hyp2 reversed ⟩
    from-list2 xs • from-list2 ys • from-list2 zs
      ≈⟨ cright lemma-append2 ys zs ⟩
    from-list2 xs • from-list2 (ys ++ zs)
      ≈⟨ lemma-append2 xs (ys ++ zs) ⟩
    from-list2 (xs ++ ys ++ zs)
      ≈⟨ refl' (Eq.cong from-list2 (lemma-split3 n m us eq)) ⟩
    from-list2 us ∎
  where open SR word-setoid

------------------------------------------------------------------------
-- Pattern-guided associativity solver

module Pattern-Assoc where

  open import Data.Unit
  import Relation.Binary.Reasoning.Setoid as SR

  -- Placeholder symbol for use in pattern words, e.g. (□ • □) • □.
  □ : Word ⊤
  □ = [ tt ]ʷ

  -- Like to-list, but guided by a pattern word: subwords at positions
  -- marked by □ are kept intact without further flattening.
  to-list-special : ∀ {X} → Word X → Word ⊤ → List (Word X)
  to-list-special w         ([ gen ]ʷ) = w ∷ []
  to-list-special ([ x ]ʷ) ε          = [ x ]ʷ ∷ []
  to-list-special ([ x ]ʷ) (p • q)    = [ x ]ʷ ∷ []
  to-list-special ε         ε          = []
  to-list-special ε         (p • q)    = []
  to-list-special (w • v)   ε          = to-list-special w ε ++ to-list-special v ε
  to-list-special (w • v)   (p • q)    = to-list-special w p ++ to-list-special v q

  flatten-word : ∀ {X} → Word (Word X) → Word X
  flatten-word ([ w ]ʷ) = w
  flatten-word ε         = ε
  flatten-word (w • v)   = flatten-word w • flatten-word v

  data ∅ {X : Set} : WRel X where

  lemma-flatten-word : ∀ {xs ys : Word (Word X)} →
    let open PB (∅ {Word X}) renaming (_≈_ to _≈₀_) in
    xs ≈₀ ys → flatten-word xs ≈ flatten-word ys
  lemma-flatten-word (axiom ())
  lemma-flatten-word refl           = refl
  lemma-flatten-word (sym hyp)      = sym (lemma-flatten-word hyp)
  lemma-flatten-word (trans hyp h₁) = trans (lemma-flatten-word hyp) (lemma-flatten-word h₁)
  lemma-flatten-word (cong hyp h₁)  = cong (lemma-flatten-word hyp) (lemma-flatten-word h₁)
  lemma-flatten-word assoc           = assoc
  lemma-flatten-word left-unit       = left-unit
  lemma-flatten-word right-unit      = right-unit

  lemma-to-list-special : ∀ (w : Word X) (p : Word ⊤) →
    flatten-word (from-list (to-list-special w p)) ≈ w
  lemma-to-list-special w         ([ gen ]ʷ) = right-unit
  lemma-to-list-special ([ x ]ʷ) ε          = right-unit
  lemma-to-list-special ([ x ]ʷ) (p • q)    = right-unit
  lemma-to-list-special ε         ε          = refl
  lemma-to-list-special ε         (p • q)    = refl
  lemma-to-list-special (w • v)   ε =
    begin flatten-word (from-list (to-list-special w ε ++ to-list-special v ε))
        ≈⟨ lemma-flatten-word (from-list-homo (to-list-special w ε) (to-list-special v ε)) ⟩
      flatten-word (from-list (to-list-special w ε) • from-list (to-list-special v ε))
        ≈⟨ refl ⟩
      flatten-word (from-list (to-list-special w ε)) • flatten-word (from-list (to-list-special v ε))
        ≈⟨ cong (lemma-to-list-special w ε) (lemma-to-list-special v ε) ⟩
      w • v ∎
    where open SR word-setoid
  lemma-to-list-special (w • v) (p • q) =
    begin flatten-word (from-list (to-list-special w p ++ to-list-special v q))
        ≈⟨ lemma-flatten-word (from-list-homo (to-list-special w p) (to-list-special v q)) ⟩
      flatten-word (from-list (to-list-special w p) • from-list (to-list-special v q))
        ≈⟨ refl ⟩
      flatten-word (from-list (to-list-special w p)) • flatten-word (from-list (to-list-special v q))
        ≈⟨ cong (lemma-to-list-special w p) (lemma-to-list-special v q) ⟩
      w • v ∎
    where open SR word-setoid

  -- Prove w ≈ v by giving matching pattern words p and q such that
  -- to-list-special w p ≡ to-list-special v q (checked by refl).
  --
  -- Example: to prove (a • b) • (c • d) ≈ a • (b • c) • d, write
  --   special-assoc ((□ • □) • (□ • □)) (□ • (□ • □) • □) refl
  special-assoc : ∀ {w v : Word X} (p q : Word ⊤) →
    to-list-special w p ≡ to-list-special v q → w ≈ v
  special-assoc {w = w} {v = v} p q hyp =
    begin w
        ≈⟨ sym (lemma-to-list-special w p) ⟩
      flatten-word (from-list (to-list-special w p))
        ≈⟨ refl' (Eq.cong (λ □ → flatten-word (from-list □)) hyp) ⟩
      flatten-word (from-list (to-list-special v q))
        ≈⟨ lemma-to-list-special v q ⟩
      v ∎
    where open SR word-setoid

------------------------------------------------------------------------
-- Word power lemmas

word-comm : ∀ {w} {v} a b →
  w • v ≈ v • w → w ^ a • v ^ b ≈ v ^ b • w ^ a
word-comm {w} {v} zero    zero    eq = refl
word-comm {w} {v} zero    (₁₊ b) eq = trans left-unit (sym right-unit)
word-comm {w} {v} (₁₊ a) zero    eq = trans right-unit (sym left-unit)
word-comm {w} {v} (₁₊ zero) (₁₊ b@(₁₊ b')) eq =
  begin w • v ^ ₁₊ b       ≈⟨ sym assoc ⟩
    (w • v) • v ^ b          ≈⟨ cong eq refl ⟩
    (v • w) • v ^ b          ≈⟨ assoc ⟩
    v • w • v ^ b            ≈⟨ cong refl (word-comm 1 b eq) ⟩
    v • v ^ b • w            ≈⟨ sym assoc ⟩
    v ^ ₁₊ b • w ∎
  where open SR word-setoid
word-comm {w} {v} (₁₊ a@(₁₊ a')) (₁₊ zero) eq =
  begin (w • w ^ ₁₊ a') • v  ≈⟨ assoc ⟩
    w • w ^ ₁₊ a' • v         ≈⟨ cong refl (word-comm a 1 eq) ⟩
    w • v • w ^ ₁₊ a'         ≈⟨ sym assoc ⟩
    (w • v) • w ^ ₁₊ a'       ≈⟨ cong eq refl ⟩
    (v • w) • w ^ ₁₊ a'       ≈⟨ assoc ⟩
    v • w • w ^ ₁₊ a' ∎
  where open SR word-setoid
word-comm (₁₊ zero)       (₁₊ zero)       eq = eq
word-comm {w} {v} (₂₊ a) (₂₊ b) eq =
  begin w ^ ₂₊ a • v ^ ₂₊ b
      ≈⟨ special-assoc ((□ • □) • □ • □) (□ • (□ • □) • □) Eq.refl ⟩
    w • (w ^ (₁₊ a) • v) • v ^ (₁₊ b)
      ≈⟨ cong refl (cong (word-comm (₁₊ a) 1 eq) refl) ⟩
    w • (v • w ^ (₁₊ a)) • v ^ (₁₊ b)
      ≈⟨ special-assoc (□ • (□ • □) • □) (□ ^ 2 • □ ^ 2) Eq.refl ⟩
    (w • v) • (w ^ (₁₊ a) • v ^ (₁₊ b))
      ≈⟨ cong eq (word-comm (₁₊ a) (₁₊ b) eq) ⟩
    (v • w) • (v ^ (₁₊ b) • w ^ (₁₊ a))
      ≈⟨ special-assoc (□ ^ 2 • □ ^ 2) (□ • □ ^ 2 • □) Eq.refl ⟩
    v • (w • v ^ (₁₊ b)) • w ^ (₁₊ a)
      ≈⟨ cong refl (cong (word-comm 1 (₁₊ b) eq) refl) ⟩
    v • (v ^ (₁₊ b) • w) • w ^ (₁₊ a)
      ≈⟨ special-assoc (□ • □ ^ 2 • □) (□ ^ 2 • □ ^ 2) Eq.refl ⟩
    v ^ ₂₊ b • w ^ ₂₊ a ∎
  where
    open SR word-setoid
    open Pattern-Assoc

^'=^ : {n : ℕ} {w : Word X} → w ^' n ≈ w ^ n
^'=^ {zero}           {w} = refl
^'=^ {₁₊ zero}       {w} = refl
^'=^ {₂₊ zero} {w} = refl
^'=^ {₃₊ n} {w} =
  begin ((w ^' ₁₊ n) • w) • w   ≈⟨ cong (^'=^ {n = ₂₊ n}) refl ⟩
    (w • (w ^ ₁₊ n)) • w         ≈⟨ assoc ⟩
    w • (w ^ ₁₊ n) • w           ≈⟨ cong refl (cong (sym (^'=^ {n = ₁₊ n})) refl) ⟩
    w • (w ^' ₁₊ n) • w          ≈⟨ cong refl (^'=^ {n = ₂₊ n}) ⟩
    w • (w • (w ^ ₁₊ n)) ∎
  where open Eqv word-setoid

lemma-^-suc : ∀ (w : Word X) a → w ^ ₁₊ a ≈ w • w ^ a
lemma-^-suc w zero    = sym right-unit
lemma-^-suc w (₁₊ a) = refl

lemma-^-+ : ∀ (w : Word X) a b → w ^ (a Nat.+ b) ≈ w ^ a • w ^ b
lemma-^-+ w zero          b       = sym left-unit
lemma-^-+ w (₁₊ zero)    zero    = sym right-unit
lemma-^-+ w (₁₊ zero)    (₁₊ b) = refl
lemma-^-+ w (₂₊ a) b =
  begin w ^ suc (₁₊ a Nat.+ b)        ≈⟨ refl ⟩
    w • w ^ (₁₊ a Nat.+ b)             ≈⟨ cong refl (lemma-^-+ w (₁₊ a) b) ⟩
    w • w ^ ₁₊ a • w ^ b              ≈⟨ sym assoc ⟩
    w ^ ₂₊ a • w ^ b ∎
  where open Eqv word-setoid

lemma-^-• : ∀ (w v : Word X) a → w • v ≈ v • w → (w • v) ^ a ≈ w ^ a • v ^ a
lemma-^-• w v zero    eq = sym left-unit
lemma-^-• w v (₁₊ zero) eq = refl
lemma-^-• w v (₂₊ a) eq =
  begin (w • v) • (w • v) ^ ₁₊ a
      ≈⟨ cong refl (lemma-^-• w v (₁₊ a) eq) ⟩
    (w • v) • w ^ ₁₊ a • v ^ ₁₊ a
      ≈⟨ sym assoc ⟩
    ((w • v) • w ^ ₁₊ a) • v ^ ₁₊ a
      ≈⟨ cong assoc refl ⟩
    (w • (v • w ^ ₁₊ a)) • v ^ ₁₊ a
      ≈⟨ cong (cong refl (word-comm 1 (₁₊ a) (sym eq))) refl ⟩
    (w • (w ^ ₁₊ a • v)) • v ^ ₁₊ a
      ≈⟨ sym (cong assoc refl) ⟩
    ((w • w ^ ₁₊ a) • v) • v ^ ₁₊ a
      ≈⟨ assoc ⟩
    (w • w ^ ₁₊ a) • v • v ^ ₁₊ a ∎
  where open Eqv word-setoid

lemma-comm-wᵃwᵇ : ∀ (w : Word X) a b → w ^ a • w ^ b ≈ w ^ b • w ^ a
lemma-comm-wᵃwᵇ w zero    zero    = refl
lemma-comm-wᵃwᵇ w zero    (₁₊ b) = trans left-unit (sym right-unit)
lemma-comm-wᵃwᵇ w (₁₊ a) zero    = trans right-unit (sym left-unit)
lemma-comm-wᵃwᵇ w (₁₊ zero) (₁₊ zero) = refl
lemma-comm-wᵃwᵇ w (₁₊ zero) (₂₊ b) =
  begin w • w • w ^ ₁₊ b                ≈⟨ cong refl (lemma-comm-wᵃwᵇ w 1 (₁₊ b)) ⟩
    w • w ^ ₁₊ b • w                     ≈⟨ sym assoc ⟩
    (w • w ^ ₁₊ b) • w ∎
  where open Eqv word-setoid
lemma-comm-wᵃwᵇ w (₂₊ a) (₁₊ zero) =
  begin (w • w ^ ₁₊ a) • w              ≈⟨ assoc ⟩
    w • w ^ ₁₊ a • w                     ≈⟨ cong refl (lemma-comm-wᵃwᵇ w (₁₊ a) 1) ⟩
    w • w • w ^ ₁₊ a ∎
  where open Eqv word-setoid
lemma-comm-wᵃwᵇ w (₂₊ a) (₂₊ b) =
  begin (w • w ^ ₁₊ a) • w • w ^ ₁₊ b
      ≈⟨ sym assoc ⟩
    ((w • w ^ ₁₊ a) • w) • w ^ ₁₊ b
      ≈⟨ cong assoc refl ⟩
    (w • w ^ ₁₊ a • w) • w ^ ₁₊ b
      ≈⟨ cong (cong refl (lemma-comm-wᵃwᵇ w (₁₊ a) 1)) refl ⟩
    (w • w • w ^ ₁₊ a) • w ^ ₁₊ b
      ≈⟨ assoc ⟩
    w • (w • w ^ ₁₊ a) • w ^ ₁₊ b
      ≈⟨ cong refl assoc ⟩
    w • w • w ^ ₁₊ a • w ^ ₁₊ b
      ≈⟨ cong refl (cong refl (lemma-comm-wᵃwᵇ w (₁₊ a) (₁₊ b))) ⟩
    w • w • w ^ ₁₊ b • w ^ ₁₊ a
      ≈⟨ cong refl (sym assoc) ⟩
    w • (w • w ^ ₁₊ b) • w ^ ₁₊ a
      ≈⟨ cong refl (cong (lemma-comm-wᵃwᵇ w 1 (₁₊ b)) refl) ⟩
    w • (w ^ ₁₊ b • w) • w ^ ₁₊ a
      ≈⟨ sym assoc ⟩
    (w • (w ^ ₁₊ b • w)) • w ^ ₁₊ a
      ≈⟨ sym (cong assoc refl) ⟩
    ((w • w ^ ₁₊ b) • w) • w ^ ₁₊ a
      ≈⟨ assoc ⟩
    (w • w ^ ₁₊ b) • w • w ^ ₁₊ a ∎
  where open Eqv word-setoid

lemma-^^ : ∀ (w : Word X) a b → (w ^ a) ^ b ≈ w ^ (a Nat.* b)
lemma-^^ w zero    zero    = refl
lemma-^^ w zero    (₁₊ zero) = PB.refl
lemma-^^ w zero    (₂₊ b) = trans left-unit (lemma-^^ w zero (₁₊ b))
lemma-^^ w (₁₊ zero) b = refl' (Eq.cong (w ^_) (Eq.sym (NP.+-identityʳ b)))
lemma-^^ w (₂₊ a) b =
  begin (w • w ^ ₁₊ a) ^ b
      ≈⟨ lemma-^-• w (w ^ ₁₊ a) b (lemma-comm-wᵃwᵇ w 1 (₁₊ a)) ⟩
    w ^ b • (w ^ ₁₊ a) ^ b
      ≈⟨ cong refl (lemma-^^ w (₁₊ a) b) ⟩
    w ^ b • w ^ (₁₊ a Nat.* b)
      ≈⟨ sym (lemma-^-+ w b (₁₊ a Nat.* b)) ⟩
    w ^ (b Nat.+ (b Nat.+ a Nat.* b)) ∎
  where open Eqv word-setoid

lemma-^^' : ∀ (w : Word X) a b → (w ^ a) ^ b ≈ (w ^ b) ^ a
lemma-^^' w a b =
  begin (w ^ a) ^ b     ≈⟨ lemma-^^ w a b ⟩
    w ^ (a Nat.* b)     ≡⟨ Eq.cong (w ^_) (NP.*-comm a b) ⟩
    w ^ (b Nat.* a)     ≈⟨ sym (lemma-^^ w b a) ⟩
    (w ^ b) ^ a ∎
  where open Eqv word-setoid

lemma-^-cong : ∀ (w v : Word X) a → w ≈ v → w ^ a ≈ v ^ a
lemma-^-cong w v 0         eq = refl
lemma-^-cong w v 1         eq = eq
lemma-^-cong w v (₂₊ a) eq =
  begin w ^ ₂₊ a   ≈⟨ refl ⟩
    w • w ^ ₁₊ a          ≈⟨ cong eq (lemma-^-cong w v (₁₊ a) eq) ⟩
    v • v ^ ₁₊ a          ≈⟨ refl ⟩
    v ^ ₂₊ a ∎
  where open Eqv word-setoid

lemma-ε^k=ε : ∀ k → ε ^ k ≈ ε
lemma-ε^k=ε zero        = refl
lemma-ε^k=ε (₁₊ zero)  = refl
lemma-ε^k=ε (₂₊ k) = trans left-unit (lemma-ε^k=ε (₁₊ k))

------------------------------------------------------------------------
-- Congruence lemmas for wfoldr / wfoldl / _⋆⋆

lemma-wfoldr :
  {X Y : Set} {_⊕_ : X → Y → Y} (R : Y → Y → Set) →
  (hyp : (a : X) → ∀ {b1 b2} → R b1 b2 → R (a ⊕ b1) (a ⊕ b2)) →
  ∀ (w : Word X) → ∀ {b1 b2} → R b1 b2 →
  let _⊕'_ = wfoldr _⊕_ in R (w ⊕' b1) (w ⊕' b2)
lemma-wfoldr R hyp [ x ]ʷ  eq = hyp x eq
lemma-wfoldr R hyp ε        eq = eq
lemma-wfoldr {_⊕_ = _⊕_} R hyp (w • w₁) eq
  with lemma-wfoldr R hyp w₁ eq
... | ih with (let _⊕'_ = wfoldr _⊕_ in lemma-wfoldr R hyp w {w₁ ⊕' _} {w₁ ⊕' _})
... | ih2 = ih2 ih

lemma-wfoldl :
  {X Y : Set} {_⊕_ : Y → X → Y} (R : Y → Y → Set) →
  (hyp : (a : X) → ∀ {b1 b2} → R b1 b2 → R (b1 ⊕ a) (b2 ⊕ a)) →
  ∀ (w : Word X) → ∀ {b1 b2} → R b1 b2 →
  let _⊕'_ = wfoldl _⊕_ in R (b1 ⊕' w) (b2 ⊕' w)
lemma-wfoldl R hyp [ x ]ʷ  eq = hyp x eq
lemma-wfoldl R hyp ε        eq = eq
lemma-wfoldl {_⊕_ = _⊕_} R hyp (w • w₁) eq
  with lemma-wfoldl R hyp w eq
... | ih with (let _⊕'_ = wfoldl _⊕_ in lemma-wfoldl R hyp w₁ {_ ⊕' w} {_ ⊕' w})
... | ih2 = ih2 ih

lemma-⋆⋆ :
  {Y X C : Set} {_⊕_ : C → Y → Word X × C}
  (RX : Word X → Word X → Set)
  (RC : C → C → Set) →
  let R = PW.Pointwise RX RC in
  (rx-cong : ∀ {w v w' v'} → RX w w' → RX v v' → RX (w • v) (w' • v')) →
  (rx-ε : RX ε ε) →
  (hyp : (y : Y) → ∀ {c1 c2} → RC c1 c2 → R (c1 ⊕ y) (c2 ⊕ y)) →
  ∀ (w : Word Y) → ∀ {c1 c2} → RC c1 c2 →
  let _⊕'_ = _⊕_ ⋆⋆ in R (c1 ⊕' w) (c2 ⊕' w)
lemma-⋆⋆ {Y} {X} {C} {_⊕_} RX RC rx-cong rx-ε hyp w {c1} {c2} r = fact1
  where
    R = PW.Pointwise RX RC

    _⊕'_ : Word X × C → Y → Word X × C
    _⊕'_ (w , c) y with c ⊕ y
    ... | v , c' = w • v , c'

    _⊕''_ = wfoldl _⊕'_

    hyp' : ∀ (y : Y) → ∀ {xc1 xc2} → R xc1 xc2 → R (xc1 ⊕' y) (xc2 ⊕' y)
    hyp' y {x1 , c1} {x2 , c2} (rx , rc) =
      rx-cong rx (hyp y rc .proj₁) , hyp y rc .proj₂

    r' : R (ε , c1) (ε , c2)
    r' = rx-ε , r

    fact : ∀ (w : Word Y) → ∀ {xc1 xc2} → R xc1 xc2 → R (xc1 ⊕'' w) (xc2 ⊕'' w)
    fact = lemma-wfoldl {_⊕_ = _⊕'_} R hyp'

    fact1 = fact w r'

------------------------------------------------------------------------
-- Normal-form witnesses

private
  variable
    w v : Word X

-- A normal-form function: maps each word to a canonical representative.
record NFProperty : Set₁ where
  field
    NF           : Set
    nf           : Word X → NF
    nf-cong      : w ≈ v → nf w ≡ nf v
    nf-injective : nf w ≡ nf v → w ≈ v

  by-equal-nf : nf w ≡ nf v → w ≈ v
  by-equal-nf = nf-injective

  nf-injection : Injection word-setoid (setoid NF)
  nf-injection = record { to = nf ; cong = nf-cong ; injective = nf-injective }

  dec-word : DecidableEquality NF → Decidable _≈_
  dec-word deceq = via-injection nf-injection deceq

-- Like NFProperty, but the normal-form function has a section.
record NFProperty' : Set₁ where
  field
    NF           : Set
    nf           : Word X → NF
    nf-cong      : w ≈ v → nf w ≡ nf v
    inv-nf       : NF → Word X
    inv-nf∘nf=id : inv-nf (nf w) ≈ w

  nf-injective : nf w ≡ nf v → w ≈ v
  nf-injective x =
    trans (sym inv-nf∘nf=id) (trans (refl' (Eq.cong inv-nf x)) inv-nf∘nf=id)

  hasNFProperty : NFProperty
  hasNFProperty = record
    { NF = NF ; nf = nf ; nf-cong = nf-cong ; nf-injective = nf-injective }

  open NFProperty hasNFProperty using (by-equal-nf) public

-- Like NFProperty but also surjective: every normal form is realised.
record SNFProperty : Set₁ where
  field
    NF            : Set
    nf            : Word X → NF
    nf-cong       : w ≈ v → nf w ≡ nf v
    nf-injective  : nf w ≡ nf v → w ≈ v
    nf-surjective : ∀ y → ∃ λ w → ∀ {v} → v ≈ w → nf v ≡ y

  inv-nf : NF → Word X
  inv-nf y = nf-surjective y .proj₁

  inv-nf∘nf=id : ∀ {w} → inv-nf (nf w) ≈ w
  inv-nf∘nf=id {w} with nf-surjective (nf w)
  ... | w' , hyp = nf-injective (hyp refl)

  hasNFProperty' : NFProperty'
  hasNFProperty' = record
    { NF = NF ; nf = nf ; nf-cong = nf-cong
    ; inv-nf = inv-nf ; inv-nf∘nf=id = inv-nf∘nf=id
    }

  open NFProperty' hasNFProperty'

-- A weaker normal-form witness: no canonicity, only injectivity.
record AlmostNFProperty : Set₁ where
  field
    ANF          : Set
    anf          : Word X → ANF
    anf-injective : anf w ≡ anf v → w ≈ v

  by-equal-anf : anf w ≡ anf v → w ≈ v
  by-equal-anf = anf-injective
