------------------------------------------------------------------------
-- Presentations of groups
--
-- Cyclic groups Z/NZ and their normal form
------------------------------------------------------------------------

{-# OPTIONS --safe #-}

open import Level using (0ℓ)

open import Relation.Binary.PropositionalEquality using (_≡_ ; inspect ; module ≡-Reasoning) renaming ([_] to [_]')
import Relation.Binary.Reasoning.Setoid as SR
import Relation.Binary.PropositionalEquality as Eq
open import Relation.Nullary.Decidable using (yes ; no)


open import Function using (_∘_ ; id)

open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂ ; map₁)
open import Data.Product.Relation.Binary.Pointwise.NonDependent using (≡×≡⇒≡ ; Pointwise ; ≡⇒≡×≡)
open import Data.Nat using (ℕ ; zero ; suc)
import Data.Nat as Nat
open import Data.Fin
open import Data.Fin.Induction
open import Data.Sum using (_⊎_)
open import Data.Unit using (⊤ ; tt)
open import Data.Empty using (⊥ ; ⊥-elim)

open import Word.Base hiding (wfoldl)
open import Word.Properties
import Presentation.Base as PB
import Presentation.Properties as PP
open PP using (NFProperty ; NFProperty')
import Presentation.CosetNF as CA
import Presentation.Reidemeister-Schreier as RS
open import Data.Fin.Properties using (suc-injective ; toℕ-inject₁ ; toℕ-fromℕ)
import Data.Nat.Properties as NP
open import Notations


module Presentation.Groups.Cyclic where

-- a generator of the cyclic group is tt, i.e., the generating set
-- is a singleton.
X = ⊤

-- a particular word.
T : Word X
T = [ tt ]ʷ

-- there is only one order relation for a cyclic group. rel is index
-- by the order of the cyclic group.
data rel (N : ℕ) : WRel X where
  order :  rel N (T ^' N) ε

-- 0-th cyclic monoid is ℕ. The rest are iso to the additative group
-- of the integers modulo N ring.
pres : ℕ → WRel X
pres N = rel N

-- successor modulo N.
sucN : ∀ {N} → Fin N → Fin N
sucN {₁₊ zero} zero = zero
sucN {₂₊ N} zero = ₁₊ zero
sucN {₂₊ N} (₁₊ f) with sucN {₁₊ N} f
... | zero = zero
... | ₁₊ ih = ₂₊ ih

-- successor function is injective.
sucN-inj : ∀ {N} a b → sucN {N} a ≡ sucN b → a ≡ b
sucN-inj {₁₊ zero} zero zero eq = eq
sucN-inj {₂₊ N} zero zero eq = Eq.refl
sucN-inj {₂₊ N} zero (₁₊ b) eq with sucN b
sucN-inj {₁₊ N} zero (₁₊ b) () | zero
sucN-inj {₁₊ N} zero (₁₊ b) () | ₁₊ h
sucN-inj {₂₊ N} (₁₊ a) zero eq with sucN a
sucN-inj {₁₊ N} (₁₊ a) zero () | zero
sucN-inj {₁₊ N} (₁₊ a) zero () | ₁₊ h
sucN-inj {₂₊ N} (₁₊ a) (₁₊ b) eq with sucN a | sucN b | inspect sucN a | inspect sucN b
... | zero | zero | [ eqa ]' | [ eqb ]' = Eq.cong suc (sucN-inj a b (Eq.trans eqa (Eq.sym eqb)))
sucN-inj {₁₊ N} (₁₊ a) (₁₊ b) Eq.refl | ₁₊ ha | ₁₊ hb | [ eqa ]' | [ eqb ]' = Eq.cong suc (sucN-inj a b (Eq.trans eqa (Eq.sym eqb)))


-- predecessor fuction is the inverse of sucN.
predN : ∀ {N} → Fin N → Fin N
predN {₁₊ zero} zero = zero
predN {₂₊ N} zero = suc (predN {₁₊ N} zero)
predN {₂₊ N} (₁₊ f) = inject₁ f

aux-inject₁ : ∀ {N} x → sucN {₁₊ N} (inject₁ x) ≡ ₁₊ x
aux-inject₁ {₁₊ zero} zero = Eq.refl
aux-inject₁ {₂₊ N} zero = Eq.refl
aux-inject₁ {₂₊ N} (₁₊ x) with aux-inject₁ {₁₊ N} x
... | ih rewrite ih = Eq.refl

lemma-suc-pred : ∀ {N} (x : Fin N) → sucN (predN x) ≡ x
lemma-suc-pred {₁₊ zero} zero = Eq.refl
lemma-suc-pred {₂₊ N} zero with lemma-suc-pred {₁₊ N} zero
... | ih rewrite ih = Eq.refl
lemma-suc-pred {₂₊ N} (₁₊ x) = aux-inject₁ x

-- 0-th Normal Form set NF is ℕ. order N cyclic group has normal
-- form set Fin N.
NF : ℕ → Set
NF zero = ℕ
NF (₁₊ N) = Fin (₁₊ N)

succ : ∀ {N} → NF N → NF N
succ {zero} = suc
succ {₁₊ N} = sucN


z : ∀ {N} → NF N
z {zero} = zero
z {₁₊ N} = zero

[_] : ∀ {N} → NF N → Word X
[_] {zero} nf = T ^' nf
[_] {₁₊ N} nf = T ^' toℕ nf

[z]=ε : ∀ {N} → [_] {N} z ≡ ε
[z]=ε {zero} = Eq.refl
[z]=ε {₁₊ N} = Eq.refl


--   wfoldl : ∀ {N} (NF N → X → NF N) → (NF N → Word X → NF N)
-->  wfoldl : ∀ {N} (Word ⊥ × C N → X → Word ⊥ × C N) → (Word ⊥ × C N → Word X → Word ⊥ × C N)
-->  wfoldl : ∀ {N} → (C N → X → C N) → (C N → Word X → C N)
-->  wfoldl : ∀ {N} → (C N → C N) → (C N → Word X → C N)
-->  wfoldl : ∀ {N} → (NF N → NF N) → (NF N → Word X → NF N)

wfoldl : ∀ {N} → (NF N → NF N) → (NF N → Word X → NF N)
wfoldl {N} succ c [ x ]ʷ = succ c
wfoldl {N} succ c ε = c
wfoldl {N} succ c (w • w₁) = wfoldl {N} succ (wfoldl {N} succ c w) w₁

f : ∀ {N} → Word X → NF N
f {N} = wfoldl {N} succ z

lemma-wfoldl : ∀ {N} → let _≈_ = PB._≈_ (pres N) in
  ∀ (succ : NF N → NF N)
    (lemma-succ :  ∀ c → ([ c ] • T) ≈ [ succ c ])
    (c : NF N) (w : Word X)
    →
    [ wfoldl succ c w ] ≈ ([ c ] • w)
lemma-wfoldl {N} succ lemma-succ c [ x ]ʷ = PB._≈_.sym (lemma-succ c)
lemma-wfoldl {N} succ lemma-succ c ε = PB._≈_.sym PB._≈_.right-unit
lemma-wfoldl {N} succ lemma-succ c (w • v) = _≈_.sym claim
  where
  open PB (pres N)
  open PP (pres N) hiding (lemma-wfoldl)
  open SR word-setoid  

  claim : [ c ] • (w • v) ≈ [ wfoldl succ c (w • v) ]
  claim = begin
    [ c ] • (w • v) ≈⟨ sym assoc ⟩
    ([ c ] • w) • v ≈⟨ cong (sym (lemma-wfoldl {N} succ lemma-succ c w)) refl ⟩
    ([ wfoldl succ c w ]) • v ≈⟨ sym (lemma-wfoldl {N} succ lemma-succ (wfoldl succ c w) v) ⟩
    [ wfoldl succ (wfoldl succ c w) v ] ≈⟨ _≈_.refl ⟩
    [ wfoldl succ c (w • v) ] ∎

lemma-wfoldl-succ : ∀ {N} (c : Fin (₁₊ N)) w → wfoldl succ (succ c) w ≡ succ (wfoldl succ c w)
lemma-wfoldl-succ c [ x ]ʷ = Eq.refl
lemma-wfoldl-succ c ε = Eq.refl
lemma-wfoldl-succ c (w • w₁) with lemma-wfoldl-succ c w
... | ih with lemma-wfoldl-succ ( (wfoldl sucN c w)) w₁
... | ih2 = Eq.trans (Eq.cong (\xx → wfoldl sucN xx w₁) ih) ih2


aux-x=h : ∀ {N} (w : Fin (₁₊ N)) (h : Fin N) → sucN w ≡ ₁₊ h → toℕ w ≡ toℕ h
aux-x=h {₁₊ N} zero zero eq = Eq.refl
aux-x=h {₁₊ N} (₁₊ w) zero eq with sucN w | inspect sucN w
aux-x=h {₁₊ N} (₁₊ w) zero () | zero | [ eqh ]'
aux-x=h {₁₊ N} (₁₊ w) zero () | ₁₊ hyp | [ eqh ]'
aux-x=h {₁₊ N} (₁₊ w) (₁₊ h) eq with sucN w | inspect sucN w
... | ₁₊ hyp | [ eqh ]' with aux-x=h {N} w h (Eq.trans eqh (suc-injective eq))
... | ih = Eq.cong ₁₊ ih

aux-x=N : ∀ {N} (x : Fin (suc (N))) → sucN x ≡ zero → toℕ x ≡ N
aux-x=N {zero} zero eq = Eq.refl
aux-x=N {₁₊ N} (₁₊ x) eq with sucN x | inspect sucN x
... | zero | [ eqh ]' with aux-x=N {N} x eqh
... | ih = Eq.cong ₁₊ ih

aux-x=N' : ∀ {N} (x : Fin (suc (N))) → sucN x ≡ zero → sucN (₁₊ x) ≡ zero
aux-x=N' {zero} zero eq = Eq.refl
aux-x=N' {₁₊ N} (₁₊ x) eq with sucN x | inspect sucN x
... | zero | [ eqh ]' with aux-x=N {N} x eqh
... | ih = Eq.refl

sucN-inject₁ : ∀ {N} (x : Fin ((N))) → sucN (inject₁ x) ≡ ₁₊ x
sucN-inject₁ {₁₊ N} zero = Eq.refl
sucN-inject₁ {₂₊ N} (₁₊ x) with sucN-inject₁ {₁₊ N} x
... | ih rewrite (ih) = Eq.refl


aux-sx=0 : ∀ {N} (x : Fin (suc (N))) → toℕ x ≡ N → sucN x ≡ zero
aux-sx=0 {zero} zero eq = Eq.refl
aux-sx=0 {₁₊ N} zero = λ ()
aux-sx=0 {₁₊ N} (₁₊ x) hyp with aux-sx=0 {N} x
... | ih with ih (NP.suc-injective hyp)
... | ih' rewrite ih' = Eq.refl

lemma-succ : ∀ {N} → let _≈_ = PB._≈_ (pres N) in
  ∀ c → ([ c ] • T) ≈ [ succ {N} c ]
lemma-succ {zero} zero = PB._≈_.left-unit
lemma-succ {zero} (₁₊ c) = PB._≈_.refl
lemma-succ {₁₊ zero} zero = PB._≈_.trans PB._≈_.left-unit (PB._≈_.axiom order)
lemma-succ {₂₊ N} zero = PB._≈_.left-unit
lemma-succ {₂₊ N} (₁₊ c) with succ c | inspect succ c
... | zero | [ eqc ]' rewrite aux-x=N c eqc = PB._≈_.axiom order
... | ₁₊ hyp | [ eqc ]' rewrite aux-x=h c hyp eqc = PB._≈_.refl


lemma-f' : ∀ {N} → f {₁₊ N} (T ^' (₁₊ N)) ≡ sucN (f {₁₊ N} (T ^' N))
lemma-f' {zero} = Eq.refl
lemma-f' {₁₊ N} = Eq.refl

lemma-sucN : ∀ {N} (x : Fin (₁₊ N)) → sucN x ≡ zero → sucN (₁₊ x) ≡ zero
lemma-sucN {N} x eq with sucN x
... | zero = Eq.refl

lemma-sucN2 : ∀ {N} (x : Fin (₁₊ N)) y → sucN x ≡ ₁₊ y → sucN (₁₊ x) ≡ ₂₊ y
lemma-sucN2 {N} x y eq with sucN x
... | ₁₊ h rewrite eq = Eq.refl


g : ∀ {N} → NF N → Word X
g = [_]

lemma-gf=id : ∀ {N} → let _≈_ = PB._≈_ (pres N) in
  ∀ {w} → g {N} (f {N} w) ≈ w
lemma-gf=id {N} {w} = begin
  g {N} (f {N} w) ≈⟨ _≈_.refl ⟩
  g {N} (wfoldl succ z w) ≈⟨ lemma-wfoldl succ lemma-succ z w ⟩
  g {N} z • w ≈⟨ cong (refl' ([z]=ε {N})) refl ⟩
  ε • w ≈⟨ _≈_.left-unit ⟩
  w ∎
  where
  open PB (pres N)
  open PP (pres N) hiding (lemma-wfoldl)
  open SR word-setoid  



lemma-N-step : ∀ {N} → f {₁₊ N} (T ^' (₁₊ N)) ≡ sucN (f {₁₊ N} (T ^' N))
lemma-N-step {zero} = Eq.refl
lemma-N-step {₁₊ N} = Eq.refl

lemma-N-step0 : ∀ (x : ℕ) → f {0} (T ^' ₁₊ x) ≡ suc (f {0} (T ^' x))
lemma-N-step0 zero = Eq.refl
lemma-N-step0 (₁₊ x) = Eq.refl

ncompose : ∀ {A : Set} (f : A → A) → ℕ → A → A
ncompose {A} f zero = id
ncompose {A} f (₁₊ n) = ncompose f n ∘ f

comm-suc-inject₁ : ∀ {N} → (x : Fin N) → suc (inject₁ x) ≡ inject₁ (₁₊ x)
comm-suc-inject₁ {₁₊ N} x = Eq.refl

fg : ∀ {N} → NF N → NF N
fg = f ∘ g

fg=id : ∀ {N} (x : Fin (₁₊ N)) → fg x ≡ x
fg=id {N@zero} zero = Eq.refl
fg=id {N@(₁₊ N')} = <-weakInduction
  (\(x : Fin (₁₊ N)) → fg x ≡ x)
  Eq.refl
  (claim N)
  where
  claim : ∀ N → (i : Fin N) → fg (inject₁ i) ≡ inject₁ i → fg (₁₊ i) ≡ ₁₊ i
  claim (₁₊ zero) zero hyp = Eq.refl
  claim (₂₊ N) zero hyp = Eq.refl
  claim (₂₊ N) (₁₊ i) hyp with claim (₁₊ N) i (fg=id (inject₁ i))
  claim (₂₊ N) (₁₊ i) hyp | ih with sucN (inject₁ i) | inspect sucN (inject₁ i)
  claim (₂₊ N) (₁₊ i) hyp | ih | zero | [ eqi ]' rewrite toℕ-inject₁ i | hyp | eqi | comm-suc-inject₁ i  with (Eq.trans (Eq.sym (sucN-inject₁ i )) eqi)
  ... | ()
    where
    c0 : (wfoldl sucN zero ([ tt ]ʷ ^' suc (toℕ i))) ≡ inject₁ (wfoldl (sucN {₂₊ N}) zero ([ tt ]ʷ ^' suc (toℕ i)))
    c0 = Eq.trans hyp (Eq.trans (comm-suc-inject₁ i) (Eq.cong inject₁ (Eq.sym ih)) ) 

    c1 : sucN (wfoldl sucN zero ([ tt ]ʷ ^' suc (toℕ i))) ≡ ₂₊ i
    c1 = Eq.trans (Eq.cong sucN c0) (Eq.trans ( sucN-inject₁ (wfoldl (sucN {₂₊ N}) zero ([ tt ]ʷ ^' suc (toℕ i))) ) (Eq.cong ₁₊ ih))

    c2 : fg {₃₊ N} (₂₊ i) ≡ zero
    c2 rewrite hyp | eqi = Eq.refl

    c3 : (₁₊ i) ≡ zero
    c3 = Eq.trans (Eq.sym (sucN-inject₁ i )) eqi

  claim (₂₊ N) (₁₊ i) hyp | ih | ₁₊ ii | [ eqi ]' rewrite toℕ-inject₁ i | hyp | eqi | comm-suc-inject₁ i = (Eq.sym (Eq.cong ₁₊ c3))
    where
    c0 : (wfoldl sucN zero ([ tt ]ʷ ^' suc (toℕ i))) ≡ inject₁ (wfoldl (sucN {₂₊ N}) zero ([ tt ]ʷ ^' suc (toℕ i)))
    c0 = Eq.trans hyp (Eq.trans (comm-suc-inject₁ i) (Eq.cong inject₁ (Eq.sym ih)) ) 

    c1 : sucN (wfoldl sucN zero ([ tt ]ʷ ^' suc (toℕ i))) ≡ ₂₊ i
    c1 = Eq.trans (Eq.cong sucN c0) (Eq.trans ( sucN-inject₁ (wfoldl (sucN {₂₊ N}) zero ([ tt ]ʷ ^' suc (toℕ i))) ) (Eq.cong ₁₊ ih))

    c2 : fg {₃₊ N} (₂₊ i) ≡ ₂₊ ii
    c2 rewrite hyp | eqi = Eq.refl

    c3 : (₁₊ i) ≡ (₁₊ ii)
    c3 = Eq.trans (Eq.sym (sucN-inject₁ i )) eqi


lemma-f2 : ∀ {N} (x : Fin (₁₊ N)) → toℕ x ≡ N → sucN (f {₁₊ N} ([ x ])) ≡ zero
lemma-f2 {N} x eq = aux-sx=0 ((f {₁₊ N} ([ x ]))) (Eq.trans (Eq.cong toℕ (fg=id x)) eq)

lemma-f : ∀ {N} → f {₁₊ N} (T ^' (₁₊ N)) ≡ zero
lemma-f {N} = Eq.trans (c1 N) (lemma-f2 (fromℕ N) (toℕ-fromℕ N))
  where
  c1 : ∀ N → f {₁₊ N} (T ^' (₁₊ N)) ≡ sucN (f {₁₊ N} [ fromℕ N ])
  c1 zero = Eq.refl
  c1 (₁₊ N) rewrite toℕ-fromℕ N = Eq.refl


lemma-f4 : ∀ {N} {w} → f {₁₊ N} (w • ε) ≡ f {₁₊ N} (w)
lemma-f4 {N} {w} = Eq.refl

lemma-wfoldl-succw : ∀ {N} n → wfoldl (sucN {₁₊ N}) zero (T ^' ₁₊ n) ≡ sucN (wfoldl sucN zero (T ^' n))
lemma-wfoldl-succw {N} zero = Eq.refl
lemma-wfoldl-succw {N} (₁₊ n) = Eq.refl

lemma-f3 : ∀ {N} (c : Fin (₁₊ N)) → f {₁₊ N} ([ c ] • T ^' (₁₊ N)) ≡ f {₁₊ N} ([ c ] • ε)
lemma-f3 {N} = <-weakInduction
  (\(c : Fin (₁₊ N)) → f {₁₊ N} ([ c ] • T ^' (₁₊ N)) ≡ f {₁₊ N} ([ c ] • ε))
  lemma-f
  (c1 N)
  where
  c1 : ∀ N → (i : Fin N) →
    f {₁₊ N} ((T ^' toℕ (inject₁ i)) • (T ^' ₁₊ N)) ≡ f ((T ^' toℕ (inject₁ i)) • ε) →
    f {₁₊ N} ((T ^' suc (toℕ i)) • (T ^' ₁₊ N)) ≡ f ((T ^' suc (toℕ i)) • ε)
  c1 N i ih rewrite toℕ-inject₁ i = claim
    where
    claim : wfoldl (sucN {₁₊ N}) (wfoldl sucN zero ([ tt ]ʷ ^' suc (toℕ i)))([ tt ]ʷ ^' ₁₊ N)
      ≡ wfoldl sucN zero ([ tt ]ʷ ^' suc (toℕ i))
    claim = begin
       wfoldl (sucN {₁₊ N}) (wfoldl sucN zero ([ tt ]ʷ ^' suc (toℕ i)))([ tt ]ʷ ^' ₁₊ N) ≡⟨ Eq.cong (\xx → wfoldl (sucN {₁₊ N}) xx ([ tt ]ʷ ^' ₁₊ N)) (lemma-wfoldl-succw (toℕ i)) ⟩
       wfoldl (sucN {₁₊ N}) (sucN (wfoldl sucN zero ([ tt ]ʷ ^' (toℕ i))))([ tt ]ʷ ^' ₁₊ N) ≡⟨ lemma-wfoldl-succ ((wfoldl sucN zero ([ tt ]ʷ ^' (toℕ i)))) (T ^' ₁₊ N) ⟩
       sucN (wfoldl (sucN {₁₊ N}) ( (wfoldl sucN zero ([ tt ]ʷ ^' (toℕ i))))([ tt ]ʷ ^' ₁₊ N)) ≡⟨ Eq.cong sucN ih ⟩
       sucN (wfoldl sucN zero ([ tt ]ʷ ^' (toℕ i))) ≡⟨ Eq.sym (lemma-wfoldl-succw (toℕ i)) ⟩
       wfoldl sucN zero ([ tt ]ʷ ^' suc (toℕ i)) ∎
       where open ≡-Reasoning

lemma-f3' : ∀ {N} (c : Fin (₁₊ N)) → wfoldl sucN c (T ^' (₁₊ N)) ≡ c
lemma-f3' {N} = <-weakInduction
  (\ (c : Fin (₁₊ N)) → wfoldl sucN c (T ^' (₁₊ N)) ≡ c)
  lemma-f
  (c1 N)
  where
  c1 : ∀ N → (i : Fin N) → wfoldl sucN (inject₁ i) (T ^' ₁₊ N) ≡ inject₁ i →
    wfoldl sucN (₁₊ i) (T ^' ₁₊ N) ≡ ₁₊ i
  c1 N i ih = begin
    wfoldl sucN (₁₊ i) (T ^' ₁₊ N) ≡⟨ Eq.cong (λ xx → wfoldl sucN xx (T ^' ₁₊ N)) (Eq.sym (sucN-inject₁ i)) ⟩
    wfoldl sucN (sucN (inject₁ i)) (T ^' ₁₊ N) ≡⟨ lemma-wfoldl-succ (inject₁ i) (T ^' ₁₊ N) ⟩
    sucN (wfoldl sucN ( (inject₁ i)) (T ^' ₁₊ N)) ≡⟨ Eq.cong sucN ih ⟩
    sucN (inject₁ i) ≡⟨ sucN-inject₁ i ⟩
    ₁₊ i ∎
       where open ≡-Reasoning



lemma-comm-inj-sucN : ∀ {N} (x : Fin (₁₊ N)) → (sucN x ≡ zero → ⊥) → inject₁ (sucN x) ≡ sucN (inject₁ x)
lemma-comm-inj-sucN {zero} zero np = ⊥-elim (np Eq.refl)
lemma-comm-inj-sucN {₁₊ zero} zero np = Eq.refl
lemma-comm-inj-sucN {₁₊ zero} (₁₊ zero) np = ⊥-elim (np Eq.refl)
lemma-comm-inj-sucN {₂₊ N} zero np = Eq.refl
lemma-comm-inj-sucN {₂₊ N} (₁₊ x) np with sucN x | inspect sucN x
... | zero | [ eq ]' = ⊥-elim (np Eq.refl)
... | ₁₊ hyp | [ eq ]' with lemma-comm-inj-sucN {₁₊ N} x (λ x₁ → claim (Eq.trans (Eq.sym eq) x₁))
  where
  claim : ₁₊ hyp ≡ zero → ⊥
  claim = λ ()
... | ih rewrite eq | Eq.sym ih = Eq.refl


aux0 : ∀ {N} → sucN {₁₊ N} (fromℕ N) ≡ zero
aux0 {zero} = Eq.refl
aux0 {₁₊ N} with aux0 {N}
... | ih rewrite ih = Eq.refl

aux0' : ∀ {N} x → toℕ x ≡ N → sucN {₁₊ N} x ≡ zero
aux0' {zero} zero eq = Eq.refl
aux0' {₁₊ zero} (₁₊ zero) eq = Eq.refl
aux0' {₂₊ N} (₁₊ x) eq with sucN x | inspect sucN x
... | zero | [ eqh ]' = Eq.refl
... | ₁₊ h | [ eqh ]' with aux0' {₁₊ N} x (NP.suc-injective eq)
... | hyp with Eq.trans (Eq.sym eqh) hyp
... | ()


f-wd : ∀ {N} → let _≈_ = PB._≈_ (pres N) in let _===_ = PB._===_ (pres N) in
  ∀ (c : NF N){u t : Word X} → u === t → wfoldl succ c u ≡ wfoldl succ c t
f-wd {zero} c order = Eq.refl
f-wd {₁₊ N} c order = lemma-f3' c


wfoldl-cong : ∀ {N} → let _≈_ = PB._≈_ (pres (N)) in

  ∀ {w v} → (c : NF N) → w ≈ v → wfoldl succ c w ≡ wfoldl succ c v

wfoldl-cong {N} {w} {v} c PB.refl = Eq.refl
wfoldl-cong {N} {w} {v} c (PB.sym eq) = Eq.sym (wfoldl-cong c eq)
wfoldl-cong {N} {w} {v} c (PB.trans eq eq₁) = Eq.trans (wfoldl-cong c eq) (wfoldl-cong c eq₁)
wfoldl-cong {N} {w • w'} {v • v'} c (PB.cong eq eq₁) with wfoldl succ c w | wfoldl succ c v | wfoldl-cong {N} {w} {v} c eq
... | c' | c'' | ih rewrite ih = wfoldl-cong {N} {w'} {v'} c'' eq₁
wfoldl-cong {N} {w} {v} c PB.assoc = Eq.refl
wfoldl-cong {N} {w} {v} c PB.left-unit = Eq.refl
wfoldl-cong {N} {w} {v} c PB.right-unit = Eq.refl
wfoldl-cong {zero} {w} {v} c (PB.axiom order) = Eq.refl
wfoldl-cong {₁₊ N} {w} {v} c (PB.axiom order) = lemma-f3' c


f-cong : ∀ {N} → let _≈_ = PB._≈_ (pres (N)) in

  ∀ {w v} → w ≈ v → f {N} w ≡ f {N} v

f-cong {N} {w} {v} = wfoldl-cong z


nfp' : (n : ℕ) → NFProperty' (pres n)
nfp' n = record
           { NF = NF n ; nf = f ; nf-cong = f-cong ; inv-nf = g ; inv-nf∘nf=id = lemma-gf=id }

nfp : (n : ℕ) → NFProperty (pres n)
nfp n = NFProperty'.hasNFProperty (nfp' n)


