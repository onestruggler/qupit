{-# OPTIONS  --safe #-}
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
module RSF = RS.Star-Injective-Full.Reidemeister-Schreier-Full


open import Data.Fin.Properties using (suc-injective ; toℕ-inject₁ ; toℕ-fromℕ)
import Data.Nat.Properties as NP


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
pres : ℕ -> WRel X
pres N = rel N

-- successor modulo N.
sucN : ∀ {N} -> Fin N -> Fin N
sucN {suc zero} zero = zero
sucN {suc (suc N)} zero = suc zero
sucN {suc (suc N)} (suc f) with sucN {suc N} f
... | zero = zero
... | suc ih = suc (suc ih)

-- successor function is injective.
sucN-inj : ∀ {N} a b -> sucN {N} a ≡ sucN b -> a ≡ b
sucN-inj {suc zero} zero zero eq = eq
sucN-inj {suc (suc N)} zero zero eq = Eq.refl
sucN-inj {suc (suc N)} zero (suc b) eq with sucN b
sucN-inj {suc N} zero (suc b) () | zero
sucN-inj {suc N} zero (suc b) () | suc h
sucN-inj {suc (suc N)} (suc a) zero eq with sucN a
sucN-inj {suc N} (suc a) zero () | zero
sucN-inj {suc N} (suc a) zero () | suc h
sucN-inj {suc (suc N)} (suc a) (suc b) eq with sucN a | sucN b | inspect sucN a | inspect sucN b
... | zero | zero | [ eqa ]' | [ eqb ]' = Eq.cong suc (sucN-inj a b (Eq.trans eqa (Eq.sym eqb)))
sucN-inj {suc N} (suc a) (suc b) Eq.refl | suc ha | suc hb | [ eqa ]' | [ eqb ]' = Eq.cong suc (sucN-inj a b (Eq.trans eqa (Eq.sym eqb)))


-- predecessor fuction is the inverse of sucN.
predN : ∀ {N} -> Fin N -> Fin N
predN {suc zero} zero = zero
predN {suc (suc N)} zero = suc (predN {suc N} zero)
predN {suc (suc N)} (suc f) = inject₁ f

aux-inject₁ : ∀ {N} x -> sucN {suc N} (inject₁ x) ≡ suc x
aux-inject₁ {suc zero} zero = Eq.refl
aux-inject₁ {suc (suc N)} zero = Eq.refl
aux-inject₁ {suc (suc N)} (suc x) with aux-inject₁ {suc N} x
... | ih rewrite ih = Eq.refl

lemma-suc-pred : ∀ {N} (x : Fin N) -> sucN (predN x) ≡ x
lemma-suc-pred {suc zero} zero = Eq.refl
lemma-suc-pred {suc (suc N)} zero with lemma-suc-pred {suc N} zero
... | ih rewrite ih = Eq.refl
lemma-suc-pred {suc (suc N)} (suc x) = aux-inject₁ x

-- 0-th Normal Form set NF is ℕ. order N cyclic group has normal
-- form set Fin N.
NF : ℕ -> Set
NF zero = ℕ
NF (suc N) = Fin (suc N)

succ : ∀ {N} -> NF N -> NF N
succ {zero} = suc
succ {suc N} = sucN


z : ∀ {N} -> NF N
z {zero} = zero
z {suc N} = zero

[_] : ∀ {N} -> NF N -> Word X
[_] {zero} nf = T ^' nf
[_] {suc N} nf = T ^' toℕ nf

[z]=ε : ∀ {N} -> [_] {N} z ≡ ε
[z]=ε {zero} = Eq.refl
[z]=ε {suc N} = Eq.refl


--   wfoldl : ∀ {N} (NF N -> X -> NF N) -> (NF N -> Word X -> NF N)
-->  wfoldl : ∀ {N} (Word ⊥ × C N -> X -> Word ⊥ × C N) -> (Word ⊥ × C N -> Word X -> Word ⊥ × C N)
-->  wfoldl : ∀ {N} -> (C N -> X -> C N) -> (C N -> Word X -> C N)
-->  wfoldl : ∀ {N} -> (C N -> C N) -> (C N -> Word X -> C N)
-->  wfoldl : ∀ {N} -> (NF N -> NF N) -> (NF N -> Word X -> NF N)

wfoldl : ∀ {N} -> (NF N -> NF N) -> (NF N -> Word X -> NF N)
wfoldl {N} succ c [ x ]ʷ = succ c
wfoldl {N} succ c ε = c
wfoldl {N} succ c (w • w₁) = wfoldl {N} succ (wfoldl {N} succ c w) w₁

f : ∀ {N} -> Word X -> NF N
f {N} = wfoldl {N} succ z

lemma-wfoldl : ∀ {N} -> let _≈_ = PB._≈_ (pres N) in
  ∀ (succ : NF N -> NF N)
    (lemma-succ :  ∀ c -> ([ c ] • T) ≈ [ succ c ])
    (c : NF N) (w : Word X)
    ->
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

lemma-wfoldl-succ : ∀ {N} (c : Fin (suc N)) w -> wfoldl succ (succ c) w ≡ succ (wfoldl succ c w)
lemma-wfoldl-succ c [ x ]ʷ = Eq.refl
lemma-wfoldl-succ c ε = Eq.refl
lemma-wfoldl-succ c (w • w₁) with lemma-wfoldl-succ c w
... | ih with lemma-wfoldl-succ ( (wfoldl sucN c w)) w₁
... | ih2 = Eq.trans (Eq.cong (\xx -> wfoldl sucN xx w₁) ih) ih2


aux-x=h : ∀ {N} (w : Fin (suc N)) (h : Fin N) -> sucN w ≡ suc h -> toℕ w ≡ toℕ h
aux-x=h {suc N} zero zero eq = Eq.refl
aux-x=h {suc N} (suc w) zero eq with sucN w | inspect sucN w
aux-x=h {suc N} (suc w) zero () | zero | [ eqh ]'
aux-x=h {suc N} (suc w) zero () | suc hyp | [ eqh ]'
aux-x=h {suc N} (suc w) (suc h) eq with sucN w | inspect sucN w
... | suc hyp | [ eqh ]' with aux-x=h {N} w h (Eq.trans eqh (suc-injective eq))
... | ih = Eq.cong suc ih

aux-x=N : ∀ {N} (x : Fin (suc (N))) -> sucN x ≡ zero -> toℕ x ≡ N
aux-x=N {zero} zero eq = Eq.refl
aux-x=N {suc N} (suc x) eq with sucN x | inspect sucN x
... | zero | [ eqh ]' with aux-x=N {N} x eqh
... | ih = Eq.cong suc ih

aux-x=N' : ∀ {N} (x : Fin (suc (N))) -> sucN x ≡ zero -> sucN (suc x) ≡ zero
aux-x=N' {zero} zero eq = Eq.refl
aux-x=N' {suc N} (suc x) eq with sucN x | inspect sucN x
... | zero | [ eqh ]' with aux-x=N {N} x eqh
... | ih = Eq.refl

sucN-inject₁ : ∀ {N} (x : Fin ((N))) -> sucN (inject₁ x) ≡ suc x
sucN-inject₁ {suc N} zero = Eq.refl
sucN-inject₁ {suc (suc N)} (suc x) with sucN-inject₁ {suc N} x
... | ih rewrite (ih) = Eq.refl


aux-sx=0 : ∀ {N} (x : Fin (suc (N))) -> toℕ x ≡ N -> sucN x ≡ zero
aux-sx=0 {zero} zero eq = Eq.refl
aux-sx=0 {suc N} zero = λ ()
aux-sx=0 {suc N} (suc x) hyp with aux-sx=0 {N} x
... | ih with ih (NP.suc-injective hyp)
... | ih' rewrite ih' = Eq.refl

lemma-succ : ∀ {N} -> let _≈_ = PB._≈_ (pres N) in
  ∀ c -> ([ c ] • T) ≈ [ succ {N} c ]
lemma-succ {zero} zero = PB._≈_.left-unit
lemma-succ {zero} (suc c) = PB._≈_.refl
lemma-succ {suc zero} zero = PB._≈_.trans PB._≈_.left-unit (PB._≈_.axiom order)
lemma-succ {suc (suc N)} zero = PB._≈_.left-unit
lemma-succ {suc (suc N)} (suc c) with succ c | inspect succ c
... | zero | [ eqc ]' rewrite aux-x=N c eqc = PB._≈_.axiom order
... | suc hyp | [ eqc ]' rewrite aux-x=h c hyp eqc = PB._≈_.refl


lemma-f' : ∀ {N} -> f {suc N} (T ^' (suc N)) ≡ sucN (f {suc N} (T ^' N))
lemma-f' {zero} = Eq.refl
lemma-f' {suc N} = Eq.refl

lemma-sucN : ∀ {N} (x : Fin (suc N)) -> sucN x ≡ zero -> sucN (suc x) ≡ zero
lemma-sucN {N} x eq with sucN x
... | zero = Eq.refl

lemma-sucN2 : ∀ {N} (x : Fin (suc N)) y -> sucN x ≡ suc y -> sucN (suc x) ≡ suc (suc y)
lemma-sucN2 {N} x y eq with sucN x
... | suc h rewrite eq = Eq.refl


g : ∀ {N} -> NF N -> Word X
g = [_]

lemma-gf=id : ∀ {N} -> let _≈_ = PB._≈_ (pres N) in
  ∀ {w} -> g {N} (f {N} w) ≈ w
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



lemma-N-step : ∀ {N} -> f {suc N} (T ^' (suc N)) ≡ sucN (f {suc N} (T ^' N))
lemma-N-step {zero} = Eq.refl
lemma-N-step {suc N} = Eq.refl

lemma-N-step0 : ∀ (x : ℕ) -> f {0} (T ^' suc x) ≡ suc (f {0} (T ^' x))
lemma-N-step0 zero = Eq.refl
lemma-N-step0 (suc x) = Eq.refl

ncompose : ∀ {A : Set} (f : A -> A) -> ℕ -> A -> A
ncompose {A} f zero = id
ncompose {A} f (suc n) = ncompose f n ∘ f

comm-suc-inject₁ : ∀ {N} -> (x : Fin N) -> suc (inject₁ x) ≡ inject₁ (suc x)
comm-suc-inject₁ {suc N} x = Eq.refl

fg : ∀ {N} -> NF N -> NF N
fg = f ∘ g

fg=id : ∀ {N} (x : Fin (suc N)) -> fg x ≡ x
fg=id {N@zero} zero = Eq.refl
fg=id {N@(suc N')} = <-weakInduction
  (\(x : Fin (suc N)) -> fg x ≡ x)
  Eq.refl
  (claim N)
  where
  claim : ∀ N -> (i : Fin N) → fg (inject₁ i) ≡ inject₁ i → fg (suc i) ≡ suc i
  claim (suc zero) zero hyp = Eq.refl
  claim (suc (suc N)) zero hyp = Eq.refl
  claim (suc (suc N)) (suc i) hyp with claim (suc N) i (fg=id (inject₁ i))
  claim (suc (suc N)) (suc i) hyp | ih with sucN (inject₁ i) | inspect sucN (inject₁ i)
  claim (suc (suc N)) (suc i) hyp | ih | zero | [ eqi ]' rewrite toℕ-inject₁ i | hyp | eqi | comm-suc-inject₁ i  with (Eq.trans (Eq.sym (sucN-inject₁ i )) eqi)
  ... | ()
    where
    c0 : (wfoldl sucN zero ([ tt ]ʷ ^' suc (toℕ i))) ≡ inject₁ (wfoldl (sucN {suc (suc N)}) zero ([ tt ]ʷ ^' suc (toℕ i)))
    c0 = Eq.trans hyp (Eq.trans (comm-suc-inject₁ i) (Eq.cong inject₁ (Eq.sym ih)) ) 

    c1 : sucN (wfoldl sucN zero ([ tt ]ʷ ^' suc (toℕ i))) ≡ suc (suc i)
    c1 = Eq.trans (Eq.cong sucN c0) (Eq.trans ( sucN-inject₁ (wfoldl (sucN {suc (suc N)}) zero ([ tt ]ʷ ^' suc (toℕ i))) ) (Eq.cong suc ih))

    c2 : fg {suc (suc (suc N))} (suc (suc i)) ≡ zero
    c2 rewrite hyp | eqi = Eq.refl

    c3 : (suc i) ≡ zero
    c3 = Eq.trans (Eq.sym (sucN-inject₁ i )) eqi

  claim (suc (suc N)) (suc i) hyp | ih | suc ii | [ eqi ]' rewrite toℕ-inject₁ i | hyp | eqi | comm-suc-inject₁ i = (Eq.sym (Eq.cong suc c3))
    where
    c0 : (wfoldl sucN zero ([ tt ]ʷ ^' suc (toℕ i))) ≡ inject₁ (wfoldl (sucN {suc (suc N)}) zero ([ tt ]ʷ ^' suc (toℕ i)))
    c0 = Eq.trans hyp (Eq.trans (comm-suc-inject₁ i) (Eq.cong inject₁ (Eq.sym ih)) ) 

    c1 : sucN (wfoldl sucN zero ([ tt ]ʷ ^' suc (toℕ i))) ≡ suc (suc i)
    c1 = Eq.trans (Eq.cong sucN c0) (Eq.trans ( sucN-inject₁ (wfoldl (sucN {suc (suc N)}) zero ([ tt ]ʷ ^' suc (toℕ i))) ) (Eq.cong suc ih))

    c2 : fg {suc (suc (suc N))} (suc (suc i)) ≡ suc (suc ii)
    c2 rewrite hyp | eqi = Eq.refl

    c3 : (suc i) ≡ (suc ii)
    c3 = Eq.trans (Eq.sym (sucN-inject₁ i )) eqi


lemma-f2 : ∀ {N} (x : Fin (suc N)) -> toℕ x ≡ N -> sucN (f {suc N} ([ x ])) ≡ zero
lemma-f2 {N} x eq = aux-sx=0 ((f {suc N} ([ x ]))) (Eq.trans (Eq.cong toℕ (fg=id x)) eq)

lemma-f : ∀ {N} -> f {suc N} (T ^' (suc N)) ≡ zero
lemma-f {N} = Eq.trans (c1 N) (lemma-f2 (fromℕ N) (toℕ-fromℕ N))
  where
  c1 : ∀ N -> f {suc N} (T ^' (suc N)) ≡ sucN (f {suc N} [ fromℕ N ])
  c1 zero = Eq.refl
  c1 (suc N) rewrite toℕ-fromℕ N = Eq.refl


lemma-f4 : ∀ {N} {w} -> f {suc N} (w • ε) ≡ f {suc N} (w)
lemma-f4 {N} {w} = Eq.refl

lemma-f5 : ∀ {N} {w} -> f {suc N} (w • ε) ≡ f {suc N} (w)
lemma-f5 {N} {w} = Eq.refl

lemma-wfoldl-succw : ∀ {N} n -> wfoldl (sucN {suc N}) zero (T ^' suc n) ≡ sucN (wfoldl sucN zero (T ^' n))
lemma-wfoldl-succw {N} zero = Eq.refl
lemma-wfoldl-succw {N} (suc n) = Eq.refl

lemma-f3 : ∀ {N} (c : Fin (suc N)) -> f {suc N} ([ c ] • T ^' (suc N)) ≡ f {suc N} ([ c ] • ε)
lemma-f3 {N} = <-weakInduction
  (\(c : Fin (suc N)) -> f {suc N} ([ c ] • T ^' (suc N)) ≡ f {suc N} ([ c ] • ε))
  lemma-f
  (c1 N)
  where
  c1 : ∀ N -> (i : Fin N) →
    f {suc N} ((T ^' toℕ (inject₁ i)) • (T ^' suc N)) ≡ f ((T ^' toℕ (inject₁ i)) • ε) →
    f {suc N} ((T ^' suc (toℕ i)) • (T ^' suc N)) ≡ f ((T ^' suc (toℕ i)) • ε)
  c1 N i ih rewrite toℕ-inject₁ i = claim
    where
    claim : wfoldl (sucN {suc N}) (wfoldl sucN zero ([ tt ]ʷ ^' suc (toℕ i)))([ tt ]ʷ ^' suc N)
      ≡ wfoldl sucN zero ([ tt ]ʷ ^' suc (toℕ i))
    claim = begin
       wfoldl (sucN {suc N}) (wfoldl sucN zero ([ tt ]ʷ ^' suc (toℕ i)))([ tt ]ʷ ^' suc N) ≡⟨ Eq.cong (\xx -> wfoldl (sucN {suc N}) xx ([ tt ]ʷ ^' suc N)) (lemma-wfoldl-succw (toℕ i)) ⟩
       wfoldl (sucN {suc N}) (sucN (wfoldl sucN zero ([ tt ]ʷ ^' (toℕ i))))([ tt ]ʷ ^' suc N) ≡⟨ lemma-wfoldl-succ ((wfoldl sucN zero ([ tt ]ʷ ^' (toℕ i)))) (T ^' suc N) ⟩
       sucN (wfoldl (sucN {suc N}) ( (wfoldl sucN zero ([ tt ]ʷ ^' (toℕ i))))([ tt ]ʷ ^' suc N)) ≡⟨ Eq.cong sucN ih ⟩
       sucN (wfoldl sucN zero ([ tt ]ʷ ^' (toℕ i))) ≡⟨ Eq.sym (lemma-wfoldl-succw (toℕ i)) ⟩
       wfoldl sucN zero ([ tt ]ʷ ^' suc (toℕ i)) ∎
       where open ≡-Reasoning

lemma-f3' : ∀ {N} (c : Fin (suc N)) -> wfoldl sucN c (T ^' (suc N)) ≡ c
lemma-f3' {N} = <-weakInduction
  (\ (c : Fin (suc N)) -> wfoldl sucN c (T ^' (suc N)) ≡ c)
  lemma-f
  (c1 N)
  where
  c1 : ∀ N -> (i : Fin N) → wfoldl sucN (inject₁ i) (T ^' suc N) ≡ inject₁ i →
    wfoldl sucN (suc i) (T ^' suc N) ≡ suc i
  c1 N i ih = begin
    wfoldl sucN (suc i) (T ^' suc N) ≡⟨ Eq.cong (λ xx → wfoldl sucN xx (T ^' suc N)) (Eq.sym (sucN-inject₁ i)) ⟩
    wfoldl sucN (sucN (inject₁ i)) (T ^' suc N) ≡⟨ lemma-wfoldl-succ (inject₁ i) (T ^' suc N) ⟩
    sucN (wfoldl sucN ( (inject₁ i)) (T ^' suc N)) ≡⟨ Eq.cong sucN ih ⟩
    sucN (inject₁ i) ≡⟨ sucN-inject₁ i ⟩
    suc i ∎
       where open ≡-Reasoning



lemma-comm-inj-sucN : ∀ {N} (x : Fin (suc N)) -> (sucN x ≡ zero -> ⊥) -> inject₁ (sucN x) ≡ sucN (inject₁ x)
lemma-comm-inj-sucN {zero} zero np = ⊥-elim (np Eq.refl)
lemma-comm-inj-sucN {suc zero} zero np = Eq.refl
lemma-comm-inj-sucN {suc zero} (suc zero) np = ⊥-elim (np Eq.refl)
lemma-comm-inj-sucN {suc (suc N)} zero np = Eq.refl
lemma-comm-inj-sucN {suc (suc N)} (suc x) np with sucN x | inspect sucN x
... | zero | [ eq ]' = ⊥-elim (np Eq.refl)
... | suc hyp | [ eq ]' with lemma-comm-inj-sucN {suc N} x (λ x₁ → claim (Eq.trans (Eq.sym eq) x₁))
  where
  claim : suc hyp ≡ zero -> ⊥
  claim = λ ()
... | ih rewrite eq | Eq.sym ih = Eq.refl


aux0 : ∀ {N} -> sucN {suc N} (fromℕ N) ≡ zero
aux0 {zero} = Eq.refl
aux0 {suc N} with aux0 {N}
... | ih rewrite ih = Eq.refl

aux0' : ∀ {N} x -> toℕ x ≡ N -> sucN {suc N} x ≡ zero
aux0' {zero} zero eq = Eq.refl
aux0' {suc zero} (suc zero) eq = Eq.refl
aux0' {suc (suc N)} (suc x) eq with sucN x | inspect sucN x
... | zero | [ eqh ]' = Eq.refl
... | suc h | [ eqh ]' with aux0' {suc N} x (NP.suc-injective eq)
... | hyp with Eq.trans (Eq.sym eqh) hyp
... | ()


f-wd : ∀ {N} -> let _≈_ = PB._≈_ (pres N) in let _===_ = PB._===_ (pres N) in
  ∀ (c : NF N){u t : Word X} -> u === t -> wfoldl succ c u ≡ wfoldl succ c t
f-wd {zero} c order = Eq.refl
f-wd {suc N} c order = lemma-f3' c


wfoldl-cong : ∀ {N} -> let _≈_ = PB._≈_ (pres (N)) in

  ∀ {w v} -> (c : NF N) -> w ≈ v -> wfoldl succ c w ≡ wfoldl succ c v

wfoldl-cong {N} {w} {v} c PB.refl = Eq.refl
wfoldl-cong {N} {w} {v} c (PB.sym eq) = Eq.sym (wfoldl-cong c eq)
wfoldl-cong {N} {w} {v} c (PB.trans eq eq₁) = Eq.trans (wfoldl-cong c eq) (wfoldl-cong c eq₁)
wfoldl-cong {N} {w • w'} {v • v'} c (PB.cong eq eq₁) with wfoldl succ c w | wfoldl succ c v | wfoldl-cong {N} {w} {v} c eq
... | c' | c'' | ih rewrite ih = wfoldl-cong {N} {w'} {v'} c'' eq₁
wfoldl-cong {N} {w} {v} c PB.assoc = Eq.refl
wfoldl-cong {N} {w} {v} c PB.left-unit = Eq.refl
wfoldl-cong {N} {w} {v} c PB.right-unit = Eq.refl
wfoldl-cong {zero} {w} {v} c (PB.axiom order) = Eq.refl
wfoldl-cong {suc N} {w} {v} c (PB.axiom order) = lemma-f3' c


f-cong : ∀ {N} -> let _≈_ = PB._≈_ (pres (N)) in

  ∀ {w v} -> w ≈ v -> f {N} w ≡ f {N} v

f-cong {N} {w} {v} = wfoldl-cong z


nfp' : (n : ℕ) -> NFProperty' (pres n)
nfp' n = record
           { NF = NF n ; nf = f ; nf-cong = f-cong ; inv-nf = g ; inv-nf∘nf=id = lemma-gf=id }

nfp : (n : ℕ) -> NFProperty (pres n)
nfp n = NFProperty'.hasNFProperty (nfp' n)


