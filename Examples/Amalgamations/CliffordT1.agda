------------------------------------------------------------------------
-- Examples
--
-- Completeness proof for the qubit Clifford+T gate set.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}

open import Relation.Binary.PropositionalEquality using (_≡_)
import Relation.Binary.Reasoning.Setoid as SR
import Relation.Binary.PropositionalEquality as Eq

open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂ ; ∃)
open import Data.Product.Relation.Binary.Pointwise.NonDependent using (Pointwise)
open import Data.Nat using (zero ; suc)
open import Data.Sum using (_⊎_ ; inj₁ ; inj₂ ; [_,_])
open import Data.Unit using (⊤ ; tt)

open import Word.Base
open import Word.Properties
import Presentation.Horizontal-Syntactics as PB
import Presentation.Properties as PP
open PP using (NFProperty ; NFProperty')
import Presentation.CosetNF as CA
open CA using (CosetNF-CT-Assumptions-And-Theorems-Packed)
import Presentation.Reidemeister-Schreier as RS

import Presentation.Groups.Sn as Sn
import Presentation.Groups.Cyclic as Cyclic
open import Presentation.Construct.Base
open import Presentation.Construct.Properties.Amalgamation
import Presentation.Construct.Properties.DirectProduct as DP
open import Notations


module Examples.Amalgamations.CliffordT1 where

module M0 where
  Pω : WRel Cyclic.X
  Pω = Cyclic.rel 8

  PS : WRel Cyclic.X
  PS = Cyclic.rel 4

  nfp : NFProperty (Pω ⊕ PS)
  nfp = DNF.NFP.nfp (Cyclic.nfp 8) (Cyclic.nfp 4)
    where
    module DNF = DP Pω PS

  nfp' : NFProperty' (Pω ⊕ PS)
  nfp' = DNF.NFP'.nfp' (Cyclic.nfp' 8) (Cyclic.nfp' 4)
    where
    module DNF = DP Pω PS

  open PB (Pω ⊕ PS) renaming (Alphabet to M0 ; _===_ to _===₀_) using ()

  ω : Word M0
  ω = [ inj₁ tt ]ʷ

  S : Word M0
  S = [ inj₂ tt ]ʷ

module M where
  data Gen : Set where
    X-gen : Gen
    S-gen : Gen
    ω-gen : Gen

  X : Word Gen
  X = [ X-gen ]ʷ

  S : Word Gen
  S = [ S-gen ]ʷ

  ω : Word Gen
  ω = [ ω-gen ]ʷ

  infix 4 _===_
  data _===_ : WRel Gen where
    order-ω : ω ^ 8 === ε
    order-S : S ^ 4 === ε
    order-X : X ^ 2 === ε
    order-SX : (S • X) ^ 2 === ω ^ 2
    comm : ∀ {gen} → ω • [ gen ]ʷ === [ gen ]ʷ • ω

  data C : Set where
    X-cr : C
    ε-cr : C

  open M0 using (Pω ; PS)
  open PB (Pω ⊕ PS) renaming (Alphabet to M0 ; _===_ to _===₀_ ; _≈_ to _≈₀_) using ()
  open NFProperty M0.nfp using (by-equal-nf)

  open PB _===_ renaming (Alphabet to M) using (_≈_)

  open _≈_

  f : M0 → Word M
  f (inj₁ tt) = ω
  f (inj₂ tt) = S

  h : C → M → Word M0 × C
  h X-cr X-gen = ε , ε-cr
  h X-cr S-gen = (M0.ω ^ 2 • M0.S ^ 3) , X-cr
  h X-cr ω-gen = M0.ω , X-cr
  h ε-cr X-gen = ε , X-cr
  h ε-cr S-gen = M0.S , ε-cr
  h ε-cr ω-gen = M0.ω , ε-cr

  infix 4 _~_
  _~_ = Pointwise _≈₀_ (_≡_ {A = C})

  h=⁻¹f-gen : ∀ x → ([ x ]ʷ , ε-cr) ~ ((h **) ε-cr (f x)) 
  h=⁻¹f-gen (inj₁ tt) = _≈₀_.refl , Eq.refl
  h=⁻¹f-gen (inj₂ tt) = _≈₀_.refl , Eq.refl

  h-wd-ax : ∀ c {u t} → u === t → (h **) c u ~ (h **) c t
  h-wd-ax X-cr {u} {t} order-ω = (by-equal-nf Eq.refl) , Eq.refl
  h-wd-ax X-cr {u} {t} order-S = (by-equal-nf Eq.refl) , Eq.refl
  h-wd-ax X-cr {u} {t} order-X = (by-equal-nf Eq.refl) , Eq.refl
  h-wd-ax X-cr {u} {t} order-SX = (by-equal-nf Eq.refl) , Eq.refl
  h-wd-ax X-cr {u} {t} (comm {X-gen}) = (by-equal-nf Eq.refl) , Eq.refl
  h-wd-ax X-cr {u} {t} (comm {S-gen}) = (by-equal-nf Eq.refl) , Eq.refl
  h-wd-ax X-cr {u} {t} (comm {ω-gen}) = (by-equal-nf Eq.refl) , Eq.refl
  h-wd-ax ε-cr {u} {t} order-ω = (by-equal-nf Eq.refl) , Eq.refl
  h-wd-ax ε-cr {u} {t} order-X = (by-equal-nf Eq.refl) , Eq.refl
  h-wd-ax ε-cr {u} {t} order-S = (by-equal-nf Eq.refl) , Eq.refl
  h-wd-ax ε-cr {u} {t} order-SX = (by-equal-nf Eq.refl) , Eq.refl
  h-wd-ax ε-cr {u} {t} (comm {X-gen}) = (by-equal-nf Eq.refl) , Eq.refl
  h-wd-ax ε-cr {u} {t} (comm {S-gen}) = (by-equal-nf Eq.refl) , Eq.refl
  h-wd-ax ε-cr {u} {t} (comm {ω-gen}) = (by-equal-nf Eq.refl) , Eq.refl

  open PP _===_

  f-wd-ax : ∀ {w v} → w ===₀ v → (f *) w ≈ (f *) v
  f-wd-ax {w} {v} (left Cyclic.order) = _≈_.trans (by-assoc Eq.refl) (_≈_.axiom order-ω) 
  f-wd-ax {w} {v} (right Cyclic.order) = _≈_.trans _≈_.assoc (_≈_.trans _≈_.assoc (_≈_.axiom order-S))
  f-wd-ax {w} {v} (mid (comm tt tt)) = _≈_.axiom comm

  [_] : C → Word M
  [ X-cr ] = X
  [ ε-cr ] = ε

  lemma-ω : ∀ w → w • ω ≈ ω • w
  lemma-ω [ x ]ʷ = sym (axiom comm)
  lemma-ω ε = trans left-unit (sym right-unit)
  lemma-ω (w • v) = trans assoc (trans (cong refl (lemma-ω v)) (trans (sym assoc) (trans (cong (lemma-ω w) refl) assoc)))

  lemma-ω^n : ∀ n w → w • ω ^ n ≈ ω ^ n • w
  lemma-ω^n zero w = trans right-unit (sym left-unit)
  lemma-ω^n (₁₊ n@zero) w = begin
    w • ω ^ ₁₊ n ≈⟨ sym right-unit ⟩
    (w • ω) • ω ^ n ≈⟨ cong (lemma-ω w) refl ⟩
    (ω • w) • ω ^ n ≈⟨ assoc ⟩
    ω • w • ω ^ n ≈⟨ cong refl (lemma-ω^n n w) ⟩
    ω • ω ^ n • w ≈⟨ cong refl left-unit ⟩
    ω ^ ₁₊ n • w ∎
    where
    open SR word-setoid

  lemma-ω^n (₁₊ n@(₁₊ n')) w = begin
    w • ω ^ ₁₊ n ≈⟨ sym assoc ⟩
    (w • ω) • ω ^ n ≈⟨ cong (lemma-ω w) refl ⟩
    (ω • w) • ω ^ n ≈⟨ assoc ⟩
    ω • w • ω ^ n ≈⟨ cong refl (lemma-ω^n n w) ⟩
    ω • ω ^ n • w ≈⟨ sym assoc ⟩
    (ω • ω ^ n) • w ≈⟨ refl ⟩
    ω ^ ₁₊ n • w ∎
    where
    open SR word-setoid


  lemma-XS : X • S ≈ (ω ^ 2 • S ^ 3) • X
  lemma-XS = begin
    X • S ≈⟨ trans (sym right-unit) (sym (cong refl (axiom order-X))) ⟩
   (X • S) • (X • X) ≈⟨ trans (sym left-unit) (sym (cong (axiom order-S) refl)) ⟩
   (S ^ 4) • (X • S) • (X • X) ≈⟨ by-assoc Eq.refl ⟩
   (S ^ 3) • (S • X) ^ 2  • X ≈⟨ cong refl (cong (axiom order-SX) refl) ⟩ 
   (S ^ 3) • ω ^ 2 • X ≈⟨ sym assoc ⟩
   (S ^ 3 • ω ^ 2) • X ≈⟨ cong (lemma-ω^n 2 (S ^ 3)) refl ⟩
   (ω ^ 2 • S ^ 3) • X ∎
    where
    open SR word-setoid

  h-hyp : ∀ c b → [ c ] • [ b ]ʷ ≈ (f *) (h c b .proj₁) • [ h c b .proj₂ ]
  h-hyp X-cr X-gen = _≈_.trans (axiom order-X) (_≈_.sym _≈_.left-unit)
  h-hyp X-cr S-gen = lemma-XS
  h-hyp X-cr ω-gen = sym (axiom comm)
  h-hyp ε-cr X-gen = refl
  h-hyp ε-cr S-gen = trans left-unit (sym right-unit)
  h-hyp ε-cr ω-gen = trans left-unit (sym right-unit)

  module ca = CA.Data (Pω ⊕ PS) _===_ C ε-cr f h [_]
  module aat = ca.Assumptions-And-Theorems h=⁻¹f-gen h-wd-ax f-wd-ax _≈_.refl h-hyp
  open aat using (nfp ; nfp') public
  

module MA where
  data Gen : Set where
    H-gen : Gen
    X-gen : Gen
    S-gen : Gen
    ω-gen : Gen

  H : Word Gen
  H = [ H-gen ]ʷ

  S : Word Gen
  S = [ S-gen ]ʷ

  ω : Word Gen
  ω = [ ω-gen ]ʷ

  X : Word Gen
  X = [ X-gen ]ʷ

  infix 4 _===_
  data _===_ : WRel Gen where
    order-ω : ω ^ 8 === ε
    order-S : S ^ 4 === ε
    order-H : H ^ 2 === ε
    order-SH : (S • H) ^ 3 === ω
    def-X : X === H • S • S • H
    comm : ∀ {gen} → ω • [ gen ]ʷ === [ gen ]ʷ • ω


  open PB (M._===_) renaming (Alphabet to M ; _===_ to _===₀_ ; _≈_ to _≈₀_) using ()
  open NFProperty (M.nfp M0.nfp) using (by-equal-nf)
  open PB _===_ renaming (Alphabet to MA) using (_≈_)

  open _≈_

  f : M → Word MA
  f M.X-gen = X
  f M.S-gen = S
  f M.ω-gen = ω

  data C : Set where
    HS-cr : C
    H-cr : C

  CT = C ⊎ ⊤

  I : CT
  I = inj₂ tt

  h : CT → MA → Word M × CT
  h (inj₁ HS-cr) H-gen = M.ω • M.S ^ 3 • M.X , (inj₁ HS-cr)
  h (inj₁ HS-cr) S-gen = M.X , (inj₁ H-cr)
  h (inj₁ HS-cr) ω-gen = M.ω , (inj₁ HS-cr)
  h (inj₁ H-cr) H-gen = ε , (inj₂ tt)
  h (inj₁ H-cr) S-gen = ε , (inj₁ HS-cr)
  h (inj₁ H-cr) ω-gen = M.ω , (inj₁ H-cr)
  h (inj₂ tt) H-gen = ε , (inj₁ H-cr)
  h (inj₂ tt) S-gen = M.S , (inj₂ tt)
  h (inj₂ tt) ω-gen = M.ω , (inj₂ tt)
  h (inj₁ HS-cr) X-gen = M.ω ^ 2 • M.S ^ 2 • M.X , inj₁ HS-cr
  h (inj₁ H-cr) X-gen = (M.S • M.S) , inj₁ H-cr
  h (inj₂ tt) X-gen = M.X , (inj₂ tt)

  infix 4 _~_
  _~_ = Pointwise _≈₀_ (_≡_ {A = CT})

  h=⁻¹f-gen : ∀ x → ([ x ]ʷ , I) ~ ((h **) I (f x)) 
  h=⁻¹f-gen M.X-gen = (by-equal-nf Eq.refl) , Eq.refl
  h=⁻¹f-gen M.S-gen = (by-equal-nf Eq.refl) , Eq.refl
  h=⁻¹f-gen M.ω-gen = (by-equal-nf Eq.refl) , Eq.refl

  h-wd-ax : ∀ c {u t} → u === t → (h **) c u ~ (h **) c t
  h-wd-ax (inj₁ HS-cr) {u} {t} order-ω = (by-equal-nf Eq.refl) , Eq.refl
  h-wd-ax (inj₁ HS-cr) {u} {t} order-S = (by-equal-nf Eq.refl) , Eq.refl
  h-wd-ax (inj₁ HS-cr) {u} {t} order-H = (by-equal-nf Eq.refl) , Eq.refl
  h-wd-ax (inj₁ HS-cr) {u} {t} order-SH = (by-equal-nf Eq.refl) , Eq.refl
  h-wd-ax (inj₁ HS-cr) {u} {t} (comm {H-gen}) = (by-equal-nf Eq.refl) , Eq.refl
  h-wd-ax (inj₁ HS-cr) {u} {t} (comm {S-gen}) = (by-equal-nf Eq.refl) , Eq.refl
  h-wd-ax (inj₁ HS-cr) {u} {t} (comm {ω-gen}) = (by-equal-nf Eq.refl) , Eq.refl
  h-wd-ax (inj₁ HS-cr) {u} {t} (comm {X-gen}) = (by-equal-nf Eq.refl) , Eq.refl
  h-wd-ax (inj₁ H-cr) {u} {t} order-ω = (by-equal-nf Eq.refl) , Eq.refl
  h-wd-ax (inj₁ H-cr) {u} {t} order-S = (by-equal-nf Eq.refl) , Eq.refl
  h-wd-ax (inj₁ H-cr) {u} {t} order-H = (by-equal-nf Eq.refl) , Eq.refl
  h-wd-ax (inj₁ H-cr) {u} {t} order-SH = (by-equal-nf Eq.refl) , Eq.refl
  h-wd-ax (inj₁ H-cr) {u} {t} (comm {H-gen}) = (by-equal-nf Eq.refl) , Eq.refl
  h-wd-ax (inj₁ H-cr) {u} {t} (comm {S-gen}) = (by-equal-nf Eq.refl) , Eq.refl
  h-wd-ax (inj₁ H-cr) {u} {t} (comm {ω-gen}) = (by-equal-nf Eq.refl) , Eq.refl
  h-wd-ax (inj₁ H-cr) {u} {t} (comm {X-gen}) = (by-equal-nf Eq.refl) , Eq.refl
  h-wd-ax (inj₂ tt) {u} {t} order-ω = (by-equal-nf Eq.refl) , Eq.refl
  h-wd-ax (inj₂ tt) {u} {t} order-S = (by-equal-nf Eq.refl) , Eq.refl
  h-wd-ax (inj₂ tt) {u} {t} order-H = (by-equal-nf Eq.refl) , Eq.refl
  h-wd-ax (inj₂ tt) {u} {t} order-SH = (by-equal-nf Eq.refl) , Eq.refl
  h-wd-ax (inj₂ tt) {u} {t} (comm {H-gen}) = (by-equal-nf Eq.refl) , Eq.refl
  h-wd-ax (inj₂ tt) {u} {t} (comm {S-gen}) = (by-equal-nf Eq.refl) , Eq.refl
  h-wd-ax (inj₂ tt) {u} {t} (comm {ω-gen}) = (by-equal-nf Eq.refl) , Eq.refl
  h-wd-ax (inj₂ tt) {u} {t} (comm {X-gen}) = (by-equal-nf Eq.refl) , Eq.refl
  h-wd-ax (inj₁ HS-cr) {u} {t} def-X = (by-equal-nf Eq.refl) , Eq.refl
  h-wd-ax (inj₁ H-cr) {u} {t} def-X = (by-equal-nf Eq.refl) , Eq.refl
  h-wd-ax (inj₂ tt) {u} {t} def-X = (by-equal-nf Eq.refl) , Eq.refl
  
  open PP _===_

  lemma-ω : ∀ w → w • ω ≈ ω • w
  lemma-ω [ x ]ʷ = sym (axiom comm)
  lemma-ω ε = trans left-unit (sym right-unit)
  lemma-ω (w • v) = trans assoc (trans (cong refl (lemma-ω v)) (trans (sym assoc) (trans (cong (lemma-ω w) refl) assoc)))

  lemma-ω^n : ∀ n w → w • ω ^ n ≈ ω ^ n • w
  lemma-ω^n zero w = trans right-unit (sym left-unit)
  lemma-ω^n (₁₊ n@zero) w = begin
    w • ω ^ ₁₊ n ≈⟨ sym right-unit ⟩
    (w • ω) • ω ^ n ≈⟨ cong (lemma-ω w) refl ⟩
    (ω • w) • ω ^ n ≈⟨ assoc ⟩
    ω • w • ω ^ n ≈⟨ cong refl (lemma-ω^n n w) ⟩
    ω • ω ^ n • w ≈⟨ cong refl left-unit ⟩
    ω ^ ₁₊ n • w ∎
    where
    open SR word-setoid

  lemma-ω^n (₁₊ n@(₁₊ n')) w = begin
    w • ω ^ ₁₊ n ≈⟨ sym assoc ⟩
    (w • ω) • ω ^ n ≈⟨ cong (lemma-ω w) refl ⟩
    (ω • w) • ω ^ n ≈⟨ assoc ⟩
    ω • w • ω ^ n ≈⟨ cong refl (lemma-ω^n n w) ⟩
    ω • ω ^ n • w ≈⟨ sym assoc ⟩
    (ω • ω ^ n) • w ≈⟨ refl ⟩
    ω ^ ₁₊ n • w ∎
    where
    open SR word-setoid


  lemma-X^2 : X ^ 2 ≈ ε
  lemma-X^2 = begin
    X ^ 2 ≈⟨ cong (axiom def-X) (axiom def-X) ⟩
    (H • S • S • H) ^ 2 ≈⟨ by-assoc Eq.refl ⟩
    (H • S • S) • (H • H) • S • S • H ≈⟨ cong refl (cong (axiom order-H) refl) ⟩
    (H • S • S) • ε • S • S • H ≈⟨ cong refl left-unit ⟩
    (H • S • S) • S • S • H ≈⟨ by-assoc Eq.refl ⟩
    H • (S • S • S • S) • H ≈⟨ cong refl (cong (axiom order-S) refl) ⟩
    H • ε • H ≈⟨ cong refl left-unit ⟩
    H • H ≈⟨ axiom order-H ⟩
    ε ∎
    where
    open SR word-setoid

  lemma-SX^2 : (S • X) ^ 2 ≈ ω ^ 2
  lemma-SX^2 = begin
    (S • X) ^ 2 ≈⟨ cong (cong refl (axiom def-X)) (cong refl (axiom def-X)) ⟩
    (S • (H • S • S • H)) ^ 2 ≈⟨ by-assoc Eq.refl ⟩
    (S • H • S) • (S • H • S • H • S) • S • H ≈⟨ cong refl (cong refl (trans (sym left-unit) (cong (sym (axiom order-H)) refl))) ⟩
    (S • H • S) • (S • H • S • H • S) • (H • H) • S • H ≈⟨ by-assoc Eq.refl ⟩
    (S • H • S) • (S • H) ^ 3 • H • S • H ≈⟨ cong refl (cong (axiom order-SH) refl) ⟩
    (S • H • S) • ω • H • S • H ≈⟨ cong refl (sym (lemma-ω (H • S • H))) ⟩
    (S • H • S) • (H • S • H) • ω ≈⟨ by-assoc Eq.refl ⟩
    (S • H) ^ 3 • ω ≈⟨ cong (axiom order-SH) refl ⟩
    ω ^ 2 ∎
    where
    open SR word-setoid

  f-wd-ax : ∀ {w v} → w ===₀ v → (f *) w ≈ (f *) v
  f-wd-ax {w} {v} M.order-ω = axiom order-ω
  f-wd-ax {w} {v} M.order-S = axiom order-S
  f-wd-ax {w} {v} M.order-X = lemma-X^2
  f-wd-ax {w} {v} M.order-SX = lemma-SX^2
  f-wd-ax {w} {v} (M.comm {M.X-gen}) = sym (lemma-ω X)
  f-wd-ax {w} {v} (M.comm {M.S-gen}) = axiom comm
  f-wd-ax {w} {v} (M.comm {M.ω-gen}) = refl

  [_]ₒ : C → Word MA
  [ HS-cr ]ₒ = H • S
  [ H-cr ]ₒ = H

  [_] : C ⊎ ⊤ → Word MA
  [_] = [_,_] [_]ₒ (λ v → ε)

  lemma-HS : H • S ≈ ω • S ^ 3 • H • S ^ 3 • H
  lemma-HS = begin
    H • S ≈⟨ trans (sym right-unit) (sym (cong refl (axiom order-H))) ⟩
    (H • S) • H • H ≈⟨ by-assoc Eq.refl ⟩
    (H • S • H) • H ≈⟨ cong refl (trans (sym left-unit) (sym (cong (axiom order-S) refl))) ⟩
    (H • S • H) • S ^ 4 • H ≈⟨ by-assoc Eq.refl ⟩
    H • (S • H • S) • S ^ 3 • H ≈⟨ cong refl (cong refl (trans (sym left-unit) (cong (sym (axiom order-H)) refl))) ⟩
    H • (S • H • S) • H ^ 2 • S ^ 3 • H ≈⟨ trans (sym left-unit) (sym (cong (axiom order-S) refl)) ⟩
    S ^ 4 • H • (S • H • S) • H ^ 2 • S ^ 3 • H ≈⟨ by-assoc Eq.refl ⟩
    (S ^ 3 • (S • H) ^ 3) • H • S ^ 3 • H ≈⟨ cong (cong refl (axiom order-SH)) refl ⟩
    (S ^ 3 • ω) • H • S ^ 3 • H ≈⟨ cong (lemma-ω (S ^ 3)) refl ⟩
    (ω • S ^ 3) • H • S ^ 3 • H ≈⟨ assoc ⟩
    ω • S ^ 3 • H • S ^ 3 • H ∎
    where
    open SR word-setoid

  lemma-HS' : H • S ≈ ω • S ^ 3 • X • H • S • H
  lemma-HS' = begin
    H • S ≈⟨ lemma-HS ⟩
    ω • S ^ 3 • H • S ^ 3 • H ≈⟨ by-assoc Eq.refl ⟩
    (ω • S ^ 3 • H • S ^ 2) • S • H ≈⟨ cong refl (trans (sym left-unit) (cong (sym (axiom order-H)) refl)) ⟩
    (ω • S ^ 3 • H • S ^ 2) • (H • H) • S • H ≈⟨ by-assoc Eq.refl ⟩
    (ω • S ^ 3) • (H • S • S • H) • H • S • H ≈⟨ cong refl (cong (sym (axiom def-X)) refl) ⟩
    (ω • S ^ 3) • X • H • S • H ≈⟨ by-assoc Eq.refl ⟩
    ω • S ^ 3 • X • H • S • H ∎
    where
    open SR word-setoid

  lemma-HSS : (H • S) • S ≈ X • H
  lemma-HSS = begin
    (H • S) • S ≈⟨ cong refl (trans (sym right-unit) (cong refl (sym (axiom order-H)))) ⟩
    (H • S) • S • H • H ≈⟨ by-assoc Eq.refl ⟩
    (H • S • S • H) • H ≈⟨ cong (sym (axiom def-X)) refl ⟩
    X • H ∎
    where
    open SR word-setoid

  lemma-HSH : (H • S • H) • H ≈ (ω • S ^ 3 • X) • H • S • H
  lemma-HSH = begin
    (H • S • H) • H ≈⟨ by-assoc Eq.refl ⟩
    H • S • H • H ≈⟨ cong refl (trans (cong refl (axiom order-H)) right-unit) ⟩
    H • S ≈⟨ lemma-HS' ⟩
    ω • S ^ 3 • X • H • S • H ≈⟨ by-assoc Eq.refl ⟩
    (ω • S ^ 3 • X) • H • S • H ∎
    where
    open SR word-setoid

  lemma-HSH' : (H • S) • H ≈ (ω • S ^ 3 • X) • H • S
  lemma-HSH' = begin
    (H • S) • H ≈⟨ cong lemma-HS' refl ⟩
    (ω • S ^ 3 • X • H • S • H) • H ≈⟨ by-assoc Eq.refl ⟩
    (ω • S ^ 3 • X • H • S) • H • H ≈⟨ trans (cong refl (axiom order-H)) right-unit ⟩
    (ω • S ^ 3 • X • H • S) ≈⟨ by-assoc Eq.refl ⟩
    (ω • S ^ 3 • X) • H • S ∎
    where
    open SR word-setoid

  lemma-HSX : (H • S) • X ≈ (ω ^ 2 • S ^ 2 • X) • H • S
  lemma-HSX = begin
    (H • S) • X ≈⟨ cong lemma-HS' refl ⟩
    (ω • S ^ 3 • X • H • S • H) • X ≈⟨ cong refl (axiom def-X) ⟩
    (ω • S ^ 3 • X • H • S • H) • (H • S • S • H) ≈⟨ by-assoc Eq.refl ⟩
    (ω • S ^ 3 • X • H • S) • (H • H) • (S • S • H) ≈⟨ cong refl (trans (cong (axiom order-H) refl) left-unit) ⟩
    (ω • S ^ 3 • X • H • S) • (S • S • H) ≈⟨ cong (cong refl (cong refl (cong (axiom def-X) refl))) refl ⟩
    (ω • S ^ 3 • (H • S • S • H) • H • S) • (S • S • H) ≈⟨ by-assoc Eq.refl ⟩
    (ω • S ^ 3 • H • S • S) • (H • H) • S • (S • S • H) ≈⟨ cong refl (trans (cong (axiom order-H) refl) left-unit) ⟩
    (ω • S ^ 3 • H • S • S) • S • (S • S • H) ≈⟨ by-assoc Eq.refl ⟩
    (ω • S ^ 3 • H • S) • (S • S • S • S) • H ≈⟨ cong refl (trans (cong (axiom order-S) refl) left-unit) ⟩
    (ω • S ^ 3 • H • S) • H ≈⟨ by-assoc Eq.refl ⟩
    (ω • S ^ 3) • (H • S) • H ≈⟨ cong refl lemma-HSH' ⟩
    (ω • S ^ 3) • (ω • S ^ 3 • X) • H • S ≈⟨ by-assoc Eq.refl ⟩
    ω • (S ^ 3 • ω) • S ^ 3 • X • H • S ≈⟨ cong refl (cong (lemma-ω (S ^ 3)) refl) ⟩
    ω • (ω • S ^ 3) • S ^ 3 • X • H • S ≈⟨ by-assoc Eq.refl ⟩
    ω ^ 2 • S ^ 2 • S ^ 4 • X • H • S ≈⟨ cong refl (cong refl (trans (cong (axiom order-S) refl) left-unit)) ⟩
    ω ^ 2 • S ^ 2 • X • H • S ≈⟨ by-assoc Eq.refl ⟩
    (ω ^ 2 • S ^ 2 • X) • H • S ∎
    where
    open SR word-setoid

  lemma-HX : H • X ≈ (S • S) • H
  lemma-HX = begin
    H • X ≈⟨ cong refl (axiom def-X) ⟩
    H • H • S • S • H ≈⟨ by-assoc Eq.refl ⟩
    (H • H) • S • S • H ≈⟨ trans (cong (axiom order-H) refl) left-unit ⟩
    S • S • H ≈⟨ sym assoc ⟩
    (S • S) • H ∎
    where
    open SR word-setoid

  h-hyp : ∀ c b → [ c ] • [ b ]ʷ ≈ (f *) (h c b .proj₁) • [ h c b .proj₂ ]
  h-hyp (inj₁ HS-cr) H-gen = lemma-HSH'
  h-hyp (inj₁ HS-cr) S-gen = lemma-HSS
  h-hyp (inj₁ HS-cr) ω-gen = lemma-ω [ inj₁ HS-cr ]
  h-hyp (inj₁ H-cr) H-gen = trans (axiom order-H) (sym right-unit)
  h-hyp (inj₁ H-cr) S-gen = sym left-unit
  h-hyp (inj₁ H-cr) ω-gen = sym (axiom comm)
  h-hyp (inj₂ tt) H-gen = refl
  h-hyp (inj₂ tt) S-gen = trans left-unit (sym right-unit)
  h-hyp (inj₂ tt) ω-gen = trans left-unit (sym right-unit)
  h-hyp (inj₁ HS-cr) X-gen = lemma-HSX
  h-hyp (inj₁ H-cr) X-gen = lemma-HX
  h-hyp (inj₂ tt) X-gen = trans left-unit (sym right-unit)

  module ca = CA.Data (M._===_) _===_ CT (inj₂ tt) f h [_]
  module aat = ca.Assumptions-And-Theorems h=⁻¹f-gen h-wd-ax f-wd-ax _≈_.refl h-hyp
  open aat using (nfp ; nfp') public
  
  open PP.NFProperty (nfp (M.nfp M0.nfp)) renaming (by-equal-nf to by-nf) using ()

  hcme : ∀ c m → ∃ \ w → ∃ \ c' → ((h **) (inj₁ c) (f m)) ≡ (w , inj₁ c')
  hcme HS-cr M.X-gen = M.ω ^ 2 • M.S ^ 2 • M.X , HS-cr , Eq.refl
  hcme HS-cr M.S-gen = M.X , H-cr , Eq.refl
  hcme HS-cr M.ω-gen = M.ω , HS-cr , Eq.refl
  hcme H-cr M.X-gen = M.S • M.S , H-cr , Eq.refl
  hcme H-cr M.S-gen = ε , HS-cr , Eq.refl
  hcme H-cr M.ω-gen = M.ω , H-cr , Eq.refl
  
  htme : ∀ m → ((h **) (inj₂ tt) (f m)) ≡ ([ m ]ʷ , inj₂ tt)
  htme M.X-gen = Eq.refl
  htme M.S-gen = Eq.refl
  htme M.ω-gen = Eq.refl

  htme~ : ∀ (m : M) → ([ m ]ʷ , I) ~ ((h **) I (f m))
  htme~ M.X-gen = _≈₀_.refl , Eq.refl
  htme~ M.S-gen = _≈₀_.refl , Eq.refl
  htme~ M.ω-gen = _≈₀_.refl , Eq.refl

  [_]ₓ = f *

  hcme~ : ∀ (c : C) (m : M) → let (w' , c' , p) = hcme c m in ([ c ]ₒ • f m) ≈ ([ w' ]ₓ • [ c' ]ₒ)
  hcme~ HS-cr M.X-gen = by-nf Eq.refl
  hcme~ HS-cr M.S-gen = by-nf Eq.refl
  hcme~ HS-cr M.ω-gen = by-nf Eq.refl
  hcme~ H-cr M.X-gen = by-nf Eq.refl
  hcme~ H-cr M.S-gen = by-nf Eq.refl
  hcme~ H-cr M.ω-gen = by-nf Eq.refl

  ca' : CosetNF-CT-Assumptions-And-Theorems-Packed M._===_ _===_
  ca' = record
          { C = C
          ; f = f
          ; h = h
          ; [_]ₒ = [_]ₒ
          ; hcme = hcme
          ; htme = htme
          ; htme~ = htme~
          ; hcme~ = hcme~
          ; h-wd-ax = h-wd-ax
          ; f-wd-ax = f-wd-ax
          ; h=ract = h-hyp
          }

module MB where
  data Gen : Set where
    T-gen : Gen
    X-gen : Gen
    S-gen : Gen
    ω-gen : Gen

  T : Word Gen
  T = [ T-gen ]ʷ

  X : Word Gen
  X = [ X-gen ]ʷ

  S : Word Gen
  S = [ S-gen ]ʷ

  ω : Word Gen
  ω = [ ω-gen ]ʷ

  infix 4 _===_
  data _===_ : WRel Gen where
    order-ω : ω ^ 8 === ε
    order-T : T ^ 2 === S
    order-S : S ^ 4 === ε
    order-X : X ^ 2 === ε
    order-TX : (T • X) ^ 2 === ω
    comm : ∀ {gen} → ω • [ gen ]ʷ === [ gen ]ʷ • ω


  open PB (M._===_) renaming (Alphabet to M ; _===_ to _===₀_ ; _≈_ to _≈₀_) using ()
  open NFProperty (M.nfp M0.nfp) using (by-equal-nf)
  open PB _===_ renaming (Alphabet to MA) using (_≈_)

  open _≈_

  f : M → Word MA
  f M.X-gen = X
  f M.S-gen = S
  f M.ω-gen = ω

  data C : Set where
    T-cr : C

  CT = C ⊎ ⊤

  h : CT → MA → Word M × CT
  h (inj₁ T-cr) T-gen = M.S , (inj₂ tt)
  h (inj₁ T-cr) X-gen = M.X • M.ω • M.S ^ 3 , (inj₁ T-cr)
  h (inj₁ T-cr) S-gen = M.S , (inj₁ T-cr)
  h (inj₁ T-cr) ω-gen = M.ω , (inj₁ T-cr)
  h (inj₂ tt) T-gen = ε , (inj₁ T-cr)
  h (inj₂ tt) X-gen = M.X , (inj₂ tt)
  h (inj₂ tt) S-gen = M.S , (inj₂ tt)
  h (inj₂ tt) ω-gen = M.ω , (inj₂ tt)

  infix 4 _~_
  _~_ = Pointwise _≈₀_ (_≡_ {A = CT})

  h=⁻¹f-gen : ∀ x → ([ x ]ʷ , (inj₂ tt)) ~ ((h **) (inj₂ tt) (f x)) 
  h=⁻¹f-gen M.X-gen = _≈₀_.refl , Eq.refl
  h=⁻¹f-gen M.S-gen = _≈₀_.refl , Eq.refl
  h=⁻¹f-gen M.ω-gen = _≈₀_.refl , Eq.refl

  h-wd-ax : ∀ c {u t} → u === t → (h **) c u ~ (h **) c t
  h-wd-ax (inj₁ T-cr) {u} {t} order-ω = (by-equal-nf Eq.refl) , Eq.refl
  h-wd-ax (inj₁ T-cr) {u} {t} order-T = (by-equal-nf Eq.refl) , Eq.refl
  h-wd-ax (inj₁ T-cr) {u} {t} order-S = (by-equal-nf Eq.refl) , Eq.refl
  h-wd-ax (inj₁ T-cr) {u} {t} order-X = (by-equal-nf Eq.refl) , Eq.refl
  h-wd-ax (inj₁ T-cr) {u} {t} order-TX = (by-equal-nf Eq.refl) , Eq.refl
  h-wd-ax (inj₁ T-cr) {u} {t} (comm {T-gen}) = (by-equal-nf Eq.refl) , Eq.refl
  h-wd-ax (inj₁ T-cr) {u} {t} (comm {X-gen}) = (by-equal-nf Eq.refl) , Eq.refl
  h-wd-ax (inj₁ T-cr) {u} {t} (comm {S-gen}) = (by-equal-nf Eq.refl) , Eq.refl
  h-wd-ax (inj₁ T-cr) {u} {t} (comm {ω-gen}) = (by-equal-nf Eq.refl) , Eq.refl
  h-wd-ax (inj₂ tt) {u} {t} order-ω = (by-equal-nf Eq.refl) , Eq.refl
  h-wd-ax (inj₂ tt) {u} {t} order-T = (by-equal-nf Eq.refl) , Eq.refl
  h-wd-ax (inj₂ tt) {u} {t} order-S = (by-equal-nf Eq.refl) , Eq.refl
  h-wd-ax (inj₂ tt) {u} {t} order-X = (by-equal-nf Eq.refl) , Eq.refl
  h-wd-ax (inj₂ tt) {u} {t} order-TX = (by-equal-nf Eq.refl) , Eq.refl
  h-wd-ax (inj₂ tt) {u} {t} (comm {T-gen}) = (by-equal-nf Eq.refl) , Eq.refl
  h-wd-ax (inj₂ tt) {u} {t} (comm {X-gen}) = (by-equal-nf Eq.refl) , Eq.refl
  h-wd-ax (inj₂ tt) {u} {t} (comm {S-gen}) = (by-equal-nf Eq.refl) , Eq.refl
  h-wd-ax (inj₂ tt) {u} {t} (comm {ω-gen}) = (by-equal-nf Eq.refl) , Eq.refl

  open PP _===_

  lemma-ω : ∀ w → w • ω ≈ ω • w
  lemma-ω [ x ]ʷ = sym (axiom comm)
  lemma-ω ε = trans left-unit (sym right-unit)
  lemma-ω (w • v) = trans assoc (trans (cong refl (lemma-ω v)) (trans (sym assoc) (trans (cong (lemma-ω w) refl) assoc)))

  lemma-ω^n : ∀ n w → w • ω ^ n ≈ ω ^ n • w
  lemma-ω^n zero w = trans right-unit (sym left-unit)
  lemma-ω^n (₁₊ n@zero) w = begin
    w • ω ^ ₁₊ n ≈⟨ sym right-unit ⟩
    (w • ω) • ω ^ n ≈⟨ cong (lemma-ω w) refl ⟩
    (ω • w) • ω ^ n ≈⟨ assoc ⟩
    ω • w • ω ^ n ≈⟨ cong refl (lemma-ω^n n w) ⟩
    ω • ω ^ n • w ≈⟨ cong refl left-unit ⟩
    ω ^ ₁₊ n • w ∎
    where
    open SR word-setoid

  lemma-ω^n (₁₊ n@(₁₊ n')) w = begin
    w • ω ^ ₁₊ n ≈⟨ sym assoc ⟩
    (w • ω) • ω ^ n ≈⟨ cong (lemma-ω w) refl ⟩
    (ω • w) • ω ^ n ≈⟨ assoc ⟩
    ω • w • ω ^ n ≈⟨ cong refl (lemma-ω^n n w) ⟩
    ω • ω ^ n • w ≈⟨ sym assoc ⟩
    (ω • ω ^ n) • w ≈⟨ refl ⟩
    ω ^ ₁₊ n • w ∎
    where
    open SR word-setoid


  lemma-T^8 : T ^ 8 ≈ ε
  lemma-T^8 = begin
    T ^ 8 ≈⟨ by-assoc Eq.refl ⟩
    (T ^ 2) • (T ^ 2) • (T ^ 2) • (T ^ 2) ≈⟨ cong (axiom order-T) (cong (axiom order-T) (cong (axiom order-T) (axiom order-T))) ⟩
    S ^ 4 ≈⟨ axiom order-S ⟩
    ε ∎
    where
    open SR word-setoid

  lemma-XT : (X • T) ^ 2 ≈ ω
  lemma-XT = begin
    (X • T) ^ 2 ≈⟨ trans (sym left-unit) (cong (sym lemma-T^8) refl) ⟩
    (T ^ 8 • (X • T) ^ 2) ≈⟨ by-assoc Eq.refl ⟩
    T ^ 7 • (T • X) ^ 2 • T ≈⟨ cong refl (cong (axiom order-TX) refl) ⟩
    T ^ 7 • ω • T ≈⟨ cong refl (sym (lemma-ω T)) ⟩
    T ^ 7 • T • ω ≈⟨ by-assoc Eq.refl ⟩
    T ^ 8 • ω ≈⟨ cong lemma-T^8 refl ⟩
    ε • ω ≈⟨ left-unit ⟩
    ω ∎
    where
    open SR word-setoid

  lemma-SX : (S • X) ^ 2 ≈ ω ^ 2
  lemma-SX = begin
    (S • X) ^ 2 ≈⟨ cong (sym (cong (axiom order-T) refl)) (sym (cong (axiom order-T) refl)) ⟩
    (T ^ 2 • X) ^ 2 ≈⟨ by-assoc Eq.refl ⟩
    T • T • X • T • T • X ≈⟨ cong refl (trans (sym left-unit) (cong (sym (axiom order-X)) refl)) ⟩
    T • (X • X) • T • X • T • T • X ≈⟨ by-assoc Eq.refl ⟩
    T • X • (X • T) ^ 2 • T • X ≈⟨ cong refl (cong refl (cong lemma-XT refl)) ⟩
    T • X • ω • T • X ≈⟨ cong refl (cong refl (sym (lemma-ω (T • X)))) ⟩
    T • X • (T • X) • ω ≈⟨ by-assoc Eq.refl ⟩
    (T • X) ^ 2 • ω ≈⟨ cong (axiom order-TX) refl ⟩
    ω ^ 2 ∎
    where
    open SR word-setoid


  lemma-TX : T • X ≈ (X • ω • S ^ 3) • T
  lemma-TX = begin
    T • X ≈⟨ trans (sym left-unit) (cong (sym (axiom order-X)) refl) ⟩
    (X ^ 2) • T • X ≈⟨ trans (sym right-unit) (sym (cong refl lemma-T^8)) ⟩
    ((X ^ 2) • T • X) • T ^ 8 ≈⟨ by-assoc Eq.refl ⟩
    X • (X • T) ^ 2  • T ^ 7 ≈⟨ cong refl (cong lemma-XT refl) ⟩
    X • ω • T ^ 7 ≈⟨ by-assoc Eq.refl ⟩
    (X • ω • T ^ 2 • T ^ 2 • T ^ 2) • T ≈⟨ cong (cong refl (cong refl (cong (axiom order-T) (cong (axiom order-T) (axiom order-T))))) refl ⟩
    (X • ω • S ^ 3) • T ∎
    where
    open SR word-setoid


  lemma-TS : T • S ≈ S • T
  lemma-TS = begin
    T • S ≈⟨ cong refl (sym (axiom order-T))⟩
    T • T ^ 2 ≈⟨ by-assoc Eq.refl ⟩
    T ^ 2 • T ≈⟨ cong (axiom order-T) refl ⟩
    S • T ∎
    where
    open SR word-setoid

  f-wd-ax : ∀ {w v} → w ===₀ v → (f *) w ≈ (f *) v
  f-wd-ax {w} {v} M.order-ω = axiom order-ω
  f-wd-ax {w} {v} M.order-S = axiom order-S
  f-wd-ax {w} {v} M.order-X = axiom order-X
  f-wd-ax {w} {v} M.order-SX = lemma-SX
  f-wd-ax {w} {v} (M.comm {M.X-gen}) = axiom comm
  f-wd-ax {w} {v} (M.comm {M.S-gen}) = axiom comm
  f-wd-ax {w} {v} (M.comm {M.ω-gen}) = refl

  [_]ₒ : C → Word MA
  [ T-cr ]ₒ = T

  [_] : C ⊎ ⊤ → Word MA
  [_] = [_,_] [_]ₒ (λ v → ε)

  h-hyp : ∀ c b → [ c ] • [ b ]ʷ ≈ (f *) (h c b .proj₁) • [ h c b .proj₂ ]
  h-hyp (inj₁ T-cr) T-gen = trans (axiom order-T) (sym right-unit)
  h-hyp (inj₁ T-cr) X-gen = lemma-TX
  h-hyp (inj₁ T-cr) S-gen = lemma-TS
  h-hyp (inj₁ T-cr) ω-gen = sym (axiom comm)
  h-hyp (inj₂ tt) T-gen = refl
  h-hyp (inj₂ tt) X-gen = trans left-unit (sym right-unit)
  h-hyp (inj₂ tt) S-gen = trans left-unit (sym right-unit)
  h-hyp (inj₂ tt) ω-gen = trans left-unit (sym right-unit)

  module ca = CA.Data (M._===_) _===_ CT (inj₂ tt) f h [_]
  module aat = ca.Assumptions-And-Theorems h=⁻¹f-gen h-wd-ax f-wd-ax _≈_.refl h-hyp
  open aat using (nfp ; nfp') public
  
  open PP.NFProperty (nfp (M.nfp M0.nfp)) renaming (by-equal-nf to by-nf) using ()

  I : CT
  I = inj₂ tt

  hcme : ∀ c m → ∃ \ w → ∃ \ c' → ((h **) (inj₁ c) (f m)) ≡ (w , inj₁ c')
  hcme T-cr M.X-gen = M.X • M.ω • M.S ^ 3 , T-cr , Eq.refl
  hcme T-cr M.S-gen = M.S , T-cr , Eq.refl
  hcme T-cr M.ω-gen = M.ω , T-cr , Eq.refl
  
  htme : ∀ m → ((h **) (inj₂ tt) (f m)) ≡ ([ m ]ʷ , inj₂ tt)
  htme M.X-gen = Eq.refl
  htme M.S-gen = Eq.refl
  htme M.ω-gen = Eq.refl

  htme~ : ∀ (m : M) → ([ m ]ʷ , I) ~ ((h **) I (f m))
  htme~ M.X-gen = _≈₀_.refl , Eq.refl
  htme~ M.S-gen = _≈₀_.refl , Eq.refl
  htme~ M.ω-gen = _≈₀_.refl , Eq.refl
  
  [_]ₓ = f *

  hcme~ : ∀ (c : C) (m : M) → let (w' , c' , p) = hcme c m in ([ c ]ₒ • f m) ≈ ([ w' ]ₓ • [ c' ]ₒ)
  hcme~ T-cr M.X-gen = by-nf Eq.refl
  hcme~ T-cr M.S-gen = by-nf Eq.refl
  hcme~ T-cr M.ω-gen = by-nf Eq.refl

  ca' : CosetNF-CT-Assumptions-And-Theorems-Packed M._===_ _===_
  ca' = record
          { C = C
          ; f = f
          ; h = h
          ; [_]ₒ = [_]ₒ
          ; hcme = hcme
          ; htme = htme
          ; htme~ = htme~
          ; hcme~ = hcme~
          ; h-wd-ax = h-wd-ax
          ; f-wd-ax = f-wd-ax
          ; h=ract = h-hyp
          }

module CliffordT1 where

  data Gen : Set where
    T-gen : Gen
    H-gen : Gen
    S-gen : Gen
    ω-gen : Gen

  T : Word Gen
  T = [ T-gen ]ʷ

  H : Word Gen
  H = [ H-gen ]ʷ

  S : Word Gen
  S = [ S-gen ]ʷ

  ω : Word Gen
  ω = [ ω-gen ]ʷ

  X : Word Gen
  X = H • S • S • H

  infix 4 _===_
  data _===_ : WRel Gen where
    order-ω : ω ^ 8 === ε
    order-T : T ^ 2 === S
    order-S : S ^ 4 === ε
    order-H : H ^ 2 === ε
    order-SH : (S • H) ^ 3 === ω
    order-TX : (T • X) ^ 2 === ω
    comm : ∀ {gen} → ω • [ gen ]ʷ === [ gen ]ʷ • ω


  amalt1 : AmalDataNF M.Gen MB._===_ MA._===_
  amalt1 = record { P₀ = M._===_ ;
    CA₁ = MB.ca' ;
    CA₂ = MA.ca' }

  open ANF MB._===_  MA._===_ amalt1 using (nfp ; nfp') public

  f : Gen → Word (MB.Gen ⊎ MA.Gen)
  f T-gen = [ MB.T ]ₗ
  f H-gen = [ MA.H ]ᵣ
  f S-gen = [ MB.S ]ₗ
  f ω-gen = [ MB.ω ]ₗ

  g : (MB.Gen ⊎ MA.Gen) → Word Gen
  g (inj₁ MB.T-gen) = T
  g (inj₁ MB.X-gen) = X
  g (inj₁ MB.S-gen) = S
  g (inj₁ MB.ω-gen) = ω
  g (inj₂ MA.H-gen) = H
  g (inj₂ MA.X-gen) = X
  g (inj₂ MA.S-gen) = S
  g (inj₂ MA.ω-gen) = ω

  mypres = MB._===_ * MA._===_ ⋆ CosetNF-CT-Assumptions-And-Theorems-Packed.f MB.ca' ⋆ CosetNF-CT-Assumptions-And-Theorems-Packed.f MA.ca'
  
  open PB _===_ renaming (_===_ to _===₁_ ; _≈_ to _≈₁_) using ()
  open PP _===_ using (by-assoc)
  
  open PB mypres renaming (_===_ to _===₂_ ; _≈_ to _≈₂_) using ()

  
  open NFProperty (nfp (M.nfp M0.nfp)) using (by-equal-nf)

  open import Algebra.Bundles using (Monoid)
  open import Algebra.Morphism.Structures using (module MonoidMorphisms)
  open PP _===_ renaming (•-ε-monoid to m₁ ; word-setoid to ws₁)
  open PP mypres renaming (•-ε-monoid to m₂)
  

  open import Presentation.Morphism

  f-well-defined : ∀ {w v} → w ===₁ v → (f *) w ≈₂ (f *) v
  f-well-defined {.(ω ^ 8)} {.ε} order-ω = _≈₂_.axiom (left MB.order-ω)
  f-well-defined {.(T ^ 2)} {.S} order-T = _≈₂_.axiom (left MB.order-T)
  f-well-defined {.(S ^ 4)} {.ε} order-S = _≈₂_.axiom (left MB.order-S)
  f-well-defined {.(H ^ 2)} {.ε} order-H = _≈₂_.axiom (right MA.order-H)
  f-well-defined {.((S • H) ^ 3)} {.ω} order-SH = by-equal-nf Eq.refl
  f-well-defined {.((T • X) ^ 2)} {.ω} order-TX = by-equal-nf Eq.refl
  f-well-defined {.(ω • [ T-gen ]ʷ)} {.([ T-gen ]ʷ • ω)} (comm {T-gen}) = _≈₂_.axiom (left MB.comm)
  f-well-defined {.(ω • [ H-gen ]ʷ)} {.([ H-gen ]ʷ • ω)} (comm {H-gen}) = by-equal-nf Eq.refl
  f-well-defined {.(ω • [ S-gen ]ʷ)} {.([ S-gen ]ʷ • ω)} (comm {S-gen}) = _≈₂_.axiom (left MB.comm)
  f-well-defined {.(ω • [ ω-gen ]ʷ)} {.([ ω-gen ]ʷ • ω)} (comm {ω-gen}) = _≈₂_.refl


  g-well-defined : ∀ {w v} → w ===₂ v → (g *) w ≈₁ (g *) v
  g-well-defined {.([ MB.ω ^ 8 ]ₗ)} {.([ ε ]ₗ)} (left {.(MB.ω ^ 8)} {.ε} MB.order-ω) = _≈₁_.axiom order-ω
  g-well-defined {.([ MB.T ^ 2 ]ₗ)} {.([ MB.S ]ₗ)} (left {.(MB.T ^ 2)} {.MB.S} MB.order-T) = _≈₁_.axiom order-T
  g-well-defined {.([ MB.S ^ 4 ]ₗ)} {.([ ε ]ₗ)} (left {.(MB.S ^ 4)} {.ε} MB.order-S) = _≈₁_.axiom order-S
  g-well-defined {.([ MB.X ^ 2 ]ₗ)} {.([ ε ]ₗ)} (left {.(MB.X ^ 2)} {.ε} MB.order-X) = lemma-X^2
    where
      open _≈₁_
      open PP _===₁_ renaming (by-assoc to by-assoc₁)
      lemma-X^2 : X ^ 2 ≈₁ ε
      lemma-X^2 = begin
        X ^ 2 ≈⟨ _≈₁_.refl ⟩
        (H • S • S • H) ^ 2 ≈⟨ by-assoc₁ Eq.refl ⟩
        (H • S • S) • (H • H) • S • S • H ≈⟨ cong refl (cong (axiom order-H) refl) ⟩
        (H • S • S) • ε • S • S • H ≈⟨ cong refl left-unit ⟩
        (H • S • S) • S • S • H ≈⟨ by-assoc₁ Eq.refl ⟩
        H • (S • S • S • S) • H ≈⟨ cong refl (cong (axiom order-S) refl) ⟩
        H • ε • H ≈⟨ cong refl left-unit ⟩
        H • H ≈⟨ axiom order-H ⟩
        ε ∎
        where
        open SR ws₁

  g-well-defined {.([ (MB.T • MB.X) ^ 2 ]ₗ)} {.([ MB.ω ]ₗ)} (left {.((MB.T • MB.X) ^ 2)} {.MB.ω} MB.order-TX) = _≈₁_.axiom order-TX
  g-well-defined {.([ MB.ω • [ MB.T-gen ]ʷ ]ₗ)} {.([ [ MB.T-gen ]ʷ • MB.ω ]ₗ)} (left {.(MB.ω • [ MB.T-gen ]ʷ)} {.([ MB.T-gen ]ʷ • MB.ω)} (MB.comm {MB.T-gen})) = _≈₁_.axiom comm
  g-well-defined {.([ MB.ω • [ MB.X-gen ]ʷ ]ₗ)} {.([ [ MB.X-gen ]ʷ • MB.ω ]ₗ)} (left {.(MB.ω • [ MB.X-gen ]ʷ)} {.([ MB.X-gen ]ʷ • MB.ω)} (MB.comm {MB.X-gen})) = sym (lemma-ω X)
    where
      open _≈₁_
    
      lemma-ω : ∀ w → w • ω ≈₁ ω • w
      lemma-ω [ x ]ʷ = sym (axiom comm)
      lemma-ω ε = trans left-unit (sym right-unit)
      lemma-ω (w • v) = trans assoc (trans (cong refl (lemma-ω v)) (trans (sym assoc) (trans (cong (lemma-ω w) refl) assoc)))

  g-well-defined {.([ MB.ω • [ MB.S-gen ]ʷ ]ₗ)} {.([ [ MB.S-gen ]ʷ • MB.ω ]ₗ)} (left {.(MB.ω • [ MB.S-gen ]ʷ)} {.([ MB.S-gen ]ʷ • MB.ω)} (MB.comm {MB.S-gen})) = _≈₁_.axiom comm
  g-well-defined {.([ MB.ω • [ MB.ω-gen ]ʷ ]ₗ)} {.([ [ MB.ω-gen ]ʷ • MB.ω ]ₗ)} (left {.(MB.ω • [ MB.ω-gen ]ʷ)} {.([ MB.ω-gen ]ʷ • MB.ω)} (MB.comm {MB.ω-gen})) = _≈₁_.refl
  g-well-defined {.([ MA.ω ^ 8 ]ᵣ)} {.([ ε ]ᵣ)} (right {.(MA.ω ^ 8)} {.ε} MA.order-ω) = _≈₁_.axiom order-ω
  g-well-defined {.([ MA.S ^ 4 ]ᵣ)} {.([ ε ]ᵣ)} (right {.(MA.S ^ 4)} {.ε} MA.order-S) = _≈₁_.axiom order-S
  g-well-defined {.([ MA.H ^ 2 ]ᵣ)} {.([ ε ]ᵣ)} (right {.(MA.H ^ 2)} {.ε} MA.order-H) = _≈₁_.axiom order-H
  g-well-defined {.([ (MA.S • MA.H) ^ 3 ]ᵣ)} {.([ MA.ω ]ᵣ)} (right {.((MA.S • MA.H) ^ 3)} {.MA.ω} MA.order-SH) = _≈₁_.axiom order-SH
  g-well-defined {.([ MA.X ]ᵣ)} {.([ MA.H • MA.S • MA.S • MA.H ]ᵣ)} (right {.MA.X} {.(MA.H • MA.S • MA.S • MA.H)} MA.def-X) = _≈₁_.refl
  g-well-defined {.([ MA.ω • [ MA.H-gen ]ʷ ]ᵣ)} {.([ [ MA.H-gen ]ʷ • MA.ω ]ᵣ)} (right {.(MA.ω • [ MA.H-gen ]ʷ)} {.([ MA.H-gen ]ʷ • MA.ω)} (MA.comm {MA.H-gen})) = _≈₁_.axiom comm
  g-well-defined {.([ MA.ω • [ MA.X-gen ]ʷ ]ᵣ)} {.([ [ MA.X-gen ]ʷ • MA.ω ]ᵣ)} (right {.(MA.ω • [ MA.X-gen ]ʷ)} {.([ MA.X-gen ]ʷ • MA.ω)} (MA.comm {MA.X-gen})) = sym (lemma-ω X)
    where
      open _≈₁_
    
      lemma-ω : ∀ w → w • ω ≈₁ ω • w
      lemma-ω [ x ]ʷ = sym (axiom comm)
      lemma-ω ε = trans left-unit (sym right-unit)
      lemma-ω (w • v) = trans assoc (trans (cong refl (lemma-ω v)) (trans (sym assoc) (trans (cong (lemma-ω w) refl) assoc)))

  g-well-defined {.([ MA.ω • [ MA.S-gen ]ʷ ]ᵣ)} {.([ [ MA.S-gen ]ʷ • MA.ω ]ᵣ)} (right {.(MA.ω • [ MA.S-gen ]ʷ)} {.([ MA.S-gen ]ʷ • MA.ω)} (MA.comm {MA.S-gen})) = _≈₁_.axiom comm
  g-well-defined {.([ MA.ω • [ MA.ω-gen ]ʷ ]ᵣ)} {.([ [ MA.ω-gen ]ʷ • MA.ω ]ᵣ)} (right {.(MA.ω • [ MA.ω-gen ]ʷ)} {.([ MA.ω-gen ]ʷ • MA.ω)} (MA.comm {MA.ω-gen})) = _≈₁_.refl
  g-well-defined {.([ CosetNF-CT-Assumptions-And-Theorems-Packed.f (AmalDataNF.CA₁ amalt1) M.X-gen ]ₗ)} {.([ CosetNF-CT-Assumptions-And-Theorems-Packed.f (AmalDataNF.CA₂ amalt1) M.X-gen ]ᵣ)} (mid (amal {M.X-gen})) = _≈₁_.refl
  g-well-defined {.([ CosetNF-CT-Assumptions-And-Theorems-Packed.f (AmalDataNF.CA₁ amalt1) M.S-gen ]ₗ)} {.([ CosetNF-CT-Assumptions-And-Theorems-Packed.f (AmalDataNF.CA₂ amalt1) M.S-gen ]ᵣ)} (mid (amal {M.S-gen})) = _≈₁_.refl
  g-well-defined {.([ CosetNF-CT-Assumptions-And-Theorems-Packed.f (AmalDataNF.CA₁ amalt1) M.ω-gen ]ₗ)} {.([ CosetNF-CT-Assumptions-And-Theorems-Packed.f (AmalDataNF.CA₂ amalt1) M.ω-gen ]ᵣ)} (mid (amal {M.ω-gen})) = _≈₁_.refl

  f-left-inv-gen : ∀ x → [ x ]ʷ ≈₂ (f *) (g x)
  f-left-inv-gen (inj₁ MB.T-gen) = _≈₂_.refl
  f-left-inv-gen (inj₁ MB.X-gen) = by-equal-nf Eq.refl
  f-left-inv-gen (inj₁ MB.S-gen) = _≈₂_.refl
  f-left-inv-gen (inj₁ MB.ω-gen) = _≈₂_.refl
  f-left-inv-gen (inj₂ MA.H-gen) = _≈₂_.refl
  f-left-inv-gen (inj₂ MA.X-gen) = by-equal-nf Eq.refl
  f-left-inv-gen (inj₂ MA.S-gen) = by-equal-nf Eq.refl
  f-left-inv-gen (inj₂ MA.ω-gen) = by-equal-nf Eq.refl

  g-left-inv-gen : ∀ x → [ x ]ʷ ≈₁ (g *) (f x)
  g-left-inv-gen T-gen = _≈₁_.refl
  g-left-inv-gen H-gen = _≈₁_.refl
  g-left-inv-gen S-gen = _≈₁_.refl
  g-left-inv-gen ω-gen = _≈₁_.refl

  open MonoidMorphisms 

  Theorem-CliffordT1-iso-B*A⋆⋆ : IsMonoidIsomorphism (Monoid.rawMonoid m₁) (Monoid.rawMonoid m₂) (f *)
  Theorem-CliffordT1-iso-B*A⋆⋆ = StarIsomorphism.isMonoidIsomorphism _===_ mypres f g f-well-defined  f-left-inv-gen g-well-defined  g-left-inv-gen
  

{-
module Test where

  open NFProperty' (CliffordT1.nfp' (M.nfp' M0.nfp')) using (by-equal-nf ; nf ; inv-nf)
  open PP CliffordT1.mypres
  open PB CliffordT1.mypres

  pattern H = [ inj₂ MA.H-gen ]ʷ
  pattern T = [ inj₁ MB.T-gen ]ʷ
  pattern S = [ inj₂ MA.S-gen ]ʷ
  pattern S' = [ inj₁ MB.S-gen ]ʷ
  pattern X = [ inj₁ MB.X-gen ]ʷ
  pattern ω = [ inj₁ MB.ω-gen ]ʷ

  t :  T • T ≈ S
  t = {!(mod-assoc ∘ inv-nf ∘ nf) (X • H • T • S • H • T • S • H • S • H • T)!}

  t2 :  [ MB.T • MB.T ]ₗ ≈ [ MA.S • MA.X • MA.X • MA.H • MA.H ]ᵣ
  t2 = by-equal-nf {!(mod-assoc ∘ inv-nf ∘ nf) (H • S • H)!}

  t3 :  T • T ≈ S
  t3 = by-equal-nf Eq.refl
-}