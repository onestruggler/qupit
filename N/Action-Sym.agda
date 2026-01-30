{-# OPTIONS  --safe #-}
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
open import Data.List hiding ([_] ; _++_ ; last ; head ; tail ; _∷ʳ_)
open import Data.Vec hiding ([_])
import Data.Vec as Vec
open import Data.Fin hiding (_+_ ; _-_)

open import Data.Maybe
open import Data.Sum using (_⊎_ ; inj₁ ; inj₂ ; [_,_] ; [_,_]′)
open import Data.Unit using (⊤ ; tt)
open import Data.Empty using (⊥ ; ⊥-elim)

open import Word.Base as WB hiding (wfoldl ; _*)
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
open import Data.Fin.Properties using (suc-injective ; toℕ-inject₁ ; toℕ-fromℕ ; toℕ-fromℕ< ; fromℕ<-toℕ ; toℕ<n ; fromℕ<-cong)
import Data.Nat.Properties as NP
open import Presentation.GroupLike
open import Presentation.Tactics hiding ([_])
open import Data.Nat.Primality
open import Zp.Fermats-little-theorem


open import Zp.ModularArithmetic
module N.Action-Sym
  (p-2 : ℕ)
  (p-prime : Prime (suc (suc p-2)))
  (let open PrimeModulus' p-2 p-prime hiding (act))
  (g*@(g , g≠0) : ℤ* ₚ)
  (g-gen : ∀ ((x , _) : ℤ* ₚ) -> ∃ \ (k : ℤ ₚ-₁) -> x ≡ g ^′ toℕ k )
  where
open Primitive-Root-Modp' g* g-gen

private
  variable
    n : ℕ

open import N.Symplectic p-2 p-prime
open import N.Symplectic-Derived p-2 p-prime as SD
open import N.Symplectic-Simplified p-2 p-prime g* g-gen
open import N.Lemmas-2Qupit p-2 p-prime
open Lemmas-2Q 2 hiding (lemma-CZ^k-%)
open Symplectic
open Simplified-Relations

open import N.Pauli p-2 p-prime
open import N.Iso-Sym-Derived p-2 p-prime hiding (module G1 ; module G2)
open Iso
open import Algebra.Morphism.Construct.Composition


open Symplectic renaming (Gen to Gen₁ ; _QRel,_===_ to _QRel,_===₁_) using ()
open Sim renaming (_QRel,_===_ to _QRel,_===₂_) using ()
open SymDerived renaming (Gen to Gen₃ ; _QRel,_===_ to _QRel,_===₃_) using ()

open Symplectic-GroupLike renaming (grouplike to grouplike₁) using ()
open Symplectic-Sim-GroupLike renaming (grouplike to grouplike₂) using ()
open Symplectic-Derived-GroupLike renaming (grouplike to grouplike₃) using ()


open import Algebra.Bundles using (Group)
open import Algebra.Morphism.Structures using (module GroupMorphisms)

open GroupMorphisms

Theorem-Sim-iso-Der : ∀ {n} ->
  let
  module G1 = Group-Lemmas (Gen₁ n) (n QRel,_===₁_) grouplike₁
  module G2 = Group-Lemmas (Gen₂ n) (n QRel,_===₂_) grouplike₂
  module G3 = Group-Lemmas (Gen₃ n) (n QRel,_===₃_) grouplike₃
  in
  IsGroupIsomorphism (Group.rawGroup G2.•-ε-group) (Group.rawGroup G3.•-ε-group) ((f'* {n}) ∘ id)
Theorem-Sim-iso-Der {n}  = isGroupIsomorphism PB.trans Theorem-Sym-iso-Sim' Theorem-Sym-iso-SymDerived

der : Word (Gen₂ n) -> Word (Gen₃ n)
der {n} = ((f'* {n}) ∘ id)

open import N.Action p-2 p-prime renaming (act to dact) using ()
act : ∀ {n} → Word (Gen n) → Pauli n → Pauli n
act {n} w ps = dact (der w) ps


module D = SymDerived
open import Data.Nat.DivMod


lemma-der' : let open PB ((₁₊ n) QRel,_===₃_) in
  ∀ k -> der (S ^ k) ≈ D.S ^ k
lemma-der' ₀ = PB.refl
lemma-der' ₁ = PB.refl
lemma-der' (₂₊ k) = PB.cong PB.refl (lemma-der' (₁₊ k))


lemma-der'' : ∀ k ->
  let
  open PB ((₁₊ n) QRel,_===₃_)
  k' = fromℕ< (m%n<n k p)
  in
  der (S ^ k) ≈ D.S^ k'
lemma-der'' {n} k = begin
  der (S ^ k) ≈⟨ lemma-der' k ⟩
  D.S ^ k ≈⟨ lemma-S^k-% k ⟩
  D.S ^ (k Nat.% p) ≈⟨ refl' (Eq.cong (D.S ^_) (Eq.sym ( toℕ-fromℕ< (m%n<n k p)))) ⟩
  D.S ^ toℕ k' ≈⟨ sym (axiom (D._QRel,_===_.derived-S k')) ⟩
  D.S^ k' ∎
  where
  open PB ((₁₊ n) QRel,_===₃_)
  open PP ((₁₊ n) QRel,_===₃_)
  open SR word-setoid
  k' = fromℕ< (m%n<n k p)
  open SD.Lemmas0 n

lemma-der : let open PB ((₁₊ n) QRel,_===₃_) in
  ∀ k -> der (S^ k) ≈ D.S^ k
lemma-der {n} k = begin
  der (S^ k) ≈⟨ refl ⟩
  der (S ^ toℕ k) ≈⟨ lemma-der'' (toℕ k) ⟩
  D.S^ k' ≈⟨ refl' (Eq.cong D.S^ (fromℕ<-cong (toℕ k Nat.% p) (toℕ k) (m<n⇒m%n≡m (toℕ<n k)) (m%n<n (toℕ k) p) (toℕ<n k))) ⟩
  D.S^ k'' ≈⟨ refl' (Eq.cong D.S^ (fromℕ<-toℕ k (toℕ<n k))) ⟩
  D.S^ k ∎
  where
  open PB ((₁₊ n) QRel,_===₃_)
  open PP ((₁₊ n) QRel,_===₃_)
  open SR word-setoid
  k'' : ℤ ₚ
  k'' = fromℕ< (toℕ<n k)
  k' = fromℕ< (m%n<n (toℕ k) p)
  open SD.Lemmas0 n




lemma-derH : ∀ k ->
  let
  open PB ((₁₊ n) QRel,_===₃_)
  in
  der (H^ k) ≈ D.H^ k
lemma-derH {n} ₀ = PB.sym (PB.axiom (D._QRel,_===_.derived-H ₀))
lemma-derH {n} ₁ = PB.refl
lemma-derH {n} ₂ = PB.sym (PB.axiom (D._QRel,_===_.derived-H ₂))
lemma-derH {n} ₃ = PB.sym (PB.axiom (D._QRel,_===_.derived-H ₃))



lemma-derM : let open PB ((₁₊ n) QRel,_===₃_) in
  ∀ k -> der (M k) ≈ D.M k
lemma-derM {n} k*@(k , nz) = cong (lemma-der k) (cong (lemma-derH ₁) (cong (lemma-der k⁻¹) (cong (lemma-derH ₁) (cong (lemma-der k) refl))))
  where
  open PB ((₁₊ n) QRel,_===₃_)
  open PP ((₁₊ n) QRel,_===₃_)
  open SR word-setoid
  k⁻¹ = (k* ⁻¹) .proj₁


lemma-derCZ' : let open PB ((₂₊ n) QRel,_===₃_) in
  ∀ k -> der (CZ ^ k) ≈ D.CZ ^ k
lemma-derCZ' ₀ = PB.refl
lemma-derCZ' ₁ = PB.refl
lemma-derCZ' (₂₊ k) = PB.cong PB.refl (lemma-derCZ' (₁₊ k))


lemma-derCZ'' : ∀ k ->
  let
  open PB ((₂₊ n) QRel,_===₃_)
  k' = fromℕ< (m%n<n k p)
  in
  der (CZ ^ k) ≈ D.CZ^ k'
lemma-derCZ'' {n} k = begin
  der (CZ ^ k) ≈⟨ lemma-derCZ' k ⟩
  D.CZ ^ k ≈⟨ lemma-CZ^k-% k ⟩
  D.CZ ^ (k Nat.% p) ≈⟨ refl' (Eq.cong (D.CZ ^_) (Eq.sym ( toℕ-fromℕ< (m%n<n k p)))) ⟩
  D.CZ ^ toℕ k' ≈⟨ sym (axiom (D._QRel,_===_.derived-CZ k')) ⟩
  D.CZ^ k' ∎
  where
  open PB ((₂₊ n) QRel,_===₃_)
  open PP ((₂₊ n) QRel,_===₃_)
  open SR word-setoid
  k' = fromℕ< (m%n<n k p)
  open SD.Lemmas-1 n

lemma-derCZ : let open PB ((₂₊ n) QRel,_===₃_) in
  ∀ k -> der (CZ^ k) ≈ D.CZ^ k
lemma-derCZ {n} k = begin
  der (CZ^ k) ≈⟨ refl ⟩
  der (CZ ^ toℕ k) ≈⟨ lemma-derCZ'' (toℕ k) ⟩
  D.CZ^ k' ≈⟨ refl' (Eq.cong D.CZ^ (fromℕ<-cong (toℕ k Nat.% p) (toℕ k) (m<n⇒m%n≡m (toℕ<n k)) (m%n<n (toℕ k) p) (toℕ<n k))) ⟩
  D.CZ^ k'' ≈⟨ refl' (Eq.cong D.CZ^ (fromℕ<-toℕ k (toℕ<n k))) ⟩
  D.CZ^ k ∎
  where
  open PB ((₂₊ n) QRel,_===₃_)
  open PP ((₂₊ n) QRel,_===₃_)
  open SR word-setoid
  k'' : ℤ ₚ
  k'' = fromℕ< (toℕ<n k)
  k' = fromℕ< (m%n<n (toℕ k) p)
  open SD.Lemmas0 n
