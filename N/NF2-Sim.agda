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
open import Data.Fin.Properties using (suc-injective ; toℕ-inject₁ ; toℕ-fromℕ)
import Data.Nat.Properties as NP
open import Presentation.GroupLike
open import Presentation.Tactics hiding ([_] ; inspect)
open import Data.Nat.Primality
open import Zp.Fermats-little-theorem


open import Zp.ModularArithmetic

module N.NF2-Sim
  (p-2 : ℕ)
  (p-prime : Prime (suc (suc p-2)))
  (let open PrimeModulus' p-2 p-prime hiding (act))
  (g*@(g , g≠0) : ℤ* ₚ)
  (g-gen : ∀ ((x , _) : ℤ* ₚ) -> ∃ \ (k : ℤ ₚ-₁) -> x ≡ g ^′ toℕ k )
  where
open Primitive-Root-Modp' g* g-gen


pattern auto = Eq.refl

pattern ₀ = zero
pattern ₁ = suc ₀
pattern ₂ = suc ₁
pattern ₃ = suc ₂
pattern ₄ = 4
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


open import N.Symplectic p-2 p-prime
open import N.Symplectic-Simplified p-2 p-prime g* g-gen
import N.Symplectic-Derived p-2 p-prime as ND
open import N.Lemmas-2Qupit p-2 p-prime
open import N.Cosets p-2 p-prime
open Lemmas-2Q 2
open Symplectic
open import N.NF1 p-2 p-prime
open Normal-Form1 renaming (⟦_⟧₁ to ⟦_⟧₁' ; ⟦_⟧ₘ₊ to ⟦_⟧ₘ₊') using ()
open import N.NF1-Sim p-2 p-prime g* g-gen
open import N.Action p-2 p-prime renaming (act to dact)
open import N.Action-Sym p-2 p-prime g* g-gen

module LM2 where

  private
    variable
      n : ℕ

  
  ⟦_⟧ₚ : Postfix -> Word (Gen (₂₊ n))
  ⟦ s , mc2 , mc1 ⟧ₚ = S^ s • (H^ ₃ • CZ • H) • ⟦ mc2 ⟧ₘ₊ ↑ • ⟦ mc1 ⟧ₘ₊
  
  ⟦_⟧₂ : Cosets2 -> Word (Gen (₂₊ n))
  ⟦ case-||ₐ k p ⟧₂ = CZ^ k • ⟦ p ⟧ₚ
  ⟦ case-|| (k , _) l p ⟧₂ = CZ^ k • H^ ₃ ↑ • S^ l ↑ • ⟦ p ⟧ₚ
  ⟦ case-Ex-| nf1 mc ⟧₂ = Ex • CZ • ⟦ nf1 ⟧₁ ↑ • ⟦ mc ⟧ₘ₊
  ⟦ case-| mc nf1 ⟧₂ = CZ • ⟦ mc ⟧ₘ₊ ↑ • ⟦ nf1 ⟧₁
  ⟦ case-nf1 nf1 ⟧₂ = ⟦ nf1 ⟧₁
  ⟦ case-Ex-nf1 nf1 ⟧₂ = Ex • ⟦ nf1 ⟧₁ ↑


  module Sym  = Symplectic
  module Sym'  = Lemmas-Sym
  module SymDerived  = ND.Symplectic-Derived-Gen

  open Symplectic renaming (Gen to Gen₁ ; _QRel,_===_ to _QRel,_===₁_) using ()
  Gen₂ = Gen₁
  open Simplified-Relations renaming (_QRel,_===_ to _QRel,_===₂_) using ()
  open SymDerived renaming (Gen to Gen₃ ; _QRel,_===_ to _QRel,_===₃_) using ()

  open Symplectic-GroupLike renaming (grouplike to grouplike₁) using ()
  open Symplectic-Sim-GroupLike renaming (grouplike to grouplike₂) using ()
  open ND.Symplectic-Derived-GroupLike renaming (grouplike to grouplike₃) using ()


  open import Algebra.Bundles using (Group)
  open import Algebra.Morphism.Structures using (module GroupMorphisms)

  open GroupMorphisms

  import N.NF2 p-2 p-prime as LM2T 
  module LM2P = LM2T.LM2
  open LM2P renaming (⟦_⟧₂ to ⟦_⟧₂' ; ⟦_⟧ₚ to ⟦_⟧ₚ') using ()



  sim-of-der : ∀ {n} -> Word (Gen₂ n) -> Word (Gen₃ n)
  sim-of-der {n} = λ z → ε



  der-of-sim : ∀ {n} -> Word (Gen₂ n) -> Word (Gen₃ n)
  der-of-sim {n} = der

  lemma-der-↑ : ∀ w -> let open PB ((₁₊ n) QRel,_===₃_) in
    (der {₁₊ n} (w ↑)) ≈ (der {n} w) D.↑
  lemma-der-↑ w@([ H-gen ]ʷ) = PB.refl
  lemma-der-↑ [ S-gen ]ʷ = PB.refl
  lemma-der-↑ [ CZ-gen ]ʷ = PB.refl
  lemma-der-↑ [ x ↥ ]ʷ = PB.refl
  lemma-der-↑ ε = PB.refl
  lemma-der-↑ (w • w₁) = PB.cong (lemma-der-↑ w) (lemma-der-↑ w₁)

  lemma-der-MC : let open PB ((₁₊ n) QRel,_===₃_) in
    ∀ mc -> der ⟦ mc ⟧ₘ₊ ≈ ⟦ mc ⟧ₘ₊'
  lemma-der-MC {n} (m , c@ε) = cong (lemma-derM m) refl
    where
    open PB ((₁₊ n) QRel,_===₃_)
  lemma-der-MC {n} (m , c@(HS^ k)) = cong (lemma-derM m) ((cong refl (lemma-der k)))
    where
    open PB ((₁₊ n) QRel,_===₃_)


  lemma-der-NF1 : let open PB ((₁₊ n) QRel,_===₃_) in
    ∀ nf1 -> der ⟦ nf1 ⟧₁ ≈ ⟦ nf1 ⟧₁'
  lemma-der-NF1 {n} nf1@(s , m , ε) = begin
    der ⟦ nf1 ⟧₁ ≈⟨ cong (lemma-der s) (cong (lemma-derM m) refl) ⟩
    ⟦ nf1 ⟧₁' ∎
    where
    open PB ((₁₊ n) QRel,_===₃_)
    open PP ((₁₊ n) QRel,_===₃_)
    open SR word-setoid

  lemma-der-NF1 {n} nf1@(s , m , HS^ k) = begin
    der ⟦ nf1 ⟧₁ ≈⟨ cong (lemma-der s) (cong (lemma-derM m) (cong refl (lemma-der k))) ⟩
    ⟦ nf1 ⟧₁' ∎
    where
    open PB ((₁₊ n) QRel,_===₃_)
    open PP ((₁₊ n) QRel,_===₃_)
    open SR word-setoid

  lemma-der-Ex : let open PB ((₂₊ n) QRel,_===₃_) in
    der Ex ≈ D.Ex
  lemma-der-Ex {n} = cong (lemma-derCZ ₁) (cright (cright cong (lemma-derCZ ₁) (cright cright cong (lemma-derCZ ₁) refl)))
    where
    open PB ((₂₊ n) QRel,_===₃_)

  lemma-der-Postfix : let open PB ((₂₊ n) QRel,_===₃_) in
    ∀ pf -> der ⟦ pf ⟧ₚ ≈ ⟦ pf ⟧ₚ'
  lemma-der-Postfix {n} pf@(s , mc2 , mc1) = cong (lemma-der s) (cong (cong (sym (axiom (_QRel,_===₃_.derived-H ₃))) refl) (cong (trans (lemma-der-↑ ⟦ mc2 ⟧ₘ₊) (D.lemma-cong↑ _ _ (lemma-der-MC mc2))) (lemma-der-MC mc1)))
    where
    open PB ((₂₊ n) QRel,_===₃_)


  lemma-der-of-sim : let open PB ((₂₊ n) QRel,_===₃_) in
  
    ∀ lm -> der-of-sim ⟦ lm ⟧₂ ≈ ⟦ lm ⟧₂'
    
  lemma-der-of-sim {n} (case-||ₐ x x₁) = cong (lemma-derCZ x) (lemma-der-Postfix x₁)
    where
    open PB ((₂₊ n) QRel,_===₃_)
  lemma-der-of-sim {n} (case-|| x x₁ x₂) = cong (lemma-derCZ (x .proj₁)) (cong (sym (axiom (_QRel,_===₃_.cong↑ (_QRel,_===₃_.derived-H ₃)))) (cong ((trans (lemma-der-↑ (S^ x₁)) (D.lemma-cong↑ _ _ (lemma-der (x₁))))) (lemma-der-Postfix x₂)))
    where
    open PB ((₂₊ n) QRel,_===₃_)
  lemma-der-of-sim {n} (case-Ex-| x x₁) = cong refl (cright cong (trans (lemma-der-↑ ⟦ x ⟧₁) (D.lemma-cong↑ _ _ (lemma-der-NF1 x))) (lemma-der-MC x₁))
    where
    open PB ((₂₊ n) QRel,_===₃_)
  lemma-der-of-sim {n} (case-| x x₁) = cong refl (cong (trans (lemma-der-↑ ⟦ x ⟧ₘ₊) (D.lemma-cong↑ _ _ (lemma-der-MC x))) (lemma-der-NF1 x₁))
    where
    open PB ((₂₊ n) QRel,_===₃_)
  lemma-der-of-sim {n} (case-nf1 (s , m , c)) = lemma-der-NF1 (s , m , c)
  
  lemma-der-of-sim {n} (case-Ex-nf1 x) = cong lemma-der-Ex (trans (lemma-der-↑ ⟦ x ⟧₁) (D.lemma-cong↑ _ _ (lemma-der-NF1 x)))
    where
    open PB ((₂₊ n) QRel,_===₃_)


  open import N.Action-Lemmas p-2 p-prime

  Theorem-LM2 :

    ∀ (ps qs : Pauli 2) (t : Pauli n) ->
    sform ps qs ≡ ₁ ->
    -----------------------------------------------
    ∃ \ lm -> act ⟦ lm ⟧₂ (ps ++ t) ≡ pZ ∷ pI ∷ t ×
              act ⟦ lm ⟧₂ (qs ++ t) ≡ pX ∷ pI ∷ t

  Theorem-LM2 ps qs t cond with LM2P.Theorem-LM2 ps qs t cond
  ... | (lm , pr) = lm , claim1 , claim2
    where
    open ≡-Reasoning
    claim1 : act ⟦ lm ⟧₂ (ps ++ t) ≡ pZ ∷ pI ∷ t
    claim1 = begin
      act ⟦ lm ⟧₂ (ps ++ t) ≡⟨ auto ⟩
      dact (der-of-sim ⟦ lm ⟧₂) (ps ++ t) ≡⟨ lemma-act-cong _ _ (lemma-der-of-sim lm) ((ps ++ t)) ⟩
      dact (⟦ lm ⟧₂') (ps ++ t) ≡⟨ pr .proj₁ ⟩
      pZ ∷ pI ∷ t ∎

    claim2 : act ⟦ lm ⟧₂ (qs ++ t) ≡ pX ∷ pI ∷ t
    claim2 = begin
      act ⟦ lm ⟧₂ (qs ++ t) ≡⟨ auto ⟩
      dact (der-of-sim ⟦ lm ⟧₂) (qs ++ t) ≡⟨ lemma-act-cong _ _ (lemma-der-of-sim lm) ((qs ++ t)) ⟩
      dact (⟦ lm ⟧₂') (qs ++ t) ≡⟨ pr .proj₂ ⟩
      pX ∷ pI ∷ t ∎
