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


open import Zp.ModularArithmetic

module N.NF2-Sym
 (p-2 : ℕ) (p-prime : Prime (2+ p-2))
  where
open PrimeModulus p-2 p-prime


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
import N.Symplectic-Derived p-2 p-prime as ND
open import N.Lemmas-2Qupit p-2 p-prime
open Lemmas-2Q 2
open Symplectic
open import N.Action p-2 p-prime renaming (act to dact)
open import N.NF1-Sym p-2 p-prime

module LM2 where

  private
    variable
      n : ℕ

  open import N.Cosets p-2 p-prime
  
  ⟦_⟧ₚ : Postfix -> Word (Gen (₂₊ n))
  ⟦ s , mc2 , mc1 ⟧ₚ = S^ s • (H^ ₃ • CZ • H) • ⟦ mc2 ⟧ₘ₊ ↑ • ⟦ mc1 ⟧ₘ₊
  
  ⟦_⟧₂ : Cosets2 -> Word (Gen (₂₊ n))
  ⟦ case-||ₐ k p ⟧₂ = CZ^ k • ⟦ p ⟧ₚ
  ⟦ case-|| (k , _) l p ⟧₂ = CZ^ k • H^ ₃ ↑ • S^ l ↑ • ⟦ p ⟧ₚ
  ⟦ case-Ex-| nf1 mc ⟧₂ = Ex • CZ • ⟦ nf1 ⟧₁ ↑ • ⟦ mc ⟧ₘ₊
  ⟦ case-| mc nf1 ⟧₂ = CZ • ⟦ mc ⟧ₘ₊ ↑ • ⟦ nf1 ⟧₁
  ⟦ case-nf1 nf1 ⟧₂ = ⟦ nf1 ⟧₁
  ⟦ case-Ex-nf1 nf1 ⟧₂ = Ex • ⟦ nf1 ⟧₁ ↑



{-
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
  open LM2P renaming (⟦_⟧₂ to ⟦_⟧₂') using ()

{-

  sim-of-der : ∀ {n} -> Word (Gen₂ n) -> Word (Gen₃ n)
  sim-of-der {n} = {!!}



  der-of-sim : ∀ {n} -> Word (Gen₂ n) -> Word (Gen₃ n)
  der-of-sim {n} = der

  lemma-der-of-sim : let open PB ((₂₊ n) QRel,_===₃_) in
  
    ∀ lm -> der-of-sim ⟦ lm ⟧₂ ≈ ⟦ lm ⟧₂'
    
  lemma-der-of-sim (case-||ₐ x x₁) = {!!}
  lemma-der-of-sim (case-|| x x₁ x₂) = {!!}
  lemma-der-of-sim (case-Ex-| x x₁) = {!!}
  lemma-der-of-sim (case-| x x₁) = {!!}
  lemma-der-of-sim (case-nf1 (s , m , c)) = {!!}
  lemma-der-of-sim (case-Ex-nf1 x) = {!!}




  Theorem-LM2 :

    ∀ (ps qs : Pauli 2) (t : Pauli n) ->
    sform ps qs ≡ ₁ ->
    -----------------------------------------------
    ∃ \ lm -> act ⟦ lm ⟧₂ (ps ++ t) ≡ pZ ∷ pI ∷ t ×
              act ⟦ lm ⟧₂ (qs ++ t) ≡ pX ∷ pI ∷ t

  Theorem-LM2 ps qs t cond with LM2P.Theorem-LM2 ps qs t cond
  ... | (lm , pr) = lm , claim1 , {!!}
    where
    open ≡-Reasoning
    claim1 : act ⟦ lm ⟧₂ (ps ++ t) ≡ pZ ∷ pI ∷ t
    claim1 = begin
      act ⟦ lm ⟧₂ (ps ++ t) ≡⟨ auto ⟩
      dact (der-of-sim ⟦ lm ⟧₂) (ps ++ t) ≡⟨ {!↑ʷ x !} ⟩
      dact (⟦ lm ⟧₂') (ps ++ t) ≡⟨ {![ ↥ ↥  x ]ʷ!} ⟩
      pZ ∷ pI ∷ t ∎


{-
  sform-pIₙ-t=0 : ∀ {n} (t : Pauli n) → sform pIₙ t ≡ ₀
  sform-pIₙ-t=0 {₀} [] = auto
  sform-pIₙ-t=0 {₁₊ n} (x ∷ t) = Eq.cong₂ _+_ (sform-pI-q=0 x) (sform-pIₙ-t=0 t)


  sform-pIpI-qq'=0 : ∀ (qs : Pauli 2) t -> sform {₂₊ n} pIₙ (qs ++ t) ≡ ₀
  sform-pIpI-qq'=0 qs@(q ∷ q' ∷ []) t = begin
    sform pIₙ (qs ++ t) ≡⟨ auto ⟩
    sform1 pI q + (sform1 pI q' + sform pIₙ t) ≡⟨ Eq.cong₂ (\ xx  yy -> xx + (yy + sform pIₙ t)) (sform-pI-q=0 q)  (sform-pI-q=0 q') ⟩
    ₀ + (₀ + sform pIₙ t) ≡⟨ Eq.cong (\ xx -> ₀ + (₀ + xx)) (sform-pIₙ-t=0 t) ⟩
    ₀ + (₀ + ₀) ≡⟨ auto ⟩
    ₀ ∎
    where open ≡-Reasoning

  sform-pIpI-qq'=0' : ∀ (qs : Pauli 2) -> sform pIₙ qs ≡ ₀
  sform-pIpI-qq'=0' qs@(q ∷ q' ∷ []) = begin
    sform pIₙ qs ≡⟨ auto ⟩
    sform1 pI q + (sform1 pI q' + ₀) ≡⟨ Eq.cong₂ (\ xx yy -> xx + (yy + ₀)) (sform-pI-q=0 q)  (sform-pI-q=0 q') ⟩
    ₀ + (₀ + ₀) ≡⟨ auto ⟩
    ₀ ∎
    where open ≡-Reasoning

  open import Algebra.Properties.Ring (+-*-ring p-2)

  act-Ex : ∀ a b c d t ->
  
    act {₂₊ n} Ex ((a , b) ∷ (c , d) ∷ t) ≡ ((c , d) ∷ (a , b) ∷ t)

  act-Ex {n} a b c d t = begin
    act {₂₊ n} Ex ((a , b) ∷ (c , d) ∷ t) ≡⟨ auto ⟩
    act {₂₊ n} (CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑) ((a , b) ∷ (c , d) ∷ t) ≡⟨ auto ⟩
    act {₂₊ n} (CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑ • CZ • H ↓) ((a , b) ∷ (- d , c) ∷ t) ≡⟨ auto ⟩
    act {₂₊ n} (CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑ • CZ) ((- b , a) ∷ (- d , c) ∷ t) ≡⟨ auto ⟩
    act {₂₊ n} (CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑) ((- b , a + - d * ₁) ∷ (- d , c + - b * ₁) ∷ t) ≡⟨ Eq.cong₂ (\ xx yy -> act {₂₊ n} (CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑) ((- b , a + xx) ∷ (- d , c + yy) ∷ t)) (*-identityʳ (- d)) (*-identityʳ (- b)) ⟩
    act {₂₊ n} (CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑) ((- b , a + - d) ∷ (- d , c + - b) ∷ t) ≡⟨ auto ⟩
    act {₂₊ n} (CZ • H ↓ • H ↑ • CZ) ((- (a + - d) , - b) ∷ (- (c + - b) , - d) ∷ t) ≡⟨ auto ⟩
    act {₂₊ n} (CZ • H ↓ • H ↑) ((- (a + - d) , - b + - (c + - b) * ₁) ∷ (- (c + - b) , - d + - (a + - d) * ₁) ∷ t) ≡⟨ auto ⟩
    act {₂₊ n} (CZ) ((- (- b + - (c + - b) * ₁) , - (a + - d)) ∷ (- (- d + - (a + - d) * ₁) , - (c + - b)) ∷ t) ≡⟨ Eq.cong₂ (\ xx yy -> act {₂₊ n} (CZ) ((- (- b + xx) , - (a + - d)) ∷ (- (- d + yy) , - (c + - b)) ∷ t)) (*-identityʳ (- (c + - b))) (*-identityʳ (- (a + - d))) ⟩
    act {₂₊ n} (CZ) ((- (- b + - (c + - b)) , - (a + - d)) ∷ (- (- d + - (a + - d)) , - (c + - b)) ∷ t) ≡⟨ auto ⟩
    ((- (- b + - (c + - b)) , - (a + - d) + - (- d + - (a + - d)) * ₁) ∷ (- (- d + - (a + - d)) , - (c + - b) + - (- b + - (c + - b)) * ₁) ∷ t) ≡⟨ Eq.cong₂ (\ xx yy -> ((- (- b + - (c + - b)) , - (a + - d) + xx) ∷ (- (- d + - (a + - d)) , - (c + - b) + yy) ∷ t)) (*-identityʳ (- (- d + - (a + - d)))) (*-identityʳ (- (- b + - (c + - b)))) ⟩
    (- (- b + - (c + - b)) , - (a + - d) + - (- d + - (a + - d))) ∷ (- (- d + - (a + - d)) , - (c + - b) + - (- b + - (c + - b))) ∷ t ≡⟨ Eq.cong₂ (\ xx yy -> xx ∷ yy ∷ t) (≡×≡⇒≡ (c1 , c2)) (≡×≡⇒≡ (c3 , c4)) ⟩
    ((c , d) ∷ (a , b) ∷ t) ∎
    where
    open ≡-Reasoning
    c1 : - (- b + - (c + - b)) ≡ c
    c1 = begin
      - (- b + - (c + - b)) ≡⟨ Eq.sym (-‿+-comm (- b) (- (c + - b))) ⟩
      - - b + - - (c + - b) ≡⟨ Eq.cong₂ _+_ (-‿involutive b) (-‿involutive (c + - b)) ⟩
      b + (c + - b) ≡⟨ Eq.cong (b +_) (+-comm c (- b)) ⟩
      b + (- b + c) ≡⟨ Eq.sym (+-assoc b (- b) c) ⟩
      (b + - b) + c ≡⟨ Eq.cong (_+ c) (+-inverseʳ b) ⟩
      ₀ + c ≡⟨ +-identityˡ c ⟩
      c ∎

    c2 : - (a + - d) + - (- d + - (a + - d)) ≡ d
    c2 = begin
      - (a + - d) + - (- d + - (a + - d)) ≡⟨ Eq.cong₂ _+_ (Eq.sym (-‿+-comm a (- d))) (Eq.sym (-‿+-comm (- d) (- (a + - d)))) ⟩
      (- a + - - d) + (- - d + - - (a + - d)) ≡⟨ Eq.cong₂ _+_  (Eq.cong (- a +_) (-‿involutive d)) (Eq.cong₂ _+_ (-‿involutive d) (-‿involutive (a + - d))) ⟩
      (- a + d) + (d + (a + - d)) ≡⟨ Eq.cong₂ _+_ (+-comm (- a) d) (+-comm d (a + - d)) ⟩
      (d + - a) + ((a + - d) + d) ≡⟨ Eq.cong ((d + - a) +_) (+-assoc a (- d) d) ⟩
      (d + - a) + (a + (- d + d)) ≡⟨ Eq.cong (\ xx -> (d + - a) + (a + xx)) (+-inverseˡ d) ⟩
      (d + - a) + (a + ₀) ≡⟨ Eq.cong (\ xx -> (d + - a) + xx) (+-identityʳ a) ⟩
      (d + - a) + (a) ≡⟨ +-assoc d (- a) a ⟩
      d + (- a + a) ≡⟨ Eq.cong (d +_) (+-inverseˡ a) ⟩
      d + ₀ ≡⟨ +-identityʳ d ⟩
      d ∎


    c3 : - (- d + - (a + - d)) ≡ a
    c3 = begin
      - (- d + - (a + - d)) ≡⟨ Eq.sym (-‿+-comm (- d) (- (a + - d))) ⟩
      - - d + - - (a + - d) ≡⟨ Eq.cong₂ _+_ (-‿involutive d) (-‿involutive (a + - d)) ⟩
      d + (a + - d) ≡⟨ Eq.cong (d +_) (+-comm a (- d)) ⟩
      d + (- d + a) ≡⟨ Eq.sym (+-assoc d (- d) a) ⟩
      (d + - d) + a ≡⟨ Eq.cong (_+ a) (+-inverseʳ d) ⟩
      ₀ + a ≡⟨ +-identityˡ a ⟩
      a ∎

    c4 : - (c + - b) + - (- b + - (c + - b)) ≡ b
    c4 = begin
      - (c + - b) + - (- b + - (c + - b)) ≡⟨ Eq.cong₂ _+_ (Eq.sym (-‿+-comm c (- b))) (Eq.sym (-‿+-comm (- b) (- (c + - b)))) ⟩
      (- c + - - b) + (- - b + - - (c + - b)) ≡⟨ Eq.cong₂ _+_  (Eq.cong (- c +_) (-‿involutive b)) (Eq.cong₂ _+_ (-‿involutive b) (-‿involutive (c + - b))) ⟩
      (- c + b) + (b + (c + - b)) ≡⟨ Eq.cong₂ _+_ (+-comm (- c) b) (+-comm b (c + - b)) ⟩
      (b + - c) + ((c + - b) + b) ≡⟨ Eq.cong ((b + - c) +_) (+-assoc c (- b) b) ⟩
      (b + - c) + (c + (- b + b)) ≡⟨ Eq.cong (\ xx -> (b + - c) + (c + xx)) (+-inverseˡ b) ⟩
      (b + - c) + (c + ₀) ≡⟨ Eq.cong (\ xx -> (b + - c) + xx) (+-identityʳ c) ⟩
      (b + - c) + (c) ≡⟨ +-assoc b (- c) c ⟩
      b + (- c + c) ≡⟨ Eq.cong (b +_) (+-inverseˡ c) ⟩
      b + ₀ ≡⟨ +-identityʳ b ⟩
      b ∎

  aux-act-c : ∀ c t -> act {₁₊ n} ⟦ c ⟧ₕₛ ((₀ , ₀) ∷ t) ≡ (₀ , ₀) ∷ t
  aux-act-c {n} ε t = auto
  aux-act-c {n} c@(HS^ x) t = begin
    act {₁₊ n} ⟦ c ⟧ₕₛ ((₀ , ₀) ∷ t) ≡⟨ auto ⟩
    act {₁₊ n} (H • S^ x) ((₀ , ₀) ∷ t) ≡⟨ auto ⟩
    act {₁₊ n} (H) ((₀ , ₀ + ₀ * x) ∷ t) ≡⟨ auto ⟩
    (- (₀ + ₀ * x) , ₀) ∷ t ≡⟨ auto ⟩
    (- (₀ * x) , ₀) ∷ t ≡⟨ Eq.cong (\ xx -> (- xx , ₀) ∷ t) (*-zeroˡ x) ⟩
    (- ₀ , ₀) ∷ t ≡⟨ Eq.cong (\ xx -> (xx , ₀) ∷ t) -0#≈0# ⟩
    (₀ , ₀) ∷ t ∎
    where
    open ≡-Reasoning

  aux-act-mc : ∀ mc t -> act {₁₊ n} ⟦ mc ⟧ₘ₊ ((₀ , ₀) ∷ t) ≡ (₀ , ₀) ∷ t
  aux-act-mc {n} mc@(m , c) t = begin
    act {₁₊ n} ⟦ mc ⟧ₘ₊ ((₀ , ₀) ∷ t) ≡⟨ auto ⟩
    act (⟦ m ⟧ₘ • ⟦ c ⟧ₕₛ) ((₀ , ₀) ∷ t) ≡⟨ Eq.cong (act ⟦ m ⟧ₘ) (aux-act-c c t) ⟩
    act (⟦ m ⟧ₘ) ((₀ , ₀) ∷ t) ≡⟨ lemma-M ₀ ₀ t m ⟩
    (₀ * x⁻¹ , ₀ * x) ∷ t ≡⟨ auto ⟩
    (₀ , ₀) ∷ t ∎
    where
    open ≡-Reasoning
    x = (m .proj₁)
    x⁻¹ = ((m ⁻¹) .proj₁ )

  aux-act-s : ∀ k t -> act {₁₊ n} (S^ k) ((₀ , ₀) ∷ t) ≡ (₀ , ₀) ∷ t
  aux-act-s k t = begin
    act (S^ k) ((₀ , ₀) ∷ t) ≡⟨ auto ⟩
    ((₀ , ₀ + ₀ * k) ∷ t) ≡⟨ auto ⟩
    (₀ , ₀) ∷ t ∎
    where
    open ≡-Reasoning

  aux-act-nf1 : ∀ nf1 t -> act {₁₊ n} ⟦ nf1 ⟧₁ ((₀ , ₀) ∷ t) ≡ (₀ , ₀) ∷ t
  aux-act-nf1 {n} nf1@(s , m , c) t = begin
    act {₁₊ n} ⟦ nf1 ⟧₁ ((₀ , ₀) ∷ t) ≡⟨ Eq.cong (act {₁₊ n} (S^ s)) (aux-act-mc (m , c) t) ⟩
    act {₁₊ n} (S^ s) ((₀ , ₀) ∷ t) ≡⟨ auto ⟩
    (₀ , ₀) ∷ t ∎
    where
    open ≡-Reasoning


  Theorem-LM2-aux :

    ∀ (p p' : Pauli1) (qs : Pauli 2) (t : Pauli n) ->
    p ≢ pI -> p' ≢ pI ->
    let ps = p ∷ p' ∷ [] in
    sform ps qs ≡ ₁ ->
    -----------------------------------------------
    ∃ \ nf -> act ⟦ nf ⟧₂ (ps ++ t) ≡ pZ ∷ pI ∷ t ×
              act ⟦ nf ⟧₂ (qs ++ t) ≡ pX ∷ pI ∷ t

  Theorem-LM2-aux {n} p@(a1 , b1) p'@(a2 , b2) qs@(q@(c1 , d1) ∷ q'@(c2 , d2) ∷ []) t neq1 neq2 eq = nf2 , claim1 , claim2
    where
    open ≡-Reasoning
    cl1 : sform1 (a1 , b1) (c1 , d1) + sform1 (a2 , b2) (c2 , d2) ≡ ₁
    cl1 = begin
--      sform1 (a2 , b2) (c2 , d2) + sform1 (a1 , b1) (c1 , d1) ≡⟨ +-comm (sform1 (a2 , b2) (c2 , d2)) (sform1 (a1 , b1) (c1 , d1)) ⟩
      sform1 (a1 , b1) (c1 , d1) + sform1 (a2 , b2) (c2 , d2) ≡⟨ Eq.cong (\ xx -> sform1 (a1 , b1) (c1 , d1) + xx) (Eq.sym (+-identityʳ (sform1 (a2 , b2) (c2 , d2)))) ⟩
      (sform1 (a1 , b1) (c1 , d1)) + (sform1 (a2 , b2) (c2 , d2) + ₀) ≡⟨ eq ⟩
      ₁ ∎
    
    mc1 = Theorem-MC-+pZp p q (p' ∷ t) neq1
    mc1' = Theorem-MC-+pZp p q (q' ∷ t) neq1
    mc2 = Theorem-MC-+pZp p' q' t neq2
    mc2' = Theorem-MC-+pZp p' q' t neq2

    e1 = mc1' .proj₂ .proj₁
    e2 = mc2 .proj₂ .proj₁

    pf : Postfix
    pf = (- e1 , mc2 .proj₁ , mc1 .proj₁)
    s = (pf .proj₁)

    aux111 : ₁ + - ₁ * ₁ ≡ 0ₚ
    aux111 = begin
      ₁ + - ₁ * ₁ ≡⟨ Eq.cong (₁ +_) (Eq.sym (-‿distribˡ-* ₁ ₁)) ⟩
      ₁ + - (₁ * ₁) ≡⟨ auto ⟩
      ₁ + - ₁ ≡⟨ +-inverseʳ ₁ ⟩
      ₀ ∎

    claim-mcZ2 : act (⟦ mc2 .proj₁ ⟧ₘ₊ ↑) (pZ ∷ p' ∷ t) ≡ pZ ∷ pZ ∷ t 
    claim-mcZ2 = begin
      act (⟦ mc2 .proj₁ ⟧ₘ₊ ↑) (pZ ∷ p' ∷ t) ≡⟨ lemma-act-↑ ⟦ mc2 .proj₁ ⟧ₘ₊ pZ (p' ∷ t) ⟩
      pZ ∷ act (⟦ mc2 .proj₁ ⟧ₘ₊) (p' ∷ t) ≡⟨ Eq.cong (pZ ∷_) (mc2 .proj₂ .proj₂ .proj₁) ⟩
      pZ ∷ pZ ∷ t ∎

    cliam-mcX2 : act (⟦ mc2 .proj₁ ⟧ₘ₊ ↑) ((sform1 p q , e1) ∷ q' ∷ t) ≡ (sform1 p q , e1) ∷ (sform1 p' q' , e2) ∷ t
    cliam-mcX2 = begin
      act (⟦ mc2 .proj₁ ⟧ₘ₊ ↑) ((sform1 p q , e1) ∷ q' ∷ t) ≡⟨ lemma-act-↑ ⟦ mc2 .proj₁ ⟧ₘ₊ ((sform1 p q , e1)) (q' ∷ t) ⟩
      (sform1 p q , e1) ∷ act (⟦ mc2 .proj₁ ⟧ₘ₊) (q' ∷ t) ≡⟨ Eq.cong ((sform1 p q , e1) ∷_) (mc2 .proj₂ .proj₂ .proj₂) ⟩
      (sform1 p q , e1) ∷ (sform1 p' q' , e2) ∷ t ∎

    claim-pf-Z : act (⟦ pf ⟧ₚ) (p ∷ p' ∷ t) ≡ pZ ∷ pI ∷ t 
    claim-pf-Z = begin
      act (⟦ pf ⟧ₚ) (p ∷ p' ∷ t) ≡⟨ Eq.cong (act (S^ s • H^ ₃ • CZ • H • ⟦ mc2 .proj₁ ⟧ₘ₊ ↑)) ( mc1 .proj₂ .proj₂ .proj₁) ⟩
      act (S^ s • H^ ₃ • CZ • H • ⟦ mc2 .proj₁ ⟧ₘ₊ ↑) (pZ ∷ p' ∷ t) ≡⟨ Eq.cong (act (S^ s  • H^ ₃ • CZ • H)) (claim-mcZ2) ⟩
      act (S^ s • H^ ₃ • CZ • H) (pZ ∷ pZ ∷ t) ≡⟨ auto ⟩
      act (S^ s • H^ ₃ • CZ) ((- ₁ , ₀) ∷ pZ ∷  t) ≡⟨ auto ⟩
      act (S^ s • H^ ₃) ((- ₁ , ₀) ∷ (₀ , ₁ + - ₁ * ₁) ∷ t) ≡⟨ Eq.cong (\ xx -> act (S^ s  • H^ ₃) ((- ₁ , ₀) ∷ (₀ , xx) ∷ t)) aux111 ⟩
      act (S^ s • H^ ₃) ((- ₁ , ₀) ∷ (₀ , ₀) ∷ t) ≡⟨ auto ⟩
      act (S^ s) ((₀ , - - ₁) ∷ (₀ , ₀) ∷ t) ≡⟨ Eq.cong (\ xx -> act (S^ s) ((₀ , xx) ∷ (₀ , ₀) ∷ t)) (-‿involutive ₁) ⟩
      act (S^ s) ((₀ , ₁) ∷ (₀ , ₀) ∷ t) ≡⟨ auto ⟩
      pZ ∷ pI ∷ t  ∎


    claim-pf-X : act (⟦ pf ⟧ₚ) (q ∷ q' ∷ t) ≡ pX ∷ (sform1 p' q' , e2 + - e1) ∷ t 
    claim-pf-X = begin
      act (S^ s • H^ ₃ • CZ • H • ⟦ mc2 .proj₁ ⟧ₘ₊ ↑ • ⟦ mc1 .proj₁ ⟧ₘ₊) (q ∷ q' ∷ t) ≡⟨ Eq.cong (\ xx -> act (S^ s • H^ ₃ • CZ • H • ⟦ mc2 .proj₁ ⟧ₘ₊ ↑ • ⟦ xx ⟧ₘ₊) (q ∷ q' ∷ t)) (aux-MC p q (p' ∷ t) (q' ∷ t) neq1) ⟩
      act (S^ s • H^ ₃ • CZ • H • ⟦ mc2 .proj₁ ⟧ₘ₊ ↑ • ⟦ mc1' .proj₁ ⟧ₘ₊) (q ∷ q' ∷ t) ≡⟨ Eq.cong (act (S^ s • H^ ₃ • CZ • H • ⟦ mc2 .proj₁ ⟧ₘ₊ ↑)) (mc1' .proj₂ .proj₂ .proj₂) ⟩ 
      act (S^ s • H^ ₃ • CZ • H • ⟦ mc2 .proj₁ ⟧ₘ₊ ↑) ((sform1 p q , e1) ∷ q' ∷ t) ≡⟨ Eq.cong (act (S^ s  • H^ ₃ • CZ • H)) cliam-mcX2 ⟩
      act (S^ s • H^ ₃ • CZ • H) ((sform1 p q , e1) ∷ (sform1 p' q' , e2) ∷ t) ≡⟨ auto ⟩
      act (S^ s • H^ ₃ • CZ) ((- e1 , sform1 p q) ∷ (sform1 p' q' , e2) ∷ t) ≡⟨ auto ⟩
      act (S^ s • H^ ₃) ((- e1 , sform1 p q + sform1 p' q' * ₁) ∷ (sform1 p' q' , e2 + - e1 * ₁) ∷ t) ≡⟨  Eq.cong₂ (\ xx yy -> act (S^ s • H^ ₃) ((- e1 , sform1 p q + xx) ∷ (sform1 p' q' , e2 + yy) ∷ t)) (*-identityʳ (sform1 p' q')) (*-identityʳ (- e1))  ⟩
      act (S^ s • H^ ₃) ((- e1 , sform1 p q + sform1 p' q') ∷ (sform1 p' q' , e2 + - e1) ∷ t) ≡⟨ Eq.cong (\ xx -> act (S^ s • H^ ₃) ((- e1 , xx) ∷ (sform1 p' q' , e2 + - e1) ∷ t)) cl1 ⟩
      act (S^ s • H^ ₃) ((- e1 , ₁) ∷ (sform1 p' q' , e2 + - e1) ∷ t) ≡⟨ auto ⟩
      act (S^ s) ((₁ , - - e1) ∷ (sform1 p' q' , e2 + - e1) ∷ t) ≡⟨ auto ⟩
      act (S^ s) ((₁ , - - e1) ∷ (sform1 p' q' , e2 + - e1) ∷ t) ≡⟨ Eq.cong (\ xx -> act (S^ s) ((₁ , xx) ∷ (sform1 p' q' , e2 + - e1) ∷ t)) (-‿involutive e1) ⟩
      act (S^ s) ((₁ , e1) ∷ (sform1 p' q' , e2 + - e1) ∷ t) ≡⟨ auto ⟩
      ((₁ , e1 + ₁ * - e1) ∷ (sform1 p' q' , e2 + - e1) ∷ t) ≡⟨ Eq.cong (\ xx -> ((₁ , xx) ∷ (sform1 p' q' , e2 + - e1) ∷ t)) (Eq.trans (Eq.cong (e1 +_) (*-identityˡ (- e1))) (+-inverseʳ e1)) ⟩
      ((₁ , ₀) ∷ (sform1 p' q' , e2 + - e1) ∷ t) ∎

    k = - (e2 + - e1)

    nf2 : Cosets2
    nf2 with sform1 p' q'
    ... | ₀ = case-||ₐ k pf
    ... | y@(₁₊ _) = case-|| (y , λ ()) (k * yinv) pf
      where
      yinv = ((y , λ ()) ⁻¹) .proj₁

    claim1 : act ⟦ nf2 ⟧₂ (p ∷ p' ∷ t) ≡ pZ ∷ pI ∷ t
    claim1 with sform1 p' q'
    ... | ₀ = begin
      act ⟦ case-||ₐ k pf ⟧₂ (p ∷ p' ∷ t) ≡⟨ auto ⟩
      act (CZ^ k) (act ⟦ pf ⟧ₚ (p ∷ p' ∷ t)) ≡⟨ Eq.cong (act (CZ^ k)) claim-pf-Z ⟩
      act (CZ^ k) (pZ ∷ pI ∷ t) ≡⟨ auto ⟩
      pZ ∷ pI ∷ t ∎
    ... | y@(₁₊ _) = begin
      act ⟦ case-|| (y , λ ()) (k * yinv) pf ⟧₂ (p ∷ p' ∷ t) ≡⟨ Eq.cong (act (CZ^ y • H^ ₃ ↑ • S^ (k * yinv) ↑)) claim-pf-Z ⟩
      act (CZ^ y • H^ ₃ ↑ • S^ (k * yinv) ↑) (pZ ∷ pI ∷ t) ≡⟨ auto ⟩
      act (CZ^ y • H^ ₃ ↑) (pZ ∷ pI ∷ t) ≡⟨ auto ⟩
      act (CZ^ y) (pZ ∷ (₀ , - ₀) ∷ t) ≡⟨ Eq.cong (\ xx -> act (CZ^ y) (pZ ∷ (₀ , xx) ∷ t)) -0#≈0# ⟩
      act (CZ^ y) (pZ ∷ (₀ , ₀) ∷ t) ≡⟨ auto ⟩
      pZ ∷ pI ∷ t ∎
      where
      yinv = ((y , λ ()) ⁻¹) .proj₁


    aux-ee : e2 + - e1 + ₁ * k ≡ ₀
    aux-ee = begin
      e2 + - e1 + ₁ * k ≡⟨ Eq.cong (\ xx -> e2 + - e1 + xx) (*-identityˡ k) ⟩
      e2 + - e1 + k ≡⟨ +-inverseʳ (e2 + - e1) ⟩
      ₀ ∎

    claim2 : act ⟦ nf2 ⟧₂ (q ∷ q' ∷ t) ≡ pX ∷ pI ∷ t
    claim2 with sform1 p' q' | inspect (sform1 p') q'
    ... | ₀ | [ eqn ]' = begin
      act ⟦ case-||ₐ k pf ⟧₂ (q ∷ q' ∷ t) ≡⟨ Eq.cong (act (CZ^ k)) claim-pf-X ⟩
      act (CZ^ k) (pX ∷ (sform1 p' q' , e2 + - e1) ∷ t) ≡⟨ Eq.cong (\ xx -> act (CZ^ k) (pX ∷ (xx , e2 + - e1) ∷ t)) eqn ⟩
      act (CZ^ k) (pX ∷ (₀ , e2 + - e1) ∷ t) ≡⟨ auto ⟩
      (pX ∷ (₀ , e2 + - e1 + ₁ * k) ∷ t) ≡⟨ Eq.cong (\ xx -> pX ∷ (₀ , xx) ∷ t) aux-ee ⟩
      pX ∷ pI ∷ t ∎
    ... | y@(₁₊ _) | [ eqn ]' = begin
      act ⟦ case-|| (y , λ ()) (- (e2 + - e1) * yinv) pf ⟧₂ (q ∷ q' ∷ t) ≡⟨ auto ⟩
      act (CZ^ y • H^ ₃ ↑ • S^ (- (e2 + - e1) * yinv) ↑ • ⟦ pf ⟧ₚ) (q ∷ q' ∷ t) ≡⟨ auto ⟩
      act (CZ^ y • H^ ₃ ↑ • S^ (- (e2 + - e1) * yinv) ↑) (act ⟦ pf ⟧ₚ(q ∷ q' ∷ t)) ≡⟨ Eq.cong (act (CZ^ y • H^ ₃ ↑ • S^ (- (e2 + - e1) * yinv) ↑) ) claim-pf-X ⟩
      act (CZ^ y • H^ ₃ ↑ • S^ (- (e2 + - e1) * yinv) ↑) (pX ∷ (sform1 p' q' , e2 + - e1) ∷ t) ≡⟨ Eq.cong (\ xx -> act (CZ^ y • H^ ₃ ↑ • S^ (- (e2 + - e1) * yinv) ↑) (pX ∷ (xx , e2 + - e1) ∷ t)) eqn ⟩
      act (CZ^ y • H^ ₃ ↑ • S^ (- (e2 + - e1) * yinv) ↑) (pX ∷ (y , e2 + - e1) ∷ t) ≡⟨ auto ⟩
      act (CZ^ y • H^ ₃ ↑) (pX ∷ (y , e2 + - e1 + y * (- (e2 + - e1) * yinv)) ∷ t) ≡⟨ Eq.cong (\ xx -> act (CZ^ y • H^ ₃ ↑) (pX ∷ (y , xx) ∷ t)) aux-eey ⟩
      act (CZ^ y • H^ ₃ ↑) (pX ∷ (y , ₀) ∷ t) ≡⟨ auto ⟩
      act (CZ^ y) (pX ∷ (₀ , - y) ∷ t) ≡⟨ auto ⟩
      (pX ∷ (₀ , - y + ₁ * y) ∷ t) ≡⟨ Eq.cong (\ xx -> (pX ∷ (₀ , xx) ∷ t)) aux-yy ⟩
      pX ∷ pI ∷ t ∎
      where
      yinv = ((y , λ ()) ⁻¹) .proj₁
      aux-eey : e2 + - e1 + y * (- (e2 + - e1) * yinv) ≡ ₀
      aux-eey = begin
        e2 + - e1 + y * (- (e2 + - e1) * yinv) ≡⟨ Eq.cong (\ xx -> e2 + - e1 + y * xx) (*-comm (- (e2 + - e1)) (yinv)) ⟩
        e2 + - e1 + y * (yinv * - (e2 + - e1)) ≡⟨ Eq.cong (\ xx -> e2 + - e1 + xx) (Eq.sym (*-assoc (y) (yinv) (- (e2 + - e1)))) ⟩
        e2 + - e1 + y * yinv * - (e2 + - e1) ≡⟨ Eq.cong (\ xx -> e2 + - e1 + xx * - (e2 + - e1)) (lemma-⁻¹ʳ y {{nztoℕ {y = y} {neq0 = λ ()}}} ) ⟩
        e2 + - e1 + ₁ * - (e2 + - e1) ≡⟨ Eq.cong (\ xx -> e2 + - e1 + xx) (*-identityˡ (- (e2 + - e1))) ⟩
        e2 + - e1 + - (e2 + - e1) ≡⟨ +-inverseʳ (e2 + - e1) ⟩
        ₀ ∎
      aux-yy : - y + ₁ * y ≡ ₀
      aux-yy = begin
        - y + ₁ * y ≡⟨ Eq.cong (- y +_) (*-identityˡ y) ⟩
        - y + y ≡⟨ +-inverseˡ y ⟩
        ₀ ∎





  Theorem-LM2 :

    ∀ (ps qs : Pauli 2) (t : Pauli n) ->
    sform ps qs ≡ ₁ ->
    -----------------------------------------------
    ∃ \ nf -> act ⟦ nf ⟧₂ (ps ++ t) ≡ pZ ∷ pI ∷ t ×
              act ⟦ nf ⟧₂ (qs ++ t) ≡ pX ∷ pI ∷ t

  Theorem-LM2 {n} ps@((₀ , ₀) ∷ (₀ , ₀) ∷ []) qs t eq with 0ₚ≢1ₚ (Eq.trans (Eq.sym (sform-pIpI-qq'=0' qs)) eq)
  ... | ()


  Theorem-LM2 {n} ps@((₀ , ₀) ∷ (a2 , b2) ∷ []) qs@((₀ , ₀) ∷ (c2 , d2) ∷ []) t eq = nf2 , (claim1 , claim2)
    where
    open ≡-Reasoning
    c1 : sform1 (a2 , b2) (c2 , d2) ≡ ₁
    c1 = begin
      sform1 (a2 , b2) (c2 , d2) ≡⟨ Eq.sym ( +-identityˡ (sform1 (a2 , b2) (c2 , d2))) ⟩
      ₀ + (sform1 (a2 , b2) (c2 , d2)) ≡⟨ Eq.cong (_+ (sform1 (a2 , b2) (c2 , d2))) (Eq.sym (sform-pI-q=0 ((₀ , ₀)))) ⟩
      sform1 (₀ , ₀) (₀ , ₀) + (sform1 (a2 , b2) (c2 , d2)) ≡⟨ Eq.cong (sform1 (₀ , ₀) (₀ , ₀) +_) (Eq.sym (+-identityʳ (sform1 (a2 , b2) (c2 , d2)))) ⟩
      sform1 (₀ , ₀) (₀ , ₀) + (sform1 (a2 , b2) (c2 , d2) + ₀) ≡⟨ eq ⟩
      ₁ ∎
    
    nf1 = Theorem-NF1 (a2 , b2) (c2 , d2) t c1
    nf2 = case-Ex-nf1 (nf1 .proj₁)
    claim1 : act (⟦ nf2 ⟧₂) ((₀ , ₀) ∷ (a2 , b2) ∷ t) ≡ pZ ∷ pI ∷ t
    claim1 = begin
      act (Ex • ⟦ nf1 .proj₁ ⟧₁ ↑) ((₀ , ₀) ∷ (a2 , b2) ∷ t) ≡⟨ Eq.cong (act Ex) (lemma-act-↑ ⟦ nf1 .proj₁ ⟧₁ ((₀ , ₀)) ((a2 , b2) ∷ t)) ⟩
      act (Ex) ((₀ , ₀) ∷ act (⟦ nf1 .proj₁ ⟧₁) ((a2 , b2) ∷ t)) ≡⟨ Eq.cong (\ xx ->  act Ex ((₀ , ₀) ∷ xx)) (nf1 .proj₂ .proj₁) ⟩
      act (Ex) ((₀ , ₀) ∷ pZ ∷ t) ≡⟨ act-Ex ₀ ₀ ₀ ₁ t ⟩
      pZ ∷ (₀ , ₀) ∷ t ∎

    
    claim2 : act (⟦ nf2 ⟧₂) ((₀ , ₀) ∷ (c2 , d2) ∷ t) ≡ pX ∷ pI ∷ t
    claim2 = begin
      act (Ex • ⟦ nf1 .proj₁ ⟧₁ ↑) ((₀ , ₀) ∷ (c2 , d2) ∷ t) ≡⟨ Eq.cong (act Ex) (lemma-act-↑ ⟦ nf1 .proj₁ ⟧₁ ((₀ , ₀)) ((c2 , d2) ∷ t)) ⟩
      act Ex ((₀ , ₀) ∷ act (⟦ nf1 .proj₁ ⟧₁) ((c2 , d2) ∷ t)) ≡⟨ Eq.cong (\ xx -> act Ex ((₀ , ₀) ∷ xx)) (nf1 .proj₂ .proj₂) ⟩
      act Ex ((₀ , ₀) ∷ pX ∷ t) ≡⟨ act-Ex ₀ ₀ ₁ ₀ t ⟩
      pX ∷ (₀ , ₀) ∷ t ∎


  Theorem-LM2 {n} ps@((a1 , b1) ∷ (₀ , ₀) ∷ []) qs@(q@(c1 , d1) ∷ q'@(₀ , ₀) ∷ []) t eq = nf2 , claim1 , claim2
    where
    open ≡-Reasoning
    cl1 : sform1 (a1 , b1) (c1 , d1) ≡ ₁
    cl1 = begin
      sform1 (a1 , b1) (c1 , d1) ≡⟨ Eq.sym ( +-identityʳ (sform1 (a1 , b1) (c1 , d1))) ⟩
      (sform1 (a1 , b1) (c1 , d1)) + ₀ ≡⟨ Eq.cong ((sform1 (a1 , b1) (c1 , d1)) +_) (Eq.sym (sform-pIₙ-t=0 ((₀ , ₀) ∷ []))) ⟩
      (sform1 (a1 , b1) (c1 , d1)) + sform ((₀ , ₀) ∷ []) ((₀ , ₀) ∷ []) ≡⟨ eq ⟩
      ₁ ∎
    
    nf1 = Theorem-NF1 (a1 , b1) (c1 , d1) ((₀ , ₀) ∷ t) cl1
    nf2 = case-nf1 (nf1 .proj₁)
    claim1 : act (⟦ nf1 .proj₁ ⟧₁) ((a1 , b1) ∷ (₀ , ₀) ∷ t) ≡ pZ ∷ (₀ , ₀) ∷ t 
    claim1 = begin
      act (⟦ nf1 .proj₁ ⟧₁) ((a1 , b1) ∷ (₀ , ₀) ∷ t) ≡⟨ (nf1 .proj₂ .proj₁) ⟩
      pZ ∷ (₀ , ₀) ∷ t ∎



    claim2 : act (⟦ nf1 .proj₁ ⟧₁) ((c1 , d1) ∷ (₀ , ₀) ∷ t) ≡ pX ∷ pI ∷ t
    claim2 = begin
      act (⟦ nf1 .proj₁ ⟧₁) ((c1 , d1) ∷ (₀ , ₀) ∷ t) ≡⟨ (nf1 .proj₂ .proj₂) ⟩
      pX ∷ (₀ , ₀) ∷ t ∎


  Theorem-LM2 {n} ps@((₀ , ₀) ∷ p'@(a2 , b2) ∷ []) qs@(q@(c1 , d1@(₁₊ sq)) ∷ q'@(c2 , d2) ∷ []) t eq = nf2 , claim1' , claim2'
    where
    open ≡-Reasoning
    cl1 : sform1 (a2 , b2) (c2 , d2) ≡ ₁
    cl1 = begin
      sform1 (a2 , b2) (c2 , d2) ≡⟨ Eq.sym ( +-identityˡ (sform1 (a2 , b2) (c2 , d2))) ⟩
      ₀ + (sform1 (a2 , b2) (c2 , d2)) ≡⟨ Eq.cong (_+ (sform1 (a2 , b2) (c2 , d2))) (Eq.sym (sform-pI-q=0 q)) ⟩
      sform1 (₀ , ₀) q + (sform1 (a2 , b2) (c2 , d2)) ≡⟨ Eq.cong (sform1 (₀ , ₀) q +_) (Eq.sym (+-identityʳ (sform1 (a2 , b2) (c2 , d2)))) ⟩
      sform1 (₀ , ₀) q + (sform1 (a2 , b2) (c2 , d2) + ₀) ≡⟨ eq ⟩
      ₁ ∎

  
    nf1 = Theorem-NF1 (a2 , b2) (c2 , d2) t cl1
    mc = Theorem-MC-pZ q (q' ∷ t) λ ()
    nf2 = case-Ex-| (nf1 .proj₁) (mc .proj₁)
--    nf2 = case-Ex-nf1 (nf1 .proj₁)
    
    claim1 : act (⟦ nf1 .proj₁ ⟧₁ ↑) ((₀ , ₀) ∷ (a2 , b2) ∷ t) ≡ pI ∷ pZ ∷ t
    claim1 = begin
      act (⟦ nf1 .proj₁ ⟧₁ ↑) ((₀ , ₀) ∷ (a2 , b2) ∷ t) ≡⟨ lemma-act-↑ ⟦ nf1 .proj₁ ⟧₁ ((₀ , ₀)) ((a2 , b2) ∷ t) ⟩
      (₀ , ₀) ∷ act (⟦ nf1 .proj₁ ⟧₁) ((a2 , b2) ∷ t) ≡⟨ Eq.cong (\ xx -> (₀ , ₀) ∷ xx) (nf1 .proj₂ .proj₁) ⟩
      (₀ , ₀) ∷ pZ ∷ t ∎

    
    claim2 : ∀ p -> act (⟦ nf1 .proj₁ ⟧₁ ↑) (p ∷ (c2 , d2) ∷ t) ≡ p ∷ pX ∷ t
    claim2 p = begin
      act (⟦ nf1 .proj₁ ⟧₁ ↑) (p ∷ (c2 , d2) ∷ t) ≡⟨ lemma-act-↑ ⟦ nf1 .proj₁ ⟧₁ (p) ((c2 , d2) ∷ t) ⟩
      p ∷ act (⟦ nf1 .proj₁ ⟧₁) ((c2 , d2) ∷ t) ≡⟨ Eq.cong (\ xx -> p ∷ xx) (nf1 .proj₂ .proj₂) ⟩
      p ∷ pX ∷ t ∎


    claim1' : act (⟦ nf2 ⟧₂) ((₀ , ₀) ∷ (a2 , b2) ∷ t) ≡ pZ ∷ pI ∷ t
    claim1' = begin
      act (⟦ nf2 ⟧₂) ((₀ , ₀) ∷ (a2 , b2) ∷ t) ≡⟨ auto ⟩
      act (Ex • CZ • ⟦ (nf1 .proj₁) ⟧₁ ↑ • ⟦ mc .proj₁ ⟧ₘ₊) ((₀ , ₀) ∷ (a2 , b2) ∷ t) ≡⟨ Eq.cong (act (Ex • CZ • ⟦ (nf1 .proj₁) ⟧₁ ↑)) (aux-act-mc (mc .proj₁) ((a2 , b2) ∷ t)) ⟩
      act (Ex • CZ • ⟦ (nf1 .proj₁) ⟧₁ ↑) ((₀ , ₀) ∷ (a2 , b2) ∷ t) ≡⟨ Eq.cong (act (Ex • CZ)) ( lemma-act-↑ ⟦ (nf1 .proj₁) ⟧₁ pI ((a2 , b2) ∷ t)) ⟩
      act (Ex • CZ) ((₀ , ₀) ∷ act ⟦ (nf1 .proj₁) ⟧₁ ((a2 , b2) ∷ t)) ≡⟨  Eq.cong (\ xx -> act (Ex • CZ) ((₀ , ₀) ∷ xx)) (nf1 .proj₂ .proj₁) ⟩
      act (Ex • CZ) ((₀ , ₀) ∷ pZ ∷ t) ≡⟨  auto ⟩
      act (Ex) ((₀ , ₀) ∷ pZ ∷ t) ≡⟨  act-Ex ₀ ₀ ₀ ₁ t ⟩
      pZ ∷ pI ∷ t ∎

    aux111 : - ₁ + ₁ * ₁ ≡ 0ₚ
    aux111 = +-inverseˡ ₁


    claim2' : act (⟦ nf2 ⟧₂) ((c1 , d1) ∷ (c2 , d2) ∷ t) ≡ pX ∷ pI ∷ t
    claim2' = begin
      act (⟦ nf2 ⟧₂) ((c1 , d1) ∷ (c2 , d2) ∷ t) ≡⟨ auto ⟩
      act (Ex • CZ • ⟦ (nf1 .proj₁) ⟧₁ ↑ • ⟦ mc .proj₁ ⟧ₘ₊) ((c1 , d1) ∷ (c2 , d2) ∷ t) ≡⟨ Eq.cong (act (Ex • CZ • ⟦ (nf1 .proj₁) ⟧₁ ↑)) (mc .proj₂) ⟩
      act (Ex • CZ • ⟦ (nf1 .proj₁) ⟧₁ ↑) (-pZ ∷ (c2 , d2) ∷ t) ≡⟨ auto ⟩
      act (Ex • CZ) (act (⟦ (nf1 .proj₁) ⟧₁ ↑) (-pZ ∷ (c2 , d2) ∷ t)) ≡⟨ Eq.cong (act (Ex • CZ)) (lemma-act-↑ ⟦ (nf1 .proj₁) ⟧₁ -pZ ((c2 , d2) ∷ t)) ⟩
      act (Ex • CZ) (-pZ ∷ act (⟦ (nf1 .proj₁) ⟧₁) ((c2 , d2) ∷ t)) ≡⟨ Eq.cong (\ xx -> act (Ex • CZ) (-pZ ∷ xx)) (nf1 .proj₂ .proj₂) ⟩
      act (Ex • CZ) (-pZ ∷ pX ∷ t) ≡⟨ auto ⟩
      act (Ex) ((₀ , - ₁ + ₁ * ₁) ∷ pX ∷ t) ≡⟨  Eq.cong (\ xx -> act (Ex) ((₀ , xx) ∷ pX ∷ t)) aux111 ⟩
      act (Ex) ((₀ , ₀) ∷ pX ∷ t) ≡⟨ act-Ex ₀ ₀ ₁ ₀ t ⟩
      pX ∷ pI ∷ t ∎


  Theorem-LM2 {n} ps@((₀ , ₀) ∷ p'@(a2 , b2) ∷ []) qs@(q@(c1@(₁₊ sq) , d1) ∷ q'@(c2 , d2) ∷ []) t eq = nf2 , claim1' , claim2'
    where
    open ≡-Reasoning
    cl1 : sform1 (a2 , b2) (c2 , d2) ≡ ₁
    cl1 = begin
      sform1 (a2 , b2) (c2 , d2) ≡⟨ Eq.sym ( +-identityˡ (sform1 (a2 , b2) (c2 , d2))) ⟩
      ₀ + (sform1 (a2 , b2) (c2 , d2)) ≡⟨ Eq.cong (_+ (sform1 (a2 , b2) (c2 , d2))) (Eq.sym (sform-pI-q=0 q)) ⟩
      sform1 (₀ , ₀) q + (sform1 (a2 , b2) (c2 , d2)) ≡⟨ Eq.cong (sform1 (₀ , ₀) q +_) (Eq.sym (+-identityʳ (sform1 (a2 , b2) (c2 , d2)))) ⟩
      sform1 (₀ , ₀) q + (sform1 (a2 , b2) (c2 , d2) + ₀) ≡⟨ eq ⟩
      ₁ ∎

  
    nf1 = Theorem-NF1 (a2 , b2) (c2 , d2) t cl1
    mc = Theorem-MC-pZ q (q' ∷ t) λ ()
    nf2 = case-Ex-| (nf1 .proj₁) (mc .proj₁)
--    nf2 = case-Ex-nf1 (nf1 .proj₁)
    
    claim1 : act (⟦ nf1 .proj₁ ⟧₁ ↑) ((₀ , ₀) ∷ (a2 , b2) ∷ t) ≡ pI ∷ pZ ∷ t
    claim1 = begin
      act (⟦ nf1 .proj₁ ⟧₁ ↑) ((₀ , ₀) ∷ (a2 , b2) ∷ t) ≡⟨ lemma-act-↑ ⟦ nf1 .proj₁ ⟧₁ ((₀ , ₀)) ((a2 , b2) ∷ t) ⟩
      (₀ , ₀) ∷ act (⟦ nf1 .proj₁ ⟧₁) ((a2 , b2) ∷ t) ≡⟨ Eq.cong (\ xx -> (₀ , ₀) ∷ xx) (nf1 .proj₂ .proj₁) ⟩
      (₀ , ₀) ∷ pZ ∷ t ∎

    
    claim2 : ∀ p -> act (⟦ nf1 .proj₁ ⟧₁ ↑) (p ∷ (c2 , d2) ∷ t) ≡ p ∷ pX ∷ t
    claim2 p = begin
      act (⟦ nf1 .proj₁ ⟧₁ ↑) (p ∷ (c2 , d2) ∷ t) ≡⟨ lemma-act-↑ ⟦ nf1 .proj₁ ⟧₁ (p) ((c2 , d2) ∷ t) ⟩
      p ∷ act (⟦ nf1 .proj₁ ⟧₁) ((c2 , d2) ∷ t) ≡⟨ Eq.cong (\ xx -> p ∷ xx) (nf1 .proj₂ .proj₂) ⟩
      p ∷ pX ∷ t ∎


    claim1' : act (⟦ nf2 ⟧₂) ((₀ , ₀) ∷ (a2 , b2) ∷ t) ≡ pZ ∷ pI ∷ t
    claim1' = begin
      act (⟦ nf2 ⟧₂) ((₀ , ₀) ∷ (a2 , b2) ∷ t) ≡⟨ auto ⟩
      act (Ex • CZ • ⟦ (nf1 .proj₁) ⟧₁ ↑ • ⟦ mc .proj₁ ⟧ₘ₊) ((₀ , ₀) ∷ (a2 , b2) ∷ t) ≡⟨ Eq.cong (act (Ex • CZ • ⟦ (nf1 .proj₁) ⟧₁ ↑)) (aux-act-mc (mc .proj₁) ((a2 , b2) ∷ t)) ⟩
      act (Ex • CZ • ⟦ (nf1 .proj₁) ⟧₁ ↑) ((₀ , ₀) ∷ (a2 , b2) ∷ t) ≡⟨ Eq.cong (act (Ex • CZ)) ( lemma-act-↑ ⟦ (nf1 .proj₁) ⟧₁ pI ((a2 , b2) ∷ t)) ⟩
      act (Ex • CZ) ((₀ , ₀) ∷ act ⟦ (nf1 .proj₁) ⟧₁ ((a2 , b2) ∷ t)) ≡⟨  Eq.cong (\ xx -> act (Ex • CZ) ((₀ , ₀) ∷ xx)) (nf1 .proj₂ .proj₁) ⟩
      act (Ex • CZ) ((₀ , ₀) ∷ pZ ∷ t) ≡⟨  auto ⟩
      act (Ex) ((₀ , ₀) ∷ pZ ∷ t) ≡⟨  act-Ex ₀ ₀ ₀ ₁ t ⟩
      pZ ∷ pI ∷ t ∎

    aux111 : - ₁ + ₁ * ₁ ≡ 0ₚ
    aux111 = +-inverseˡ ₁


    claim2' : act (⟦ nf2 ⟧₂) ((c1 , d1) ∷ (c2 , d2) ∷ t) ≡ pX ∷ pI ∷ t
    claim2' = begin
      act (⟦ nf2 ⟧₂) ((c1 , d1) ∷ (c2 , d2) ∷ t) ≡⟨ auto ⟩
      act (Ex • CZ • ⟦ (nf1 .proj₁) ⟧₁ ↑ • ⟦ mc .proj₁ ⟧ₘ₊) ((c1 , d1) ∷ (c2 , d2) ∷ t) ≡⟨ Eq.cong (act (Ex • CZ • ⟦ (nf1 .proj₁) ⟧₁ ↑)) (mc .proj₂) ⟩
      act (Ex • CZ • ⟦ (nf1 .proj₁) ⟧₁ ↑) (-pZ ∷ (c2 , d2) ∷ t) ≡⟨ auto ⟩
      act (Ex • CZ) (act (⟦ (nf1 .proj₁) ⟧₁ ↑) (-pZ ∷ (c2 , d2) ∷ t)) ≡⟨ Eq.cong (act (Ex • CZ)) (lemma-act-↑ ⟦ (nf1 .proj₁) ⟧₁ -pZ ((c2 , d2) ∷ t)) ⟩
      act (Ex • CZ) (-pZ ∷ act (⟦ (nf1 .proj₁) ⟧₁) ((c2 , d2) ∷ t)) ≡⟨ Eq.cong (\ xx -> act (Ex • CZ) (-pZ ∷ xx)) (nf1 .proj₂ .proj₂) ⟩
      act (Ex • CZ) (-pZ ∷ pX ∷ t) ≡⟨ auto ⟩
      act (Ex) ((₀ , - ₁ + ₁ * ₁) ∷ pX ∷ t) ≡⟨  Eq.cong (\ xx -> act (Ex) ((₀ , xx) ∷ pX ∷ t)) aux111 ⟩
      act (Ex) ((₀ , ₀) ∷ pX ∷ t) ≡⟨ act-Ex ₀ ₀ ₁ ₀ t ⟩
      pX ∷ pI ∷ t ∎


  Theorem-LM2 {n} ps@((a1 , b1) ∷ (₀ , ₀) ∷ []) qs@(q@(c1 , d1) ∷ q'@(c2@(₁₊ _) , d2 ) ∷ []) t eq = nf2 , claim1' , claim2'
    where
    open ≡-Reasoning
    cl1 : sform1 (a1 , b1) (c1 , d1) ≡ ₁
    cl1 = begin
      sform1 (a1 , b1) (c1 , d1) ≡⟨ Eq.sym ( +-identityʳ (sform1 (a1 , b1) (c1 , d1))) ⟩
      (sform1 (a1 , b1) (c1 , d1)) + ₀ ≡⟨ Eq.cong ((sform1 (a1 , b1) (c1 , d1)) +_) (Eq.sym (sform-pIₙ-t=0 (q' ∷ []))) ⟩
      (sform1 (a1 , b1) (c1 , d1)) + sform ((₀ , ₀) ∷ []) (q' ∷ []) ≡⟨ eq ⟩
      ₁ ∎


    nf1 = Theorem-NF1 (a1 , b1) (c1 , d1) ((₀ , ₀) ∷ t) cl1
    nf1q = Theorem-NF1 (a1 , b1) (c1 , d1) (q' ∷ t) cl1
    mc = Theorem-MC-pZ q' (t) λ ()
    nf2 = case-| (mc .proj₁) (nf1 .proj₁) 

    claim1 : act (⟦ nf1 .proj₁ ⟧₁) ((a1 , b1) ∷ (₀ , ₀) ∷ t) ≡ pZ ∷ (₀ , ₀) ∷ t 
    claim1 = begin
      act (⟦ nf1 .proj₁ ⟧₁) ((a1 , b1) ∷ (₀ , ₀) ∷ t) ≡⟨ nf1 .proj₂ .proj₁ ⟩
      pZ ∷ (₀ , ₀) ∷ t ∎

    claim1' : act (⟦ nf2 ⟧₂) ((a1 , b1) ∷ (₀ , ₀) ∷ t) ≡ pZ ∷ pI ∷ t
    claim1' = begin
      act (⟦ nf2 ⟧₂) ((a1 , b1) ∷ (₀ , ₀) ∷ t) ≡⟨ auto ⟩
      act (CZ • ⟦ mc .proj₁ ⟧ₘ₊ ↑ • ⟦ nf1 .proj₁ ⟧₁) ((a1 , b1) ∷ (₀ , ₀) ∷ t) ≡⟨ Eq.cong (\ xx -> act ((CZ) • ⟦ mc .proj₁ ⟧ₘ₊ ↑) xx) claim1 ⟩
      act (CZ • ⟦ mc .proj₁ ⟧ₘ₊ ↑) (pZ ∷ (₀ , ₀) ∷ t) ≡⟨ auto ⟩
      act (CZ) (pZ ∷ act (⟦ mc .proj₁ ⟧ₘ₊) ((₀ , ₀) ∷ t)) ≡⟨ Eq.cong (\xx -> act (CZ) (pZ ∷ xx)) (aux-act-mc (mc .proj₁) t) ⟩
      act (CZ) (pZ ∷ ((₀ , ₀) ∷ t)) ≡⟨ auto ⟩
      pZ ∷ pI ∷ t ∎
    

    claim2' : act (⟦ nf2 ⟧₂) ((c1 , d1) ∷ q' ∷ t) ≡ pX ∷ pI ∷ t
    claim2' = begin
      act (⟦ nf2 ⟧₂) ((c1 , d1) ∷ q' ∷ t) ≡⟨ auto ⟩
      act (CZ • ⟦ mc .proj₁ ⟧ₘ₊ ↑ • ⟦ nf1 .proj₁ ⟧₁) ((c1 , d1) ∷ q' ∷ t) ≡⟨ Eq.cong (\ xx -> act (CZ • ⟦ mc .proj₁ ⟧ₘ₊ ↑ • ⟦ xx ⟧₁) ((c1 , d1) ∷ q' ∷ t)) (aux-NF1 ((a1 , b1)) ((c1 , d1)) (((₀ , ₀) ∷ t)) ((q' ∷ t)) cl1) ⟩
      act (CZ • ⟦ mc .proj₁ ⟧ₘ₊ ↑ • ⟦ nf1q .proj₁ ⟧₁) ((c1 , d1) ∷ q' ∷ t) ≡⟨ Eq.cong (act (CZ • ⟦ mc .proj₁ ⟧ₘ₊ ↑)) (nf1q .proj₂ .proj₂) ⟩
      act (CZ • ⟦ mc .proj₁ ⟧ₘ₊ ↑) (pX ∷ q' ∷ t) ≡⟨ Eq.cong (act (CZ)) (lemma-act-↑ ⟦ mc .proj₁ ⟧ₘ₊ pX (q' ∷ t)) ⟩
      act (CZ) (pX ∷ act ⟦ mc .proj₁ ⟧ₘ₊ (q' ∷ t)) ≡⟨ Eq.cong (\ xx -> act (CZ) (pX ∷ xx)) (mc .proj₂) ⟩
      act (CZ) (pX ∷ -pZ ∷ t) ≡⟨ auto ⟩
      ((₁ , ₀) ∷ (₀ , - ₁ + ₁ * ₁) ∷ t) ≡⟨ Eq.cong (\ xx -> (pX ∷ (₀ , xx) ∷ t)) (+-inverseˡ ₁) ⟩
      ((₁ , ₀) ∷ (₀ , ₀) ∷ t) ≡⟨ auto ⟩
      pX ∷ pI ∷ t ∎


  Theorem-LM2 {n} ps@((a1 , b1) ∷ (₀ , ₀) ∷ []) qs@(q@(c1 , d1) ∷ q'@(c2 , d2@(₁₊ _)) ∷ []) t eq = nf2 , claim1' , claim2'
    where
    open ≡-Reasoning
    cl1 : sform1 (a1 , b1) (c1 , d1) ≡ ₁
    cl1 = begin
      sform1 (a1 , b1) (c1 , d1) ≡⟨ Eq.sym ( +-identityʳ (sform1 (a1 , b1) (c1 , d1))) ⟩
      (sform1 (a1 , b1) (c1 , d1)) + ₀ ≡⟨ Eq.cong ((sform1 (a1 , b1) (c1 , d1)) +_) (Eq.sym (sform-pIₙ-t=0 (q' ∷ []))) ⟩
      (sform1 (a1 , b1) (c1 , d1)) + sform ((₀ , ₀) ∷ []) (q' ∷ []) ≡⟨ eq ⟩
      ₁ ∎


    nf1 = Theorem-NF1 (a1 , b1) (c1 , d1) ((₀ , ₀) ∷ t) cl1
    nf1q = Theorem-NF1 (a1 , b1) (c1 , d1) (q' ∷ t) cl1
    mc = Theorem-MC-pZ q' (t) λ ()
    nf2 = case-| (mc .proj₁) (nf1 .proj₁) 

    claim1 : act (⟦ nf1 .proj₁ ⟧₁) ((a1 , b1) ∷ (₀ , ₀) ∷ t) ≡ pZ ∷ (₀ , ₀) ∷ t 
    claim1 = begin
      act (⟦ nf1 .proj₁ ⟧₁) ((a1 , b1) ∷ (₀ , ₀) ∷ t) ≡⟨ nf1 .proj₂ .proj₁ ⟩
      pZ ∷ (₀ , ₀) ∷ t ∎

    claim1' : act (⟦ nf2 ⟧₂) ((a1 , b1) ∷ (₀ , ₀) ∷ t) ≡ pZ ∷ pI ∷ t
    claim1' = begin
      act (⟦ nf2 ⟧₂) ((a1 , b1) ∷ (₀ , ₀) ∷ t) ≡⟨ auto ⟩
      act (CZ • ⟦ mc .proj₁ ⟧ₘ₊ ↑ • ⟦ nf1 .proj₁ ⟧₁) ((a1 , b1) ∷ (₀ , ₀) ∷ t) ≡⟨ Eq.cong (\ xx -> act ((CZ) • ⟦ mc .proj₁ ⟧ₘ₊ ↑) xx) claim1 ⟩
      act (CZ • ⟦ mc .proj₁ ⟧ₘ₊ ↑) (pZ ∷ (₀ , ₀) ∷ t) ≡⟨ auto ⟩
      act CZ (act (⟦ mc .proj₁ ⟧ₘ₊ ↑) (pZ ∷ (₀ , ₀) ∷ t)) ≡⟨ Eq.cong (act CZ) (lemma-act-↑ ⟦ mc .proj₁ ⟧ₘ₊ pZ ((₀ , ₀) ∷ t)) ⟩
      act CZ (pZ ∷ act (⟦ mc .proj₁ ⟧ₘ₊) ((₀ , ₀) ∷ t)) ≡⟨ auto ⟩
      act (CZ) (pZ ∷ act (⟦ mc .proj₁ ⟧ₘ₊) ((₀ , ₀) ∷ t)) ≡⟨ Eq.cong (\xx -> act (CZ) (pZ ∷ xx)) (aux-act-mc (mc .proj₁) t) ⟩
      act (CZ) (pZ ∷ ((₀ , ₀) ∷ t)) ≡⟨ auto ⟩
      pZ ∷ pI ∷ t ∎
    

    claim2' : act (⟦ nf2 ⟧₂) ((c1 , d1) ∷ q' ∷ t) ≡ pX ∷ pI ∷ t
    claim2' = begin
      act (⟦ nf2 ⟧₂) ((c1 , d1) ∷ q' ∷ t) ≡⟨ auto ⟩
      act (CZ • ⟦ mc .proj₁ ⟧ₘ₊ ↑ • ⟦ nf1 .proj₁ ⟧₁) ((c1 , d1) ∷ q' ∷ t) ≡⟨ Eq.cong (\ xx -> act (CZ • ⟦ mc .proj₁ ⟧ₘ₊ ↑ • ⟦ xx ⟧₁) ((c1 , d1) ∷ q' ∷ t)) (aux-NF1 ((a1 , b1)) ((c1 , d1)) (((₀ , ₀) ∷ t)) ((q' ∷ t)) cl1) ⟩
      act (CZ • ⟦ mc .proj₁ ⟧ₘ₊ ↑ • ⟦ nf1q .proj₁ ⟧₁) ((c1 , d1) ∷ q' ∷ t) ≡⟨ Eq.cong (act (CZ • ⟦ mc .proj₁ ⟧ₘ₊ ↑)) (nf1q .proj₂ .proj₂) ⟩
      act (CZ • ⟦ mc .proj₁ ⟧ₘ₊ ↑) (pX ∷ q' ∷ t) ≡⟨ Eq.cong (act (CZ)) (lemma-act-↑ ⟦ mc .proj₁ ⟧ₘ₊ pX (q' ∷ t)) ⟩
      act (CZ) (pX ∷ act ⟦ mc .proj₁ ⟧ₘ₊ (q' ∷ t)) ≡⟨ Eq.cong (\ xx -> act (CZ) (pX ∷ xx)) (mc .proj₂) ⟩
      act (CZ) (pX ∷ -pZ ∷ t) ≡⟨ auto ⟩
      ((₁ , ₀) ∷ (₀ , - ₁ + ₁ * ₁) ∷ t) ≡⟨ Eq.cong (\ xx -> (pX ∷ (₀ , xx) ∷ t)) (+-inverseˡ ₁) ⟩
      ((₁ , ₀) ∷ (₀ , ₀) ∷ t) ≡⟨ auto ⟩
      pX ∷ pI ∷ t ∎

  Theorem-LM2 {n} (p@(_ , ₁₊ _) ∷ p'@(₁₊ _ , _) ∷ []) qs t eq = Theorem-LM2-aux p p' qs t (λ ()) (λ ()) eq
  Theorem-LM2 {n} (p@(_ , ₁₊ _) ∷ p'@(_ , ₁₊ _) ∷ []) qs t eq = Theorem-LM2-aux p p' qs t (λ ()) (λ ()) eq
  Theorem-LM2 {n} (p@(₁₊ _ , _) ∷ p'@(₁₊ _ , _) ∷ []) qs t eq = Theorem-LM2-aux p p' qs t (λ ()) (λ ()) eq
  Theorem-LM2 {n} (p@(₁₊ _ , _) ∷ p'@(_ , ₁₊ _) ∷ []) qs t eq = Theorem-LM2-aux p p' qs t (λ ()) (λ ()) eq



-}
-}
-}
