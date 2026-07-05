{-# OPTIONS --safe #-}
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

open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂ ; map₁ ; ∃)
open import Data.Product.Relation.Binary.Pointwise.NonDependent as PW using (≡×≡⇒≡ ; Pointwise ; ≡⇒≡×≡)
open import Data.Nat hiding (_^_ ; _+_ ; _*_ ; _%_ ; _/_)
open import Agda.Builtin.Nat using ()
import Data.Nat as Nat
open import Data.Fin hiding (_+_ ; _-_)
open import Data.Bool
open import Data.List hiding ([_])

open import Data.Maybe
open import Data.Sum using (_⊎_ ; inj₁ ; inj₂ ; [_,_])
open import Data.Unit using (⊤ ; tt)
open import Data.Empty using (⊥ ; ⊥-elim)

open import Word.Base as WB hiding (wfoldl ; _*)
open import Word.Properties
import Presentation.Base as PB
import Presentation.Properties as PP
open PP using (NFProperty ; NFProperty')
import Presentation.CosetNF as CA
import Presentation.Reidemeister-Schreier as RS
open import Notations
module RSF = RS.Star-Injective-Full.Reidemeister-Schreier-Full

open import Presentation.Construct.Base hiding (_*_)
import Presentation.Construct.Properties.SemiDirectProduct2 as SDP2
import Presentation.Construct.Properties.DirectProduct as DP
import Presentation.Groups.Cyclic as Cyclic


open import Data.Fin.Properties using (suc-injective ; toℕ-inject₁ ; toℕ-fromℕ)
import Data.Nat.Properties as NP
open import Presentation.GroupLike
open import One.SymplecticZp

module One.Completeness where

open import Data.Nat.Primality
open import Data.Nat.Coprimality hiding (sym)
open import Data.Nat.GCD
open Bézout
open import Data.Empty
open import Algebra.Properties.Group

pattern auto = Eq.refl

pattern ₀ = zero
pattern ₁ = ₁₊ ₀
pattern ₂ = ₁₊ ₁
pattern ₃ = ₁₊ ₂
pattern ₄ = ₁₊ ₃


module Completeness (p-2 : ℕ) (p-prime : Prime (₂₊ p-2)) where

  open import Zp.ModularArithmetic
  open PrimeModulus p-2 p-prime hiding (p)
  open NF1 p-2 p-prime hiding (p)
  open Symℕ p-2 p-prime renaming (M to Mz)

  open Symplectic-Powers p-2 p-prime
  open Symplectic-Rewriting-HH p-2 p-prime
  open Lemmas p-2 p-prime

  open PB _===_ hiding (_===_)
  open PP _===_
  open SR word-setoid
  open Pattern-Assoc

--  update-nf : ∀ (nf : NF1) (g : Gen) -> NF1

  PrimitiveGen : Gen -> Set
  PrimitiveGen (Symℕ.H-gen ₁) = ⊤
  PrimitiveGen (Symℕ.S-gen ₁) = ⊤
  PrimitiveGen (Symℕ.H-gen x) = ⊥
  PrimitiveGen (Symℕ.S-gen x) = ⊥

  PrimitiveWord : Word Gen -> Set
  PrimitiveWord [ x ]ʷ = PrimitiveGen x
  PrimitiveWord ε = ⊤
  PrimitiveWord (w • w₁) = PrimitiveWord w × PrimitiveWord w₁

  desugar-gen : Gen -> Word Gen
  desugar-gen (Symℕ.H-gen x) = H ^ toℕ x
  desugar-gen (Symℕ.S-gen x) = S ^ toℕ x

  desugar-word = desugar-gen WB.*

  lemma-H^-Prim : ∀ x -> PrimitiveWord (H ^ x)
  lemma-H^-Prim ₀ = tt
  lemma-H^-Prim ₁ = tt
  lemma-H^-Prim (₂₊ k) = tt , (lemma-H^-Prim (₁₊ k))
  
  lemma-S^-Prim : ∀ x -> PrimitiveWord (S ^ x)
  lemma-S^-Prim ₀ = tt
  lemma-S^-Prim ₁ = tt
  lemma-S^-Prim (₂₊ k) = tt , (lemma-S^-Prim (₁₊ k))
  
  lemma-desugar-gen : (g : Gen) -> PrimitiveWord (desugar-gen g)
  lemma-desugar-gen (Symℕ.H-gen x) = lemma-H^-Prim (toℕ x)
  lemma-desugar-gen (Symℕ.S-gen x) = lemma-S^-Prim (toℕ x)

  lemma-desugar-word : (w : Word Gen) -> PrimitiveWord (desugar-word w)
  lemma-desugar-word [ x ]ʷ = lemma-desugar-gen x
  lemma-desugar-word ε = tt
  lemma-desugar-word (w • w₁) = (lemma-desugar-word w) , (lemma-desugar-word w₁)

  lemma-desugar-gen-≈ : (g : Gen) -> desugar-gen g ≈ [ g ]ʷ
  lemma-desugar-gen-≈ (Symℕ.H-gen x) = sym (axiom (derived-H x))
  lemma-desugar-gen-≈ (Symℕ.S-gen x) = sym (axiom (derived-S x))

  lemma-desugar-word-≈ : (w : Word Gen) -> desugar-word w ≈ w
  lemma-desugar-word-≈ [ x ]ʷ = lemma-desugar-gen-≈ x
  lemma-desugar-word-≈ ε = refl
  lemma-desugar-word-≈ (w • w₁) = cong (lemma-desugar-word-≈ w) (lemma-desugar-word-≈ w₁)


  Lemma-single-qupit-completeness :
    
    ∀ (nf : NF1) (g : Gen) (pg : PrimitiveGen g) ->
    -----------------------------------------------
    ∃ \ nf' -> ⟦ nf ⟧ • [ g ]ʷ ≈ ⟦ nf' ⟧
    
  Lemma-single-qupit-completeness nf@(s ∙ m ∙ ε) (Symℕ.H-gen ₁) pg = (s ∙ m ∙ HS ₀) , claim
    where
    claim : (⟦ s ⟧↥ • ⟦ m ⟧ₘ • ε) • [ H-gen ₁ ]ʷ ≈ ⟦ s ⟧↥ • ⟦ m ⟧ₘ • H • S^ ₀
    claim = begin
      (⟦ s ⟧↥ • ⟦ m ⟧ₘ • ε) • H ≈⟨ _≈_.cong (_≈_.cong refl right-unit) refl ⟩
      (⟦ s ⟧↥ • ⟦ m ⟧ₘ) • H ≈⟨ by-assoc auto ⟩
      (⟦ s ⟧↥ • ⟦ m ⟧ₘ) • H • ε ≈⟨ (cright cright _≈_.sym (axiom (derived-S ₀))) ⟩
      (⟦ s ⟧↥ • ⟦ m ⟧ₘ) • H • S^ ₀ ≈⟨ assoc ⟩
      ⟦ s ⟧↥ • ⟦ m ⟧ₘ • H • S^ ₀ ∎
  Lemma-single-qupit-completeness nf@(s ∙ M x ∙ HS ₀) (Symℕ.H-gen ₁) pg = nf' , claim
    where
    x'  = x *' -'₁
    nf' = s ∙ M x' ∙ ε
    claim : ⟦ s ∙ M x ∙ HS ₀ ⟧ • [ H-gen ₁ ]ʷ ≈ ⟦ nf' ⟧
    claim = begin
      ⟦ s ∙ M x ∙ HS ₀ ⟧ • [ H-gen ₁ ]ʷ ≈⟨ (cleft (cright (cright (cright axiom (derived-S ₀))))) ⟩
      (⟦ s ⟧↥ • Mz x • (H • ε)) • H ≈⟨ trans assoc (cright assoc) ⟩
      ⟦ s ⟧↥ • Mz x • (H • ε) • H ≈⟨ (cright cright cong right-unit refl) ⟩
      ⟦ s ⟧↥ • Mz x • HH ≈⟨ (cright cright lemma-HH-M-1) ⟩
      ⟦ s ⟧↥ • Mz x • Mz -'₁ ≈⟨ (cright axiom (M-mul x -'₁)) ⟩
      ⟦ s ⟧↥ • Mz (x *' -'₁) ≈⟨ sym (cong refl right-unit) ⟩
      ⟦ s ⟧↥ • Mz (x *' -'₁) • ε ≈⟨ refl ⟩
      ⟦ nf' ⟧ ∎
    
  Lemma-single-qupit-completeness nf@(𝕊 l ∙ M (y , nzy) ∙ HS x@(₁₊ k')) (Symℕ.H-gen ₁) pg = nf' , claim
    where
    x' : ℤ* ₚ
    x' = (x , λ ())
    nz = x' .proj₂
    x⁻¹ = ((x , nz) ⁻¹) .proj₁
    x⁻¹⁻¹ = (((x , nz) ⁻¹) ⁻¹) .proj₁
    -x⁻¹ = - x⁻¹
    -y/x' = (((y , nzy) *' ((x , nz) ⁻¹)) *' -'₁)
    -y/x = -y/x' .proj₁

    nf' = 𝕊 (l + -x⁻¹ * (y * y)) ∙ M -y/x' ∙ (HS -x⁻¹)
    claim : ⟦ 𝕊 l ∙ M (y , nzy) ∙ HS (₁₊ k') ⟧ • [ H-gen ₁ ]ʷ ≈ ⟦ nf' ⟧
    claim = begin
      ⟦ 𝕊 l ∙ M (y , nzy) ∙ HS (₁₊ k') ⟧ • [ H-gen ₁ ]ʷ ≈⟨ trans assoc (cong refl assoc) ⟩
      S^ l • Mz (y , nzy) • (H • S^ (₁₊ k')) • H ≈⟨ (cright cright assoc) ⟩
      S^ l • Mz (y , nzy) • H • S^ (₁₊ k') • H ≈⟨ (cright derived-7 x y nz nzy) ⟩
      S^ l • S^ (-x⁻¹ * (y * y)) • Mz -y/x' • (H • S^ -x⁻¹) ≈⟨ sym assoc ⟩
      (S^ l • S^ (-x⁻¹ * (y * y))) • Mz -y/x' • (H • S^ -x⁻¹) ≈⟨ (cleft lemma-S^k+l l (-x⁻¹ * (y * y))) ⟩
      ⟦ nf' ⟧ ∎
  
  Lemma-single-qupit-completeness nf@(𝕊 l ∙ M (y , nzy) ∙ ε) (Symℕ.S-gen ₁) pg = nf' , claim
    where
    nf' = 𝕊 (l + y * y) ∙ M (y , nzy) ∙ ε
    claim : ⟦ 𝕊 l ∙ M (y , nzy) ∙ ε ⟧ • [ S-gen ₁ ]ʷ ≈ ⟦ nf' ⟧
    claim = begin
      ⟦ 𝕊 l ∙ M (y , nzy) ∙ ε ⟧ • [ S-gen ₁ ]ʷ ≈⟨ trans assoc (cong refl assoc) ⟩
      S^ l • Mz (y , nzy) • ε • [ S-gen ₁ ]ʷ ≈⟨ cong refl (cong refl left-unit) ⟩
      S^ l • Mz (y , nzy) • S ≈⟨ (cright axiom (semi-MS (y , nzy))) ⟩
      S^ l • S^ (y * y) • Mz (y , nzy) ≈⟨ sym assoc ⟩
      (S^ l • S^ (y * y)) • Mz (y , nzy) ≈⟨ (cleft lemma-S^k+l l (y * y)) ⟩
      S^ (l + (y * y)) • Mz (y , nzy) ≈⟨ sym (cong refl right-unit) ⟩
      ⟦ nf' ⟧ ∎
      
  Lemma-single-qupit-completeness nf@(s ∙ m ∙ HS k) (Symℕ.S-gen ₁) pg = nf' , claim
    where
    k' = k + ₁
    nf' = s ∙ m ∙ HS k'
    claim : ⟦ s ∙ m ∙ HS k ⟧ • [ S-gen ₁ ]ʷ ≈ ⟦ nf' ⟧
    claim = begin
      ⟦ s ∙ m ∙ HS k ⟧ • [ S-gen ₁ ]ʷ ≈⟨ trans assoc (cong refl assoc) ⟩
      ⟦ s ⟧↥ • ⟦ m ⟧ₘ • (H • S^ k) • S ≈⟨ refl ⟩
      ⟦ s ⟧↥ • ⟦ m ⟧ₘ • (H • S^ k) • S^ ₁ ≈⟨ (cright cright assoc) ⟩
      ⟦ s ⟧↥ • ⟦ m ⟧ₘ • H • S^ k • S^ ₁ ≈⟨ (cright cright cright lemma-S^k+l k ₁) ⟩
      ⟦ s ⟧↥ • ⟦ m ⟧ₘ • H • S^ (k + ₁) ≈⟨ refl ⟩
      ⟦ nf' ⟧ ∎

  Corollary-single-qupit-completeness :
    
    ∀ (nf : NF1) (w : Word Gen) (pw : PrimitiveWord w) ->
    -----------------------------------------------
    ∃ \ nf' -> ⟦ nf ⟧ • w ≈ ⟦ nf' ⟧

  Corollary-single-qupit-completeness nf [ x ]ʷ pw = Lemma-single-qupit-completeness nf x pw
  Corollary-single-qupit-completeness nf ε pw = nf , right-unit
  Corollary-single-qupit-completeness nf (w • w₁) (pwl , pwr) with Corollary-single-qupit-completeness nf w pwl
  ... | (nf' , ih) with Corollary-single-qupit-completeness nf' w₁ pwr
  ... | (nf'' , ih2) = nf'' , claim
    where
    claim : (⟦ nf ⟧ • w • w₁) ≈ ⟦ nf'' ⟧
    claim = begin
      (⟦ nf ⟧ • w • w₁) ≈⟨ sym assoc ⟩
      (⟦ nf ⟧ • w) • w₁ ≈⟨ (cleft ih) ⟩
      (⟦ nf' ⟧) • w₁ ≈⟨ ih2 ⟩
      ⟦ nf'' ⟧ ∎
    

  Theorem-single-qupit-completeness :
    
    ∀ (nf : NF1) (g : Gen) ->
    ------------------------------------
    ∃ \ nf' -> ⟦ nf ⟧ • [ g ]ʷ ≈ ⟦ nf' ⟧
    
  Theorem-single-qupit-completeness nf g with Corollary-single-qupit-completeness nf (desugar-gen g) (lemma-desugar-gen g)
  ... | (nf' , hyp) = nf' , claim
    where
    claim : ⟦ nf ⟧ • [ g ]ʷ ≈ ⟦ nf' ⟧
    claim = begin
      ⟦ nf ⟧ • [ g ]ʷ ≈⟨ sym (cright lemma-desugar-gen-≈ g) ⟩
      ⟦ nf ⟧ • desugar-gen g ≈⟨ hyp ⟩
      ⟦ nf' ⟧ ∎

  nf₀ = (𝕊 ₀ ∙ M (₁ , λ ()) ∙ ε)
  lemma-nf₀ : ⟦ nf₀ ⟧ ≈ ε
  lemma-nf₀ = begin
    ⟦ nf₀ ⟧ ≈⟨ cong (axiom (derived-S ₀)) (cong (sym lemma-M1) refl) ⟩
    ε • ε • ε ≈⟨ trans left-unit left-unit ⟩
    ε ∎

  Theorem-single-qupit-completeness-nfw :
    
    ∀ (w : Word Gen) ->
    ----------------------
    ∃ \ nf' -> w ≈ ⟦ nf' ⟧

  Theorem-single-qupit-completeness-nfw [ x ]ʷ with Theorem-single-qupit-completeness nf₀ x
  ... | (nf' , hyp) = nf' , claim
    where
    claim : [ x ]ʷ ≈ ⟦ nf' ⟧
    claim = begin
      [ x ]ʷ ≈⟨ sym left-unit ⟩
      ε • [ x ]ʷ ≈⟨ cleft sym lemma-nf₀ ⟩
      (S^ ₀ • M₁ • ε) • [ x ]ʷ ≈⟨ hyp ⟩
      ⟦ nf' ⟧ ∎
  Theorem-single-qupit-completeness-nfw ε = nf₀ , sym lemma-nf₀
  Theorem-single-qupit-completeness-nfw (w • w₁) with Theorem-single-qupit-completeness-nfw w
  ... | (nf1 , ih1) with Corollary-single-qupit-completeness nf1 (desugar-word w₁) (lemma-desugar-word w₁)
  ... | (nf2 , hyp)= nf2 , claim
    where
    claim : w • w₁ ≈ ⟦ nf2 ⟧
    claim = begin
      w • w₁ ≈⟨ cong ih1 refl ⟩
      ⟦ nf1 ⟧ • w₁ ≈⟨ (cright sym (lemma-desugar-word-≈ w₁)) ⟩
      ⟦ nf1 ⟧ • desugar-word w₁ ≈⟨ hyp ⟩
      ⟦ nf2 ⟧ ∎


module Iso (p-2 : ℕ) (p-prime : Prime (₂₊ p-2)) where
  p : ℕ
  p = ₂₊ p-2
  open import Zp.ModularArithmetic
  open PrimeModulus p-2 p-prime hiding (p ; 0ₚ ; 1ₚ ; 0ₚ≢1ₚ)

  module Sym  = Symplectic p-2 p-prime
  module SymDerived  = Symℕ p-2 p-prime
  open Sym renaming (grouplike to grouplike₁ ; Gen to Gen₁) using ()
  open SymDerived renaming (grouplike to grouplike₂ ; Gen to Gen₂) using ()



  f : Sym.Gen -> SymDerived.Gen
  f Symplectic.H-gen = SymDerived.H-gen ₁
  f Symplectic.S-gen = SymDerived.S-gen ₁

  g : SymDerived.Gen -> Word Sym.Gen
  g (SymDerived.H-gen k) = Sym.H ^ toℕ k
  g (SymDerived.S-gen k) = Sym.S ^ toℕ k
  

  open PB Sym._===_ renaming (_===_ to _===₁_ ; _≈_ to _≈₁_) using ()
  open PB SymDerived._===_ renaming (_===_ to _===₂_ ; _≈_ to _≈₂_) using ()

  open import Presentation.Morphism _===₁_ _===₂_
  open GroupMorphs grouplike₁ grouplike₂

  open PP Sym._===_ renaming (by-assoc-and to by-assoc-and₁ ; word-setoid to ws₁)
  open PP SymDerived._===_ renaming (by-assoc-and to by-assoc-and₂ ; word-setoid to ws₂ ; by-assoc to by-assoc₂) using ()

  open PB hiding (_===_)
  open SymDerived hiding (p)

  f* = wmap f
  f' = [_]ʷ ∘ f
  f'* = f' WB.*
  
  lemma-f* : ∀ k -> f* (Sym.S ^ k) ≈₂ SymDerived.S ^ k
  lemma-f* ₀ = _≈₂_.refl
  lemma-f* ₁ = _≈₂_.refl
  lemma-f* (₂₊ k) = cong _≈₂_.refl (lemma-f* (₁₊ k))

  lemma-f'* : ∀ k -> f'* (Sym.S ^ k) ≈₂ SymDerived.S ^ k
  lemma-f'* ₀ = _≈₂_.refl
  lemma-f'* ₁ = _≈₂_.refl
  lemma-f'* (₂₊ k) = cong _≈₂_.refl (lemma-f'* (₁₊ k))

  lemma-f'*-H : ∀ k -> f'* (Sym.H ^ k) ≈₂ SymDerived.H ^ k
  lemma-f'*-H ₀ = _≈₂_.refl
  lemma-f'*-H ₁ = _≈₂_.refl
  lemma-f'*-H (₂₊ k) = cong _≈₂_.refl (lemma-f'*-H (₁₊ k))

  lemma-f'*-M : ∀ x -> f'* (Sym.M x) ≈₂ SymDerived.M x
  lemma-f'*-M x' = begin
    f'* (Sym.M x') ≈⟨ _≈₂_.refl ⟩
    f'* (Sym.S^ x • Sym.H • Sym.S^ x⁻¹ • Sym.H • Sym.S^ x • Sym.H) ≈⟨ _≈₂_.refl ⟩
    f'* (Sym.S^ x) • f'* Sym.H • f'* (Sym.S^ x⁻¹) • f'* Sym.H • f'* (Sym.S^ x) • f'* (Sym.H) ≈⟨ cong (lemma-f'* (toℕ x)) (cong _≈₂_.refl (cong (lemma-f'* (toℕ x⁻¹)) (cong _≈₂_.refl (cong (lemma-f'* (toℕ x)) _≈₂_.refl)))) ⟩
    (S ^ toℕ x) • H • (S ^ toℕ x⁻¹) • H • (S ^ toℕ x) • (H) ≈⟨ cong (_≈₂_.sym (_≈₂_.axiom (derived-S x))) (cong _≈₂_.refl (cong (_≈₂_.sym (_≈₂_.axiom (derived-S x⁻¹))) (cong _≈₂_.refl (_≈₂_.sym (_≈₂_.cong (_≈₂_.axiom (derived-S x)) _≈₂_.refl))))) ⟩
    (S^ x) • H • (S^ x⁻¹) • H • (S^ x) • (H) ≈⟨ _≈₂_.refl ⟩
    M x' ∎
    where
    open SR ws₂
    x = x' .proj₁
    x⁻¹ = ((x' ⁻¹) .proj₁ )
    

  f-well-defined : ∀ {w v} -> w ===₁ v -> f'* w ≈₂ f'* v
  f-well-defined Symplectic.order-S = begin
    f'* (Sym.S • Sym.S ^ ₁₊ p-2) ≡⟨ lemma-* ([ Sym.S-gen ]ʷ • Sym.S ^ ₁₊ p-2) ⟩
    (wmap f) (Sym.S • Sym.S ^ ₁₊ p-2) ≈⟨ lemma-f* (₂₊ p-2) ⟩
    SymDerived.S ^ p ≈⟨ _≈₂_.axiom order-S ⟩
    f'* ε ∎
    where
    open SR ws₂
  f-well-defined Symplectic.order-H = axiom order-H
  f-well-defined Symplectic.order-SH = _≈₂_.axiom order-SH
  f-well-defined Symplectic.comm-HHS = _≈₂_.axiom comm-HHS
  f-well-defined (Symplectic.M-mul x y) = begin
    f'* (Sym.M x • Sym.M y) ≈⟨ _≈₂_.refl ⟩
    f'* (Sym.M x) • f'* (Sym.M y) ≈⟨ cong (lemma-f'*-M x) (lemma-f'*-M y) ⟩
    (SymDerived.M x) • (SymDerived.M y) ≈⟨ axiom (M-mul x y) ⟩
    (SymDerived.M (x *' y)) ≈⟨ sym (lemma-f'*-M (x *' y)) ⟩
    f'* (Sym.M (x *' y)) ∎
    where
    open SR ws₂
  f-well-defined (Symplectic.semi-MS (x , nz)) = begin
    f'* (Sym.M (x , nz) • Sym.S) ≈⟨ cong (lemma-f'*-M (x , nz)) (lemma-f'* ₁) ⟩
    (M (x , nz) • S) ≈⟨ _≈₂_.axiom (semi-MS (x , nz)) ⟩
    (S^ (x * x) • M (x , nz)) ≈⟨ _≈₂_.cong (_≈₂_.axiom (derived-S (x * x))) _≈₂_.refl ⟩
    (S ^ toℕ (x * x) • M (x , nz)) ≈⟨ cong (sym (lemma-f'* (toℕ (x * x)))) (sym (lemma-f'*-M (x , nz))) ⟩
    f'* (Sym.S^ (x * x) • Sym.M (x , nz)) ∎
    where
    open SR ws₂

  g* = g WB.*

  lemma-g* : ∀ k -> g* (S ^ k) ≈₁ Sym.S ^ k
  lemma-g* ₀ = refl
  lemma-g* ₁ = refl
  lemma-g* (₂₊ k) = cong refl (lemma-g* (₁₊ k))

  lemma-g*-H : ∀ k -> g* (H ^ k) ≈₁ Sym.H ^ k
  lemma-g*-H ₀ = refl
  lemma-g*-H ₁ = refl
  lemma-g*-H (₂₊ k) = cong refl (lemma-g*-H (₁₊ k))

  lemma-g*'-H : ∀ k -> g* (H^ k) ≈₁ Sym.H ^ toℕ k
  lemma-g*'-H ₀ = refl
  lemma-g*'-H ₁ = refl
  lemma-g*'-H ₂ = refl
  lemma-g*'-H ₃ = refl


  lemma-g*-M : ∀ x -> g* (M x) ≈₁ Sym.M x
  lemma-g*-M x' = begin
    g* (M x') ≈⟨ refl ⟩
    g* (S^ x • H • S^ x⁻¹ • H • S^ x • H) ≈⟨ refl ⟩
    g* (S^ x) • g* H • g* (S^ x⁻¹) • g* H • g* (S^ x) • g* (H) ≈⟨ cong (sym ( lemma-g* (toℕ x))) (cong refl (cong (sym ( lemma-g* (toℕ x⁻¹))) (cong refl (sym (cong ( lemma-g* (toℕ x)) refl))))) ⟩
    g* (S ^ toℕ x) • g* H • g* (S ^ toℕ x⁻¹) • g* H • g* (S ^ toℕ x) • g* (H) ≈⟨ cong (lemma-g* (toℕ x)) (cong refl (cong (lemma-g* (toℕ x⁻¹)) (cong refl (cong (lemma-g* (toℕ x)) refl)))) ⟩
    (Sym.S ^ toℕ x) • Sym.H • (Sym.S ^ toℕ x⁻¹) • Sym.H • (Sym.S ^ toℕ x) • (Sym.H) ≈⟨ refl ⟩
    (Sym.S^ x) • Sym.H • (Sym.S^ x⁻¹) • Sym.H • (Sym.S^ x) • (Sym.H) ≈⟨ refl ⟩
    Sym.M x' ∎
    where
    open SR ws₁
    x = x' .proj₁
    x⁻¹ = ((x' ⁻¹) .proj₁ )

  g-well-defined : ∀ {w v} -> w ===₂ v -> g* w ≈₁ g* v
  g-well-defined Symℕ.order-S = begin
    g* (S • S ^ ₁₊ p-2) ≈⟨ lemma-g* p ⟩
    (Sym.S ^ p) ≈⟨ axiom Sym.order-S ⟩
    g* ε ∎
    where open SR ws₁
  g-well-defined Symℕ.order-H = axiom Sym.order-H
  g-well-defined Symℕ.order-SH = axiom Sym.order-SH
  g-well-defined Symℕ.comm-HHS = axiom Sym.comm-HHS
  g-well-defined (Symℕ.M-mul x y) = begin
    g* (M x • M y) ≈⟨ refl ⟩
    g* (M x) • g* (M y) ≈⟨ cong (lemma-g*-M x) (lemma-g*-M y) ⟩
    (Sym.M x) • (Sym.M y) ≈⟨ axiom (Sym.M-mul x y) ⟩
    (Sym.M (x *' y)) ≈⟨ sym (lemma-g*-M (x *' y)) ⟩
    g* (M (x *' y)) ∎
    where
    open SR ws₁
  g-well-defined (Symℕ.semi-MS (x , nz)) = begin
    g* (M (x , nz) • S) ≈⟨ cong (lemma-g*-M (x , nz)) (lemma-g* ₁) ⟩
    (Sym.M (x , nz) • Sym.S) ≈⟨ axiom (Sym.semi-MS (x , nz)) ⟩
    (Sym.S^ (x * x) • Sym.M (x , nz)) ≈⟨ cong (refl) refl ⟩
    (Sym.S ^ toℕ (x * x) • Sym.M (x , nz)) ≈⟨ cong (sym (lemma-g* (toℕ (x * x)))) (sym (lemma-g*-M (x , nz))) ⟩
    g* (S ^ toℕ (x * x) • M (x , nz)) ≈⟨ cong (sym (g-well-defined (derived-S (fromℕ< _)))) refl ⟩
    g* (S^ (x * x) • M (x , nz)) ∎
    where
    open SR ws₁
  g-well-defined (Symℕ.derived-S k) = begin
    g* [ S-gen k ]ʷ ≈⟨ refl ⟩
    Sym.S ^ toℕ k ≈⟨ sym (lemma-g* (toℕ k)) ⟩
    g* (S ^ toℕ k) ∎
    where
    open SR ws₁
  g-well-defined (Symℕ.derived-H k) = begin
    g* [ H-gen k ]ʷ ≈⟨ lemma-g*'-H k ⟩
    Sym.H ^ toℕ k ≈⟨ sym (lemma-g*-H (toℕ k)) ⟩
    g* (H ^ toℕ k) ∎
    where
    open SR ws₁


  f-left-inv-gen : ∀ x -> [ x ]ʷ ≈₂ (f'*) (g x)
  f-left-inv-gen (SymDerived.H-gen k) = begin
    [ H-gen k ]ʷ ≈⟨ _≈₂_.axiom (derived-H k) ⟩
    H ^ toℕ k ≈⟨ sym (lemma-f'*-H (toℕ k)) ⟩
    f'* (Sym.H ^ toℕ k) ∎
    where open SR ws₂
  f-left-inv-gen (SymDerived.S-gen k) = begin
    [ S-gen k ]ʷ ≈⟨ _≈₂_.axiom (derived-S k) ⟩
    S ^ toℕ k ≈⟨ sym (lemma-f'* (toℕ k)) ⟩
    f'* (Sym.S ^ toℕ k) ∎
    where open SR ws₂

  g-left-inv-gen : ∀ x -> [ x ]ʷ ≈₁ (g*) (f' x)
  g-left-inv-gen Sym.S-gen = refl
  g-left-inv-gen Sym.H-gen = refl

  open import Algebra.Bundles using (Group)
  open import Algebra.Morphism.Structures using (module GroupMorphisms)

  open import Presentation.Morphism
  open GroupMorphisms
  module G1 = Group-Lemmas Sym.Gen Sym._===_ Sym.grouplike
  module G2 = Group-Lemmas SymDerived.Gen SymDerived._===_ SymDerived.grouplike

  Theorem-Sym-iso-SymDerived : IsGroupIsomorphism (Group.rawGroup G1.•-ε-group) (Group.rawGroup G2.•-ε-group) (f'*)
  Theorem-Sym-iso-SymDerived = StarGroupIsomorphism.isGroupIsomorphism f' g f-well-defined  f-left-inv-gen g-well-defined  g-left-inv-gen

