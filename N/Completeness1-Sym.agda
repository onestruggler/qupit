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
open import Presentation.Tactics hiding ([_])
open import Data.Nat.Primality



module N.Completeness1-Sym (p-2 : ℕ) (p-prime : Prime (2+ p-2))  where

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


open import Zp.ModularArithmetic
open PrimeModulus p-2 p-prime
open import N.Symplectic p-2 p-prime
open import N.Lemmas-2Qupit p-2 p-prime
open import N.NF1-Sym p-2 p-prime
open import N.Cosets p-2 p-prime
open Lemmas-2Q 2
open Symplectic
--open Normal-Form1

module Completeness where

  private
    variable
      n : ℕ
      

  TopwGen : Gen (₁₊ n) -> Set
  TopwGen (H-gen) = ⊤
  TopwGen (S-gen) = ⊤
  TopwGen _ = ⊥

  TopwWord : Word(Gen (₁₊ n)) -> Set
  TopwWord [ x ]ʷ = TopwGen x
  TopwWord ε = ⊤
  TopwWord (w • w₁) = TopwWord w × TopwWord w₁

  -- desugar-gen :(Gen (₁₊ n)) -> Word(Gen (₁₊ n))
  -- desugar-gen (H-gen x) = H ^ toℕ x
  -- desugar-gen (S-gen x) = S ^ toℕ x
  -- desugar-gen (CZ-gen x) = CZ ^ toℕ x
  -- desugar-gen {₁₊ n} (x ↥) = (desugar-gen x) ↑

  -- desugar-word : Word (Gen (₁₊ n)) -> Word(Gen (₁₊ n))
  -- desugar-word = desugar-gen WB.*


  -- lemma-H^-Prim : ∀ x -> TopwWord {n} (H ^ x)
  -- lemma-H^-Prim ₀ = tt
  -- lemma-H^-Prim ₁ = tt
  -- lemma-H^-Prim (₂₊ k) = tt , (lemma-H^-Prim (₁₊ k))

  -- lemma-S^-Prim : ∀ x -> TopwWord {n} (S ^ x)
  -- lemma-S^-Prim ₀ = tt
  -- lemma-S^-Prim ₁ = tt
  -- lemma-S^-Prim (₂₊ k) = tt , (lemma-S^-Prim (₁₊ k))

  -- lemma-desugar-gen : (g :(Gen (₁₊ n))) -> TopwGen g -> TopwWord (desugar-gen g)
  -- lemma-desugar-gen (H-gen x) pg = lemma-H^-Prim (toℕ x)
  -- lemma-desugar-gen (S-gen x) pg = lemma-S^-Prim (toℕ x)
  
  -- lemma-desugar-word : (w : Word(Gen (₁₊ n))) ->  TopwWord w -> TopwWord (desugar-word w)
  -- lemma-desugar-word [ x ]ʷ pg = lemma-desugar-gen x pg
  -- lemma-desugar-word ε pg = tt
  -- lemma-desugar-word (w • w₁) (pgl , pgr)= (lemma-desugar-word w pgl) , (lemma-desugar-word w₁ pgr)


  -- lemma-desugar-gen-≈ : let open PB ((₁₊ n) QRel,_===_) in
  --   (g :(Gen (₁₊ n))) -> desugar-gen g ≈ [ g ]ʷ
  -- lemma-desugar-gen-≈ (H-gen x) = PB.sym (PB.axiom (derived-H x))
  -- lemma-desugar-gen-≈ (S-gen x) = PB.sym (PB.axiom (derived-S x))
  -- lemma-desugar-gen-≈ (CZ-gen x) = PB.sym (PB.axiom (derived-CZ x))
  -- lemma-desugar-gen-≈ {₁₊ n} (x ↥) = lemma-cong↑ _ _ (lemma-desugar-gen-≈ x)


  -- lemma-desugar-word-≈ : let open PB ((₁₊ n) QRel,_===_) in
  --   (w : Word(Gen (₁₊ n))) -> desugar-word w ≈ w
  -- lemma-desugar-word-≈ [ x ]ʷ = lemma-desugar-gen-≈ x
  -- lemma-desugar-word-≈ ε = PB.refl
  -- lemma-desugar-word-≈ (w • w₁) = PB.cong (lemma-desugar-word-≈ w) (lemma-desugar-word-≈ w₁)


  

  Lemma-single-qupit-completeness : let open PB ((₁₊ n) QRel,_===_) in
    
    ∀ (nf : NF1) (g : Gen (₁₊ n)) -> (tg : TopwGen g) ->
    -----------------------------------------------
    ∃ \ nf' -> ⟦ nf ⟧₁ • [ g ]ʷ ≈ ⟦ nf' ⟧₁
    
  Lemma-single-qupit-completeness {n} nf@(s , m , ε) (H-gen) tg = (s , m , HS^ ₀) , claim
    where
    open PB ((₁₊ n) QRel,_===_)
    open PP ((₁₊ n) QRel,_===_)
    open SR word-setoid
    open Pattern-Assoc
    claim : (⟦ s ⟧ₛ • ⟦ m ⟧ₘ • ε) • [ H-gen ]ʷ ≈ ⟦ s ⟧ₛ • ⟦ m ⟧ₘ • H • S^ ₀
    claim = begin
      (⟦ s ⟧ₛ • ⟦ m ⟧ₘ • ε) • H ≈⟨ _≈_.cong (_≈_.cong refl right-unit) refl ⟩
      (⟦ s ⟧ₛ • ⟦ m ⟧ₘ) • H ≈⟨ by-assoc auto ⟩
      (⟦ s ⟧ₛ • ⟦ m ⟧ₘ) • H • ε ≈⟨ (cright cright _≈_.sym (refl)) ⟩
      (⟦ s ⟧ₛ • ⟦ m ⟧ₘ) • H • S^ ₀ ≈⟨ assoc ⟩
      ⟦ s ⟧ₛ • ⟦ m ⟧ₘ • H • S^ ₀ ∎


  Lemma-single-qupit-completeness {n} nf@(s , x , HS^ ₀) (H-gen) tg = nf' , claim
    where
    open PB ((₁₊ n) QRel,_===_)
    open PP ((₁₊ n) QRel,_===_)
    open SR word-setoid
    open Pattern-Assoc
    open Lemmas0 n

    x'  = x *' -'₁
    nf' = s , x' , ε
    claim : ⟦ s , x , HS^ ₀ ⟧₁ • [ H-gen ]ʷ ≈ ⟦ nf' ⟧₁
    claim = begin
      ⟦ s , x , HS^ ₀ ⟧₁ • [ H-gen ]ʷ ≈⟨ (cleft (cright (cright (cright refl)))) ⟩
      (⟦ s ⟧ₛ • M x • (H • ε)) • H ≈⟨ trans assoc (cright assoc) ⟩
      ⟦ s ⟧ₛ • M x • (H • ε) • H ≈⟨ (cright cright cong right-unit refl) ⟩
      ⟦ s ⟧ₛ • M x • HH ≈⟨ (cright cright lemma-HH-M-1) ⟩
      ⟦ s ⟧ₛ • M x • M -'₁ ≈⟨ (cright axiom (M-mul x -'₁)) ⟩
      ⟦ s ⟧ₛ • M (x *' -'₁) ≈⟨ sym (cong refl right-unit) ⟩
      ⟦ s ⟧ₛ • M (x *' -'₁) • ε ≈⟨ refl ⟩
      ⟦ nf' ⟧₁ ∎

  Lemma-single-qupit-completeness {n} nf@(l , (y , nzy) , HS^ x@(₁₊ k')) (H-gen) tg = nf' , claim
    where
    open PB ((₁₊ n) QRel,_===_)
    open PP ((₁₊ n) QRel,_===_)
    open SR word-setoid
    open Pattern-Assoc
    open Lemmas0 n

    x' : ℤ* ₚ
    x' = (x , λ ())
    nz = x' .proj₂
    x⁻¹ = ((x , nz) ⁻¹) .proj₁
    x⁻¹⁻¹ = (((x , nz) ⁻¹) ⁻¹) .proj₁
    -x⁻¹ = - x⁻¹
    -y/x' = (((y , nzy) *' ((x , nz) ⁻¹)) *' -'₁)
    -y/x = -y/x' .proj₁

    nf' = (l + -x⁻¹ * (y * y)) , -y/x' , (HS^ -x⁻¹)
    claim : ⟦ l , (y , nzy) , HS^ (₁₊ k') ⟧₁ • [ H-gen ]ʷ ≈ ⟦ nf' ⟧₁
    claim = begin
      ⟦ l , (y , nzy) , HS^ (₁₊ k') ⟧₁ • [ H-gen ]ʷ ≈⟨ trans assoc (cong refl assoc) ⟩
      S^ l • M (y , nzy) • (H • S^ (₁₊ k')) • H ≈⟨ (cright cright assoc) ⟩
      S^ l • M (y , nzy) • H • S^ (₁₊ k') • H ≈⟨ (cright derived-7 x y nz nzy) ⟩
      S^ l • S^ (-x⁻¹ * (y * y)) • M -y/x' • (H • S^ -x⁻¹) ≈⟨ sym assoc ⟩
      (S^ l • S^ (-x⁻¹ * (y * y))) • M -y/x' • (H • S^ -x⁻¹) ≈⟨ (cleft lemma-S^k+l l (-x⁻¹ * (y * y))) ⟩
      ⟦ nf' ⟧₁ ∎

  Lemma-single-qupit-completeness {n} nf@(l , (y , nzy) , ε) (S-gen) tg = nf' , claim
    where
    open PB ((₁₊ n) QRel,_===_)
    open PP ((₁₊ n) QRel,_===_)
    open SR word-setoid
    open Pattern-Assoc
    open Lemmas0 n

    nf' = (l + y * y) , (y , nzy) , ε
    claim : ⟦ l , (y , nzy) , ε ⟧₁ • [ S-gen ]ʷ ≈ ⟦ nf' ⟧₁
    claim = begin
      ⟦ l , (y , nzy) , ε ⟧₁ • [ S-gen ]ʷ ≈⟨ trans assoc (cong refl assoc) ⟩
      S^ l • M (y , nzy) • ε • [ S-gen ]ʷ ≈⟨ cong refl (cong refl left-unit) ⟩
      S^ l • M (y , nzy) • S ≈⟨ (cright axiom (semi-MS (y , nzy))) ⟩
      S^ l • S^ (y * y) • M (y , nzy) ≈⟨ sym assoc ⟩
      (S^ l • S^ (y * y)) • M (y , nzy) ≈⟨ (cleft lemma-S^k+l l (y * y)) ⟩
      S^ (l + (y * y)) • M (y , nzy) ≈⟨ sym (cong refl right-unit) ⟩
      ⟦ nf' ⟧₁ ∎
      
  Lemma-single-qupit-completeness {n} nf@(s , m , HS^ k) (S-gen) tg = nf' , claim
    where
    open PB ((₁₊ n) QRel,_===_)
    open PP ((₁₊ n) QRel,_===_)
    open SR word-setoid
    open Pattern-Assoc
    open Lemmas0 n

    k' = k + ₁
    nf' = s , m , HS^ k'
    claim : ⟦ s , m , HS^ k ⟧₁ • [ S-gen ]ʷ ≈ ⟦ nf' ⟧₁
    claim = begin
      ⟦ s , m , HS^ k ⟧₁ • [ S-gen ]ʷ ≈⟨ trans assoc (cong refl assoc) ⟩
      ⟦ s ⟧ₛ • ⟦ m ⟧ₘ • (H • S^ k) • S ≈⟨ refl ⟩
      ⟦ s ⟧ₛ • ⟦ m ⟧ₘ • (H • S^ k) • S^ ₁ ≈⟨ (cright cright assoc) ⟩
      ⟦ s ⟧ₛ • ⟦ m ⟧ₘ • H • S^ k • S^ ₁ ≈⟨ (cright cright cright lemma-S^k+l k ₁) ⟩
      ⟦ s ⟧ₛ • ⟦ m ⟧ₘ • H • S^ (k + ₁) ≈⟨ refl ⟩
      ⟦ nf' ⟧₁ ∎

  Corollary-single-qupit-completeness : let open PB ((₁₊ n) QRel,_===_) in
    
    ∀ (nf : NF1) (w : Word (Gen (₁₊ n))) -> (tg : TopwWord w) ->
    --------------------------------------------------------
    ∃ \ nf' -> ⟦ nf ⟧₁ • w ≈ ⟦ nf' ⟧₁

  Corollary-single-qupit-completeness nf [ x ]ʷ tg = Lemma-single-qupit-completeness nf x tg
  Corollary-single-qupit-completeness nf ε tg = nf , PB.right-unit
  Corollary-single-qupit-completeness {n} nf (w • w₁) (tgl , tgr) with Corollary-single-qupit-completeness nf w tgl
  ... | (nf' , ih) with Corollary-single-qupit-completeness nf' w₁ tgr
  ... | (nf'' , ih2) = nf'' , claim
    where
    open PB ((₁₊ n) QRel,_===_)
    open PP ((₁₊ n) QRel,_===_)
    open SR word-setoid
    open Pattern-Assoc
    open Lemmas0 n

    claim : (⟦ nf ⟧₁ • w • w₁) ≈ ⟦ nf'' ⟧₁
    claim = begin
      (⟦ nf ⟧₁ • w • w₁) ≈⟨ sym assoc ⟩
      (⟦ nf ⟧₁ • w) • w₁ ≈⟨ (cleft ih) ⟩
      (⟦ nf' ⟧₁) • w₁ ≈⟨ ih2 ⟩
      ⟦ nf'' ⟧₁ ∎


  nf₀ : NF1
  nf₀ = (₀ , (₁ , λ ()) , ε)
  lemma-nf₀ : let open PB ((₁₊ n) QRel,_===_) in ⟦ nf₀ ⟧₁ ≈ ε
  lemma-nf₀ {n} = begin
    ⟦ nf₀ ⟧₁ ≈⟨ cong refl (cong (sym lemma-M1) refl) ⟩
    ε • ε • ε ≈⟨ trans left-unit left-unit ⟩
    ε ∎
    where
    open PB ((₁₊ n) QRel,_===_)
    open PP ((₁₊ n) QRel,_===_)
    open SR word-setoid
    open Lemmas0 n



  Theorem-single-qupit-completeness : let open PB ((₁₊ n) QRel,_===_) in
    
    ∀ (w : Word (Gen (₁₊ n))) -> (tg : TopwWord w) ->
    --------------------------------------------------------
    ∃ \ nf' -> w ≈ ⟦ nf' ⟧₁

  Theorem-single-qupit-completeness {n} [ x ]ʷ tg with Corollary-single-qupit-completeness nf₀ [ x ]ʷ tg
  ... | (nf' , hyp) = nf' , claim
    where
    open PB ((₁₊ n) QRel,_===_)
    open PP ((₁₊ n) QRel,_===_)
    open SR word-setoid
    open Pattern-Assoc
    open Lemmas0 n
    claim : [ x ]ʷ ≈ ⟦ nf' ⟧₁
    claim = begin
      [ x ]ʷ ≈⟨ sym left-unit ⟩
      ε • [ x ]ʷ ≈⟨ cleft sym lemma-nf₀ ⟩
      (S^ ₀ • M₁ • ε) • [ x ]ʷ ≈⟨ hyp ⟩
      ⟦ nf' ⟧₁ ∎
    
  Theorem-single-qupit-completeness {n} ε tg = nf₀ , sym lemma-nf₀
    where
    open PB ((₁₊ n) QRel,_===_)
  Theorem-single-qupit-completeness {n} (w • w₁) (tgl , tgr) with Theorem-single-qupit-completeness w tgl
  ... | (nf1 , ih1) with Corollary-single-qupit-completeness nf1 w₁ tgr
  ... | (nf2 , ih2) = nf2 , claim
    where
    open PB ((₁₊ n) QRel,_===_)
    open PP ((₁₊ n) QRel,_===_)
    open SR word-setoid
    open Pattern-Assoc
    open Lemmas0 n

    claim : w • w₁ ≈ ⟦ nf2 ⟧₁
    claim = begin
      w • w₁ ≈⟨ cong ih1 refl ⟩
      ⟦ nf1 ⟧₁ • w₁ ≈⟨ ih2 ⟩
      ⟦ nf2 ⟧₁ ∎


  Lemma-single-qupit-completeness-mc-H : let open PB ((₁₊ n) QRel,_===_) in
    
    ∀ (mc : MC) ->
    -----------------------------------------------
    ∃ \ k -> ∃ \ mc' -> ⟦ mc ⟧ₘ₊ • H ≈ S^ k • ⟦ mc' ⟧ₘ₊
    
  Lemma-single-qupit-completeness-mc-H {n} mc@(m , ε) = ₀ , (m , HS^ ₀) , claim
    where
    open PB ((₁₊ n) QRel,_===_)
    open PP ((₁₊ n) QRel,_===_)
    open SR word-setoid
    open Pattern-Assoc
    claim : (⟦ m ⟧ₘ • ε) • [ H-gen ]ʷ ≈ ε • ⟦ m ⟧ₘ • H • S^ ₀
    claim = trans (cong right-unit (sym right-unit)) (sym left-unit) 

  Lemma-single-qupit-completeness-mc-H {n} mc@(x , HS^ ₀) = ₀ , mc' , claim
    where
    open PB ((₁₊ n) QRel,_===_)
    open PP ((₁₊ n) QRel,_===_)
    open SR word-setoid
    open Pattern-Assoc
    open Lemmas0 n

    x'  = x *' -'₁
    mc' = x' , ε
    claim : ⟦ x , HS^ ₀ ⟧ₘ₊ • [ H-gen ]ʷ ≈ ε • ⟦ mc' ⟧ₘ₊
    claim = begin
      ⟦ x , HS^ ₀ ⟧ₘ₊ • [ H-gen ]ʷ ≈⟨ assoc ⟩
      M x • (H • ε) • H ≈⟨ (cright cong right-unit refl) ⟩
      M x • HH ≈⟨ (cright lemma-HH-M-1) ⟩
      M x • M -'₁ ≈⟨ ( axiom (M-mul x -'₁)) ⟩
      M (x *' -'₁) ≈⟨ sym ( right-unit) ⟩
      M (x *' -'₁) • ε ≈⟨ sym left-unit ⟩
      ε • ⟦ mc' ⟧ₘ₊ ∎


  Lemma-single-qupit-completeness-mc-H {n} mc@((y , nzy) , HS^ x@(₁₊ k')) = (-x⁻¹ * (y * y)) , mc' , claim
    where
    open PB ((₁₊ n) QRel,_===_)
    open PP ((₁₊ n) QRel,_===_)
    open SR word-setoid
    open Pattern-Assoc
    open Lemmas0 n

    x' : ℤ* ₚ
    x' = (x , λ ())
    nz = x' .proj₂
    x⁻¹ = ((x , nz) ⁻¹) .proj₁
    x⁻¹⁻¹ = (((x , nz) ⁻¹) ⁻¹) .proj₁
    -x⁻¹ = - x⁻¹
    -y/x' = (((y , nzy) *' ((x , nz) ⁻¹)) *' -'₁)
    -y/x = -y/x' .proj₁

    mc' = (-y/x' , (HS^ -x⁻¹))
    claim : ⟦ (y , nzy) , HS^ (₁₊ k') ⟧ₘ₊ • [ H-gen ]ʷ ≈ (S^ (-x⁻¹ * (y * y))) • ⟦ mc' ⟧ₘ₊
    claim = begin
      ⟦ (y , nzy) , HS^ (₁₊ k') ⟧ₘ₊ • [ H-gen ]ʷ ≈⟨ trans assoc (cong refl refl) ⟩
      M (y , nzy) • (H • S^ (₁₊ k')) • H ≈⟨ (cright assoc) ⟩
      M (y , nzy) • H • S^ (₁₊ k') • H ≈⟨ (derived-7 x y nz nzy) ⟩
      S^ (-x⁻¹ * (y * y)) • M -y/x' • (H • S^ -x⁻¹) ≈⟨ sym refl ⟩
      (S^ (-x⁻¹ * (y * y))) • M -y/x' • (H • S^ -x⁻¹) ∎





  open import Data.Fin.Properties
  open import Data.Nat.DivMod

  Lemma-single-qupit-completeness-mc-S : let open PB ((₁₊ n) QRel,_===_) in
    
    ∀ (mc : MC) ->
    -----------------------------------------------
    ∃ \ k -> ∃ \ mc' -> ⟦ mc ⟧ₘ₊ • S ≈ S^ k • ⟦ mc' ⟧ₘ₊
    
  Lemma-single-qupit-completeness-mc-S {n} mc@(m , ε) = (m ^2) , mc ,  claim
    where
    open PB ((₁₊ n) QRel,_===_)
    open PP ((₁₊ n) QRel,_===_)
    open SR word-setoid
    open Pattern-Assoc
    claim : (⟦ m ⟧ₘ • ε) • [ S-gen ]ʷ ≈ S^ (m ^2) • ⟦ m ⟧ₘ • ε
    claim = begin
      (⟦ m ⟧ₘ • ε) • [ S-gen ]ʷ ≈⟨ cong right-unit refl ⟩
      ⟦ m ⟧ₘ • S ≈⟨ axiom (semi-MS m) ⟩
      S^ (m ^2) • ⟦ m ⟧ₘ ≈⟨ sym (cong refl right-unit) ⟩
      S^ (m ^2) • ⟦ m ⟧ₘ • ε ∎


  Lemma-single-qupit-completeness-mc-S {n} mc@(x , HS^ k) = ₀ , mc' , claim
    where
    open PB ((₁₊ n) QRel,_===_)
    open PP ((₁₊ n) QRel,_===_)
    open SR word-setoid
    open Pattern-Assoc
    open Lemmas0 n
    
    aux-S^ : ∀ a b -> S^ a • S^ b ≈ S^ (a + b)
    aux-S^ a b = begin
      S^ a • S^ b ≈⟨ sym (lemma-^-+ S (toℕ a) (toℕ b)) ⟩
      S ^ (toℕ a Nat.+ toℕ b) ≈⟨ lemma-S^k-% (toℕ a Nat.+ toℕ b) ⟩
      S ^ ((toℕ a Nat.+ toℕ b) Nat.% p) ≡⟨ Eq.cong (S ^_) (Eq.sym (toℕ-fromℕ< (m%n<n (toℕ a Nat.+ toℕ b) p))) ⟩
      S ^ toℕ (a + b) ≈⟨ refl ⟩
      S^ (a + b) ∎

    mc' = x , HS^ (1ₚ + k)
    claim : ⟦ x , HS^ k ⟧ₘ₊ • S ≈ ε • ⟦ mc' ⟧ₘ₊
    claim = begin
      ⟦ x , HS^ k ⟧ₘ₊ • S ≈⟨ trans assoc (cong refl assoc) ⟩
      ⟦ x ⟧ₘ • H • S^ k • S ≈⟨ (cright cright word-comm (toℕ k) 1 refl) ⟩
      ⟦ x ⟧ₘ • H • S • S^ k ≈⟨ (cright cright aux-S^ 1ₚ k) ⟩
      ⟦ x ⟧ₘ • H • S^ (1ₚ + k) ≈⟨ sym left-unit ⟩
      ε • ⟦ mc' ⟧ₘ₊ ∎



  Lemma-single-qupit-completeness-mc-S-ε : let open PB ((₁₊ n) QRel,_===_) in
    
    ∀ m -> let mc = (m , ε) in
    -----------------------------------------------
    let k = (m *' m) .proj₁ in  ⟦ mc ⟧ₘ₊ • S ≈ S^ k • ⟦ mc ⟧ₘ₊
    
  Lemma-single-qupit-completeness-mc-S-ε {n} m = claim
    where
    open PB ((₁₊ n) QRel,_===_)
    open PP ((₁₊ n) QRel,_===_)
    open SR word-setoid
    open Pattern-Assoc
    claim : (⟦ m ⟧ₘ • ε) • [ S-gen ]ʷ ≈ S^ (m ^2) • ⟦ m ⟧ₘ • ε
    claim = begin
      (⟦ m ⟧ₘ • ε) • [ S-gen ]ʷ ≈⟨ cong right-unit refl ⟩
      ⟦ m ⟧ₘ • S ≈⟨ axiom (semi-MS m) ⟩
      S^ (m ^2) • ⟦ m ⟧ₘ ≈⟨ sym (cong refl right-unit) ⟩
      S^ (m ^2) • ⟦ m ⟧ₘ • ε ∎


  Lemma-single-qupit-completeness-mc-S-HS : let open PB ((₁₊ n) QRel,_===_) in
    
    ∀ m k -> let mc = (m , HS^ k) in let mc' = m , HS^ (1ₚ + k) in
    ---------------------------------------------------------------
    ⟦ mc ⟧ₘ₊ • S ≈ ⟦ mc' ⟧ₘ₊
    
  Lemma-single-qupit-completeness-mc-S-HS {n} x k = claim
    where
    open PB ((₁₊ n) QRel,_===_)
    open PP ((₁₊ n) QRel,_===_)
    open SR word-setoid
    open Pattern-Assoc
    open Lemmas0 n
    
    aux-S^ : ∀ a b -> S^ a • S^ b ≈ S^ (a + b)
    aux-S^ a b = begin
      S^ a • S^ b ≈⟨ sym (lemma-^-+ S (toℕ a) (toℕ b)) ⟩
      S ^ (toℕ a Nat.+ toℕ b) ≈⟨ lemma-S^k-% (toℕ a Nat.+ toℕ b) ⟩
      S ^ ((toℕ a Nat.+ toℕ b) Nat.% p) ≡⟨ Eq.cong (S ^_) (Eq.sym (toℕ-fromℕ< (m%n<n (toℕ a Nat.+ toℕ b) p))) ⟩
      S ^ toℕ (a + b) ≈⟨ refl ⟩
      S^ (a + b) ∎

    mc' = x , HS^ (1ₚ + k)
    claim : ⟦ x , HS^ k ⟧ₘ₊ • S ≈ ⟦ mc' ⟧ₘ₊
    claim = begin
      ⟦ x , HS^ k ⟧ₘ₊ • S ≈⟨ trans assoc (cong refl assoc) ⟩
      ⟦ x ⟧ₘ • H • S^ k • S ≈⟨ (cright cright word-comm (toℕ k) 1 refl) ⟩
      ⟦ x ⟧ₘ • H • S • S^ k ≈⟨ (cright cright aux-S^ 1ₚ k) ⟩
      ⟦ x ⟧ₘ • H • S^ (1ₚ + k) ≈⟨ refl ⟩
      ⟦ mc' ⟧ₘ₊ ∎


  Lemma-single-qupit-completeness-mc-H-ε : let open PB ((₁₊ n) QRel,_===_) in
    
    ∀ m -> let mc = (m , ε) in
    -----------------------------------------------
    let mc' = (m , HS^ ₀) in ⟦ mc ⟧ₘ₊ • H ≈ ⟦ mc' ⟧ₘ₊
    
  Lemma-single-qupit-completeness-mc-H-ε {n} m = claim
    where
    open PB ((₁₊ n) QRel,_===_)
    open PP ((₁₊ n) QRel,_===_)
    open SR word-setoid
    open Pattern-Assoc
    claim : (⟦ m ⟧ₘ • ε) • [ H-gen ]ʷ ≈ ⟦ m ⟧ₘ • H • S^ ₀
    claim = trans (cong right-unit (sym right-unit)) refl

  Lemma-single-qupit-completeness-mc-H-HS⁰ : let open PB ((₁₊ n) QRel,_===_) in
    
    ∀ m -> let mc = (m , HS^ ₀) in
    -------------------------------------------------
    let mc' = (m *' -'₁ , ε) in ⟦ mc ⟧ₘ₊ • H ≈ ⟦ mc' ⟧ₘ₊

  Lemma-single-qupit-completeness-mc-H-HS⁰ {n} x = claim
    where
    open PB ((₁₊ n) QRel,_===_)
    open PP ((₁₊ n) QRel,_===_)
    open SR word-setoid
    open Pattern-Assoc
    open Lemmas0 n

    x'  = x *' -'₁
    mc' = x' , ε
    claim : ⟦ x , HS^ ₀ ⟧ₘ₊ • [ H-gen ]ʷ ≈ ⟦ mc' ⟧ₘ₊
    claim = begin
      ⟦ x , HS^ ₀ ⟧ₘ₊ • [ H-gen ]ʷ ≈⟨ assoc ⟩
      M x • (H • ε) • H ≈⟨ (cright cong right-unit refl) ⟩
      M x • HH ≈⟨ (cright lemma-HH-M-1) ⟩
      M x • M -'₁ ≈⟨ ( axiom (M-mul x -'₁)) ⟩
      M (x *' -'₁) ≈⟨ sym ( right-unit) ⟩
      M (x *' -'₁) • ε ≈⟨ refl ⟩
      ⟦ mc' ⟧ₘ₊ ∎

-- (-' (x' ⁻¹) *' (m *' m))

  Lemma-single-qupit-completeness-mc-H-HS : let open PB ((₁₊ n) QRel,_===_) in
    
    ∀ m (kk* : ℤ* ₚ) -> let mc = (m , HS^ (kk* .proj₁)) in
    ----------------------------------------------------------------------------------
    let k* = (-' (kk* ⁻¹) *' (m *' m)) in
    let k = k* .proj₁ in
    let -m/kk* = ((m *' kk* ⁻¹) *' -'₁) in
    let -1/kk = - (kk* ⁻¹) .proj₁ in
    let mc' = (-m/kk* , HS^ -1/kk) in
    ⟦ mc ⟧ₘ₊ • H ≈ S^ k • ⟦ mc' ⟧ₘ₊

  Lemma-single-qupit-completeness-mc-H-HS {n} m@(y , nzy) x' = claim
    where
    open PB ((₁₊ n) QRel,_===_)
    open PP ((₁₊ n) QRel,_===_)
    open SR word-setoid
    open Pattern-Assoc
    open Lemmas0 n
    x = x' .proj₁

    nz = x' .proj₂
    x⁻¹ = ((x , nz) ⁻¹) .proj₁
    x⁻¹⁻¹ = (((x , nz) ⁻¹) ⁻¹) .proj₁
    -x⁻¹ = - x⁻¹
    -y/x' = (((y , nzy) *' ((x , nz) ⁻¹)) *' -'₁)
    -y/x = -y/x' .proj₁

    mc' = (-y/x' , (HS^ -x⁻¹))
    claim : ⟦ (y , nzy) , HS^ x ⟧ₘ₊ • [ H-gen ]ʷ ≈ (S^ (-x⁻¹ * (y * y))) • ⟦ mc' ⟧ₘ₊
    claim = begin
      ⟦ (y , nzy) , HS^ x ⟧ₘ₊ • [ H-gen ]ʷ ≈⟨ trans assoc (cong refl refl) ⟩
      M (y , nzy) • (H • S^ x) • H ≈⟨ (cright assoc) ⟩
      M (y , nzy) • H • S^ x • H ≈⟨ (derived-7 x y nz nzy) ⟩
      S^ (-x⁻¹ * (y * y)) • M -y/x' • (H • S^ -x⁻¹) ≈⟨ sym refl ⟩
      (S^ (-x⁻¹ * (y * y))) • M -y/x' • (H • S^ -x⁻¹) ∎



  top-S^k : ∀ k -> TopwWord {n} (S ^ k)
  top-S^k ₀ = tt
  top-S^k ₁ = tt
  top-S^k (₂₊ k) = tt , (top-S^k (₁₊ k))

  top-M : ∀ m -> TopwWord {n} (M m)
  top-M m@x' = top-S^k (toℕ x) , tt , top-S^k (toℕ x⁻¹) , tt , top-S^k (toℕ x) , tt
    where
    x = x' .proj₁
    x⁻¹ = ((x' ⁻¹) .proj₁ )

