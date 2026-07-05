{-# OPTIONS --termination-depth=4 #-}
open import Level using (0ℓ)

open import Relation.Binary using (Rel)
open import Relation.Binary.PropositionalEquality using (_≡_ ; _≢_) renaming ([_] to [_]')
import Relation.Binary.Reasoning.Setoid as SR
import Relation.Binary.PropositionalEquality as Eq

open import Function using (_∘_ ; id)

open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂ ; ∃)
open import Data.Nat hiding (_^_ ; _*_ ; _+_)
import Data.Nat as Nat
open import Data.Fin hiding (_+_ ; _≤_)
open import Data.Sum using (_⊎_ ; inj₁ ; inj₂ ; [_,_])

open import Word.Base as WB hiding (wfoldl)
open import Word.Properties
import Presentation.Base as PB
import Presentation.Properties as PP

open import Presentation.Construct.Base hiding (_*_)
open import Presentation.GroupLike

open import Data.Fin.Properties using (suc-injective ; toℕ-inject₁ ; toℕ-fromℕ ; toℕ-fromℕ<)
open import Data.Nat.DivMod using (_%_ ; _/_ ; m≡m%n+[m/n]*n ; m%n<n)
import Data.Nat.Properties as NP
import N.Symplectic as NS
open import Data.Nat.Primality

open import Zp.ModularArithmetic
open import Zp.Fermats-little-theorem

open import Algebra.Bundles using (Group)
open import Algebra.Morphism.Structures using (module GroupMorphisms)
open import Notations


module N.Clifford.Iso3
  (p-3 : ℕ)
  (let p-2 = ₁₊ p-3)
  (p-prime : Prime (suc (₁₊ p-2)))
  (let open PrimeModulus' p-2 p-prime)
  (g*@(g , g≠0) : ℤ* ₚ)
  (g-gen : ∀ ((x , _) : ℤ* ₚ) -> ∃ \ (k : ℤ ₚ-₁) -> x ≡ g ^′ toℕ k )
  where


open import N.Clifford.SDProduct p-3 p-prime g* g-gen
open import N.Clifford.Clifford-Mod-Scalar p-3 p-prime g* g-gen as Cli
import N.Clifford.Iso p-3 p-prime g* g-gen as ISO
import N.Clifford.Iso2 p-3 p-prime g* g-gen as ISO2

pattern ₀ = zero
pattern ₁ = ₁₊ ₀
pattern ₂ = ₁₊ ₁

import N.Symplectic p-2 p-prime as NSym
import N.XZ p-2 p-prime as XZ


module M (n : ℕ) where
  open ISO.Iso n using (f ; h ; f-well-defined ; lemma-f*-SD↑)
  open ISO2.Iso-Inverse-Direction n using (h-well-defined ; h-X ; h-Z ; hs ; lemma-h↑)

  -- f ∘ h ≈ id on Clifford generators
  f-left-inv-gen : ∀ {m} (x : Cli.Gen m) →
    let open PB (Cli.Clifford-Relations._QRel,_===_ m) using (_≈_) in
    [ x ]ʷ ≈ (f *) (h x)
  f-left-inv-gen Cli.H-gen = PB.refl
  f-left-inv-gen Cli.CZ-gen = PB.refl
  f-left-inv-gen (x Cli.↥) =
    PB.trans (Cli.Lemmas-Clifford.lemma-cong↑ _ _ (f-left-inv-gen x))
             (PB.refl' (Cli.Clifford-Relations._QRel,_===_ _) (Eq.sym (lemma-f*-SD↑ (h x))))
  f-left-inv-gen {₁₊ m} Cli.S-gen = begin
      [ Cli.S-gen ]ʷ
        ≈⟨ sym claim ⟩
      C.Z^ Cli.-1/2 • C.𝑠
        ≡⟨ Eq.cong (λ z → z • C.𝑠) (Eq.sym (lemma-f*-w^n {f = f} {w = SemiDirect.Z} (toℕ Cli.-1/2))) ⟩
      (f *) (h Cli.S-gen) ∎
    where
    module C = Cli.Clifford-Relations
    open PB (C._QRel,_===_ (₁₊ m))
    open PP (C._QRel,_===_ (₁₊ m))
    open SR word-setoid
    open Cli.Lemmas1 m using (lemma-order-Z ; lemma-comm-Z-S)
    toℕ-+ : ∀ (a b : ℤ ₚ) → (toℕ a Nat.+ toℕ b) % p ≡ toℕ (a + b)
    toℕ-+ a b = Eq.sym (toℕ-fromℕ< (m%n<n (toℕ a Nat.+ toℕ b) p))
    arith0 : (toℕ Cli.-1/2 Nat.+ toℕ Cli.1/2) % p ≡ 0
    arith0 = Eq.trans (toℕ-+ Cli.-1/2 Cli.1/2) (Eq.cong toℕ (+-inverseˡ Cli.1/2))
    Zmod : ∀ a → C.Z ^ a ≈ C.Z ^ (a % p)
    Zmod a = begin
      C.Z ^ a                                          ≡⟨ Eq.cong (C.Z ^_) (m≡m%n+[m/n]*n a p) ⟩
      C.Z ^ (a % p Nat.+ a / p Nat.* p)                ≈⟨ lemma-^-+ C.Z (a % p) (a / p Nat.* p) ⟩
      C.Z ^ (a % p) • C.Z ^ (a / p Nat.* p)            ≈⟨ cright (refl' (Eq.cong (C.Z ^_) (NP.*-comm (a / p) p))) ⟩
      C.Z ^ (a % p) • C.Z ^ (p Nat.* (a / p))          ≈⟨ cright (sym (lemma-^^ C.Z p (a / p))) ⟩
      C.Z ^ (a % p) • (C.Z ^ p) ^ (a / p)              ≈⟨ cright (lemma-^-cong (C.Z ^ p) ε (a / p) lemma-order-Z) ⟩
      C.Z ^ (a % p) • ε ^ (a / p)                      ≈⟨ cright (lemma-ε^k=ε (a / p)) ⟩
      C.Z ^ (a % p) • ε                                ≈⟨ right-unit ⟩
      C.Z ^ (a % p) ∎
    zhalf : C.Z^ Cli.-1/2 • C.Z^ Cli.1/2 ≈ ε
    zhalf = begin
      C.Z^ Cli.-1/2 • C.Z^ Cli.1/2                          ≈⟨ sym (lemma-^-+ C.Z (toℕ Cli.-1/2) (toℕ Cli.1/2)) ⟩
      C.Z ^ (toℕ Cli.-1/2 Nat.+ toℕ Cli.1/2)               ≈⟨ Zmod (toℕ Cli.-1/2 Nat.+ toℕ Cli.1/2) ⟩
      C.Z ^ ((toℕ Cli.-1/2 Nat.+ toℕ Cli.1/2) % p)         ≡⟨ Eq.cong (C.Z ^_) arith0 ⟩
      ε ∎
    commSZ : Cli.S • C.Z^ Cli.1/2 ≈ C.Z^ Cli.1/2 • Cli.S
    commSZ = word-comm 1 (toℕ Cli.1/2) (sym lemma-comm-Z-S)
    claim : C.Z^ Cli.-1/2 • C.𝑠 ≈ Cli.S
    claim = begin
      C.Z^ Cli.-1/2 • C.𝑠                                ≈⟨ cright commSZ ⟩
      C.Z^ Cli.-1/2 • (C.Z^ Cli.1/2 • Cli.S)                 ≈⟨ sym assoc ⟩
      (C.Z^ Cli.-1/2 • C.Z^ Cli.1/2) • Cli.S                 ≈⟨ cleft zhalf ⟩
      ε • Cli.S                                          ≈⟨ left-unit ⟩
      Cli.S ∎

  -- h ∘ f ≈ id on SemiDirect generators
  g-left-inv-gen : ∀ {m} (x : SemiDirect.Gen m) →
    let open PB (SemiDirect._QRel,_===_ m) using (_≈_) in
    [ x ]ʷ ≈ (h *) (f x)
  g-left-inv-gen SemiDirect.X-gen = PB.sym h-X
  g-left-inv-gen SemiDirect.Z-gen = PB.sym h-Z
  g-left-inv-gen SemiDirect.H-gen = PB.refl
  g-left-inv-gen SemiDirect.S-gen = PB.sym hs
  g-left-inv-gen SemiDirect.CZ-gen = PB.refl
  g-left-inv-gen (inj₁ (x XZ.↥)) =
    PB.trans (SemiDirect.lemma-cong↑ _ _ (g-left-inv-gen (inj₁ x)))
             (PB.refl' (SemiDirect._QRel,_===_ _) (Eq.sym (lemma-h↑ (f (inj₁ x)))))
  g-left-inv-gen (inj₂ (y NS.Symplectic.↥)) =
    PB.trans (SemiDirect.lemma-cong↑ _ _ (g-left-inv-gen (inj₂ y)))
             (PB.refl' (SemiDirect._QRel,_===_ _) (Eq.sym (lemma-h↑ (f (inj₂ y)))))

  module G1 = Group-Lemmas (SemiDirect.Gen n) (SemiDirect._QRel,_===_ n) (Semi-GroupLike.grouplike {n})
  module G2 = Group-Lemmas (Cli.Gen n) (Cli.Clifford-Relations._QRel,_===_ n) (Cli.Clifford-GroupLike.grouplike {n})

  open GroupMorphisms

  open import Presentation.Morphism (SemiDirect._QRel,_===_ n) (Cli.Clifford-Relations._QRel,_===_ n)
  open GroupMorphs (Semi-GroupLike.grouplike {n}) (Cli.Clifford-GroupLike.grouplike {n})

  Theorem-SemiDirect-iso-Clifford :
    IsGroupIsomorphism (Group.rawGroup G1.•-ε-group) (Group.rawGroup G2.•-ε-group) (f *)
  Theorem-SemiDirect-iso-Clifford =
    StarGroupIsomorphism.isGroupIsomorphism f h f-well-defined f-left-inv-gen h-well-defined g-left-inv-gen
