{-# OPTIONS --allow-unsolved-metas #-}
-- {-# OPTIONS  --safe #-}
{-# OPTIONS --termination-depth=4 #-}
open import Level using (0ℓ)

open import Relation.Binary using (Rel)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Binary.Morphism.Definitions using (Homomorphic₂)
open import Relation.Binary.PropositionalEquality using (_≡_ ; _≢_ ; inspect ; setoid ; module ≡-Reasoning) renaming ([_] to [_]')
import Relation.Binary.Reasoning.Setoid as SR
import Relation.Binary.PropositionalEquality as Eq
open import Relation.Nullary.Decidable using (yes ; no)


open import Function using (_∘_ ; id)
open import Function.Definitions using (Injective)

open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂ ; map₁ ; ∃ ; Σ ; Σ-syntax)

open import Data.Product.Relation.Binary.Pointwise.NonDependent as PW using (≡×≡⇒≡ ; Pointwise ; ≡⇒≡×≡)
open import Data.Nat hiding (_^_ ; _*_ ; _+_)
open import Agda.Builtin.Nat using (_-_)
import Data.Nat as Nat
open import Data.Fin hiding (_+_ ; _≤_)
open import Data.Bool hiding (_≤_)
open import Data.List hiding ([_])

open import Data.Maybe
open import Data.Sum using (_⊎_ ; inj₁ ; inj₂ ; [_,_])
open import Data.Unit using (⊤ ; tt)
open import Data.Empty using (⊥ ; ⊥-elim)

open import Word.Base as WB hiding (wfoldl)
open import Word.Properties
import Presentation.Base as PB
import Presentation.Properties as PP
open PP using (NFProperty ; NFProperty')
import Presentation.CosetNF as CA
import Presentation.Reidemeister-Schreier as RS
module RSF = RS.Star-Injective-Full.Reidemeister-Schreier-Full

open import Presentation.Construct.Base hiding (_*_)
import Presentation.Construct.Properties.SemiDirectProduct2 as SDP2
import Presentation.Construct.Properties.DirectProduct as DP
import Presentation.Groups.Cyclic as Cyclic
open import Presentation.Tactics hiding ([_])

open import Data.Fin.Properties using (suc-injective ; toℕ-inject₁ ; toℕ-fromℕ)
import Data.Nat.Properties as NP
open import Presentation.GroupLike
import N.Symplectic as NS
open import Data.Nat.Primality

open import Zp.ModularArithmetic
open import Zp.Fermats-little-theorem


module N.Clifford.Iso2
  (p-3 : ℕ)
  (let p-2 = suc p-3)
  (p-prime : Prime (suc (suc p-2)))
  (let open PrimeModulus' p-2 p-prime)
  (g*@(g , g≠0) : ℤ* ₚ)
  (g-gen : ∀ ((x , _) : ℤ* ₚ) -> ∃ \ (k : ℤ ₚ-₁) -> x ≡ g ^′ toℕ k )
  where


open import N.Clifford.SDProduct p-3 p-prime g* g-gen
open import N.Clifford.Iso p-3 p-prime g* g-gen
open import N.Clifford.Clifford-Lemmas p-3 p-prime g* g-gen hiding (module CL ; module CLb)

pattern ₀ = zero
pattern ₁ = suc ₀
pattern ₂ = suc ₁

pattern ₁₊ ⱼ = suc ⱼ
pattern ₂₊ ⱼ = suc (suc ⱼ)
pattern ₃₊ ⱼ = suc (suc (suc ⱼ))

import N.Symplectic p-2 p-prime as NSym
import N.Symplectic-Simplified p-2 p-prime g* g-gen as NSim
--module Sym = NSym.Symplectic
--module Sim = NSim.Simplified-Relations
import N.XZ p-2 p-prime as XZ


module Iso-Inverse-Direction (n : ℕ) where

  open import N.Clifford.Clifford-Mod-Scalar p-3 p-prime g* g-gen as Cli

--  module Clifford = Clifford-Relations
--  open Clifford-Lemmas

--  open import Presentation.Morphism SemiDirect._===_ Clifford-Relations._===_
--  open GroupMorphs SemiDirect.grouplike Clifford-GroupLike.grouplike


  open import Presentation.Construct.Properties
  open Clifford-Relations
  open Iso n


  h-well-defined : ∀ {n w v} ->
    let
      open PB (n SemiDirect.QRel,_===_) renaming (_===_ to _===₁_ ; _≈_ to _≈₁_) using ()
      open PB (n Clifford.QRel,_===_) renaming (_===_ to _===₂_ ; _≈_ to _≈₂_ ; cleft_ to cleft₂_ ; cright_ to cright₂_) using ()
    in
    w ===₂ v -> (h *) w ≈₁ (h *) v

  h-well-defined {n} {w} {v} order-S = {!!}
  h-well-defined {n} {w} {v} order-H = {!!}
  h-well-defined {n} {w} {v} (M-power k) = {!!}
  h-well-defined {n} {w} {v} semi-M𝑠 = {!!}
  h-well-defined {n} {w} {v} order-SH = {!!}
  h-well-defined {n} {w} {v} comm-HHSHHS = {!!}
  h-well-defined {n} {w} {v} comm-X-Z = {!!}
  h-well-defined {n} {w} {v} semi-M↑CZ = {!!}
  h-well-defined {n} {w} {v} semi-M↓CZ = {!!}
  h-well-defined {n} {w} {v} rel-X↑-CZ = {!!}
  h-well-defined {n} {w} {v} rel-X↓-CZ = {!!}
  h-well-defined {n} {w} {v} order-CZ = {!!}
  h-well-defined {n} {w} {v} comm-CZ-S↓ = {!!}
  h-well-defined {n} {w} {v} comm-CZ-S↑ = {!!}
  h-well-defined {n} {w} {v} selinger-c10 = {!!}
  h-well-defined {n} {w} {v} selinger-c11 = {!!}
  h-well-defined {n} {w} {v} selinger-c12 = {!!}
  h-well-defined {n} {w} {v} selinger-c13 = {!!}
  h-well-defined {n} {w} {v} selinger-c14 = {!!}
  h-well-defined {n} {w} {v} selinger-c15 = {!!}
  h-well-defined {n} {w} {v} comm-H = {!!}
  h-well-defined {n} {w} {v} comm-S = {!!}
  h-well-defined {n} {w} {v} comm-CZ = {!!}
  h-well-defined {n} {w} {v} (cong↑ eq) = {!!}



{-  

{-
  open PB Sim._===_ renaming (_===_ to _===₂_ ; _≈_ to _≈₂_) using ()
  open PP Sim._===_ renaming (•-ε-monoid to m₂ ; word-setoid to ws₂) using ()
  
  open PB XZ._===_ renaming (_===_ to _===₁_ ; _≈_ to _≈₁_) using ()
  open PP XZ._===_ renaming (•-ε-monoid to m₁ ; word-setoid to ws₁ ; by-assoc-and to by-assoc-and₁ ; by-assoc to by-assoc₁) using ()
-}

  open PB hiding (_===_)


  hyph :
    let
    open PB (Sim._QRel,_===_ n) renaming (_===_ to _===₂_ ; _≈_ to _≈₂_) using ()
    open PB (XZ._QRel,_===_ n) renaming (_===_ to _===₁_ ; _≈_ to _≈₁_) using ()
    in
    
    ∀ {c d} n -> c ===₂ d -> (conj ʰ') c n ≈₁ (conj ʰ') d n

  hyph {c} {d} [ XZ.X-gen ]ʷ Sim.order-S = {!!}
  hyph {c} {d} [ XZ.Z-gen ]ʷ Sim.order-S = {!!}
  hyph {c} {d} [ (x XZ.↥) ]ʷ Sim.order-S = {!!}
  hyph {c} {d} [ x ]ʷ Sim.order-H = {!!}
  hyph {c} {d} [ x ]ʷ (Sim.M-power k) = {!!}
  hyph {c} {d} [ x ]ʷ Sim.semi-MS = {!!}
  hyph {c} {d} [ x ]ʷ Sim.semi-M↑CZ = {!!}
  hyph {c} {d} [ x ]ʷ Sim.semi-M↓CZ = {!!}
  hyph {c} {d} [ x ]ʷ Sim.order-CZ = {!!}
  hyph {c} {d} [ x ]ʷ Sim.comm-CZ-S↓ = {!!}
  hyph {c} {d} [ x ]ʷ Sim.comm-CZ-S↑ = {!!}
  hyph {c} {d} [ x ]ʷ Sim.selinger-c10 = {!!}
  hyph {c} {d} [ x ]ʷ Sim.selinger-c11 = {!!}
  hyph {c} {d} [ x ]ʷ Sim.selinger-c12 = {!!}
  hyph {c} {d} [ x ]ʷ Sim.selinger-c13 = {!!}
  hyph {c} {d} [ x ]ʷ Sim.selinger-c14 = {!!}
  hyph {c} {d} [ x ]ʷ Sim.selinger-c15 = {!!}
  hyph {c} {d} [ x ]ʷ Sim.comm-H = {!!}
  hyph {c} {d} [ x ]ʷ Sim.comm-S = {!!}
  hyph {c} {d} [ x ]ʷ Sim.comm-CZ = {!!}
  hyph {c} {d} [ x ]ʷ (Sim.cong↑ ax) = {!!}
  hyph {c} {d} ε ax = {!!}
  hyph {c} {d} (n • n₁) ax = {!!}


  hypn :
    let
    open PB (Sim._QRel,_===_ n) renaming (_===_ to _===₂_ ; _≈_ to _≈₂_) using ()
    open PB (XZ._QRel,_===_ n) renaming (_===_ to _===₁_ ; _≈_ to _≈₁_) using ()
    in
  
    ∀ c {w v} -> w ===₁ v -> (conj ⁿ') c w ≈₁ (conj ⁿ') c v
  hypn Sym.H-gen XZ.order-X = {!!}
  hypn Sym.H-gen XZ.order-Z = {!!}
  hypn Sym.H-gen XZ.comm-Z-X = {!!}
  hypn Sym.H-gen XZ.comm-X = {!!}
  hypn Sym.H-gen XZ.comm-Z = {!!}
  hypn Sym.H-gen (XZ.cong↑ ax) = {!!}
  hypn Sym.S-gen XZ.order-X = {!!}
  hypn Sym.S-gen XZ.order-Z = {!!}
  hypn Sym.S-gen XZ.comm-Z-X = {!!}
  hypn Sym.S-gen XZ.comm-X = {!!}
  hypn Sym.S-gen XZ.comm-Z = {!!}
  hypn Sym.S-gen (XZ.cong↑ ax) = {!!}
  hypn Sym.CZ-gen XZ.order-X = {!!}
  hypn Sym.CZ-gen XZ.order-Z = {!!}
  hypn Sym.CZ-gen XZ.comm-Z-X = {!!}
  hypn Sym.CZ-gen XZ.comm-X = {!!}
  hypn Sym.CZ-gen XZ.comm-Z = {!!}
  hypn Sym.CZ-gen (XZ.cong↑ ax) = {!!}
  hypn (c Sym.↥) XZ.order-X = {!!}
  hypn (c Sym.↥) XZ.order-Z = {!!}
  hypn (c Sym.↥) XZ.comm-Z-X = {!!}
  hypn (c Sym.↥) XZ.comm-X = {!!}
  hypn (c Sym.↥) XZ.comm-Z = {!!}
  hypn (c Sym.↥) (XZ.cong↑ ax) = {!!}


  nfp' : (n : ℕ) -> NFProperty' (n QRel,_===_)
  nfp' n = SDP2.NFP'.nfp' (XZ._QRel,_===_  n) (Sim._QRel,_===_ n) (conj {n}) (hyph {n}) (hypn {n}) {!!} {!!}


-}



{-
  f-well-defined SemiDirect.order-X₀ = by-sub-nf₀ OL.lemma-order-X
  f-well-defined SemiDirect.order-Z₀ = by-sub-nf₀ OL.lemma-order-Z
  f-well-defined SemiDirect.comm-Z₀-X₀ = by-sub-nf₀ OL.lemma-conj-X-Z

  f-well-defined SemiDirect.order-X₁ = by-sub-nf₁ OL.lemma-order-X
  f-well-defined SemiDirect.order-Z₁ = by-sub-nf₁ OL.lemma-order-Z
  f-well-defined SemiDirect.comm-Z₁-X₁ = by-sub-nf₁ OL.lemma-conj-X-Z

  f-well-defined SemiDirect.order-H₀ = by-sub-nf₀ (axiom O.order-H)
  f-well-defined SemiDirect.order-S₀ =  ( by-sub-nf₀ lemma-order-𝑠)
  f-well-defined SemiDirect.order-S₀H₀ = by-sub-nf₀ lemma-order-𝑠H
  f-well-defined SemiDirect.comm-H₀H₀S₀ = by-sub-nf₀ lemma-comm-HH𝑠

  f-well-defined SemiDirect.order-H₁ = by-sub-nf₁ (axiom O.order-H)
  f-well-defined SemiDirect.order-S₁ =  ( by-sub-nf₁ lemma-order-𝑠)
  f-well-defined SemiDirect.order-S₁H₁ = by-sub-nf₁ lemma-order-𝑠H
  f-well-defined SemiDirect.comm-H₁H₁S₁ = by-sub-nf₁ lemma-comm-HH𝑠

  f-well-defined SemiDirect.comm-H₁H₀ = general-comm auto
  f-well-defined SemiDirect.comm-H₁S₀ = general-comm auto
  f-well-defined SemiDirect.comm-S₁H₀ = general-comm auto
  f-well-defined SemiDirect.comm-S₁S₀ = general-comm auto

  f-well-defined SemiDirect.order-CZ = _≈₂_.axiom order-CZ
  f-well-defined SemiDirect.comm-CZ-S₀ = rewrite-push-HH 100 auto
  f-well-defined SemiDirect.comm-CZ-S₁ = rewrite-push-HH 100 auto
  f-well-defined SemiDirect.comm-CZ-H₀H₀ = rewrite-push-HH 100 auto
  f-well-defined SemiDirect.comm-CZ-H₁H₁ = rewrite-push-HH 100 auto

  f-well-defined SemiDirect.rel-CZ-H₀-CZ = lemma-rel-CZ-H₀-CZ
  f-well-defined SemiDirect.rel-CZ-H₁-CZ = by-duality lemma-rel-CZ-H₀-CZ

  f-well-defined SemiDirect.conj-H₀-X₀ = rewrite-push-HH 100 auto
  f-well-defined SemiDirect.conj-H₀-Z₀ = rewrite-push-HH 100 auto
  f-well-defined SemiDirect.conj-S₀-X₀ = by-sub-nf₀ lemma-conj-𝑠-X
  f-well-defined SemiDirect.conj-S₀-Z₀ = rewrite-push-HH 100 auto

  f-well-defined SemiDirect.conj-H₁-X₁ = rewrite-push-HH 100 auto
  f-well-defined SemiDirect.conj-H₁-Z₁ = rewrite-push-HH 100 auto
  f-well-defined SemiDirect.conj-S₁-X₁ = by-sub-nf₁ lemma-conj-𝑠-X
  f-well-defined SemiDirect.conj-S₁-Z₁ = rewrite-push-HH 100 auto

  f-well-defined SemiDirect.conj-H₁-X₀ = general-comm auto
  f-well-defined SemiDirect.conj-H₁-Z₀ = general-comm auto
  f-well-defined SemiDirect.conj-S₁-X₀ = general-comm auto
  f-well-defined SemiDirect.conj-S₁-Z₀ = general-comm auto

  f-well-defined SemiDirect.conj-H₀-X₁ = general-comm auto
  f-well-defined SemiDirect.conj-H₀-Z₁ = general-comm auto
  f-well-defined SemiDirect.conj-S₀-X₁ = general-comm auto
  f-well-defined SemiDirect.conj-S₀-Z₁ = general-comm auto

  f-well-defined SemiDirect.conj-CZ-X₁ = by-assoc-and₂ (axiom rel-X₁-CZ) auto auto
  f-well-defined SemiDirect.conj-CZ-Z₁ = rewrite-push-HH 100 auto
  f-well-defined SemiDirect.conj-CZ-X₀ = by-assoc-and₂ (axiom rel-X₀-CZ) auto auto
    where open SR ws₂
  f-well-defined SemiDirect.conj-CZ-Z₀ = rewrite-push-HH 100 auto

  f-well-defined SemiDirect.comm-Z₀-X₁ = general-comm auto
  f-well-defined SemiDirect.comm-X₀-X₁ = general-comm auto
  f-well-defined SemiDirect.comm-Z₀-Z₁ = general-comm auto
  f-well-defined SemiDirect.comm-X₀-Z₁ = general-comm auto

  import One.Symplectic-Clifford as OSC


  g-well-defined : ∀ {w v} -> w ===₂ v -> (g *) w ≈₁ (g *) v

  g-well-defined Clifford.order-S₀ = by-equal-nf₁ auto
  g-well-defined Clifford.order-H₀ = by-equal-nf₁ auto
  g-well-defined Clifford.order-S₀H₀ = by-equal-nf₁ auto
  g-well-defined Clifford.comm-H₀H₀S₀H₀H₀S₀ = by-equal-nf₁ auto

  g-well-defined Clifford.order-S₁ = by-equal-nf₁ auto
  g-well-defined Clifford.order-H₁ = by-equal-nf₁ auto
  g-well-defined Clifford.order-S₁H₁ = by-equal-nf₁ auto
  g-well-defined Clifford.comm-H₁H₁S₁H₁H₁S₁ = by-equal-nf₁ auto

  g-well-defined Clifford.comm-H₁H₀ = by-equal-nf₁ auto
  g-well-defined Clifford.comm-H₁S₀ = by-equal-nf₁ auto
  g-well-defined Clifford.comm-S₁H₀ = by-equal-nf₁ auto
  g-well-defined Clifford.comm-S₁S₀ = by-equal-nf₁ auto

  g-well-defined Clifford.order-CZ = by-equal-nf₁ auto
  g-well-defined Clifford.comm-CZ-S₀ = by-equal-nf₁ auto
  g-well-defined Clifford.comm-CZ-S₁ = by-equal-nf₁ auto
  g-well-defined Clifford.comm-CZ-H₀H₀ = by-equal-nf₁ auto
  g-well-defined Clifford.comm-CZ-H₁H₁ = by-equal-nf₁ auto

  g-well-defined Clifford.rel-CZ-H₀-CZ = by-equal-nf₁ auto
  g-well-defined Clifford.rel-CZ-H₁-CZ = by-equal-nf₁ auto
  g-well-defined Clifford.rel-X₀-CZ = by-equal-nf₁ auto
  g-well-defined Clifford.rel-X₁-CZ = by-equal-nf₁ auto

  f-left-inv-gen : ∀ x -> [ x ]ʷ ≈₂ (f *) (g x)
  f-left-inv-gen Clifford.H₀-gen = _≈₂_.refl
  f-left-inv-gen Clifford.S₀-gen = by-sub-nf₀ (OSC.Iso.f-left-inv-gen OC.Clifford.S-gen)
  f-left-inv-gen Clifford.H₁-gen = _≈₂_.refl
  f-left-inv-gen Clifford.S₁-gen = by-sub-nf₁ (OSC.Iso.f-left-inv-gen OC.Clifford.S-gen)
  f-left-inv-gen Clifford.CZ-gen = _≈₂_.refl

  g-left-inv-gen : ∀ x -> [ x ]ʷ ≈₁ (g *) (f x)
  g-left-inv-gen SemiDirect.S₀-gen = by-equal-nf₁ auto
  g-left-inv-gen SemiDirect.H₀-gen = by-equal-nf₁ auto
  g-left-inv-gen SemiDirect.X₀-gen = by-equal-nf₁ auto
  g-left-inv-gen SemiDirect.Z₀-gen = by-equal-nf₁ auto
  g-left-inv-gen SemiDirect.S₁-gen = by-equal-nf₁ auto
  g-left-inv-gen SemiDirect.H₁-gen = by-equal-nf₁ auto
  g-left-inv-gen SemiDirect.X₁-gen = by-equal-nf₁ auto
  g-left-inv-gen SemiDirect.Z₁-gen = by-equal-nf₁ auto
  g-left-inv-gen SemiDirect.CZ-gen = by-equal-nf₁ auto


  open import Algebra.Bundles using (Group)
  open import Algebra.Morphism.Structures using (module GroupMorphisms)

  open import Presentation.Morphism
  open GroupMorphisms
  module G1 = Group-Lemmas SemiDirect.Gen SemiDirect._===_ SemiDirect.grouplike
  module G2 = Group-Lemmas Clifford.Gen Clifford._===_ Clifford-GroupLike.grouplike

  Theorem-SemiDirect-iso-Clifford : IsGroupIsomorphism (Group.rawGroup G1.•-ε-group) (Group.rawGroup G2.•-ε-group) (f *)
  Theorem-SemiDirect-iso-Clifford = StarGroupIsomorphism.isGroupIsomorphism f g f-well-defined  f-left-inv-gen g-well-defined  g-left-inv-gen

  -- This theorem says 2 qutrit Clifford mod scalars is isomorphic to
  -- ℤ₃⁴ ⋊ Sp(2*2,3). The presentations are:
  
  -- Clifford:
    -- order-S₀ : S₀ ^ 3 === ε
    -- order-H₀ : H₀ ^ 4 === ε
    -- order-S₀H₀ : (S₀ • H₀) ^ 3 === ε
    -- comm-H₀H₀S₀H₀H₀S₀ : H₀ • H₀ • S₀ • H₀ • H₀ • S₀ === S₀ • H₀ • H₀ • S₀ • H₀ • H₀

    -- order-S₁ : S₁ ^ 3 === ε
    -- order-H₁ : H₁ ^ 4 === ε
    -- order-S₁H₁ : (S₁ • H₁) ^ 3 === ε
    -- comm-H₁H₁S₁H₁H₁S₁ : H₁ • H₁ • S₁ • H₁ • H₁ • S₁ === S₁ • H₁ • H₁ • S₁ • H₁ • H₁

    -- comm-H₁H₀ : H₁ • H₀ === H₀ • H₁
    -- comm-H₁S₀ : H₁ • S₀ === S₀ • H₁
    -- comm-S₁H₀ : S₁ • H₀ === H₀ • S₁
    -- comm-S₁S₀ : S₁ • S₀ === S₀ • S₁

    -- order-CZ : CZ ^ 3 === ε
    -- comm-CZ-S₀ : CZ • S₀ === S₀ • CZ
    -- comm-CZ-S₁ : CZ • S₁ === S₁ • CZ
    -- comm-CZ-H₀H₀ : CZ • H₀H₀ === H₀H₀ • CZ ^ 2
    -- comm-CZ-H₁H₁ : CZ • H₁H₁ === H₁H₁ • CZ ^ 2

    -- rel-CZ-H₀-CZ : CZ • H₀ • CZ === S₀ ^ 2 • H₀ • S₀ ^ 2 • CZ • H₀ • S₀ ^ 2 • S₁ ^ 2 • X₀ ^ 2 • Z₀ ^ 2
    -- rel-CZ-H₁-CZ : CZ • H₁ • CZ === S₁ ^ 2 • H₁ • S₁ ^ 2 • CZ • H₁ • S₁ ^ 2 • S₀ ^ 2 • X₁ ^ 2 • Z₁ ^ 2

    -- rel-X₀-CZ : CZ • X₀ === X₀ • Z₁ • CZ
    -- rel-X₁-CZ : CZ • X₁ === X₁ • Z₀ • CZ

  -- Semidirct product:
  
  --   ℤ₃⁴:
  --     order-X 
  --     order-Z 
  --     comm-Z-X
      
  --   Sp(2*2,3): 
      -- order-S₀ : S₀ ^ 3 === ε
      -- order-H₀ : H₀ ^ 4 === ε
      -- order-S₀H₀ : (S₀ • H₀) ^ 3 === ε
      -- comm-H₀H₀S₀ : H₀ • H₀ • S₀ === S₀ • H₀ • H₀

      -- order-S₁ : S₁ ^ 3 === ε
      -- order-H₁ : H₁ ^ 4 === ε
      -- order-S₁H₁ : (S₁ • H₁) ^ 3 === ε
      -- comm-H₁H₁S₁ : H₁ • H₁ • S₁ === S₁ • H₁ • H₁

      -- comm-H₁H₀ : H₁ • H₀ === H₀ • H₁
      -- comm-H₁S₀ : H₁ • S₀ === S₀ • H₁
      -- comm-S₁H₀ : S₁ • H₀ === H₀ • S₁
      -- comm-S₁S₀ : S₁ • S₀ === S₀ • S₁

      -- order-CZ : CZ ^ 3 === ε
      -- comm-CZ-S₀ : CZ • S₀ === S₀ • CZ
      -- comm-CZ-S₁ : CZ • S₁ === S₁ • CZ
      -- comm-CZ-H₀H₀ : CZ • H₀H₀ === H₀H₀ • CZ ^ 2
      -- comm-CZ-H₁H₁ : CZ • H₁H₁ === H₁H₁ • CZ ^ 2

      -- rel-CZ-H₀-CZ : CZ • H₀ • CZ === S₀ ^ 2 • H₀ • S₀ ^ 2 • CZ • H₀ • S₀ ^ 2 • S₁ ^ 2
      -- rel-CZ-H₁-CZ : CZ • H₁ • CZ === S₁ ^ 2 • H₁ • S₁ ^ 2 • CZ • H₁ • S₁ ^ 2 • S₀ ^ 2
      
  --   conjugation:
  --     conj-H-X 
  --     conj-H-Z 
  --     conj-S-X 
  --     conj-S-Z 
  --     conj-CZ-Z 
  --     conj-CZ-X 
  --     etc. the usual conjugation rules

  -- NOTE: S in Sp(2*2,3) is ZZS in Clifford.

-}




{-

module Clifford-Mod-Scalar-Completeness where

  private
    variable
      n : ℕ

  open import N.Clifford.Clifford-Mod-Scalar p-3 p-prime g* g-gen renaming (module Lemmas1 to CL1)
  module Semi  = SemiDirect
  module Cli  = Clifford-Relations

  open Semi renaming (Gen to Gen₁ ; _QRel,_===_ to _QRel,_===₁_) using ()
  Gen₂ = Sym.Gen
  open Cli renaming (_QRel,_===_ to _QRel,_===₂_ ) using ()
  open Semi-GroupLike renaming (grouplike to grouplike₁) using ()
  open Clifford-GroupLike renaming (grouplike to grouplike₂) using ()

  
  to-cli-gen : Gen₁ n -> Word (Gen₂ n)
  to-cli-gen {₁₊ n} Semi.X-gen = Cli.X
  to-cli-gen {₁₊ n} Semi.Z-gen = Cli.Z
  to-cli-gen {₁₊ n} Semi.H-gen = Sym.H
  to-cli-gen {₁₊ n} Semi.S-gen = Cli.Z^ 1/2 • Sym.S
  to-cli-gen {₂₊ n} Semi.CZ-gen = Sym.CZ
  to-cli-gen {₂₊ n} (inj₁ (g XZ.↥)) = to-cli-gen (inj₁ g) Sym.↑
  to-cli-gen {₂₊ n} (inj₂ (g Sym.↥)) = to-cli-gen (inj₂ g) Sym.↑

  to-cli : Word (Gen₁ n) -> Word (Gen₂ n)
  to-cli = to-cli-gen WB.*

  f-well-defined : let open PB (n QRel,_===₂_) renaming (_≈_ to _≈₂_) in
    ∀ {w v} -> n QRel, w ===₁ v -> to-cli w ≈₂ to-cli v
  f-well-defined {n} (left XZ.order-X) = {!!}
  f-well-defined {n} (left XZ.order-Z) = {!!}
  f-well-defined {n} (left XZ.comm-Z-X) = {!!}
  f-well-defined {n} (left XZ.comm-X) = {!!}
  f-well-defined {n} (left XZ.comm-Z) = {!!}
  f-well-defined {n} (left (XZ.cong↑ x)) = {!!}
  f-well-defined {n} (right Sim.order-S) = {!!}
  f-well-defined {n@(₁₊ n')} (right Sim.order-H) = {!!}
    where
    open PP (n QRel,_===₂_)
  f-well-defined {n} (right (Sim.M-power k)) = {!!}
  f-well-defined {n} (right Sim.semi-MS) = {!!}
  f-well-defined {n} (right Sim.semi-M↑CZ) = {!!}
  f-well-defined {n} (right Sim.semi-M↓CZ) = {!!}
  f-well-defined {n} (right Sim.order-CZ) = {!!}
  f-well-defined {n} (right Sim.comm-CZ-S↓) = {!!}
  f-well-defined {n} (right Sim.comm-CZ-S↑) = {!!}
  f-well-defined {n} (right Sim.selinger-c10) = {!!}
  f-well-defined {n} (right Sim.selinger-c11) = {!!}
  f-well-defined {n} (right Sim.selinger-c12) = PB.axiom Cli.selinger-c12
  f-well-defined {n} (right Sim.selinger-c13) = PB.axiom Cli.selinger-c13
  f-well-defined {n} (right Sim.selinger-c14) = PB.axiom Cli.selinger-c14
  f-well-defined {n} (right Sim.selinger-c15) = PB.axiom Cli.selinger-c15
  f-well-defined {n} (right Sim.comm-H) = {!!}
  f-well-defined {n} (right Sim.comm-S) = {!!}
  f-well-defined {n} (right Sim.comm-CZ) = {!!}
  f-well-defined {n} (right (Sim.cong↑ x)) = {!!}
  f-well-defined {n} (mid (comm XZ.X-gen Sym.H-gen)) = {!!}
  f-well-defined {n} (mid (comm XZ.X-gen Sym.S-gen)) = {!!}
  f-well-defined {n} (mid (comm XZ.X-gen Sym.CZ-gen)) = {!!}
  f-well-defined {n} (mid (comm XZ.X-gen (h Sym.↥))) = {!!}
  f-well-defined {n} (mid (comm XZ.Z-gen Sym.H-gen)) = {!!}
  f-well-defined {n} (mid (comm XZ.Z-gen Sym.S-gen)) = {!!}
  f-well-defined {n} (mid (comm XZ.Z-gen Sym.CZ-gen)) = {!!}
  f-well-defined {n} (mid (comm XZ.Z-gen (h Sym.↥))) = {!!}
  f-well-defined {n} (mid (comm (n₁ XZ.↥) Sym.H-gen)) = {!!}
  f-well-defined {n} (mid (comm (n₁ XZ.↥) Sym.S-gen)) = {!!}
  f-well-defined {n} (mid (comm (n₁ XZ.↥) Sym.CZ-gen)) = {!!}
  f-well-defined {n} (mid (comm (n₁ XZ.↥) (h Sym.↥))) = {!!}


  f-well-defined {₁₊ n} order-SH = lemma-order-SH
    where
    open Lemmas1 n
  f-well-defined {₁₊ n} comm-HHS = lemma-comm-HHS
    where
    open Lemmas1b n
  f-well-defined {₁₊ n} (M-mul x y) = lemma-M-mul x y
    where
    open Lemmas1 n
  f-well-defined {₁₊ n} (semi-MS x) = lemma-semi-MS x
    where
    open Lemmas1 n
  f-well-defined {₂₊ n} (semi-M↑CZ x) = lemma-semi-M↑CZ x
    where
    open Lemmas2 n
  f-well-defined {₂₊ n} (semi-M↓CZ x) = lemma-semi-M↓CZ x
    where
    open Lemmas2 n
  f-well-defined {n} order-CZ = PB.axiom Sim.order-CZ
  f-well-defined {n} comm-CZ-S↓ = PB.axiom Sim.comm-CZ-S↓
  f-well-defined {n} comm-CZ-S↑ = PB.axiom Sim.comm-CZ-S↑
  f-well-defined {n} selinger-c10 = PB.axiom Sim.selinger-c10
  f-well-defined {n} selinger-c11 = PB.axiom Sim.selinger-c11
  f-well-defined {n} selinger-c12 = PB.axiom Sim.selinger-c12
  f-well-defined {n} selinger-c13 = PB.axiom Sim.selinger-c13
  f-well-defined {n} selinger-c14 = PB.axiom Sim.selinger-c14
  f-well-defined {n} selinger-c15 = PB.axiom Sim.selinger-c15
  f-well-defined {n} comm-H = PB.axiom Sim.comm-H
  f-well-defined {n} comm-S = PB.axiom Sim.comm-S
  f-well-defined {n} comm-CZ = PB.axiom Sim.comm-CZ
  f-well-defined {n} (cong↑ eq) = lemma-cong↑ _ _ (f-well-defined eq)
    where
    open Lemmas-Sim
  
  g-well-defined : let open PB (n QRel,_===₁_) renaming (_≈_ to _≈₁_) in
    ∀ {u t} -> n QRel, u ===₂ t -> id u ≈₁ id t
  g-well-defined Sim.order-S = PB.axiom _QRel,_===₁_.order-S
  g-well-defined {₁₊ n} Sim.order-H = lemma-HH-M-1
    where
    open Lemmas0 n
  g-well-defined {₁₊ n} (Sim.M-power k) = begin
    (Mg^ k) ≡⟨ auto ⟩
    Mg ^ toℕ k ≈⟨ lemma-^-cong (Mg) (M g′) (toℕ k) (refl) ⟩
    M g′ ^ toℕ k ≈⟨ lemma-M-power g′ (toℕ k) ⟩
    M (g^ k) ≈⟨ refl ⟩
    (M (g^ k)) ∎
    where
    open PB ((₁₊ n) QRel,_===₁_)
    open PP ((₁₊ n) QRel,_===₁_)
    open SR word-setoid
    open Lemmas0 n
    open Sim

    
  g-well-defined {₁₊ n} Sim.semi-MS = PB.axiom (_QRel,_===₁_.semi-MS ((g , g≠0)))
  g-well-defined Sim.semi-M↑CZ = PB.axiom (_QRel,_===₁_.semi-M↑CZ ((g , g≠0)))
  g-well-defined Sim.semi-M↓CZ = PB.axiom (_QRel,_===₁_.semi-M↓CZ ((g , g≠0)))
  g-well-defined Sim.order-CZ = PB.axiom _QRel,_===₁_.order-CZ
  g-well-defined Sim.comm-CZ-S↓ = PB.axiom _QRel,_===₁_.comm-CZ-S↓
  g-well-defined Sim.comm-CZ-S↑ = PB.axiom _QRel,_===₁_.comm-CZ-S↑
  g-well-defined Sim.selinger-c10 = PB.axiom _QRel,_===₁_.selinger-c10
  g-well-defined Sim.selinger-c11 = PB.axiom _QRel,_===₁_.selinger-c11
  g-well-defined Sim.selinger-c12 = PB.axiom _QRel,_===₁_.selinger-c12
  g-well-defined Sim.selinger-c13 = PB.axiom _QRel,_===₁_.selinger-c13
  g-well-defined Sim.selinger-c14 = PB.axiom _QRel,_===₁_.selinger-c14
  g-well-defined Sim.selinger-c15 = PB.axiom _QRel,_===₁_.selinger-c15
  g-well-defined Sim.comm-H = PB.axiom _QRel,_===₁_.comm-H
  g-well-defined Sim.comm-S = PB.axiom _QRel,_===₁_.comm-S
  g-well-defined Sim.comm-CZ = PB.axiom _QRel,_===₁_.comm-CZ
  g-well-defined (Sim.cong↑ eq) = lemma-cong↑ _ _ (g-well-defined eq)
    where
    open Lemmas-Sym


  open import Algebra.Bundles using (Group)
  open import Algebra.Morphism.Structures using (module GroupMorphisms)

  open GroupMorphisms


  Theorem-Sym-iso-Cli : ∀ {n} ->
    let
    module G1 = Group-Lemmas (Gen₁ n) (n QRel,_===₁_) grouplike₁
    module G2 = Group-Lemmas (Gen₂ n) (n QRel,_===₂_) grouplike₂
    in
    IsGroupIsomorphism (Group.rawGroup G1.•-ε-group) (Group.rawGroup G2.•-ε-group) id
  Theorem-Sym-iso-Cli {n}  = StarGroupIsomorphism.isGroupIsomorphism f-well-defined g-well-defined
    where
    open import Presentation.MorphismId (n QRel,_===₁_) (n QRel,_===₂_)
    open GroupMorphs (grouplike₁ {n}) (grouplike₂ {n})



  Theorem-Sym-iso-Sim' : ∀ {n} ->
    let
    module G1 = Group-Lemmas (Gen₁ n) (n QRel,_===₁_) grouplike₁
    module G2 = Group-Lemmas (Gen₂ n) (n QRel,_===₂_) grouplike₂
    in
    IsGroupIsomorphism (Group.rawGroup G2.•-ε-group) (Group.rawGroup G1.•-ε-group)  id
  Theorem-Sym-iso-Sim' {n} = StarGroupIsomorphism.isGroupIsomorphism g-well-defined f-well-defined
    where
    open import Presentation.MorphismId  (n QRel,_===₂_) (n QRel,_===₁_)
    open GroupMorphs (grouplike₂ {n}) (grouplike₁ {n}) 

-}

