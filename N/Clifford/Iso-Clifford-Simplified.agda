{-# OPTIONS --termination-depth=20 #-}
{-# OPTIONS --inversion-max-depth=1000 #-}

------------------------------------------------------------------------
-- The id-isomorphism  Clifford-Relations ≅ Simplified-Relations.
-- f-well-defined: every Clifford relation holds in Simplified
--                 (selinger via completeness; rest via axiom).
-- g-well-defined: every Simplified relation holds in Clifford
--                 (selinger via soundness; rest via axiom).
-- Fully machine-checked — NO termination pragma (route (B)).
------------------------------------------------------------------------

open import Level using (0ℓ)
open import Relation.Binary.PropositionalEquality using (_≡_ ; _≢_)
import Relation.Binary.PropositionalEquality as Eq
open import Function using (id)
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂ ; ∃)
open import Data.Nat hiding (_^_ ; _+_ ; _*_ ; _%_ ; _/_)
open import Data.Fin hiding (_+_ ; _-_)
open import Word.Base as WB hiding (wfoldl)
import Presentation.Base as PB
import Presentation.Properties as PP
open import Presentation.Construct.Base hiding (_*_)
open import Presentation.GroupLike
open import Data.Nat.Primality
open import Algebra.Morphism.Structures using (module GroupMorphisms)
open GroupMorphisms

open import Zp.ModularArithmetic
open import Zp.Fermats-little-theorem

module N.Clifford.Iso-Clifford-Simplified
  (p-3 : ℕ)
  (let p-2 = suc p-3)
  (p-prime : Prime (suc (suc p-2)))
  (let open PrimeModulus' p-2 p-prime)
  (g*@(g , g≠0) : ℤ* ₚ)
  (g-gen : ∀ ((x , _) : ℤ* ₚ) -> ∃ \ (k : ℤ ₚ-₁) -> x ≡ g ^′ toℕ k )
  where

pattern ₁₊ n = suc n
pattern ₂₊ n = suc (suc n)

open Primitive-Root-Modp' g* g-gen

open import N.Clifford.Clifford-Mod-Scalar p-3 p-prime g* g-gen
import N.Clifford.Clifford-Mod-Scalars-Simplified p-3 p-prime g* g-gen as Sim
import N.Clifford.Clifford-Simplified-Verify p-3 p-prime g* g-gen as Snd
import N.Clifford.Simplified-Lemmas p-3 p-prime g* g-gen as Cmp

open import Algebra.Bundles using (Group)

module CliR = Clifford-Relations
module SimR = Sim.Simplified-Relations

-- f : Clifford → Simplified  (every Clifford relation holds in Simplified)
f-well-defined : ∀ {n} → let open PB (SimR._QRel,_===_ n) renaming (_≈_ to _≈₂_) in
    ∀ {w v} -> CliR._QRel,_===_ n w v -> id w ≈₂ id v
f-well-defined CliR.order-S        = PB.axiom SimR.order-S
f-well-defined CliR.order-H        = PB.axiom SimR.order-H
f-well-defined (CliR.M-power k)    = PB.axiom (SimR.M-power k)
f-well-defined CliR.semi-M𝑠        = PB.axiom SimR.semi-M𝑠
f-well-defined CliR.order-SH       = PB.axiom SimR.order-SH
f-well-defined CliR.comm-HHSHHS    = PB.axiom SimR.comm-HHSHHS
f-well-defined CliR.comm-X-Z       = PB.axiom SimR.comm-X-Z
f-well-defined CliR.semi-M↑CZ      = PB.axiom SimR.semi-M↑CZ
f-well-defined CliR.semi-M↓CZ      = PB.axiom SimR.semi-M↓CZ
f-well-defined CliR.rel-X↑-CZ      = PB.axiom SimR.rel-X↑-CZ
f-well-defined CliR.rel-X↓-CZ      = PB.axiom SimR.rel-X↓-CZ
f-well-defined CliR.order-CZ       = PB.axiom SimR.order-CZ
f-well-defined CliR.comm-CZ-S↓     = PB.axiom SimR.comm-CZ-S↓
f-well-defined CliR.comm-CZ-S↑     = PB.axiom SimR.comm-CZ-S↑
f-well-defined CliR.selinger-c10   = Cmp.Completeness-S.completeness-c10 _
f-well-defined CliR.selinger-c11   = Cmp.Completeness-S.completeness-c11 _
f-well-defined CliR.selinger-c12   = PB.axiom SimR.selinger-c12
f-well-defined CliR.selinger-c13   = PB.axiom SimR.selinger-c13
f-well-defined CliR.selinger-c14   = PB.axiom SimR.selinger-c14
f-well-defined CliR.selinger-c15   = PB.axiom SimR.selinger-c15
f-well-defined CliR.comm-H         = PB.axiom SimR.comm-H
f-well-defined CliR.comm-S         = PB.axiom SimR.comm-S
f-well-defined CliR.comm-CZ        = PB.axiom SimR.comm-CZ
f-well-defined (CliR.cong↑ eq)     = Cmp.Lemmas-Clifford-S.lemma-cong↑ _ _ (f-well-defined eq)

-- g : Simplified → Clifford  (every Simplified relation holds in Clifford)
g-well-defined : ∀ {n} → let open PB (CliR._QRel,_===_ n) renaming (_≈_ to _≈₁_) in
  ∀ {u t} -> SimR._QRel,_===_ n u t -> id u ≈₁ id t
g-well-defined SimR.order-S        = PB.axiom CliR.order-S
g-well-defined SimR.order-H        = PB.axiom CliR.order-H
g-well-defined (SimR.M-power k)    = PB.axiom (CliR.M-power k)
g-well-defined SimR.semi-M𝑠        = PB.axiom CliR.semi-M𝑠
g-well-defined SimR.order-SH       = PB.axiom CliR.order-SH
g-well-defined SimR.comm-HHSHHS    = PB.axiom CliR.comm-HHSHHS
g-well-defined SimR.comm-X-Z       = PB.axiom CliR.comm-X-Z
g-well-defined SimR.semi-M↑CZ      = PB.axiom CliR.semi-M↑CZ
g-well-defined SimR.semi-M↓CZ      = PB.axiom CliR.semi-M↓CZ
g-well-defined SimR.rel-X↑-CZ      = PB.axiom CliR.rel-X↑-CZ
g-well-defined SimR.rel-X↓-CZ      = PB.axiom CliR.rel-X↓-CZ
g-well-defined SimR.order-CZ       = PB.axiom CliR.order-CZ
g-well-defined SimR.comm-CZ-S↓     = PB.axiom CliR.comm-CZ-S↓
g-well-defined SimR.comm-CZ-S↑     = PB.axiom CliR.comm-CZ-S↑
g-well-defined SimR.selinger-c10   = Snd.C10.soundness-c10 _
g-well-defined SimR.selinger-c11   = Snd.C11.soundness-c11 _
g-well-defined SimR.selinger-c12   = PB.axiom CliR.selinger-c12
g-well-defined SimR.selinger-c13   = PB.axiom CliR.selinger-c13
g-well-defined SimR.selinger-c14   = PB.axiom CliR.selinger-c14
g-well-defined SimR.selinger-c15   = PB.axiom CliR.selinger-c15
g-well-defined SimR.comm-H         = PB.axiom CliR.comm-H
g-well-defined SimR.comm-S         = PB.axiom CliR.comm-S
g-well-defined SimR.comm-CZ        = PB.axiom CliR.comm-CZ
g-well-defined (SimR.cong↑ eq)     = Lemmas-Clifford.lemma-cong↑ _ _ (g-well-defined eq)

module M (n : ℕ) where
  module G1 = Group-Lemmas (Gen n) (CliR._QRel,_===_ n) (Clifford-GroupLike.grouplike {n})
  module G2 = Group-Lemmas (Gen n) (SimR._QRel,_===_ n) (Cmp.Simplified-GroupLike-S.grouplike {n})

  open import Presentation.MorphismId (CliR._QRel,_===_ n) (SimR._QRel,_===_ n)
  open GroupMorphs (Clifford-GroupLike.grouplike {n}) (Cmp.Simplified-GroupLike-S.grouplike {n})

  Theorem-Clifford-iso-Simplified :
    IsGroupIsomorphism (Group.rawGroup G1.•-ε-group) (Group.rawGroup G2.•-ε-group) id
  Theorem-Clifford-iso-Simplified =
    StarGroupIsomorphism.isGroupIsomorphism f-well-defined g-well-defined
