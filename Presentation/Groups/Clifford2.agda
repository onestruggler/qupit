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
open import Data.Nat using (ℕ ; zero ; suc)
import Data.Nat as Nat
open import Data.Fin
open import Data.Fin.Induction
open import Data.Sum using (_⊎_ ; inj₁ ; inj₂ ; [_,_])
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

open import Presentation.Construct.Base
import Presentation.Construct.Properties.SemiDirectProduct2 as SDP2
import Presentation.Construct.Properties.DirectProduct as DP
import Presentation.Groups.Cyclic as Cyclic


open import Data.Fin.Properties using (suc-injective ; toℕ-inject₁ ; toℕ-fromℕ)
import Data.Nat.Properties as NP
import Presentation.Groups.Clifford1 as C1

module Presentation.Groups.Clifford2 where

module CliffordWithScalar where

  data Gen : Set where
    H0-gen : Gen
    S0-gen : Gen
    H1-gen : Gen
    S1-gen : Gen
    CZ-gen : Gen
    W-gen : Gen

  H0 : Word Gen
  H0 = [ H0-gen ]ʷ

  S0 : Word Gen
  S0 = [ S0-gen ]ʷ

  Z0 : Word Gen
  Z0 = S0 • S0

  X0 : Word Gen
  X0 = H0 • S0 • S0 • H0

  H1 : Word Gen
  H1 = [ H1-gen ]ʷ

  S1 : Word Gen
  S1 = [ S1-gen ]ʷ

  Z1 : Word Gen
  Z1 = S1 • S1

  X1 : Word Gen
  X1 = H1 • S1 • S1 • H1

  CZ : Word Gen
  CZ = [ CZ-gen ]ʷ
  
  CX : Word Gen
  CX = H1 • CZ • H1

  XC : Word Gen
  XC = H0 • CZ • H0

  W : Word Gen
  W = [ W-gen ]ʷ

  infix 4 _===_
  data _===_ : WRel Gen where
    order-W : W ^ 8 === ε
    order-S0 : S0 ^ 4 === ε
    order-H0 : H0 ^ 2 === ε
    order-S0H0 : (S0 • H0) ^ 3 === W
    order-S1 : S1 ^ 4 === ε
    order-H1 : H1 ^ 2 === ε
    order-S1H1 : (S1 • H1) ^ 3 === W
    order-CZ : CZ ^ 2 === ε
    
    comm-W : ∀ {gen} -> W • [ gen ]ʷ === [ gen ]ʷ • W
    comm-H0H1 : H0 • H1 === H1 • H0
    comm-H0S1 : H0 • S1 === S1 • H0
    comm-S0H1 : S0 • H1 === H1 • S0
    comm-S0S1 : S0 • S1 === S1 • S0

    comm-S0-CZ : S0 • CZ === CZ • S0
    comm-S1-CZ : S1 • CZ === CZ • S1
    rel-X0-CZ : X0 • CZ === CZ • Z1 • X0
    rel-X1-CZ : X1 • CZ === CZ • Z0 • X1
    rel-CZ-H0-CZ : CZ • H0 • CZ === S0 • H0 • CZ • S0 • H0 • S0 • S1 • W ^ 7
    rel-CZ-H1-CZ : CZ • H1 • CZ === S1 • H1 • CZ • S1 • H1 • S1 • S0 • W ^ 7


module ℤ₂⁴ where

  open import Data.Sum
  open import Data.Unit
  open C1
  
  Gen = ℤ₂².Gen ⊎ ℤ₂².Gen

  rel-ℤ₂⁴ = (ℤ₂²._===_ ⸲ ℤ₂²._===_ ⸲ Γₓ)
  infix 4 _===_
  _===_ = rel-ℤ₂⁴

  pattern Z0-gen = inj₁ (inj₂ tt)
  pattern X0-gen = inj₁ (inj₁ tt)
  pattern Z1-gen = inj₂ (inj₂ tt)
  pattern X1-gen = inj₂ (inj₁ tt)

  X0 : Word Gen
  X0 = [ X0-gen ]ʷ

  Z0 : Word Gen
  Z0 = [ Z0-gen ]ʷ

  X1 : Word Gen
  X1 = [ X1-gen ]ʷ

  Z1 : Word Gen
  Z1 = [ Z1-gen ]ʷ

  nfp'-ℤ₂⁴ : NFProperty' _===_
  nfp'-ℤ₂⁴ = DP.NFP'.nfp' ℤ₂².rel-ℤ₂² ℤ₂².rel-ℤ₂² ℤ₂².nfp' ℤ₂².nfp'



module Semidirect where

  open import Presentation.Groups.Symplectic2-Lemmas
  open import Presentation.Groups.Clifford-Lemmas
  open import Presentation.Construct.Base
  open ℤ₂⁴ hiding (Gen ; _===_)
  
  conj : Symplectic.Gen -> ℤ₂⁴.Gen -> Word ℤ₂⁴.Gen
  conj Symplectic.H0-gen X0-gen = Z0
  conj Symplectic.H0-gen X1-gen = X1
  conj Symplectic.H0-gen Z0-gen = X0
  conj Symplectic.H0-gen Z1-gen = Z1
  conj Symplectic.H1-gen X0-gen = X0
  conj Symplectic.H1-gen X1-gen = Z1
  conj Symplectic.H1-gen Z0-gen = Z0
  conj Symplectic.H1-gen Z1-gen = X1
  conj Symplectic.S0-gen X0-gen = X0 • Z0
  conj Symplectic.S0-gen X1-gen = X1
  conj Symplectic.S0-gen Z0-gen = Z0
  conj Symplectic.S0-gen Z1-gen = Z1
  conj Symplectic.S1-gen X0-gen = X0
  conj Symplectic.S1-gen X1-gen = X1 • Z1
  conj Symplectic.S1-gen Z0-gen = Z0
  conj Symplectic.S1-gen Z1-gen = Z1
  conj Symplectic.CZ-gen X0-gen = X0 • Z1
  conj Symplectic.CZ-gen X1-gen = X1 • Z0
  conj Symplectic.CZ-gen Z0-gen = Z0
  conj Symplectic.CZ-gen Z1-gen = Z1
  
  Gen = ℤ₂⁴.Gen ⊎ Symplectic.Gen
  sdp = (ℤ₂⁴.rel-ℤ₂⁴ ⸲ Symplectic._===_ ⸲ Γⱼ' conj)

  pattern H0-gen = inj₂ Symplectic.H0-gen
  pattern S0-gen = inj₂ Symplectic.S0-gen
  pattern H1-gen = inj₂ Symplectic.H1-gen
  pattern S1-gen = inj₂ Symplectic.S1-gen
  pattern CZ-gen = inj₂ Symplectic.CZ-gen
  pattern X0'-gen = inj₁ X0-gen
  pattern X1'-gen = inj₁ X1-gen
  pattern Z0'-gen = inj₁ Z0-gen
  pattern Z1'-gen = inj₁ Z1-gen

  H0 : Word Gen
  H0 = [ Symplectic.H0 ]ᵣ
  
  S0 : Word Gen
  S0 = [ Symplectic.S0 ]ᵣ

  X0' : Word Gen
  X0' = [ ℤ₂⁴.X0 ]ₗ

  Z0' : Word Gen
  Z0' = [ ℤ₂⁴.Z0 ]ₗ

  Z1' : Word Gen
  Z1' = [ ℤ₂⁴.Z1 ]ₗ

  H1 : Word Gen
  H1 = [ Symplectic.H1 ]ᵣ
  
  S1 : Word Gen
  S1 = [ Symplectic.S1 ]ᵣ

  X1' : Word Gen
  X1' = [ ℤ₂⁴.X1 ]ₗ

  CZ : Word Gen
  CZ = [ Symplectic.CZ ]ᵣ

  CX : Word Gen
  CX = [ Symplectic.CX ]ᵣ

  XC : Word Gen
  XC = [ Symplectic.XC ]ᵣ

  open PB Symplectic._===_ renaming (_===_ to _===₂_ ; _≈_ to _≈₂_) using ()
  open PP Symplectic._===_ renaming (•-ε-monoid to m₂ ; word-setoid to ws₂) using ()
  
  open PB ℤ₂⁴._===_ renaming (_===_ to _===₁_ ; _≈_ to _≈₁_) using ()
  open PP ℤ₂⁴._===_ renaming (•-ε-monoid to m₁ ; word-setoid to ws₁ ; by-assoc-and to by-assoc-and₁ ; by-assoc to by-assoc₁) using ()


  module SDP2A = SDP2 ℤ₂⁴._===_ Symplectic._===_ conj


  open PB ℤ₂⁴._===_

  open NFProperty' nfp'-ℤ₂⁴


  hyph : ∀ {c d} n -> c ===₂ d -> (conj ʰ') c n ≈₁ (conj ʰ') d n
  hyph {c} {d} [ X0-gen ]ʷ Symplectic.order-S0 = by-equal-nf auto
  hyph {c} {d} [ Z0-gen ]ʷ Symplectic.order-S0 = by-equal-nf auto
  hyph {c} {d} [ X1-gen ]ʷ Symplectic.order-S0 = by-equal-nf auto
  hyph {c} {d} [ Z1-gen ]ʷ Symplectic.order-S0 = by-equal-nf auto
  hyph {c} {d} [ X0-gen ]ʷ Symplectic.order-H0 = by-equal-nf auto
  hyph {c} {d} [ Z0-gen ]ʷ Symplectic.order-H0 = by-equal-nf auto
  hyph {c} {d} [ X1-gen ]ʷ Symplectic.order-H0 = by-equal-nf auto
  hyph {c} {d} [ Z1-gen ]ʷ Symplectic.order-H0 = by-equal-nf auto
  hyph {c} {d} [ X0-gen ]ʷ Symplectic.order-S1 = by-equal-nf auto
  hyph {c} {d} [ Z0-gen ]ʷ Symplectic.order-S1 = by-equal-nf auto
  hyph {c} {d} [ X1-gen ]ʷ Symplectic.order-S1 = by-equal-nf auto
  hyph {c} {d} [ Z1-gen ]ʷ Symplectic.order-S1 = by-equal-nf auto
  hyph {c} {d} [ X0-gen ]ʷ Symplectic.order-H1 = by-equal-nf auto
  hyph {c} {d} [ Z0-gen ]ʷ Symplectic.order-H1 = by-equal-nf auto
  hyph {c} {d} [ X1-gen ]ʷ Symplectic.order-H1 = by-equal-nf auto
  hyph {c} {d} [ Z1-gen ]ʷ Symplectic.order-H1 = by-equal-nf auto
  hyph {c} {d} [ X0-gen ]ʷ Symplectic.order-S0H0 = by-equal-nf auto
  hyph {c} {d} [ Z0-gen ]ʷ Symplectic.order-S0H0 = by-equal-nf auto
  hyph {c} {d} [ X1-gen ]ʷ Symplectic.order-S0H0 = by-equal-nf auto
  hyph {c} {d} [ Z1-gen ]ʷ Symplectic.order-S0H0 = by-equal-nf auto
  hyph {c} {d} [ X0-gen ]ʷ Symplectic.order-S1H1 = by-equal-nf auto
  hyph {c} {d} [ Z0-gen ]ʷ Symplectic.order-S1H1 = by-equal-nf auto
  hyph {c} {d} [ X1-gen ]ʷ Symplectic.order-S1H1 = by-equal-nf auto
  hyph {c} {d} [ Z1-gen ]ʷ Symplectic.order-S1H1 = by-equal-nf auto
  hyph {c} {d} [ X0-gen ]ʷ Symplectic.order-CZ = by-equal-nf auto
  hyph {c} {d} [ Z0-gen ]ʷ Symplectic.order-CZ = by-equal-nf auto
  hyph {c} {d} [ X1-gen ]ʷ Symplectic.order-CZ = by-equal-nf auto
  hyph {c} {d} [ Z1-gen ]ʷ Symplectic.order-CZ = by-equal-nf auto
  hyph {c} {d} [ X0-gen ]ʷ Symplectic.comm-H0H1 = by-equal-nf auto
  hyph {c} {d} [ Z0-gen ]ʷ Symplectic.comm-H0H1 = by-equal-nf auto
  hyph {c} {d} [ X1-gen ]ʷ Symplectic.comm-H0H1 = by-equal-nf auto
  hyph {c} {d} [ Z1-gen ]ʷ Symplectic.comm-H0H1 = by-equal-nf auto
  hyph {c} {d} [ X0-gen ]ʷ Symplectic.comm-H0S1 = by-equal-nf auto
  hyph {c} {d} [ Z0-gen ]ʷ Symplectic.comm-H0S1 = by-equal-nf auto
  hyph {c} {d} [ X1-gen ]ʷ Symplectic.comm-H0S1 = by-equal-nf auto
  hyph {c} {d} [ Z1-gen ]ʷ Symplectic.comm-H0S1 = by-equal-nf auto
  hyph {c} {d} [ X0-gen ]ʷ Symplectic.comm-S0H1 = by-equal-nf auto
  hyph {c} {d} [ Z0-gen ]ʷ Symplectic.comm-S0H1 = by-equal-nf auto
  hyph {c} {d} [ X1-gen ]ʷ Symplectic.comm-S0H1 = by-equal-nf auto
  hyph {c} {d} [ Z1-gen ]ʷ Symplectic.comm-S0H1 = by-equal-nf auto
  hyph {c} {d} [ X0-gen ]ʷ Symplectic.comm-S0S1 = by-equal-nf auto
  hyph {c} {d} [ Z0-gen ]ʷ Symplectic.comm-S0S1 = by-equal-nf auto
  hyph {c} {d} [ X1-gen ]ʷ Symplectic.comm-S0S1 = by-equal-nf auto
  hyph {c} {d} [ Z1-gen ]ʷ Symplectic.comm-S0S1 = by-equal-nf auto
  hyph {c} {d} [ X0-gen ]ʷ Symplectic.comm-S0-CZ = by-equal-nf auto
  hyph {c} {d} [ Z0-gen ]ʷ Symplectic.comm-S0-CZ = by-equal-nf auto
  hyph {c} {d} [ X1-gen ]ʷ Symplectic.comm-S0-CZ = by-equal-nf auto
  hyph {c} {d} [ Z1-gen ]ʷ Symplectic.comm-S0-CZ = by-equal-nf auto
  hyph {c} {d} [ X0-gen ]ʷ Symplectic.comm-S1-CZ = by-equal-nf auto
  hyph {c} {d} [ Z0-gen ]ʷ Symplectic.comm-S1-CZ = by-equal-nf auto
  hyph {c} {d} [ X1-gen ]ʷ Symplectic.comm-S1-CZ = by-equal-nf auto
  hyph {c} {d} [ Z1-gen ]ʷ Symplectic.comm-S1-CZ = by-equal-nf auto
  hyph {c} {d} [ X0-gen ]ʷ Symplectic.rel-CZ-H0-CZ = by-equal-nf auto
  hyph {c} {d} [ Z0-gen ]ʷ Symplectic.rel-CZ-H0-CZ = by-equal-nf auto
  hyph {c} {d} [ X1-gen ]ʷ Symplectic.rel-CZ-H0-CZ = by-equal-nf auto
  hyph {c} {d} [ Z1-gen ]ʷ Symplectic.rel-CZ-H0-CZ = by-equal-nf auto
  hyph {c} {d} [ X0-gen ]ʷ Symplectic.rel-CZ-H1-CZ = by-equal-nf auto
  hyph {c} {d} [ Z0-gen ]ʷ Symplectic.rel-CZ-H1-CZ = by-equal-nf auto
  hyph {c} {d} [ X1-gen ]ʷ Symplectic.rel-CZ-H1-CZ = by-equal-nf auto
  hyph {c} {d} [ Z1-gen ]ʷ Symplectic.rel-CZ-H1-CZ = by-equal-nf auto
  hyph {c} {d} ε Symplectic.order-S0 = by-equal-nf auto
  hyph {c} {d} ε Symplectic.order-H0 = by-equal-nf auto
  hyph {c} {d} ε Symplectic.order-S0H0 = by-equal-nf auto
  hyph {c} {d} ε Symplectic.order-S1 = by-equal-nf auto
  hyph {c} {d} ε Symplectic.order-H1 = by-equal-nf auto
  hyph {c} {d} ε Symplectic.order-S1H1 = by-equal-nf auto
  hyph {c} {d} ε Symplectic.order-CZ = by-equal-nf auto
  hyph {c} {d} ε Symplectic.comm-H0H1 = by-equal-nf auto
  hyph {c} {d} ε Symplectic.comm-H0S1 = by-equal-nf auto
  hyph {c} {d} ε Symplectic.comm-S0H1 = by-equal-nf auto
  hyph {c} {d} ε Symplectic.comm-S0S1 = by-equal-nf auto
  hyph {c} {d} ε Symplectic.comm-S0-CZ = by-equal-nf auto
  hyph {c} {d} ε Symplectic.comm-S1-CZ = by-equal-nf auto
  hyph {c} {d} ε Symplectic.rel-CZ-H0-CZ = by-equal-nf auto
  hyph {c} {d} ε Symplectic.rel-CZ-H1-CZ = by-equal-nf auto
  hyph {c} {d} (n • n₁) eq@Symplectic.order-S0 = cong (hyph n eq) (hyph n₁ eq)
  hyph {c} {d} (n • n₁) eq@Symplectic.order-H0 = cong (hyph n eq) (hyph n₁ eq)
  hyph {c} {d} (n • n₁) eq@Symplectic.order-S0H0 = cong (hyph n eq) (hyph n₁ eq)
  hyph {c} {d} (n • n₁) eq@Symplectic.order-S1 = cong (hyph n eq) (hyph n₁ eq)
  hyph {c} {d} (n • n₁) eq@Symplectic.order-H1 = cong (hyph n eq) (hyph n₁ eq)
  hyph {c} {d} (n • n₁) eq@Symplectic.order-S1H1 = cong (hyph n eq) (hyph n₁ eq)
  hyph {c} {d} (n • n₁) eq@Symplectic.order-CZ = cong (hyph n eq) (hyph n₁ eq)
  hyph {c} {d} (n • n₁) eq@Symplectic.comm-H0H1 = cong (hyph n eq) (hyph n₁ eq)
  hyph {c} {d} (n • n₁) eq@Symplectic.comm-H0S1 = cong (hyph n eq) (hyph n₁ eq)
  hyph {c} {d} (n • n₁) eq@Symplectic.comm-S0H1 = cong (hyph n eq) (hyph n₁ eq)
  hyph {c} {d} (n • n₁) eq@Symplectic.comm-S0S1 = cong (hyph n eq) (hyph n₁ eq)
  hyph {c} {d} (n • n₁) eq@Symplectic.comm-S0-CZ = cong (hyph n eq) (hyph n₁ eq)
  hyph {c} {d} (n • n₁) eq@Symplectic.comm-S1-CZ = cong (hyph n eq) (hyph n₁ eq)
  hyph {c} {d} (n • n₁) eq@Symplectic.rel-CZ-H0-CZ = cong (hyph n eq) (hyph n₁ eq)
  hyph {c} {d} (n • n₁) eq@Symplectic.rel-CZ-H1-CZ = cong (hyph n eq) (hyph n₁ eq)


  hypn : ∀ c {w v} -> w ===₁ v -> (conj ⁿ') c w ≈₁ (conj ⁿ') c v
  hypn Symplectic.H0-gen {w} {v} (left (left Cyclic.order)) = by-equal-nf auto
  hypn Symplectic.H0-gen {w} {v} (left (right Cyclic.order)) = by-equal-nf auto
  hypn Symplectic.H0-gen {w} {v} (left (mid (comm tt tt))) = by-equal-nf auto
  hypn Symplectic.H0-gen {w} {v} (right (left Cyclic.order)) = by-equal-nf auto
  hypn Symplectic.H0-gen {w} {v} (right (right Cyclic.order)) = by-equal-nf auto
  hypn Symplectic.H0-gen {w} {v} (right (mid (comm tt tt))) = by-equal-nf auto
  hypn Symplectic.H0-gen {w} {v} (mid (comm (inj₁ tt) (inj₁ tt))) = by-equal-nf auto
  hypn Symplectic.H0-gen {w} {v} (mid (comm (inj₁ tt) (inj₂ tt))) = by-equal-nf auto
  hypn Symplectic.H0-gen {w} {v} (mid (comm (inj₂ tt) (inj₁ tt))) = by-equal-nf auto
  hypn Symplectic.H0-gen {w} {v} (mid (comm (inj₂ tt) (inj₂ tt))) = by-equal-nf auto
  hypn Symplectic.S0-gen {w} {v} (left (left Cyclic.order)) = by-equal-nf auto
  hypn Symplectic.S0-gen {w} {v} (left (right Cyclic.order)) = by-equal-nf auto
  hypn Symplectic.S0-gen {w} {v} (left (mid (comm tt tt))) = by-equal-nf auto
  hypn Symplectic.S0-gen {w} {v} (right (left Cyclic.order)) = by-equal-nf auto
  hypn Symplectic.S0-gen {w} {v} (right (right Cyclic.order)) = by-equal-nf auto
  hypn Symplectic.S0-gen {w} {v} (right (mid (comm tt tt))) = by-equal-nf auto
  hypn Symplectic.S0-gen {w} {v} (mid (comm (inj₁ tt) (inj₁ tt))) = by-equal-nf auto
  hypn Symplectic.S0-gen {w} {v} (mid (comm (inj₁ tt) (inj₂ tt))) = by-equal-nf auto
  hypn Symplectic.S0-gen {w} {v} (mid (comm (inj₂ tt) (inj₁ tt))) = by-equal-nf auto
  hypn Symplectic.S0-gen {w} {v} (mid (comm (inj₂ tt) (inj₂ tt))) = by-equal-nf auto
  hypn Symplectic.H1-gen {w} {v} (left (left Cyclic.order)) = by-equal-nf auto
  hypn Symplectic.H1-gen {w} {v} (left (right Cyclic.order)) = by-equal-nf auto
  hypn Symplectic.H1-gen {w} {v} (left (mid (comm tt tt))) = by-equal-nf auto
  hypn Symplectic.H1-gen {w} {v} (right (left Cyclic.order)) = by-equal-nf auto
  hypn Symplectic.H1-gen {w} {v} (right (right Cyclic.order)) = by-equal-nf auto
  hypn Symplectic.H1-gen {w} {v} (right (mid (comm tt tt))) = by-equal-nf auto
  hypn Symplectic.H1-gen {w} {v} (mid (comm (inj₁ tt) (inj₁ tt))) = by-equal-nf auto
  hypn Symplectic.H1-gen {w} {v} (mid (comm (inj₁ tt) (inj₂ tt))) = by-equal-nf auto
  hypn Symplectic.H1-gen {w} {v} (mid (comm (inj₂ tt) (inj₁ tt))) = by-equal-nf auto
  hypn Symplectic.H1-gen {w} {v} (mid (comm (inj₂ tt) (inj₂ tt))) = by-equal-nf auto
  hypn Symplectic.S1-gen {w} {v} (left (left Cyclic.order)) = by-equal-nf auto
  hypn Symplectic.S1-gen {w} {v} (left (right Cyclic.order)) = by-equal-nf auto
  hypn Symplectic.S1-gen {w} {v} (left (mid (comm tt tt))) = by-equal-nf auto
  hypn Symplectic.S1-gen {w} {v} (right (left Cyclic.order)) = by-equal-nf auto
  hypn Symplectic.S1-gen {w} {v} (right (right Cyclic.order)) = by-equal-nf auto
  hypn Symplectic.S1-gen {w} {v} (right (mid (comm tt tt))) = by-equal-nf auto
  hypn Symplectic.S1-gen {w} {v} (mid (comm (inj₁ tt) (inj₁ tt))) = by-equal-nf auto
  hypn Symplectic.S1-gen {w} {v} (mid (comm (inj₁ tt) (inj₂ tt))) = by-equal-nf auto
  hypn Symplectic.S1-gen {w} {v} (mid (comm (inj₂ tt) (inj₁ tt))) = by-equal-nf auto
  hypn Symplectic.S1-gen {w} {v} (mid (comm (inj₂ tt) (inj₂ tt))) = by-equal-nf auto
  hypn Symplectic.CZ-gen {w} {v} (left (left Cyclic.order)) = by-equal-nf auto
  hypn Symplectic.CZ-gen {w} {v} (left (right Cyclic.order)) = by-equal-nf auto
  hypn Symplectic.CZ-gen {w} {v} (left (mid (comm tt tt))) = by-equal-nf auto
  hypn Symplectic.CZ-gen {w} {v} (right (left Cyclic.order)) = by-equal-nf auto
  hypn Symplectic.CZ-gen {w} {v} (right (right Cyclic.order)) = by-equal-nf auto
  hypn Symplectic.CZ-gen {w} {v} (right (mid (comm tt tt))) = by-equal-nf auto
  hypn Symplectic.CZ-gen {w} {v} (mid (comm (inj₁ tt) (inj₁ tt))) = by-equal-nf auto
  hypn Symplectic.CZ-gen {w} {v} (mid (comm (inj₁ tt) (inj₂ tt))) = by-equal-nf auto
  hypn Symplectic.CZ-gen {w} {v} (mid (comm (inj₂ tt) (inj₁ tt))) = by-equal-nf auto
  hypn Symplectic.CZ-gen {w} {v} (mid (comm (inj₂ tt) (inj₂ tt))) = by-equal-nf auto


  sdp-nfp' : NFProperty' sdp
  sdp-nfp' = SDP2.NFP'.nfp' ℤ₂⁴._===_ Symplectic._===_ conj hyph hypn ℤ₂⁴.nfp'-ℤ₂⁴ Sym2.Sym2-nfp'

module Iso where

  Gen = Semidirect.Gen
  sdp = Semidirect.sdp

  sdp-nfp' : NFProperty' sdp
  sdp-nfp' = Semidirect.sdp-nfp'

  open PB sdp renaming (_===_ to _===₂_ ; _≈_ to _≈₂_) using ()
  open PP sdp renaming (•-ε-monoid to m₂ ; word-setoid to ws₂)

  open import Presentation.Groups.Clifford-Lemmas
  open PB Clifford._===_ renaming (_===_ to _===₁_ ; _≈_ to _≈₁_) using ()
  open PP Clifford._===_ renaming (•-ε-monoid to m₁ ; word-setoid to ws₁ ; by-assoc to by-assoc₁ ;  by-assoc-and to by-assoc-and₁)

  open PB hiding (_===_)

  open import Algebra.Bundles using (Monoid)
  open import Algebra.Morphism.Structures using (module MonoidMorphisms)
  open import Presentation.Morphism


  f : Clifford.Gen -> Word Gen
  f Clifford.H0-gen = Semidirect.H0
  f Clifford.S0-gen = Semidirect.X0' • Semidirect.S0
  f Clifford.H1-gen = Semidirect.H1
  f Clifford.S1-gen = Semidirect.X1' • Semidirect.S1
  f Clifford.CZ-gen = Semidirect.CZ -- Semidirect.H0 • Semidirect.H1 • Semidirect.CZ • Semidirect.H1 • Semidirect.H0

  open Semidirect using (H0-gen ; H1-gen ; S0-gen ; S1-gen ; CZ-gen)
    renaming (X0'-gen to X0-gen ; X1'-gen to X1-gen ; Z0'-gen to Z0-gen ; Z1'-gen to Z1-gen)

  g : Gen -> Word Clifford.Gen
  g X0-gen = Clifford.X0
  g Z0-gen = Clifford.Z0
  g H0-gen = Clifford.H0
  g S0-gen = Clifford.X0 • Clifford.S0
  g X1-gen = Clifford.X1
  g Z1-gen = Clifford.Z1
  g H1-gen = Clifford.H1
  g S1-gen = Clifford.X1 • Clifford.S1
  g CZ-gen = Clifford.CZ • Clifford.Z0

  open PP.NFProperty' sdp-nfp'

  f-well-defined : ∀ {w v} -> w ===₁ v -> (f *) w ≈₂ (f *) v
  f-well-defined {w} {v} Clifford.order-S0 = by-equal-nf Eq.refl
  f-well-defined {w} {v} Clifford.order-H0 = by-equal-nf Eq.refl
  f-well-defined {w} {v} Clifford.order-S0H0 = by-equal-nf Eq.refl
  f-well-defined {w} {v} Clifford.order-S1 = by-equal-nf Eq.refl
  f-well-defined {w} {v} Clifford.order-H1 = by-equal-nf Eq.refl
  f-well-defined {w} {v} Clifford.order-S1H1 = by-equal-nf Eq.refl
  f-well-defined Clifford.order-CZ = by-equal-nf Eq.refl
  f-well-defined Clifford.comm-H0H1 = by-equal-nf Eq.refl
  f-well-defined Clifford.comm-H0S1 = by-equal-nf Eq.refl
  f-well-defined Clifford.comm-S0H1 = by-equal-nf Eq.refl
  f-well-defined Clifford.comm-S0S1 = by-equal-nf Eq.refl
  f-well-defined Clifford.comm-S0-CZ = by-equal-nf {!Eq.refl!}
  f-well-defined Clifford.comm-S1-CZ = by-equal-nf {!nf ((f *) (Clifford.S0 • Clifford.CZ))!}
  f-well-defined Clifford.rel-X0-CZ = by-equal-nf auto
  f-well-defined Clifford.rel-X1-CZ = by-equal-nf auto
  f-well-defined Clifford.rel-CZ-H0-CZ = by-equal-nf {!nf ((f *) (Clifford.CZ • Clifford.S0))!}
  f-well-defined Clifford.rel-CZ-H1-CZ = by-equal-nf {!!}

  open import Presentation.Groups.Symplectic2-Lemmas

  g-well-defined : ∀ {w v} -> w ===₂ v -> (g *) w ≈₁ (g *) v
  g-well-defined {w} {v} (left (left (left Cyclic.order))) = rewrite-clifford 20 auto
  g-well-defined {w} {v} (left (left (right Cyclic.order))) = rewrite-clifford 20 auto
  g-well-defined {w} {v} (left (left (mid (comm tt tt)))) = rewrite-clifford 20 auto
  g-well-defined {w} {v} (left (right (left Cyclic.order))) = rewrite-clifford 20 auto
  g-well-defined {w} {v} (left (right (right Cyclic.order))) = rewrite-clifford 20 auto
  g-well-defined {w} {v} (left (right (mid (comm tt tt)))) = rewrite-clifford 20 auto
  g-well-defined {w} {v} (left (mid (comm (inj₁ tt) (inj₁ tt)))) = rewrite-clifford 20 auto
  g-well-defined {w} {v} (left (mid (comm (inj₁ tt) (inj₂ tt)))) = rewrite-clifford 20 auto
  g-well-defined {w} {v} (left (mid (comm (inj₂ tt) (inj₁ tt)))) = rewrite-clifford 20 auto
  g-well-defined {w} {v} (left (mid (comm (inj₂ tt) (inj₂ tt)))) = rewrite-clifford 20 auto
  g-well-defined {w} {v} (right Symplectic.order-S0) = rewrite-clifford 20 auto
  g-well-defined {w} {v} (right Symplectic.order-H0) = rewrite-clifford 20 auto
  g-well-defined {w} {v} (right Symplectic.order-S0H0) = rewrite-clifford 20 auto
  g-well-defined {w} {v} (right Symplectic.order-S1) = rewrite-clifford 20 auto
  g-well-defined {w} {v} (right Symplectic.order-H1) = rewrite-clifford 20 auto
  g-well-defined {w} {v} (right Symplectic.order-S1H1) = rewrite-clifford 20 auto
  g-well-defined {w} {v} (right Symplectic.order-CZ) = rewrite-clifford 20 auto
  g-well-defined {w} {v} (right Symplectic.comm-H0H1) = rewrite-clifford 20 auto
  g-well-defined {w} {v} (right Symplectic.comm-H0S1) = rewrite-clifford 20 auto
  g-well-defined {w} {v} (right Symplectic.comm-S0H1) = rewrite-clifford 20 auto
  g-well-defined {w} {v} (right Symplectic.comm-S0S1) = rewrite-clifford 40 auto
  g-well-defined {w} {v} (right Symplectic.comm-S0-CZ) = {!(g *) [ Symplectic.S1 • Symplectic.S0 ]ᵣ!}
  g-well-defined {w} {v} (right Symplectic.comm-S1-CZ) = {!rewrite-clifford 80 auto!}
  g-well-defined {w} {v} (right Symplectic.rel-CZ-H0-CZ) = {!rewrite-clifford 80 auto!}
  g-well-defined {w} {v} (right Symplectic.rel-CZ-H1-CZ) = {!rewrite-clifford 80 auto!}
  g-well-defined {w} {v} (mid (comm (inj₁ (inj₁ tt)) Symplectic.H0-gen)) = rewrite-clifford 20 auto
  g-well-defined {w} {v} (mid (comm (inj₁ (inj₂ tt)) Symplectic.H0-gen)) = rewrite-clifford 20 auto
  g-well-defined {w} {v} (mid (comm (inj₁ (inj₁ tt)) Symplectic.S0-gen)) = rewrite-clifford 20 auto
  g-well-defined {w} {v} (mid (comm (inj₁ (inj₂ tt)) Symplectic.S0-gen)) = rewrite-clifford 20 auto
  g-well-defined {w} {v} (mid (comm (inj₁ (inj₁ tt)) Symplectic.H1-gen)) = rewrite-clifford 20 auto
  g-well-defined {w} {v} (mid (comm (inj₁ (inj₂ tt)) Symplectic.H1-gen)) = rewrite-clifford 20 auto
  g-well-defined {w} {v} (mid (comm (inj₁ (inj₁ tt)) Symplectic.S1-gen)) = rewrite-clifford 20 auto
  g-well-defined {w} {v} (mid (comm (inj₁ (inj₂ tt)) Symplectic.S1-gen)) = rewrite-clifford 20 auto
  g-well-defined {w} {v} (mid (comm (inj₁ (inj₁ tt)) Symplectic.CZ-gen)) = rewrite-clifford 20 auto
  g-well-defined {w} {v} (mid (comm (inj₁ (inj₂ tt)) Symplectic.CZ-gen)) = rewrite-clifford 20 auto
  g-well-defined {w} {v} (mid (comm (inj₂ (inj₁ tt)) Symplectic.H0-gen)) = rewrite-clifford 20 auto
  g-well-defined {w} {v} (mid (comm (inj₂ (inj₂ tt)) Symplectic.H0-gen)) = rewrite-clifford 20 auto
  g-well-defined {w} {v} (mid (comm (inj₂ (inj₁ tt)) Symplectic.S0-gen)) = rewrite-clifford 20 auto
  g-well-defined {w} {v} (mid (comm (inj₂ (inj₂ tt)) Symplectic.S0-gen)) = rewrite-clifford 20 auto
  g-well-defined {w} {v} (mid (comm (inj₂ (inj₁ tt)) Symplectic.H1-gen)) = rewrite-clifford 20 auto
  g-well-defined {w} {v} (mid (comm (inj₂ (inj₂ tt)) Symplectic.H1-gen)) = rewrite-clifford 20 auto
  g-well-defined {w} {v} (mid (comm (inj₂ (inj₁ tt)) Symplectic.S1-gen)) = rewrite-clifford 20 auto
  g-well-defined {w} {v} (mid (comm (inj₂ (inj₂ tt)) Symplectic.S1-gen)) = rewrite-clifford 20 auto
  g-well-defined {w} {v} (mid (comm (inj₂ (inj₁ tt)) Symplectic.CZ-gen)) = rewrite-clifford 40 auto
  g-well-defined {w} {v} (mid (comm (inj₂ (inj₂ tt)) Symplectic.CZ-gen)) = rewrite-clifford 20 auto

  
{-
  f-left-inv-gen : ∀ x -> [ x ]ʷ ≈₂ (f *) (g x)
  f-left-inv-gen (inj₁ (inj₁ tt)) = by-equal-nf Eq.refl
  f-left-inv-gen (inj₁ (inj₂ tt)) = by-equal-nf Eq.refl
  f-left-inv-gen (inj₂ Symplectic.H0-gen) = by-equal-nf Eq.refl
  f-left-inv-gen (inj₂ Symplectic.S0-gen) = by-equal-nf Eq.refl

  g-left-inv-gen : ∀ x -> [ x ]ʷ ≈₁ (g *) (f x)
  g-left-inv-gen Clifford.H0-gen = refl
  g-left-inv-gen Clifford.S0-gen = begin
    Clifford.S0 ≈⟨ sym left-unit ⟩
    ε • Clifford.S0 ≈⟨ cong (sym Clifford.lemma-X0X0) refl ⟩
    (Clifford.X0 • Clifford.X0) • Clifford.S0 ≈⟨ assoc ⟩
    Clifford.X0 • Clifford.X0 • Clifford.S0 ∎
    where open SR ws₁

  open MonoidMorphisms 

  Theorem-Clifford-iso-ℤ₂⁴⋊Sym : IsMonoidIsomorphism (Monoid.rawMonoid m₁) (Monoid.rawMonoid m₂) (f *)
  Theorem-Clifford-iso-ℤ₂⁴⋊Sym = S0tarIsomorphism.isMonoidIsomorphism Clifford._===_ sdp f g f-well-defined  f-left-inv-gen g-well-defined  g-left-inv-gen

-}



{-
  
  lemma-X0X0 : X0 ^ 2 ≈ ε
  lemma-X0X0 = begin
    X0 ^ 2 ≈⟨ refl ⟩
    (H0 • S0 • S0 • H0) ^ 2 ≈⟨ by-assoc Eq.refl ⟩
    (H0 • S0 • S0) • H0 ^ 2 • S0 ^ 2 • H0 ≈⟨ cong refl (cong (axiom order-H0) refl) ⟩
    (H0 • S0 • S0) • ε • S0 ^ 2 • H0 ≈⟨ by-assoc Eq.refl ⟩
    H0 • S0 ^ 4 • H0 ≈⟨ cong refl (cong (axiom order-S0) refl) ⟩
    H0 • ε • H0 ≈⟨ trans (cong refl left-unit) (axiom order-H0) ⟩
    ε ∎

  lemma-S0H0S0H0S0=H0 : (S0 • H0) ^ 2 • S0 ≈ H0
  lemma-S0H0S0H0S0=H0 = begin
    (S0 • H0) ^ 2 • S0 ≈⟨ cong refl (sym
                                   (trans (cong refl (axiom order-H0))
                                    right-unit)) ⟩
    (S0 • H0) ^ 2 • S0 • H0 ^ 2 ≈⟨ by-assoc Eq.refl ⟩
    (S0 • H0) ^ 3 • H0 ≈⟨ trans (cong (axiom order-S0H0) refl)
                        left-unit ⟩
    H0 ∎

  lemma-H0S0H0=S0H0S0 : H0 • S0 • H0 ≈ S0 ^ 3 • H0 • S0 ^ 3
  lemma-H0S0H0=S0H0S0 = begin
    H0 • S0 • H0 ≈⟨ sym right-unit ⟩
    (H0 • S0 • H0) • ε ≈⟨ sym (cong refl (axiom order-S0)) ⟩
    (H0 • S0 • H0) • S0 ^ 4 ≈⟨ trans (sym left-unit) (cong (sym (axiom order-S0)) refl) ⟩
    S0 ^ 4 • (H0 • S0 • H0) • S0 ^ 4 ≈⟨ by-assoc Eq.refl ⟩
    (S0 ^ 3  • (S0 • H0) ^ 2 • S0) • S0 ^ 3 ≈⟨ cong (cong refl lemma-S0H0S0H0S0=H0) refl ⟩
    (S0 ^ 3 • H0) • S0 ^ 3 ≈⟨ assoc ⟩
    S0 ^ 3 • H0 • S0 ^ 3 ∎


  lemma-H0S0 : H0 • S0 ≈ S0 ^ 3 • H0 • S0 ^ 3 • H0
  lemma-H0S0 = begin
    H0 • S0 ≈⟨ trans (sym right-unit) (sym (cong refl (axiom order-H0))) ⟩
    (H0 • S0) • H0 • H0 ≈⟨ by-assoc Eq.refl ⟩
    (H0 • S0 • H0) • H0 ≈⟨ cong refl (trans (sym left-unit) (sym (cong (axiom order-S0) refl))) ⟩
    (H0 • S0 • H0) • S0 ^ 4 • H0 ≈⟨ by-assoc Eq.refl ⟩
    H0 • (S0 • H0 • S0) • S0 ^ 3 • H0 ≈⟨ cong refl (cong refl (trans (sym left-unit) (cong (sym (axiom order-H0)) refl))) ⟩
    H0 • (S0 • H0 • S0) • H0 ^ 2 • S0 ^ 3 • H0 ≈⟨ trans (sym left-unit) (sym (cong (axiom order-S0) refl)) ⟩
    S0 ^ 4 • H0 • (S0 • H0 • S0) • H0 ^ 2 • S0 ^ 3 • H0 ≈⟨ by-assoc Eq.refl ⟩
    (S0 ^ 3 • (S0 • H0) ^ 3) • H0 • S0 ^ 3 • H0 ≈⟨ cong (cong refl (axiom order-S0H0)) refl ⟩
    (S0 ^ 3 • ε) • H0 • S0 ^ 3 • H0 ≈⟨ cong right-unit refl ⟩
    S0 ^ 3 • H0 • S0 ^ 3 • H0 ∎

  lemma-H0S0' : H0 • S0 ≈ S0 ^ 3 • X0 • H0 • S0 • H0
  lemma-H0S0' = begin
    H0 • S0 ≈⟨ lemma-H0S0 ⟩
    S0 ^ 3 • H0 • S0 ^ 3 • H0 ≈⟨ by-assoc Eq.refl ⟩
    (S0 ^ 3 • H0 • S0 ^ 2) • S0 • H0 ≈⟨ cong refl (trans (sym left-unit) (cong (sym (axiom order-H0)) refl)) ⟩
    (S0 ^ 3 • H0 • S0 ^ 2) • (H0 • H0) • S0 • H0 ≈⟨ by-assoc Eq.refl ⟩
    (S0 ^ 3) • (H0 • S0 • S0 • H0) • H0 • S0 • H0 ≈⟨ cong refl (cong (sym (refl)) refl) ⟩
    (S0 ^ 3) • X0 • H0 • S0 • H0 ≈⟨ by-assoc Eq.refl ⟩
    S0 ^ 3 • X0 • H0 • S0 • H0 ∎

  lemma-H0S0S0 : (H0 • S0) • S0 ≈ X0 • H0
  lemma-H0S0S0 = begin
    (H0 • S0) • S0 ≈⟨ cong refl (trans (sym right-unit) (cong refl (sym (axiom order-H0)))) ⟩
    (H0 • S0) • S0 • H0 • H0 ≈⟨ by-assoc Eq.refl ⟩
    (H0 • S0 • S0 • H0) • H0 ≈⟨ cong (sym (refl)) refl ⟩
    X0 • H0 ∎

  lemma-H0S0H0 : (H0 • S0 • H0) • H0 ≈ (S0 ^ 3 • X0) • H0 • S0 • H0
  lemma-H0S0H0 = begin
    (H0 • S0 • H0) • H0 ≈⟨ by-assoc Eq.refl ⟩
    H0 • S0 • H0 • H0 ≈⟨ cong refl (trans (cong refl (axiom order-H0)) right-unit) ⟩
    H0 • S0 ≈⟨ lemma-H0S0' ⟩
    S0 ^ 3 • X0 • H0 • S0 • H0 ≈⟨ by-assoc Eq.refl ⟩
    (S0 ^ 3 • X0) • H0 • S0 • H0 ∎

  lemma-H0S0H0' : (H0 • S0) • H0 ≈ (S0 ^ 3 • X0) • H0 • S0
  lemma-H0S0H0' = begin
    (H0 • S0) • H0 ≈⟨ cong lemma-H0S0' refl ⟩
    (S0 ^ 3 • X0 • H0 • S0 • H0) • H0 ≈⟨ by-assoc Eq.refl ⟩
    (S0 ^ 3 • X0 • H0 • S0) • H0 • H0 ≈⟨ trans (cong refl (axiom order-H0)) right-unit ⟩
    (S0 ^ 3 • X0 • H0 • S0) ≈⟨ by-assoc Eq.refl ⟩
    (S0 ^ 3 • X0) • H0 • S0 ∎

  lemma-H0S0X0 : (H0 • S0) • X0 ≈ (S0 ^ 2 • X0) • H0 • S0
  lemma-H0S0X0 = begin
    (H0 • S0) • X0 ≈⟨ cong lemma-H0S0' refl ⟩
    (S0 ^ 3 • X0 • H0 • S0 • H0) • X0 ≈⟨ cong refl (refl) ⟩
    (S0 ^ 3 • X0 • H0 • S0 • H0) • (H0 • S0 • S0 • H0) ≈⟨ by-assoc Eq.refl ⟩
    (S0 ^ 3 • X0 • H0 • S0) • (H0 • H0) • (S0 • S0 • H0) ≈⟨ cong refl (trans (cong (axiom order-H0) refl) left-unit) ⟩
    (S0 ^ 3 • X0 • H0 • S0) • (S0 • S0 • H0) ≈⟨ cong (cong refl (cong refl (cong (refl) refl))) refl ⟩
    (S0 ^ 3 • (H0 • S0 • S0 • H0) • H0 • S0) • (S0 • S0 • H0) ≈⟨ by-assoc Eq.refl ⟩
    (S0 ^ 3 • H0 • S0 • S0) • (H0 • H0) • S0 • (S0 • S0 • H0) ≈⟨ cong refl (trans (cong (axiom order-H0) refl) left-unit) ⟩
    (S0 ^ 3 • H0 • S0 • S0) • S0 • (S0 • S0 • H0) ≈⟨ by-assoc Eq.refl ⟩
    (S0 ^ 3 • H0 • S0) • (S0 • S0 • S0 • S0) • H0 ≈⟨ cong refl (trans (cong (axiom order-S0) refl) left-unit) ⟩
    (S0 ^ 3 • H0 • S0) • H0 ≈⟨ by-assoc Eq.refl ⟩
    (S0 ^ 3) • (H0 • S0) • H0 ≈⟨ cong refl lemma-H0S0H0' ⟩
    (S0 ^ 3) • (S0 ^ 3 • X0) • H0 • S0 ≈⟨ by-assoc Eq.refl ⟩
    (S0 ^ 3) • S0 ^ 3 • X0 • H0 • S0 ≈⟨ by-assoc Eq.refl ⟩
    S0 ^ 2 • S0 ^ 4 • X0 • H0 • S0 ≈⟨ cong refl (cong (axiom order-S0) refl) ⟩
    S0 ^ 2 • ε • X0 • H0 • S0 ≈⟨ cong refl left-unit ⟩
    S0 ^ 2 • X0 • H0 • S0 ≈⟨ by-assoc Eq.refl ⟩
    (S0 ^ 2 • X0) • H0 • S0 ∎

  lemma-H0X0 : H0 • X0 ≈ (S0 • S0) • H0
  lemma-H0X0 = begin
    H0 • H0 • S0 • S0 • H0 ≈⟨ by-assoc Eq.refl ⟩
    (H0 • H0) • S0 • S0 • H0 ≈⟨ trans (cong (axiom order-H0) refl) left-unit ⟩
    S0 • S0 • H0 ≈⟨ sym assoc ⟩
    (S0 • S0) • H0 ∎

  lemma-S0H0S0 : S0 • H0 • S0 ≈ H0 • S0 ^ 3 • H0
  lemma-S0H0S0 = begin
    S0 • H0 • S0 ≈⟨ cong refl lemma-H0S0 ⟩
    S0 • S0 ^ 3 • H0 • S0 ^ 3 • H0 ≈⟨ sym assoc ⟩
    S0 ^ 4 • H0 • S0 ^ 3 • H0 ≈⟨ cong (axiom order-S0) refl ⟩
    ε • H0 • S0 ^ 3 • H0 ≈⟨ left-unit ⟩
    H0 • S0 ^ 3 • H0 ∎

  
  lemma-X0S0 : X0 • S0 ≈ S0 • Z0 • X0
  lemma-X0S0 = begin
    X0 • S0 ≈⟨ by-assoc Eq.refl ⟩
    (H0 • S0) • (S0 • H0 • S0) ≈⟨ cong refl lemma-S0H0S0 ⟩
    (H0 • S0) • H0 • S0 ^ 3 • H0 ≈⟨ by-assoc Eq.refl ⟩
    (H0 • S0 • H0) • S0 ^ 3 • H0 ≈⟨ cong lemma-H0S0H0=S0H0S0 refl ⟩
    (S0 ^ 3 • H0 • S0 ^ 3) • S0 ^ 3 • H0 ≈⟨ by-assoc Eq.refl ⟩
    (S0 • Z0 • H0) • S0 ^ 4 • S0 ^ 2 • H0 ≈⟨ cong refl (cong (axiom order-S0) refl) ⟩
    (S0 • Z0 • H0) • ε • S0 ^ 2 • H0 ≈⟨ by-assoc Eq.refl ⟩
    S0 • Z0 • X0 ∎

  lemma-X0Z0 : X0 • Z0 ≈ Z0 • X0
  lemma-X0Z0 = begin
    X0 • Z0 ≈⟨ by-assoc Eq.refl ⟩
    (X0 • S0) • S0 ≈⟨ cong lemma-X0S0 refl ⟩
    (S0 • Z0 • X0) • S0 ≈⟨ trans (cong (sym assoc) refl) assoc ⟩
    (S0 • Z0) • X0 • S0 ≈⟨ cong refl lemma-X0S0 ⟩
    (S0 • Z0) • S0 • Z0 • X0 ≈⟨ by-assoc Eq.refl ⟩
    S0 ^ 4 • Z0 • X0 ≈⟨ cong (axiom order-S0) refl ⟩
    ε • Z0 • X0 ≈⟨ left-unit ⟩
    Z0 • X0 ∎

  lemma-X0S0^2 : (X0 • S0) ^ 2 ≈ ε
  lemma-X0S0^2 = begin
    (X0 • S0) ^ 2 ≈⟨ cong refl lemma-X0S0 ⟩
    (X0 • S0) • S0 • Z0 • X0 ≈⟨ by-assoc Eq.refl ⟩
    X0 • S0 ^ 4 • X0 ≈⟨ trans (cong refl (cong (axiom order-S0) refl)) (cong refl left-unit) ⟩
    X0 • X0 ≈⟨ lemma-X0X0 ⟩
    ε ∎

  lemma-X0S0H0^3 : ((X0 • S0) • H0) ^ 3 ≈ ε
  lemma-X0S0H0^3 = begin
    ((X0 • S0) • H0) • ((X0 • S0) • H0) • ((X0 • S0) • H0) ≈⟨ by-assoc Eq.refl ⟩
    (X0 • S0) • H0 ^ 2 • ((S0 ^ 2 • H0 • S0)) • H0 ^ 2 • ((S0 ^ 2 • H0 • S0) • H0) ≈⟨ cong refl (cong (axiom order-H0) (cong refl (cong (axiom order-H0) refl))) ⟩
    (X0 • S0) • ε • ((S0 ^ 2 • H0 • S0)) • ε • ((S0 ^ 2 • H0 • S0) • H0) ≈⟨ by-assoc Eq.refl ⟩
    X0 • (S0 ^ 3 • H0 • S0 ^ 3 • H0) • S0 • H0 ≈⟨ cong refl (cong (sym lemma-H0S0) refl) ⟩
    X0 • (H0 • S0) • S0 • H0 ≈⟨ by-assoc Eq.refl ⟩
    X0 • X0 ≈⟨ lemma-X0X0 ⟩
    ε ∎

  lemma-X0S0X0 : (X0 • S0) • X0 ≈ X0 • Z0 • X0 • S0
  lemma-X0S0X0 = begin
    (X0 • S0) • X0 ≈⟨ cong lemma-X0S0 refl ⟩
    (S0 • Z0 • X0) • X0 ≈⟨ trans (cong (sym assoc) refl) assoc ⟩
    (S0 • Z0) • X0 • X0 ≈⟨ cong refl lemma-X0X0 ⟩
    (S0 • Z0) • ε ≈⟨ by-assoc Eq.refl ⟩
    Z0 • ε • S0 ≈⟨ cong refl (cong (sym lemma-X0X0) refl) ⟩
    Z0 • X0 ^ 2 • S0 ≈⟨ by-assoc Eq.refl ⟩
    (Z0 • X0) • X0 • S0 ≈⟨ cong (sym lemma-X0Z0) refl ⟩
    (X0 • Z0) • X0 • S0 ≈⟨ assoc ⟩
    X0 • Z0 • X0 • S0 ∎

  lemma-Z0X0S0 : Z0 • X0 • S0 ≈ (X0 • S0) • Z0
  lemma-Z0X0S0 = begin
    Z0 • X0 • S0 ≈⟨ sym assoc ⟩
    (Z0 • X0) • S0 ≈⟨ cong (sym lemma-X0Z0) refl ⟩
    (X0 • Z0) • S0 ≈⟨ by-assoc Eq.refl ⟩
    (X0 • S0) • Z0 ∎

-}

