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
open import Data.Product.Relation.Binary.Pointwise.NonDependent using (≡×≡⇒≡ ; Pointwise ; ≡⇒≡×≡)
open import Data.Nat using (ℕ ; zero ; suc)
import Data.Nat as Nat
open import Data.Fin
open import Data.Fin.Induction
open import Data.Unit using (⊤ ; tt)
open import Data.Empty using (⊥ ; ⊥-elim)

open import Word.Base
open import Word.Properties
import Presentation.Base as PB
import Presentation.Properties as PP
open PP using (NFProperty ; NFProperty')
import Presentation.CosetNF as CA
open CA using (CosetNF-CT-Assumptions-And-Theorems-Packed)
import Presentation.Reidemeister-Schreier as RS
module RSF = RS.Star-Injective-Full.Reidemeister-Schreier-Full

open import Data.Sum hiding (swap)


open import Data.Fin.Properties using (suc-injective ; toℕ-inject₁ ; toℕ-fromℕ)
import Data.Nat.Properties as NP


import Presentation.Groups.Sn as Sn
import Presentation.Groups.Cyclic as Cyclic
open import Presentation.Construct.Base
open import Presentation.Construct.Properties.Amalgamation
import Presentation.Construct.Properties.DirectProduct as DP


module QutritCliffordT1 where

module M0 where
  Pζ : WRel Cyclic.X
  Pζ = Cyclic.rel 9

  ζ0 : Word Cyclic.X
  ζ0 = [ tt ]ʷ

  data Gen : Set where
    S-gen : Gen
    ζ-gen : Gen

  ζ : Word Gen
  ζ = [ ζ-gen ]ʷ

  S : Word Gen
  S = [ S-gen ]ʷ

  infix 4 _===_
  data _===_ : WRel Gen where
    order-ζ : ζ ^ 9 === ε
    order-S : S ^ 3 === ζ ^ 6
    comm : ∀ {gen} -> ζ • [ gen ]ʷ === [ gen ]ʷ • ζ

  data C : Set where
    ε-cr : C
    S-cr : C
    SS-cr : C

  open PB Pζ renaming (Alphabet to M0 ; _===_ to _===₀_ ; _≈_ to _≈₀_) using ()
  open NFProperty (Cyclic.nfp 9) using (by-equal-nf)

  open PB _===_ renaming (Alphabet to M) using (_≈_)

  open _≈_

  f : M0 -> Word M
  f tt = ζ

  h : C -> M -> Word M0 × C
  h ε-cr S-gen = ε , S-cr
  h ε-cr ζ-gen = ζ0 , ε-cr
  h S-cr S-gen = ε , SS-cr
  h S-cr ζ-gen = ζ0 , S-cr
  h SS-cr S-gen = ζ0 ^ 6 , ε-cr
  h SS-cr ζ-gen = ζ0 , SS-cr

  infix 4 _~_
  _~_ = Pointwise _≈₀_ (_≡_ {A = C})

  h=⁻¹f-gen : ∀ x -> ([ x ]ʷ , ε-cr) ~ ((h **) ε-cr (f x)) 
  h=⁻¹f-gen tt = _≈₀_.refl , Eq.refl

  h-wd-ax : ∀ c {u t} -> u === t -> (h **) c u ~ (h **) c t
  h-wd-ax ε-cr {u} {t} order-ζ = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax ε-cr {u} {t} order-S = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax ε-cr {u} {t} (comm {S-gen}) = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax ε-cr {u} {t} (comm {ζ-gen}) = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax S-cr {u} {t} order-ζ = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax S-cr {u} {t} order-S = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax S-cr {u} {t} (comm {S-gen}) = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax S-cr {u} {t} (comm {ζ-gen}) = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax SS-cr {u} {t} order-ζ = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax SS-cr {u} {t} order-S = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax SS-cr {u} {t} (comm {S-gen}) = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax SS-cr {u} {t} (comm {ζ-gen}) = by-equal-nf Eq.refl , Eq.refl

  open PP _===_

  f-wd-ax : ∀ {w v} -> w ===₀ v -> (f *) w ≈ (f *) v
  f-wd-ax {w} {v} Cyclic.order = _≈_.trans (by-assoc Eq.refl) (_≈_.axiom order-ζ) 

  [_] : C -> Word M
  [ SS-cr ] = S ^ 2
  [ S-cr ] = S
  [ ε-cr ] = ε

  lemma-ζ : ∀ w -> w • ζ ≈ ζ • w
  lemma-ζ [ x ]ʷ = sym (axiom comm)
  lemma-ζ ε = trans left-unit (sym right-unit)
  lemma-ζ (w • v) = trans assoc (trans (cong refl (lemma-ζ v)) (trans (sym assoc) (trans (cong (lemma-ζ w) refl) assoc)))

  lemma-ζ^n : ∀ n w -> w • ζ ^ n ≈ ζ ^ n • w
  lemma-ζ^n zero w = trans right-unit (sym left-unit)
  lemma-ζ^n (suc n@zero) w = begin
    w • ζ ^ suc n ≈⟨ sym right-unit ⟩
    (w • ζ) • ζ ^ n ≈⟨ cong (lemma-ζ w) refl ⟩
    (ζ • w) • ζ ^ n ≈⟨ assoc ⟩
    ζ • w • ζ ^ n ≈⟨ cong refl (lemma-ζ^n n w) ⟩
    ζ • ζ ^ n • w ≈⟨ cong refl left-unit ⟩
    ζ ^ suc n • w ∎
    where
    open SR word-setoid
  lemma-ζ^n (suc n@(suc n')) w = begin
    w • ζ ^ suc n ≈⟨ sym assoc ⟩
    (w • ζ) • ζ ^ n ≈⟨ cong (lemma-ζ w) refl ⟩
    (ζ • w) • ζ ^ n ≈⟨ assoc ⟩
    ζ • w • ζ ^ n ≈⟨ cong refl (lemma-ζ^n n w) ⟩
    ζ • ζ ^ n • w ≈⟨ sym assoc ⟩
    (ζ • ζ ^ n) • w ≈⟨ refl ⟩
    ζ ^ suc n • w ∎
    where
    open SR word-setoid


  h-hyp : ∀ c b -> [ c ] • [ b ]ʷ ≈ (f *) (h c b .proj₁) • [ h c b .proj₂ ]
  h-hyp ε-cr S-gen = refl
  h-hyp ε-cr ζ-gen = trans left-unit (sym right-unit)
  h-hyp S-cr S-gen = sym left-unit
  h-hyp S-cr ζ-gen = sym (axiom comm)
  h-hyp SS-cr S-gen = trans (trans assoc (axiom order-S)) (sym right-unit)
  h-hyp SS-cr ζ-gen = lemma-ζ^n 1 [ SS-cr ]

  module ca = CA.Data Pζ _===_ C ε-cr f h [_]
  module aat = ca.Assumptions-And-Theorems h=⁻¹f-gen h-wd-ax f-wd-ax _≈_.refl h-hyp
  open aat using (nfp ; nfp') public


module M where
  data Gen : Set where
    X-gen : Gen
    S-gen : Gen
    ζ-gen : Gen

  X : Word Gen
  X = [ X-gen ]ʷ

  S : Word Gen
  S = [ S-gen ]ʷ

  ζ : Word Gen
  ζ = [ ζ-gen ]ʷ

  Z : Word Gen
  Z = ζ ^ 3 • S ^ 2 • X ^ 2 • S • X

  infix 4 _===_
  data _===_ : WRel Gen where
    order-ζ : ζ ^ 9 === ε
    order-S : S ^ 3 === ζ ^ 6
    order-X : X ^ 3 === ε
    order-SX : (S • X) ^ 3 === ε
    comm-XS-SX : (X • S) • (S • X) === ζ ^ 6 • (S • X) • (X • S)
    comm : ∀ {gen} -> ζ • [ gen ]ʷ === [ gen ]ʷ • ζ

  data C : Set where
    ε-cr : C
    X-cr : C
    XX-cr : C
    XS-cr : C
    XXS-cr : C
    XSX-cr : C
    XXSX-cr : C
    XSXX-cr : C
    XXSXX-cr : C

  open PB (M0._===_) renaming (Alphabet to M0 ; _===_ to _===₀_ ; _≈_ to _≈₀_) using ()
  open NFProperty (M0.nfp (Cyclic.nfp 9)) using (by-equal-nf)
  open M0 renaming (S to S' ; ζ to ζ') using ()

  open PB _===_ renaming (Alphabet to M) using (_≈_)

  open _≈_

  f : M0 -> Word M
  f M0.S-gen = S
  f M0.ζ-gen = ζ

  h : C -> M -> Word M0 × C
  h ε-cr ζ-gen = ζ' , ε-cr
  h X-cr ζ-gen = ζ' , X-cr
  h XX-cr ζ-gen = ζ' , XX-cr
  h XS-cr ζ-gen = ζ' , XS-cr
  h XXS-cr ζ-gen = ζ' , XXS-cr
  h XSX-cr ζ-gen = ζ' , XSX-cr
  h XXSX-cr ζ-gen = ζ' , XXSX-cr
  h XSXX-cr ζ-gen = ζ' , XSXX-cr
  h XXSXX-cr ζ-gen = ζ' , XXSXX-cr
  h ε-cr S-gen = S' , ε-cr
  h X-cr S-gen = ε , XS-cr
  h XX-cr S-gen = ε , XXS-cr
  h XS-cr S-gen = S' • S' • S' • S' , XXSXX-cr
  h XXS-cr S-gen = S' • S' • S' • S' , XSX-cr
  h XSX-cr S-gen = S' • S' • S' • S' • S' • S' • S' • S' , XX-cr
  h XXSX-cr S-gen = S' , XXSX-cr
  h XSXX-cr S-gen = S' , XSXX-cr
  h XXSXX-cr S-gen = S' • S' • S' • S' • S' • S' • S' • S' , X-cr
  h ε-cr X-gen = ε , X-cr
  h X-cr X-gen = ε , XX-cr
  h XX-cr X-gen = ε , ε-cr
  h XS-cr X-gen = ε , XSX-cr
  h XXS-cr X-gen = ε , XXSX-cr
  h XSX-cr X-gen = ε , XSXX-cr
  h XXSX-cr X-gen = ε , XXSXX-cr
  h XSXX-cr X-gen = ε , XS-cr
  h XXSXX-cr X-gen = ε , XXS-cr

  infix 4 _~_
  _~_ = Pointwise _≈₀_ (_≡_ {A = C})

  h=⁻¹f-gen : ∀ x -> ([ x ]ʷ , ε-cr) ~ ((h **) ε-cr (f x)) 
  h=⁻¹f-gen M0.S-gen = _≈₀_.refl , Eq.refl
  h=⁻¹f-gen M0.ζ-gen = _≈₀_.refl , Eq.refl

  h-wd-ax : ∀ c {u t} -> u === t -> (h **) c u ~ (h **) c t
  h-wd-ax ε-cr {u} {t} order-ζ = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax ε-cr {u} {t} order-S = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax ε-cr {u} {t} order-X = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax ε-cr {u} {t} order-SX = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax X-cr {u} {t} order-ζ = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax X-cr {u} {t} order-S = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax X-cr {u} {t} order-X = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax X-cr {u} {t} order-SX = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax XX-cr {u} {t} order-ζ = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax XX-cr {u} {t} order-S = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax XX-cr {u} {t} order-X = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax XX-cr {u} {t} order-SX = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax XS-cr {u} {t} order-ζ = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax XS-cr {u} {t} order-S = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax XS-cr {u} {t} order-X = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax XS-cr {u} {t} order-SX = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax XXS-cr {u} {t} order-ζ = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax XXS-cr {u} {t} order-S = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax XXS-cr {u} {t} order-X = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax XXS-cr {u} {t} order-SX = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax XSX-cr {u} {t} order-ζ = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax XSX-cr {u} {t} order-S = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax XSX-cr {u} {t} order-X = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax XSX-cr {u} {t} order-SX = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax XXSX-cr {u} {t} order-ζ = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax XXSX-cr {u} {t} order-S = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax XXSX-cr {u} {t} order-X = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax XXSX-cr {u} {t} order-SX = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax XSXX-cr {u} {t} order-ζ = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax XSXX-cr {u} {t} order-S = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax XSXX-cr {u} {t} order-X = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax XSXX-cr {u} {t} order-SX = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax XXSXX-cr {u} {t} order-ζ = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax XXSXX-cr {u} {t} order-S = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax XXSXX-cr {u} {t} order-X = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax XXSXX-cr {u} {t} order-SX = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax ε-cr {u} {t} (comm {X-gen}) = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax ε-cr {u} {t} (comm {S-gen}) = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax ε-cr {u} {t} (comm {ζ-gen}) = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax X-cr {u} {t} (comm {X-gen}) = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax X-cr {u} {t} (comm {S-gen}) = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax X-cr {u} {t} (comm {ζ-gen}) = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax XX-cr {u} {t} (comm {X-gen}) = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax XX-cr {u} {t} (comm {S-gen}) = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax XX-cr {u} {t} (comm {ζ-gen}) = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax XS-cr {u} {t} (comm {X-gen}) = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax XS-cr {u} {t} (comm {S-gen}) = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax XS-cr {u} {t} (comm {ζ-gen}) = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax XSX-cr {u} {t} (comm {X-gen}) = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax XSX-cr {u} {t} (comm {S-gen}) = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax XSX-cr {u} {t} (comm {ζ-gen}) = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax XSXX-cr {u} {t} (comm {X-gen}) = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax XSXX-cr {u} {t} (comm {S-gen}) = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax XSXX-cr {u} {t} (comm {ζ-gen}) = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax XXSXX-cr {u} {t} (comm {X-gen}) = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax XXSXX-cr {u} {t} (comm {S-gen}) = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax XXSXX-cr {u} {t} (comm {ζ-gen}) = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax XXS-cr {u} {t} (comm {X-gen}) = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax XXS-cr {u} {t} (comm {S-gen}) = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax XXS-cr {u} {t} (comm {ζ-gen}) = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax XXSX-cr {u} {t} (comm {X-gen}) = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax XXSX-cr {u} {t} (comm {S-gen}) = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax XXSX-cr {u} {t} (comm {ζ-gen}) = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax ε-cr comm-XS-SX = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax X-cr comm-XS-SX = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax XX-cr comm-XS-SX = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax XS-cr comm-XS-SX = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax XXS-cr comm-XS-SX = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax XSX-cr comm-XS-SX = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax XXSX-cr comm-XS-SX = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax XSXX-cr comm-XS-SX = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax XXSXX-cr comm-XS-SX = by-equal-nf Eq.refl , Eq.refl
  open PP _===_

  f-wd-ax : ∀ {w v} -> w ===₀ v -> (f *) w ≈ (f *) v
  f-wd-ax {w} {v} M0.order-ζ = axiom order-ζ
  f-wd-ax {w} {v} M0.order-S = axiom order-S
  f-wd-ax {w} {v} (M0.comm {M0.S-gen}) = axiom comm
  f-wd-ax {w} {v} (M0.comm {M0.ζ-gen}) = refl

  [_] : C -> Word M
  [ ε-cr ] = ε
  [ X-cr ] = X
  [ XX-cr ] = X • X
  [ XS-cr ] = X • S
  [ XXS-cr ] = X • X • S
  [ XSX-cr ] = X • S • X
  [ XXSX-cr ] = X • X • S • X
  [ XSXX-cr ] = X • S • X • X
  [ XXSXX-cr ] = X • X • S • X • X

  lemma-ζ : ∀ w -> w • ζ ≈ ζ • w
  lemma-ζ [ x ]ʷ = sym (axiom comm)
  lemma-ζ ε = trans left-unit (sym right-unit)
  lemma-ζ (w • v) = trans assoc (trans (cong refl (lemma-ζ v)) (trans (sym assoc) (trans (cong (lemma-ζ w) refl) assoc)))

  lemma-ζ^n : ∀ n w -> w • ζ ^ n ≈ ζ ^ n • w
  lemma-ζ^n zero w = trans right-unit (sym left-unit)
  lemma-ζ^n (suc n@zero) w = begin
    w • ζ ^ suc n ≈⟨ sym right-unit ⟩
    (w • ζ) • ζ ^ n ≈⟨ cong (lemma-ζ w) refl ⟩
    (ζ • w) • ζ ^ n ≈⟨ assoc ⟩
    ζ • w • ζ ^ n ≈⟨ cong refl (lemma-ζ^n n w) ⟩
    ζ • ζ ^ n • w ≈⟨ cong refl left-unit ⟩
    ζ ^ suc n • w ∎
    where
    open SR word-setoid

  lemma-ζ^n (suc n@(suc n')) w = begin
    w • ζ ^ suc n ≈⟨ sym assoc ⟩
    (w • ζ) • ζ ^ n ≈⟨ cong (lemma-ζ w) refl ⟩
    (ζ • w) • ζ ^ n ≈⟨ assoc ⟩
    ζ • w • ζ ^ n ≈⟨ cong refl (lemma-ζ^n n w) ⟩
    ζ • ζ ^ n • w ≈⟨ sym assoc ⟩
    (ζ • ζ ^ n) • w ≈⟨ refl ⟩
    ζ ^ suc n • w ∎
    where
    open SR word-setoid

  lemma-XXSXXX : (X • X • S • X • X) • [ X-gen ]ʷ ≈ (f *) ε • X • X • S
  lemma-XXSXXX = begin
    (X • X • S • X • X) • [ X-gen ]ʷ ≈⟨ by-assoc Eq.refl ⟩
    (X • X • S) • X ^ 3 ≈⟨ cong refl (axiom order-X) ⟩
    (X • X • S) • ε ≈⟨ right-unit ⟩
    (X • X • S) ≈⟨ sym left-unit ⟩
    (f *) ε • X • X • S ∎
    where
    open SR word-setoid

  lemma-XSXXX : (X • S • X • X) • [ X-gen ]ʷ ≈ (f *) ε • X • S
  lemma-XSXXX = begin
    (X • S • X • X) • [ X-gen ]ʷ ≈⟨ by-assoc Eq.refl ⟩
    (X • S) • X ^ 3 ≈⟨ cong refl (axiom order-X) ⟩
    (X • S) • ε ≈⟨ right-unit ⟩
    (X • S) ≈⟨ sym left-unit ⟩
    (f *) ε • X • S ∎
    where
    open SR word-setoid

  open SR word-setoid

  lemma-S^9 : S ^ 9 ≈ ε
  lemma-S^9 = begin
    S ^ 9 ≈⟨ by-assoc Eq.refl ⟩
    (S ^ 3) ^ 3 ≈⟨ cong (axiom order-S) (cong (axiom order-S) (axiom order-S)) ⟩
    (ζ ^ 6) ^ 3 ≈⟨ by-assoc Eq.refl ⟩
    (ζ ^ 9) ^ 2 ≈⟨ trans (cong (axiom order-ζ) (axiom order-ζ)) right-unit ⟩
    ε ∎
  
  lemma-XSXS : (X • S • X) • S ≈ S ^ 8 • X ^ 2
  lemma-XSXS = begin
    (X • S • X) • S ≈⟨ trans (sym left-unit) (cong (sym lemma-S^9) refl) ⟩
    S ^ 9 • ((X • S • X) • S) ≈⟨ trans (sym right-unit) (sym (cong refl (axiom order-X)))  ⟩
    (S ^ 9 • ((X • S • X) • S)) • X ^ 3 ≈⟨ by-assoc Eq.refl ⟩
    S ^ 8 • ((S • X) ^ 3) • X ^ 2 ≈⟨ cong refl (cong (axiom order-SX) refl) ⟩
    S ^ 8 • ε • X ^ 2 ≈⟨ cong refl left-unit ⟩
    S ^ 8 • X ^ 2 ∎

  lemma-XSX : (X • S • X) ≈ S ^ 8 • X ^ 2 • S ^ 8
  lemma-XSX = begin
    (X • S • X) ≈⟨ trans (sym right-unit) (cong refl (sym lemma-S^9)) ⟩
    (X • S • X) • S ^ 9 ≈⟨ by-assoc Eq.refl ⟩
    ((X • S • X) • S) • S ^ 8 ≈⟨ cong lemma-XSXS refl ⟩
    (S ^ 8 • X ^ 2) • S ^ 8 ≈⟨ assoc ⟩
    S ^ 8 • X ^ 2 • S ^ 8 ∎

  lemma-XSX' : (X • S • X) ≈ ζ ^ 6 • S ^ 2 • X ^ 2 • S ^ 2
  lemma-XSX' = begin
    (X • S • X) ≈⟨ trans (sym right-unit) (cong refl (sym lemma-S^9)) ⟩
    (X • S • X) • S ^ 9 ≈⟨ by-assoc Eq.refl ⟩
    ((X • S • X) • S) • S ^ 8 ≈⟨ cong lemma-XSXS refl ⟩
    (S ^ 8 • X ^ 2) • S ^ 8 ≈⟨ by-assoc Eq.refl ⟩
    (S ^ 3) ^ 2 • (S ^ 2 • X ^ 2 • S ^ 2) • (S ^ 3) ^ 2 ≈⟨ cong (cong (axiom order-S) (axiom order-S)) refl ⟩
    (ζ ^ 6) ^ 2 • (S ^ 2 • X ^ 2 • S ^ 2) • (S ^ 3) ^ 2 ≈⟨ cong refl (cong refl (cong (axiom order-S) (axiom order-S))) ⟩
    (ζ ^ 6) ^ 2 • (S ^ 2 • X ^ 2 • S ^ 2) • (ζ ^ 6) ^ 2 ≈⟨ by-assoc Eq.refl ⟩
    (ζ ^ 6) ^ 2 • (S ^ 2 • X ^ 2 • S ^ 2) • (ζ ^ 12) ≈⟨ cong refl (lemma-ζ^n 12 (S ^ 2 • X ^ 2 • S ^ 2)) ⟩
    (ζ ^ 6) ^ 2 • ζ ^ 12 • (S ^ 2 • X ^ 2 • S ^ 2) ≈⟨ by-assoc Eq.refl ⟩
    (ζ ^ 9) ^ 2 • ζ ^ 6 • (S ^ 2 • X ^ 2 • S ^ 2) ≈⟨ cong (trans (cong (axiom order-ζ) (axiom order-ζ)) right-unit) refl ⟩
    ε • ζ ^ 6 • (S ^ 2 • X ^ 2 • S ^ 2) ≈⟨ left-unit ⟩
    ζ ^ 6 • S ^ 2 • X ^ 2 • S ^ 2 ∎

  lemma-SX^3S^8 : S • X ^ 3 • S ^ 8 ≈ ε
  lemma-SX^3S^8 = begin
    S • X ^ 3 • S ^ 8 ≈⟨ cong refl (cong (axiom order-X) refl) ⟩
    S • ε • S ^ 8 ≈⟨ by-assoc Eq.refl ⟩
    S ^ 9 ≈⟨ lemma-S^9 ⟩
    ε ∎

  lemma-S^8 : S ^ 8 ≈ ζ ^ 3 • S ^ 2
  lemma-S^8 = begin
    S ^ 8 ≈⟨ by-assoc Eq.refl ⟩
    (S ^ 3) ^ 2 • S ^ 2 ≈⟨ cong (cong (axiom order-S) (axiom order-S)) refl ⟩
    (ζ ^ 6) ^ 2 • S ^ 2 ≈⟨ by-assoc Eq.refl ⟩
    (ζ ^ 9) • ζ ^ 3 • S ^ 2 ≈⟨ trans (cong (axiom order-ζ) refl) left-unit ⟩
    ζ ^ 3 • S ^ 2 ∎

  lemma-S^4 : S ^ 4 ≈ ζ ^ 6 • S
  lemma-S^4 = begin
    S ^ 4 ≈⟨ by-assoc Eq.refl ⟩
    (S ^ 3) • S ≈⟨ cong ((axiom order-S)) refl ⟩
    (ζ ^ 6) • S ∎

  lemma-SXSX : S • X • S • X ≈ ζ ^ 3 • X ^ 2 • S ^ 2
  lemma-SXSX = begin
    S • X • S • X ≈⟨ trans (sym right-unit) (sym (cong refl lemma-SX^3S^8)) ⟩
    (S • X • S • X) • S • (X • X ^ 2) • S ^ 8 ≈⟨ by-assoc Eq.refl ⟩
    (S • X) ^ 3 • X ^ 2 • S ^ 8 ≈⟨ trans (cong (axiom order-SX) refl) left-unit ⟩
    X ^ 2 • S ^ 8 ≈⟨ cong refl lemma-S^8 ⟩
    X ^ 2 • ζ ^ 3 • S ^ 2 ≈⟨ sym assoc ⟩
    (X ^ 2 • ζ ^ 3) • S ^ 2 ≈⟨ cong (lemma-ζ^n 3 (X ^ 2)) refl ⟩
    (ζ ^ 3 • X ^ 2) • S ^ 2 ≈⟨ assoc ⟩
    ζ ^ 3 • X ^ 2 • S ^ 2 ∎

  lemma-XSS : (X • S) • [ S-gen ]ʷ ≈ (f *) (S' • S' • S' • S') • X • X • S • X • X
  lemma-XSS = begin
    (X • S) • S ≈⟨ refl ⟩
    (X • S) • S ≈⟨ trans (sym right-unit) (sym (cong refl (axiom order-X))) ⟩
    ((X • S) • S) • X ^ 3 ≈⟨ by-assoc Eq.refl ⟩
    ((X • S) • (S • X)) • X ^ 2 ≈⟨ cong (axiom comm-XS-SX) refl ⟩
    (ζ ^ 6 • (S • X) • (X • S)) • X ^ 2 ≈⟨ by-assoc Eq.refl ⟩
    (ζ ^ 6 • S) • X • X • S • X • X  ≈⟨ cong (sym (lemma-ζ^n 6 S)) refl ⟩
    (S • ζ ^ 6) • X • X • S • X • X  ≈⟨ cong (cong refl (sym (axiom order-S))) refl ⟩
    (S • S • S • S) • X • X • S • X • X ∎

  lemma-S^4XSX : S ^ 4 • X • S • X ≈ (X • X • S) • S
  lemma-S^4XSX = begin
    S ^ 4 • X • S • X ≈⟨ cong lemma-S^4 refl ⟩
    (ζ ^ 6 • S) • X • S • X ≈⟨ assoc ⟩
    ζ ^ 6 • S • X • S • X ≈⟨ cong refl lemma-SXSX ⟩
    ζ ^ 6 • ζ ^ 3 • X ^ 2 • S ^ 2 ≈⟨ by-assoc Eq.refl ⟩
    ζ ^ 9 • X ^ 2 • S ^ 2 ≈⟨ trans (cong (axiom order-ζ) refl) left-unit ⟩
    X ^ 2 • S ^ 2 ≈⟨ by-assoc Eq.refl ⟩
    (X • X • S) • S ∎

  lemma-XXSXXS : (X • X • S • X • X) • [ S-gen ]ʷ ≈ (f *) (S' • S' • S' • S' • S' • S' • S' • S') • X
  lemma-XXSXXS = begin
    (X • X • S • X • X) • [ S-gen ]ʷ ≈⟨ by-assoc Eq.refl ⟩
    X • X • (S • X • X • S) ≈⟨ cong refl (cong refl (trans (sym left-unit) (sym (cong (axiom order-ζ) refl)))) ⟩
    X • X • ζ ^ 9 • (S • X • X • S) ≈⟨ by-assoc Eq.refl ⟩
    X • X • ζ ^ 9 • ((S • X) • X • S) ≈⟨ by-assoc Eq.refl ⟩
    X • X • ζ ^ 3 • (ζ ^ 6 • (S • X) • X • S) ≈⟨ cong refl (cong refl (cong refl (sym (trans (sym assoc) (axiom comm-XS-SX))))) ⟩
    X • X • ζ ^ 3 • (X • S • S • X) ≈⟨ by-assoc Eq.refl ⟩
    ((X • X) • ζ ^ 3) • (X • S • S • X) ≈⟨ cong (lemma-ζ^n 3 (X • X)) refl  ⟩
    (ζ ^ 3 • X • X) • (X • S • S • X) ≈⟨ by-assoc Eq.refl ⟩
    ζ ^ 3 • (X • X • X) • S • S • X ≈⟨ cong refl (trans (cong (axiom order-X) refl) left-unit) ⟩
    ζ ^ 3 • S • S • X ≈⟨ by-assoc Eq.refl ⟩
    (ζ ^ 3 • S • S) • X ≈⟨ cong (sym lemma-S^8) refl ⟩
    S ^ 8 • X ≈⟨ refl ⟩
    (f *) (S' • S' • S' • S' • S' • S' • S' • S') • X ∎

  lemma-XSXXS : (X • S • X • X) • S ≈ S • X • S • X • X
  lemma-XSXXS = begin
    (X • S • X • X) • [ S-gen ]ʷ ≈⟨ by-assoc Eq.refl ⟩
    X • (S • X • X • S) ≈⟨ (cong refl (trans (sym left-unit) (sym (cong (axiom order-ζ) refl)))) ⟩
    X • ζ ^ 9 • (S • X • X • S) ≈⟨ by-assoc Eq.refl ⟩
    X • ζ ^ 9 • ((S • X) • X • S) ≈⟨ by-assoc Eq.refl ⟩
    X • ζ ^ 3 • (ζ ^ 6 • (S • X) • X • S) ≈⟨ (cong refl (cong refl (sym (trans (sym assoc) (axiom comm-XS-SX))))) ⟩
    X • ζ ^ 3 • (X • S • S • X) ≈⟨ sym assoc ⟩
    (X • ζ ^ 3) • (X • S • S • X) ≈⟨ cong (lemma-ζ^n 3 X) refl ⟩
    (ζ ^ 3 • X) • (X • S • S • X) ≈⟨ by-assoc Eq.refl ⟩
    (ζ ^ 3 • X ^ 2 • S ^ 2) • X ≈⟨ cong (sym lemma-SXSX) refl ⟩
    (S • X • S • X) • X ≈⟨ by-assoc Eq.refl ⟩
    S • X • S • X • X ∎

  lemma-XXSS : (X • X • S) • [ S-gen ]ʷ ≈ (f *) (S' • S' • S' • S') • X • S • X
  lemma-XXSS = begin
    (X • X • S) • [ S-gen ]ʷ ≈⟨ by-assoc Eq.refl ⟩
    X ^ 2 • S ^ 2 ≈⟨ trans (sym left-unit) (sym (cong (axiom order-ζ) refl)) ⟩ 
    ζ ^ 9 • X ^ 2 • S ^ 2 ≈⟨ by-assoc Eq.refl ⟩
    ζ ^ 6 • ζ ^ 3 • X ^ 2 • S ^ 2 ≈⟨ cong refl (sym lemma-SXSX) ⟩
    ζ ^ 6 • S • X • S • X ≈⟨ sym assoc ⟩
    (ζ ^ 6 • S) • X • S • X ≈⟨ cong (sym lemma-S^4) refl ⟩
    (f *) (S' • S' • S' • S') • X • S • X ∎

  lemma-XXSXS : (X • X • S • X) • [ S-gen ]ʷ ≈ (f *) S' • X • X • S • X
  lemma-XXSXS = begin
    (X • X • S • X) • [ S-gen ]ʷ ≈⟨ by-assoc Eq.refl ⟩
    X • (X • S • X) • S ≈⟨ cong refl lemma-XSXS ⟩
    X • S ^ 8 • X ^ 2 ≈⟨ cong refl (cong lemma-S^8 refl)  ⟩
    X • (ζ ^ 3 • S ^ 2) • X ^ 2 ≈⟨ by-assoc Eq.refl ⟩
    (X • ζ ^ 3) • S ^ 2 • X ^ 2 ≈⟨ cong (lemma-ζ^n 3 X) refl ⟩
    (ζ ^ 3 • X) • S ^ 2 • X ^ 2 ≈⟨ by-assoc Eq.refl ⟩
    ζ ^ 3 • ((X • S) • (S • X)) • X ≈⟨ cong refl (cong (axiom comm-XS-SX) refl) ⟩
    ζ ^ 3 • (ζ ^ 6 • (S • X) • (X • S)) • X ≈⟨ by-assoc Eq.refl ⟩
    (ζ ^ 9) • (S • X) • (X • S) • X ≈⟨ trans (cong (axiom order-ζ) refl) left-unit ⟩
    (S • X) • (X • S) • X ≈⟨ by-assoc Eq.refl ⟩
    (f *) S' • X • X • S • X ∎
  
  h-hyp : ∀ c b -> [ c ] • [ b ]ʷ ≈ (f *) (h c b .proj₁) • [ h c b .proj₂ ]
  h-hyp ε-cr X-gen = refl
  h-hyp ε-cr S-gen = trans left-unit (sym right-unit)
  h-hyp ε-cr ζ-gen = trans left-unit (sym right-unit)
  h-hyp X-cr X-gen = sym left-unit
  h-hyp X-cr S-gen = sym left-unit
  h-hyp X-cr ζ-gen = sym (axiom comm)
  h-hyp XX-cr X-gen = trans (trans assoc (axiom order-X)) (sym left-unit)
  h-hyp XX-cr S-gen = trans assoc (sym left-unit)
  h-hyp XX-cr ζ-gen = lemma-ζ [ XX-cr ]
  h-hyp XS-cr X-gen = trans assoc (sym left-unit)
  h-hyp XS-cr S-gen = lemma-XSS
  h-hyp XS-cr ζ-gen = lemma-ζ [ XS-cr ]
  h-hyp XXS-cr X-gen = by-assoc Eq.refl
  h-hyp XXS-cr S-gen = lemma-XXSS
  h-hyp XXS-cr ζ-gen = lemma-ζ [ XXS-cr ]
  h-hyp XSX-cr X-gen = by-assoc Eq.refl
  h-hyp XSX-cr S-gen = lemma-XSXS
  h-hyp XSX-cr ζ-gen = lemma-ζ [ XSX-cr ]
  h-hyp XXSX-cr X-gen = by-assoc Eq.refl
  h-hyp XXSX-cr S-gen = lemma-XXSXS
  h-hyp XXSX-cr ζ-gen = lemma-ζ [ XXSX-cr ]
  h-hyp XSXX-cr X-gen = lemma-XSXXX
  h-hyp XSXX-cr S-gen = lemma-XSXXS
  h-hyp XSXX-cr ζ-gen = lemma-ζ [ XSXX-cr ]
  h-hyp XXSXX-cr X-gen = lemma-XXSXXX
  h-hyp XXSXX-cr S-gen = lemma-XXSXXS
  h-hyp XXSXX-cr ζ-gen = lemma-ζ [ XXSXX-cr ]
  
  module ca = CA.Data M0._===_ _===_ C ε-cr f h [_]
  module aat = ca.Assumptions-And-Theorems h=⁻¹f-gen h-wd-ax f-wd-ax _≈_.refl h-hyp
  open aat using (nfp ; nfp') public

  module MM = PP.NFProperty (nfp (M0.nfp (Cyclic.nfp 9)))

  lemma-order-Z : Z ^ 3 ≈ ε
  lemma-order-Z = MM.by-equal-nf Eq.refl

module M2 where
  data Gen : Set where
    HH-gen : Gen
    X-gen : Gen
    S-gen : Gen
    ζ-gen : Gen

  X : Word Gen
  X = [ X-gen ]ʷ

  S : Word Gen
  S = [ S-gen ]ʷ

  ζ : Word Gen
  ζ = [ ζ-gen ]ʷ

  Z : Word Gen
  Z = ζ ^ 3 • S ^ 2 • X ^ 2 • S • X

  HH : Word Gen
  HH = [ HH-gen ]ʷ

  infix 4 _===_
  data _===_ : WRel Gen where
    order-ζ : ζ ^ 9 === ε
    order-S : S ^ 3 === ζ ^ 6
    order-X : X ^ 3 === ε
    order-HH : HH ^ 2 === ε
    comm-HH-X : HH • X === X ^ 2 • HH
    comm-HH-S : HH • S === (S • Z) • HH
    order-SX : (S • X) ^ 3 === ε
    comm-XS-SX : (X • S) • (S • X) === ζ ^ 6 • (S • X) • (X • S)
    comm : ∀ {gen} -> ζ • [ gen ]ʷ === [ gen ]ʷ • ζ

  data C : Set where
    ε-cr : C
    HH-cr : C

  open PB (M._===_) renaming (Alphabet to M ; _===_ to _===₀_ ; _≈_ to _≈₀_) using ()
  open NFProperty (M.nfp (M0.nfp (Cyclic.nfp 9))) using (by-equal-nf)
  open M renaming (S to S' ; ζ to ζ' ; X to X') using ()

  open PB _===_ renaming (Alphabet to M2) using (_≈_)

  open _≈_

  f : M.Gen -> Word M2
  f M.X-gen = X
  f M.S-gen = S
  f M.ζ-gen = ζ

  h : C -> Gen -> Word M × C
  h ε-cr ζ-gen = ζ' , ε-cr
  h HH-cr ζ-gen = ζ' , HH-cr
  h ε-cr S-gen = S' , ε-cr
  h HH-cr S-gen = X' • X' • S' • X' , HH-cr
  h ε-cr X-gen = X' , ε-cr
  h HH-cr X-gen = X' • X' , HH-cr
  h ε-cr HH-gen = ε , HH-cr
  h HH-cr HH-gen = ε , ε-cr

  infix 4 _~_
  _~_ = Pointwise _≈₀_ (_≡_ {A = C})

  h-wd-ax : ∀ c {u t} -> u === t -> (h **) c u ~ (h **) c t
  h-wd-ax ε-cr order-ζ = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax ε-cr order-S = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax ε-cr order-X = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax ε-cr order-HH = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax ε-cr order-SX = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax ε-cr comm-XS-SX = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax ε-cr (comm {HH-gen}) = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax ε-cr (comm {X-gen}) = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax ε-cr (comm {S-gen}) = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax ε-cr (comm {ζ-gen}) = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax HH-cr order-ζ = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax HH-cr order-S = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax HH-cr order-X = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax HH-cr order-HH = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax HH-cr order-SX = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax HH-cr comm-XS-SX = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax HH-cr (comm {HH-gen}) = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax HH-cr (comm {X-gen}) = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax HH-cr (comm {S-gen}) = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax HH-cr (comm {ζ-gen}) = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax ε-cr comm-HH-X = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax HH-cr comm-HH-X = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax ε-cr comm-HH-S = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax HH-cr comm-HH-S = by-equal-nf Eq.refl , Eq.refl
  
  open PP _===_

  f-wd-ax : ∀ {w v} -> w ===₀ v -> (f *) w ≈ (f *) v
  f-wd-ax {w} {v} M.order-ζ = axiom order-ζ
  f-wd-ax {w} {v} M.order-S = axiom order-S
  f-wd-ax {w} {v} M.order-X = axiom order-X
  f-wd-ax {w} {v} M.order-SX = axiom order-SX
  f-wd-ax {w} {v} M.comm-XS-SX = axiom comm-XS-SX
  f-wd-ax {w} {v} (M.comm {M.X-gen}) = axiom comm
  f-wd-ax {w} {v} (M.comm {M.S-gen}) = axiom comm
  f-wd-ax {w} {v} (M.comm {M.ζ-gen}) = refl

  by-sub-nf : ∀ {w v} -> w ≈₀ v -> (f *) w ≈ (f *) v
  by-sub-nf {w} {v} eq = RS.Star-Congruence.lemma-f*-cong M._===_ _===_ f f-wd-ax eq 

  [_] : C -> Word M2
  [ ε-cr ] = ε
  [ HH-cr ] = HH

  open SR word-setoid

  lemma-ζ : ∀ w -> w • ζ ≈ ζ • w
  lemma-ζ [ x ]ʷ = sym (axiom comm)
  lemma-ζ ε = trans left-unit (sym right-unit)
  lemma-ζ (w • v) = trans assoc (trans (cong refl (lemma-ζ v)) (trans (sym assoc) (trans (cong (lemma-ζ w) refl) assoc)))

  lemma-ζ^n : ∀ n w -> w • ζ ^ n ≈ ζ ^ n • w
  lemma-ζ^n zero w = trans right-unit (sym left-unit)
  lemma-ζ^n (suc n@zero) w = begin
    w • ζ ^ suc n ≈⟨ sym right-unit ⟩
    (w • ζ) • ζ ^ n ≈⟨ cong (lemma-ζ w) refl ⟩
    (ζ • w) • ζ ^ n ≈⟨ assoc ⟩
    ζ • w • ζ ^ n ≈⟨ cong refl (lemma-ζ^n n w) ⟩
    ζ • ζ ^ n • w ≈⟨ cong refl left-unit ⟩
    ζ ^ suc n • w ∎
  lemma-ζ^n (suc n@(suc n')) w = begin
    w • ζ ^ suc n ≈⟨ sym assoc ⟩
    (w • ζ) • ζ ^ n ≈⟨ cong (lemma-ζ w) refl ⟩
    (ζ • w) • ζ ^ n ≈⟨ assoc ⟩
    ζ • w • ζ ^ n ≈⟨ cong refl (lemma-ζ^n n w) ⟩
    ζ • ζ ^ n • w ≈⟨ sym assoc ⟩
    (ζ • ζ ^ n) • w ≈⟨ refl ⟩
    ζ ^ suc n • w ∎

  lemma-HHS : HH • [ S-gen ]ʷ ≈ (f *) (X' • X' • S' • X') • HH
  lemma-HHS = begin
    HH • [ S-gen ]ʷ ≈⟨ axiom comm-HH-S ⟩
    (S • Z) • HH ≈⟨ by-assoc Eq.refl ⟩
    (S • ζ ^ 3) • (S ^ 2 • X ^ 2 • S • X) • HH ≈⟨ cong (lemma-ζ^n 3 S) refl ⟩
    (ζ ^ 3 • S) • (S ^ 2 • X ^ 2 • S • X) • HH ≈⟨ by-assoc Eq.refl ⟩
    (ζ ^ 3) • S ^ 3 • (X ^ 2 • S • X) • HH ≈⟨ cong refl (cong (axiom order-S) refl)  ⟩
    (ζ ^ 3) • ζ ^ 6 • (X ^ 2 • S • X) • HH ≈⟨ by-assoc Eq.refl ⟩
    (ζ ^ 9) • (X ^ 2 • S • X) • HH ≈⟨ trans (cong (axiom order-ζ) refl) left-unit ⟩
    (X ^ 2 • S • X) • HH ≈⟨ by-assoc Eq.refl ⟩
    (f *) (X' • X' • S' • X') • HH ∎


  h-hyp : ∀ c b -> [ c ] • [ b ]ʷ ≈ (f *) (h c b .proj₁) • [ h c b .proj₂ ]
  h-hyp ε-cr HH-gen = refl
  h-hyp ε-cr X-gen = trans left-unit (sym right-unit)
  h-hyp ε-cr S-gen = trans left-unit (sym right-unit)
  h-hyp ε-cr ζ-gen = trans left-unit (sym right-unit)
  h-hyp HH-cr HH-gen = trans (axiom order-HH) (sym right-unit)
  h-hyp HH-cr X-gen = axiom comm-HH-X
  h-hyp HH-cr S-gen = lemma-HHS
  h-hyp HH-cr ζ-gen = sym (axiom comm)

  h=⁻¹f-gen : ∀ x -> ([ x ]ʷ , ε-cr) ~ ((h **) ε-cr (f x)) 
  h=⁻¹f-gen M.S-gen = _≈₀_.refl , Eq.refl
  h=⁻¹f-gen M.X-gen = _≈₀_.refl , Eq.refl
  h=⁻¹f-gen M.ζ-gen = _≈₀_.refl , Eq.refl

  module ca = CA.Data M._===_ _===_ C ε-cr f h [_]
  module aat = ca.Assumptions-And-Theorems h=⁻¹f-gen h-wd-ax f-wd-ax _≈_.refl h-hyp
  open aat using (nfp ; nfp') public

  module MM = PP.NFProperty (nfp (M.nfp (M0.nfp (Cyclic.nfp 9))))

  lemma-order-Z : Z ^ 3 ≈ ε
  lemma-order-Z = MM.by-equal-nf Eq.refl

-- Julien's normal form
module MA where
  data Gen : Set where
    T-gen : Gen
    HH-gen : Gen
    X-gen : Gen
    S-gen : Gen
    ζ-gen : Gen

  T : Word Gen
  T = [ T-gen ]ʷ

  X : Word Gen
  X = [ X-gen ]ʷ

  S : Word Gen
  S = [ S-gen ]ʷ

  HH : Word Gen
  HH = [ HH-gen ]ʷ

  ζ : Word Gen
  ζ = [ ζ-gen ]ʷ

  f : M2.Gen -> Word Gen
  f M2.HH-gen = HH
  f M2.X-gen = X
  f M2.S-gen = S
  f M2.ζ-gen = ζ

  Z : Word Gen
  Z = (f *) M2.Z

  infix 4 _===_
  data _===_ : WRel Gen where
    order-ζ : ζ ^ 9 === ε
    order-S : S ^ 3 === ζ ^ 6
    order-X : X ^ 3 === ε
    order-HH : HH ^ 2 === ε
    order-SX : (S • X) ^ 3 === ε
    comm-XS-SX : (X • S) • (S • X) === ζ ^ 6 • (S • X) • (X • S)
    comm-HH-X : HH • X === X ^ 2 • HH
    comm-HH-S : HH • S === (S • Z) • HH
    
    order-T : T ^ 3 === Z
    comm-TS : T • S === S • T
    comm-TX : T • X === ζ ^ 3 • S ^ 2 • X • T
    comm-THH : T • HH === Z • HH • T • T
    comm : ∀ {gen} -> ζ • [ gen ]ʷ === [ gen ]ʷ • ζ


  open PB (M2._===_) renaming (Alphabet to M ; _===_ to _===₀_ ; _≈_ to _≈₀_) using ()
  open NFProperty (M2.nfp (M.nfp (M0.nfp (Cyclic.nfp 9)) )) using (by-equal-nf)
  open PB _===_ renaming (Alphabet to MA) using (_≈_)
  open M2 renaming (ζ to ζ' ; S to S' ; X to X' ; Z to Z' ; HH to HH') using ()
  
  open _≈_


  data C : Set where
    T-cr : C
    THH-cr : C

  CT = C ⊎ ⊤
  
  ε-cr : CT
  ε-cr = inj₂ tt

  h : CT -> MA -> Word M × CT
  h (inj₂ tt) ζ-gen = ζ' , inj₂ tt
  h (inj₁ T-cr) ζ-gen = ζ' , inj₁ T-cr
  h (inj₁ THH-cr) ζ-gen = ζ' , inj₁ THH-cr
  h (inj₂ tt) S-gen = S' , inj₂ tt
  h (inj₁ T-cr) S-gen = S' , inj₁ T-cr
  h (inj₁ THH-cr) S-gen = X' • X' • S' • X' , inj₁ THH-cr
  h (inj₂ tt) X-gen = X' , inj₂ tt
  h (inj₁ T-cr) X-gen = ζ' ^ 3 • S' ^ 2 • X' , inj₁ T-cr
  h (inj₁ THH-cr) X-gen = X' • X' • S' , inj₁ THH-cr
  h (inj₂ tt) HH-gen = HH' , inj₂ tt
  h (inj₁ T-cr) HH-gen = ε , inj₁ THH-cr
  h (inj₁ THH-cr) HH-gen = ε , inj₁ T-cr
  h (inj₂ tt) T-gen = ε , inj₁ T-cr
  h (inj₁ T-cr) T-gen = Z' • HH' , inj₁ THH-cr
  h (inj₁ THH-cr) T-gen = HH' , inj₂ tt

  infix 4 _~_
  _~_ = Pointwise _≈₀_ (_≡_ {A = CT})

  h=⁻¹f-gen : ∀ x -> ([ x ]ʷ , (inj₂ tt)) ~ ((h **) (inj₂ tt) (f x)) 
  h=⁻¹f-gen M2.HH-gen = _≈₀_.refl , Eq.refl
  h=⁻¹f-gen M2.X-gen = _≈₀_.refl , Eq.refl
  h=⁻¹f-gen M2.S-gen = _≈₀_.refl , Eq.refl
  h=⁻¹f-gen M2.ζ-gen = _≈₀_.refl , Eq.refl

-- by-equal-nf Eq.refl , Eq.refl
  h-wd-ax : ∀ c {u t} -> u === t -> (h **) c u ~ (h **) c t
  h-wd-ax (inj₁ T-cr) order-ζ = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax (inj₁ T-cr) order-S = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax (inj₁ T-cr) order-X = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax (inj₁ T-cr) order-HH = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax (inj₁ T-cr) order-SX = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax (inj₁ T-cr) comm-XS-SX = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax (inj₁ T-cr) comm-HH-X = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax (inj₁ T-cr) comm-HH-S = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax (inj₁ T-cr) order-T = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax (inj₁ T-cr) comm-TS = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax (inj₁ T-cr) comm-TX = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax (inj₁ T-cr) comm-THH = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax (inj₁ T-cr) (comm {T-gen}) = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax (inj₁ T-cr) (comm {HH-gen}) = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax (inj₁ T-cr) (comm {X-gen}) = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax (inj₁ T-cr) (comm {S-gen}) = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax (inj₁ T-cr) (comm {ζ-gen}) = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax (inj₁ THH-cr) order-ζ = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax (inj₁ THH-cr) order-S = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax (inj₁ THH-cr) order-X = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax (inj₁ THH-cr) order-HH = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax (inj₁ THH-cr) order-SX = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax (inj₁ THH-cr) comm-XS-SX = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax (inj₁ THH-cr) comm-HH-X = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax (inj₁ THH-cr) comm-HH-S = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax (inj₁ THH-cr) order-T = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax (inj₁ THH-cr) comm-TS = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax (inj₁ THH-cr) comm-TX = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax (inj₁ THH-cr) comm-THH = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax (inj₁ THH-cr) (comm {T-gen}) = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax (inj₁ THH-cr) (comm {HH-gen}) = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax (inj₁ THH-cr) (comm {X-gen}) = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax (inj₁ THH-cr) (comm {S-gen}) = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax (inj₁ THH-cr) (comm {ζ-gen}) = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax (inj₂ tt) order-ζ = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax (inj₂ tt) order-S = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax (inj₂ tt) order-X = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax (inj₂ tt) order-HH = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax (inj₂ tt) order-SX = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax (inj₂ tt) comm-XS-SX = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax (inj₂ tt) comm-HH-X = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax (inj₂ tt) comm-HH-S = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax (inj₂ tt) order-T = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax (inj₂ tt) comm-TS = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax (inj₂ tt) comm-TX = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax (inj₂ tt) comm-THH = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax (inj₂ tt) (comm {T-gen}) = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax (inj₂ tt) (comm {HH-gen}) = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax (inj₂ tt) (comm {X-gen}) = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax (inj₂ tt) (comm {S-gen}) = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax (inj₂ tt) (comm {ζ-gen}) = by-equal-nf Eq.refl , Eq.refl


  open PP _===_

  f-wd-ax : ∀ {w v} -> w ===₀ v -> (f *) w ≈ (f *) v
  f-wd-ax {w} {v} M2.order-ζ = axiom order-ζ
  f-wd-ax {w} {v} M2.order-S = axiom order-S
  f-wd-ax {w} {v} M2.order-X = axiom order-X
  f-wd-ax {w} {v} M2.order-SX = axiom order-SX
  f-wd-ax {w} {v} M2.comm-XS-SX = axiom comm-XS-SX
  f-wd-ax {w} {v} (M2.comm {M2.X-gen}) = axiom comm
  f-wd-ax {w} {v} (M2.comm {M2.S-gen}) = axiom comm
  f-wd-ax {w} {v} (M2.comm {M2.ζ-gen}) = refl
  f-wd-ax M2.order-HH = axiom order-HH
  f-wd-ax M2.comm-HH-X = axiom comm-HH-X
  f-wd-ax M2.comm-HH-S = axiom comm-HH-S
  f-wd-ax (M2.comm {M2.HH-gen}) = axiom comm

  by-sub-nf : ∀ {w v} -> w ≈₀ v -> (f *) w ≈ (f *) v
  by-sub-nf {w} {v} eq = RS.Star-Congruence.lemma-f*-cong M2._===_ _===_ f f-wd-ax eq 

  lemma-order-Z : Z ^ 3 ≈ ε
  lemma-order-Z = RS.Star-Congruence.lemma-f*-cong M2._===_ _===_ f f-wd-ax M2.lemma-order-Z 

  lemma-ζ : ∀ w -> w • ζ ≈ ζ • w
  lemma-ζ [ x ]ʷ = sym (axiom comm)
  lemma-ζ ε = trans left-unit (sym right-unit)
  lemma-ζ (w • v) = trans assoc (trans (cong refl (lemma-ζ v)) (trans (sym assoc) (trans (cong (lemma-ζ w) refl) assoc)))

  lemma-ζ^n : ∀ n w -> w • ζ ^ n ≈ ζ ^ n • w
  lemma-ζ^n zero w = trans right-unit (sym left-unit)
  lemma-ζ^n (suc n@zero) w = begin
    w • ζ ^ suc n ≈⟨ sym right-unit ⟩
    (w • ζ) • ζ ^ n ≈⟨ cong (lemma-ζ w) refl ⟩
    (ζ • w) • ζ ^ n ≈⟨ assoc ⟩
    ζ • w • ζ ^ n ≈⟨ cong refl (lemma-ζ^n n w) ⟩
    ζ • ζ ^ n • w ≈⟨ cong refl left-unit ⟩
    ζ ^ suc n • w ∎
    where
    open SR word-setoid

  lemma-ζ^n (suc n@(suc n')) w = begin
    w • ζ ^ suc n ≈⟨ sym assoc ⟩
    (w • ζ) • ζ ^ n ≈⟨ cong (lemma-ζ w) refl ⟩
    (ζ • w) • ζ ^ n ≈⟨ assoc ⟩
    ζ • w • ζ ^ n ≈⟨ cong refl (lemma-ζ^n n w) ⟩
    ζ • ζ ^ n • w ≈⟨ sym assoc ⟩
    (ζ • ζ ^ n) • w ≈⟨ refl ⟩
    ζ ^ suc n • w ∎
    where
    open SR word-setoid

  open SR word-setoid

  lemma-order-T : T ^ 9 ≈ ε
  lemma-order-T = begin
    T ^ 9 ≈⟨ by-assoc Eq.refl ⟩
    (T ^ 3) ^ 3 ≈⟨ cong (axiom order-T) (cong (axiom order-T) (axiom order-T)) ⟩
    Z ^ 3 ≈⟨ lemma-order-Z ⟩
    ε ∎

  lemma-order-TX : (T • X) ^ 3 ≈ ε
  lemma-order-TX = begin
    (T • X) ^ 3 ≈⟨ cong (axiom comm-TX) (cong (axiom comm-TX) refl) ⟩
    (ζ ^ 3 • S ^ 2 • X • T) • (ζ ^ 3 • S ^ 2 • X • T) • T • X ≈⟨ by-assoc Eq.refl ⟩
    (ζ ^ 3 • S ^ 2 • X) • (T • ζ ^ 3) • (S ^ 2 • X • T) • T • X ≈⟨ cong refl (cong (lemma-ζ^n 3 T) refl) ⟩
    (ζ ^ 3 • S ^ 2 • X) • (ζ ^ 3 • T) • (S ^ 2 • X • T) • T • X ≈⟨ by-assoc Eq.refl ⟩
    (ζ ^ 3 • S ^ 2 • X • ζ ^ 3) • ((T • S) • S) • X • T • T • X ≈⟨ cong refl (cong (cong (axiom comm-TS) refl) refl) ⟩
    (ζ ^ 3 • S ^ 2 • X • ζ ^ 3) • ((S • T) • S) • X • T • T • X ≈⟨ by-assoc Eq.refl ⟩
    (ζ ^ 3 • S ^ 2 • X • ζ ^ 3) • (S • T • S) • X • T • T • X ≈⟨ cong refl (cong (cong refl (axiom comm-TS)) refl) ⟩
    (ζ ^ 3 • S ^ 2 • X • ζ ^ 3) • (S • S • T) • X • T • T • X ≈⟨ by-assoc Eq.refl ⟩
    (ζ ^ 3 • S ^ 2 • X • ζ ^ 3) • (S • S) • (T • X) • T • T • X ≈⟨ cong refl (cong refl (cong (axiom comm-TX) refl)) ⟩
    (ζ ^ 3 • S ^ 2 • X • ζ ^ 3) • (S • S) • (ζ ^ 3 • S ^ 2 • X • T) • T • T • X ≈⟨ by-assoc Eq.refl ⟩
    (ζ ^ 3 • S ^ 2 • X • ζ ^ 3 • S • S • ζ ^ 3 • S ^ 2 • X) • (T • T • T) • X ≈⟨ cong refl (cong (axiom order-T) refl) ⟩
    (ζ ^ 3 • S ^ 2 • X • ζ ^ 3 • S • S • ζ ^ 3 • S ^ 2 • X) • Z • X ≈⟨ by-sub-nf {(ζ' ^ 3 • S' ^ 2 • X' • ζ' ^ 3 • S' • S' • ζ' ^ 3 • S' ^ 2 • X') • Z' • X'} {ε} (M2.MM.by-equal-nf Eq.refl) ⟩
    ε ∎

  lemma-XT : (X • T) ^ 3 ≈ ε
  lemma-XT = begin
    (X • T) ^ 3 ≈⟨ trans (sym left-unit) (cong (sym (lemma-order-T) ) refl) ⟩
    T ^ 9 • (X • T) ^ 3 ≈⟨ by-assoc Eq.refl ⟩
    T ^ 8 • (T • X) ^ 3 • T ≈⟨ cong refl (cong (lemma-order-TX) refl) ⟩
    T ^ 8 • ε • T ≈⟨ by-assoc Eq.refl ⟩
    T ^ 9 ≈⟨ lemma-order-T ⟩
    ε ∎

{-
  lemma-SX : (S • X) ^ 2 ≈ ζ ^ 2
  lemma-SX = begin
    (S • X) ^ 2 ≈⟨ cong (sym (cong (axiom order-T) refl)) (sym (cong (axiom order-T) refl)) ⟩
    (T ^ 2 • X) ^ 2 ≈⟨ by-assoc Eq.refl ⟩
    T • T • X • T • T • X ≈⟨ cong refl (trans (sym left-unit) (cong (sym (axiom order-X)) refl)) ⟩
    T • (X • X) • T • X • T • T • X ≈⟨ by-assoc Eq.refl ⟩
    T • X • (X • T) ^ 2 • T • X ≈⟨ cong refl (cong refl (cong lemma-XT refl)) ⟩
    T • X • ζ • T • X ≈⟨ cong refl (cong refl (sym (lemma-ζ (T • X)))) ⟩
    T • X • (T • X) • ζ ≈⟨ by-assoc Eq.refl ⟩
    (T • X) ^ 2 • ζ ≈⟨ cong (axiom order-TX) refl ⟩
    ζ ^ 2 ∎
    where
    open SR word-setoid


  lemma-TX : T • X ≈ (X • ζ • S ^ 3) • T
  lemma-TX = begin
    T • X ≈⟨ trans (sym left-unit) (cong (sym (axiom order-X)) refl) ⟩
    (X ^ 2) • T • X ≈⟨ trans (sym right-unit) (sym (cong refl lemma-T^8)) ⟩
    ((X ^ 2) • T • X) • T ^ 8 ≈⟨ by-assoc Eq.refl ⟩
    X • (X • T) ^ 2  • T ^ 7 ≈⟨ cong refl (cong lemma-XT refl) ⟩
    X • ζ • T ^ 7 ≈⟨ by-assoc Eq.refl ⟩
    (X • ζ • T ^ 2 • T ^ 2 • T ^ 2) • T ≈⟨ cong (cong refl (cong refl (cong (axiom order-T) (cong (axiom order-T) (axiom order-T))))) refl ⟩
    (X • ζ • S ^ 3) • T ∎
    where
    open SR word-setoid

-}


  lemma-TTS : T ^ 2 • S ≈ S • T ^ 2
  lemma-TTS = begin
    T ^ 2 • S ≈⟨ assoc ⟩
    T • T • S ≈⟨ cong refl (axiom comm-TS) ⟩
    T • S • T ≈⟨ sym assoc ⟩
    (T • S) • T ≈⟨ cong (axiom comm-TS) refl ⟩
    (S • T) • T ≈⟨ assoc ⟩
    S • T ^ 2 ∎

  lemma-T-comm : T • ζ ^ 3 • S ^ 2 ≈ (ζ ^ 3 • S ^ 2) • T
  lemma-T-comm = begin
    T • ζ ^ 3 • S ^ 2 ≈⟨ sym assoc ⟩
    (T • ζ ^ 3) • S ^ 2 ≈⟨ cong (lemma-ζ^n 3 T) refl ⟩
    (ζ ^ 3 • T) • S ^ 2 ≈⟨ by-assoc Eq.refl ⟩
    ζ ^ 3 • (T • S) • S ≈⟨ cong refl (cong (axiom comm-TS) refl)  ⟩
    ζ ^ 3 • (S • T) • S ≈⟨ cong refl assoc ⟩
    ζ ^ 3 • S • T • S ≈⟨ cong refl (cong refl (axiom comm-TS)) ⟩
    ζ ^ 3 • S • S • T ≈⟨ by-assoc Eq.refl ⟩
    (ζ ^ 3 • S ^ 2) • T ∎

  lemma-TTX : T ^ 2 • X ≈ (ζ ^ 3 • S • X) • T ^ 2
  lemma-TTX = begin
    T ^ 2 • X ≈⟨ assoc ⟩
    T • T • X ≈⟨ cong refl (axiom comm-TX) ⟩
    T • ζ ^ 3 • S ^ 2 • X • T ≈⟨ by-assoc Eq.refl ⟩
    (T • ζ ^ 3 • S ^ 2) • X • T ≈⟨ cong lemma-T-comm refl  ⟩
    ((ζ ^ 3 • S ^ 2) • T) • X • T ≈⟨ by-assoc Eq.refl ⟩
    (ζ ^ 3 • S ^ 2) • (T • X) • T ≈⟨ cong refl (cong (axiom comm-TX) refl) ⟩
    (ζ ^ 3 • S ^ 2) • (ζ ^ 3 • S ^ 2 • X • T) • T ≈⟨ by-assoc Eq.refl ⟩
    (ζ ^ 3 • S ^ 2 • ζ ^ 3 • S ^ 2 • X) • T • T ≈⟨ cong (by-sub-nf {ζ' ^ 3 • S' ^ 2 • ζ' ^ 3 • S' ^ 2 • X'} {ζ' ^ 3 • S' • X'} (M2.MM.by-equal-nf Eq.refl)) refl ⟩
    (ζ ^ 3 • S • X) • T ^ 2 ∎


  [_]ₒ : C -> Word MA
  [ T-cr ]ₒ = T
  [ THH-cr ]ₒ = T • HH

  [_] : C ⊎ ⊤ -> Word MA
  [_] = [_,_] [_]ₒ (λ v → ε)

  lemma-TTHH : T ^ 2 • HH ≈ (Z • HH) • T
  lemma-TTHH = begin
    T ^ 2 • HH ≈⟨ assoc ⟩
    T • T • HH ≈⟨ cong refl (axiom comm-THH) ⟩
    T • Z • HH • T • T ≈⟨ by-assoc Eq.refl ⟩
    T • (Z • HH) • T • T ≈⟨ cong refl (cong (by-sub-nf {Z' • HH'} {HH' • Z' ^ 2} (M2.MM.by-equal-nf Eq.refl)) refl) ⟩
    T • (HH • Z ^ 2) • T • T ≈⟨ by-assoc Eq.refl ⟩
    (T • HH) • Z ^ 2 • T • T ≈⟨ cong (axiom comm-THH) refl ⟩
    (Z • HH • T • T) • Z ^ 2 • T • T ≈⟨ cong refl (cong (sym (cong (axiom order-T) (axiom order-T))) refl) ⟩
    (Z • HH • T • T) • (T ^ 3) ^ 2 • T • T ≈⟨ by-assoc Eq.refl ⟩
    (Z • HH) • T • T ^ 9 ≈⟨ sym assoc ⟩
    ((Z • HH) • T) • T ^ 9 ≈⟨ trans (cong refl lemma-order-T) right-unit ⟩
    (Z • HH) • T ∎

  lemma-TT : T ^ 2 ≈ (Z • HH) • T • HH
  lemma-TT = begin
    T ^ 2 ≈⟨ trans (sym right-unit) (sym (cong refl (axiom order-HH))) ⟩
    T ^ 2 • HH ^ 2 ≈⟨ sym assoc ⟩
    (T ^ 2 • HH) • HH ≈⟨ cong lemma-TTHH refl ⟩
    ((Z • HH) • T) • HH ≈⟨ assoc ⟩
    (Z • HH) • T • HH ∎

  lemma-TT' : HH ≈ (T • HH) • T
  lemma-TT' = begin
    HH ≈⟨ trans (sym left-unit) (cong (sym lemma-order-Z) refl) ⟩
    Z ^ 3 • HH ≈⟨ cong (cong (sym (axiom order-T)) (sym (cong (axiom order-T) (axiom order-T)))) refl ⟩
    (T ^ 3) ^ 3 • HH ≈⟨ by-assoc Eq.refl ⟩
    (T ^ 7) • T ^ 2 • HH ≈⟨ cong refl (cong lemma-TT refl) ⟩
    (T ^ 7) • ((Z • HH) • T • HH) • HH ≈⟨ by-assoc Eq.refl ⟩
     T • (T ^ 3) ^ 2 • Z • HH • T • HH • HH ≈⟨ cong refl (cong (cong (axiom order-T) (axiom order-T)) refl) ⟩
     T • Z ^ 2 • Z • HH • T • HH • HH ≈⟨ by-assoc Eq.refl ⟩
     (T • Z ^ 3 • HH • T) • HH • HH ≈⟨ cong (cong refl (cong lemma-order-Z refl)) (axiom order-HH) ⟩
     (T • ε • HH • T) • ε ≈⟨ by-assoc Eq.refl ⟩
    (T • HH) • T ∎

  lemma-THHX : [ inj₁ THH-cr ] • [ X-gen ]ʷ ≈ (f *) (X' • X' • S') • [ inj₁ THH-cr ]
  lemma-THHX = begin
    [ inj₁ THH-cr ] • [ X-gen ]ʷ ≈⟨ assoc ⟩
    T • HH • X ≈⟨ cong refl (trans (axiom comm-HH-X) assoc) ⟩
    T • X • X • HH ≈⟨ sym assoc ⟩
    (T • X) • X • HH ≈⟨ cong (axiom comm-TX) refl ⟩
    (ζ ^ 3 • S ^ 2 • X • T) • X • HH ≈⟨ by-assoc Eq.refl ⟩
    (ζ ^ 3 • S ^ 2 • X) • (T • X) • HH ≈⟨ cong refl (cong (axiom comm-TX) refl) ⟩
    (ζ ^ 3 • S ^ 2 • X) • (ζ ^ 3 • S ^ 2 • X • T) • HH ≈⟨ by-assoc Eq.refl ⟩
    ((ζ ^ 3 • S ^ 2 • X) • (ζ ^ 3 • S ^ 2 • X)) • T • HH ≈⟨ cong  (by-sub-nf {(ζ' ^ 3 • S' ^ 2 • X') • (ζ' ^ 3 • S' ^ 2 • X')} {(X' • X' • S')} (M2.MM.by-equal-nf Eq.refl)) refl ⟩
    (f *) (X' • X' • S') • [ inj₁ THH-cr ] ∎

  lemma-THHS : [ inj₁ THH-cr ] • [ S-gen ]ʷ ≈ (f *) (X' • X' • S' • X') • [ inj₁ THH-cr ]
  lemma-THHS = begin
    [ inj₁ THH-cr ] • [ S-gen ]ʷ ≈⟨ assoc ⟩
    T • HH • S ≈⟨ cong refl (axiom comm-HH-S) ⟩
    T • (S • Z) • HH ≈⟨ trans (cong refl assoc) (sym assoc) ⟩
    (T • S) • Z • HH ≈⟨ cong (axiom comm-TS) (sym (cong (axiom order-T) refl)) ⟩
    (S • T) • T ^ 3 • HH ≈⟨ by-assoc Eq.refl ⟩
    S • T ^ 3 • T • HH ≈⟨ cong refl (cong (axiom order-T) refl) ⟩
    S • Z • T • HH ≈⟨ sym assoc ⟩
    (S • Z) • T • HH ≈⟨ cong (by-sub-nf {S' • Z'} {X' • X' • S' • X'} (M2.MM.by-equal-nf Eq.refl)) refl ⟩
    (f *) (X' • X' • S' • X') • [ inj₁ THH-cr ] ∎

  h-hyp : ∀ c b -> [ c ] • [ b ]ʷ ≈ (f *) (h c b .proj₁) • [ h c b .proj₂ ]
  h-hyp (inj₁ T-cr) T-gen = lemma-TT
  h-hyp (inj₁ T-cr) HH-gen = sym left-unit
  h-hyp (inj₁ T-cr) X-gen = trans (axiom comm-TX) (sym (trans assoc (cong refl assoc)))
  h-hyp (inj₁ T-cr) S-gen = axiom comm-TS
  h-hyp (inj₁ T-cr) ζ-gen = sym (axiom comm)
  h-hyp (inj₁ THH-cr) T-gen = trans (sym lemma-TT') (sym right-unit)
  h-hyp (inj₁ THH-cr) HH-gen = trans assoc (trans (trans (cong refl (axiom order-HH)) right-unit) (sym left-unit))
  h-hyp (inj₁ THH-cr) X-gen = lemma-THHX
  h-hyp (inj₁ THH-cr) S-gen = lemma-THHS
  h-hyp (inj₁ THH-cr) ζ-gen = lemma-ζ^n 1 [ inj₁ THH-cr ]
  h-hyp (inj₂ tt) T-gen = refl
  h-hyp (inj₂ tt) HH-gen = trans left-unit (sym right-unit)
  h-hyp (inj₂ tt) X-gen = trans left-unit (sym right-unit)
  h-hyp (inj₂ tt) S-gen = trans left-unit (sym right-unit)
  h-hyp (inj₂ tt) ζ-gen = trans left-unit (sym right-unit)

  module ca = CA.Data (M2._===_) _===_ CT (inj₂ tt) f h [_]
  module aat = ca.Assumptions-And-Theorems h=⁻¹f-gen h-wd-ax f-wd-ax _≈_.refl h-hyp
  open aat using (nfp ; nfp') public
  
  open PP.NFProperty (nfp (M2.nfp (M.nfp (M0.nfp (Cyclic.nfp 9))))) renaming (by-equal-nf to by-nf) using ()

  I : CT
  I = inj₂ tt

  hcme : ∀ c m -> ∃ \ w -> ∃ \ c' -> ((h **) (inj₁ c) (f m)) ≡ (w , inj₁ c')
  hcme T-cr M2.HH-gen = ε , THH-cr , Eq.refl
  hcme T-cr M2.X-gen = ζ' ^ 3 • S' ^ 2 • X' , T-cr , Eq.refl
  hcme T-cr M2.S-gen = S' , T-cr , Eq.refl
  hcme T-cr M2.ζ-gen = ζ' , T-cr , Eq.refl
  hcme THH-cr M2.HH-gen = ε , T-cr , Eq.refl
  hcme THH-cr M2.X-gen = X' • X' • S' , THH-cr , Eq.refl
  hcme THH-cr M2.S-gen = X' • X' • S' • X' , THH-cr , Eq.refl
  hcme THH-cr M2.ζ-gen = ζ' , THH-cr , Eq.refl
  
  htme : ∀ m -> ((h **) (inj₂ tt) (f m)) ≡ ([ m ]ʷ , inj₂ tt)
  htme M2.X-gen = Eq.refl
  htme M2.S-gen = Eq.refl
  htme M2.ζ-gen = Eq.refl
  htme M2.HH-gen = Eq.refl
  
  htme~ : ∀ (m : M) -> ([ m ]ʷ , I) ~ ((h **) I (f m))
  htme~ M2.X-gen = _≈₀_.refl , Eq.refl
  htme~ M2.S-gen = _≈₀_.refl , Eq.refl
  htme~ M2.ζ-gen = _≈₀_.refl , Eq.refl
  htme~ M2.HH-gen = _≈₀_.refl , Eq.refl

  [_]ₓ = f *

  hcme~ : ∀ (c : C) (m : M) -> let (w' , c' , p) = hcme c m in ([ c ]ₒ • f m) ≈ ([ w' ]ₓ • [ c' ]ₒ)
  hcme~ T-cr M2.HH-gen = sym left-unit
  hcme~ T-cr M2.X-gen = by-nf Eq.refl
  hcme~ T-cr M2.S-gen = axiom comm-TS
  hcme~ T-cr M2.ζ-gen = sym (axiom comm)
  hcme~ THH-cr M2.HH-gen = by-nf Eq.refl
  hcme~ THH-cr M2.X-gen = by-nf Eq.refl
  hcme~ THH-cr M2.S-gen = by-nf Eq.refl
  hcme~ THH-cr M2.ζ-gen = by-nf Eq.refl
  

  ca' : CosetNF-CT-Assumptions-And-Theorems-Packed M2._===_ _===_
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


-- India normal form
module MA' where
  data Gen : Set where
    T-gen : Gen
    HH-gen : Gen
    X-gen : Gen
    S-gen : Gen
    ζ-gen : Gen

  T : Word Gen
  T = [ T-gen ]ʷ

  X : Word Gen
  X = [ X-gen ]ʷ

  S : Word Gen
  S = [ S-gen ]ʷ

  HH : Word Gen
  HH = [ HH-gen ]ʷ

  ζ : Word Gen
  ζ = [ ζ-gen ]ʷ

  f : M2.Gen -> Word Gen
  f M2.HH-gen = HH
  f M2.X-gen = X
  f M2.S-gen = S
  f M2.ζ-gen = ζ

  Z : Word Gen
  Z = (f *) M2.Z

  infix 4 _===_
  data _===_ : WRel Gen where
    order-ζ : ζ ^ 9 === ε
    order-S : S ^ 3 === ζ ^ 6
    order-X : X ^ 3 === ε
    order-HH : HH ^ 2 === ε
    order-SX : (S • X) ^ 3 === ε
    comm-XS-SX : (X • S) • (S • X) === ζ ^ 6 • (S • X) • (X • S)
    comm-HH-X : HH • X === X ^ 2 • HH
    comm-HH-S : HH • S === (S • Z) • HH
    
    order-T : T ^ 3 === Z
    comm-TS : T • S === S • T
    comm-TX : T • X === ζ ^ 3 • S ^ 2 • X • T
    comm-THH : T • HH === Z • HH • T • T
    comm : ∀ {gen} -> ζ • [ gen ]ʷ === [ gen ]ʷ • ζ


  open PB (M2._===_) renaming (Alphabet to M ; _===_ to _===₀_ ; _≈_ to _≈₀_) using ()
  open NFProperty (M2.nfp (M.nfp (M0.nfp (Cyclic.nfp 9)) )) using (by-equal-nf)
  open PB _===_ renaming (Alphabet to MA) using (_≈_)
  open M2 renaming (ζ to ζ' ; S to S' ; X to X' ; Z to Z' ; HH to HH') using ()
  
  open _≈_


  data C : Set where
    T-cr : C
    TT-cr : C

  CT = C ⊎ ⊤
  
  ε-cr : CT
  ε-cr = inj₂ tt

  h : CT -> MA -> Word M × CT
  h (inj₂ tt) ζ-gen = ζ' , ε-cr
  h (inj₁ T-cr) ζ-gen = ζ' , inj₁ T-cr
  h (inj₁ TT-cr) ζ-gen = ζ' , inj₁ TT-cr
  h (inj₂ tt) S-gen = S' , ε-cr
  h (inj₁ T-cr) S-gen = S' , inj₁ T-cr
  h (inj₁ TT-cr) S-gen = S' , inj₁ TT-cr
  h (inj₂ tt) X-gen = X' , ε-cr
  h (inj₁ T-cr) X-gen = ζ' ^ 3 • S' ^ 2 • X' , inj₁ T-cr
  h (inj₁ TT-cr) X-gen = ζ' ^ 3 • S' • X' , inj₁ TT-cr
  h (inj₂ tt) T-gen = ε , inj₁ T-cr
  h (inj₁ T-cr) T-gen = ε , inj₁ TT-cr
  h (inj₁ TT-cr) T-gen = Z' , ε-cr
  h (inj₂ tt) HH-gen = HH' , inj₂ tt
  h (inj₁ T-cr) HH-gen = Z' • HH' , inj₁ TT-cr
  h (inj₁ TT-cr) HH-gen = Z' • HH' , inj₁ T-cr

  infix 4 _~_
  _~_ = Pointwise _≈₀_ (_≡_ {A = CT})

  h=⁻¹f-gen : ∀ x -> ([ x ]ʷ , (inj₂ tt)) ~ ((h **) (inj₂ tt) (f x)) 
  h=⁻¹f-gen M2.HH-gen = _≈₀_.refl , Eq.refl
  h=⁻¹f-gen M2.X-gen = _≈₀_.refl , Eq.refl
  h=⁻¹f-gen M2.S-gen = _≈₀_.refl , Eq.refl
  h=⁻¹f-gen M2.ζ-gen = _≈₀_.refl , Eq.refl

  h-wd-ax : ∀ c {u t} -> u === t -> (h **) c u ~ (h **) c t
  h-wd-ax (inj₁ T-cr) order-ζ = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax (inj₁ T-cr) order-S = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax (inj₁ T-cr) order-X = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax (inj₁ T-cr) order-SX = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax (inj₁ T-cr) comm-XS-SX = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax (inj₁ T-cr) order-T = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax (inj₁ T-cr) comm-TS = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax (inj₁ T-cr) comm-TX = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax (inj₁ T-cr) (comm {T-gen}) = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax (inj₁ T-cr) (comm {X-gen}) = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax (inj₁ T-cr) (comm {S-gen}) = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax (inj₁ T-cr) (comm {ζ-gen}) = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax (inj₁ TT-cr) order-ζ = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax (inj₁ TT-cr) order-S = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax (inj₁ TT-cr) order-X = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax (inj₁ TT-cr) order-SX = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax (inj₁ TT-cr) comm-XS-SX = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax (inj₁ TT-cr) order-T = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax (inj₁ TT-cr) comm-TS = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax (inj₁ TT-cr) comm-TX = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax (inj₁ TT-cr) (comm {T-gen}) = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax (inj₁ TT-cr) (comm {X-gen}) = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax (inj₁ TT-cr) (comm {S-gen}) = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax (inj₁ TT-cr) (comm {ζ-gen}) = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax (inj₂ tt) order-ζ = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax (inj₂ tt) order-S = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax (inj₂ tt) order-X = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax (inj₂ tt) order-SX = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax (inj₂ tt) comm-XS-SX = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax (inj₂ tt) order-T = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax (inj₂ tt) comm-TS = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax (inj₂ tt) comm-TX = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax (inj₂ tt) (comm {T-gen}) = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax (inj₂ tt) (comm {X-gen}) = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax (inj₂ tt) (comm {S-gen}) = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax (inj₂ tt) (comm {ζ-gen}) = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax (inj₁ T-cr) (comm {HH-gen}) = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax (inj₁ TT-cr) (comm {HH-gen}) = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax (inj₂ tt) (comm {HH-gen}) = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax (inj₁ T-cr) order-HH = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax (inj₁ T-cr) comm-HH-X = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax (inj₁ T-cr) comm-HH-S = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax (inj₁ TT-cr) order-HH = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax (inj₁ TT-cr) comm-HH-X = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax (inj₁ TT-cr) comm-HH-S = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax (inj₂ tt) order-HH = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax (inj₂ tt) comm-HH-X = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax (inj₂ tt) comm-HH-S = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax (inj₁ T-cr) comm-THH = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax (inj₁ TT-cr) comm-THH = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax (inj₂ tt) comm-THH = by-equal-nf Eq.refl , Eq.refl

  open PP _===_

  f-wd-ax : ∀ {w v} -> w ===₀ v -> (f *) w ≈ (f *) v
  f-wd-ax {w} {v} M2.order-ζ = axiom order-ζ
  f-wd-ax {w} {v} M2.order-S = axiom order-S
  f-wd-ax {w} {v} M2.order-X = axiom order-X
  f-wd-ax {w} {v} M2.order-SX = axiom order-SX
  f-wd-ax {w} {v} M2.comm-XS-SX = axiom comm-XS-SX
  f-wd-ax {w} {v} (M2.comm {M2.X-gen}) = axiom comm
  f-wd-ax {w} {v} (M2.comm {M2.S-gen}) = axiom comm
  f-wd-ax {w} {v} (M2.comm {M2.ζ-gen}) = refl
  f-wd-ax M2.order-HH = axiom order-HH
  f-wd-ax M2.comm-HH-X = axiom comm-HH-X
  f-wd-ax M2.comm-HH-S = axiom comm-HH-S
  f-wd-ax (M2.comm {M2.HH-gen}) = axiom comm

  by-sub-nf : ∀ {w v} -> w ≈₀ v -> (f *) w ≈ (f *) v
  by-sub-nf {w} {v} eq = RS.Star-Congruence.lemma-f*-cong M2._===_ _===_ f f-wd-ax eq 

  lemma-order-Z : Z ^ 3 ≈ ε
  lemma-order-Z = RS.Star-Congruence.lemma-f*-cong M2._===_ _===_ f f-wd-ax M2.lemma-order-Z 

  lemma-ζ : ∀ w -> w • ζ ≈ ζ • w
  lemma-ζ [ x ]ʷ = sym (axiom comm)
  lemma-ζ ε = trans left-unit (sym right-unit)
  lemma-ζ (w • v) = trans assoc (trans (cong refl (lemma-ζ v)) (trans (sym assoc) (trans (cong (lemma-ζ w) refl) assoc)))

  lemma-ζ^n : ∀ n w -> w • ζ ^ n ≈ ζ ^ n • w
  lemma-ζ^n zero w = trans right-unit (sym left-unit)
  lemma-ζ^n (suc n@zero) w = begin
    w • ζ ^ suc n ≈⟨ sym right-unit ⟩
    (w • ζ) • ζ ^ n ≈⟨ cong (lemma-ζ w) refl ⟩
    (ζ • w) • ζ ^ n ≈⟨ assoc ⟩
    ζ • w • ζ ^ n ≈⟨ cong refl (lemma-ζ^n n w) ⟩
    ζ • ζ ^ n • w ≈⟨ cong refl left-unit ⟩
    ζ ^ suc n • w ∎
    where
    open SR word-setoid

  lemma-ζ^n (suc n@(suc n')) w = begin
    w • ζ ^ suc n ≈⟨ sym assoc ⟩
    (w • ζ) • ζ ^ n ≈⟨ cong (lemma-ζ w) refl ⟩
    (ζ • w) • ζ ^ n ≈⟨ assoc ⟩
    ζ • w • ζ ^ n ≈⟨ cong refl (lemma-ζ^n n w) ⟩
    ζ • ζ ^ n • w ≈⟨ sym assoc ⟩
    (ζ • ζ ^ n) • w ≈⟨ refl ⟩
    ζ ^ suc n • w ∎
    where
    open SR word-setoid

  open SR word-setoid

  lemma-order-T : T ^ 9 ≈ ε
  lemma-order-T = begin
    T ^ 9 ≈⟨ by-assoc Eq.refl ⟩
    (T ^ 3) ^ 3 ≈⟨ cong (axiom order-T) (cong (axiom order-T) (axiom order-T)) ⟩
    Z ^ 3 ≈⟨ lemma-order-Z ⟩
    ε ∎

  lemma-order-TX : (T • X) ^ 3 ≈ ε
  lemma-order-TX = begin
    (T • X) ^ 3 ≈⟨ cong (axiom comm-TX) (cong (axiom comm-TX) refl) ⟩
    (ζ ^ 3 • S ^ 2 • X • T) • (ζ ^ 3 • S ^ 2 • X • T) • T • X ≈⟨ by-assoc Eq.refl ⟩
    (ζ ^ 3 • S ^ 2 • X) • (T • ζ ^ 3) • (S ^ 2 • X • T) • T • X ≈⟨ cong refl (cong (lemma-ζ^n 3 T) refl) ⟩
    (ζ ^ 3 • S ^ 2 • X) • (ζ ^ 3 • T) • (S ^ 2 • X • T) • T • X ≈⟨ by-assoc Eq.refl ⟩
    (ζ ^ 3 • S ^ 2 • X • ζ ^ 3) • ((T • S) • S) • X • T • T • X ≈⟨ cong refl (cong (cong (axiom comm-TS) refl) refl) ⟩
    (ζ ^ 3 • S ^ 2 • X • ζ ^ 3) • ((S • T) • S) • X • T • T • X ≈⟨ by-assoc Eq.refl ⟩
    (ζ ^ 3 • S ^ 2 • X • ζ ^ 3) • (S • T • S) • X • T • T • X ≈⟨ cong refl (cong (cong refl (axiom comm-TS)) refl) ⟩
    (ζ ^ 3 • S ^ 2 • X • ζ ^ 3) • (S • S • T) • X • T • T • X ≈⟨ by-assoc Eq.refl ⟩
    (ζ ^ 3 • S ^ 2 • X • ζ ^ 3) • (S • S) • (T • X) • T • T • X ≈⟨ cong refl (cong refl (cong (axiom comm-TX) refl)) ⟩
    (ζ ^ 3 • S ^ 2 • X • ζ ^ 3) • (S • S) • (ζ ^ 3 • S ^ 2 • X • T) • T • T • X ≈⟨ by-assoc Eq.refl ⟩
    (ζ ^ 3 • S ^ 2 • X • ζ ^ 3 • S • S • ζ ^ 3 • S ^ 2 • X) • (T • T • T) • X ≈⟨ cong refl (cong (axiom order-T) refl) ⟩
    (ζ ^ 3 • S ^ 2 • X • ζ ^ 3 • S • S • ζ ^ 3 • S ^ 2 • X) • Z • X ≈⟨ by-sub-nf {(ζ' ^ 3 • S' ^ 2 • X' • ζ' ^ 3 • S' • S' • ζ' ^ 3 • S' ^ 2 • X') • Z' • X'} {ε} (M2.MM.by-equal-nf Eq.refl) ⟩
    ε ∎

  lemma-XT : (X • T) ^ 3 ≈ ε
  lemma-XT = begin
    (X • T) ^ 3 ≈⟨ trans (sym left-unit) (cong (sym (lemma-order-T) ) refl) ⟩
    T ^ 9 • (X • T) ^ 3 ≈⟨ by-assoc Eq.refl ⟩
    T ^ 8 • (T • X) ^ 3 • T ≈⟨ cong refl (cong (lemma-order-TX) refl) ⟩
    T ^ 8 • ε • T ≈⟨ by-assoc Eq.refl ⟩
    T ^ 9 ≈⟨ lemma-order-T ⟩
    ε ∎

{-
  lemma-SX : (S • X) ^ 2 ≈ ζ ^ 2
  lemma-SX = begin
    (S • X) ^ 2 ≈⟨ cong (sym (cong (axiom order-T) refl)) (sym (cong (axiom order-T) refl)) ⟩
    (T ^ 2 • X) ^ 2 ≈⟨ by-assoc Eq.refl ⟩
    T • T • X • T • T • X ≈⟨ cong refl (trans (sym left-unit) (cong (sym (axiom order-X)) refl)) ⟩
    T • (X • X) • T • X • T • T • X ≈⟨ by-assoc Eq.refl ⟩
    T • X • (X • T) ^ 2 • T • X ≈⟨ cong refl (cong refl (cong lemma-XT refl)) ⟩
    T • X • ζ • T • X ≈⟨ cong refl (cong refl (sym (lemma-ζ (T • X)))) ⟩
    T • X • (T • X) • ζ ≈⟨ by-assoc Eq.refl ⟩
    (T • X) ^ 2 • ζ ≈⟨ cong (axiom order-TX) refl ⟩
    ζ ^ 2 ∎
    where
    open SR word-setoid


  lemma-TX : T • X ≈ (X • ζ • S ^ 3) • T
  lemma-TX = begin
    T • X ≈⟨ trans (sym left-unit) (cong (sym (axiom order-X)) refl) ⟩
    (X ^ 2) • T • X ≈⟨ trans (sym right-unit) (sym (cong refl lemma-T^8)) ⟩
    ((X ^ 2) • T • X) • T ^ 8 ≈⟨ by-assoc Eq.refl ⟩
    X • (X • T) ^ 2  • T ^ 7 ≈⟨ cong refl (cong lemma-XT refl) ⟩
    X • ζ • T ^ 7 ≈⟨ by-assoc Eq.refl ⟩
    (X • ζ • T ^ 2 • T ^ 2 • T ^ 2) • T ≈⟨ cong (cong refl (cong refl (cong (axiom order-T) (cong (axiom order-T) (axiom order-T))))) refl ⟩
    (X • ζ • S ^ 3) • T ∎
    where
    open SR word-setoid

-}



  lemma-TTS : T ^ 2 • S ≈ S • T ^ 2
  lemma-TTS = begin
    T ^ 2 • S ≈⟨ assoc ⟩
    T • T • S ≈⟨ cong refl (axiom comm-TS) ⟩
    T • S • T ≈⟨ sym assoc ⟩
    (T • S) • T ≈⟨ cong (axiom comm-TS) refl ⟩
    (S • T) • T ≈⟨ assoc ⟩
    S • T ^ 2 ∎

  lemma-T-comm : T • ζ ^ 3 • S ^ 2 ≈ (ζ ^ 3 • S ^ 2) • T
  lemma-T-comm = begin
    T • ζ ^ 3 • S ^ 2 ≈⟨ sym assoc ⟩
    (T • ζ ^ 3) • S ^ 2 ≈⟨ cong (lemma-ζ^n 3 T) refl ⟩
    (ζ ^ 3 • T) • S ^ 2 ≈⟨ by-assoc Eq.refl ⟩
    ζ ^ 3 • (T • S) • S ≈⟨ cong refl (cong (axiom comm-TS) refl)  ⟩
    ζ ^ 3 • (S • T) • S ≈⟨ cong refl assoc ⟩
    ζ ^ 3 • S • T • S ≈⟨ cong refl (cong refl (axiom comm-TS)) ⟩
    ζ ^ 3 • S • S • T ≈⟨ by-assoc Eq.refl ⟩
    (ζ ^ 3 • S ^ 2) • T ∎

  lemma-TTX : T ^ 2 • X ≈ (ζ ^ 3 • S • X) • T ^ 2
  lemma-TTX = begin
    T ^ 2 • X ≈⟨ assoc ⟩
    T • T • X ≈⟨ cong refl (axiom comm-TX) ⟩
    T • ζ ^ 3 • S ^ 2 • X • T ≈⟨ by-assoc Eq.refl ⟩
    (T • ζ ^ 3 • S ^ 2) • X • T ≈⟨ cong lemma-T-comm refl  ⟩
    ((ζ ^ 3 • S ^ 2) • T) • X • T ≈⟨ by-assoc Eq.refl ⟩
    (ζ ^ 3 • S ^ 2) • (T • X) • T ≈⟨ cong refl (cong (axiom comm-TX) refl) ⟩
    (ζ ^ 3 • S ^ 2) • (ζ ^ 3 • S ^ 2 • X • T) • T ≈⟨ by-assoc Eq.refl ⟩
    (ζ ^ 3 • S ^ 2 • ζ ^ 3 • S ^ 2 • X) • T • T ≈⟨ cong (by-sub-nf {ζ' ^ 3 • S' ^ 2 • ζ' ^ 3 • S' ^ 2 • X'} {ζ' ^ 3 • S' • X'} (M2.MM.by-equal-nf Eq.refl)) refl ⟩
    (ζ ^ 3 • S • X) • T ^ 2 ∎



  [_]ₒ : C -> Word MA
  [ T-cr ]ₒ = T
  [ TT-cr ]ₒ = T ^ 2

  [_] : C ⊎ ⊤ -> Word MA
  [_] = [_,_] [_]ₒ (λ v → ε)

  lemma-TTHH : T ^ 2 • HH ≈ (Z • HH) • T
  lemma-TTHH = begin
    T ^ 2 • HH ≈⟨ assoc ⟩
    T • T • HH ≈⟨ cong refl (axiom comm-THH) ⟩
    T • Z • HH • T • T ≈⟨ by-assoc Eq.refl ⟩
    T • (Z • HH) • T • T ≈⟨ cong refl (cong (by-sub-nf {Z' • HH'} {HH' • Z' ^ 2} (M2.MM.by-equal-nf Eq.refl)) refl) ⟩
    T • (HH • Z ^ 2) • T • T ≈⟨ by-assoc Eq.refl ⟩
    (T • HH) • Z ^ 2 • T • T ≈⟨ cong (axiom comm-THH) refl ⟩
    (Z • HH • T • T) • Z ^ 2 • T • T ≈⟨ cong refl (cong (sym (cong (axiom order-T) (axiom order-T))) refl) ⟩
    (Z • HH • T • T) • (T ^ 3) ^ 2 • T • T ≈⟨ by-assoc Eq.refl ⟩
    (Z • HH) • T • T ^ 9 ≈⟨ sym assoc ⟩
    ((Z • HH) • T) • T ^ 9 ≈⟨ trans (cong refl lemma-order-T) right-unit ⟩
    (Z • HH) • T ∎

  h-hyp : ∀ c b -> [ c ] • [ b ]ʷ ≈ (f *) (h c b .proj₁) • [ h c b .proj₂ ]
  h-hyp (inj₁ T-cr) T-gen = sym left-unit
  h-hyp (inj₁ T-cr) X-gen = trans (axiom comm-TX) (sym (trans assoc (cong refl assoc)))
  h-hyp (inj₁ T-cr) S-gen = axiom comm-TS
  h-hyp (inj₁ T-cr) ζ-gen = sym (axiom comm)
  h-hyp (inj₁ TT-cr) T-gen = trans assoc (trans (axiom order-T) (sym right-unit))
  h-hyp (inj₁ TT-cr) X-gen = lemma-TTX
  h-hyp (inj₁ TT-cr) S-gen = lemma-TTS
  h-hyp (inj₁ TT-cr) ζ-gen = lemma-ζ^n 1 [ inj₁ TT-cr ]
  h-hyp (inj₂ tt) T-gen = refl
  h-hyp (inj₂ tt) X-gen = trans left-unit (sym right-unit)
  h-hyp (inj₂ tt) S-gen = trans left-unit (sym right-unit)
  h-hyp (inj₂ tt) ζ-gen = trans left-unit (sym right-unit)
  h-hyp (inj₁ T-cr) HH-gen = trans (axiom comm-THH) (sym assoc)
  h-hyp (inj₁ TT-cr) HH-gen = lemma-TTHH
  h-hyp (inj₂ tt) HH-gen = trans left-unit (sym right-unit)



  module ca = CA.Data (M2._===_) _===_ CT (inj₂ tt) f h [_]
  module aat = ca.Assumptions-And-Theorems h=⁻¹f-gen h-wd-ax f-wd-ax _≈_.refl h-hyp
  open aat using (nfp ; nfp') public
  
  open PP.NFProperty (nfp (M2.nfp (M.nfp (M0.nfp (Cyclic.nfp 9))))) renaming (by-equal-nf to by-nf) using ()

  I : CT
  I = inj₂ tt

  hcme : ∀ c m -> ∃ \ w -> ∃ \ c' -> ((h **) (inj₁ c) (f m)) ≡ (w , inj₁ c')
  hcme T-cr M2.X-gen = ζ' ^ 3 • S' ^ 2 • X' , T-cr , Eq.refl
  hcme T-cr M2.S-gen = S' , T-cr , Eq.refl
  hcme T-cr M2.ζ-gen = ζ' , T-cr , Eq.refl
  hcme TT-cr M2.X-gen = ζ' ^ 3 • S' • X' , TT-cr , Eq.refl
  hcme TT-cr M2.S-gen = S' , TT-cr , Eq.refl
  hcme TT-cr M2.ζ-gen = ζ' , TT-cr , Eq.refl
  hcme T-cr M2.HH-gen = Z' • HH' , TT-cr , Eq.refl
  hcme TT-cr M2.HH-gen = Z' • HH' , T-cr , Eq.refl
  
  htme : ∀ m -> ((h **) (inj₂ tt) (f m)) ≡ ([ m ]ʷ , inj₂ tt)
  htme M2.X-gen = Eq.refl
  htme M2.S-gen = Eq.refl
  htme M2.ζ-gen = Eq.refl
  htme M2.HH-gen = Eq.refl
  
  htme~ : ∀ (m : M) -> ([ m ]ʷ , I) ~ ((h **) I (f m))
  htme~ M2.X-gen = _≈₀_.refl , Eq.refl
  htme~ M2.S-gen = _≈₀_.refl , Eq.refl
  htme~ M2.ζ-gen = _≈₀_.refl , Eq.refl
  htme~ M2.HH-gen = _≈₀_.refl , Eq.refl
  
  [_]ₓ = f *

  hcme~ : ∀ (c : C) (m : M) -> let (w' , c' , p) = hcme c m in ([ c ]ₒ • f m) ≈ ([ w' ]ₓ • [ c' ]ₒ)
  hcme~ T-cr M2.X-gen = by-nf Eq.refl
  hcme~ T-cr M2.S-gen = by-nf Eq.refl
  hcme~ T-cr M2.ζ-gen = by-nf Eq.refl
  hcme~ TT-cr M2.X-gen = by-nf Eq.refl
  hcme~ TT-cr M2.S-gen = by-nf Eq.refl
  hcme~ TT-cr M2.ζ-gen = by-nf Eq.refl
  hcme~ T-cr M2.HH-gen = by-nf Eq.refl
  hcme~ TT-cr M2.HH-gen = by-nf Eq.refl
  
  ca' : CosetNF-CT-Assumptions-And-Theorems-Packed M2._===_ _===_
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
    H-gen : Gen
    HH-gen : Gen
    X-gen : Gen
    S-gen : Gen
    ζ-gen : Gen

  H : Word Gen
  H = [ H-gen ]ʷ

  HH : Word Gen
  HH = [ HH-gen ]ʷ

  S : Word Gen
  S = [ S-gen ]ʷ

  ζ : Word Gen
  ζ = [ ζ-gen ]ʷ

  X : Word Gen
  X = [ X-gen ]ʷ

  f : M2.Gen -> Word Gen
  f M2.HH-gen = HH
  f M2.X-gen = X
  f M2.S-gen = S
  f M2.ζ-gen = ζ

  Z : Word Gen
  Z = (f *) M2.Z

  infix 4 _===_
  data _===_ : WRel Gen where
    order-ζ : ζ ^ 9 === ε
    order-S : S ^ 3 === ζ ^ 6
    order-X : X ^ 3 === ε
    order-H : H ^ 4 === ε
    def-HH : HH === H • H
    order-SH : (S • H) ^ 3 === ε
    comm-HH-X : HH • X === X ^ 2 • HH
    comm-HH-S : HH • S === (S • Z) • HH
    HXH^3=Z : H • X • H ^ 3 === Z
    order-SX : (S • X) ^ 3 === ε
    comm-XS-SX : (X • S) • (S • X) === ζ ^ 6 • (S • X) • (X • S)
    comm : ∀ {gen} -> ζ • [ gen ]ʷ === [ gen ]ʷ • ζ

  open PB (M2._===_) renaming (Alphabet to M ; _===_ to _===₀_ ; _≈_ to _≈₀_) using ()
  open NFProperty (M2.nfp (M.nfp (M0.nfp (Cyclic.nfp 9)))) using (by-equal-nf)
  open PB _===_ renaming (Alphabet to MB) using (_≈_)
  open M2 renaming (ζ to ζ' ; S to S' ; X to X' ; Z to Z' ; HH to HH') using ()


  open _≈_

  data C : Set where
    HSS-cr : C
    HS-cr : C
    H-cr : C

  CT = C ⊎ ⊤

  I : CT
  I = inj₂ tt

  h : CT -> MB -> Word M × CT
  h (inj₂ tt) ζ-gen = ζ' , (inj₂ tt)
  h (inj₁ H-cr) ζ-gen = ζ' , (inj₁ H-cr)
  h (inj₁ HS-cr) ζ-gen = ζ' , (inj₁ HS-cr)
  h (inj₁ HSS-cr) ζ-gen = ζ' , (inj₁ HSS-cr)
  h (inj₂ tt) S-gen = S' , (inj₂ tt)
  h (inj₁ H-cr) S-gen = ε , (inj₁ HS-cr)
  h (inj₁ HS-cr) S-gen = ε , (inj₁ HSS-cr)
  h (inj₁ HSS-cr) S-gen = ζ' ^ 6 , (inj₁ H-cr)
  h (inj₂ tt) X-gen = X' , (inj₂ tt)
  h (inj₁ H-cr) X-gen = Z' , (inj₁ H-cr)
  h (inj₁ HS-cr) X-gen = ζ' ^ 3 • S' ^ 2 • X' • X' • S' , (inj₁ HS-cr)
  h (inj₁ HSS-cr) X-gen = Z' • X' , (inj₁ HSS-cr)
  h (inj₂ tt) H-gen = ε , (inj₁ H-cr)
  h (inj₁ H-cr) H-gen = HH' , (inj₂ tt)
  h (inj₁ HS-cr) H-gen = ζ' ^ 6 • S' • S' • HH' , (inj₁ HSS-cr)
  h (inj₁ HSS-cr) H-gen = ζ' ^ 6 • X' • X' • S' , (inj₁ HS-cr)
  h (inj₂ tt) HH-gen = HH' , (inj₂ tt)
  h (inj₁ H-cr) HH-gen = HH' , (inj₁ H-cr)
  h (inj₁ HS-cr) HH-gen = X' • HH' , (inj₁ HS-cr)
  h (inj₁ HSS-cr) HH-gen = X' • X' • HH' , (inj₁ HSS-cr)
  
  infix 4 _~_
  _~_ = Pointwise _≈₀_ (_≡_ {A = CT})

  h=⁻¹f-gen : ∀ x -> ([ x ]ʷ , I) ~ ((h **) I (f x)) 
  h=⁻¹f-gen M2.HH-gen = (by-equal-nf Eq.refl) , Eq.refl
  h=⁻¹f-gen M2.X-gen = (by-equal-nf Eq.refl) , Eq.refl
  h=⁻¹f-gen M2.S-gen = (by-equal-nf Eq.refl) , Eq.refl
  h=⁻¹f-gen M2.ζ-gen = (by-equal-nf Eq.refl) , Eq.refl

  h-wd-ax : ∀ c {u t} -> u === t -> (h **) c u ~ (h **) c t
  h-wd-ax (inj₁ HSS-cr) order-ζ = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax (inj₁ HSS-cr) order-S = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax (inj₁ HSS-cr) order-X = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax (inj₁ HSS-cr) order-H = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax (inj₁ HSS-cr) HXH^3=Z = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax (inj₁ HSS-cr) order-SX = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax (inj₁ HSS-cr) comm-XS-SX = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax (inj₁ HSS-cr) (comm {H-gen}) = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax (inj₁ HSS-cr) (comm {X-gen}) = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax (inj₁ HSS-cr) (comm {S-gen}) = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax (inj₁ HSS-cr) (comm {ζ-gen}) = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax (inj₁ HS-cr) order-ζ = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax (inj₁ HS-cr) order-S = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax (inj₁ HS-cr) order-X = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax (inj₁ HS-cr) order-H = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax (inj₁ HS-cr) HXH^3=Z = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax (inj₁ HS-cr) order-SX = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax (inj₁ HS-cr) comm-XS-SX = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax (inj₁ HS-cr) (comm {H-gen}) = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax (inj₁ HS-cr) (comm {X-gen}) = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax (inj₁ HS-cr) (comm {S-gen}) = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax (inj₁ HS-cr) (comm {ζ-gen}) = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax (inj₁ H-cr) order-ζ = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax (inj₁ H-cr) order-S = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax (inj₁ H-cr) order-X = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax (inj₁ H-cr) order-H = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax (inj₁ H-cr) HXH^3=Z = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax (inj₁ H-cr) order-SX = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax (inj₁ H-cr) comm-XS-SX = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax (inj₁ H-cr) (comm {H-gen}) = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax (inj₁ H-cr) (comm {X-gen}) = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax (inj₁ H-cr) (comm {S-gen}) = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax (inj₁ H-cr) (comm {ζ-gen}) = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax (inj₂ tt) order-ζ = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax (inj₂ tt) order-S = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax (inj₂ tt) order-X = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax (inj₂ tt) order-H = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax (inj₂ tt) HXH^3=Z = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax (inj₂ tt) order-SX = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax (inj₂ tt) comm-XS-SX = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax (inj₂ tt) (comm {H-gen}) = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax (inj₂ tt) (comm {X-gen}) = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax (inj₂ tt) (comm {S-gen}) = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax (inj₂ tt) (comm {ζ-gen}) = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax (inj₁ HSS-cr) comm-HH-X = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax (inj₁ HSS-cr) comm-HH-S = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax (inj₁ HS-cr) comm-HH-X = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax (inj₁ HS-cr) comm-HH-S = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax (inj₁ H-cr) comm-HH-X = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax (inj₁ H-cr) comm-HH-S = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax (inj₂ tt) comm-HH-X = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax (inj₂ tt) comm-HH-S = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax (inj₁ HSS-cr) order-SH = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax (inj₁ HS-cr) order-SH = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax (inj₁ H-cr) order-SH = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax (inj₂ tt) order-SH = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax (inj₁ HSS-cr) def-HH = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax (inj₁ HSS-cr) (comm {HH-gen}) = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax (inj₁ HS-cr) def-HH = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax (inj₁ HS-cr) (comm {HH-gen}) = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax (inj₁ H-cr) def-HH = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax (inj₁ H-cr) (comm {HH-gen}) = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax (inj₂ tt) def-HH = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax (inj₂ tt) (comm {HH-gen}) = by-equal-nf Eq.refl , Eq.refl

  open PP _===_
  open SR word-setoid
  
  lemma-ζ : ∀ w -> w • ζ ≈ ζ • w
  lemma-ζ [ x ]ʷ = sym (axiom comm)
  lemma-ζ ε = trans left-unit (sym right-unit)
  lemma-ζ (w • v) = trans assoc (trans (cong refl (lemma-ζ v)) (trans (sym assoc) (trans (cong (lemma-ζ w) refl) assoc)))

  lemma-ζ^n : ∀ n w -> w • ζ ^ n ≈ ζ ^ n • w
  lemma-ζ^n zero w = trans right-unit (sym left-unit)
  lemma-ζ^n (suc n@zero) w = begin
    w • ζ ^ suc n ≈⟨ sym right-unit ⟩
    (w • ζ) • ζ ^ n ≈⟨ cong (lemma-ζ w) refl ⟩
    (ζ • w) • ζ ^ n ≈⟨ assoc ⟩
    ζ • w • ζ ^ n ≈⟨ cong refl (lemma-ζ^n n w) ⟩
    ζ • ζ ^ n • w ≈⟨ cong refl left-unit ⟩
    ζ ^ suc n • w ∎
  lemma-ζ^n (suc n@(suc n')) w = begin
    w • ζ ^ suc n ≈⟨ sym assoc ⟩
    (w • ζ) • ζ ^ n ≈⟨ cong (lemma-ζ w) refl ⟩
    (ζ • w) • ζ ^ n ≈⟨ assoc ⟩
    ζ • w • ζ ^ n ≈⟨ cong refl (lemma-ζ^n n w) ⟩
    ζ • ζ ^ n • w ≈⟨ sym assoc ⟩
    (ζ • ζ ^ n) • w ≈⟨ refl ⟩
    ζ ^ suc n • w ∎

  lemma-order-HH : HH ^ 2 ≈ ε
  lemma-order-HH = begin
    HH ^ 2 ≈⟨ cong (axiom def-HH) (axiom def-HH) ⟩
    (H ^ 2) ^ 2 ≈⟨ assoc ⟩
    (H ^ 4) ≈⟨ axiom order-H ⟩
    ε ∎
  

  f-wd-ax : ∀ {w v} -> w ===₀ v -> (f *) w ≈ (f *) v
  f-wd-ax M2.order-ζ = axiom order-ζ
  f-wd-ax M2.order-S = axiom order-S
  f-wd-ax M2.order-X = axiom order-X
  f-wd-ax M2.order-HH = lemma-order-HH
  f-wd-ax M2.comm-HH-X = axiom comm-HH-X
  f-wd-ax M2.comm-HH-S = axiom comm-HH-S
  f-wd-ax M2.order-SX = axiom order-SX
  f-wd-ax M2.comm-XS-SX = axiom comm-XS-SX
  f-wd-ax (M2.comm {M2.HH-gen}) = sym (lemma-ζ (wconcat (wmap f [ M2.HH-gen ]ʷ)))
  f-wd-ax (M2.comm {M2.X-gen}) = axiom comm
  f-wd-ax (M2.comm {M2.S-gen}) = axiom comm
  f-wd-ax (M2.comm {M2.ζ-gen}) = refl

  by-sub-nf : ∀ {w v} -> w ≈₀ v -> (f *) w ≈ (f *) v
  by-sub-nf {w} {v} eq = RS.Star-Congruence.lemma-f*-cong M2._===_ _===_ f f-wd-ax eq 


  lemma-def-X : X ≈ H ^ 3 • Z • H
  lemma-def-X = begin
    X ≈⟨ trans (sym right-unit) (cong refl (sym (axiom order-H))) ⟩
    X • H ^ 4 ≈⟨ trans (sym left-unit) (sym (cong (axiom order-H) refl)) ⟩
    H ^ 4 • X • H ^ 4 ≈⟨ by-assoc Eq.refl ⟩
    H ^ 3 • (H • X • H ^ 3) • H ≈⟨ cong refl (cong (axiom HXH^3=Z) refl) ⟩
    H ^ 3 • Z • H ∎
    
  lemma-X^3 : X ^ 3 ≈ ε
  lemma-X^3 = begin
    X ^ 3 ≈⟨ cong lemma-def-X (cong lemma-def-X lemma-def-X) ⟩
    (H ^ 3 • Z • H) ^ 3 ≈⟨ by-assoc Eq.refl ⟩
    (H ^ 3 • Z) • (H ^ 4) • Z • (H ^ 4) • Z • H ≈⟨ cong refl (cong (axiom order-H) (cong refl (cong (axiom order-H) refl))) ⟩
    (H ^ 3 • Z) • ε • Z • ε • Z • H ≈⟨ by-assoc Eq.refl ⟩
    H ^ 3 • Z ^ 3 • H ≈⟨ cong refl (cong (by-sub-nf {Z' ^ 3} {ε} (M2.MM.by-equal-nf Eq.refl)) refl) ⟩
    H ^ 3 • ε • H ≈⟨ by-assoc Eq.refl ⟩
    H ^ 4 ≈⟨ axiom order-H ⟩
    ε ∎

  [_]ₒ : C -> Word MB
  [ HSS-cr ]ₒ = H • S • S
  [ HS-cr ]ₒ = H • S
  [ H-cr ]ₒ = H

  [_] : C ⊎ ⊤ -> Word MB
  [_] = [_,_] [_]ₒ (λ v → ε)

  lemma-HX : H • X ≈ Z • H
  lemma-HX = begin
    H • X ≈⟨ cong refl lemma-def-X ⟩
    H • H ^ 3 • Z • H ≈⟨ sym assoc ⟩
    H ^ 4 • Z • H ≈⟨ trans (cong (axiom order-H) refl) left-unit ⟩
    Z • H ∎

  lemma-HSSS : (H • S • S) • S ≈ ζ ^ 6 • H
  lemma-HSSS = begin
    (H • S • S) • S ≈⟨ trans assoc (cong refl assoc) ⟩
    H • S • S • S ≈⟨ cong refl (axiom order-S) ⟩
    H • ζ ^ 6 ≈⟨ lemma-ζ^n 6 H ⟩
    ζ ^ 6 • H ∎

  lemma-SHSHS : S • H • S • H • S ≈ H ^ 3
  lemma-SHSHS = begin
    S • H • S • H • S ≈⟨ trans (sym right-unit) (sym (cong refl (axiom order-H))) ⟩
    (S • H • S • H • S) • H ^ 4 ≈⟨ by-assoc Eq.refl ⟩
    (S • H) ^ 3 • H ^ 3 ≈⟨ trans (cong (axiom order-SH) refl) left-unit ⟩
    H ^ 3 ∎
  
  lemma-HSH : (H • S) • H ≈ (f *) ((ζ' ^ 6) • S' • S' • HH') • [ inj₁ HSS-cr ]
  lemma-HSH = begin
    (H • S) • H ≈⟨ cong refl (trans (sym right-unit) (cong refl (by-sub-nf {ε} {S' ^ 9} (M2.MM.by-equal-nf Eq.refl)))) ⟩
    (H • S) • H • S ^ 9 ≈⟨ assoc ⟩
    (H • S • H • S ^ 9) ≈⟨ trans (sym left-unit) (cong (by-sub-nf {ε} {S' ^ 9} (M2.MM.by-equal-nf Eq.refl)) refl) ⟩
    S ^ 9 • (H • S • H • S ^ 9) ≈⟨ by-assoc Eq.refl ⟩
    S ^ 8 • (S • H • S • H • S) • S ^ 8 ≈⟨ cong refl (cong lemma-SHSHS refl) ⟩
    S ^ 8 • (H ^ 3) • S ^ 8 ≈⟨ cong (by-sub-nf {S' ^ 8} {ζ' ^ 3 • S' ^ 2} (M2.MM.by-equal-nf Eq.refl)) (cong refl (by-sub-nf {S' ^ 8} {ζ' ^ 3 • S' ^ 2} (M2.MM.by-equal-nf Eq.refl))) ⟩
    (ζ ^ 3 • S ^ 2) • (H ^ 3) • (ζ ^ 3 • S ^ 2) ≈⟨ by-assoc Eq.refl ⟩
    (ζ ^ 3 • S ^ 2) • (H ^ 3 • ζ ^ 3) • S ^ 2 ≈⟨ cong refl (cong (lemma-ζ^n 3 (H ^ 3)) refl) ⟩
    (ζ ^ 3 • S ^ 2) • (ζ ^ 3 • H ^ 3) • S ^ 2 ≈⟨ by-assoc Eq.refl ⟩
    (ζ ^ 3 • S ^ 2 • ζ ^ 3) • H ^ 3 • S ^ 2 ≈⟨ cong (by-sub-nf {ζ' ^ 3 • S' ^ 2 • ζ' ^ 3} {ζ' ^ 6 • S' ^ 2} (M2.MM.by-equal-nf Eq.refl)) refl  ⟩
    (ζ ^ 6 • S ^ 2) • H ^ 3 • S ^ 2 ≈⟨ by-assoc Eq.refl ⟩
    (ζ ^ 6 • S ^ 2) • H ^ 2 • H • S ^ 2 ≈⟨ cong refl (cong (sym (axiom def-HH)) refl)  ⟩
    (ζ ^ 6 • S ^ 2) • HH • H • S ^ 2 ≈⟨ by-assoc Eq.refl ⟩
    (f *) ((ζ' ^ 6) • S' • S' • HH') • [ inj₁ HSS-cr ] ∎

  lemma-HSHS : H • S • H • S ≈ S ^ 8 • H ^ 3
  lemma-HSHS = begin
    H • S • H • S ≈⟨ trans (sym left-unit) (cong (by-sub-nf {ε} {S' ^ 9} (M2.MM.by-equal-nf Eq.refl)) refl) ⟩
    S ^ 9 • H • S • H • S ≈⟨ by-assoc Eq.refl ⟩
    S ^ 8 • S • H • S • H • S ≈⟨ cong refl lemma-SHSHS ⟩
    S ^ 8 • H ^ 3 ∎
  

  lemma-HSSH : [ inj₁ HSS-cr ] • [ H-gen ]ʷ ≈ (f *) ((ζ' ^ 6) • X' • X' • S') • [ inj₁ HS-cr ]
  lemma-HSSH = begin
    [ inj₁ HSS-cr ] • [ H-gen ]ʷ ≈⟨ assoc ⟩
    H • (S • S) • H ≈⟨ cong refl (cong (by-sub-nf {S' • S'} {ζ' ^ 6 • HH' • Z' • Z' • S' ^ 8 • HH'} (M2.MM.by-equal-nf Eq.refl)) refl) ⟩
    H • (ζ ^ 6 • HH • Z • Z • S ^ 8 • HH) • H ≈⟨ by-assoc Eq.refl ⟩
    H • (ζ ^ 6 • HH • Z • Z • S ^ 8) • HH • H ≈⟨ cong refl (cong refl (cong (axiom def-HH) refl)) ⟩
    H • (ζ ^ 6 • HH • Z • Z • S ^ 8) • H ^ 2 • H ≈⟨ by-assoc Eq.refl ⟩
    H • (ζ ^ 6 • HH • Z • Z) • (S ^ 8 • H ^ 3) ≈⟨ cong refl (cong refl (sym lemma-HSHS)) ⟩
    H • (ζ ^ 6 • HH • Z • Z) • (H • S • H • S) ≈⟨ by-assoc Eq.refl ⟩
    (H • ζ ^ 6) • (HH • Z) • ε • Z • (H • S • H • S) ≈⟨ cong (lemma-ζ^n 6 H) (cong refl (sym (cong (axiom order-H) refl))) ⟩
    (ζ ^ 6 • H) • (HH • Z) • H ^ 4 • Z • (H • S • H • S) ≈⟨ cong refl (cong (cong (axiom def-HH) refl) refl) ⟩
    (ζ ^ 6 • H) • (H ^ 2 • Z) • H ^ 4 • Z • (H • S • H • S) ≈⟨ by-assoc Eq.refl ⟩
    ζ ^ 6 • (H ^ 3 • Z • H) • (H ^ 3 • Z • H) • S • H • S ≈⟨ cong refl (cong (sym lemma-def-X) (cong (sym lemma-def-X) refl)) ⟩
    ζ ^ 6 • X • X • S • H • S ≈⟨ by-assoc Eq.refl ⟩
    (f *) ((ζ' ^ 6) • X' • X' • S') • [ inj₁ HS-cr ] ∎


  lemma-HSSX : [ inj₁ HSS-cr ] • [ X-gen ]ʷ ≈ (f *) (Z' • X') • [ inj₁ HSS-cr ]
  lemma-HSSX = begin
    [ inj₁ HSS-cr ] • [ X-gen ]ʷ ≈⟨ trans assoc (cong refl assoc) ⟩
    H • S • S • X ≈⟨ cong refl (by-sub-nf {S' • S' • X'} { X' • HH' • Z' • HH' • S' • S'} (M2.MM.by-equal-nf Eq.refl)) ⟩
    H • X • HH • Z • HH • S • S ≈⟨ by-assoc Eq.refl ⟩
    (H • X • HH • Z) • HH • S • S ≈⟨ cong refl (cong (axiom def-HH) refl) ⟩
    (H • X • HH • Z) • H ^ 2 • S • S ≈⟨ by-assoc Eq.refl ⟩
    (H • X) • HH • Z • H • H • S • S ≈⟨ cong lemma-HX refl ⟩
    (Z • H) • HH • Z • H • H • S • S ≈⟨ cong refl (cong (axiom def-HH) refl) ⟩
    (Z • H) • H ^ 2 • Z • H • H • S • S ≈⟨ by-assoc Eq.refl ⟩
    (Z • H ^ 3) • Z • H • H • S • S ≈⟨ by-assoc Eq.refl ⟩
    Z • (H ^ 3 • Z • H) • H • S • S ≈⟨ cong refl (cong (sym lemma-def-X) refl) ⟩
    Z • X • H • S • S ≈⟨ sym assoc ⟩
    (f *) (Z' • X') • [ inj₁ HSS-cr ] ∎

  lemma-HHHX : H ^ 3 • X ≈ H ^ 2 • Z • H
  lemma-HHHX = begin
    H ^ 3 • X ≈⟨ trans (cong (sym assoc) refl) assoc ⟩
    H ^ 2 • H • X ≈⟨ cong refl lemma-HX ⟩
    H ^ 2 • Z • H ∎

  lemma-HXSHSX : H • X • S • H • S • X ≈ H • S • H • S
  lemma-HXSHSX = begin
    H • X • S • H • S • X ≈⟨ sym assoc ⟩
    (H • X) • S • H • S • X ≈⟨ cong lemma-HX refl ⟩
    (Z • H) • S • H • S • X ≈⟨ by-assoc Eq.refl ⟩
    Z • (H • S • H • S) • X ≈⟨ cong refl (cong lemma-HSHS refl) ⟩
    Z • (S ^ 8 • H ^ 3) • X ≈⟨ by-assoc Eq.refl ⟩
    Z • S ^ 8 • (H ^ 3 • X) ≈⟨ cong refl (cong refl lemma-HHHX) ⟩
    Z • S ^ 8 • (H ^ 2 • Z • H) ≈⟨ cong refl (cong refl (cong (sym (axiom def-HH)) refl)) ⟩
    Z • S ^ 8 • (HH • Z • H) ≈⟨ by-assoc Eq.refl ⟩
    (Z • S ^ 8 • HH • Z) • H ≈⟨ cong (by-sub-nf {Z' • S' ^ 8 • HH' • Z'} {S' ^ 8 • HH'} (M2.MM.by-equal-nf Eq.refl)) refl  ⟩
    (S ^ 8 • HH) • H ≈⟨ cong (cong refl (axiom def-HH)) refl  ⟩
    (S ^ 8 • H ^ 2) • H ≈⟨ by-assoc Eq.refl ⟩
    S ^ 8 • H ^ 3 ≈⟨ sym lemma-HSHS ⟩
    H • S • H • S ∎


  lemma-XSHSX : X • S • H • S • X ≈ S • H • S
  lemma-XSHSX = begin
    X • S • H • S • X ≈⟨ trans (sym left-unit) (sym (cong (axiom order-H) refl)) ⟩
    H ^ 4 • X • S • H • S • X ≈⟨ by-assoc Eq.refl ⟩
    H ^ 3 • H • X • S • H • S • X ≈⟨ cong refl lemma-HXSHSX ⟩
    H ^ 3 • H • S • H • S ≈⟨ by-assoc Eq.refl ⟩
    H ^ 4 • S • H • S ≈⟨ trans (cong (axiom order-H) refl) left-unit ⟩
    S • H • S ∎


  lemma-HSX : [ inj₁ HS-cr ] • [ X-gen ]ʷ ≈ (f *) ((ζ' • ζ' • ζ') • (S' • S') • X' • X' • S') • [ inj₁ HS-cr ]
  lemma-HSX = begin
    [ inj₁ HS-cr ] • [ X-gen ]ʷ ≈⟨ assoc ⟩
    H • S • X ≈⟨ trans (sym left-unit) ((cong (by-sub-nf {ε} {S' ^ 9} (M2.MM.by-equal-nf Eq.refl)) refl)) ⟩
    S ^ 9 • H • S • X ≈⟨ by-assoc Eq.refl ⟩
    S ^ 8 • S • H • S • X ≈⟨ cong refl (trans (sym left-unit) ((cong (by-sub-nf {ε} {X' ^ 3} (M2.MM.by-equal-nf Eq.refl)) refl))) ⟩
    S ^ 8 • X ^ 3 • S • H • S • X ≈⟨ by-assoc Eq.refl ⟩
    S ^ 8 • X ^ 2 • X • S • H • S • X ≈⟨ cong refl (cong refl lemma-XSHSX) ⟩
    S ^ 8 • X ^ 2 • S • H • S ≈⟨ by-assoc Eq.refl ⟩
    (S ^ 8 • X ^ 2 • S) • H • S ≈⟨ cong (by-sub-nf {S' ^ 8 • X' ^ 2 • S'} {ζ' ^ 3 • S' ^ 2 • X' • X' • S'} (M2.MM.by-equal-nf Eq.refl)) refl ⟩
    (ζ ^ 3 • S ^ 2 • X • X • S) • H • S ≈⟨ refl ⟩
    (f *) ((ζ' • ζ' • ζ') • (S' • S') • X' • X' • S') • [ inj₁ HS-cr ] ∎

  lemma-HHH : H • HH ≈ HH • H
  lemma-HHH = begin
    H • HH ≈⟨ cong refl (axiom def-HH) ⟩
    H • H ^ 2 ≈⟨ sym assoc ⟩
    (H • H) • H ≈⟨ cong (sym (axiom def-HH)) refl ⟩
    HH • H ∎

  lemma-HSHH : (H • S) • HH ≈ (X • HH) • H • S
  lemma-HSHH = begin
    (H • S) • HH ≈⟨ cong refl (axiom def-HH) ⟩
    (H • S) • H ^ 2 ≈⟨ sym assoc ⟩
    ((H • S) • H) • H ≈⟨ cong lemma-HSH refl ⟩
    ((f *) ((ζ' ^ 6) • S' • S' • HH') • [ inj₁ HSS-cr ]) • H ≈⟨ assoc ⟩
    ((f *) ((ζ' ^ 6) • S' • S' • HH')) • ([ inj₁ HSS-cr ] • H) ≈⟨ cong refl lemma-HSSH ⟩
    ((f *) ((ζ' ^ 6) • S' • S' • HH')) • ((f *) ((ζ' ^ 6) • X' • X' • S') • [ inj₁ HS-cr ]) ≈⟨ sym assoc ⟩
    ((f *) (((ζ' ^ 6) • S' • S' • HH') • (ζ' ^ 6) • X' • X' • S')) • [ inj₁ HS-cr ] ≈⟨ cong (by-sub-nf {(((ζ' ^ 6) • S' • S' • HH') • (ζ' ^ 6) • X' • X' • S')} {X' • HH'} (M2.MM.by-equal-nf Eq.refl))  refl ⟩
    (X • HH) • H • S ∎

  lemma-HSSHH : (H • S • S) • HH ≈ (X • X • HH) • H • S • S
  lemma-HSSHH = begin
    (H • S • S) • HH ≈⟨ cong refl (axiom def-HH) ⟩
    (H • S • S) • H ^ 2 ≈⟨ sym assoc ⟩
    ((H • S • S) • H) • H ≈⟨ cong lemma-HSSH refl ⟩
    ((f *) ((ζ' ^ 6) • X' • X' • S') • [ inj₁ HS-cr ]) • H ≈⟨ assoc ⟩
    ((f *) ((ζ' ^ 6) • X' • X' • S')) • [ inj₁ HS-cr ] • H ≈⟨ cong refl lemma-HSH ⟩
    ((f *) ((ζ' ^ 6) • X' • X' • S')) • (f *) ((ζ' ^ 6) • S' • S' • HH') • [ inj₁ HSS-cr ] ≈⟨ sym assoc ⟩
    (((f *) ((ζ' ^ 6) • X' • X' • S')) • (f *) ((ζ' ^ 6) • S' • S' • HH')) • [ inj₁ HSS-cr ] ≈⟨ refl ⟩
    ((f *) (((ζ' ^ 6) • X' • X' • S') • ((ζ' ^ 6) • S' • S' • HH'))) • [ inj₁ HSS-cr ] ≈⟨ cong (by-sub-nf {(((ζ' ^ 6) • X' • X' • S') • ((ζ' ^ 6) • S' • S' • HH'))} {X' • X' • HH'} (M2.MM.by-equal-nf Eq.refl)) refl ⟩
    (X • X • HH) • H • S • S ∎


  h-hyp : ∀ c b -> [ c ] • [ b ]ʷ ≈ (f *) (h c b .proj₁) • [ h c b .proj₂ ]
  h-hyp (inj₁ HSS-cr) H-gen = lemma-HSSH
  h-hyp (inj₁ HSS-cr) X-gen = lemma-HSSX
  h-hyp (inj₁ HSS-cr) S-gen = lemma-HSSS
  h-hyp (inj₁ HSS-cr) ζ-gen = lemma-ζ^n 1 [ inj₁ HSS-cr ]
  h-hyp (inj₁ HS-cr) H-gen = lemma-HSH
  h-hyp (inj₁ HS-cr) X-gen = lemma-HSX
  h-hyp (inj₁ HS-cr) S-gen = trans assoc (sym left-unit)
  h-hyp (inj₁ HS-cr) ζ-gen = lemma-ζ^n 1 [ inj₁ HS-cr ]
  h-hyp (inj₁ H-cr) H-gen = sym (trans right-unit (axiom def-HH))
  h-hyp (inj₁ H-cr) X-gen = lemma-HX
  h-hyp (inj₁ H-cr) S-gen = sym left-unit
  h-hyp (inj₁ H-cr) ζ-gen = sym (axiom comm)
  h-hyp (inj₂ tt) H-gen = refl
  h-hyp (inj₂ tt) X-gen = trans left-unit (sym right-unit)
  h-hyp (inj₂ tt) S-gen = trans left-unit (sym right-unit)
  h-hyp (inj₂ tt) ζ-gen = trans left-unit (sym right-unit)
  h-hyp (inj₁ HSS-cr) HH-gen = lemma-HSSHH
  h-hyp (inj₁ HS-cr) HH-gen = lemma-HSHH
  h-hyp (inj₁ H-cr) HH-gen = lemma-HHH
  h-hyp (inj₂ tt) HH-gen = trans left-unit (sym right-unit)

  module ca = CA.Data (M2._===_) _===_ CT (inj₂ tt) f h [_]
  module aat = ca.Assumptions-And-Theorems h=⁻¹f-gen h-wd-ax f-wd-ax _≈_.refl h-hyp
  open aat using (nfp ; nfp') public
  
  open PP.NFProperty (nfp (M2.nfp (M.nfp (M0.nfp (Cyclic.nfp 9) )))) renaming (by-equal-nf to by-nf) using ()

  hcme : ∀ c m -> ∃ \ w -> ∃ \ c' -> ((h **) (inj₁ c) (f m)) ≡ (w , inj₁ c')
  hcme HSS-cr M2.HH-gen = X' • X' • HH' , HSS-cr , Eq.refl
  hcme HSS-cr M2.X-gen = Z' • X' , HSS-cr , Eq.refl
  hcme HSS-cr M2.S-gen = ζ' ^ 6 , H-cr , Eq.refl
  hcme HSS-cr M2.ζ-gen = ζ' , HSS-cr , Eq.refl
  hcme HS-cr M2.HH-gen = X' • HH' , HS-cr , Eq.refl
  hcme HS-cr M2.X-gen = ζ' ^ 3 • S' ^ 2 • X' • X' • S' , HS-cr , Eq.refl
  hcme HS-cr M2.S-gen = ε , HSS-cr , Eq.refl
  hcme HS-cr M2.ζ-gen = ζ' , HS-cr , Eq.refl
  hcme H-cr M2.HH-gen = HH' , H-cr , Eq.refl
  hcme H-cr M2.X-gen = Z' , H-cr , Eq.refl
  hcme H-cr M2.S-gen = ε , HS-cr , Eq.refl
  hcme H-cr M2.ζ-gen = ζ' , H-cr , Eq.refl
  
  htme : ∀ m -> ((h **) (inj₂ tt) (f m)) ≡ ([ m ]ʷ , inj₂ tt)
  htme M2.HH-gen = Eq.refl
  htme M2.X-gen = Eq.refl
  htme M2.S-gen = Eq.refl
  htme M2.ζ-gen = Eq.refl



  htme~ : ∀ (m : M) -> ([ m ]ʷ , I) ~ ((h **) I (f m))
  htme~ M2.X-gen = _≈₀_.refl , Eq.refl
  htme~ M2.S-gen = _≈₀_.refl , Eq.refl
  htme~ M2.ζ-gen = _≈₀_.refl , Eq.refl
  htme~ M2.HH-gen = _≈₀_.refl , Eq.refl
  
  [_]ₓ = f *

  hcme~ : ∀ (c : C) (m : M) -> let (w' , c' , p) = hcme c m in ([ c ]ₒ • f m) ≈ ([ w' ]ₓ • [ c' ]ₒ)
  hcme~ HS-cr M2.X-gen = by-nf Eq.refl
  hcme~ HS-cr M2.S-gen = by-nf Eq.refl
  hcme~ HS-cr M2.ζ-gen = by-nf Eq.refl
  hcme~ H-cr M2.X-gen = by-nf Eq.refl
  hcme~ H-cr M2.S-gen = by-nf Eq.refl
  hcme~ H-cr M2.ζ-gen = by-nf Eq.refl
  hcme~ HSS-cr M2.X-gen = by-nf Eq.refl
  hcme~ HSS-cr M2.S-gen = by-nf Eq.refl
  hcme~ HSS-cr M2.ζ-gen = by-nf Eq.refl
  hcme~ HSS-cr M2.HH-gen = by-nf Eq.refl
  hcme~ HS-cr M2.HH-gen = by-nf Eq.refl
  hcme~ H-cr M2.HH-gen = by-nf Eq.refl

  ca' : CosetNF-CT-Assumptions-And-Theorems-Packed M2._===_ _===_
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
    X-gen : Gen
    H-gen : Gen
    S-gen : Gen
    ζ-gen : Gen

  T : Word Gen
  T = [ T-gen ]ʷ

  H : Word Gen
  H = [ H-gen ]ʷ

  S : Word Gen
  S = [ S-gen ]ʷ

  X : Word Gen
  X = [ X-gen ]ʷ

  ζ : Word Gen
  ζ = [ ζ-gen ]ʷ

  Z : Word Gen
  Z = ζ ^ 3 • S ^ 2 • X ^ 2 • S • X

  HH : Word Gen
  HH = H ^ 2

  infix 4 _===_
  data _===_ : WRel Gen where
    order-ζ : ζ ^ 9 === ε
    order-S : S ^ 3 === ζ ^ 6
    order-X : X ^ 3 === ε
    order-H : H ^ 4 === ε
    order-T : T ^ 3 === Z
    -- order-HH is derivable
    order-SX : (S • X) ^ 3 === ε
    order-SH : (S • H) ^ 3 === ε
    
    comm-XS-SX : (X • S) • (S • X) === ζ ^ 6 • (S • X) • (X • S)
    comm-TS : T • S === S • T
    comm-TX : T • X === ζ ^ 3 • S ^ 2 • X • T
    comm-THH : T • HH === Z • HH • T • T

    comm-HX : H • X === Z • H

    comm-HH-X : HH • X === X ^ 2 • HH
    comm-HH-S : HH • S === (S • Z) • HH
    
    comm : ∀ {gen} -> ζ • [ gen ]ʷ === [ gen ]ʷ • ζ

  open PB _===_ using (_≈_)
  open PP _===_ renaming (word-setoid to ws ; •-ε-monoid to mo) 

  open SR ws
  open _≈_

  lemma-HXH^3=Z : H • X • H ^ 3 ≈ Z
  lemma-HXH^3=Z = begin
    H • X • H ^ 3 ≈⟨ sym assoc ⟩
    (H • X) • H ^ 3 ≈⟨ cong (axiom comm-HX) refl ⟩
    (Z • H) • H ^ 3 ≈⟨ assoc ⟩
    Z • H ^ 4 ≈⟨ trans (cong refl (axiom order-H)) right-unit ⟩
    Z ∎


  lemma-order-HH : HH ^ 2 ≈ ε
  lemma-order-HH = begin
    HH ^ 2 ≈⟨ refl ⟩
    (H ^ 2) ^ 2 ≈⟨ assoc ⟩
    (H ^ 4) ≈⟨ axiom order-H ⟩
    ε ∎

  lemma-def-X : X ≈ H ^ 3 • Z • H
  lemma-def-X = begin
    X ≈⟨ trans (sym right-unit) (cong refl (sym (axiom order-H))) ⟩
    X • H ^ 4 ≈⟨ trans (sym left-unit) (sym (cong (axiom order-H) refl)) ⟩
    H ^ 4 • X • H ^ 4 ≈⟨ by-assoc Eq.refl ⟩
    H ^ 3 • (H • X • H ^ 3) • H ≈⟨ cong refl (cong (lemma-HXH^3=Z) refl) ⟩
    H ^ 3 • Z • H ∎


  f₁ = CosetNF-CT-Assumptions-And-Theorems-Packed.f MA.ca'
  f₂ = CosetNF-CT-Assumptions-And-Theorems-Packed.f MB.ca'
  mypres = MA._===_ * MB._===_ ⋆ f₁ ⋆ f₂


  amalt1 : AmalDataNF M2.Gen MA._===_ MB._===_
  amalt1 = record { P₀ = M2._===_ ;
    CA₁ = MA.ca' ;
    CA₂ = MB.ca' }

  open ANF MA._===_  MB._===_ amalt1 using (nfp ; nfp') public

--  open PB _===_ renaming (_===_ to _===₁_ ; _≈_ to _≈_) using ()
  open PB mypres renaming (_===_ to _===₂_ ; _≈_ to _≈₂_) using ()

  
  open PP.NFProperty (nfp (M2.nfp (M.nfp (M0.nfp (Cyclic.nfp 9))))) using (by-equal-nf)

  open import Algebra.Bundles using (Monoid)
  open import Algebra.Morphism.Structures using (module MonoidMorphisms)

  f : Gen -> Word (MA.Gen ⊎ MB.Gen)
  f T-gen = [ MA.T ]ₗ
  f X-gen = [ MA.X ]ₗ
  f H-gen = [ MB.H ]ᵣ
  f S-gen = [ MA.S ]ₗ
  f ζ-gen = [ MA.ζ ]ₗ

  g : (MA.Gen ⊎ MB.Gen) -> Word Gen
  g (inj₁ MA.T-gen) = T
  g (inj₁ MA.X-gen) = X
  g (inj₁ MA.S-gen) = S
  g (inj₁ MA.ζ-gen) = ζ
  g (inj₂ MB.H-gen) = H
  g (inj₂ MB.X-gen) = X
  g (inj₂ MB.S-gen) = S
  g (inj₂ MB.ζ-gen) = ζ
  g (inj₁ MA.HH-gen) = HH
  g (inj₂ MB.HH-gen) = HH

  open import Presentation.Morphism

  lemma-ζ : ∀ w -> w • ζ ≈ ζ • w
  lemma-ζ [ x ]ʷ = sym (axiom comm)
  lemma-ζ ε = trans left-unit (sym right-unit)
  lemma-ζ (w • v) = trans assoc (trans (cong refl (lemma-ζ v)) (trans (sym assoc) (trans (cong (lemma-ζ w) refl) assoc)))


  f-well-defined : ∀ {w v} -> w === v -> (f *) w ≈₂ (f *) v
  f-well-defined order-ζ = _≈₂_.axiom (left MA.order-ζ)
  f-well-defined order-S = _≈₂_.axiom (left MA.order-S)
  f-well-defined order-X = _≈₂_.axiom (left MA.order-X)
  f-well-defined order-H = _≈₂_.axiom (right MB.order-H)
  f-well-defined order-T = _≈₂_.axiom (left MA.order-T)
  f-well-defined order-SX = _≈₂_.axiom (left MA.order-SX)
  f-well-defined order-SH = by-equal-nf Eq.refl
  f-well-defined comm-XS-SX = _≈₂_.axiom (left MA.comm-XS-SX)
  f-well-defined comm-TS = _≈₂_.axiom (left MA.comm-TS)
  f-well-defined comm-TX = _≈₂_.axiom (left MA.comm-TX)
  f-well-defined comm-THH = by-equal-nf Eq.refl
  f-well-defined comm-HX = by-equal-nf Eq.refl
  f-well-defined comm-HH-X = by-equal-nf Eq.refl
  f-well-defined comm-HH-S = by-equal-nf Eq.refl
  f-well-defined (comm {T-gen}) = _≈₂_.axiom (left MA.comm)
  f-well-defined (comm {X-gen}) = _≈₂_.axiom (left MA.comm)
  f-well-defined (comm {H-gen}) = by-equal-nf Eq.refl
  f-well-defined (comm {S-gen}) = _≈₂_.axiom (left MA.comm)
  f-well-defined (comm {ζ-gen}) = _≈₂_.refl
  
  g-well-defined : ∀ {w v} -> w ===₂ v -> (g *) w ≈ (g *) v
  g-well-defined (left MA.order-ζ) = axiom order-ζ
  g-well-defined (left MA.order-S) = axiom order-S
  g-well-defined (left MA.order-X) = _≈_.axiom order-X
  g-well-defined (left MA.order-HH) = lemma-order-HH
  g-well-defined (left MA.order-SX) = axiom order-SX
  g-well-defined (left MA.comm-XS-SX) = _≈_.axiom comm-XS-SX
  g-well-defined (left MA.comm-HH-X) = _≈_.axiom comm-HH-X
  g-well-defined (left MA.comm-HH-S) = _≈_.axiom comm-HH-S
  g-well-defined (left MA.order-T) = _≈_.axiom order-T
  g-well-defined (left MA.comm-TS) = _≈_.axiom comm-TS
  g-well-defined (left MA.comm-TX) = _≈_.axiom comm-TX
  g-well-defined (left MA.comm-THH) = _≈_.axiom comm-THH
  g-well-defined (left (MA.comm {MA.T-gen})) = _≈_.axiom comm
  g-well-defined (left (MA.comm {MA.X-gen})) = _≈_.axiom comm
  g-well-defined (left (MA.comm {MA.S-gen})) = _≈_.axiom comm
  g-well-defined (left (MA.comm {MA.ζ-gen})) = _≈_.refl
  g-well-defined (left (MA.comm {MA.HH-gen})) = _≈_.sym (lemma-ζ (wconcat (wmap g (wmap inj₁ [ MA.HH-gen ]ʷ))))

  g-well-defined (right MB.order-ζ) = _≈_.axiom order-ζ
  g-well-defined (right MB.order-S) = _≈_.axiom order-S
  g-well-defined (right MB.order-X) = _≈_.axiom order-X
  g-well-defined (right MB.order-H) = _≈_.axiom order-H
  g-well-defined (right MB.def-HH) = _≈_.refl
  g-well-defined (right MB.order-SH) = _≈_.axiom order-SH
  g-well-defined (right MB.comm-HH-X) = _≈_.axiom comm-HH-X
  g-well-defined (right MB.comm-HH-S) = _≈_.axiom comm-HH-S
  g-well-defined (right MB.HXH^3=Z) = lemma-HXH^3=Z
  g-well-defined (right MB.order-SX) = axiom order-SX
  g-well-defined (right MB.comm-XS-SX) = _≈_.axiom comm-XS-SX
  g-well-defined (right (MB.comm {MB.H-gen})) = _≈_.axiom comm
  g-well-defined (right (MB.comm {MB.X-gen})) = _≈_.axiom comm
  g-well-defined (right (MB.comm {MB.S-gen})) = _≈_.axiom comm
  g-well-defined (right (MB.comm {MB.ζ-gen})) = _≈_.refl
  g-well-defined (right (MB.comm {MB.HH-gen})) = _≈_.sym (lemma-ζ (wconcat (wmap g (wmap inj₂ [ MB.HH-gen ]ʷ))))
  
  g-well-defined (mid (amal {M2.HH-gen})) = _≈_.refl
  g-well-defined (mid (amal {M2.X-gen})) = _≈_.refl
  g-well-defined (mid (amal {M2.S-gen})) = _≈_.refl
  g-well-defined (mid (amal {M2.ζ-gen})) = _≈_.refl

  f-left-inv-gen : ∀ x -> [ x ]ʷ ≈₂ (f *) (g x)
  f-left-inv-gen (inj₁ MA.T-gen) = _≈₂_.refl
  f-left-inv-gen (inj₁ MA.X-gen) = by-equal-nf Eq.refl
  f-left-inv-gen (inj₁ MA.S-gen) = _≈₂_.refl
  f-left-inv-gen (inj₁ MA.ζ-gen) = _≈₂_.refl
  f-left-inv-gen (inj₂ MB.H-gen) = _≈₂_.refl
  f-left-inv-gen (inj₂ MB.X-gen) = by-equal-nf Eq.refl
  f-left-inv-gen (inj₂ MB.S-gen) = by-equal-nf Eq.refl
  f-left-inv-gen (inj₂ MB.ζ-gen) = by-equal-nf Eq.refl
  f-left-inv-gen (inj₁ MA.HH-gen) = by-equal-nf Eq.refl
  f-left-inv-gen (inj₂ MB.HH-gen) = by-equal-nf Eq.refl

  g-left-inv-gen : ∀ x -> [ x ]ʷ ≈ (g *) (f x)
  g-left-inv-gen T-gen = _≈_.refl
  g-left-inv-gen H-gen = _≈_.refl
  g-left-inv-gen S-gen = _≈_.refl
  g-left-inv-gen ζ-gen = _≈_.refl
  g-left-inv-gen X-gen = _≈_.refl

  open MonoidMorphisms 
  open PP mypres renaming (•-ε-monoid to m₂)


  Theorem-CliffordT1-iso-B*A⋆⋆ : IsMonoidIsomorphism (Monoid.rawMonoid mo) (Monoid.rawMonoid m₂) (f *)
  Theorem-CliffordT1-iso-B*A⋆⋆ = StarIsomorphism.isMonoidIsomorphism _===_ mypres f g f-well-defined  f-left-inv-gen g-well-defined  g-left-inv-gen


module CliffordT1-Simplified where

  data Gen : Set where
    T-gen : Gen
    H-gen : Gen
    S-gen : Gen
    ζ-gen : Gen

  T : Word Gen
  T = [ T-gen ]ʷ

  H : Word Gen
  H = [ H-gen ]ʷ

  S : Word Gen
  S = [ S-gen ]ʷ

  ζ : Word Gen
  ζ = [ ζ-gen ]ʷ

  X : Word Gen
  X = ζ ^ 3 • (H • S • H) • (H • S • S • H)

  Z : Word Gen
  Z = ζ ^ 3 • S ^ 2 • H ^ 2 • S • H ^ 2

  infix 4 _===_
  data _===_ : WRel Gen where
    order-ζ : ζ ^ 9 === ε
    order-S : S ^ 3 === ζ ^ 6
    order-H : H ^ 4 === ε
    order-T : T ^ 3 === Z
    
    order-SH : (S • H) ^ 3 === ε
    comm-HHSHHS : H • H • S • H • H • S === S • H • H • S • H • H
    
    order-THH : (T • H • H) ^ 2 === ε
    comm-TS : T • S === S • T
    comm-TX : T • X === ζ ^ 3 • S ^ 2 • X • T

    comm : ∀ {gen} -> ζ • [ gen ]ʷ === [ gen ]ʷ • ζ

  open PB _===_ using (_≈_)
  open PP _===_ renaming (word-setoid to ws ; •-ε-monoid to mo) 

  open SR ws
  open _≈_

  lemma-ζ : ∀ w -> w • ζ ≈ ζ • w
  lemma-ζ [ x ]ʷ = sym (axiom comm)
  lemma-ζ ε = trans left-unit (sym right-unit)
  lemma-ζ (w • v) = trans assoc (trans (cong refl (lemma-ζ v)) (trans (sym assoc) (trans (cong (lemma-ζ w) refl) assoc)))

  lemma-ζ^n : ∀ n w -> w • ζ ^ n ≈ ζ ^ n • w
  lemma-ζ^n zero w = trans right-unit (sym left-unit)
  lemma-ζ^n (suc n@zero) w = begin
    w • ζ ^ suc n ≈⟨ sym right-unit ⟩
    (w • ζ) • ζ ^ n ≈⟨ cong (lemma-ζ w) refl ⟩
    (ζ • w) • ζ ^ n ≈⟨ assoc ⟩
    ζ • w • ζ ^ n ≈⟨ cong refl (lemma-ζ^n n w) ⟩
    ζ • ζ ^ n • w ≈⟨ cong refl left-unit ⟩
    ζ ^ suc n • w ∎
  lemma-ζ^n (suc n@(suc n')) w = begin
    w • ζ ^ suc n ≈⟨ sym assoc ⟩
    (w • ζ) • ζ ^ n ≈⟨ cong (lemma-ζ w) refl ⟩
    (ζ • w) • ζ ^ n ≈⟨ assoc ⟩
    ζ • w • ζ ^ n ≈⟨ cong refl (lemma-ζ^n n w) ⟩
    ζ • ζ ^ n • w ≈⟨ sym assoc ⟩
    (ζ • ζ ^ n) • w ≈⟨ refl ⟩
    ζ ^ suc n • w ∎

  lemma-comm-HHSSHHS : H • H • S • S • H • H • S ≈ S • H • H • S • S • H • H
  lemma-comm-HHSSHHS = begin
    H • H • S • S • H • H • S ≈⟨ by-assoc Eq.refl ⟩
    (H • H • S) • S • H • H • S ≈⟨ cong refl (trans (sym left-unit) (sym (cong (axiom order-H) refl))) ⟩
    (H • H • S) • H ^ 4 • S • H • H • S ≈⟨ by-assoc Eq.refl ⟩
    (H • H • S • H  • H) • (H • H • S • H • H • S) ≈⟨ cong refl (axiom comm-HHSHHS) ⟩
    (H • H • S • H  • H) • S • (H • H • S • H • H) ≈⟨ by-assoc Eq.refl ⟩
    (H • H • S • H  • H • S) • (H • H • S • H • H) ≈⟨ cong (axiom comm-HHSHHS) refl ⟩
    (S • (H • H • S • H • H)) • (H • H • S • H • H) ≈⟨ by-assoc Eq.refl ⟩
    (S • H • H • S) • H ^ 4 • S • H • H ≈⟨ cong refl (cong (axiom order-H) refl) ⟩
    (S • H • H • S) • ε • S • H • H ≈⟨ by-assoc Eq.refl ⟩
    S • H • H • S • S • H • H ∎


  lemma-comm-HH-X' : X • H ^ 2 • X ≈ H ^ 2
  lemma-comm-HH-X' = begin
    X • H ^ 2 • X ≈⟨ by-assoc Eq.refl ⟩
    (ζ ^ 3 • (H • S • H) • (H • S • S • H) • H ^ 2) • ζ ^ 3 • (H • S • H) • (H • S • S • H) ≈⟨ cong refl (sym (lemma-ζ^n 3 ((H • S • H) • H • S • S • H))) ⟩
    (ζ ^ 3 • (H • S • H) • (H • S • S • H) • H ^ 2) • ((H • S • H) • (H • S • S • H)) • ζ ^ 3 ≈⟨ by-assoc Eq.refl ⟩
    (ζ ^ 3 • (H • S • H) • (H • S • S)) • H ^ 4 • (S • H) • (H • S • S • H) • ζ ^ 3 ≈⟨ cong refl (cong (axiom order-H) refl) ⟩
    (ζ ^ 3 • (H • S • H) • (H • S • S)) • ε • (S • H) • (H • S • S • H) • ζ ^ 3 ≈⟨ by-assoc Eq.refl ⟩
    (ζ ^ 3 • (H • S • H • H)) • S ^ 3 • H • H • S • S • H • ζ ^ 3 ≈⟨ cong refl (cong (axiom order-S) refl) ⟩
    (ζ ^ 3 • (H • S • H • H)) • ζ ^ 6 • H • H • S • S • H • ζ ^ 3 ≈⟨ cong refl (sym (lemma-ζ^n 6 (H • H • S • S • H • ζ ^ 3))) ⟩
    (ζ ^ 3 • (H • S • H • H)) • (H • H • S • S • H • ζ ^ 3) • ζ ^ 6 ≈⟨ by-assoc Eq.refl ⟩
    (ζ ^ 3 • H • S) • H ^ 4 • (S • S • H) • ζ ^ 9 ≈⟨ cong refl (cong (axiom order-H) (cong refl (axiom order-ζ))) ⟩
    (ζ ^ 3 • H • S) • ε • (S • S • H) • ε ≈⟨ by-assoc Eq.refl ⟩
    (ζ ^ 3 • H) • S ^ 3 • H ≈⟨ cong refl (cong (axiom order-S) refl) ⟩
    (ζ ^ 3 • H) • ζ ^ 6 • H ≈⟨ sym assoc ⟩
    ((ζ ^ 3 • H) • ζ ^ 6) • H ≈⟨ cong (lemma-ζ^n 6 (ζ ^ 3 • H)) refl ⟩
    (ζ ^ 6 • (ζ ^ 3 • H)) • H ≈⟨ by-assoc Eq.refl ⟩
    ζ ^ 9 • H ^ 2 ≈⟨ cong (axiom order-ζ) refl ⟩
    ε • H ^ 2 ≈⟨ left-unit ⟩
    H ^ 2 ∎






  lemma-order-HH : (H ^ 2) ^ 2 ≈ ε
  lemma-order-HH = begin
    (H ^ 2) ^ 2 ≈⟨ assoc ⟩
    (H ^ 4) ≈⟨ axiom order-H ⟩
    ε ∎
{-
  lemma-def-X : X ≈ H ^ 3 • Z • H
  lemma-def-X = begin
    X ≈⟨ trans (sym right-unit) (cong refl (sym (axiom order-H))) ⟩
    X • H ^ 4 ≈⟨ trans (sym left-unit) (sym (cong (axiom order-H) refl)) ⟩
    H ^ 4 • X • H ^ 4 ≈⟨ by-assoc Eq.refl ⟩
    H ^ 3 • (H • X • H ^ 3) • H ≈⟨ cong refl (cong (lemma-HXH^3=Z) refl) ⟩
    H ^ 3 • Z • H ∎
-}

  lemma-def-XX : X • X ≈ ζ ^ 3 • (H • S • S • H) • (H • S • H)
  lemma-def-XX = begin
    X • X ≈⟨ sym assoc ⟩
    ((ζ ^ 3 • (H • S • H) • (H • S • S • H)) • ζ ^ 3) • (H • S • H) • (H • S • S • H) ≈⟨ cong (lemma-ζ^n 3 (ζ ^ 3 • (H • S • H) • H • S • S • H)) refl ⟩
    (ζ ^ 3 • (ζ ^ 3 • (H • S • H) • (H • S • S • H))) • (H • S • H) • (H • S • S • H) ≈⟨ by-assoc Eq.refl ⟩
    (ζ ^ 6 • H • S) • (H • H • S • S • H • H • S) • H • H • S • S • H ≈⟨ cong refl (cong lemma-comm-HHSSHHS refl) ⟩
    (ζ ^ 6 • H • S) • (S • H • H • S • S • H • H) • H • H • S • S • H ≈⟨ by-assoc Eq.refl ⟩
    (ζ ^ 6 • H • S • S • H • H • S • S) • H ^ 4 • S • S • H ≈⟨ cong refl (cong (axiom order-H) refl) ⟩
    (ζ ^ 6 • H • S • S • H • H • S • S) • ε • S • S • H ≈⟨ by-assoc Eq.refl ⟩
    (ζ ^ 6 • H • S • S • H • H) • S ^ 3 • S • H ≈⟨ cong refl (cong (axiom order-S) refl) ⟩
    (ζ ^ 6 • H • S • S • H • H) • ζ ^ 6 • S • H ≈⟨ sym assoc ⟩
    ((ζ ^ 6 • H • S • S • H • H) • ζ ^ 6) • S • H ≈⟨ cong (lemma-ζ^n 6 (ζ ^ 6 • H • S • S • H • H)) refl ⟩
    (ζ ^ 6 • (ζ ^ 6 • H • S • S • H • H)) • S • H ≈⟨ by-assoc Eq.refl ⟩
    ζ ^ 9 • (ζ ^ 3 • (H • S • S • H) • (H • S • H)) ≈⟨ cong (axiom order-ζ) refl ⟩
    ε • (ζ ^ 3 • (H • S • S • H) • (H • S • H)) ≈⟨ left-unit ⟩
    ζ ^ 3 • (H • S • S • H) • (H • S • H) ∎

  lemma-order-S : S ^ 9 ≈ ε
  lemma-order-S = begin
    S ^ 9 ≈⟨ by-assoc Eq.refl ⟩
    (S ^ 3) ^ 3 ≈⟨ cong (axiom order-S) (cong (axiom order-S) (axiom order-S)) ⟩
    (ζ ^ 6) ^ 3 ≈⟨ by-assoc Eq.refl ⟩
    (ζ ^ 9) ^ 2 ≈⟨ trans (cong (axiom order-ζ) (axiom order-ζ)) right-unit ⟩
    ε ∎


  lemma-SHSHS : S • H • S • H • S ≈ H ^ 3
  lemma-SHSHS = begin
    S • H • S • H • S ≈⟨ trans (sym right-unit) (sym (cong refl (axiom order-H))) ⟩
    (S • H • S • H • S) • H ^ 4 ≈⟨ by-assoc Eq.refl ⟩
    (S • H) ^ 3 • H ^ 3 ≈⟨ trans (cong (axiom order-SH) refl) left-unit ⟩
    H ^ 3 ∎
  
  lemma-HSHS : H • S • H • S ≈ S ^ 8 • H ^ 3
  lemma-HSHS = begin
    H • S • H • S ≈⟨ trans (sym left-unit) (cong (sym lemma-order-S) refl) ⟩
    S ^ 9 • H • S • H • S ≈⟨ by-assoc Eq.refl ⟩
    S ^ 8 • S • H • S • H • S ≈⟨ cong refl lemma-SHSHS ⟩
    S ^ 8 • H ^ 3 ∎

  lemma-S^8 : S ^ 8 ≈ ζ ^ 3 • S ^ 2
  lemma-S^8 = begin
    S ^ 8 ≈⟨ by-assoc Eq.refl ⟩
    (S ^ 3) ^ 2 • S ^ 2 ≈⟨ cong (cong (axiom order-S) (axiom order-S)) refl ⟩
    (ζ ^ 6) ^ 2 • S ^ 2 ≈⟨ by-assoc Eq.refl ⟩
    (ζ ^ 9) • ζ ^ 3 • S ^ 2 ≈⟨ trans (cong (axiom order-ζ) refl) left-unit ⟩
    ζ ^ 3 • S ^ 2 ∎

  lemma-HSHS' : H • S • H • S ≈ (ζ ^ 3 • S ^ 2) • H ^ 3
  lemma-HSHS' = begin
    H • S • H • S ≈⟨ lemma-HSHS ⟩
    S ^ 8 • H ^ 3 ≈⟨ cong lemma-S^8 refl ⟩
    (ζ ^ 3 • S ^ 2) • H ^ 3 ∎

  lemma-HHHSSHHH : H ^ 3 • ζ ^ 3 • S • S • H ^ 3 ≈ S • H • S
  lemma-HHHSSHHH = begin
    H ^ 3 • ζ ^ 3 • S • S • H ^ 3 ≈⟨ by-assoc Eq.refl ⟩
    H ^ 3 • ((ζ ^ 3 • S • S) • H ^ 3) ≈⟨ cong refl (cong (sym lemma-S^8) refl) ⟩
    H ^ 3 • (S ^ 8 • H ^ 3) ≈⟨ cong refl (sym lemma-HSHS) ⟩
    H ^ 3 • (H • S • H • S) ≈⟨ by-assoc Eq.refl ⟩
    H ^ 4 • (S • H • S) ≈⟨ trans (cong (axiom order-H) refl) left-unit ⟩
    S • H • S ∎
{-
  lemma-XSSX : X • S • S • X ≈ (S • H • S • S • H) • (H • S • H • S)
  lemma-XSSX = begin
    X • S • S • X ≈⟨ by-assoc {!!} ⟩
    ζ ^ 3 • (H • S • H) • (H • S • S • H) • S • S • ζ ^ 3 • (H • S • H) • (H • S • S • H) ≈⟨ by-assoc {!lemma!} ⟩
    (S • H • S • S • H) • (H • S • H • S) ∎


  lemma-XSSX : X • S • S • X ≈ (S • H • S • S • H) • (H • S • H • S)
  lemma-XSSX = begin
    X • S • S • X ≈⟨ by-assoc {!!} ⟩
    (ζ ^ 3 • H ^ 3 • S ^ 2 • H ^ 2 • S • H ^ 3) • ((S • S) • ζ ^ 3) • H ^ 3 • S ^ 2 • H ^ 2 • S • H ^ 3 ≈⟨ cong refl (cong (lemma-ζ^n 3 (S • S)) refl) ⟩
    (ζ ^ 3 • H ^ 3 • S ^ 2 • H ^ 2 • S • H ^ 3) • (ζ ^ 3 • (S • S)) • H ^ 3 • S ^ 2 • H ^ 2 • S • H ^ 3 ≈⟨ by-assoc Eq.refl ⟩
    (ζ ^ 3 • H ^ 3 • S ^ 2 • H ^ 2 • S) • (H ^ 3 • ζ ^ 3 • S • S • H ^ 3) • S ^ 2 • H ^ 2 • S • H ^ 3 ≈⟨ cong refl (cong lemma-HHHSSHHH refl) ⟩
    (ζ ^ 3 • H ^ 3 • S ^ 2 • H ^ 2 • S) • (S • H • S) • S ^ 2 • H ^ 2 • S • H ^ 3 ≈⟨ by-assoc Eq.refl ⟩
    (ζ ^ 3 • H ^ 3 • S ^ 2) • (H ^ 2 • S • S • H) • S ^ 3 • H ^ 2 • S • H ^ 3 ≈⟨ cong refl (cong refl (cong (axiom order-S) refl)) ⟩
    (ζ ^ 3 • H ^ 3 • S ^ 2) • (H ^ 2 • S • S • H) • ζ ^ 6 • H ^ 2 • S • H ^ 3 ≈⟨ by-assoc Eq.refl ⟩
    (ζ ^ 3 • H ^ 3 • S ^ 2) • H ^ 2 • ((S • S • H) • ζ ^ 3) • (ζ ^ 3 • H ^ 2) • S • H ^ 3 ≈⟨ cong refl (cong refl (cong (lemma-ζ^n 3 (S • S • H)) (cong (sym (lemma-ζ^n 3 (H ^ 2))) refl))) ⟩
    (ζ ^ 3 • H ^ 3 • S ^ 2) • H ^ 2 • (ζ ^ 3 • (S • S • H)) • (H ^ 2 • ζ ^ 3) • S • H ^ 3 ≈⟨ cong refl (trans (sym left-unit) (sym (cong (axiom order-H) refl))) ⟩
    (ζ ^ 3 • H ^ 3 • S ^ 2) • H ^ 4 • H ^ 2 • (ζ ^ 3 • (S • S • H)) • (H ^ 2 • ζ ^ 3) • S • H ^ 3 ≈⟨ by-assoc Eq.refl ⟩
    (ζ ^ 3 • H ^ 3 • S ^ 2 • H ^ 3) • (H ^ 3 • ζ ^ 3 • S • S • H ^ 3) • ζ ^ 3 • S • H ^ 3 ≈⟨ cong refl (cong lemma-HHHSSHHH refl) ⟩
    (ζ ^ 3 • H ^ 3 • S ^ 2 • H ^ 3) • (S • H • S) • ζ ^ 3 • S • H ^ 3 ≈⟨ by-assoc Eq.refl ⟩
    (ζ ^ 3 • H ^ 3) • (S ^ 2 • H ^ 3) • (S • H) • (S • ζ ^ 3) • S • H ^ 3 ≈⟨ cong (sym (lemma-ζ^n 3 (H ^ 3))) (cong refl (cong refl (cong (lemma-ζ^n 3 S) refl)))  ⟩
    (H ^ 3 • ζ ^ 3) • (S ^ 2 • H ^ 3) • (S • H) • (ζ ^ 3 • S) • S • H ^ 3 ≈⟨ by-assoc Eq.refl ⟩
    (H ^ 3 • ζ ^ 3 • S • S • H ^ 3) • S • H • (ζ ^ 3 • S) • S • H ^ 3 ≈⟨ cong lemma-HHHSSHHH refl ⟩
    (S • H • S) • S • H • (ζ ^ 3 • S) • S • H ^ 3 ≈⟨ cong refl (cong refl (cong refl (cong (sym (lemma-ζ^n 3 S)) refl)))  ⟩
    (S • H • S) • S • H • (S • ζ ^ 3) • S • H ^ 3 ≈⟨ by-assoc Eq.refl ⟩
    (S • H • S • S • H) • (S • ζ ^ 3) • S • H ^ 3 ≈⟨ cong refl (cong (lemma-ζ^n 3 S) refl) ⟩
    (S • H • S • S • H) • (ζ ^ 3 • S) • S • H ^ 3 ≈⟨ by-assoc Eq.refl ⟩
    (S • H • S • S • H) • ((ζ ^ 3 • S ^ 2) • H ^ 3) ≈⟨ cong refl (sym lemma-HSHS') ⟩
    (S • H • S • S • H) • (H • S • H • S) ∎

  lemma-SXXS : S • X • X • S ≈ (S • H • S • S • H • ζ ^ 3) • (H • S • H • S)
  lemma-SXXS = begin
    S • X • X • S ≈⟨ by-assoc Eq.refl ⟩
    S • X ^ 2 • S ≈⟨ cong refl (cong {!!} refl) ⟩
    S • (ζ ^ 3 • H • S ^ 2 • H ^ 2 • S • H) • S ≈⟨ by-assoc Eq.refl ⟩
    S • (ζ ^ 3 • H • S ^ 2 • H) • (H • S • H) • S ≈⟨ cong refl (cong (sym (lemma-ζ^n 3 (H • S ^ 2 • H))) refl) ⟩
    S • ((H • S ^ 2 • H) • ζ ^ 3) • (H • S • H) • S ≈⟨ by-assoc Eq.refl ⟩
    (S • H • S • S • H • ζ ^ 3) • (H • S • H • S) ∎


  lemma-SXXS' : ζ ^ 6 • (S • X) • (X • S) ≈ (S • H • S • S • H) • (H • S • H • S)
  lemma-SXXS' = begin
    ζ ^ 6 • (S • X) • (X • S) ≈⟨ by-assoc Eq.refl ⟩
    ζ ^ 6 • (S • X • X • S) ≈⟨ cong refl lemma-SXXS ⟩
    ζ ^ 6 • (S • H • S • S • H • ζ ^ 3) • (H • S • H • S) ≈⟨ by-assoc Eq.refl ⟩
    ζ ^ 6 • ((S • H • S • S • H) • ζ ^ 3) • (H • S • H • S) ≈⟨ cong refl (cong (lemma-ζ^n 3 (S • H • S • S • H)) refl) ⟩
    ζ ^ 6 • (ζ ^ 3 • (S • H • S • S • H)) • (H • S • H • S) ≈⟨ by-assoc Eq.refl ⟩
    ζ ^ 9 • (S • H • S • S • H) • (H • S • H • S) ≈⟨ cong (axiom order-ζ) refl ⟩
    ε • (S • H • S • S • H) • (H • S • H • S) ≈⟨ left-unit ⟩
    (S • H • S • S • H) • (H • S • H • S) ∎
-}
  lemma-comm-XS-SX : (X • S) • (S • X) ≈ ζ ^ 6 • (S • X) • (X • S)
  lemma-comm-XS-SX = begin
    (X • S) • (S • X) ≈⟨ by-assoc Eq.refl ⟩
    (ζ ^ 3 • H • S • H • H • S • S • H) • ((S • S) • ζ ^ 3) • (H • S • H) • (H • S • S • H) ≈⟨ cong refl (cong (lemma-ζ^n 3 (S • S)) refl) ⟩
    (ζ ^ 3 • H • S • H • H • S • S • H) • (ζ ^ 3 • (S • S)) • (H • S • H) • (H • S • S • H) ≈⟨ by-assoc Eq.refl ⟩
    (ζ ^ 3 • H • S • H • H • S • S • H) • ε • (ζ ^ 3 • (S • S)) • ε • (H • S • H) • (H • S • S • H) ≈⟨ cong refl (cong (sym (axiom order-H)) (cong refl (sym (cong (axiom order-H) refl)))) ⟩
    (ζ ^ 3 • H • S • H • H • S • S • H) • H ^ 4 • (ζ ^ 3 • (S • S)) • H ^ 4 • (H • S • H) • (H • S • S • H) ≈⟨ by-assoc Eq.refl ⟩
    (ζ ^ 3 • H • S • H • H • S • S • H • H) • (H ^ 3 • ζ ^ 3 • S • S • H ^ 3) • (H • H • S • H) • (H • S • S • H) ≈⟨ cong refl (cong lemma-HHHSSHHH refl) ⟩
    (ζ ^ 3 • H • S • H • H • S • S • H • H) • (S • H • S) • (H • H • S • H) • (H • S • S • H) ≈⟨ by-assoc Eq.refl ⟩
    (ζ ^ 3 • H) • (S • H • H • S • S • H • H) • (S • H) • (S • H • H • S • H • H) • S • S • H ≈⟨ cong refl (cong (sym lemma-comm-HHSSHHS) (cong refl (cong (sym (axiom comm-HHSHHS)) refl))) ⟩
    (ζ ^ 3 • H) • (H • H • S • S • H • H • S) • (S • H) • (H • H • S • H • H • S) • S • S • H ≈⟨ by-assoc Eq.refl ⟩
    (ζ ^ 3 • H • H • H) • (S • S • H • H) • ε • (S • S) • H • (H • H • S • H • H • S) • S • S • H ≈⟨ cong (sym (lemma-ζ^n 3 (H • H • H))) (cong refl (sym (cong (axiom order-H) refl))) ⟩
    ((H • H • H) • ζ ^ 3) • (S • S • H • H) • H ^ 4 • (S • S) • H • (H • H • S • H • H • S) • S • S • H ≈⟨ by-assoc Eq.refl ⟩
    (H ^ 3 • ζ ^ 3 • S • S • H ^ 3) • H ^ 3 • S • S • H ^ 3 • (S • H • H • S) • S • S • H ≈⟨ cong lemma-HHHSSHHH refl ⟩
    (S • H • S) • H ^ 3 • S • S • H ^ 3 • (S • H • H • S) • S • S • H ≈⟨ by-assoc Eq.refl ⟩
    ((S • H • S) • H ^ 3 • S • S • H ^ 3 • S • H • H) • S ^ 3 • H ≈⟨ cong refl (cong (axiom order-S) refl) ⟩
    ((S • H • S) • H ^ 3 • S • S • H ^ 3 • S • H • H) • ζ ^ 6 • H ≈⟨ by-assoc Eq.refl ⟩
    (S • H • S) • H ^ 3 • ((S • S • H ^ 3 • S • H • H) • ζ ^ 3) • ζ ^ 3 • H ≈⟨ cong refl (cong refl (cong (lemma-ζ^n 3 (S • S • H ^ 3 • S • H • H)) (sym (lemma-ζ^n 3 H)))) ⟩
    (S • H • S) • H ^ 3 • (ζ ^ 3 • (S • S • H ^ 3 • S • H • H)) • H • ζ ^ 3 ≈⟨ by-assoc Eq.refl ⟩
    (S • H • S) • (H ^ 3 • ζ ^ 3 • S • S • H ^ 3) • S • H ^ 3 • ζ ^ 3 ≈⟨ cong refl (cong lemma-HHHSSHHH refl) ⟩
    (S • H • S) • (S • H • S) • S • H ^ 3 • ζ ^ 3 ≈⟨ by-assoc Eq.refl ⟩
    (S • H • S • S) • ε • H • ((S • S • H ^ 3) • ζ ^ 3) ≈⟨ cong refl (cong (sym (axiom order-H)) (cong refl (lemma-ζ^n 3 (S • S • H ^ 3)))) ⟩
    (S • H • S • S) • H ^ 4 • H • (ζ ^ 3 • (S • S • H ^ 3)) ≈⟨ by-assoc Eq.refl ⟩
    (S • H • S • S • H • H) • (H ^ 3 • ζ ^ 3 • S • S • H ^ 3) ≈⟨ cong refl lemma-HHHSSHHH ⟩
    (S • H • S • S • H • H) • (S • H • S) ≈⟨ by-assoc Eq.refl ⟩
    ε • S • (H • S • S • H) • (H • S • H) • S ≈⟨ sym (cong (axiom order-ζ) refl) ⟩
    ζ ^ 9 • S • (H • S • S • H) • (H • S • H) • S ≈⟨ by-assoc Eq.refl ⟩
    ζ ^ 6 • (ζ ^ 3 • S) • (H • S • S • H) • (H • S • H) • S ≈⟨ cong refl (cong (sym (lemma-ζ^n 3 S)) refl) ⟩
    ζ ^ 6 • (S • ζ ^ 3) • (H • S • S • H) • (H • S • H) • S ≈⟨ by-assoc Eq.refl ⟩
    ζ ^ 6 • (S • (ζ ^ 3 • (H • S • S • H) • (H • S • H)) • S) ≈⟨ cong refl (cong refl (cong (sym lemma-def-XX) refl)) ⟩
    ζ ^ 6 • (S • X ^ 2 • S) ≈⟨ by-assoc Eq.refl ⟩
    ζ ^ 6 • (S • X) • (X • S) ∎



  lemma-order-X : X ^ 3 ≈ ε
  lemma-order-X = begin
    X ^ 3 ≈⟨ by-assoc Eq.refl ⟩
    ((ζ ^ 3 • (H • S • H) • (H • S • S • H) • ζ ^ 3 • (H • S • H) • (H • S • S • H)) • ζ ^ 3) • (H • S • H) • (H • S • S • H) ≈⟨
      cong (lemma-ζ^n 3 (ζ ^ 3 • (H • S • H) • (H • S • S • H) • ζ ^ 3 • (H • S • H) • H • S • S • H)) refl ⟩
    (ζ ^ 3 • (ζ ^ 3 • (H • S • H) • (H • S • S • H) • ζ ^ 3 • (H • S • H) • (H • S • S • H))) • (H • S • H) • (H • S • S • H) ≈⟨ by-assoc Eq.refl ⟩
    ζ ^ 6 • (((H • S • H) • (H • S • S • H)) • ζ ^ 3) • (H • S • H) • (H • S • S • H) • (H • S • H) • (H • S • S • H) ≈⟨ cong refl (cong (lemma-ζ^n 3 ((H • S • H) • H • S • S • H)) refl) ⟩
    ζ ^ 6 • (ζ ^ 3 • ((H • S • H) • (H • S • S • H))) • (H • S • H) • (H • S • S • H) • (H • S • H) • (H • S • S • H) ≈⟨ by-assoc Eq.refl ⟩
    (ζ ^ 9 • H) • (S • H • H • S • S • H • H) • S • (H • H • S • S • H • H • S) • H • H • S • S • H ≈⟨ cong refl (cong (sym lemma-comm-HHSSHHS) (cong refl (cong lemma-comm-HHSSHHS refl))) ⟩
    (ζ ^ 9 • H) • (H • H • S • S • H • H • S) • S • (S • H • H • S • S • H • H) • H • H • S • S • H ≈⟨ by-assoc Eq.refl ⟩
    (ζ ^ 9 • H) • (H • H • S • S • H • H) • S ^ 3 • (H • H • S • S) • H ^ 4 • S • S • H ≈⟨ cong (cong (axiom order-ζ) refl) (cong refl (cong (axiom order-S) (cong refl (cong (axiom order-H) refl)))) ⟩
    (ε • H) • (H • H • S • S • H • H) • ζ ^ 6 • (H • H • S • S) • ε • S • S • H ≈⟨ by-assoc Eq.refl ⟩
    ((H • H • H • S • S • H • H) • ζ ^ 6) • ((H • H) • S ^ 3) • S • H ≈⟨ cong refl (cong (cong refl (axiom order-S)) refl) ⟩
    ((H • H • H • S • S • H • H) • ζ ^ 6) • ((H • H) • ζ ^ 6) • S • H ≈⟨ cong refl (cong (lemma-ζ^n 6 (H • H)) refl)  ⟩
    ((H • H • H • S • S • H • H) • ζ ^ 6) • (ζ ^ 6 • (H • H)) • S • H ≈⟨ by-assoc Eq.refl ⟩
    ((H • H • H • S • S • H • H) • ζ ^ 12) • ((H • H)) • S • H ≈⟨ cong (lemma-ζ^n 12 (H • H • H • S • S • H • H)) refl ⟩
    (ζ ^ 12 • (H • H • H • S • S • H • H)) • ((H • H)) • S • H ≈⟨ by-assoc Eq.refl ⟩
    (ζ ^ 12 • H • H • H • S • S) • H ^ 4 • S • H ≈⟨ cong refl (cong (axiom order-H) refl) ⟩
    (ζ ^ 12 • H • H • H • S • S) • ε • S • H ≈⟨ by-assoc Eq.refl ⟩
    (ζ ^ 12 • H • H • H) • S ^ 3 • H ≈⟨ cong refl (cong (axiom order-S) refl) ⟩
    (ζ ^ 12 • H • H • H) • ζ ^ 6 • H ≈⟨ cong refl (sym (lemma-ζ^n 6 H)) ⟩
    (ζ ^ 12 • H • H • H) • H • ζ ^ 6 ≈⟨ by-assoc Eq.refl ⟩
    (ζ ^ 12) • H ^ 4 • ζ ^ 6 ≈⟨ cong refl (cong (axiom order-H) refl) ⟩
    (ζ ^ 12) • ε • ζ ^ 6 ≈⟨ by-assoc Eq.refl ⟩
    (ζ ^ 9) ^ 2 ≈⟨ cong (axiom order-ζ) (axiom order-ζ) ⟩
    ε ^ 2 ≈⟨ left-unit ⟩
    ε ∎

  lemma-comm-HX : H • X ≈ Z • H
  lemma-comm-HX = begin
    H • X ≈⟨ refl ⟩
    H • ζ ^ 3 • (H • S • H) • (H • S • S • H) ≈⟨ by-assoc Eq.refl ⟩
    (H • ζ ^ 3) • H • S • H • H • S • S • H ≈⟨ cong (lemma-ζ^n 3 H) refl ⟩
    (ζ ^ 3 • H) • H • S • H • H • S • S • H ≈⟨ by-assoc Eq.refl ⟩
    ζ ^ 3 • (H • H • S • H • H • S) • S • H ≈⟨ cong refl (cong (axiom comm-HHSHHS) refl) ⟩
    ζ ^ 3 • (S • H • H • S • H • H) • S • H ≈⟨ by-assoc Eq.refl ⟩
    (ζ ^ 3 • S) • (H • H • S • H • H • S) • H ≈⟨ cong refl (cong (axiom comm-HHSHHS) refl) ⟩
    (ζ ^ 3 • S) • (S • H • H • S • H • H) • H ≈⟨ by-assoc Eq.refl ⟩
    Z • H ∎

  lemma-comm-HH-S : H ^ 2 • S ≈ (S • Z) • H ^ 2
  lemma-comm-HH-S = begin
    H ^ 2 • S ≈⟨ sym left-unit ⟩
    ε • H ^ 2 • S ≈⟨ sym (cong (axiom order-ζ) refl) ⟩
    (ζ ^ 9) • H ^ 2 • S ≈⟨ by-assoc Eq.refl ⟩
    (ζ ^ 3) • ζ ^ 6 • H ^ 2 • S ≈⟨ cong refl (sym (cong (axiom order-S) refl)) ⟩
    (ζ ^ 3) • S ^ 3 • H ^ 2 • S ≈⟨ by-assoc Eq.refl ⟩
    (ζ ^ 3 • S) • ((S ^ 2 • H ^ 2 • S) • ε) ≈⟨ cong (sym (lemma-ζ^n 3 S)) (cong refl (sym (axiom order-H))) ⟩
    (S • ζ ^ 3) • ((S ^ 2 • H ^ 2 • S) • H ^ 4) ≈⟨ by-assoc Eq.refl ⟩
    (S • ζ ^ 3 • S ^ 2 • H ^ 2 • S • H ^ 2) • H ^ 2 ≈⟨ refl ⟩
    (S • Z) • H ^ 2 ∎


  lemma-order-HS : (H • S) ^ 3 ≈ ε
  lemma-order-HS = begin
    (H • S) ^ 3 ≈⟨ by-assoc Eq.refl ⟩
    H • S • H • S • H • S ≈⟨ cong refl lemma-SHSHS ⟩
    H • H ^ 3 ≈⟨ axiom order-H ⟩
    ε ∎

  lemma-order-SX : (S • X) ^ 3 ≈ ε
  lemma-order-SX = begin
    (S • X) ^ 3 ≈⟨ refl ⟩
    (S • ζ ^ 3 • (H • S • H) • (H • S • S • H)) ^ 3 ≈⟨ cong refl (cong (cong refl (sym (lemma-ζ^n 3 ((H • S • H) • H • S • S • H)))) refl) ⟩
    (S • ζ ^ 3 • (H • S • H) • (H • S • S • H)) • (S • ((H • S • H) • (H • S • S • H)) • ζ ^ 3) • (S • ζ ^ 3 • (H • S • H) • (H • S • S • H)) ≈⟨ by-assoc Eq.refl ⟩
    (S • ζ ^ 3 • H • S • H • H • S) • (S • H) ^ 3 • (H • S • S • H) • ζ ^ 3 • S • ζ ^ 3 • (H • S • H) • (H • S • S • H) ≈⟨ cong refl (cong (axiom order-SH) refl) ⟩
    (S • ζ ^ 3 • H • S • H • H • S) • ε • (H • S • S • H) • ζ ^ 3 • S • ζ ^ 3 • (H • S • H) • (H • S • S • H) ≈⟨ by-assoc Eq.refl ⟩
    (S • ζ ^ 3 • H • S • H • H • S • H • S) • ((S • H) • ζ ^ 3) • S • (ζ ^ 3 • (H • S • H)) • (H • S • S • H) ≈⟨ cong refl (cong (lemma-ζ^n 3 (S • H)) (cong refl (cong (sym (lemma-ζ^n 3 (H • S • H))) refl))) ⟩
    (S • ζ ^ 3 • H • S • H • H • S • H • S) • (ζ ^ 3 • (S • H)) • S • ((H • S • H) • ζ ^ 3) • (H • S • S • H) ≈⟨ by-assoc Eq.refl ⟩
    (S • ζ ^ 3 • H • S • H • H • S • H • S • ζ ^ 3) • (S • H) ^ 3 • ζ ^ 3 • (H • S • S • H) ≈⟨ cong refl (cong (axiom order-SH) refl) ⟩
    (S • ζ ^ 3 • H • S • H • H • S • H • S • ζ ^ 3) • ε • ζ ^ 3 • (H • S • S • H) ≈⟨ by-assoc Eq.refl ⟩
    (S • ζ ^ 3 • H • S • H • H • S • H • S) • (ζ ^ 6 • H • S) • S • H ≈⟨ cong refl (cong (sym (lemma-ζ^n 6 (H • S))) refl) ⟩
    (S • ζ ^ 3 • H • S • H • H • S • H • S) • ((H • S) • ζ ^ 6) • S • H ≈⟨ by-assoc Eq.refl ⟩
    (S • ζ ^ 3 • H • S • H) • (H • S) ^ 3 • ζ ^ 6 • S • H ≈⟨ cong refl (cong lemma-order-HS refl) ⟩
    (S • ζ ^ 3 • H • S • H) • ε • ζ ^ 6 • S • H ≈⟨ by-assoc Eq.refl ⟩
    (S • ζ ^ 3) • (H • S • H) • (ζ ^ 6 • (S • H)) ≈⟨ cong (lemma-ζ^n 3 S) (cong refl (sym (lemma-ζ^n 6 (S • H)))) ⟩
    (ζ ^ 3 • S) • (H • S • H) • ((S • H) • ζ ^ 6) ≈⟨ by-assoc Eq.refl ⟩
    ζ ^ 3 • (S • H) ^ 3 • ζ ^ 6 ≈⟨ cong refl (cong (axiom order-SH) refl) ⟩
    ζ ^ 3 • ε • ζ ^ 6 ≈⟨ by-assoc Eq.refl ⟩
    ζ ^ 9 ≈⟨ axiom order-ζ ⟩
    ε ∎

  lemma-comm-HH-X : H ^ 2 • X ≈ X ^ 2 • H ^ 2
  lemma-comm-HH-X = begin
    H ^ 2 • X ≈⟨ trans  (sym left-unit) (sym (cong (lemma-order-X) refl)) ⟩
    X ^ 3 • H ^ 2 • X ≈⟨ by-assoc Eq.refl ⟩
    X ^ 2 • X • H ^ 2 • X ≈⟨ cong refl lemma-comm-HH-X' ⟩
    X ^ 2 • H ^ 2 ∎


  lemma-HXH^3=Z : H • X • H ^ 3 ≈ Z
  lemma-HXH^3=Z = begin
    H • X • H ^ 3 ≈⟨ sym assoc ⟩
    (H • X) • H ^ 3 ≈⟨ cong (lemma-comm-HX) refl ⟩
    (Z • H) • H ^ 3 ≈⟨ assoc ⟩
    Z • H ^ 4 ≈⟨ trans (cong refl (axiom order-H)) right-unit ⟩
    Z ∎


  f₁ = CosetNF-CT-Assumptions-And-Theorems-Packed.f MA.ca'
  f₂ = CosetNF-CT-Assumptions-And-Theorems-Packed.f MB.ca'
  mypres = MA._===_ * MB._===_ ⋆ f₁ ⋆ f₂


  amalt1 : AmalDataNF M2.Gen MA._===_ MB._===_
  amalt1 = record { P₀ = M2._===_ ;
    CA₁ = MA.ca' ;
    CA₂ = MB.ca' }

  open ANF MA._===_  MB._===_ amalt1 using (nfp ; nfp') public

--  open PB _===_ renaming (_===_ to _===₁_ ; _≈_ to _≈_) using ()

  
  open PP.NFProperty (nfp (M2.nfp (M.nfp (M0.nfp (Cyclic.nfp 9))))) using (by-equal-nf)

  open import Algebra.Bundles using (Monoid)
  open import Algebra.Morphism.Structures using (module MonoidMorphisms)

  f : Gen -> Word (MA.Gen ⊎ MB.Gen)
  f T-gen = [ MA.T ]ₗ
  f H-gen = [ MB.H ]ᵣ
  f S-gen = [ MA.S ]ₗ
  f ζ-gen = [ MA.ζ ]ₗ

  g : (MA.Gen ⊎ MB.Gen) -> Word Gen
  g (inj₁ MA.T-gen) = T
  g (inj₁ MA.X-gen) = X
  g (inj₁ MA.S-gen) = S
  g (inj₁ MA.ζ-gen) = ζ
  g (inj₂ MB.H-gen) = H
  g (inj₂ MB.X-gen) = X
  g (inj₂ MB.S-gen) = S
  g (inj₂ MB.ζ-gen) = ζ
  g (inj₁ MA.HH-gen) = H ^ 2
  g (inj₂ MB.HH-gen) = H ^ 2

  lemma-Z : (g *) [ MA.Z ]ₗ ≈ Z
  lemma-Z = begin
    (g *) [ MA.Z ]ₗ ≈⟨ _≈_.refl ⟩
    ζ ^ 3 • S ^ 2 • X ^ 2 • S • X ≈⟨ by-assoc Eq.refl ⟩
    (ζ ^ 3 • S ^ 2 • ζ ^ 3 • H • S • H • H • S • S • H) • ζ ^ 3 • (H • S • H) • (H • S • S • H) • S • X ≈⟨ cong refl (sym (lemma-ζ^n 3 ((H • S • H) • (H • S • S • H) • S • X))) ⟩
    (ζ ^ 3 • S ^ 2 • ζ ^ 3 • H • S • H • H • S • S • H) • ((H • S • H) • (H • S • S • H) • S • X) • ζ ^ 3 ≈⟨ by-assoc Eq.refl ⟩
    ((ζ ^ 3 • S ^ 2 • ζ ^ 3 • H) • (S • H • H • S • S • H • H) • S • H • H • S • S • H • S) • (ζ ^ 3 • (H • S • H) • (H • S • S • H)) • ζ ^ 3 ≈⟨ cong (cong refl (cong (sym lemma-comm-HHSSHHS) refl)) (cong (sym (lemma-ζ^n 3 ((H • S • H) • H • S • S • H))) refl) ⟩
    ((ζ ^ 3 • S ^ 2 • ζ ^ 3 • H) • (H • H • S • S • H • H • S) • S • H • H • S • S • H • S) • (((H • S • H) • (H • S • S • H)) • ζ ^ 3) • ζ ^ 3 ≈⟨ by-assoc Eq.refl ⟩
    (ζ ^ 3 • S ^ 2 • ζ ^ 3 • H • H • H • S) • (S • H • H • S • S • H • H) • S • (S • H) ^ 3 • (H • S • S • H) • ζ ^ 6 ≈⟨ cong refl (cong (sym lemma-comm-HHSSHHS) refl) ⟩
    (ζ ^ 3 • S ^ 2 • ζ ^ 3 • H • H • H • S) • (H • H • S • S • H • H • S) • S • (S • H) ^ 3 • (H • S • S • H) • ζ ^ 6 ≈⟨ by-assoc Eq.refl ⟩
    (ζ ^ 3 • S ^ 2 • ζ ^ 3 • H • H • H) • (S • H • H • S • S • H • H) • (S • S) • (S • H) ^ 3 • (H • S • S • H) • ζ ^ 6 ≈⟨ cong refl (cong refl (cong refl (cong (axiom order-SH) refl))) ⟩
    (ζ ^ 3 • S ^ 2 • ζ ^ 3 • H • H • H) • (S • H • H • S • S • H • H) • (S • S) • ε • (H • S • S • H) • ζ ^ 6 ≈⟨ cong refl (cong (sym lemma-comm-HHSSHHS) refl) ⟩
    (ζ ^ 3 • S ^ 2 • ζ ^ 3 • H • H • H) • (H • H • S • S • H • H • S) • (S • S) • ε • (H • S • S • H) • ζ ^ 6 ≈⟨ by-assoc Eq.refl ⟩
    (ζ ^ 3 • S ^ 2 • ζ ^ 3) • H ^ 4 • (H • S • S • H • H) • S ^ 3 • (H • S • S • H) • ζ ^ 6 ≈⟨ cong refl (cong (axiom order-H) (cong refl (cong (axiom order-S) refl))) ⟩
    (ζ ^ 3 • S ^ 2 • ζ ^ 3) • ε • (H • S • S • H • H) • ζ ^ 6 • (H • S • S • H) • ζ ^ 6 ≈⟨ cong refl (sym (cong (axiom order-H) refl)) ⟩
    (ζ ^ 3 • S ^ 2 • ζ ^ 3) • H ^ 4 • (H • S • S • H • H) • ζ ^ 6 • (H • S • S • H) • ζ ^ 6 ≈⟨ by-assoc Eq.refl ⟩
    (ζ ^ 3 • S ^ 2) • (ζ ^ 3 • (H ^ 4 • H)) • S • S • H • H • ζ ^ 6 • (H • S • S • H) • ζ ^ 6 ≈⟨ cong refl (cong (sym (lemma-ζ^n 3 (H ^ 4 • H))) refl) ⟩
    (ζ ^ 3 • S ^ 2) • ((H ^ 4 • H) • ζ ^ 3) • S • S • H • H • ζ ^ 6 • (H • S • S • H) • ζ ^ 6 ≈⟨ by-assoc Eq.refl ⟩
    (ζ ^ 3 • S ^ 2 • H ^ 2) • (H ^ 3 • ζ ^ 3 • S • S • H • H) • ζ ^ 6 • (H • S • S • H) • ζ ^ 6 ≈⟨ cong refl (cong refl (sym (lemma-ζ^n 6 ((H • S • S • H) • ζ ^ 6)))) ⟩
    (ζ ^ 3 • S ^ 2 • H ^ 2) • (H ^ 3 • ζ ^ 3 • S • S • H • H) • ((H • S • S • H) • ζ ^ 6) • ζ ^ 6 ≈⟨ by-assoc Eq.refl ⟩
    (ζ ^ 3 • S ^ 2 • H ^ 2) • (H ^ 3 • ζ ^ 3 • S • S • H ^ 3) • S • S • H • ζ ^ 12 ≈⟨ cong refl (cong lemma-HHHSSHHH refl) ⟩
    (ζ ^ 3 • S ^ 2 • H ^ 2) • (S • H • S) • S • S • H • ζ ^ 12 ≈⟨ by-assoc Eq.refl ⟩
    (ζ ^ 3 • S ^ 2 • H ^ 2 • S • H) • S ^ 3 • H • ζ ^ 12 ≈⟨ cong refl (cong (axiom order-S) refl) ⟩
    (ζ ^ 3 • S ^ 2 • H ^ 2 • S • H) • ζ ^ 6 • H • ζ ^ 12 ≈⟨ cong refl (sym (lemma-ζ^n 6 (H • ζ ^ 12))) ⟩
    (ζ ^ 3 • S ^ 2 • H ^ 2 • S • H) • (H • ζ ^ 12) • ζ ^ 6 ≈⟨ by-assoc Eq.refl ⟩
    (ζ ^ 3 • S ^ 2 • H ^ 2 • S • H • H) • (ζ ^ 9) ^ 2 ≈⟨ cong refl (cong (axiom order-ζ) (axiom order-ζ)) ⟩
    (ζ ^ 3 • S ^ 2 • H ^ 2 • S • H • H) • (ε) ^ 2 ≈⟨ trans (cong refl left-unit) right-unit ⟩
    Z ∎

  lemma-comm-HH-S' : H ^ 2 • S ≈ (S • (g *) [ MA.Z ]ₗ) • H ^ 2
  lemma-comm-HH-S' = begin
    H ^ 2 • S ≈⟨ lemma-comm-HH-S ⟩
    (S • Z) • H ^ 2 ≈⟨ cong (cong refl (sym lemma-Z)) refl ⟩
    (S • (g *) [ MA.Z ]ₗ) • H ^ 2 ∎


  lemma-THHT : T • H ^ 2 • T ≈ Z • H ^ 2 • Z
  lemma-THHT = begin
    T • H ^ 2 • T ≈⟨ trans (sym right-unit) (sym (cong refl (axiom order-H))) ⟩
    (T • H ^ 2 • T) • H ^ 4 ≈⟨ by-assoc Eq.refl ⟩
    (T • H • H) ^ 2 • H ^ 2 ≈⟨ cong (trans (axiom order-THH) (sym right-unit)) refl ⟩
    ε ^ 2 • H ^ 2 ≈⟨ trans assoc (trans left-unit left-unit) ⟩
    H ^ 2 ≈⟨ sym left-unit ⟩
    ε • H ^ 2 ≈⟨ sym (cong (axiom order-ζ) refl) ⟩
    ζ ^ 9 • H ^ 2 ≈⟨ by-assoc Eq.refl ⟩
    ζ ^ 3 • ζ ^ 6 • H ^ 2 ≈⟨ cong refl (sym (cong (axiom order-S) refl)) ⟩
    ζ ^ 3 • S ^ 3 • H ^ 2 ≈⟨ by-assoc Eq.refl ⟩
    (ζ ^ 3 • S ^ 2) • ε • S • H ^ 2 ≈⟨ cong refl (sym (cong (axiom order-H) refl)) ⟩
    (ζ ^ 3 • S ^ 2) • H ^ 4 • S • H ^ 2 ≈⟨ by-assoc Eq.refl ⟩
    (ζ ^ 3 • S ^ 2 • H ^ 2) • ε • H ^ 2 • S • H ^ 2 ≈⟨ cong refl (sym (cong (axiom order-ζ) refl)) ⟩
    (ζ ^ 3 • S ^ 2 • H ^ 2) • ζ ^ 9 • H ^ 2 • S • H ^ 2 ≈⟨ by-assoc Eq.refl ⟩
    (ζ ^ 3 • S ^ 2 • H ^ 2) • ζ ^ 6 • (ζ ^ 3) • H ^ 2 • S • H ^ 2 ≈⟨ cong refl (cong (sym (axiom order-S)) refl) ⟩
    (ζ ^ 3 • S ^ 2 • H ^ 2) • S ^ 3 • (ζ ^ 3) • H ^ 2 • S • H ^ 2 ≈⟨ by-assoc Eq.refl ⟩
    (ζ ^ 3 • S ^ 2 • H ^ 2 • S) • ε • (S ^ 2 • ζ ^ 3) • H ^ 2 • S • H ^ 2 ≈⟨ cong refl (cong (sym (axiom order-H)) (cong (lemma-ζ^n 3 (S ^ 2)) refl)) ⟩
    (ζ ^ 3 • S ^ 2 • H ^ 2 • S) • H ^ 4 • (ζ ^ 3 • S ^ 2) • H ^ 2 • S • H ^ 2 ≈⟨ by-assoc Eq.refl ⟩
    Z • H ^ 2 • Z ∎

  lemma-order-Z : Z ^ 3 ≈ ε
  lemma-order-Z = begin
    Z ^ 3 ≈⟨ by-assoc Eq.refl ⟩
    ((ζ ^ 3 • S ^ 2 • H ^ 2 • S • H ^ 2) • ζ ^ 3) • (S ^ 2 • H ^ 2 • S • H ^ 2) • ζ ^ 3 • S ^ 2 • H ^ 2 • S • H ^ 2 ≈⟨ cong (lemma-ζ^n 3 (ζ ^ 3 • S ^ 2 • H ^ 2 • S • H ^ 2)) (cong refl (sym (lemma-ζ^n 3 (S ^ 2 • H ^ 2 • S • H ^ 2)))) ⟩
    (ζ ^ 3 • (ζ ^ 3 • S ^ 2 • H ^ 2 • S • H ^ 2)) • (S ^ 2 • H ^ 2 • S • H ^ 2) • (S ^ 2 • H ^ 2 • S • H ^ 2) • ζ ^ 3 ≈⟨ by-assoc Eq.refl ⟩
    (ζ ^ 3 • ζ ^ 3 • S ^ 2 • H ^ 2) • (S • H • H • S • S • H • H) • S • (H • H • S • S • H • H • S) • H ^ 2 • ζ ^ 3 ≈⟨ cong refl (cong (sym lemma-comm-HHSSHHS) (cong refl (cong lemma-comm-HHSSHHS refl))) ⟩
    (ζ ^ 3 • ζ ^ 3 • S ^ 2 • H ^ 2) • (H • H • S • S • H • H • S) • S • (S • H • H • S • S • H • H) • H ^ 2 • ζ ^ 3 ≈⟨ by-assoc Eq.refl ⟩
    (ζ ^ 3 • ζ ^ 3 • S ^ 2) • H ^ 4 • (S • S • H • H) • S ^ 3 • (H • H • S • S) • H ^ 4 • ζ ^ 3 ≈⟨ cong refl (cong (axiom order-H) (cong refl (cong (axiom order-S) (cong refl (cong (axiom order-H) refl))))) ⟩
    (ζ ^ 3 • ζ ^ 3 • S ^ 2) • ε • (S • S • H • H) • ζ ^ 6 • (H • H • S • S) • ε • ζ ^ 3 ≈⟨ by-assoc Eq.refl ⟩
    (ζ ^ 3 • ζ ^ 3 • S) • S ^ 3 • (H • H) • ζ ^ 6 • (H • H • S • S) • ζ ^ 3 ≈⟨ cong refl (cong (axiom order-S) (cong refl (sym (lemma-ζ^n 6 ((H • H • S • S) • ζ ^ 3))))) ⟩
    (ζ ^ 3 • ζ ^ 3 • S) • ζ ^ 6 • (H • H) • ((H • H • S • S) • ζ ^ 3) • ζ ^ 6 ≈⟨ by-assoc Eq.refl ⟩
    (ζ ^ 3 • ζ ^ 3 • S • ζ ^ 6) • H ^ 4 • (S • S) • ζ ^ 9 ≈⟨ cong refl (cong (axiom order-H) (cong refl (axiom order-ζ))) ⟩
    (ζ ^ 3 • ζ ^ 3 • S • ζ ^ 6) • ε • (S • S) • ε ≈⟨ by-assoc Eq.refl ⟩
    (ζ ^ 3 • ζ ^ 3) • (S • ζ ^ 6) • (S • S) ≈⟨ cong refl (cong (lemma-ζ^n 6 S) refl) ⟩
    (ζ ^ 3 • ζ ^ 3) • (ζ ^ 6 • S) • (S • S) ≈⟨ by-assoc Eq.refl ⟩
    ζ ^ 3 • ζ ^ 9 • S ^ 3 ≈⟨ cong refl (cong (axiom order-ζ) (axiom order-S)) ⟩
    ζ ^ 3 • ε • ζ ^ 6 ≈⟨ by-assoc Eq.refl ⟩
    ζ ^ 9 ≈⟨ axiom order-ζ ⟩
    ε ∎

  lemma-order-T : T ^ 9 ≈ ε
  lemma-order-T = begin
    T ^ 9 ≈⟨ by-assoc Eq.refl ⟩
    (T ^ 3) ^ 3 ≈⟨ cong (axiom order-T) (cong (axiom order-T) (axiom order-T)) ⟩
    Z ^ 3 ≈⟨ lemma-order-Z ⟩
    ε ∎

  lemma-comm-THH : T • H ^ 2 ≈ Z • H ^ 2 • T • T
  lemma-comm-THH = begin
    T • H ^ 2 ≈⟨ trans (sym right-unit) (cong refl (sym lemma-order-T)) ⟩
    (T • H ^ 2) • T ^ 9 ≈⟨ by-assoc Eq.refl ⟩
    (T • H ^ 2 • T) • T ^ 8 ≈⟨ cong lemma-THHT refl ⟩
    (Z • H ^ 2 • Z) • T ^ 8 ≈⟨ cong (cong refl (cong refl (sym (axiom order-T)))) refl ⟩
    (Z • H ^ 2 • T ^ 3) • T ^ 8 ≈⟨ by-assoc Eq.refl ⟩
    (Z • H ^ 2 • T • T) • T ^ 9 ≈⟨ trans (cong refl lemma-order-T) right-unit ⟩
    (Z • H ^ 2 • T • T) ∎


  open import Presentation.Morphism
  open PB mypres renaming (_===_ to _===₂_ ; _≈_ to _≈₂_) using ()


  f-well-defined : ∀ {w v} -> w === v -> (f *) w ≈₂ (f *) v
  f-well-defined order-ζ = _≈₂_.axiom (left MA.order-ζ)
  f-well-defined order-S = _≈₂_.axiom (left MA.order-S)
  f-well-defined order-H = _≈₂_.axiom (right MB.order-H)
  f-well-defined order-T = by-equal-nf Eq.refl
  f-well-defined order-SH = by-equal-nf Eq.refl
  f-well-defined comm-TS = _≈₂_.axiom (left MA.comm-TS)
  f-well-defined comm-TX = by-equal-nf Eq.refl
  f-well-defined (comm {T-gen}) = _≈₂_.axiom (left MA.comm)
  f-well-defined (comm {H-gen}) = by-equal-nf Eq.refl
  f-well-defined (comm {S-gen}) = _≈₂_.axiom (left MA.comm)
  f-well-defined (comm {ζ-gen}) = _≈₂_.refl
  f-well-defined comm-HHSHHS = by-equal-nf Eq.refl
  f-well-defined order-THH = by-equal-nf Eq.refl
  
  g-well-defined : ∀ {w v} -> w ===₂ v -> (g *) w ≈ (g *) v
  g-well-defined (left MA.order-ζ) = axiom order-ζ
  g-well-defined (left MA.order-S) = axiom order-S
  g-well-defined (left MA.order-X) = lemma-order-X
  g-well-defined (left MA.order-HH) = lemma-order-HH
  g-well-defined (left MA.comm-XS-SX) = lemma-comm-XS-SX
  g-well-defined (left MA.comm-HH-X) = lemma-comm-HH-X
  g-well-defined (left MA.comm-HH-S) = lemma-comm-HH-S'
  g-well-defined (left MA.order-T) = trans (axiom order-T) (sym lemma-Z)
  g-well-defined (left MA.comm-TS) = _≈_.axiom comm-TS
  g-well-defined (left MA.comm-TX) = _≈_.axiom comm-TX
  g-well-defined (left MA.comm-THH) = trans (lemma-comm-THH) (cong (sym lemma-Z) refl)
  g-well-defined (left (MA.comm {MA.T-gen})) = _≈_.axiom comm
  g-well-defined (left (MA.comm {MA.X-gen})) = _≈_.sym (lemma-ζ (wconcat (wmap g (wmap inj₁ [ MA.X-gen ]ʷ))))
  g-well-defined (left (MA.comm {MA.S-gen})) = _≈_.axiom comm
  g-well-defined (left (MA.comm {MA.ζ-gen})) = _≈_.refl
  g-well-defined (left (MA.comm {MA.HH-gen})) = _≈_.sym (lemma-ζ (wconcat (wmap g (wmap inj₁ [ MA.HH-gen ]ʷ))))
  g-well-defined (left MA.order-SX) = lemma-order-SX

  g-well-defined (right MB.order-ζ) = _≈_.axiom order-ζ
  g-well-defined (right MB.order-S) = _≈_.axiom order-S
  g-well-defined (right MB.order-X) = lemma-order-X
  g-well-defined (right MB.order-H) = _≈_.axiom order-H
  g-well-defined (right MB.def-HH) = _≈_.refl
  g-well-defined (right MB.order-SH) = _≈_.axiom order-SH
  g-well-defined (right MB.comm-HH-X) = lemma-comm-HH-X
  g-well-defined (right MB.HXH^3=Z) = trans lemma-HXH^3=Z (trans (sym lemma-Z) refl)
  g-well-defined (right MB.order-SX) = lemma-order-SX
  g-well-defined (right MB.comm-XS-SX) = lemma-comm-XS-SX
  g-well-defined (right (MB.comm {MB.H-gen})) = _≈_.axiom comm
  g-well-defined (right (MB.comm {MB.X-gen})) = _≈_.sym (lemma-ζ (wconcat (wmap g (wmap inj₂ [ MB.X-gen ]ʷ))))
  g-well-defined (right (MB.comm {MB.S-gen})) = _≈_.axiom comm
  g-well-defined (right (MB.comm {MB.ζ-gen})) = _≈_.refl
  g-well-defined (right (MB.comm {MB.HH-gen})) = _≈_.sym (lemma-ζ (wconcat (wmap g (wmap inj₂ [ MB.HH-gen ]ʷ))))
  g-well-defined (right MB.comm-HH-S) = trans lemma-comm-HH-S (cong (cong refl (sym lemma-Z)) refl)
  
  g-well-defined (mid (amal {M2.HH-gen})) = _≈_.refl
  g-well-defined (mid (amal {M2.X-gen})) = _≈_.refl
  g-well-defined (mid (amal {M2.S-gen})) = _≈_.refl
  g-well-defined (mid (amal {M2.ζ-gen})) = _≈_.refl

  f-left-inv-gen : ∀ x -> [ x ]ʷ ≈₂ (f *) (g x)
  f-left-inv-gen (inj₁ MA.T-gen) = _≈₂_.refl
  f-left-inv-gen (inj₁ MA.X-gen) = by-equal-nf Eq.refl
  f-left-inv-gen (inj₁ MA.S-gen) = _≈₂_.refl
  f-left-inv-gen (inj₁ MA.ζ-gen) = _≈₂_.refl
  f-left-inv-gen (inj₂ MB.H-gen) = _≈₂_.refl
  f-left-inv-gen (inj₂ MB.X-gen) = by-equal-nf Eq.refl
  f-left-inv-gen (inj₂ MB.S-gen) = by-equal-nf Eq.refl
  f-left-inv-gen (inj₂ MB.ζ-gen) = by-equal-nf Eq.refl
  f-left-inv-gen (inj₁ MA.HH-gen) = by-equal-nf Eq.refl
  f-left-inv-gen (inj₂ MB.HH-gen) = by-equal-nf Eq.refl

  g-left-inv-gen : ∀ x -> [ x ]ʷ ≈ (g *) (f x)
  g-left-inv-gen T-gen = _≈_.refl
  g-left-inv-gen H-gen = _≈_.refl
  g-left-inv-gen S-gen = _≈_.refl
  g-left-inv-gen ζ-gen = _≈_.refl

  open MonoidMorphisms 
  open PP mypres renaming (•-ε-monoid to m₂)


  Theorem-CliffordT1-iso-B*A⋆⋆ : IsMonoidIsomorphism (Monoid.rawMonoid mo) (Monoid.rawMonoid m₂) (f *)
  Theorem-CliffordT1-iso-B*A⋆⋆ = StarIsomorphism.isMonoidIsomorphism _===_ mypres f g f-well-defined  f-left-inv-gen g-well-defined  g-left-inv-gen

module Test where

  open NFProperty' (CliffordT1.nfp' (M2.nfp' (M.nfp' (M0.nfp' (Cyclic.nfp' 9))))) using (by-equal-nf ; nf ; inv-nf)
  open PP CliffordT1.mypres
  open PB CliffordT1.mypres

  pattern H = [ inj₂ MB.H-gen ]ʷ
  pattern HH = [ inj₁ MA.HH-gen ]ʷ
  pattern T = [ inj₁ MA.T-gen ]ʷ
  pattern S = [ inj₁ MA.S-gen ]ʷ
  pattern S' = [ inj₂ MB.S-gen ]ʷ
  pattern X = [ inj₁ MA.X-gen ]ʷ
  pattern ζ = [ inj₁ MA.ζ-gen ]ʷ

  Z : Word (MA.Gen ⊎ MB.Gen)
  Z = ζ ^ 3 • S ^ 2 • X ^ 2 • S • X

  t :  T • T • T ≈ Z
  t = {!(mod-assoc ∘ inv-nf ∘ nf) (X • H • T • S • H • T • S • H • S • H • T)!}

  t2 :  [ MA.T • MA.T ]ₗ ≈ [ MB.S • MB.X • MB.X • MB.H • MB.H ]ᵣ
  t2 = by-equal-nf {!(mod-assoc ∘ inv-nf ∘ nf) (H • S • S • H • S • S • H • S • S • H   )!}

  t3 :  T • T • T ≈ Z
  t3 = by-equal-nf Eq.refl



