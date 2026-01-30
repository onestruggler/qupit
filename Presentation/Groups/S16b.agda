open import Level using (0ℓ)

open import Relation.Binary using (Rel)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Binary.Morphism.Definitions using (Homomorphic₂)
open import Relation.Binary.PropositionalEquality using (_≡_ ; inspect ; setoid ; module ≡-Reasoning) renaming ([_] to [_]ₑ)
import Relation.Binary.Reasoning.Setoid as SR
import Relation.Binary.PropositionalEquality as Eq
open import Relation.Nullary.Decidable using (yes ; no)


open import Function using (_∘_ ; id)
open import Function.Definitions using (Injective)

open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂ ; map₁)
open import Data.Product.Relation.Binary.Pointwise.NonDependent using (≡×≡⇒≡ ; Pointwise ; ≡⇒≡×≡)
open import Data.Product.Relation.Binary.Pointwise.NonDependent as PW
import Data.Product.Properties as DPP
open import Data.Nat using (ℕ ; zero ; suc ; 2+)
open import Data.Unit using (⊤ ; tt)


open import Word.Base
open import Word.Properties
import Presentation.Base as PB
import Presentation.Properties as PP
open PP using (NFProperty ; NFProperty')

import Presentation.CosetNF as CA
import Presentation.Reidemeister-Schreier as RS
module RSF = RS.Star-Injective-Full.Reidemeister-Schreier-Full

open import Presentation.Groups.Sn
open import Presentation.Groups.S16
 
module Presentation.Groups.S16b where

  open import Data.Bool
  open import Data.Sum as Sum hiding (swap) 
  open import Data.Product hiding (swap)

  open import Presentation.Construct.Base
  open PB (pres 1) renaming (Alphabet to S2) using ()

  import Presentation.Construct.Properties.DirectProduct as DP
  open PB
    
  lemma-fmfm : ∀ {n} w ->
    let open PB (pres 1 ⊕ pres (2+ n)) renaming (_≈_ to _≈₀_) in
    fm (fm w) • [ [ swap ]ʷ ]ᵣ ≈₀ [ [ swap ]ʷ ]ᵣ • fm (fm w)
  lemma-fmfm {n} [ inj₁ swap ]ʷ = axiom (mid (comm swap swap))
  lemma-fmfm {n} [ inj₂ swap ]ʷ = sym (axiom (right comm))
  lemma-fmfm {n} [ inj₂ (y ₛ) ]ʷ = sym (axiom (right comm))
  lemma-fmfm {n} ε = trans left-unit (sym right-unit)
  lemma-fmfm {n} (w • v) = begin
    fm (fm (w • v)) • [ [ swap ]ʷ ]ᵣ ≈⟨ assoc ⟩
    fm (fm w) • fm (fm v) • [ [ swap ]ʷ ]ᵣ ≈⟨ cong refl (lemma-fmfm v) ⟩
    fm (fm w) • [ [ swap ]ʷ ]ᵣ • fm (fm v) ≈⟨ _≈₀_.sym _≈₀_.assoc ⟩
    (fm (fm w) • [ [ swap ]ʷ ]ᵣ) • fm (fm v) ≈⟨ cong (lemma-fmfm w) refl ⟩
    ([ [ swap ]ʷ ]ᵣ • fm (fm w)) • fm (fm v) ≈⟨ _≈₀_.assoc ⟩
    [ [ swap ]ʷ ]ᵣ • fm (fm (w • v)) ∎
    where
    open PB (pres 1 ⊕ pres (2+ n)) renaming (_≈_ to _≈₀_) using ()
    open PP (pres 1 ⊕ pres (2+ n))
    open SR word-setoid



  lemma-fm³ : ∀ {n} w ->
    let open PB (pres 1 ⊕ pres (2+ (suc n))) renaming (_≈_ to _≈₀_) in
    fm (fm (fm w)) • [ [ swap ₛ ]ʷ ]ᵣ ≈₀ [ [ swap ₛ ]ʷ ]ᵣ • fm (fm (fm w))
  lemma-fm³ {n} [ inj₁ swap ]ʷ = axiom (mid (comm swap (swap ₛ)))
  lemma-fm³ {n'} [ inj₂ swap ]ʷ = bef Eq.refl
    where
    n = 2+ (suc n')
    open NFProperty (DP.NFP.nfp (pres 1) (pres n) (nfp 1) (nfp n)) renaming (by-equal-nf to bef)
  lemma-fm³ {n'} [ inj₂ (y ₛ) ]ʷ = by-assoc-and (LR.rights (sym (axiom (congₛ comm)))) Eq.refl Eq.refl
    where
    n = 2+ (suc n')
    open NFProperty (DP.NFP.nfp (pres 1) (pres n) (nfp 1) (nfp n)) renaming (by-equal-nf to bef)
    open PP (pres 1 ⊕ pres n)
    module LR = LeftRightCongruence (pres 1) (pres n) Γₓ
  lemma-fm³ {n} ε = trans left-unit (sym right-unit)
  lemma-fm³ {n} (w • v) = begin
    fm (fm (fm (w • v))) • [ [ swap ₛ ]ʷ ]ᵣ ≈⟨ assoc ⟩
    fm (fm (fm w)) • fm (fm (fm v)) • [ [ swap ₛ ]ʷ ]ᵣ ≈⟨ cong refl (lemma-fm³ v) ⟩
    fm (fm (fm w)) • [ [ swap ₛ ]ʷ ]ᵣ • fm (fm (fm v)) ≈⟨ _≈₀_.sym _≈₀_.assoc ⟩
    (fm (fm (fm w)) • [ [ swap ₛ ]ʷ ]ᵣ) • fm (fm (fm v)) ≈⟨ cong (lemma-fm³ w) refl ⟩
    ([ [ swap ₛ ]ʷ ]ᵣ • fm (fm (fm w))) • fm (fm (fm v)) ≈⟨ _≈₀_.assoc ⟩
    [ [ swap ₛ ]ʷ ]ᵣ • fm (fm (fm (w • v))) ∎
    where
    open PB (pres 1 ⊕ pres (2+ (suc n))) renaming (_≈_ to _≈₀_) using ()
    open PP (pres 1 ⊕ pres (2+ (suc n)))
    open SR word-setoid


  h-wd-ax : ∀ {n} -> (c : CC (suc n)) -> 
    let open PB (pres (suc (suc n))) renaming (Alphabet to Sₙ₊₂ ; _≈_ to _≈₂_ ; _===_ to _===₂_) using () in
    let open PB (pres n) renaming (Alphabet to Sn ; _≈_ to _≈ₙ_) using () in
    let open PB (pres 1 ⊕ pres n) renaming ( _≈_ to _≈₁_ ; _===_ to _===₁_) using () in
    let _~_ = PW.Pointwise _≈₁_ (_≡_ {A = CC (suc n)}) in
    {u t : Word (Sₙ₊₂)} ->  u ===₂ t -> (racts3 c u) ~ (racts3 c t)


  h-wd-ax {n@(suc nn)} cd@(swap• c , swap• d) {u} {t} ( (congₛ {w = w} {v} eq)) with h-wd-ax (c , d) (eq)
  ... | (ihl , ihr) rewrite  ihr = 
    let (w' , cw , dw) = racts3 (  c ,  d)  w  in
    let (v' , cv , dv) = racts3 (  c ,  d)  v  in
    begin
    (racts3 cd [ w ⇑]) ≡⟨ ler4 ( c) d w ⟩
    fm w' , swap• cw , swap• dw ≈⟨ fm-cong w' v' ihl , Eq.cong (dmap swap•_ swap•_) ihr  ⟩
    fm v' , swap• cv , swap• dv ≡⟨ Eq.sym (ler4 ( c) d v) ⟩
    (racts3 cd [ v ⇑]) ∎
    where
     open NFProperty (DP.NFP.nfp (pres 1) (pres n) (nfp 1) (nfp n)) renaming (by-equal-nf to bef)
     open PP (pres (suc (suc n))) using (by-assoc ; word-setoid)
     open PP (pres 1 ⊕ pres n) renaming (word-setoid to ws)
     ts = ×-setoid ws (setoid (CC (suc n)))
     open SR ts
     open import Relation.Binary.Bundles
     import Data.Product as DP

  h-wd-ax {0} cd@(swap• ε , swap• ε) {u} {t} (congₛ {w = w} {v} order) = axiom (left order) , Eq.refl
  h-wd-ax {0} cd@(swap• ε , swap• ε) {u} {t} (congₛ {w = w} {v} (congₛ ()))



  h-wd-ax {n} (ε , ε) {u} {t} order = bef Eq.refl , Eq.refl
    where
     open NFProperty (DP.NFP.nfp (pres 1) (pres n) (nfp 1) (nfp n)) renaming (by-equal-nf to bef)
  h-wd-ax {n} (ε , ε) {u} {t} comm = bef Eq.refl , Eq.refl
    where
     open NFProperty (DP.NFP.nfp (pres 1) (pres n) (nfp 1) (nfp n)) renaming (by-equal-nf to bef)
  h-wd-ax {n} (ε , ε) {u} {t} yang-baxter = (bef Eq.refl) , Eq.refl
    where
     open NFProperty (DP.NFP.nfp (pres 1) (pres n) (nfp 1) (nfp n)) renaming (by-equal-nf to bef)
  h-wd-ax {n} (ε , ε) {u} {t} (congₛ order) = (bef Eq.refl) , Eq.refl
    where
     open NFProperty (DP.NFP.nfp (pres 1) (pres n) (nfp 1) (nfp n)) renaming (by-equal-nf to bef)
  h-wd-ax {n} (ε , ε) {u} {t} (congₛ comm) = (bef Eq.refl) , Eq.refl
    where
     open NFProperty (DP.NFP.nfp (pres 1) (pres n) (nfp 1) (nfp n)) renaming (by-equal-nf to bef)
  h-wd-ax {n} (ε , ε) {u} {t} (congₛ yang-baxter) = (bef Eq.refl) , Eq.refl
    where
     open NFProperty (DP.NFP.nfp (pres 1) (pres n) (nfp 1) (nfp n)) renaming (by-equal-nf to bef)
  h-wd-ax {n} c@(ε , ε) {u} {t} (congₛ (congₛ {w = w} {v} eq)) = begin
    (racts3 c u) ≈⟨ auxr3a w ⟩
    ([ w ]ᵣ , c) ≈⟨ (axiom (right eq)) , Eq.refl ⟩
    ([ v ]ᵣ , c) ≈⟨ Setoid.sym ts (auxr3a v) ⟩
    (racts3 c t) ∎
    where
     open NFProperty (DP.NFP.nfp (pres 1) (pres n) (nfp 1) (nfp n)) renaming (by-equal-nf to bef)
     open PP (pres (suc (suc n))) using (by-assoc ; word-setoid)
     open PP (pres 1 ⊕ pres n) renaming (word-setoid to ws)
     ts = ×-setoid ws (setoid (CC (suc n)))
     open SR ts
     open import Relation.Binary.Bundles



  h-wd-ax {zero} (swap• ε , ε) order = left-unit , Eq.refl
  h-wd-ax {zero} (swap• ε , swap• ε) order = left-unit , Eq.refl
  h-wd-ax {zero} (swap• ε , ε) yang-baxter = refl , Eq.refl
  h-wd-ax {n@zero} (swap• ε , swap• ε) yang-baxter = (bef Eq.refl) , Eq.refl
    where open NFProperty (DP.NFP.nfp (pres 1) (pres n) (nfp 1) (nfp n)) renaming (by-equal-nf to bef)

  h-wd-ax {zero} (swap• ε , ε) (congₛ order) = left-unit , Eq.refl
  h-wd-ax {suc n} (swap• ε , ε) order = left-unit , Eq.refl
  h-wd-ax {suc n} (swap• ε , swap• ε) order = left-unit , Eq.refl
  h-wd-ax {suc n} (swap• swap• c , ε) order = left-unit , Eq.refl
  h-wd-ax {suc n} (swap• swap• c , swap• ε) order = left-unit , Eq.refl
  h-wd-ax {suc n} (swap• swap• c , swap• swap• d) order = axiom (right order) , Eq.refl
  h-wd-ax {suc n} (swap• ε , ε) yang-baxter = refl , Eq.refl
  h-wd-ax {suc n} (swap• ε , swap• ε) yang-baxter = by-assoc Eq.refl , Eq.refl
    where open PP (pres 1 ⊕ pres (suc n))
  h-wd-ax {suc n} (swap• swap• c , ε) yang-baxter = by-assoc Eq.refl , Eq.refl
    where open PP (pres 1 ⊕ pres (suc n))
  h-wd-ax {suc n} (swap• swap• ε , swap• ε) yang-baxter = by-assoc Eq.refl , Eq.refl
    where open PP (pres 1 ⊕ pres (suc n))
  h-wd-ax {suc n} (swap• swap• ε , swap• swap• ε) yang-baxter = by-assoc Eq.refl , Eq.refl
    where open PP (pres 1 ⊕ pres (suc n))
  h-wd-ax {suc n} (swap• swap• swap• c , swap• ε) yang-baxter = by-assoc Eq.refl , Eq.refl
    where open PP (pres 1 ⊕ pres (suc n))
  h-wd-ax {suc n} (swap• swap• swap• c , swap• swap• ε) yang-baxter = by-assoc Eq.refl , Eq.refl
    where open PP (pres 1 ⊕ pres (suc n))
  h-wd-ax {suc n} (swap• swap• swap• ε , swap• swap• swap• ε) yang-baxter = by-assoc-and (axiom (right yang-baxter)) Eq.refl  Eq.refl , Eq.refl
    where
    open NFProperty (DP.NFP.nfp (pres 1) (pres (suc n)) (nfp 1) (nfp (suc n))) renaming (by-equal-nf to bef)
    open PP (pres 1 ⊕ pres (suc n)) using (by-assoc ; by-assoc-and)

  h-wd-ax {suc n} (swap• swap• swap• swap• c , swap• swap• swap• ε) yang-baxter = by-assoc-and (axiom (right yang-baxter)) Eq.refl Eq.refl , Eq.refl
    where
    open NFProperty (DP.NFP.nfp (pres 1) (pres (suc n)) (nfp 1) (nfp (suc n))) renaming (by-equal-nf to bef)
    open PP (pres 1 ⊕ pres (suc n)) using (by-assoc ; by-assoc-and)
    
  h-wd-ax {suc n} (swap• swap• swap• swap• c , swap• swap• swap• swap• d) yang-baxter = by-assoc-and (axiom (right yang-baxter)) Eq.refl Eq.refl , Eq.refl
    where open PP (pres 1 ⊕ pres (suc n))


  h-wd-ax {suc n} (swap• ε , ε) (congₛ order) = left-unit , Eq.refl
  h-wd-ax {suc n} (swap• ε , ε) (congₛ (comm {a = swap})) = trans left-unit (sym right-unit) , Eq.refl
  h-wd-ax {suc n} (swap• ε , ε) (congₛ (comm {a = swap ₛ})) = trans left-unit (sym right-unit) , Eq.refl
  h-wd-ax {suc n} (swap• ε , ε) (congₛ (comm {a = (a ₛ) ₛ})) = trans left-unit (sym right-unit) , Eq.refl
  h-wd-ax {suc n} (swap• ε , ε) (congₛ yang-baxter) = refl , Eq.refl
  h-wd-ax {suc n} (swap• ε , ε) (congₛ (congₛ order)) = left-unit , Eq.refl
  h-wd-ax {suc n} (swap• ε , ε) (congₛ (congₛ comm)) = trans left-unit (sym right-unit) , Eq.refl
  h-wd-ax {suc n} (swap• ε , ε) (congₛ (congₛ yang-baxter)) = (by-assoc Eq.refl) , Eq.refl
    where
    open NFProperty (DP.NFP.nfp (pres 1) (pres (suc n)) (nfp 1) (nfp (suc n))) renaming (by-equal-nf to bef)
    open PP (pres 1 ⊕ pres (suc n)) using (by-assoc ; by-assoc-and)
  h-wd-ax {n} c@(swap• ε , ε) {u} {t} (congₛ (congₛ (congₛ {w = w} {v} eq))) =  begin
    (racts3 c u) ≈⟨ auxr3b w ⟩
    ([ [ w ⇑] ]ᵣ , c) ≈⟨ LR.rights ([⇑]-cong _ _ (axiom eq)) , Eq.refl ⟩
    ([ [ v ⇑] ]ᵣ , c) ≈⟨ Setoid.sym ts (auxr3b v) ⟩
    (racts3 c t) ∎
    where
     open NFProperty (DP.NFP.nfp (pres 1) (pres n) (nfp 1) (nfp n)) renaming (by-equal-nf to bef)
     open PP (pres (suc (suc n))) using (by-assoc ; word-setoid)
     open PP (pres 1 ⊕ pres n) renaming (word-setoid to ws)
     ts = ×-setoid ws (setoid (CC (suc n)))
     open SR ts
     open import Relation.Binary.Bundles
     module LR = LeftRightCongruence (pres 1) (pres n) Γₓ
    
  h-wd-ax {suc n} (swap• swap• c , ε) (congₛ order) = axiom (right order) , Eq.refl
  h-wd-ax {suc n} (swap• swap• ε , ε) (congₛ yang-baxter) = (by-assoc Eq.refl) , Eq.refl
    where
    open PP (pres 1 ⊕ pres (suc n)) using (by-assoc ; by-assoc-and)
  h-wd-ax {suc n} (swap• swap• swap• c , ε) (congₛ yang-baxter) = by-assoc-and (axiom (right yang-baxter)) Eq.refl Eq.refl , Eq.refl
    where
    open PP (pres 1 ⊕ pres (suc n)) using (by-assoc ; by-assoc-and)


  h-wd-ax {n@1} cd@(swap• swap• ε , d@ε) {u} {t} (congₛ (congₛ order)) = left-unit , Eq.refl
  h-wd-ax {n@(2+ nn)} cd@(swap• swap• ε , d@ε) {u} {t} (congₛ (congₛ order)) = left-unit , Eq.refl
  h-wd-ax {n@(2+ nn)} cd@(swap• swap• swap• ε , d@ε) {u} {t} (congₛ (congₛ order)) = by-assoc-and (axiom (right (congₛ order))) Eq.refl Eq.refl , Eq.refl
    where
     open PP (pres 1 ⊕ pres n) renaming (word-setoid to ws)
  h-wd-ax {n@(2+ nn)} cd@(swap• swap• swap• swap• c , d@ε) {u} {t} (congₛ (congₛ order)) = by-assoc-and (axiom (right (congₛ order))) Eq.refl Eq.refl , Eq.refl
    where
     open PP (pres 1 ⊕ pres n) renaming (word-setoid to ws)
  h-wd-ax {n@(2+ nn)} cd@(swap• swap• ε , d@ε) {u} {t} (congₛ (congₛ yang-baxter)) = by-assoc Eq.refl , Eq.refl
    where
     open PP (pres 1 ⊕ pres n) renaming (word-setoid to ws)
  h-wd-ax {n@(2+ nn)} cd@(swap• swap• swap• ε , d@ε) {u} {t} (congₛ (congₛ yang-baxter)) = by-assoc Eq.refl , Eq.refl
    where
     open PP (pres 1 ⊕ pres n) renaming (word-setoid to ws)
  h-wd-ax {n@(2+ nn)} cd@(swap• swap• swap• swap• c , d@ε) {u} {t} (congₛ (congₛ yang-baxter)) =  by-assoc-and (axiom (right (congₛ yang-baxter))) Eq.refl Eq.refl , Eq.refl
    where
     open PP (pres 1 ⊕ pres n) renaming (word-setoid to ws)

  h-wd-ax {n@(suc (suc nn))} cd@(swap• swap• c , d@ε) {u} {t} (congₛ (congₛ (congₛ {w = w} {v} eq))) with h-wd-ax (c , ε) (congₛ eq)
  ... | (ihl , ihr) rewrite  ihr = 
    let (w' , cw , dw) = racts3 (c , ε) [ w ⇑]  in
    let (v' , cv , dv) = racts3 (c , ε) [ v ⇑] in
    begin
    (racts3 cd [ [ [ w ⇑] ⇑] ⇑]) ≡⟨ ler6 c w ⟩
    fm (fm w') , swap• swap• cw , ε ≈⟨ (fm-cong _ _ (fm-cong _ _ ihl)) , Eq.cong (dmap (λ a → swap• swap• a) λ {a} b → ε) ihr ⟩
    fm (fm v') , swap• swap• cv , ε ≡⟨ Eq.sym (ler6 c v) ⟩
    (racts3 cd [ [ [ v ⇑] ⇑] ⇑]) ∎
    where
     open NFProperty (DP.NFP.nfp (pres 1) (pres n) (nfp 1) (nfp n)) renaming (by-equal-nf to bef)
     open PP (pres (suc (suc n))) using (by-assoc ; word-setoid)
     open PP (pres 1 ⊕ pres n) renaming (word-setoid to ws)
     ts = ×-setoid ws (setoid (CC (suc n)))
     open SR ts
     open import Relation.Binary.Bundles
     import Data.Product as DP




  h-wd-ax {2+ n} (swap• swap• ε , ε) (congₛ (congₛ (comm {a = swap}))) = trans left-unit (sym right-unit) , Eq.refl
  h-wd-ax {2+ n} (swap• swap• ε , ε) (congₛ (congₛ (comm {a = a ₛ}))) = trans left-unit (sym right-unit) , Eq.refl
  h-wd-ax {2+ n} (swap• swap• swap• ε , ε) (congₛ (congₛ (comm {a = swap}))) = trans right-unit (sym left-unit) , Eq.refl
  h-wd-ax {2+ n} (swap• swap• swap• ε , ε) (congₛ (congₛ (comm {a = swap ₛ}))) = by-assoc-and (axiom (right (congₛ comm)))  Eq.refl Eq.refl , Eq.refl
    where
     open PP (pres 1 ⊕ pres (2+ n)) renaming (word-setoid to ws)
  h-wd-ax {2+ n} (swap• swap• swap• ε , ε) (congₛ (congₛ (comm {a = (a ₛ) ₛ}))) = by-assoc-and (axiom (right (congₛ comm)))  Eq.refl Eq.refl , Eq.refl
    where
     open PP (pres 1 ⊕ pres (2+ n)) renaming (word-setoid to ws)
  h-wd-ax {n@(2+ (suc nn))} (swap• swap• swap• swap• c , ε) (congₛ (congₛ (comm {a = a}))) =
    let (w4 , c4 , d4) = racts3 (swap• swap• swap• c , ε) ([ a ₛ ₛ ₛ ]ʷ) in
    let (w1 , c1 , d1) = racts3 (swap• swap• swap• swap• c , ε) [ swap ₛ ₛ ]ʷ in
    let (w5 , c5 , d5) = racts3 (swap• swap• c , ε) [ a ₛ ₛ ]ʷ in
    let (w6 , c6 , d6) = racts3 (swap• c , ε) [ a ₛ ]ʷ in
    begin
      (racts3 (swap• swap• swap• swap• c , ε) ([ swap ₛ ₛ ]ʷ • [ a ₛ ₛ ₛ ₛ ]ʷ)) ≈⟨ refl , Eq.refl ⟩
      [ inj₂ (swap ₛ) ]ʷ • racts3 (swap• swap• swap• swap• c , ε) [ a ₛ ₛ ₛ ₛ ]ʷ .proj₁ , racts3 (swap• swap• swap• swap• c , ε) [ a ₛ ₛ ₛ ₛ ]ʷ .proj₂ ≈⟨ refl , Eq.refl ⟩
      [ inj₂ (swap ₛ) ]ʷ • fm w4 , swap• c4 , ε ≈⟨ refl , Eq.refl ⟩
      [ inj₂ (swap ₛ) ]ʷ • fm (fm (fm w6)) , swap• swap• swap• c6 , ε ≈⟨ (sym (lemma-fm³ w6)) , Eq.refl ⟩
      fm (fm (fm w6)) • [ inj₂ (swap ₛ) ]ʷ , swap• swap• swap• c6 , ε ≈⟨ refl , Eq.refl ⟩
      fm (fm (fm w6)) • racts3 (swap• swap• swap• c6 , ε) ([ swap ₛ ₛ ]ʷ) .proj₁ , racts3 (swap• swap• swap• c6 , ε) ([ swap ₛ ₛ ]ʷ) .proj₂ .proj₁ , racts3 (swap• swap• swap• c6 , ε) ([ swap ₛ ₛ ]ʷ) .proj₂ .proj₂ ≈⟨ refl , Eq.refl ⟩
      fm w4 • racts3 (swap• c4 , ε) ([ swap ₛ ₛ ]ʷ) .proj₁ , racts3 (swap• c4 , ε) ([ swap ₛ ₛ ]ʷ) .proj₂ .proj₁ , racts3 (swap• c4 , ε) ([ swap ₛ ₛ ]ʷ) .proj₂ .proj₂ ≈⟨ refl , Eq.refl ⟩
      (racts3 (swap• swap• swap• swap• c , ε) ([ a ₛ ₛ ₛ ₛ ]ʷ • [ swap ₛ ₛ ]ʷ)) ∎
    where
     open NFProperty (DP.NFP.nfp (pres 1) (pres n) (nfp 1) (nfp n)) renaming (by-equal-nf to bef)
     open PP (pres (suc (suc n))) using (by-assoc ; word-setoid)
     open PP (pres 1 ⊕ pres n) renaming (word-setoid to ws)
     ts = ×-setoid ws (setoid (CC (suc n)))
     open SR ts
     open import Relation.Binary.Bundles
     import Data.Product as DP
     module LR = LeftRightCongruence (pres 1) (pres n) Γₓ


  h-wd-ax {n@(suc (suc nn))} (swap• c@(swap• c0) , swap• d@(swap• d0)) (comm {a = (a)}) = 
    let (w7 , c7 , d7) = racts3 (swap• c , swap• d) ([ a ₛ ₛ ]ʷ) in
    let (w8 , c8 , d8) = racts3 ( c ,  d) ([ a ₛ ]ʷ) in
    let (w9 , c9 , d9) = racts3 ( c0 ,  d0) ([ a ]ʷ) in
    begin
    (racts3 (swap• c , swap• d) ([ swap ]ʷ • [ a ₛ ₛ ]ʷ)) ≈⟨ refl , Eq.refl ⟩
    [ [ swap ]ʷ ]ᵣ • racts3 (swap• c , swap• d) [ a ₛ ₛ ]ʷ .proj₁ , racts3 (swap• c , swap• d) [ a ₛ ₛ ]ʷ .proj₂ ≈⟨ refl , Eq.refl ⟩ 
    [ [ swap ]ʷ ]ᵣ • fm w8 , c7 , d7 ≈⟨ refl , Eq.refl ⟩ 
    [ [ swap ]ʷ ]ᵣ • fm w8 , swap• c8 , swap• d8 ≈⟨ (cong refl (refl' _ (Eq.cong fm ( Eq.cong proj₁ (ler4 c0 d0 [ a ]ʷ))))) , Eq.cong (dmap swap•_ swap•_) (Eq.cong proj₂ (ler4 c0 d0 [ a ]ʷ)) ⟩ 
    [ [ swap ]ʷ ]ᵣ • fm (fm w9) , swap• swap• c9 , swap• swap• d9 ≈⟨ refl , Eq.refl ⟩ 
    [ [ swap ]ʷ ]ᵣ • fm (fm w9) , (swap• swap• c9 , swap• swap• d9) ≈⟨ (sym (lemma-fmfm w9)) , Eq.refl ⟩
    fm (fm w9) • [ [ swap ]ʷ ]ᵣ , (swap• swap• c9 , swap• swap• d9) ≈⟨ refl , Eq.refl ⟩
    fm (fm w9) • racts3 (swap• swap• c9 , swap• swap• d9) [ swap ]ʷ .proj₁ , racts3 (swap• swap• c9 , swap• swap• d9) [ swap ]ʷ .proj₂ ≈⟨
      (cong (sym (refl' _ (Eq.cong fm ( Eq.cong proj₁ (ler4 c0 d0 [ a ]ʷ))))) (refl' _ (Eq.cong (λ x → racts3 x [ swap ]ʷ .proj₁)
      (Eq.sym (Eq.cong (dmap swap•_ swap•_) (Eq.cong proj₂ (ler4 c0 d0 [ a ]ʷ))))))) ,
      Eq.cong (\x -> racts3 x [ swap ]ʷ .proj₂) (Eq.sym (Eq.cong (dmap swap•_ swap•_) (Eq.cong proj₂ (ler4 c0 d0 [ a ]ʷ)))) ⟩
    fm w8 • racts3 (swap• c8 , swap• d8) [ swap ]ʷ .proj₁ , racts3 (swap• c8 , swap• d8) [ swap ]ʷ .proj₂ ≈⟨ refl , Eq.refl ⟩ 
    fm w8 • racts3 (swap• c8 , swap• d8) [ swap ]ʷ .proj₁ , racts3 (swap• c8 , swap• d8) [ swap ]ʷ .proj₂ ≈⟨ refl , Eq.refl ⟩ 
    fm w8 • racts3 (c7 , d7) [ swap ]ʷ .proj₁ , racts3 (c7 , d7) [ swap ]ʷ .proj₂ ≈⟨ refl , Eq.refl ⟩ 
    (racts3 (swap• c , swap• d) ([ a ₛ ₛ ]ʷ • [ swap ]ʷ)) ∎
    where
     open NFProperty (DP.NFP.nfp (pres 1) (pres n) (nfp 1) (nfp n)) renaming (by-equal-nf to bef)
     open PP (pres (suc (suc n))) using (by-assoc ; word-setoid)
     open PP (pres 1 ⊕ pres n) renaming (word-setoid to ws)
     ts = ×-setoid ws (setoid (CC (suc n)))
     open SR ts
     open import Relation.Binary.Bundles
     import Data.Product as DP
     module LR = LeftRightCongruence (pres 1) (pres n) Γₓ


  h-wd-ax {suc n} (swap• ε , swap• ε) (comm {a = swap}) = refl , Eq.refl
  h-wd-ax {suc n} (swap• ε , swap• ε) (comm {a = a ₛ}) = trans left-unit (sym right-unit) , Eq.refl
  h-wd-ax {suc n} (swap• swap• ε , swap• ε) (comm {a = swap}) = refl , Eq.refl
  h-wd-ax {suc n} (swap• swap• swap• c , swap• ε) (comm {a = swap}) = trans left-unit (sym right-unit) , Eq.refl
  h-wd-ax {2+ n} (swap• swap• ε , swap• ε) (comm {a = swap ₛ}) = refl , Eq.refl
  h-wd-ax {2+ n} (swap• swap• swap• c , swap• ε) (comm {a = swap ₛ}) = trans left-unit (sym right-unit) , Eq.refl
  h-wd-ax {2+ n} (swap• swap• ε , swap• ε) (comm {a = (swap ₛ) ₛ}) = trans left-unit (sym right-unit) , Eq.refl
  h-wd-ax {2+ n} (swap• swap• ε , swap• ε) (comm {a = ((a ₛ) ₛ) ₛ}) = trans left-unit (sym right-unit) , Eq.refl
  h-wd-ax {2+ n} (swap• swap• swap• c , swap• ε) (comm {a = (swap ₛ) ₛ}) = trans left-unit (sym right-unit) , Eq.refl
  h-wd-ax {2+ n} (swap• swap• swap• c , swap• ε) (comm {a = ((a ₛ) ₛ) ₛ}) = trans left-unit (sym right-unit) , Eq.refl
  h-wd-ax {suc zero} (swap• swap• ε , swap• swap• ε) (comm {a = swap}) = sym (axiom (mid (comm swap swap))) , Eq.refl
  h-wd-ax {suc zero} (swap• swap• ε , swap• swap• ε) (comm {a = () ₛ})




  h-wd-ax {n@(suc ( suc nn))} (swap• swap• c , ε) (congₛ (comm {a = a})) with ler5b (c) [ a ]ʷ | lel5b {nn} c [ a ]ʷ
  ... | (w6 , c6 , pr) | (w8 , c8 , pr8) = 
    let (w3 , c3 , d3) = racts3 (swap• swap• c , swap• ε) ([ (a ₛ) ₛ ₛ ]ʷ) in
    let (w4 , c4 , d4) = racts3 (swap• c , ε) ([ (a ₛ) ₛ ]ʷ) in
    let (w5 , c5 , d5) = racts3 (swap• c4 , ε) ([ swap ₛ ]ʷ) in
    let (w7 , c7 , d7) = racts3 (swap• swap• c6 , ε) ([ swap ₛ ]ʷ) in
    begin
    (racts3 (swap• swap• c , ε) ([ swap ₛ ]ʷ • [ (a ₛ) ₛ ₛ ]ʷ)) ≈⟨ refl , Eq.refl ⟩
    [ [ swap ]ʷ ]ᵣ • racts3 (swap• swap• c , ε) [ (a ₛ) ₛ ₛ ]ʷ .proj₁ , racts3 (swap• swap• c , ε) [ (a ₛ) ₛ ₛ ]ʷ .proj₂ ≈⟨ refl , Eq.refl ⟩
    [ [ swap ]ʷ ]ᵣ • fm w4 , (swap• c4 , ε) ≈⟨ cong refl refl , Eq.cong (\x -> (swap• x , ε)) (Eq.cong (proj₁ ∘ proj₂) pr)  ⟩
    [ [ swap ]ʷ ]ᵣ • fm w4 , (swap• (swap• c6) , ε) ≈⟨ cong refl (refl' _ (Eq.cong fm (Eq.cong proj₁ pr8))) , Eq.refl ⟩
    [ [ swap ]ʷ ]ᵣ • fm [ [ w8 ⇑] ]ᵣ , (swap• (swap• c6) , ε) ≈⟨ cong refl (refl' _ (lemma-fm3 (wconcat (wmap (λ x → [ x ₛ ]ʷ) w8)))) , Eq.refl ⟩
    [ [ swap ]ʷ ]ᵣ • [ [ [ w8 ⇑] ⇑] ]ᵣ , (swap• (swap• c6) , ε) ≈⟨ LR.rights (sym (lemma-comm w8)) , Eq.refl ⟩
    [ [ [ w8 ⇑] ⇑] ]ᵣ • [ [ swap ]ʷ ]ᵣ , (swap• (swap• c6) , ε) ≈⟨ cong (sym (refl' _ (lemma-fm3 (wconcat (wmap (λ x → [ x ₛ ]ʷ) w8))))) refl , Eq.refl ⟩
    fm [ [ w8 ⇑] ]ᵣ • [ [ swap ]ʷ ]ᵣ , (swap• (swap• c6) , ε) ≈⟨ cong (refl' _ (Eq.cong fm (Eq.cong proj₁ (Eq.sym pr8)))) refl , Eq.refl ⟩
    fm w4 • [ [ swap ]ʷ ]ᵣ , (swap• (swap• c6) , ε) ≈⟨ refl , Eq.refl ⟩
    fm w4 • [ [ swap ]ʷ ]ᵣ , c7 , d7 ≈⟨ refl , Eq.refl ⟩
    fm w4 • w7 , c7 , d7 ≈⟨ refl , Eq.refl ⟩
    fm w4 • racts3 (swap• (swap• c6) , ε) ([ swap ₛ ]ʷ) .proj₁ , racts3 (swap• (swap• c6) , ε) ([ swap ₛ ]ʷ) .proj₂ .proj₁ , racts3 (swap• (swap• c6) , ε) ([ swap ₛ ]ʷ) .proj₂ .proj₂ ≈⟨ (refl' _ (Eq.cong (λ x → fm w4 • racts3 (swap• x , ε) [ swap ₛ ]ʷ .proj₁) (Eq.cong (proj₁ ∘ proj₂) (Eq.sym pr)))) , Eq.cong (\x -> racts3 (swap• x , ε) ([ swap ₛ ]ʷ) .proj₂ .proj₁ , racts3 (swap• x , ε) ([ swap ₛ ]ʷ) .proj₂ .proj₂) (Eq.cong (proj₁ ∘ proj₂) (Eq.sym pr)) ⟩
    fm w4 • racts3 (swap• c4 , ε) ([ swap ₛ ]ʷ) .proj₁ , racts3 (swap• c4 , ε) ([ swap ₛ ]ʷ) .proj₂ .proj₁ , racts3 (swap• c4 , ε) ([ swap ₛ ]ʷ) .proj₂ .proj₂ ≈⟨ refl , Eq.refl ⟩
    (racts3 (swap• swap• c , ε) ([ (a ₛ) ₛ ₛ ]ʷ • [ swap ₛ ]ʷ)) ∎
    where
     open NFProperty (DP.NFP.nfp (pres 1) (pres n) (nfp 1) (nfp n)) renaming (by-equal-nf to bef)
     open PP (pres (suc (suc n))) using (by-assoc ; word-setoid)
     open PP (pres 1 ⊕ pres n) renaming (word-setoid to ws)
     ts = ×-setoid ws (setoid (CC (suc n)))
     open SR ts
     open import Relation.Binary.Bundles
     import Data.Product as DP
     module LR = LeftRightCongruence (pres 1) (pres n) Γₓ


  h-wd-ax {n} (swap• ε , ε) {u} {t} (comm {a = swap}) = (bef Eq.refl) , Eq.refl
    where
     open NFProperty (DP.NFP.nfp (pres 1) (pres n) (nfp 1) (nfp n)) renaming (by-equal-nf to bef)
  h-wd-ax {n} (swap• ε , ε) {u} {t} (comm {a = a ₛ}) = (bef Eq.refl) , Eq.refl
    where
     open NFProperty (DP.NFP.nfp (pres 1) (pres n) (nfp 1) (nfp n)) renaming (by-equal-nf to bef)


  h-wd-ax {n@(suc nn)} (swap• c@(swap• c0) , ε) (comm {a = a}) =
    let (w , c' , d') = racts3 (c , ε) [ a ₛ ]ʷ in
    let (v , cc , dd) = racts3 (c' , d') [ swap ]ʷ in
    let (v' , cc' , dd') = racts3 (c' , ε) [ swap ]ʷ in
    begin
    (racts3 (swap• c , ε) ([ swap ]ʷ • [ (a ₛ) ₛ ]ʷ)) ≈⟨ left-unit , Eq.refl ⟩
    (racts3 (swap• c , swap• ε) ([ (a ₛ) ₛ ]ʷ)) ≡⟨ ler4 c ε [ a ₛ ]ʷ ⟩
    (fm w , swap• c' , swap• d') ≈⟨ (sym right-unit) , (Eq.cong (λ z → swap• c' , swap• z) (aux3a c a)) ⟩
    fm w • ε , swap• c' , swap• ε ≈⟨ refl , Eq.refl ⟩
    (racts3 (swap• c , ε) ([ (a ₛ) ₛ ]ʷ • [ swap ]ʷ)) ∎
    where
     open NFProperty (DP.NFP.nfp (pres 1) (pres n) (nfp 1) (nfp n)) renaming (by-equal-nf to bef)
     open PP (pres (suc (suc n))) using (by-assoc ; word-setoid)
     open PP (pres 1 ⊕ pres n) renaming (word-setoid to ws)
     ts = ×-setoid ws (setoid (CC (suc n)))
     open SR ts
     open import Relation.Binary.Bundles
     import Data.Product as DP



  nfp-n+2 : (n : ℕ) -> NFProperty (pres (suc (suc n)))

  nfp-n+2 n = AAT.nfp h=⁻¹f-gen' (h-wd-ax {n}) f-wd-ax left-unit (lemma-ract3 {n}) (DP.NFP.nfp (pres 1) (pres n) (nfp 1) (nfp n))
   where
     open myData n renaming (module Assumptions-And-Theorems to AAT)
     open PB (pres (suc (suc n))) renaming (Alphabet to Sₙ₊₂ ; _≈_ to _≈₂_ ; _===_ to _===₂_) using ()
     open PB (pres n) renaming (Alphabet to Sn ; _≈_ to _≈ₙ_) using ()
     open PB (pres 1 ⊕ pres n) renaming ( _≈_ to _≈₁_ ; _===_ to _===₁_) using ()
     open NFProperty (DP.NFP.nfp (pres 1) (pres n) (nfp 1) (nfp n)) renaming (by-equal-nf to bef₁)

     f = emb2' {n}
     h = ract3
     
   
     h=⁻¹f-gen' : ∀ (x : S2 ⊎ Sn) -> ([ x ]ʷ , (ε , ε)) ~ (racts3 (ε , ε) (f x))
     h=⁻¹f-gen' (inj₁ swap) = _≈₁_.refl , Eq.refl
     h=⁻¹f-gen' (inj₂ swap) = refl , Eq.refl
     h=⁻¹f-gen' (inj₂ (y ₛ)) = refl , Eq.refl

     
     f-wd-ax : ∀ {w v} -> w ===₁ v -> (f *) w ≈₂ (f *) v
     f-wd-ax {w} {v} (left order) = axiom order
     f-wd-ax {w} {v} (right order) = axiom (congₛ (congₛ order))
     f-wd-ax {w} {v} (right comm) = axiom (congₛ (congₛ comm))
     f-wd-ax {w} {v} (right yang-baxter) = axiom (congₛ (congₛ yang-baxter))
     f-wd-ax {w} {v} (right (congₛ {w = w₁} {v₁} x)) rewrite aux-c [ w₁ ⇑] | aux-c [ v₁ ⇑] = axiom (congₛ (congₛ (congₛ x)))
     f-wd-ax {w} {v} (mid (comm swap swap)) = axiom comm
     f-wd-ax {w} {v} (mid (comm swap (b ₛ))) = axiom comm














