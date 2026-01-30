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

module Presentation.Groups.S16 where

  open import Data.Bool
  open import Data.Sum as Sum hiding (swap) 
  open import Data.Product hiding (swap)

  open import Presentation.Construct.Base
  open PB (pres 1) renaming (Alphabet to S2) using ()

  
  embed : ∀ {n} -> C n -> C (suc (suc n))
  embed {n} ε = ε
  embed {n} (swap• c) = swap• embed c

  aux2 : ∀ {n} -> C n -> C (suc n) -> Bool × (C n × C (suc n))
  aux2 {n} ε ε = false , ε , ε
  aux2 {n} ε (swap• b) = true , b , ε
  aux2 {n} (swap• a) ε = false , ((swap• a) , ε)
  aux2 {n} (swap• a) (swap• b) with aux2 a b
  ... | bl , a' , b' = bl , (swap• a') , (swap• b')

  private
    variable
      m : ℕ

  toℕ : C m -> ℕ
  toℕ ε = 0
  toℕ (swap• c) = suc (toℕ c)

  df : C m -> Set
  df c = C (toℕ c)

  CC : ℕ -> Set
  CC m = Σ (C m) df

  aux2' : ∀ {n} -> C n -> C (suc n) -> Bool × CC n
  aux2' {n} ε ε = false , ε , ε
  aux2' {n} ε (swap• d) = true , d , ε
  aux2' {n} (swap• c) ε = false , ((swap• c) , ε)
  aux2' {n} (swap• c) (swap• d) with aux2' c d
  ... | bl , c' , d' = bl , (swap• c') , (swap• d')

  eval-bool : ∀ {n} -> Bool ->
    let open PB (pres (suc (suc n))) renaming (Alphabet to Sₙ₊₂) using (_≈_) in
    Word Sₙ₊₂
  eval-bool {n} true = [ swap ]ʷ
  eval-bool {n} false = ε

  eval-bool₁ : Bool -> Word S2
  eval-bool₁ true = [ swap ]ʷ
  eval-bool₁ false = ε

  inject : ∀ {n} {i : C n} -> df i -> C n
  inject {n} {ε} ε = ε
  inject {n} {swap• i} ε = ε
  inject {n} {swap•_ {n₁} i} (swap• x) = swap• (inject x)
  
  inject₁ : ∀ {n} (i : C n) -> C (suc n)
  inject₁ {n} ε = ε
  inject₁ {n} (swap• i) = swap• (inject₁ i)


  ract' : ∀ {n} -> C (suc n) × C (suc (suc n)) -> X (suc (suc n)) ->
    let open PB (pres n) renaming (Alphabet to Sn) using () in
    let A = S2 ⊎ Sn in
    Word A × C (suc n) × C (suc (suc n))
  ract' {n} (c , d) x with ract d x
  ... | (ws , d') with racts c ws
  ... | (ws' , c') with aux2 c' d'
  ... | false , c'' , d'' = [ ws' ]ᵣ , c'' , d''
  ... | true , c'' , d'' = [ ws' ]ᵣ • [ [ swap ]ʷ ]ₗ , c'' , d''

  racts' : ∀ {n} -> C (suc n) × C (suc (suc n)) -> Word (X (suc (suc n))) ->
    let open PB (pres n) renaming (Alphabet to Sn) using () in
    let A = S2 ⊎ Sn in
    Word A × C (suc n) × C (suc (suc n))
  racts' {n} = ract' {n} **


  fm : ∀ {n} -> Word (X 1 ⊎ X n) -> Word (X 1 ⊎ X (suc n))
  fm {n} = wmap (\{ (inj₁ x) → inj₁ x ; (inj₂ y) → inj₂ (y ₛ)})

  fm' : ∀ {n} -> (X 1 ⊎ X n) -> Word (X 1 ⊎ X (suc n))
  fm' {n} (inj₁ x) = [ inj₁ x ]ʷ
  fm' {n} (inj₂ x) = [ inj₂ (x ₛ) ]ʷ


  lemma-fm3 : ∀ {n} (w : Word (X n)) -> fm [ w ]ᵣ ≡ [ [ w ⇑] ]ᵣ
  lemma-fm3 {n} [ x ]ʷ = Eq.refl
  lemma-fm3 {n} ε = Eq.refl
  lemma-fm3 {n} (w • w₁) rewrite lemma-fm3 w | lemma-fm3 w₁  = Eq.refl

  fm-cong-ax : ∀ {n} w v ->
    let open PB (pres 1 ⊕ pres n) renaming (_===_ to _===₀_) in
    let open PB (pres 1 ⊕ pres (suc n)) renaming (_≈_ to _≈₁_) in
    w ===₀ v -> fm w ≈₁ fm v
  fm-cong-ax {n} w v (left {u} {v₁} order) = PB.axiom (left order)
  fm-cong-ax {n} w v (right order) = PB.axiom (right (congₛ order))
  fm-cong-ax {n} w v (right comm) = PB.axiom (right (congₛ comm))
  fm-cong-ax {n} w v (right yang-baxter) = PB.axiom (right (congₛ yang-baxter))
  fm-cong-ax {n} w v (right (congₛ {w = w₁} {v₁} ( x))) rewrite lemma-fm3 [ w₁ ⇑] | lemma-fm3 [ v₁ ⇑] = PB.axiom (right (congₛ (congₛ x)))
  fm-cong-ax {n} w v (mid (comm swap swap)) = PB.axiom (mid (comm swap (swap ₛ)))
  fm-cong-ax {n} w v (mid (comm swap (b ₛ))) = PB.axiom (mid (comm swap ((b ₛ) ₛ)))

  fm-cong : ∀ {n} w v ->
    let open PB (pres 1 ⊕ pres n) renaming (_≈_ to _≈₀_) in
    let open PB (pres 1 ⊕ pres (suc n)) renaming (_≈_ to _≈₁_) in
    w ≈₀ v -> fm w ≈₁ fm v
  fm-cong {n} w v PB.refl = PB.refl
  fm-cong {n} w v (PB.sym eq) = PB.sym (fm-cong v w eq)
  fm-cong {n} w v (PB.trans eq eq₁) = PB.trans (fm-cong _ _ eq) (fm-cong _ _ eq₁)
  fm-cong {n} w v (PB.cong eq eq₁) = PB.cong (fm-cong _ _ eq) (fm-cong _ _ eq₁)
  fm-cong {n} w v PB.assoc = PB.assoc
  fm-cong {n} w v PB.left-unit = PB.left-unit
  fm-cong {n} w v PB.right-unit = PB.right-unit
  fm-cong {n} w v (PB.axiom x) = fm-cong-ax w v x



  ract'' : ∀ {n} -> CC (suc n) -> X (suc (suc n)) ->
    let open PB (pres n) renaming (Alphabet to Sn) using () in
    let A = S2 ⊎ Sn in
    Word A × CC (suc n)
  ract'' {n} (c , d) x with ract (inject₁ (inject d)) x
  ... | (ws , d') with racts c ws
  ... | (ws' , c') with aux2' c' d'
  ... | b , c'' , d'' = [ ws' ]ᵣ • [ eval-bool₁ b ]ₗ , c'' , d''

  fm2 : ∀ {n} -> ((c , d) : CC (suc n)) -> CC n
  fm2 {n} (c , d) = ε , ε

  ract3 : ∀ {n} -> CC (suc n) -> X (suc (suc n)) ->
    let open PB (pres n) renaming (Alphabet to Sn) using () in
    let A = S2 ⊎ Sn in
    Word A × CC (suc n)
  ract3 {n} (ε , ε) swap = [ [ swap ]ʷ ]ₗ , (ε , ε)
  ract3 {n} (ε , ε) (swap ₛ) = ε , (swap• ε , ε)
  ract3 {n} (ε , ε) ((x ₛ) ₛ) = [ [ x ]ʷ ]ᵣ , (ε , ε)
  
  ract3 {n} (swap• c , ε) swap = ε , (swap• c , swap• ε)
  ract3 {n} (swap• ε , ε) (swap ₛ) = ε , (ε , ε)
  ract3 {n} (swap• ε , ε) ((swap ₛ) ₛ) = ε , (swap• swap• ε , ε)
  ract3 {n} (swap• ε , ε) (((x ₛ) ₛ) ₛ) = [ [ x ₛ ]ʷ ]ᵣ , (swap• ε , ε)
  ract3 {n} (swap• swap• c , ε) (swap ₛ) = [ [ swap ]ʷ ]ᵣ , (swap• swap• c , ε)
  ract3 {n} (swap• swap• c , ε) ((x ₛ ₛ)) with ract3 (swap• c , ε) (x ₛ)
  ... | (w , (c' , d')) = fm w , swap• c' , ε
  
  -- The followin two should be combined as "ract3 {n} (swap• c , swap• ε) swap = {!!}", but for some reason, it won't type check.
  ract3 {n} (swap• ε , swap• ε) swap = ε , (swap• ε , ε)
  ract3 {n} (swap• swap• c , swap• ε) swap = ε , (swap• swap• c , ε)
  ract3 {n} (swap• swap• c , swap• swap• d) swap = [ [ swap ]ʷ ]ᵣ , (swap• swap• c , swap• swap• d)

  ract3 {n} (swap• ε , swap• ε) (swap ₛ) = [ [ swap ]ʷ ]ₗ , (swap• ε , swap• ε)
  ract3 {suc n} (swap• c , swap• d) (x ₛ) with ract3 (c , d) x
  ... | (w , (c' , d')) = fm w , swap• c' , swap• d'


  ler3 : ∀ {n} (c : C n) (d : C (suc (toℕ c))) x ->
    let (w , (c' , d')) = ract3 ((swap• c),  ( d)) (x ₛ) in
    ract3 ((swap• swap• c) , (swap• ( d))) (x ₛ ₛ) ≡ (fm w , ((swap• c') , (swap• d')))
  ler3 {n} ε ε x = Eq.refl
  ler3 {n} ε (swap• ε) x = Eq.refl
  ler3 {n} (swap• c) ε x = Eq.refl
  ler3 {n} (swap• ε) (swap• ε) x = Eq.refl
  ler3 {n} (swap• ε) (swap• swap• d) x = Eq.refl
  ler3 {n} (swap• swap• c) (swap• ε) x = Eq.refl
  ler3 {n} (swap• swap• c) (swap• swap• d) x = Eq.refl


  racts'' : ∀ {n} -> CC (suc n) -> Word (X (suc (suc n))) ->
    let open PB (pres n) renaming (Alphabet to Sn) using () in
    let A = S2 ⊎ Sn in
    Word A × CC (suc n)
  racts'' {n} = ract'' {n} **

  racts2 : ∀ {n} -> CC (suc n) -> Word (X (suc (suc n))) ->
    let open PB (pres n) renaming (Alphabet to Sn) using () in
    let A = S2 ⊎ Sn in
    Word A × CC (suc n)
  racts2 {n} (c , d) w with racts (inject₁ (inject d)) w
  ... | (ws , d') with racts c ws
  ... | (ws' , c') with aux2' c' d'
  ... | b , c'' , d'' = [ ws' ]ᵣ • [ eval-bool₁ b ]ₗ , c'' , d''


  racts3 : ∀ {n} -> CC (suc n) -> Word (X (suc (suc n))) ->
    let open PB (pres n) renaming (Alphabet to Sn) using () in
    let A = S2 ⊎ Sn in
    Word A × CC (suc n)
  racts3 {n} = ract3 {n} **


  ler4 : ∀ {n} (c : C (suc n)) (d : df c) w ->
    let (w' , (c' , d')) = racts3 (c , d) w in
    racts3 (swap• c , swap• d) [ w ⇑] ≡ (fm w' , swap• c' , swap• d')
  ler4 {zero} ε ε [ swap ]ʷ = Eq.refl
  ler4 {zero} ε ε [ x ₛ ]ʷ = Eq.refl
  ler4 {zero} (swap• c) ε [ x ]ʷ = Eq.refl
  ler4 {zero} (swap• c) (swap• d) [ x ]ʷ = Eq.refl
  ler4 {suc n} ε ε [ swap ]ʷ = Eq.refl
  ler4 {suc n} (swap• c) ε [ swap ]ʷ = Eq.refl
  ler4 {suc n} (swap• c) (swap• d) [ swap ]ʷ = Eq.refl
  ler4 {suc n} ε ε [ x ₛ ]ʷ = Eq.refl
  ler4 {suc n} (swap• c) ε [ x ₛ ]ʷ = Eq.refl
  ler4 {suc n} (swap• c) (swap• d) [ x ₛ ]ʷ = Eq.refl
  ler4 {n} c d ε = Eq.refl
  ler4 {n} c d (w • v) =
    let (ww , cw , dw) = racts3 (c , d) w in
    let (vv , cv , dv) = racts3 (cw , dw) v in
    let (w' , c' , d') = racts3 (swap• c , swap• d) [ w ⇑] in
    begin
      racts3 (swap• c , swap• d) [ w • v ⇑] ≡⟨ Eq.refl ⟩
      w' • racts3 (c' , d') [ v ⇑] .proj₁ , racts3 (c' , d') [ v ⇑] .proj₂ ≡⟨ Eq.cong (\x -> x • racts3 (c' , d') [ v ⇑] .proj₁ , racts3 (c' , d') [ v ⇑] .proj₂) (Eq.cong proj₁ (ler4 c d w)) ⟩
      fm ww • racts3 (c' , d') [ v ⇑] .proj₁ , racts3 (c' , d') [ v ⇑] .proj₂ ≡⟨ Eq.cong (\x -> fm ww • racts3 (x) [ v ⇑] .proj₁ , racts3 (x) [ v ⇑] .proj₂) (Eq.cong (proj₂) (ler4 c d w)) ⟩
      fm ww • racts3 (swap• cw , swap• dw) [ v ⇑] .proj₁ , racts3 (swap• cw , swap• dw) [ v ⇑] .proj₂ ≡⟨ Eq.cong₂ (λ x y → fm ww • x , y) (Eq.cong proj₁ (ler4 cw dw v)) (Eq.cong proj₂ (ler4 cw dw v)) ⟩
      fm ww • fm vv , swap• cv , swap• dv ∎
    where
    open Eq.≡-Reasoning


  lel5b : ∀ {n} (c : C (suc n)) w ->
    ∃ \ w' -> ∃ \c' -> racts3 {suc n}(swap• c , ε) [ [ w ⇑] ⇑] ≡ ([ [ w' ⇑] ]ᵣ , swap• c' , ε)
  lel5b {n} ε [ swap ]ʷ = ε , swap• ε , Eq.refl
  lel5b {n} ε [ swap ₛ ]ʷ = [ swap ]ʷ , (ε , Eq.refl)
  lel5b {n} ε [ (x ₛ) ₛ ]ʷ = [ x ₛ ]ʷ , (ε , Eq.refl)
  lel5b {n} ε ε = ε , ε , Eq.refl
  lel5b {n} ε (w • v) with lel5b ε w
  ... | w' , cw , pw with lel5b cw v
  ... | v' , cv , pv rewrite pw | pv = w' • v' , cv , Eq.refl
  lel5b {n} (swap• ε) [ swap ]ʷ = ε , (ε , Eq.refl)
  lel5b {n} (swap• swap• c) [ swap ]ʷ = [ swap ]ʷ , ((swap• swap• c) , Eq.refl)
  lel5b {suc n} (swap• c) [ x ₛ ]ʷ with ract3 (swap• c , ε) (x ₛ ₛ) | lel5b c [ x ]ʷ
  ... | (w' , c' , d') | (w'' , c'' , pr) rewrite Eq.cong proj₁ pr | lemma-fm3 [ w'' ⇑]  =  [ w'' ⇑] , (swap• c'') , ≡×≡⇒≡ (Eq.refl , Eq.cong (λ x → swap• x , ε) (Eq.cong (proj₁ ∘ proj₂) pr) )
  lel5b {n} (swap• c) ε = ε , swap• c , Eq.refl
  lel5b {n} (swap• c) (w • v) with lel5b (swap• c) w
  ... | w' , cw , pw with lel5b cw v
  ... | v' , cv , pv rewrite pw | pv = w' • v' , cv , Eq.refl




  aux3a : ∀ {n} c x ->
    let open PB (pres n) renaming (Alphabet to Sn ; _≈_ to _≈ₙ_) using () in
    let open PB (pres (suc (suc n))) renaming (Alphabet to Sₙ₊₂) using (_≈_) in
    let (x' , c') = ract3 {n} (c , ε) (x ₛ) in c' .proj₂ ≡ ε
  aux3a {n} ε swap = Eq.refl
  aux3a {n} (swap• ε) swap = Eq.refl
  aux3a {n} (swap• swap• c) swap = Eq.refl
  aux3a {n} ε (swap ₛ) = Eq.refl
  aux3a {n} ε ((x ₛ) ₛ) = Eq.refl
  aux3a {n} (swap• ε) (swap ₛ) = Eq.refl
  aux3a {n} (swap• ε) ((x ₛ) ₛ) = Eq.refl
  aux3a {n} (swap• swap• c) (swap ₛ) = Eq.refl
  aux3a {n} (swap• swap• c) ((x ₛ) ₛ) = Eq.refl









  ler5b : ∀ {n} (c : C ( n)) w ->
    ∃ \w' -> ∃ \c' -> racts3 (swap• c , ε) [ [ w ⇑] ⇑] ≡ (w' , swap• c' , ε)
  ler5b {n} ε [ swap ]ʷ = ε , swap• ε , Eq.refl
  ler5b {n} ε [ x ₛ ]ʷ = [ [ x ₛ ]ʷ ]ᵣ , ε , Eq.refl
  ler5b {n} ε ε = ε , ε , Eq.refl
  ler5b {n} ε (w • v) with ler5b ε w
  ... | w' , cw , pw with ler5b cw v
  ... | v' , cv , pv rewrite pw | pv = w' • v' , cv , Eq.refl
  ler5b {n} (swap• c) [ swap ]ʷ = fm (ract3 (swap• c , ε) (swap ₛ) .proj₁) ,
                                    ract3 (swap• c , ε) (swap ₛ) .proj₂ .proj₁ , Eq.refl
  ler5b {n} (swap• c) [ x ₛ ]ʷ = fm (ract3 (swap• c , ε) ((x ₛ) ₛ) .proj₁) ,
                                   ract3 (swap• c , ε) ((x ₛ) ₛ) .proj₂ .proj₁ , Eq.refl
  ler5b {n} (swap• c) ε = ε , swap• c , Eq.refl
  ler5b {n} (swap• c) (w • v) with ler5b (swap• c) w
  ... | w' , cw , pw with ler5b cw v
  ... | v' , cv , pv rewrite pw | pv = w' • v' , cv , Eq.refl


  ler5c : ∀ {n} (c : C (suc n)) w ->
    ∃ \w' -> ∃ \c' -> racts3 (c , ε) [ w ⇑] ≡ (w' , c' , ε)
  ler5c {n} ε [ swap ]ʷ = ε , swap• ε , Eq.refl
  ler5c {n} (swap• ε) [ swap ]ʷ = ε , ε , Eq.refl
  ler5c {n} (swap• swap• c) [ swap ]ʷ = [ [ swap ]ʷ ]ᵣ , swap• swap• c , Eq.refl
  ler5c {n} ε [ swap ₛ ]ʷ = [ [ swap ]ʷ ]ᵣ , ε , Eq.refl
  ler5c {n} (swap• ε) [ swap ₛ ]ʷ = ε , swap• swap• ε , Eq.refl
  ler5c {n} (swap• swap• c) [ swap ₛ ]ʷ = fm (ract3 (swap• c , ε) (swap ₛ) .proj₁) ,
                                            swap• ract3 (swap• c , ε) (swap ₛ) .proj₂ .proj₁ , Eq.refl
  ler5c {n} ε [ (x ₛ) ₛ ]ʷ = [ [ x ₛ ]ʷ ]ᵣ , ε , Eq.refl
  ler5c {n} (swap• ε) [ (swap ₛ) ₛ ]ʷ = [ [ swap ₛ ]ʷ ]ᵣ , swap• ε , Eq.refl
  ler5c {n} (swap• ε) [ ((x ₛ) ₛ) ₛ ]ʷ = [ [ (x ₛ) ₛ ]ʷ ]ᵣ , swap• ε , Eq.refl
  ler5c {n} (swap• swap• c) [ (swap ₛ) ₛ ]ʷ = fm (ract3 (swap• c , ε) ((swap ₛ) ₛ) .proj₁) ,
                                                swap• ract3 (swap• c , ε) ((swap ₛ) ₛ) .proj₂ .proj₁ , Eq.refl
  ler5c {n} (swap• swap• c) [ ((x ₛ) ₛ) ₛ ]ʷ = fm (ract3 (swap• c , ε) (((x ₛ) ₛ) ₛ) .proj₁) ,
                                                 swap• ract3 (swap• c , ε) (((x ₛ) ₛ) ₛ) .proj₂ .proj₁ , Eq.refl
  ler5c {n} c ε = ε , c , Eq.refl
  ler5c {n} c (w • v) with ler5c (c) w
  ... | w' , cw , pw with ler5c cw v
  ... | v' , cv , pv rewrite pw | pv = w' • v' , cv , Eq.refl

  ler5d : ∀ {n} (c : C (suc n)) w ->
    racts3 (c , ε) [ w ⇑] .proj₂ .proj₂ ≡ ε
  ler5d {n} c w with ler5c c w
  ... | w' , c' , pr rewrite pr = Eq.refl


  ler6 : ∀ {n} (c : C (suc n)) w ->
    let (w' , (c' , d')) = racts3 (c , ε) [ w ⇑] in
    racts3 (swap• swap• c , ε) [ [ [ w ⇑] ⇑] ⇑] ≡ (fm (fm w') , swap• swap• c' , ε)
  ler6 ε [ swap ]ʷ = Eq.refl
  ler6 (swap• c) [ swap ]ʷ = Eq.refl
  ler6 ε [ x ₛ ]ʷ = Eq.refl
  ler6 (swap• c) [ x ₛ ]ʷ = Eq.refl
  ler6 c ε = Eq.refl

  ler6 c (w • v) = 
    let (ww , cw , dw) = racts3 ( c , ε) [ w ⇑] in
    let (vv , cv , dv) = racts3 (cw , ε) [ v ⇑] in
    let (w' , c' , d') = racts3 ( swap• swap• c , ε) [ [ [ w ⇑] ⇑] ⇑] in
    let (w'' , c'' , d'') = racts3 ( c , ε) [ w • v ⇑] in
    begin
      racts3 (swap• swap• c , ε) [ [ [ w • v ⇑] ⇑] ⇑] ≡⟨ Eq.refl ⟩
      racts3 (swap• swap• c , ε) [ [ [ w  ⇑] ⇑] ⇑] .proj₁ • racts3 (racts3 (swap• swap• c , ε) [ [ [ w  ⇑] ⇑] ⇑] .proj₂) [ [ [ v ⇑] ⇑] ⇑] .proj₁ , racts3 (racts3 (swap• swap• c , ε) [ [ [ w  ⇑] ⇑] ⇑] .proj₂) [ [ [ v ⇑] ⇑] ⇑] .proj₂ ≡⟨ Eq.refl ⟩
      w' • racts3 (c' , d') [ [ [ v ⇑] ⇑] ⇑] .proj₁ , racts3 (c' , d') [ [ [ v ⇑] ⇑] ⇑] .proj₂ ≡⟨ Eq.cong
                                                                                                    (λ x →
                                                                                                       x • racts3 (c' , d') [ [ [ v ⇑] ⇑] ⇑] .proj₁ ,
                                                                                                       racts3 (c' , d') [ [ [ v ⇑] ⇑] ⇑] .proj₂)
                                                                                                    (Eq.cong proj₁ (ler6 c w)) ⟩
      fm (fm ww) • racts3 (c' , d') [ [ [ v ⇑] ⇑] ⇑] .proj₁ , racts3 (c' , d') [ [ [ v ⇑] ⇑] ⇑] .proj₂ ≡⟨ Eq.cong
                                                                                                            (λ x →
                                                                                                               fm (fm ww) • racts3 x [ [ [ v ⇑] ⇑] ⇑] .proj₁ ,
                                                                                                               racts3 x [ [ [ v ⇑] ⇑] ⇑] .proj₂)
                                                                                                            (Eq.cong proj₂ (ler6 c w)) ⟩
      fm (fm ww) • racts3 (swap• swap• cw , ε) [ [ [ v ⇑] ⇑] ⇑] .proj₁ , racts3 (swap• swap• cw , ε) [ [ [ v ⇑] ⇑] ⇑] .proj₂ ≡⟨ Eq.cong₂ (λ x y → fm (fm ww) • x , y) (Eq.cong proj₁ (ler6 cw v)) (Eq.cong proj₂ (ler6 cw v)) ⟩
      fm (fm ww) • fm (fm vv) , (swap• swap• cv , ε) ≡⟨ Eq.refl ⟩
      fm (fm (ww • vv)) , (swap• swap• cv , ε) ≡⟨ Eq.refl ⟩
      fm (fm (ww • racts3 (cw , ε) [ v ⇑] .proj₁)) , swap• swap• (racts3 (cw , ε) [ v ⇑] .proj₂ .proj₁) , ε ≡⟨ Eq.cong
                                                                                                                 (λ x →
                                                                                                                    fm (fm (ww • racts3 (cw , x) [ v ⇑] .proj₁)) ,
                                                                                                                    swap• swap• racts3 (cw , x) [ v ⇑] .proj₂ .proj₁ , ε)
                                                                                                                 (Eq.sym (ler5d c w)) ⟩
      fm (fm (ww • racts3 (cw , dw) [ v ⇑] .proj₁)) , swap• swap• (racts3 (cw , dw) [ v ⇑] .proj₂ .proj₁) , ε ≡⟨ Eq.refl ⟩
      fm (fm w'') , swap• swap• c'' , ε ∎
    where
    open Eq.≡-Reasoning



  [_]' : ∀ {n} -> C (suc n) × C (suc (suc n)) -> 
    let open PB (pres n) renaming (Alphabet to Sn ; _≈_ to _≈ₙ_) using () in
    let open PB (pres (suc (suc n))) renaming (Alphabet to Sₙ₊₂) using (_≈_) in
    Word Sₙ₊₂
  [_]' {n} (c , d) = [ [ c ] ⇑] • [ d ]

  [_]'' : ∀ {n} -> CC (suc n) -> 
    let open PB (pres n) renaming (Alphabet to Sn ; _≈_ to _≈ₙ_) using () in
    let open PB (pres (suc (suc n))) renaming (Alphabet to Sₙ₊₂) using (_≈_) in
    Word Sₙ₊₂
  [_]'' {n} (c , d) = [ [ c ] ⇑] • [ inject₁ (inject d) ]


  [_]₃ : ∀ {n} -> CC (suc n) -> 
    let open PB (pres n) renaming (Alphabet to Sn ; _≈_ to _≈ₙ_) using () in
    let open PB (pres (suc (suc n))) renaming (Alphabet to Sₙ₊₂) using (_≈_) in
    Word Sₙ₊₂
  [_]₃ {n} (c , d) = [ [ c ] ⇑] • [ inject₁ (inject d) ]


  open PB hiding (_≈_)

  lemma-aux2 : ∀ {n} -> (c : C (suc n)) -> (d : C (suc (suc n))) ->
    let (b , c' , d') = aux2 {suc n} c d in
    let open PB (pres (suc (suc n))) renaming (Alphabet to Sₙ₊₂) using (_≈_) in
    [ c , d ]' ≈ eval-bool b • [ c' , d' ]'
  lemma-aux2 {n} ε ε = _≈_.sym _≈_.left-unit
    where
      open PB (pres (suc (suc n))) renaming (Alphabet to Sₙ₊₂) using (_≈_)
      open PP (pres (suc (suc n))) renaming (word-setoid to ws) using ()
      open SR ws
  lemma-aux2 {n} ε (swap• d) = begin
    [ ε , swap• d ]' ≈⟨ _≈_.refl ⟩
    ε • [ swap ]ʷ • wconcat (wmap (λ x → [ x ₛ ]ʷ) [ d ]) ≈⟨ _≈_.left-unit ⟩
    [ swap ]ʷ • wconcat (wmap (λ x → [ x ₛ ]ʷ) [ d ]) ≈⟨ _≈_.cong _≈_.refl (_≈_.sym _≈_.right-unit) ⟩
    [ swap ]ʷ • [ d , ε ]' ∎
    where
      open PB (pres (suc (suc n))) renaming (Alphabet to Sₙ₊₂) using (_≈_)
      open PP (pres (suc (suc n))) renaming (word-setoid to ws) using ()
      open SR ws
  lemma-aux2 {n} (swap• c) ε = _≈_.sym _≈_.left-unit
    where
      open PB (pres (suc (suc n))) renaming (Alphabet to Sₙ₊₂) using (_≈_)
      open PP (pres (suc (suc n))) renaming (word-setoid to ws) using ()
      open SR ws
  lemma-aux2 {zero} (swap• ε) (swap• ε) = PB.sym PB.left-unit
  lemma-aux2 {n@zero} (swap• ε) (swap• swap• ε) = begin
    [ swap• ε , swap• swap• ε ]' ≈⟨ _≈_.refl ⟩
    ([ swap ₛ ]ʷ • ε) • [ swap ]ʷ • [ swap ₛ ]ʷ • ε ≈⟨ _≈_.cong _≈_.right-unit (_≈_.sym _≈_.assoc) ⟩
    ([ swap ₛ ]ʷ) • ([ swap ]ʷ • [ swap ₛ ]ʷ) • ε ≈⟨ _≈_.cong _≈_.refl _≈_.right-unit ⟩
    ([ swap ₛ ]ʷ) • ([ swap ]ʷ • [ swap ₛ ]ʷ) ≈⟨ _≈_.sym (_≈_.axiom yang-baxter) ⟩
    ([ swap ]ʷ) • ([ swap ₛ ]ʷ • [ swap ]ʷ) ≈⟨ cong refl (_≈_.sym (_≈_.cong _≈_.right-unit _≈_.right-unit)) ⟩
    [ swap ]ʷ • [ swap• ε , swap• ε ]' ∎
    where
      open PB (pres (suc (suc n))) renaming (Alphabet to Sₙ₊₂) using (_≈_)
      open PP (pres (suc (suc n))) renaming (word-setoid to ws) using ()
      open SR ws
  lemma-aux2 {n'@(suc n)} (swap• c) (swap• d) with aux2 (c) (d) | lemma-aux2 c d
  ... | (b'@false , c'' , d'') | ih = let b = b' in let c' = swap• c'' in let d' = swap• d'' in begin
    [ swap• c , swap• d ]' ≈⟨ _≈_.refl ⟩
    [ [ swap• c ] ⇑] • [ swap• d ] ≈⟨ _≈_.assoc ⟩
    [ swap ₛ ]ʷ • [ [ [ c ] ⇑] ⇑] • ([ swap ]ʷ • [ [ d ] ⇑]) ≈⟨ _≈_.sym (_≈_.cong _≈_.refl _≈_.assoc) ⟩
    [ swap ₛ ]ʷ • ([ [ [ c ] ⇑] ⇑] • [ swap ]ʷ) • [ [ d ] ⇑] ≈⟨ cong refl (cong (lemma-comm [ c ]) refl) ⟩
    [ swap ₛ ]ʷ • ([ swap ]ʷ • [ [ [ c ] ⇑] ⇑]) • [ [ d ] ⇑] ≈⟨ _≈_.cong _≈_.refl _≈_.assoc ⟩
    [ swap ₛ ]ʷ • [ swap ]ʷ • [ [ [ c ] ⇑] ⇑] • [ [ d ] ⇑] ≈⟨ _≈_.refl ⟩
    [ swap ₛ ]ʷ • [ swap ]ʷ • [ [ [ c ] ⇑] • [ d ] ⇑] ≈⟨ _≈_.refl ⟩
    [ swap ₛ ]ʷ • [ swap ]ʷ • [ [ c , d ]' ⇑] ≈⟨ cong refl (cong refl ([⇑]-cong [ c , d ]' (eval-bool b' • [ c'' , d'' ]') ih)) ⟩
    [ swap ₛ ]ʷ • [ swap ]ʷ • [ eval-bool b' • [ c'' , d'' ]' ⇑] ≈⟨ cong refl (cong refl _≈_.refl) ⟩
    [ swap ₛ ]ʷ • [ swap ]ʷ • [ ε • [ c'' , d'' ]' ⇑] ≈⟨ cong refl (cong refl _≈_.left-unit) ⟩
    [ swap ₛ ]ʷ • [ swap ]ʷ • [ [ c'' , d'' ]' ⇑] ≈⟨ _≈_.refl ⟩
    [ swap ₛ ]ʷ • [ swap ]ʷ • [ [ [ c'' ] ⇑] • [ d'' ] ⇑] ≈⟨ _≈_.sym (_≈_.cong _≈_.refl _≈_.assoc) ⟩
    [ swap ₛ ]ʷ • ([ swap ]ʷ • [ [ [ c'' ] ⇑] ⇑]) • [ [ d'' ] ⇑] ≈⟨ cong refl (cong (sym (lemma-comm [ c'' ])) refl) ⟩
    [ swap ₛ ]ʷ • ([ [ [ c'' ] ⇑] ⇑] • [ swap ]ʷ) • [ [ d'' ] ⇑] ≈⟨ _≈_.cong _≈_.refl _≈_.assoc ⟩
    [ swap ₛ ]ʷ • [ [ [ c'' ] ⇑] ⇑] • [ swap ]ʷ • [ [ d'' ] ⇑] ≈⟨ _≈_.sym _≈_.assoc ⟩
    ([ swap ₛ ]ʷ • [ [ [ c'' ] ⇑] ⇑]) • [ swap ]ʷ • [ [ d'' ] ⇑] ≈⟨ _≈_.refl ⟩
    [ swap• c'' , swap• d'' ]' ≈⟨ _≈_.sym _≈_.left-unit ⟩
    ε • [ swap• c'' , swap• d'' ]' ≈⟨ _≈_.refl ⟩
    ε • [ c' , d' ]' ≈⟨ _≈_.refl ⟩
    eval-bool b • [ c' , d' ]' ∎
    where
      open PB (pres (suc (suc n'))) renaming (Alphabet to Sₙ₊₂) using (_≈_)
      open PP (pres (suc (suc n'))) renaming (word-setoid to ws) using ()
      open SR ws
  ... | (b'@true , c'' , d'') | ih = let b = b' in let c' = swap• c'' in let d' = swap• d'' in begin
    [ swap• c , swap• d ]' ≈⟨ _≈_.refl ⟩
    [ [ swap• c ] ⇑] • [ swap• d ] ≈⟨ _≈_.assoc ⟩
    [ swap ₛ ]ʷ • [ [ [ c ] ⇑] ⇑] • ([ swap ]ʷ • [ [ d ] ⇑]) ≈⟨ _≈_.sym (_≈_.cong _≈_.refl _≈_.assoc) ⟩
    [ swap ₛ ]ʷ • ([ [ [ c ] ⇑] ⇑] • [ swap ]ʷ) • [ [ d ] ⇑] ≈⟨ cong refl (cong (lemma-comm [ c ]) refl) ⟩
    [ swap ₛ ]ʷ • ([ swap ]ʷ • [ [ [ c ] ⇑] ⇑]) • [ [ d ] ⇑] ≈⟨ _≈_.cong _≈_.refl _≈_.assoc ⟩
    [ swap ₛ ]ʷ • [ swap ]ʷ • [ [ [ c ] ⇑] ⇑] • [ [ d ] ⇑] ≈⟨ _≈_.refl ⟩
    [ swap ₛ ]ʷ • [ swap ]ʷ • [ [ [ c ] ⇑] • [ d ] ⇑] ≈⟨ _≈_.refl ⟩
    [ swap ₛ ]ʷ • [ swap ]ʷ • [ [ c , d ]' ⇑] ≈⟨ cong refl (cong refl ([⇑]-cong [ c , d ]' (eval-bool b' • [ c'' , d'' ]') ih)) ⟩
    [ swap ₛ ]ʷ • [ swap ]ʷ • [ eval-bool b' • [ c'' , d'' ]' ⇑] ≈⟨ cong refl (cong refl _≈_.refl) ⟩
    [ swap ₛ ]ʷ • [ swap ]ʷ • [ [ swap ]ʷ • [ c'' , d'' ]' ⇑] ≈⟨ _≈_.refl ⟩
    [ swap ₛ ]ʷ • [ swap ]ʷ • [ swap ₛ ]ʷ • [ [ c'' , d'' ]' ⇑] ≈⟨ sym (trans assoc (cong refl _≈_.assoc)) ⟩
    ([ swap ₛ ]ʷ • [ swap ]ʷ • [ swap ₛ ]ʷ) • [ [ c'' , d'' ]' ⇑] ≈⟨ cong (_≈_.sym (_≈_.axiom yang-baxter)) refl ⟩
    ([ swap ]ʷ • [ swap ₛ ]ʷ • [ swap ]ʷ) • [ [ c'' , d'' ]' ⇑] ≈⟨ cong refl _≈_.refl ⟩
    ([ swap ]ʷ • [ swap ₛ ]ʷ • [ swap ]ʷ) • [ [ [ c'' ] ⇑] • [ d'' ] ⇑] ≈⟨ (trans assoc (cong refl _≈_.assoc)) ⟩
    [ swap ]ʷ • [ swap ₛ ]ʷ • [ swap ]ʷ • [ [ [ c'' ] ⇑] • [ d'' ] ⇑] ≈⟨ _≈_.refl ⟩
    [ swap ]ʷ • [ swap ₛ ]ʷ • [ swap ]ʷ • [ [ [ c'' ] ⇑] ⇑] • [ [ d'' ] ⇑] ≈⟨ cong refl (cong refl (_≈_.sym _≈_.assoc)) ⟩
    [ swap ]ʷ • [ swap ₛ ]ʷ • ([ swap ]ʷ • [ [ [ c'' ] ⇑] ⇑]) • [ [ d'' ] ⇑] ≈⟨ cong refl (cong refl (cong (sym (lemma-comm [ c'' ])) refl)) ⟩
    [ swap ]ʷ • [ swap ₛ ]ʷ • ([ [ [ c'' ] ⇑] ⇑] • [ swap ]ʷ) • [ [ d'' ] ⇑] ≈⟨ cong refl (cong refl _≈_.assoc) ⟩
    [ swap ]ʷ • [ swap ₛ ]ʷ • [ [ [ c'' ] ⇑] ⇑] • [ swap ]ʷ • [ [ d'' ] ⇑] ≈⟨ _≈_.sym (_≈_.cong _≈_.refl _≈_.assoc) ⟩
    [ swap ]ʷ • ([ swap ₛ ]ʷ • [ [ [ c'' ] ⇑] ⇑]) • [ swap ]ʷ • [ [ d'' ] ⇑] ≈⟨ _≈_.refl ⟩
    [ swap ]ʷ • [ swap• c'' , swap• d'' ]' ≈⟨ _≈_.refl ⟩
    [ swap ]ʷ • [ c' , d' ]' ≈⟨ _≈_.refl ⟩
    eval-bool b • [ c' , d' ]' ∎
    where
      open PB (pres (suc (suc n'))) renaming (Alphabet to Sₙ₊₂) using (_≈_)
      open PP (pres (suc (suc n'))) renaming (word-setoid to ws) using ()
      open SR ws

  lemma-aux2-aux2' : ∀ {n} -> (c : C (suc n)) -> (d : C (suc (suc n))) ->
    let (b , cd') = aux2' {suc n} c d in
    let (b1 , c1 , d1) = aux2 {suc n} c d in
    let open PB (pres (suc (suc n))) renaming (Alphabet to Sₙ₊₂) using (_≈_) in
    b1 ≡ b × [ c1 , d1 ]' ≈ [ cd' ]''
  lemma-aux2-aux2' {n} ε ε = Eq.refl , refl
  lemma-aux2-aux2' {zero} ε (swap• ε) = Eq.refl , refl
  lemma-aux2-aux2' {zero} ε (swap• swap• d') = Eq.refl , refl
  lemma-aux2-aux2' {(suc n')} ε (swap• ε) = Eq.refl , refl
  lemma-aux2-aux2' {(suc n')} ε (swap• swap• d') = Eq.refl , refl
  lemma-aux2-aux2' {n} (swap• c) ε = Eq.refl , refl
  lemma-aux2-aux2' {zero} (swap• ε) (swap• ε) = Eq.refl , refl
  lemma-aux2-aux2' {zero} (swap• ε) (swap• swap• ε) = Eq.refl , refl
  lemma-aux2-aux2' {n@(suc n')} (swap• c) (swap• d) with aux2' c d | aux2 c d | lemma-aux2-aux2' c d
  ... | (b , c' , d') | (b1 , c1 , d1) | (h1 , h2) = h1 , claim2
    where
      open PB (pres (suc (suc n))) renaming (Alphabet to Sₙ₊₂) using (_≈_)
      open PB (pres (suc (suc n'))) renaming (Alphabet to Sₙ₊₂ ; _≈_ to _≈₀_) using ()
      open PP (pres (suc (suc n))) renaming (word-setoid to wsh) using ()
      open SR wsh
      claim : [ c1 , d1 ]' ≈₀ [ c' , d' ]''
      claim = h2

      claim2 : [ swap• c1 , swap• d1 ]' ≈ [ swap• c' , swap• d' ]''
      claim2 = begin
        [ swap• c1 , swap• d1 ]' ≈⟨ refl ⟩
        ([ [ swap• c1 ] ⇑]) • [ swap ]ʷ • [ [ d1 ] ⇑] ≈⟨ refl ⟩
        ([ swap ₛ ]ʷ • [ [ [ c1 ] ⇑] ⇑]) • [ swap ]ʷ • [ [ d1 ] ⇑] ≈⟨ trans assoc (sym (cong refl assoc)) ⟩
        [ swap ₛ ]ʷ • ([ [ [ c1 ] ⇑] ⇑] • [ swap ]ʷ) • [ [ d1 ] ⇑] ≈⟨ cong refl (cong (lemma-comm [ c1 ]) refl) ⟩
        [ swap ₛ ]ʷ • ([ swap ]ʷ • [ [ [ c1 ] ⇑] ⇑]) • [ [ d1 ] ⇑] ≈⟨ cong refl assoc ⟩
        [ swap ₛ ]ʷ • [ swap ]ʷ • [ [ [ c1 ] ⇑] ⇑] • [ [ d1 ] ⇑] ≈⟨ refl ⟩
        [ swap ₛ ]ʷ • [ swap ]ʷ • [ [ [ c1 ] ⇑] • [ d1 ] ⇑] ≈⟨ cong refl (cong refl ([⇑]-cong _ _ h2)) ⟩
        [ swap ₛ ]ʷ • [ swap ]ʷ • [ [ c' , d' ]'' ⇑] ≈⟨ refl ⟩
        [ swap ₛ ]ʷ • [ swap ]ʷ • [ [ [ c' ] ⇑] ⇑] • [ [ inject₁ (inject d') ] ⇑] ≈⟨ sym (cong refl assoc) ⟩
        [ swap ₛ ]ʷ • ([ swap ]ʷ • [ [ [ c' ] ⇑] ⇑]) • [ [ inject₁ (inject d') ] ⇑] ≈⟨ cong refl (cong (sym (lemma-comm [ c' ])) refl) ⟩
        [ swap ₛ ]ʷ • ([ [ [ c' ] ⇑] ⇑] • [ swap ]ʷ) • [ [ inject₁ (inject d') ] ⇑] ≈⟨ sym (trans assoc (sym (cong refl assoc))) ⟩
        ([ swap ₛ ]ʷ • [ [ [ c' ] ⇑] ⇑]) • [ swap ]ʷ • [ [ inject₁ (inject d') ] ⇑] ≈⟨ refl ⟩
        [ swap• c' , swap• d' ]'' ∎

  lemma-aux2' : ∀ {n} -> (c : C (suc n)) -> (d : C (suc (suc n))) ->
    let (b , cd') = aux2' {suc n} c d in
    let open PB (pres (suc (suc n))) renaming (Alphabet to Sₙ₊₂) using (_≈_) in
    [ c , d ]' ≈ eval-bool b • [ cd' ]''
  lemma-aux2' {n} c d with aux2' c d | aux2 c d | lemma-aux2-aux2' c d | lemma-aux2 c d
  ... | (b , cd') | (b1 , c1 , d1) | (h1 , h2) | h3 = begin
    [ c , d ]' ≈⟨ h3 ⟩
    eval-bool b1 • [ c1 , d1 ]' ≈⟨ (cong (refl' _ (Eq.cong _ h1)) h2) ⟩
    eval-bool b • [ cd' ]'' ∎
    where
      open PB (pres (suc (suc n))) renaming (Alphabet to Sₙ₊₂) using (_≈_)
      open PP (pres (suc (suc n))) renaming (word-setoid to wsh) using ()
      open SR wsh

  emb2 : ∀ {n} -> 
    let open PB (pres n) renaming (Alphabet to Sn ; _≈_ to _≈ₙ_) using () in
    let open PB (pres (suc (suc n))) renaming (Alphabet to Sₙ₊₂) using (_≈_) in
    let A = S2 ⊎ Sn in
    A -> Sₙ₊₂
  emb2 {n} (inj₁ x) = swap
  emb2 {suc n} (inj₂ y) = y ₛ ₛ

  emb2' : ∀ {n} -> 
    let open PB (pres n) renaming (Alphabet to Sn ; _≈_ to _≈ₙ_) using () in
    let open PB (pres (suc (suc n))) renaming (Alphabet to Sₙ₊₂) using (_≈_) in
    let A = S2 ⊎ Sn in
    A -> Word Sₙ₊₂
  emb2' {n} (inj₁ x) = [ swap ]ʷ
  emb2' {suc n} (inj₂ y) = [ y ₛ ₛ ]ʷ

  [_⇑]'' : ∀ {n} -> 
    let open PB (pres n) renaming (Alphabet to Sn ; _≈_ to _≈ₙ_) using () in
    let open PB (pres (suc (suc n))) renaming (Alphabet to Sₙ₊₂) using (_≈_) in
    let A = S2 ⊎ Sn in
    Word A -> Word Sₙ₊₂
  [_⇑]'' {n} = ((emb2' {n}) *)

  aux-a : ∀ {n} ws ->
    let open PB (pres (suc (suc n))) renaming (Alphabet to Sₙ₊₂) using (_≈_) in
    [ [ ws ⇑] ⇑] ≈ [ [ ws ]ᵣ ⇑]''
  aux-a [ swap ]ʷ = refl
  aux-a [ x ₛ ]ʷ = refl
  aux-a ε = refl
  aux-a (ws • ws₁) = cong (aux-a ws) (aux-a ws₁)


  lemma-ract' : ∀ {n} c x ->
    let open PB (pres n) renaming (Alphabet to Sn ; _≈_ to _≈ₙ_) using () in
    let open PB (pres (suc (suc n))) renaming (Alphabet to Sₙ₊₂) using (_≈_) in
    let (x' , c') = ract' {n} c x in ([ c ]' • [ x ]ʷ) ≈ ([ x' ⇑]'' • [ c' ]')
  lemma-ract' {n} (c , d) x with ract d x | lemma-ract d x
  ... | (ws , d') | hyp1 with racts c ws | lemma-racts c ws
  ... | (ws' , c') | hyp2  with aux2 c' d' | lemma-aux2 c' d'
  ... | b@false , c'' , d'' | ih  = begin
    ([ c , d ]' • [ x ]ʷ) ≈⟨ _≈_.assoc ⟩
    [ [ c ] ⇑] • [ d ] • [ x ]ʷ ≈⟨ cong refl hyp1 ⟩
    [ [ c ] ⇑] • [ ws ⇑] • [ d' ] ≈⟨ _≈_.sym _≈_.assoc ⟩
    ([ [ c ] ⇑] • [ ws ⇑]) • [ d' ] ≈⟨ _≈_.refl ⟩
    ([ [ c ] • ws ⇑]) • [ d' ] ≈⟨ cong ([⇑]-cong ([ c ] • ws ) ([ ws' ⇑] • [ c' ]) hyp2) refl ⟩
    ([ [ ws' ⇑] • [ c' ] ⇑]) • [ d' ] ≈⟨ _≈_.refl ⟩
    ([ [ ws' ⇑] ⇑] • [ [ c' ] ⇑]) • [ d' ] ≈⟨ _≈_.assoc ⟩
    [ [ ws' ⇑] ⇑] • [ [ c' ] ⇑] • [ d' ] ≈⟨ cong refl ih ⟩
    [ [ ws' ⇑] ⇑] • eval-bool b • [ c'' , d'' ]' ≈⟨ _≈_.refl ⟩
    [ [ ws' ⇑] ⇑] • ε • [ c'' , d'' ]' ≈⟨ _≈_.cong _≈_.refl _≈_.left-unit ⟩
    [ [ ws' ⇑] ⇑] • [ c'' , d'' ]' ≈⟨ cong (aux-a ws') refl  ⟩
    ([ [ ws' ]ᵣ ⇑]'' • [ c'' , d'' ]') ∎
    where
      open PB (pres (suc (suc n))) renaming (Alphabet to Sₙ₊₂) using (_≈_)
      open PP (pres (suc (suc n))) renaming (word-setoid to wsh) using ()
      open SR wsh
  ... | b@true , c'' , d'' | ih  = begin
    ([ c , d ]' • [ x ]ʷ) ≈⟨ _≈_.assoc ⟩
    [ [ c ] ⇑] • [ d ] • [ x ]ʷ ≈⟨ cong refl hyp1 ⟩
    [ [ c ] ⇑] • [ ws ⇑] • [ d' ] ≈⟨ _≈_.sym _≈_.assoc ⟩
    ([ [ c ] ⇑] • [ ws ⇑]) • [ d' ] ≈⟨ _≈_.refl ⟩
    ([ [ c ] • ws ⇑]) • [ d' ] ≈⟨ cong ([⇑]-cong ([ c ] • ws ) ([ ws' ⇑] • [ c' ]) hyp2) refl ⟩
    ([ [ ws' ⇑] • [ c' ] ⇑]) • [ d' ] ≈⟨ _≈_.refl ⟩
    ([ [ ws' ⇑] ⇑] • [ [ c' ] ⇑]) • [ d' ] ≈⟨ _≈_.assoc ⟩
    [ [ ws' ⇑] ⇑] • [ [ c' ] ⇑] • [ d' ] ≈⟨ cong refl ih ⟩
    [ [ ws' ⇑] ⇑] • eval-bool b • [ c'' , d'' ]' ≈⟨ _≈_.refl ⟩
    [ [ ws' ⇑] ⇑] • [ swap ]ʷ • [ c'' , d'' ]' ≈⟨ cong (aux-a ws') (cong _≈_.refl refl) ⟩
    [ [ ws' ]ᵣ ⇑]'' • [ [ [ swap ]ʷ ]ₗ ⇑]'' • [ c'' , d'' ]' ≈⟨ _≈_.sym _≈_.assoc ⟩
    [ [ ws' ]ᵣ • [ [ swap ]ʷ ]ₗ ⇑]'' • [ c'' , d'' ]' ∎
    where
      open PB (pres (suc (suc n))) renaming (Alphabet to Sₙ₊₂) using (_≈_)
      open PP (pres (suc (suc n))) renaming (word-setoid to wsh) using ()
      open SR wsh


  lemma-ract'' : ∀ {n} c x ->
    let open PB (pres n) renaming (Alphabet to Sn ; _≈_ to _≈ₙ_) using () in
    let open PB (pres (suc (suc n))) renaming (Alphabet to Sₙ₊₂) using (_≈_) in
    let (x' , c') = ract'' {n} c x in ([ c ]'' • [ x ]ʷ) ≈ ([ x' ⇑]'' • [ c' ]'')
  lemma-ract'' {n} (c , d) x with ract (inject₁ (inject d)) x | lemma-ract (inject₁ (inject d)) x
  ... | (ws , d') | hyp1 with racts c ws | lemma-racts c ws
  ... | (ws' , c') | hyp2  with aux2' c' d' | lemma-aux2' c' d'
  ... | b@false , c'' , d'' | ih  =
    let iid = inject₁ (inject d) in
    let iid'' = inject₁ (inject d'') in
    begin
    ([ c , d ]'' • [ x ]ʷ) ≈⟨ _≈_.assoc ⟩
    [ [ c ] ⇑] • [ iid ] • [ x ]ʷ ≈⟨ cong refl hyp1 ⟩
    [ [ c ] ⇑] • [ ws ⇑] • [ d' ] ≈⟨ _≈_.sym _≈_.assoc ⟩
    ([ [ c ] ⇑] • [ ws ⇑]) • [ d' ] ≈⟨ _≈_.refl ⟩
    ([ [ c ] • ws ⇑]) • [ d' ] ≈⟨ cong ([⇑]-cong ([ c ] • ws ) ([ ws' ⇑] • [ c' ]) hyp2) refl ⟩
    ([ [ ws' ⇑] • [ c' ] ⇑]) • [ d' ] ≈⟨ _≈_.refl ⟩
    ([ [ ws' ⇑] ⇑] • [ [ c' ] ⇑]) • [ d' ] ≈⟨ _≈_.assoc ⟩
    [ [ ws' ⇑] ⇑] • [ [ c' ] ⇑] • [ d' ] ≈⟨ cong refl ih ⟩
    [ [ ws' ⇑] ⇑] • eval-bool b • [ c'' , inject₁ (inject d'') ]' ≈⟨ _≈_.refl ⟩
    [ [ ws' ⇑] ⇑] • ε • [ c'' , iid'' ]' ≈⟨ _≈_.cong _≈_.refl _≈_.left-unit ⟩
    [ [ ws' ⇑] ⇑] • [ c'' , iid'' ]' ≈⟨ cong (aux-a ws') refl  ⟩
    ([ [ ws' ]ᵣ ⇑]'' • [ c'' , iid'' ]') ≈⟨ _≈_.cong (_≈_.sym _≈_.right-unit) _≈_.refl ⟩
    ([ [ ws' ]ᵣ • [ eval-bool₁ b ]ₗ ⇑]'' • [ c'' , iid'' ]') ∎
    where
      open PB (pres (suc (suc n))) renaming (Alphabet to Sₙ₊₂) using (_≈_)
      open PP (pres (suc (suc n))) renaming (word-setoid to wsh) using ()
      open SR wsh
  ... | b@true , c'' , d'' | ih  =
    let iid = inject₁ (inject d) in
    let iid'' = inject₁ (inject d'') in
    begin
    ([ c , d ]'' • [ x ]ʷ) ≈⟨ _≈_.assoc ⟩
    [ [ c ] ⇑] • [ iid ] • [ x ]ʷ ≈⟨ cong refl hyp1 ⟩
    [ [ c ] ⇑] • [ ws ⇑] • [ d' ] ≈⟨ _≈_.sym _≈_.assoc ⟩
    ([ [ c ] ⇑] • [ ws ⇑]) • [ d' ] ≈⟨ _≈_.refl ⟩
    ([ [ c ] • ws ⇑]) • [ d' ] ≈⟨ cong ([⇑]-cong ([ c ] • ws ) ([ ws' ⇑] • [ c' ]) hyp2) refl ⟩
    ([ [ ws' ⇑] • [ c' ] ⇑]) • [ d' ] ≈⟨ _≈_.refl ⟩
    ([ [ ws' ⇑] ⇑] • [ [ c' ] ⇑]) • [ d' ] ≈⟨ _≈_.assoc ⟩
    [ [ ws' ⇑] ⇑] • [ [ c' ] ⇑] • [ d' ] ≈⟨ cong refl ih ⟩
    [ [ ws' ⇑] ⇑] • eval-bool b • [ c'' , iid'' ]' ≈⟨ _≈_.refl ⟩
    [ [ ws' ⇑] ⇑] • [ swap ]ʷ • [ c'' , iid'' ]' ≈⟨ cong (aux-a ws') (cong _≈_.refl refl) ⟩
    [ [ ws' ]ᵣ ⇑]'' • [ [ [ swap ]ʷ ]ₗ ⇑]'' • [ c'' , iid'' ]' ≈⟨ _≈_.sym _≈_.assoc ⟩
    [ [ ws' ]ᵣ • [ [ swap ]ʷ ]ₗ ⇑]'' • [ c'' , iid'' ]' ∎
    where
      open PB (pres (suc (suc n))) renaming (Alphabet to Sₙ₊₂) using (_≈_)
      open PP (pres (suc (suc n))) renaming (word-setoid to wsh) using ()
      open SR wsh

  open import Data.List hiding ([_])

  aux-emb : ∀ {n} (w : Word (X n)) -> [ [ w ]ᵣ ⇑]'' ≡ [ [ w ⇑] ⇑]
  aux-emb [ swap ]ʷ = Eq.refl
  aux-emb [ x ₛ ]ʷ = Eq.refl
  aux-emb ε = Eq.refl
  aux-emb (w • w₁) rewrite aux-emb w | aux-emb w₁ = Eq.refl

  aux-ii : ∀ {n} {i : C n} -> inject {i = i} ε ≡ ε
  aux-ii {n} {ε} = Eq.refl
  aux-ii {n} {swap• i} = Eq.refl

  lemma-fm : ∀ {n} (w : Word (X n)) -> [ fm [ w ]ᵣ ⇑]'' ≡ [ [ [ w ]ᵣ ⇑]'' ⇑]
  lemma-fm {n} [ swap ]ʷ = Eq.refl
  lemma-fm {n} [ x ₛ ]ʷ = Eq.refl
  lemma-fm {n} ε = Eq.refl
  lemma-fm {n} (w • w₁) rewrite lemma-fm w | lemma-fm w₁ = Eq.refl

  lemma-fm2 : ∀ {n} (w : Word (X n)) ->
    let open PB (pres (suc (suc n))) renaming (_≈_ to _≈₃_) in
    [ [ w ]ᵣ ⇑]'' • [ swap ]ʷ ≈₃ [ swap ]ʷ • [ [ w ]ᵣ ⇑]''
  lemma-fm2 {n} [ swap ]ʷ = sym (axiom comm)
  lemma-fm2 {n} [ x ₛ ]ʷ = sym (axiom comm)
  lemma-fm2 {n} ε = trans left-unit (sym right-unit)
  lemma-fm2 {n} (w • v) = begin
    [ [ w • v ]ᵣ ⇑]'' • [ swap ]ʷ ≈⟨ assoc ⟩
    [ [ w ]ᵣ ⇑]'' • [ [ v ]ᵣ ⇑]'' • [ swap ]ʷ ≈⟨ cong refl (lemma-fm2 v) ⟩
    [ [ w ]ᵣ ⇑]'' • [ swap ]ʷ • [ [ v ]ᵣ ⇑]'' ≈⟨ sym assoc ⟩
    ([ [ w ]ᵣ ⇑]'' • [ swap ]ʷ) • [ [ v ]ᵣ ⇑]'' ≈⟨ cong (lemma-fm2 w) refl ⟩
    ([ swap ]ʷ • [ [ w ]ᵣ ⇑]'') • [ [ v ]ᵣ ⇑]'' ≈⟨ assoc ⟩
    [ swap ]ʷ • [ [ w • v ]ᵣ ⇑]'' ∎
    where
    open PP (pres (suc (suc n)))
    open SR word-setoid




  aux3b : ∀ {n} c x ->
    let open PB (pres n) renaming (Alphabet to Sn ; _≈_ to _≈ₙ_) using () in
    let open PB (pres (suc (suc n))) renaming (Alphabet to Sₙ₊₂) using (_≈_) in
    let (x' , c') = ract3 {n} (swap• c , ε) (x ₛ) in
      ∃ \w -> x' ≡ [ w ]ᵣ
  aux3b {n} ε swap = ε , Eq.refl
  aux3b {n} (swap• c) swap = [ swap ]ʷ , Eq.refl
  aux3b {n} ε (swap ₛ) = ε , Eq.refl
  aux3b {n} ε ((x ₛ) ₛ) = [ x ₛ ]ʷ , Eq.refl
  aux3b {n} (swap• ε) (swap ₛ) = ε , Eq.refl
  aux3b {n} (swap• ε) ((swap ₛ) ₛ) = ε , Eq.refl
  aux3b {n} (swap• ε) (((x ₛ) ₛ) ₛ) = [ (x ₛ) ₛ ]ʷ , Eq.refl
  aux3b {n} (swap• swap• c) (x ₛ) with aux3b (swap• c) x
  ... | w , eq rewrite eq | lemma-fm3 w = [ w ⇑] , Eq.refl



  lemma-ract3 : ∀ {n} c x ->
    let open PB (pres n) renaming (Alphabet to Sn ; _≈_ to _≈ₙ_) using () in
    let open PB (pres (suc (suc n))) renaming (Alphabet to Sₙ₊₂) using (_≈_) in
    let (x' , c') = ract3 {n} c x in ([ c ]'' • [ x ]ʷ) ≈ ([ x' ⇑]'' • [ c' ]'')
  lemma-ract3 {n} (ε , ε) swap = by-assoc Eq.refl
    where open PP (pres (suc (suc n))) using (by-assoc)
  lemma-ract3 {n} (ε , ε) (swap ₛ) = by-assoc Eq.refl
    where open PP (pres (suc (suc n))) using (by-assoc)
  lemma-ract3 {n} (ε , ε) ((x ₛ) ₛ) rewrite aux-emb [ x ]ʷ = by-assoc Eq.refl
    where open PP (pres (suc (suc n))) using (by-assoc)


  lemma-ract3 {n} (swap• c , ε) swap = begin
    [ swap• c , ε ]'' • [ swap ]ʷ ≈⟨ refl ⟩
    ([ [ swap• c ] ⇑] • [ ε ]) • [ swap ]ʷ ≈⟨ cong right-unit refl ⟩
    ([ [ swap• c ] ⇑]) • [ swap ]ʷ ≈⟨ cong refl (sym right-unit) ⟩
    [ [ swap• c ] ⇑] • [ swap ]ʷ • [ [ inject₁ ε ] ⇑] ≡⟨ Eq.sym (Eq.cong (\x -> [ [ swap• c ] ⇑] • [ swap ]ʷ • [ [ inject₁ x ] ⇑]) (aux-ii {i = c}) )⟩
    [ [ swap• c ] ⇑] • [ swap ]ʷ • [ [ inject₁ (inject {i = c} ε) ] ⇑] ≈⟨ refl ⟩
    [ [ swap• c ] ⇑] • [ swap• inject₁ (inject {i = c} ε) ] ≈⟨ refl ⟩
    [ [ swap• c ] ⇑] • [ inject₁ (swap• inject {i = c} ε) ] ≈⟨ refl ⟩
    [ [ swap• c ] ⇑] • [ inject₁ (inject {i = swap• c} (swap• ε)) ] ≈⟨ sym (trans refl refl) ⟩
    [ swap• c , swap• ε ]'' ≈⟨ sym left-unit ⟩
    [ ε ⇑]'' • [ swap• c , swap• ε ]'' ∎
    where
      open PP (pres (suc (suc n))) using (by-assoc ; word-setoid)
      open SR word-setoid
  lemma-ract3 {n} (swap• ε , ε) (swap ₛ) = begin
    [ swap• ε , ε ]'' • [ swap ₛ ]ʷ ≈⟨ refl ⟩
    (([ swap ₛ ]ʷ • ε) • ε) • [ swap ₛ ]ʷ ≈⟨ by-assoc Eq.refl ⟩
    [ swap ₛ ]ʷ • [ swap ₛ ]ʷ ≈⟨ axiom (congₛ order) ⟩
    ε ≈⟨ by-assoc Eq.refl ⟩
    ε • ε • ε ≈⟨ refl ⟩
    [ ε ⇑]'' • [ ε , ε ]'' ∎
    where
      open PP (pres (suc (suc n))) using (by-assoc ; word-setoid)
      open SR word-setoid

  lemma-ract3 {n} (swap• ε , ε) ((swap ₛ) ₛ) = by-assoc Eq.refl
    where open PP (pres (suc (suc n))) using (by-assoc ; word-setoid)
  lemma-ract3 {n} (swap• ε , ε) (((x ₛ) ₛ) ₛ) = begin
    [ (swap• ε , ε) ]'' • [ (((x ₛ) ₛ) ₛ) ]ʷ ≈⟨ by-assoc Eq.refl ⟩
    [ swap ₛ ]ʷ • [ x ₛ ₛ ₛ ]ʷ ≈⟨ axiom (congₛ comm) ⟩
    [ x ₛ ₛ ₛ ]ʷ • [ swap ₛ ]ʷ ≈⟨ by-assoc Eq.refl ⟩
    [ ract3 (swap• ε , ε) (((x ₛ) ₛ) ₛ) .proj₁ ⇑]'' • [ ract3 (swap• ε , ε) (((x ₛ) ₛ) ₛ) .proj₂ ]'' ∎
    where
      open PP (pres (suc (suc n))) using (by-assoc ; word-setoid)
      open SR word-setoid
  lemma-ract3 {n} (swap• swap• c , ε) (swap ₛ) = begin
    [ (swap• swap• c , ε) ]'' • [ swap ₛ ]ʷ ≈⟨ assoc ⟩
    [ [ swap• swap• c ] ⇑] • ε • [ swap ₛ ]ʷ ≈⟨ cong refl left-unit ⟩
    [ [ swap• swap• c ] ⇑] • [ swap ₛ ]ʷ ≈⟨ trans assoc (cong refl assoc) ⟩
    [ swap ₛ ]ʷ • [ swap ₛ ₛ ]ʷ • [ [ [ [ c ] ⇑] ⇑] ⇑] • [ swap ₛ ]ʷ  ≈⟨ cong refl (cong refl refl) ⟩
    [ swap ₛ ]ʷ • [ swap ₛ ₛ ]ʷ • [ [ [ [ c ] ⇑] ⇑] • [ swap ]ʷ ⇑] ≈⟨ cong refl (cong refl ([⇑]-cong _ _ (lemma-comm [ c ]))) ⟩
    [ swap ₛ ]ʷ • [ swap ₛ ₛ ]ʷ • [ swap ₛ ]ʷ • [ [ [ [ c ] ⇑] ⇑] ⇑]  ≈⟨ by-assoc Eq.refl ⟩
    ([ swap ₛ ]ʷ • [ swap ₛ ₛ ]ʷ • [ swap ₛ ]ʷ) • [ [ [ [ c ] ⇑] ⇑] ⇑]  ≈⟨  (cong (axiom (congₛ yang-baxter)) refl) ⟩
    ([ swap ₛ ₛ ]ʷ • [ swap ₛ ]ʷ • [ swap ₛ ₛ ]ʷ) • [ [ [ [ c ] ⇑] ⇑] ⇑]  ≈⟨ trans assoc (cong refl assoc) ⟩
    [ swap ₛ ₛ ]ʷ • [ swap ₛ ]ʷ • [ swap ₛ ₛ ]ʷ • [ [ [ [ c ] ⇑] ⇑] ⇑] ≈⟨ sym (cong refl right-unit) ⟩
    [ ract3 (swap• swap• c , ε) (swap ₛ) .proj₁ ⇑]'' • [ ract3 (swap• swap• c , ε) (swap ₛ) .proj₂ ]'' ∎
    where
      open PP (pres (suc (suc n))) using (by-assoc ; word-setoid)
      open SR word-setoid
      
  lemma-ract3 {n} (swap• swap• c , ε) ((x ₛ) ₛ) with ract3 (swap• c , ε) (x ₛ) | lemma-ract3 (swap• c , ε) (x ₛ) | aux3b c x | aux3a (swap• c) x
  ... | (w , (c' , d')) | hyp | (ww , eq) | ee = begin
    [ (swap• swap• c , ε) ]'' • [ ((x ₛ) ₛ) ]ʷ ≈⟨ assoc ⟩
    [ [ swap• swap• c ] ⇑] • ε • [ ((x ₛ) ₛ) ]ʷ ≈⟨ cong refl left-unit ⟩
    [ [ swap• swap• c ] ⇑] • [ [ ((x ₛ)) ]ʷ ⇑] ≈⟨ refl ⟩
    [ [ swap ]ʷ • [ [ swap• c ] ⇑] ⇑] • [ [ ((x ₛ)) ]ʷ ⇑] ≈⟨ assoc ⟩
    [ swap ₛ ]ʷ • [ [ [ swap• c ] ⇑] ⇑] • [ [ ((x ₛ)) ]ʷ ⇑] ≈⟨ refl ⟩
    [ swap ₛ ]ʷ • [ [ [ swap• c ] ⇑] • [ ((x ₛ)) ]ʷ ⇑] ≈⟨ cong refl (sym (cong right-unit refl)) ⟩
    [ swap ₛ ]ʷ • [ [ swap• c , ε ]'' • [ ((x ₛ)) ]ʷ ⇑] ≈⟨ cong refl ([⇑]-cong _ _ hyp) ⟩
    [ swap ₛ ]ʷ • [ [ w ⇑]'' • [ c' , d' ]'' ⇑] ≈⟨ cong refl (cong (refl'' (Eq.cong (\x -> [ [ x ⇑]'' ⇑]) eq)) refl)  ⟩
    [ swap ₛ ]ʷ • [ [ [ ww ]ᵣ ⇑]'' • [ c' , d' ]'' ⇑] ≈⟨ sym assoc ⟩
    [ [ swap ]ʷ • [ [ ww ]ᵣ ⇑]'' ⇑] • [ [ c' , d' ]'' ⇑] ≈⟨ cong ([⇑]-cong _ _ (sym (lemma-fm2 ww))) refl ⟩
    [ [ [ ww ]ᵣ ⇑]'' • [ swap ]ʷ ⇑] • [ [ c' , d' ]'' ⇑] ≈⟨ assoc ⟩
    [ [ [ ww ]ᵣ ⇑]'' ⇑] • [ [ swap ]ʷ • [ c' , d' ]'' ⇑] ≈⟨ cong refl (cong refl (refl'' (Eq.cong (\x -> [ [ c' , x ]'' ⇑]) ee))) ⟩
    [ [ [ ww ]ᵣ ⇑]'' ⇑] • [ [ swap ]ʷ • [ c' , ε ]'' ⇑] ≈⟨ cong refl (cong refl (trans refl refl)) ⟩
    [ [ [ ww ]ᵣ ⇑]'' ⇑] • [ [ swap ]ʷ ⇑] • [ [ [ c' ] ⇑] ⇑] • [ [ inject₁ (inject {i = c'} ε) ] ⇑] ≈⟨ cong refl (cong refl (cong refl (refl'' (Eq.cong (\x -> [ [ inject₁ x ] ⇑]) (aux-ii {i = c'}))))) ⟩
    [ [ [ ww ]ᵣ ⇑]'' ⇑] • [ [ swap ]ʷ ⇑] • [ [ [ c' ] ⇑] ⇑] • [ [ inject₁ ε ] ⇑] ≈⟨ cong refl (special-assoc (□ • □ • □) ((□ • □) • □) Eq.refl) ⟩
    [ [ [ ww ]ᵣ ⇑]'' ⇑] • [ swap• c' , ε ]'' ≈⟨ sym (cong (refl'' (lemma-fm ww)) refl) ⟩
    [ fm [ ww ]ᵣ ⇑]'' • [ swap• c' , ε ]'' ≈⟨ cong (refl'' (Eq.cong (\x -> [ fm x ⇑]'') (Eq.sym eq))) refl ⟩
    [ fm w ⇑]'' • [ swap• c' , ε ]'' ∎
    where
      open PB (pres (suc (suc n))) renaming (refl' to refl'') using ()
      open PP (pres (suc (suc n))) using (by-assoc ; word-setoid ; module Pattern-Assoc)
      open SR word-setoid
      open Pattern-Assoc


  lemma-ract3 {n} (swap• ε , swap• ε) swap = begin
    [ (swap• ε , swap• ε) ]'' • [ swap ]ʷ ≈⟨ by-assoc Eq.refl ⟩
    [ swap ₛ ]ʷ • [ swap ]ʷ • [ swap ]ʷ ≈⟨ trans (cong refl (axiom order)) right-unit ⟩
    [ swap ₛ ]ʷ ≈⟨ by-assoc Eq.refl ⟩
    [ ract3 (swap• ε , swap• ε) swap .proj₁ ⇑]'' • [ ract3 (swap• ε , swap• ε) swap .proj₂ ]'' ∎
    where
      open PP (pres (suc (suc n))) using (by-assoc ; word-setoid)
      open SR word-setoid
  lemma-ract3 {n} (swap• swap• c , swap• ε) swap = begin
    [ (swap• swap• c , swap• ε) ]'' • [ swap ]ʷ ≈⟨ assoc ⟩
    [ [ swap• swap• c ] ⇑] • ([ swap ]ʷ • ε) • [ swap ]ʷ ≈⟨ cong refl (cong right-unit refl) ⟩
    [ [ swap• swap• c ] ⇑] • [ swap ]ʷ • [ swap ]ʷ ≈⟨  trans (cong refl (axiom order)) right-unit ⟩
    [ [ swap• swap• c ] ⇑] ≈⟨ sym (trans left-unit right-unit) ⟩
    [ ract3 (swap• swap• c , swap• ε) (swap ) .proj₁ ⇑]'' • [ ract3 (swap• swap• c , swap• ε) (swap ) .proj₂ ]'' ∎
      where
      open PP (pres (suc (suc n))) using (by-assoc ; word-setoid)
      open SR word-setoid

  lemma-ract3 {n} (swap• swap• (c) , swap• swap• (d)) swap = begin
    [ (swap• swap• c , swap• swap• d) ]'' • [ swap ]ʷ ≈⟨ assoc ⟩
    [ [ swap• swap• c ] ⇑] • [ inject₁ (inject {i = swap• swap• c} (swap• swap• d)) ] • [ swap ]ʷ ≈⟨ by-assoc Eq.refl ⟩
    ([ swap ₛ ]ʷ • [ swap ₛ ₛ ]ʷ • [ [ [ [ c ] ⇑] ⇑] ⇑]) • ([ swap ]ʷ • [ swap ₛ ]ʷ • [ [ [ inject₁ (inject {i = c} d) ] ⇑] ⇑] ) • [ swap ]ʷ ≈⟨ special-assoc ((□ • □ • □) • (□ • □ • □) • □) ((□ • □ • □ • □ • □) • □ • □) Eq.refl ⟩
    ([ swap ₛ ]ʷ • [ swap ₛ ₛ ]ʷ • [ [ [ [ c ] ⇑] ⇑] ⇑] • [ swap ]ʷ • [ swap ₛ ]ʷ) • [ [ [ inject₁ (inject {i = c} d) ] ⇑] ⇑] • [ swap ]ʷ ≈⟨ cong refl (lemma-comm [ inject₁ (inject {i = c} d) ]) ⟩
    ([ swap ₛ ]ʷ • [ swap ₛ ₛ ]ʷ • [ [ [ [ c ] ⇑] ⇑] ⇑] • [ swap ]ʷ • [ swap ₛ ]ʷ) • [ swap ]ʷ • [ [ [ inject₁ (inject {i = c} d) ] ⇑] ⇑] ≈⟨ special-assoc ((□ • □ • □ • □ • □) • □ • □) ((□ • □ • □) • □ • □ • □ • □) Eq.refl ⟩
    ([ swap ₛ ]ʷ • [ swap ₛ ₛ ]ʷ • [ [ [ [ c ] ⇑] ⇑] ⇑]) • [ swap ]ʷ • [ swap ₛ ]ʷ • [ swap ]ʷ • [ [ [ inject₁ (inject {i = c} d) ] ⇑] ⇑] ≈⟨ special-assoc ((□ • □ • □) • □ • □ • □ • □) (□ • □ • (□ • □) • □ • □ • □) Eq.refl ⟩
    [ swap ₛ ]ʷ • [ swap ₛ ₛ ]ʷ • ([ [ [ [ c ] ⇑] ⇑] ⇑] • [ swap ]ʷ) • [ swap ₛ ]ʷ • [ swap ]ʷ • [ [ [ inject₁ (inject {i = c} d) ] ⇑] ⇑] ≈⟨ cong refl (cong refl (cong (lemma-comm [ [ c ] ⇑]) refl)) ⟩
    [ swap ₛ ]ʷ • [ swap ₛ ₛ ]ʷ • ([ swap ]ʷ • [ [ [ [ c ] ⇑] ⇑] ⇑]) • [ swap ₛ ]ʷ • [ swap ]ʷ • [ [ [ inject₁ (inject {i = c} d) ] ⇑] ⇑] ≈⟨ special-assoc (□ • □ • (□ • □) • □ • □ • □) (□ • □ • □ • (□ • □) • □ • □) Eq.refl ⟩
    [ swap ₛ ]ʷ • [ swap ₛ ₛ ]ʷ • [ swap ]ʷ • ([ [ [ [ c ] ⇑] ⇑] ⇑] • [ swap ₛ ]ʷ) • [ swap ]ʷ • [ [ [ inject₁ (inject {i = c} d) ] ⇑] ⇑] ≈⟨ cong refl (cong refl (cong refl (cong ([⇑]-cong _ _ (lemma-comm [ c ])) refl))) ⟩
    [ swap ₛ ]ʷ • [ swap ₛ ₛ ]ʷ • [ swap ]ʷ • ([ swap ₛ ]ʷ • [ [ [ [ c ] ⇑] ⇑] ⇑]) • [ swap ]ʷ • [ [ [ inject₁ (inject {i = c} d) ] ⇑] ⇑] ≈⟨ special-assoc (□ • □ • □ • (□ • □) • □ • □) (□ • □ • □ • □ • (□ • □) • □)  Eq.refl  ⟩
    [ swap ₛ ]ʷ • [ swap ₛ ₛ ]ʷ • [ swap ]ʷ • [ swap ₛ ]ʷ • ([ [ [ [ c ] ⇑] ⇑] ⇑] • [ swap ]ʷ) • [ [ [ inject₁ (inject {i = c} d) ] ⇑] ⇑] ≈⟨ cong refl (cong refl (cong refl (cong refl (cong (lemma-comm [ [ c ] ⇑]) refl )))) ⟩
    [ swap ₛ ]ʷ • [ swap ₛ ₛ ]ʷ • [ swap ]ʷ • [ swap ₛ ]ʷ • ([ swap ]ʷ • [ [ [ [ c ] ⇑] ⇑] ⇑]) • [ [ [ inject₁ (inject {i = c} d) ] ⇑] ⇑] ≈⟨ special-assoc  (□ • □ • □ • □ • (□ • □) • □) ((□ • □) • (□ • □ • □) • □ • □)  Eq.refl  ⟩
    ([ swap ₛ ]ʷ • [ swap ₛ ₛ ]ʷ) • ([ swap ]ʷ • [ swap ₛ ]ʷ • [ swap ]ʷ) • [ [ [ [ c ] ⇑] ⇑] ⇑] • [ [ [ inject₁ (inject {i = c} d) ] ⇑] ⇑] ≈⟨ cong refl (cong (axiom yang-baxter) refl) ⟩
    ([ swap ₛ ]ʷ • [ swap ₛ ₛ ]ʷ) • ([ swap ₛ ]ʷ • [ swap ]ʷ • [ swap ₛ ]ʷ) • [ [ [ [ c ] ⇑] ⇑] ⇑] • [ [ [ inject₁ (inject {i = c} d) ] ⇑] ⇑] ≈⟨ special-assoc ((□ • □) • (□ • □ • □) • □ • □) ((□ • □ • □ • □) • (□ • □) • □) Eq.refl ⟩
    ([ swap ₛ ]ʷ • [ swap ₛ ₛ ]ʷ • [ swap ₛ ]ʷ • [ swap ]ʷ) • ([ swap ₛ ]ʷ • [ [ [ [ c ] ⇑] ⇑] ⇑]) • [ [ [ inject₁ (inject {i = c} d) ] ⇑] ⇑] ≈⟨ cong refl (cong (sym ([⇑]-cong _ _ (lemma-comm [ c ]))) refl) ⟩
    ([ swap ₛ ]ʷ • [ swap ₛ ₛ ]ʷ • [ swap ₛ ]ʷ • [ swap ]ʷ) • ([ [ [ [ c ] ⇑] ⇑] ⇑] • [ swap ₛ ]ʷ) • [ [ [ inject₁ (inject {i = c} d) ] ⇑] ⇑] ≈⟨ special-assoc ((□ • □ • □ • □) • (□ • □) • □) ((□ • □ • □) • (□ • □) • □ • □) Eq.refl ⟩
    ([ swap ₛ ]ʷ • [ swap ₛ ₛ ]ʷ • [ swap ₛ ]ʷ) • ([ swap ]ʷ • [ [ [ [ c ] ⇑] ⇑] ⇑]) • [ swap ₛ ]ʷ • [ [ [ inject₁ (inject {i = c} d) ] ⇑] ⇑] ≈⟨ cong refl (cong (sym (lemma-comm [ [ c ] ⇑])) refl) ⟩
    ([ swap ₛ ]ʷ • [ swap ₛ ₛ ]ʷ • [ swap ₛ ]ʷ) • ([ [ [ [ c ] ⇑] ⇑] ⇑] • [ swap ]ʷ) • [ swap ₛ ]ʷ • [ [ [ inject₁ (inject {i = c} d) ] ⇑] ⇑] ≈⟨ cong (axiom (congₛ yang-baxter)) refl ⟩
    ([ swap ₛ ₛ ]ʷ • [ swap ₛ ]ʷ • [ swap ₛ ₛ ]ʷ) • ([ [ [ [ c ] ⇑] ⇑] ⇑] • [ swap ]ʷ) • [ swap ₛ ]ʷ • [ [ [ inject₁ (inject {i = c} d) ] ⇑] ⇑] ≈⟨ special-assoc ((□ • □ • □) • (□ • □) • □ • □) (□ • (□ • □ • □) • □ • □ • □) Eq.refl ⟩
    [ swap ₛ ₛ ]ʷ • ([ swap ₛ ]ʷ • [ swap ₛ ₛ ]ʷ • [ [ [ [ c ] ⇑] ⇑] ⇑]) • [ swap ]ʷ • [ swap ₛ ]ʷ • [ [ [ inject₁ (inject {i = c} d) ] ⇑] ⇑] ≈⟨ refl ⟩
    [ ract3 (swap• swap• c , swap• swap• d) (swap) .proj₁ ⇑]'' • [ ract3 (swap• swap• c , swap• swap• d) (swap) .proj₂ ]'' ∎
      where
      open PP (pres (suc (suc n))) using (by-assoc ; word-setoid ; module Pattern-Assoc)
      open SR word-setoid
      open Pattern-Assoc


  lemma-ract3 {n} (swap• ε , swap• ε) (swap ₛ) =  begin
    [ (swap• ε , swap• ε) ]'' • [ swap ₛ ]ʷ ≈⟨ by-assoc Eq.refl ⟩
    [ swap ₛ ]ʷ • [ swap ]ʷ • [ swap ₛ ]ʷ ≈⟨ sym (axiom yang-baxter) ⟩
    [ swap ]ʷ • [ swap ₛ ]ʷ • [ swap ]ʷ ≈⟨ by-assoc Eq.refl ⟩
    [ ract3 (swap• ε , swap• ε) (swap ₛ) .proj₁ ⇑]'' • [ ract3 (swap• ε , swap• ε) (swap ₛ) .proj₂ ]'' ∎
    where
      open PP (pres (suc (suc n))) using (by-assoc ; word-setoid)
      open SR word-setoid
      open NFProperty (nfp ((suc (suc n))))
  lemma-ract3 {n} (swap• swap• (c@ε) , swap• ε) (swap ₛ) = begin
    [ (swap• swap• c , swap• ε) ]'' • [ swap ₛ ]ʷ ≈⟨ assoc ⟩
    [ [ swap• swap• c ] ⇑] • [ swap• ε ] • [ swap ₛ ]ʷ ≈⟨ by-assoc Eq.refl ⟩
    [ [ swap• swap• c ] ⇑] • [ inject₁ (inject {i = swap• swap• c} (swap• swap• ε)) ] ≈⟨ refl ⟩
    [ swap• swap• c , swap• swap• ε ]'' ≈⟨ sym left-unit ⟩
    [ ract3 (swap• swap• c , swap• ε) (swap ₛ) .proj₁ ⇑]'' • [ ract3 (swap• swap• c , swap• ε) (swap ₛ) .proj₂ ]'' ∎
    where
      open PP (pres (suc (suc n))) using (by-assoc ; word-setoid)
      open SR word-setoid
  lemma-ract3 {n} (swap• swap• (c@(swap• c')) , swap• ε) (swap ₛ) = begin
    [ (swap• swap• c , swap• ε) ]'' • [ swap ₛ ]ʷ ≈⟨ assoc ⟩
    [ [ swap• swap• c ] ⇑] • [ swap• ε ] • [ swap ₛ ]ʷ ≈⟨ by-assoc Eq.refl ⟩
    [ [ swap• swap• c ] ⇑] • [ inject₁ (inject {i = swap• swap• c} (swap• swap• ε)) ] ≈⟨ refl ⟩
    [ swap• swap• c , swap• swap• ε ]'' ≈⟨ sym left-unit ⟩
    [ ract3 (swap• swap• c , swap• ε) (swap ₛ) .proj₁ ⇑]'' • [ ract3 (swap• swap• c , swap• ε) (swap ₛ) .proj₂ ]'' ∎
    where
      open PP (pres (suc (suc n))) using (by-assoc ; word-setoid)
      open SR word-setoid
  lemma-ract3 {n} (swap• swap• ε , swap• swap• ε) (swap ₛ) = begin
    [ (swap• swap• ε , swap• swap• ε) ]'' • [ swap ₛ ]ʷ ≈⟨ by-assoc Eq.refl ⟩
    [ swap ₛ ]ʷ • [ swap ₛ ₛ ]ʷ • [ swap ]ʷ • [ swap ₛ ]ʷ • [ swap ₛ ]ʷ ≈⟨ cong refl (cong refl (cong refl (axiom (congₛ order)))) ⟩
    [ swap ₛ ]ʷ • [ swap ₛ ₛ ]ʷ • [ swap ]ʷ • ε ≈⟨ by-assoc Eq.refl ⟩
    [ ract3 (swap• swap• ε , swap• swap• ε) (swap ₛ) .proj₁ ⇑]'' • [ ract3 (swap• swap• ε , swap• swap• ε) (swap ₛ) .proj₂ ]'' ∎
    where
      open PP (pres (suc (suc n))) using (by-assoc ; word-setoid)
      open SR word-setoid
  lemma-ract3 {n} (swap• swap• swap• c , swap• swap• ε) (swap ₛ) = begin
    [ (swap• swap• swap• c , swap• swap• ε) ]'' • [ swap ₛ ]ʷ ≈⟨ assoc ⟩
    [ [ swap• swap• swap• c ] ⇑] • [ swap• swap• ε ] • [ swap ₛ ]ʷ ≈⟨ cong refl (by-assoc Eq.refl) ⟩
    [ [ swap• swap• swap• c ] ⇑] • [ swap ]ʷ • [ swap ₛ ]ʷ • [ swap ₛ ]ʷ ≈⟨ cong refl (cong refl (axiom (congₛ order))) ⟩
    [ [ swap• swap• swap• c ] ⇑] • [ swap ]ʷ • ε ≈⟨ sym left-unit ⟩
    [ ract3 (swap• swap• swap• c , swap• swap• ε) (swap ₛ) .proj₁ ⇑]'' • [ ract3 (swap• swap• swap• c , swap• swap• ε) (swap ₛ) .proj₂ ]'' ∎
    where
      open PP (pres (suc (suc n))) using (by-assoc ; word-setoid)
      open SR word-setoid
  lemma-ract3 {n} (swap• swap• swap• c , swap• swap• swap• d) (swap ₛ) = let dd = inject₁ (inject {i = c} d) in begin
    [ (swap• swap• swap• c , swap• swap• swap• d) ]'' • [ swap ₛ ]ʷ ≈⟨ _≈_.assoc ⟩
    [ [ swap• swap• swap• c ] ⇑] • [ inject₁ (inject {i = swap• swap• swap• c} (swap• swap• swap• d)) ] • [ swap ₛ ]ʷ ≈⟨ by-assoc Eq.refl ⟩
    ([ swap ₛ ]ʷ • [ swap ₛ ₛ ]ʷ • [ swap ₛ ₛ ₛ ]ʷ • [ [ [ [ [ c ] ⇑] ⇑] ⇑] ⇑]) • ([ swap ]ʷ • [ swap ₛ ]ʷ • [ swap ₛ ₛ ]ʷ • [ [ [ [ inject₁ (inject {i = c} d) ] ⇑] ⇑] ⇑] ) • [ swap ₛ ]ʷ ≈⟨ special-assoc ((□ • □ • □ • □) • (□ • □ • □ • □) • □) (((□ • □ • □) • (□ • □) • □ • □ • □ • □)) Eq.refl ⟩
    ([ swap ₛ ]ʷ • [ swap ₛ ₛ ]ʷ • [ swap ₛ ₛ ₛ ]ʷ) • ([ [ [ [ [ c ] ⇑] ⇑] ⇑] ⇑] • [ swap ]ʷ) • [ swap ₛ ]ʷ • [ swap ₛ ₛ ]ʷ • [ [ [ [ dd ] ⇑] ⇑] ⇑] • [ swap ₛ ]ʷ ≈⟨ cong refl (cong (lemma-comm [ [ [ c ] ⇑] ⇑]) refl) ⟩
    ([ swap ₛ ]ʷ • [ swap ₛ ₛ ]ʷ • [ swap ₛ ₛ ₛ ]ʷ) • ([ swap ]ʷ • [ [ [ [ [ c ] ⇑] ⇑] ⇑] ⇑]) • [ swap ₛ ]ʷ • [ swap ₛ ₛ ]ʷ • [ [ [ [ dd ] ⇑] ⇑] ⇑] • [ swap ₛ ]ʷ ≈⟨ special-assoc  (((□ • □ • □) • (□ • □) • □ • □ • □ • □))  (((□ • □ • □ • □) • (□ • □) • □ • □ • □))  Eq.refl ⟩
    ([ swap ₛ ]ʷ • [ swap ₛ ₛ ]ʷ • [ swap ₛ ₛ ₛ ]ʷ • [ swap ]ʷ) • ([ [ [ [ [ c ] ⇑] ⇑] ⇑] ⇑] • [ swap ₛ ]ʷ) • [ swap ₛ ₛ ]ʷ • [ [ [ [ dd ] ⇑] ⇑] ⇑] • [ swap ₛ ]ʷ ≈⟨ cong refl (cong ([⇑]-cong _ _ (lemma-comm  [ [ c ] ⇑] )) refl) ⟩
    ([ swap ₛ ]ʷ • [ swap ₛ ₛ ]ʷ • [ swap ₛ ₛ ₛ ]ʷ • [ swap ]ʷ) • ([ swap ₛ ]ʷ • [ [ [ [ [ c ] ⇑] ⇑] ⇑] ⇑]) • [ swap ₛ ₛ ]ʷ • [ [ [ [ dd ] ⇑] ⇑] ⇑] • [ swap ₛ ]ʷ ≈⟨ special-assoc  (((□ • □ • □ • □) • (□ • □) • □ • □ • □)) (((□ • □ • □ • □ • □) • (□ • □) • □ • □))  Eq.refl ⟩
    ([ swap ₛ ]ʷ • [ swap ₛ ₛ ]ʷ • [ swap ₛ ₛ ₛ ]ʷ • [ swap ]ʷ • [ swap ₛ ]ʷ) • ([ [ [ [ [ c ] ⇑] ⇑] ⇑] ⇑] • [ swap ₛ ₛ ]ʷ) • [ [ [ [ dd ] ⇑] ⇑] ⇑] • [ swap ₛ ]ʷ ≈⟨ cong refl (cong ([⇑]-cong _ _ ([⇑]-cong _ _ (lemma-comm  [ c ] ) )) refl) ⟩
    ([ swap ₛ ]ʷ • [ swap ₛ ₛ ]ʷ • [ swap ₛ ₛ ₛ ]ʷ • [ swap ]ʷ • [ swap ₛ ]ʷ) • ([ swap ₛ ₛ ]ʷ • [ [ [ [ [ c ] ⇑] ⇑] ⇑] ⇑]) • [ [ [ [ dd ] ⇑] ⇑] ⇑] • [ swap ₛ ]ʷ ≈⟨ special-assoc  (((□ • □ • □ • □ • □) • (□ • □) • □ • □)) (((□ • □ • □ • □ • □ • □ • □) • □ • □))  Eq.refl ⟩
    ([ swap ₛ ]ʷ • [ swap ₛ ₛ ]ʷ • [ swap ₛ ₛ ₛ ]ʷ • [ swap ]ʷ • [ swap ₛ ]ʷ • [ swap ₛ ₛ ]ʷ • [ [ [ [ [ c ] ⇑] ⇑] ⇑] ⇑]) • [ [ [ [ dd ] ⇑] ⇑] ⇑] • [ swap ₛ ]ʷ ≈⟨ cong refl (([⇑]-cong _ _ (lemma-comm  [ dd ] ) )) ⟩
    ([ swap ₛ ]ʷ • [ swap ₛ ₛ ]ʷ • [ swap ₛ ₛ ₛ ]ʷ • [ swap ]ʷ • [ swap ₛ ]ʷ • [ swap ₛ ₛ ]ʷ • [ [ [ [ [ c ] ⇑] ⇑] ⇑] ⇑]) • [ swap ₛ ]ʷ • [ [ [ [ dd ] ⇑] ⇑] ⇑] ≈⟨ special-assoc   (((□ • □ • □ • □ • □ • □ • □) • □ • □))  (((□ • □ • □ • □ • □ • □) • (□ • □) • □))  Eq.refl ⟩
    ([ swap ₛ ]ʷ • [ swap ₛ ₛ ]ʷ • [ swap ₛ ₛ ₛ ]ʷ • [ swap ]ʷ • [ swap ₛ ]ʷ • [ swap ₛ ₛ ]ʷ) • ([ [ [ [ [ c ] ⇑] ⇑] ⇑] ⇑] • [ swap ₛ ]ʷ) • [ [ [ [ dd ] ⇑] ⇑] ⇑] ≈⟨ cong refl (cong ([⇑]-cong _ _ (lemma-comm  [ [ c ] ⇑] )) refl) ⟩
    ([ swap ₛ ]ʷ • [ swap ₛ ₛ ]ʷ • [ swap ₛ ₛ ₛ ]ʷ • [ swap ]ʷ • [ swap ₛ ]ʷ • [ swap ₛ ₛ ]ʷ) • ([ swap ₛ ]ʷ • [ [ [ [ [ c ] ⇑] ⇑] ⇑] ⇑]) • [ [ [ [ dd ] ⇑] ⇑] ⇑] ≈⟨ special-assoc   ((□ • □ • □ • □ • □ • □) • (□ • □) • □)  ((□ • □ • □ • □ • □ • □ • □) • □ • □)  Eq.refl ⟩
    ([ swap ₛ ]ʷ • [ swap ₛ ₛ ]ʷ • [ swap ₛ ₛ ₛ ]ʷ • [ swap ]ʷ • [ swap ₛ ]ʷ • [ swap ₛ ₛ ]ʷ • [ swap ₛ ]ʷ) • [ [ [ [ [ c ] ⇑] ⇑] ⇑] ⇑] • [ [ [ [ dd ] ⇑] ⇑] ⇑] ≈⟨ cong claim refl ⟩
    
    ([ swap ₛ ₛ ₛ ]ʷ • [ swap ₛ ]ʷ • [ swap ₛ ₛ ]ʷ • [ swap ₛ ₛ ₛ ]ʷ • [ swap ]ʷ • [ swap ₛ ]ʷ • [ swap ₛ ₛ ]ʷ) • [ [ [ [ [ c ] ⇑] ⇑] ⇑] ⇑] • [ [ [ [ dd ] ⇑] ⇑] ⇑] ≈⟨ sym (special-assoc   ((□ • □ • □ • □ • □ • □) • (□ • □) • □)  ((□ • □ • □ • □ • □ • □ • □) • □ • □)  Eq.refl) ⟩
    ([ swap ₛ ₛ ₛ ]ʷ • [ swap ₛ ]ʷ • [ swap ₛ ₛ ]ʷ • [ swap ₛ ₛ ₛ ]ʷ • [ swap ]ʷ • [ swap ₛ ]ʷ) • ([ swap ₛ ₛ ]ʷ • [ [ [ [ [ c ] ⇑] ⇑] ⇑] ⇑]) • [ [ [ [ dd ] ⇑] ⇑] ⇑] ≈⟨ sym (cong refl (cong ([⇑]-cong _ _ ([⇑]-cong _ _ (lemma-comm  [ c ] ) )) refl)) ⟩
    ([ swap ₛ ₛ ₛ ]ʷ • [ swap ₛ ]ʷ • [ swap ₛ ₛ ]ʷ • [ swap ₛ ₛ ₛ ]ʷ • [ swap ]ʷ • [ swap ₛ ]ʷ) • ([ [ [ [ [ c ] ⇑] ⇑] ⇑] ⇑] • [ swap ₛ ₛ ]ʷ) • [ [ [ [ dd ] ⇑] ⇑] ⇑] ≈⟨ sym (special-assoc  (((□ • □ • □ • □ • □) • (□ • □) • □ • □)) (((□ • □ • □ • □ • □ • □) • (□ • □) • □))  Eq.refl) ⟩
    ([ swap ₛ ₛ ₛ ]ʷ • [ swap ₛ ]ʷ • [ swap ₛ ₛ ]ʷ • [ swap ₛ ₛ ₛ ]ʷ • [ swap ]ʷ) • ([ swap ₛ ]ʷ • [ [ [ [ [ c ] ⇑] ⇑] ⇑] ⇑]) • [ swap ₛ ₛ ]ʷ • [ [ [ [ dd ] ⇑] ⇑] ⇑] ≈⟨ sym (cong refl (cong ([⇑]-cong _ _ (lemma-comm  [ [ c ] ⇑] )) refl)) ⟩
    ([ swap ₛ ₛ ₛ ]ʷ • [ swap ₛ ]ʷ • [ swap ₛ ₛ ]ʷ • [ swap ₛ ₛ ₛ ]ʷ • [ swap ]ʷ) • ([ [ [ [ [ c ] ⇑] ⇑] ⇑] ⇑] • [ swap ₛ ]ʷ) • [ swap ₛ ₛ ]ʷ • [ [ [ [ dd ] ⇑] ⇑] ⇑] ≈⟨ sym (special-assoc  (((□ • □ • □ • □) • (□ • □) • □ • □ • □)) (((□ • □ • □ • □ • □) • (□ • □) • □ • □))  Eq.refl) ⟩
    ([ swap ₛ ₛ ₛ ]ʷ • [ swap ₛ ]ʷ • [ swap ₛ ₛ ]ʷ • [ swap ₛ ₛ ₛ ]ʷ) • ([ swap ]ʷ • [ [ [ [ [ c ] ⇑] ⇑] ⇑] ⇑]) • [ swap ₛ ]ʷ • [ swap ₛ ₛ ]ʷ • [ [ [ [ dd ] ⇑] ⇑] ⇑] ≈⟨ sym (cong refl (cong (lemma-comm [ [ [ c ] ⇑] ⇑]) refl)) ⟩
    ([ swap ₛ ₛ ₛ ]ʷ • [ swap ₛ ]ʷ • [ swap ₛ ₛ ]ʷ • [ swap ₛ ₛ ₛ ]ʷ) • ([ [ [ [ [ c ] ⇑] ⇑] ⇑] ⇑] • [ swap ]ʷ) • [ swap ₛ ]ʷ • [ swap ₛ ₛ ]ʷ • [ [ [ [ dd ] ⇑] ⇑] ⇑] ≈⟨ special-assoc   (((□ • □ • □ • □) • (□ • □) • □ • □ • □))  (□ • (□ • □ • □ • □) • (□ • □ • □ • □))  Eq.refl ⟩
    [ swap ₛ ₛ ₛ ]ʷ • ([ swap ₛ ]ʷ • [ swap ₛ ₛ ]ʷ • [ swap ₛ ₛ ₛ ]ʷ • [ [ [ [ [ c ] ⇑] ⇑] ⇑] ⇑]) • ([ swap ]ʷ • [ swap ₛ ]ʷ • [ swap ₛ ₛ ]ʷ • [ [ [ [ dd ] ⇑] ⇑] ⇑] ) ≈⟨ refl ⟩
    [ ract3 (swap• swap• swap• c , swap• swap• swap• d) (swap ₛ) .proj₁ ⇑]'' • [ ract3 (swap• swap• swap• c , swap• swap• swap• d) (swap ₛ) .proj₂ ]'' ∎
    where
      open PB (pres (suc (suc n))) using (_≈_)
      open PP (pres (suc (suc n))) using (by-assoc ; word-setoid ; module Pattern-Assoc)
      open SR word-setoid
      open Pattern-Assoc
      claim : [ swap ₛ ]ʷ • [ swap ₛ ₛ ]ʷ • [ swap ₛ ₛ ₛ ]ʷ • [ swap ]ʷ • [ swap ₛ ]ʷ • [ swap ₛ ₛ ]ʷ • [ swap ₛ ]ʷ ≈ [ swap ₛ ₛ ₛ ]ʷ • [ swap ₛ ]ʷ • [ swap ₛ ₛ ]ʷ • [ swap ₛ ₛ ₛ ]ʷ • [ swap ]ʷ • [ swap ₛ ]ʷ • [ swap ₛ ₛ ]ʷ
      claim = begin
        [ swap ₛ ]ʷ • [ swap ₛ ₛ ]ʷ • [ swap ₛ ₛ ₛ ]ʷ • [ swap ]ʷ • [ swap ₛ ]ʷ • [ swap ₛ ₛ ]ʷ • [ swap ₛ ]ʷ ≈⟨ by-assoc Eq.refl ⟩
        ([ swap ₛ ]ʷ • [ swap ₛ ₛ ]ʷ • [ swap ₛ ₛ ₛ ]ʷ • [ swap ]ʷ) • [ swap ₛ ]ʷ • [ swap ₛ ₛ ]ʷ • [ swap ₛ ]ʷ ≈⟨ cong refl (axiom (congₛ yang-baxter)) ⟩
        ([ swap ₛ ]ʷ • [ swap ₛ ₛ ]ʷ • [ swap ₛ ₛ ₛ ]ʷ • [ swap ]ʷ) • [ swap ₛ ₛ ]ʷ • [ swap ₛ ]ʷ • [ swap ₛ ₛ ]ʷ ≈⟨ by-assoc Eq.refl ⟩
        ([ swap ₛ ]ʷ • [ swap ₛ ₛ ]ʷ) • ([ swap ₛ ₛ ₛ ]ʷ • [ swap ]ʷ) • [ swap ₛ ₛ ]ʷ • [ swap ₛ ]ʷ • [ swap ₛ ₛ ]ʷ ≈⟨ cong refl (cong (_≈_.sym (_≈_.axiom comm)) refl) ⟩
        ([ swap ₛ ]ʷ • [ swap ₛ ₛ ]ʷ) • ([ swap ]ʷ • [ swap ₛ ₛ ₛ ]ʷ) • [ swap ₛ ₛ ]ʷ • [ swap ₛ ]ʷ • [ swap ₛ ₛ ]ʷ ≈⟨ by-assoc Eq.refl ⟩
        [ swap ₛ ]ʷ • ([ swap ₛ ₛ ]ʷ • [ swap ]ʷ) • [ swap ₛ ₛ ₛ ]ʷ • [ swap ₛ ₛ ]ʷ • [ swap ₛ ]ʷ • [ swap ₛ ₛ ]ʷ ≈⟨ cong refl (cong (_≈_.sym (_≈_.axiom comm)) refl) ⟩
        [ swap ₛ ]ʷ • ([ swap ]ʷ • [ swap ₛ ₛ ]ʷ) • [ swap ₛ ₛ ₛ ]ʷ • [ swap ₛ ₛ ]ʷ • [ swap ₛ ]ʷ • [ swap ₛ ₛ ]ʷ ≈⟨ by-assoc Eq.refl ⟩
        ([ swap ₛ ]ʷ • [ swap ]ʷ) • ([ swap ₛ ₛ ]ʷ • [ swap ₛ ₛ ₛ ]ʷ • [ swap ₛ ₛ ]ʷ) • [ swap ₛ ]ʷ • [ swap ₛ ₛ ]ʷ ≈⟨ cong refl (cong (axiom (congₛ (congₛ yang-baxter))) refl) ⟩
        ([ swap ₛ ]ʷ • [ swap ]ʷ) • ([ swap ₛ ₛ ₛ  ]ʷ • [ swap ₛ ₛ ]ʷ • [ swap ₛ ₛ ₛ ]ʷ) • [ swap ₛ ]ʷ • [ swap ₛ ₛ ]ʷ ≈⟨  by-assoc Eq.refl ⟩
        [ swap ₛ ]ʷ • ([ swap ]ʷ • [ swap ₛ ₛ ₛ  ]ʷ) • [ swap ₛ ₛ ]ʷ • ([ swap ₛ ₛ ₛ ]ʷ • [ swap ₛ ]ʷ) • [ swap ₛ ₛ ]ʷ ≈⟨ cong refl (cong (_≈_.axiom comm) (cong refl (cong (sym (axiom (congₛ comm))) refl))) ⟩
        [ swap ₛ ]ʷ • ([ swap ₛ ₛ ₛ  ]ʷ • [ swap ]ʷ) • [ swap ₛ ₛ ]ʷ • ([ swap ₛ ]ʷ • [ swap ₛ ₛ ₛ ]ʷ) • [ swap ₛ ₛ ]ʷ ≈⟨ by-assoc Eq.refl ⟩
        ([ swap ₛ ]ʷ • [ swap ₛ ₛ ₛ  ]ʷ) • [ swap ]ʷ • [ swap ₛ ₛ ]ʷ • [ swap ₛ ]ʷ • [ swap ₛ ₛ ₛ ]ʷ • [ swap ₛ ₛ ]ʷ ≈⟨ cong ( (axiom (congₛ comm))) refl ⟩
        ([ swap ₛ ₛ ₛ  ]ʷ • [ swap ₛ ]ʷ) • [ swap ]ʷ • [ swap ₛ ₛ ]ʷ • [ swap ₛ ]ʷ • [ swap ₛ ₛ ₛ ]ʷ • [ swap ₛ ₛ ]ʷ ≈⟨ by-assoc Eq.refl ⟩
        ([ swap ₛ ₛ ₛ ]ʷ • [ swap ₛ ]ʷ) • ([ swap ]ʷ • [ swap ₛ ₛ ]ʷ) • ([ swap ₛ ]ʷ • [ swap ₛ ₛ ₛ ]ʷ) • [ swap ₛ ₛ ]ʷ ≈⟨ cong refl (cong (_≈_.axiom comm) (cong (axiom (congₛ comm)) refl)) ⟩
        ([ swap ₛ ₛ ₛ ]ʷ • [ swap ₛ ]ʷ) • ([ swap ₛ ₛ ]ʷ • [ swap ]ʷ) • ([ swap ₛ ₛ ₛ ]ʷ • [ swap ₛ ]ʷ) • [ swap ₛ ₛ ]ʷ ≈⟨ by-assoc Eq.refl ⟩
        ([ swap ₛ ₛ ₛ ]ʷ • [ swap ₛ ]ʷ • [ swap ₛ ₛ ]ʷ) • ([ swap ]ʷ • [ swap ₛ ₛ ₛ ]ʷ) • [ swap ₛ ]ʷ • [ swap ₛ ₛ ]ʷ ≈⟨ cong refl (cong (_≈_.axiom comm) refl) ⟩
        ([ swap ₛ ₛ ₛ ]ʷ • [ swap ₛ ]ʷ • [ swap ₛ ₛ ]ʷ) • ([ swap ₛ ₛ ₛ ]ʷ • [ swap ]ʷ) • [ swap ₛ ]ʷ • [ swap ₛ ₛ ]ʷ ≈⟨ by-assoc Eq.refl ⟩
        [ swap ₛ ₛ ₛ ]ʷ • [ swap ₛ ]ʷ • [ swap ₛ ₛ ]ʷ • [ swap ₛ ₛ ₛ ]ʷ • [ swap ]ʷ • [ swap ₛ ]ʷ • [ swap ₛ ₛ ]ʷ ∎

      
  lemma-ract3 {n} (swap• ε , swap• ε) ((swap ₛ) ₛ) = begin
    [ (swap• ε , swap• ε) ]'' • [ (swap ₛ) ₛ ]ʷ ≈⟨ by-assoc Eq.refl ⟩
    [ swap ₛ ]ʷ • [ swap ]ʷ • [ swap ₛ ₛ ]ʷ ≈⟨ cong refl (axiom comm) ⟩
    [ swap ₛ ]ʷ • [ swap ₛ ₛ ]ʷ • [ swap ]ʷ ≈⟨ by-assoc Eq.refl ⟩
    [ ract3 (swap• ε , swap• ε) ((swap ₛ) ₛ) .proj₁ ⇑]'' • [ ract3 (swap• ε , swap• ε) ((swap ₛ) ₛ) .proj₂ ]'' ∎
    where
      open PP (pres (suc (suc n))) using (by-assoc ; word-setoid)
      open SR word-setoid

  lemma-ract3 {n} (swap• swap• c , swap• d) ((x ₛ ₛ)) =
    let  ( w , c' , d') = ract3 (swap• c , d) (x ₛ) in
    let d1 = inject₁ (inject (swap• d)) in
    let d2 = (inject₁ (inject d)) in
    let d3 = (inject₁ (inject (swap• d'))) in
    let d4 = (inject₁ (inject (d'))) in
    begin
    [ (swap• (swap• c) , swap• d) ]'' • [ ((x ₛ) ₛ) ]ʷ ≈⟨ refl ⟩
    ( ( [ swap ₛ ]ʷ • [ swap ₛ ₛ ]ʷ • [ [ [ [ c ] ⇑] ⇑] ⇑]) • [ d1 ] ) • [ ((x ₛ) ₛ) ]ʷ ≈⟨ _≈₃_.refl ⟩
    ( ( [ swap ₛ ]ʷ • [ swap ₛ ₛ ]ʷ • [ [ [ [ c ] ⇑] ⇑] ⇑]) • [ swap• d2 ] ) • [ ((x ₛ) ₛ) ]ʷ ≈⟨ special-assoc (((□ • □ • □) • □ • □) • □) ((□ • □) • (□ • □) • □ • □) Eq.refl ⟩
    ( [ swap ₛ ]ʷ • [ swap ₛ ₛ ]ʷ) • ([ [ [ [ c ] ⇑] ⇑] ⇑] • [ swap ]ʷ) • [ [ d2 ] ⇑] • [ ((x ₛ) ₛ) ]ʷ ≈⟨ cong refl (cong ( lemma-comm [ [ c ] ⇑]) refl) ⟩
    ( [ swap ₛ ]ʷ • [ swap ₛ ₛ ]ʷ) • ([ swap ]ʷ • [ [ [ [ c ] ⇑] ⇑] ⇑]) • [ [ d2 ] ⇑] • [ ((x ₛ) ₛ) ]ʷ ≈⟨ special-assoc ((□ • □) • (□ • □) • □ • □) (□ • (□ • □) • □ • □ • □) Eq.refl  ⟩
    [ swap ₛ ]ʷ • ([ swap ₛ ₛ ]ʷ • [ swap ]ʷ) • [ [ [ [ c ] ⇑] ⇑] ⇑] • [ [ d2 ] ⇑] • [ ((x ₛ) ₛ) ]ʷ ≈⟨ cong refl (cong ( lemma-comm [ swap ]ʷ) refl) ⟩
    [ swap ₛ ]ʷ • ([ swap ]ʷ • [ swap ₛ ₛ ]ʷ) • [ [ [ [ c ] ⇑] ⇑] ⇑] • [ [ d2 ] ⇑] • [ ((x ₛ) ₛ) ]ʷ ≈⟨ special-assoc (□ • (□ • □) • □ • □ • □) ((□ • □) • ((□ • □) • □) • □)  Eq.refl ⟩
    ([ swap ₛ ]ʷ • [ swap ]ʷ) • [ [ [ swap• c ] ⇑] • [ d2 ] ⇑] • [ ((x ₛ) ₛ) ]ʷ ≈⟨ _≈₃_.assoc ⟩
    [ swap ₛ ]ʷ • [ swap ]ʷ • [ [ swap• c , d ]'' • [ (x ₛ) ]ʷ ⇑] ≈⟨ cong refl (cong refl ([⇑]-cong _ _ (lemma-ract3 (swap• c , d) (x ₛ)))) ⟩
    [ swap ₛ ]ʷ • [ swap ]ʷ • [ [ w ⇑]'' • [ c' , d' ]'' ⇑] ≈⟨ special-assoc (□ • □ • (□ • □ • □)) ((□ • □ • □) • □ • □) Eq.refl ⟩
    ( [ swap ₛ ]ʷ • [ swap ]ʷ • [ [ w ⇑]'' ⇑]) • [ [ c' , d' ]'' ⇑] ≈⟨ cong (claim w) refl ⟩
    ([  fm w ⇑]'' • ( [ swap ₛ ]ʷ) • [ swap ]ʷ) • [ [ c' , d' ]'' ⇑] ≈⟨ special-assoc ((□ • □ • □) • □ • □) (□ • □ • □ • □ • □) Eq.refl ⟩
    [  fm w ⇑]'' • [ swap ₛ ]ʷ • [ swap ]ʷ • [ [ [ c' ] ⇑] • [ d4 ] ⇑] ≈⟨ cong refl (cong refl (_≈₃_.sym _≈₃_.assoc)) ⟩
    [  fm w ⇑]'' • [ swap ₛ ]ʷ • ([ swap ]ʷ • [ [ [ c' ] ⇑] ⇑]) • [ [ d4 ] ⇑] ≈⟨ cong refl (cong refl (cong (sym (lemma-comm [ c' ])) refl)) ⟩
    [  fm w ⇑]'' • [ swap ₛ ]ʷ • ([ [ [ c' ] ⇑] ⇑] • [ swap ]ʷ) • [ [ d4 ] ⇑] ≈⟨ special-assoc (□ • □ • (□ • □) • □) (□ • (□ • □) • □ • □) Eq.refl ⟩
    [  fm w ⇑]'' • ( [ swap ₛ ]ʷ • [ [ [ c' ] ⇑] ⇑]) • [ swap ]ʷ • [ [ d4 ] ⇑] ≈⟨ _≈₃_.refl ⟩
    [  fm w ⇑]'' • [ [ swap• c' ] ⇑] • [ swap• d4 ] ≈⟨ refl ⟩
    [  fm w ⇑]'' • [ [ swap• c' ] ⇑] • [ d3 ] ≈⟨ refl ⟩
    [  fm w ⇑]'' • [ swap• c' , swap• d' ]''  ≡⟨ Eq.sym (Eq.cong₂  (\ x y -> [  x ⇑]'' • [ y ]'') (Eq.cong proj₁ (ler3 c d x)) (Eq.cong proj₂ (ler3 c d x))) ⟩
    [  ract3 (swap• swap• c , swap• d) ((x ₛ) ₛ) .proj₁ ⇑]'' • [ ract3 (swap• swap• c , swap• d) ((x ₛ) ₛ) .proj₂ ]''  ∎
    where
      open PB (pres (suc (suc ( n)))) using () renaming (refl' to refl'' ; _≈_ to _≈₃_)
      open PP (pres (suc (suc ( n)))) using (by-assoc ; word-setoid ; module Pattern-Assoc)
      open SR word-setoid
      open Pattern-Assoc

      claim : ∀ w -> [ swap ₛ ]ʷ • [ swap ]ʷ • [ [ w ⇑]'' ⇑] ≈₃  [ fm w ⇑]'' • [ swap ₛ ]ʷ • [ swap ]ʷ
      claim ε = by-assoc Eq.refl
      claim (w • v) = begin
        [ swap ₛ ]ʷ • [ swap ]ʷ • [ [ w • v ⇑]'' ⇑] ≈⟨ _≈₃_.refl ⟩
        [ swap ₛ ]ʷ • [ swap ]ʷ • [ [ w ⇑]'' ⇑] • [ [ v ⇑]'' ⇑] ≈⟨ by-assoc Eq.refl ⟩
        ([ swap ₛ ]ʷ • [ swap ]ʷ • [ [ w ⇑]'' ⇑]) • [ [ v ⇑]'' ⇑] ≈⟨ cong (claim w) refl ⟩
        ([ fm w ⇑]'' • [ swap ₛ ]ʷ • [ swap ]ʷ) • [ [ v ⇑]'' ⇑] ≈⟨ special-assoc ((□ • □ • □) • □ ) (□ • □ • □ • □ ) Eq.refl ⟩
        [ fm w ⇑]'' • [ swap ₛ ]ʷ • [ swap ]ʷ • [ [ v ⇑]'' ⇑] ≈⟨ cong refl (claim v) ⟩
        [ fm w ⇑]'' • [ fm v ⇑]'' • [ swap ₛ ]ʷ • [ swap ]ʷ ≈⟨ _≈₃_.sym _≈₃_.assoc ⟩
        [ fm (w • v) ⇑]'' • [ swap ₛ ]ʷ • [ swap ]ʷ ∎

      claim w@([ inj₁ swap ]ʷ) = begin
        [ swap ₛ ]ʷ • [ swap ]ʷ • [ [ w ⇑]'' ⇑] ≈⟨ _≈₃_.refl ⟩
        [ swap ₛ ]ʷ • [ swap ]ʷ • [ swap ₛ ]ʷ ≈⟨ _≈₃_.sym (_≈₃_.axiom yang-baxter) ⟩
        [ swap ]ʷ • [ swap ₛ ]ʷ • [ swap ]ʷ ≈⟨ _≈₃_.refl ⟩
        [ fm w ⇑]'' • [ swap ₛ ]ʷ • [ swap ]ʷ ∎

      claim w@([ inj₂ y@(swap) ]ʷ) = begin
        [ swap ₛ ]ʷ • [ swap ]ʷ • [ [ w ⇑]'' ⇑] ≈⟨ _≈₃_.refl ⟩
        [ swap ₛ ]ʷ • [ swap ]ʷ • [ y ₛ ₛ ₛ ]ʷ ≈⟨ sym (cong refl (lemma-comm [ y ₛ ]ʷ)) ⟩
        [ swap ₛ ]ʷ • [ y ₛ ₛ ₛ ]ʷ • [ swap ]ʷ ≈⟨ _≈₃_.sym _≈₃_.assoc ⟩
        ([ swap ₛ ]ʷ • [ y ₛ ₛ ₛ ]ʷ) • [ swap ]ʷ ≈⟨ cong (sym ([⇑]-cong _ _ (lemma-comm [ y ]ʷ))) refl ⟩
        ([ y ₛ ₛ ₛ ]ʷ • [ swap ₛ ]ʷ) • [ swap ]ʷ ≈⟨ _≈₃_.assoc ⟩
        [ fm w ⇑]'' • [ swap ₛ ]ʷ • [ swap ]ʷ ∎

      claim w@([ inj₂ y@(y' ₛ) ]ʷ) = begin
        [ swap ₛ ]ʷ • [ swap ]ʷ • [ [ w ⇑]'' ⇑] ≈⟨ _≈₃_.refl ⟩
        [ swap ₛ ]ʷ • [ swap ]ʷ • [ y ₛ ₛ ₛ ]ʷ ≈⟨ sym (cong refl (lemma-comm [ y ₛ ]ʷ)) ⟩
        [ swap ₛ ]ʷ • [ y ₛ ₛ ₛ ]ʷ • [ swap ]ʷ ≈⟨ _≈₃_.sym _≈₃_.assoc ⟩
        ([ swap ₛ ]ʷ • [ y ₛ ₛ ₛ ]ʷ) • [ swap ]ʷ ≈⟨ cong (sym ([⇑]-cong _ _ (lemma-comm [ y ]ʷ))) refl ⟩
        ([ y ₛ ₛ ₛ ]ʷ • [ swap ₛ ]ʷ) • [ swap ]ʷ ≈⟨ _≈₃_.assoc ⟩
        [ fm w ⇑]'' • [ swap ₛ ]ʷ • [ swap ]ʷ ∎





  lemma-ract3 {n} (swap• ε , swap• ε) (((x ₛ) ₛ) ₛ) = begin
    [ (swap• ε , swap• ε) ]'' • [(((x ₛ) ₛ) ₛ) ]ʷ ≈⟨ by-assoc Eq.refl ⟩
    [ swap ₛ ]ʷ • [ swap ]ʷ • [(((x ₛ) ₛ) ₛ) ]ʷ ≈⟨ cong refl (_≈_.axiom comm) ⟩
    [ swap ₛ ]ʷ • [(((x ₛ) ₛ) ₛ) ]ʷ • [ swap ]ʷ ≈⟨ _≈_.sym _≈_.assoc ⟩
    ([ swap ₛ ]ʷ • [(((x ₛ) ₛ) ₛ) ]ʷ) • [ swap ]ʷ ≈⟨ cong (axiom (congₛ comm)) refl  ⟩
    ([(((x ₛ) ₛ) ₛ) ]ʷ • [ swap ₛ ]ʷ) • [ swap ]ʷ ≈⟨ _≈_.assoc ⟩
    [(((x ₛ) ₛ) ₛ) ]ʷ • [ swap ₛ ]ʷ • [ swap ]ʷ ≈⟨ by-assoc Eq.refl ⟩
    [ ract3 (swap• ε , swap• ε) (((x ₛ) ₛ) ₛ) .proj₁ ⇑]'' • [ ract3 (swap• ε , swap• ε) (((x ₛ) ₛ) ₛ) .proj₂ ]'' ∎
    where
      open PB (pres (suc (suc n))) renaming (Alphabet to Sₙ₊₂) using (_≈_)
      open PP (pres (suc (suc n))) renaming (word-setoid to wsh) using (by-assoc)
      open SR wsh



  lemma-racts' : ∀ {n} c bs ->
    let open PB (pres n) renaming (Alphabet to Sn ; _≈_ to _≈ₙ_) using () in
    let open PB (pres (suc (suc n))) renaming (Alphabet to Sₙ₊₂) using (_≈_) in
    let (x' , c') = racts' {n} c bs in ([ c ]' • bs) ≈ ([ x' ⇑]'' • [ c' ]') 
  lemma-racts' {n} c [ x ]ʷ = lemma-ract' c x
  lemma-racts' {n} c ε = _≈_.trans _≈_.right-unit (_≈_.sym _≈_.left-unit)
    where
      open PB (pres (suc (suc n))) renaming (Alphabet to Sₙ₊₂) using (_≈_)
      open PP (pres (suc (suc n))) renaming (word-setoid to wsh) using ()
      open SR wsh
  lemma-racts' {n} c (bs • as) with racts' c bs | inspect (racts' c) bs | lemma-racts' c bs
  ... | (bs' , c') | [ eq1 ]ₑ | ih1 with racts' c' as | inspect (racts' c') as | lemma-racts' c' as
  ... | (as' , c'') | [ eq2 ]ₑ | ih2 = begin
    [ c ]' • (bs • as) ≈⟨ _≈_.sym _≈_.assoc ⟩
    ([ c ]' • bs) • as ≈⟨ _≈_.cong ih1 _≈_.refl ⟩
    ([ bs' ⇑]'' • [ c' ]') • as ≈⟨ _≈_.assoc ⟩
    [ bs' ⇑]'' • [ c' ]' • as ≈⟨ _≈_.cong _≈_.refl ih2 ⟩
    [ bs' ⇑]'' • [ as' ⇑]'' • [ c'' ]' ≈⟨ _≈_.sym _≈_.assoc ⟩
    [ bs' • as' ⇑]'' • [ c'' ]' ∎
    where
      open PB (pres (suc (suc n))) renaming (Alphabet to Sₙ₊₂) using (_≈_)
      open PP (pres (suc (suc n))) renaming (word-setoid to wsh) using ()
      open SR wsh



  lemma-racts'' : ∀ {n} c bs ->
    let open PB (pres n) renaming (Alphabet to Sn ; _≈_ to _≈ₙ_) using () in
    let open PB (pres (suc (suc n))) renaming (Alphabet to Sₙ₊₂) using (_≈_) in
    let (x' , c') = racts'' {n} c bs in ([ c ]'' • bs) ≈ ([ x' ⇑]'' • [ c' ]'') 
  lemma-racts'' {n} c [ x ]ʷ = lemma-ract'' c x
  lemma-racts'' {n} c ε = _≈_.trans _≈_.right-unit (_≈_.sym _≈_.left-unit)
    where
      open PB (pres (suc (suc n))) renaming (Alphabet to Sₙ₊₂) using (_≈_)
      open PP (pres (suc (suc n))) renaming (word-setoid to wsh) using ()
      open SR wsh
  lemma-racts'' {n} c (bs • as) with racts'' c bs | inspect (racts'' c) bs | lemma-racts'' c bs
  ... | (bs' , c') | [ eq1 ]ₑ | ih1 with racts'' c' as | inspect (racts'' c') as | lemma-racts'' c' as
  ... | (as' , c'') | [ eq2 ]ₑ | ih2 = begin
    [ c ]'' • (bs • as) ≈⟨ _≈_.sym _≈_.assoc ⟩
    ([ c ]'' • bs) • as ≈⟨ _≈_.cong ih1 _≈_.refl ⟩
    ([ bs' ⇑]'' • [ c' ]'') • as ≈⟨ _≈_.assoc ⟩
    [ bs' ⇑]'' • [ c' ]'' • as ≈⟨ _≈_.cong _≈_.refl ih2 ⟩
    [ bs' ⇑]'' • [ as' ⇑]'' • [ c'' ]'' ≈⟨ _≈_.sym _≈_.assoc ⟩
    [ bs' • as' ⇑]'' • [ c'' ]'' ∎
    where
      open PB (pres (suc (suc n))) renaming (Alphabet to Sₙ₊₂) using (_≈_)
      open PP (pres (suc (suc n))) renaming (word-setoid to wsh) using ()
      open SR wsh


  lemma-racts3 : ∀ {n} c bs ->
    let open PB (pres n) renaming (Alphabet to Sn ; _≈_ to _≈ₙ_) using () in
    let open PB (pres (suc (suc n))) renaming (Alphabet to Sₙ₊₂) using (_≈_) in
    let (x' , c') = racts3 {n} c bs in ([ c ]'' • bs) ≈ ([ x' ⇑]'' • [ c' ]'') 
  lemma-racts3 {n} c [ x ]ʷ = lemma-ract3 c x
  lemma-racts3 {n} c ε = _≈_.trans _≈_.right-unit (_≈_.sym _≈_.left-unit)
    where
      open PB (pres (suc (suc n))) renaming (Alphabet to Sₙ₊₂) using (_≈_)
      open PP (pres (suc (suc n))) renaming (word-setoid to wsh) using ()
      open SR wsh
  lemma-racts3 {n} c (bs • as) with racts3 c bs | inspect (racts3 c) bs | lemma-racts3 c bs
  ... | (bs' , c') | [ eq1 ]ₑ | ih1 with racts3 c' as | inspect (racts3 c') as | lemma-racts3 c' as
  ... | (as' , c'') | [ eq2 ]ₑ | ih2 = begin
    [ c ]'' • (bs • as) ≈⟨ _≈_.sym _≈_.assoc ⟩
    ([ c ]'' • bs) • as ≈⟨ _≈_.cong ih1 _≈_.refl ⟩
    ([ bs' ⇑]'' • [ c' ]'') • as ≈⟨ _≈_.assoc ⟩
    [ bs' ⇑]'' • [ c' ]'' • as ≈⟨ _≈_.cong _≈_.refl ih2 ⟩
    [ bs' ⇑]'' • [ as' ⇑]'' • [ c'' ]'' ≈⟨ _≈_.sym _≈_.assoc ⟩
    [ bs' • as' ⇑]'' • [ c'' ]'' ∎
    where
      open PB (pres (suc (suc n))) renaming (Alphabet to Sₙ₊₂) using (_≈_)
      open PP (pres (suc (suc n))) renaming (word-setoid to wsh) using ()
      open SR wsh



  aux-c : ∀ {n} w ->
    let f = emb2' {n} in
    (f *) [ w ]ᵣ ≡ [ [ w ⇑] ⇑]
  aux-c {n} [ swap ]ʷ = Eq.refl
  aux-c {n} [ x ₛ ]ʷ = Eq.refl
  aux-c {n} ε = Eq.refl
  aux-c {n} (w • w₁) rewrite aux-c w | aux-c w₁ = Eq.refl


  open import Presentation.CosetNF as CNF


  module myData (n : ℕ) = Data (pres 1 ⊕ pres n) (pres (suc (suc n))) (CC (suc n)) (ε , ε) emb2' ract3 [_]''
    
  import Presentation.Construct.Properties.DirectProduct as DP

  lemma-ract''-suc' : ∀ {n} w ->
    let open PB (pres 1 ⊕ pres n) renaming ( _≈_ to _≈₁_ ; _===_ to _===₁_) using () in
    let _~_ = PW.Pointwise _≈₁_ (_≡_ {A = CC (suc n)}) in
    ((ract'' {n}) **) (ε , ε) [ [ w ⇑] ⇑] ~ ([ w ]ᵣ , (ε , ε))
  lemma-ract''-suc' {n} [ x ]ʷ = right-unit , Eq.refl
  lemma-ract''-suc' {n} ε = refl , Eq.refl
  lemma-ract''-suc' {n} (w • w₁) with racts'' (ε , ε) [ [ w ⇑] ⇑] | (lemma-ract''-suc' w)
  ... | (w1 , cd1) | (h1l , h1r) rewrite h1r with racts'' (ε , ε) [ [ w₁ ⇑] ⇑] | (lemma-ract''-suc' w₁)
  ... | (w2 , cd2) | (h2l , h2r) = cong h1l h2l , h2r


  lemma-ract''-suc'' : ∀ {n} w ->
    let open PB (pres 1 ⊕ pres (suc n)) renaming ( _≈_ to _≈₁_ ; _===_ to _===₁_) using () in
    let _~_ = PW.Pointwise _≈₁_ (_≡_ {A = CC (suc (suc n))}) in
    ((ract'' {suc n}) **) (swap• ε , ε) [ [ [ w ⇑] ⇑] ⇑] ~ ([ [ w ⇑] ]ᵣ , (swap• ε , ε))
  lemma-ract''-suc'' {n} [ x ]ʷ = right-unit , Eq.refl
  lemma-ract''-suc'' {n} ε = refl , Eq.refl
  lemma-ract''-suc'' {n} (w • w₁) with racts'' (swap• ε , ε) [ [ [ w ⇑] ⇑] ⇑] | (lemma-ract''-suc'' w)
  ... | (w1 , cd1) | (h1l , h1r) rewrite h1r with racts'' (swap• ε , ε) [ [ [ w₁ ⇑] ⇑] ⇑] | (lemma-ract''-suc'' w₁)
  ... | (w2 , cd2) | (h2l , h2r) = cong h1l h2l , h2r


  auxr3a : ∀ {n} -> 
    let open PB (pres (suc (suc n))) renaming (Alphabet to Sₙ₊₂ ; _≈_ to _≈₂_ ; _===_ to _===₂_) using () in
    let open PB (pres n) renaming (Alphabet to Sn ; _≈_ to _≈ₙ_) using () in
    let open PB (pres 1 ⊕ pres n) renaming ( _≈_ to _≈₁_ ; _===_ to _===₁_) using () in
    let _~_ = PW.Pointwise _≈₁_ (_≡_ {A = CC (suc n)}) in
    let c = (ε , ε) in ∀ (w) -> (racts3 c [ [ w ⇑] ⇑]) ~ ([ w ]ᵣ , c)
  auxr3a {n} w@([ x ]ʷ) = refl , Eq.refl
  auxr3a {n} ε = refl , Eq.refl
  auxr3a {n} (w • v) =
    let c = (ε , ε) in
    let (w' , c') = racts3 (ε , ε) [ [ w ⇑] ⇑] in
    let (v' , c'') = racts3 c [ [ v ⇑] ⇑] in
    begin
    (racts3 c [ [ w • v ⇑] ⇑]) ≈⟨ refl , Eq.refl ⟩
    racts3 c ([ [ w  ⇑] ⇑] • [ [ v ⇑] ⇑]) ≈⟨ refl , Eq.refl ⟩
    (w' • racts3 c' [ [ v ⇑] ⇑] .proj₁ , racts3 c' [ [ v ⇑] ⇑] .proj₂) ≡⟨ Eq.cong
                                                                            (λ x →
                                                                               w' • racts3 x [ [ v ⇑] ⇑] .proj₁ , racts3 x [ [ v ⇑] ⇑] .proj₂)
                                                                            ( proj₂ (auxr3a {n} w)) ⟩
    (w' • racts3 c [ [ v ⇑] ⇑] .proj₁ , racts3 c [ [ v ⇑] ⇑] .proj₂) ≈⟨ refl , Eq.refl ⟩
    (w' • v' , c'') ≈⟨ cong (auxr3a w .proj₁) (auxr3a v .proj₁) , (auxr3a v .proj₂) ⟩
    ([ w ]ᵣ • [ v ]ᵣ , c) ≈⟨ refl , Eq.refl ⟩
    ([ w • v ]ᵣ , c) ∎
    where
      open PP (pres (suc (suc n))) using (by-assoc ; word-setoid)
      open PP (pres 1 ⊕ pres n) renaming (word-setoid to ws)
      ts = ×-setoid ws (setoid (CC (suc n)))
      open SR ts
    


  auxr3b : ∀ {n1} -> let n = suc n1 in 
    let open PB (pres (suc (suc n))) renaming (Alphabet to Sₙ₊₂ ; _≈_ to _≈₂_ ; _===_ to _===₂_) using () in
    let open PB (pres n) renaming (Alphabet to Sn ; _≈_ to _≈ₙ_) using () in
    let open PB (pres 1 ⊕ pres n) renaming ( _≈_ to _≈₁_ ; _===_ to _===₁_) using () in
    let _~_ = PW.Pointwise _≈₁_ (_≡_ {A = CC (suc n)}) in
    let c = (swap• ε , ε) in ∀ (w) -> (racts3 c [ [ [ w ⇑] ⇑] ⇑]) ~ ([ [ w ⇑] ]ᵣ , c)
  auxr3b {n} w@([ x ]ʷ) = refl , Eq.refl
  auxr3b {n} ε = refl , Eq.refl
  auxr3b {n1} (w • v) =
    let n = suc n1 in
    let c = (swap• ε , ε) in
    let (w' , c') = racts3 c [ [ [ w ⇑] ⇑] ⇑] in
    let (v' , c'') = racts3 c [ [ [ v ⇑] ⇑] ⇑] in
    begin
    (racts3 c [ [ [ w • v ⇑] ⇑] ⇑]) ≈⟨ refl , Eq.refl ⟩
    racts3 c ([ [ [ w  ⇑] ⇑] ⇑] • [ [ [ v ⇑] ⇑] ⇑]) ≈⟨ refl , Eq.refl ⟩
    (w' • racts3 c' [ [ [ v ⇑] ⇑] ⇑] .proj₁ , racts3 c' [ [ [ v ⇑] ⇑] ⇑] .proj₂) ≡⟨ Eq.cong
                                                                            (λ x →
                                                                               w' • racts3 x [ [ [ v ⇑] ⇑] ⇑] .proj₁ , racts3 x [ [ [ v ⇑] ⇑] ⇑] .proj₂)
                                                                            ( proj₂ (auxr3b  w)) ⟩
    (w' • racts3 c [ [ [ v ⇑] ⇑] ⇑] .proj₁ , racts3 c [ [ [ v ⇑] ⇑] ⇑] .proj₂) ≈⟨ refl , Eq.refl ⟩
    (w' • v' , c'') ≈⟨ cong (auxr3b w .proj₁) (auxr3b v .proj₁) , (auxr3b v .proj₂) ⟩
    ([ [ w ⇑] ]ᵣ • [ [ v ⇑] ]ᵣ , c) ≈⟨ refl , Eq.refl ⟩
    ([ [ w • v ⇑] ]ᵣ , c) ∎
    where
      n = suc n1
      open PP (pres (suc (suc n))) using (by-assoc ; word-setoid)
      open PP (pres 1 ⊕ pres n) renaming (word-setoid to ws)
      ts = ×-setoid ws (setoid (CC (suc n)))
      open SR ts
    




{-
  qc5 : ∀ (c : CC 5) x ->
    let open PB (pres 1 ⊕ pres 4) renaming ( _≈_ to _≈₁_ ; _===_ to _===₁_) using () in
    let _~_ = PW.Pointwise _≈₁_ (_≡_ {A = CC 5}) in
    ract'' c x ~ ract3 c x
  qc5 (ε , ε) swap = PB.left-unit , Eq.refl
  qc5 (swap• ε , ε) swap = PB.left-unit , Eq.refl
  qc5 (swap• swap• ε , ε) swap = PB.left-unit , Eq.refl
  qc5 (swap• swap• swap• ε , ε) swap = PB.left-unit , Eq.refl
  qc5 (swap• swap• swap• swap• ε , ε) swap = PB.left-unit , Eq.refl
  qc5 (swap• swap• swap• swap• swap• ε , ε) swap = PB.left-unit , Eq.refl
  qc5 (swap• ε , swap• ε) swap = PB.left-unit , Eq.refl
  qc5 (swap• swap• c , swap• ε) swap = PB.left-unit , Eq.refl
  qc5 (swap• swap• ε , swap• swap• ε) swap = PB.right-unit , Eq.refl
  qc5 (swap• swap• swap• c , swap• swap• ε) swap = PB.right-unit , Eq.refl
  qc5 (swap• swap• swap• ε , swap• swap• swap• ε) swap = PB.right-unit , Eq.refl
  qc5 (swap• swap• swap• swap• c , swap• swap• swap• ε) swap = PB.right-unit , Eq.refl
  qc5 (swap• swap• swap• swap• ε , swap• swap• swap• swap• ε) swap = PB.right-unit , Eq.refl
  qc5 (swap• swap• swap• swap• swap• c , swap• swap• swap• swap• ε) swap = PB.right-unit , Eq.refl
  qc5 (swap• swap• swap• swap• swap• ε , swap• swap• swap• swap• swap• ε) swap = PB.right-unit , Eq.refl
  qc5 (ε , ε) (swap ₛ) = PB.left-unit , Eq.refl
  qc5 (ε , ε) ((swap ₛ) ₛ) = PB.right-unit , Eq.refl
  qc5 (ε , ε) (((x ₛ) ₛ) ₛ) = PB.right-unit , Eq.refl
  qc5 (swap• ε , ε) (swap ₛ) = PB.left-unit , Eq.refl
  qc5 (swap• swap• ε , ε) (swap ₛ) = {!ract3 (swap• swap• ε , ε) (swap ₛ)!}
  qc5 (swap• swap• swap• c , ε) (swap ₛ) = PB.right-unit , Eq.refl
  qc5 (swap• c , ε) ((x ₛ) ₛ) = {!!}
  qc5 (swap• c , swap• d) (swap ₛ) = {!!}
  qc5 (swap• c , swap• d) ((x ₛ) ₛ) = {!!}

-}


{-

  qc : ∀ (c : CC 8) x ->
    let open PB (pres 1 ⊕ pres 7) renaming ( _≈_ to _≈₁_ ; _===_ to _===₁_) using () in
    let _~_ = PW.Pointwise _≈₁_ (_≡_ {A = CC 8}) in
    ract'' c x ~ ract3 c x

  qc (ε , ε) swap = PB.left-unit , Eq.refl
  qc (swap• ε , ε) swap = PB.left-unit , Eq.refl
  qc (swap• swap• ε , ε) swap = PB.left-unit , Eq.refl
  qc (swap• swap• swap• ε , ε) swap = PB.left-unit , Eq.refl
  qc (swap• swap• swap• swap• c , ε) swap = PB.left-unit , Eq.refl
  qc (swap• ε , swap• ε) swap = PB.left-unit , Eq.refl
  qc (swap• swap• ε , swap• ε) swap = PB.left-unit , Eq.refl
  qc (swap• swap• swap• ε , swap• ε) swap = PB.left-unit , Eq.refl
  qc (swap• swap• swap• swap• c , swap• ε) swap = PB.left-unit , Eq.refl
  qc (swap• swap• ε , swap• swap• ε) swap = PB.right-unit , Eq.refl
  qc (swap• swap• swap• c , swap• swap• ε) swap = PB.right-unit , Eq.refl
  qc (swap• swap• swap• ε , swap• swap• swap• ε) swap = PB.right-unit , Eq.refl
  qc (swap• swap• swap• swap• c , swap• swap• swap• ε) swap = PB.right-unit , Eq.refl
  qc (swap• swap• swap• swap• ε , swap• swap• swap• swap• ε) swap = PB.right-unit , Eq.refl
  qc (swap• swap• swap• swap• swap• c , swap• swap• swap• swap• ε) swap = PB.right-unit , Eq.refl
  qc (swap• swap• swap• swap• swap• ε , swap• swap• swap• swap• swap• ε) swap = PB.right-unit , Eq.refl
  qc (swap• swap• swap• swap• swap• swap• c , swap• swap• swap• swap• swap• ε) swap = PB.right-unit , Eq.refl
  qc (swap• swap• swap• swap• swap• swap• ε , swap• swap• swap• swap• swap• swap• ε) swap = PB.right-unit , Eq.refl
  qc (swap• swap• swap• swap• swap• swap• swap• c , swap• swap• swap• swap• swap• swap• ε) swap = PB.right-unit , Eq.refl
  qc (swap• swap• swap• swap• swap• swap• swap• ε , swap• swap• swap• swap• swap• swap• swap• ε) swap = PB.right-unit , Eq.refl
  qc (swap• swap• swap• swap• swap• swap• swap• swap• c , swap• swap• swap• swap• swap• swap• swap• ε) swap = PB.right-unit , Eq.refl
  qc (swap• swap• swap• swap• swap• swap• swap• swap• ε , swap• swap• swap• swap• swap• swap• swap• swap• ε) swap = PB.right-unit , Eq.refl
  qc (ε , ε) (swap ₛ) = PB.left-unit , Eq.refl
  qc (ε , ε) ((x ₛ) ₛ) = PB.right-unit , Eq.refl
  qc (swap• ε , ε) (swap ₛ) = PB.left-unit , Eq.refl
  qc (swap• swap• ε , ε) (swap ₛ) = PB.right-unit , Eq.refl
  qc (swap• swap• swap• ε , ε) (swap ₛ) = PB.right-unit , Eq.refl
  qc (swap• swap• swap• swap• c , ε) (swap ₛ) = PB.right-unit , Eq.refl
  qc (swap• ε , ε) ((swap ₛ) ₛ) = PB.left-unit , Eq.refl
  qc (swap• ε , ε) (((x ₛ) ₛ) ₛ) = PB.right-unit , Eq.refl
  qc (swap• swap• ε , ε) ((swap ₛ) ₛ) = PB.left-unit , Eq.refl
  qc (swap• swap• swap• c , ε) ((swap ₛ) ₛ) = PB.right-unit , Eq.refl

  qc (swap• swap• ε , ε) (((swap ₛ) ₛ) ₛ) = PB.left-unit , Eq.refl
  qc (swap• swap• ε , ε) ((((x ₛ) ₛ) ₛ) ₛ) = PB.right-unit , Eq.refl
  qc (swap• swap• swap• ε , ε) (((swap ₛ) ₛ) ₛ) = PB.left-unit , Eq.refl
  qc (swap• swap• swap• ε , ε) ((((swap ₛ) ₛ) ₛ) ₛ) = PB.left-unit , Eq.refl
  qc (swap• swap• swap• ε , ε) (((((x ₛ) ₛ) ₛ) ₛ) ₛ) = PB.right-unit , Eq.refl
  qc (swap• swap• swap• swap• c , ε) (((swap ₛ) ₛ) ₛ) = PB.right-unit , Eq.refl
  qc (swap• swap• swap• swap• ε , ε) ((((swap ₛ) ₛ) ₛ) ₛ) = PB.left-unit , Eq.refl
  qc (swap• swap• swap• swap• ε , ε) (((((swap ₛ) ₛ) ₛ) ₛ) ₛ) = PB.left-unit , Eq.refl
  qc (swap• swap• swap• swap• ε , ε) ((((((x ₛ) ₛ) ₛ) ₛ) ₛ) ₛ) = PB.right-unit , Eq.refl
  qc (swap• swap• swap• swap• swap• c , ε) ((((swap ₛ) ₛ) ₛ) ₛ) = PB.right-unit , Eq.refl
  qc (swap• swap• swap• swap• swap• ε , ε) (((((swap ₛ) ₛ) ₛ) ₛ) ₛ) = PB.left-unit , Eq.refl
  qc (swap• swap• swap• swap• swap• ε , ε) ((((((swap ₛ) ₛ) ₛ) ₛ) ₛ) ₛ) = PB.left-unit , Eq.refl
  qc (swap• swap• swap• swap• swap• ε , ε) (((((((x ₛ) ₛ) ₛ) ₛ) ₛ) ₛ) ₛ) = PB.right-unit , Eq.refl
  qc (swap• swap• swap• swap• swap• swap• c , ε) (((((swap ₛ) ₛ) ₛ) ₛ) ₛ) = PB.right-unit , Eq.refl
  qc (swap• swap• swap• swap• swap• swap• ε , ε) ((((((swap ₛ) ₛ) ₛ) ₛ) ₛ) ₛ) = PB.left-unit , Eq.refl
  qc (swap• swap• swap• swap• swap• swap• ε , ε) (((((((swap ₛ) ₛ) ₛ) ₛ) ₛ) ₛ) ₛ) = PB.left-unit , Eq.refl
  qc (swap• swap• swap• swap• swap• swap• ε , ε) ((((((((x ₛ) ₛ) ₛ) ₛ) ₛ) ₛ) ₛ) ₛ) = PB.right-unit , Eq.refl
  qc (swap• swap• swap• swap• swap• swap• swap• c , ε) ((((((swap ₛ) ₛ) ₛ) ₛ) ₛ) ₛ) = PB.right-unit , Eq.refl
  qc (swap• swap• swap• swap• swap• swap• swap• ε , ε) (((((((swap ₛ) ₛ) ₛ) ₛ) ₛ) ₛ) ₛ) = PB.left-unit , Eq.refl
  qc (swap• swap• swap• swap• swap• swap• swap• swap• c , ε) (((((((swap ₛ) ₛ) ₛ) ₛ) ₛ) ₛ) ₛ) = PB.right-unit , Eq.refl
  qc (swap• swap• swap• swap• swap• swap• swap• ε , ε) ((((((((swap ₛ) ₛ) ₛ) ₛ) ₛ) ₛ) ₛ) ₛ) = PB.left-unit , Eq.refl
  qc (swap• swap• swap• swap• swap• swap• swap• swap• ε , ε) ((((((((swap ₛ) ₛ) ₛ) ₛ) ₛ) ₛ) ₛ) ₛ) = PB.left-unit , Eq.refl
  qc (swap• ε , swap• ε) (swap ₛ) = PB.left-unit , Eq.refl
  qc (swap• swap• ε , swap• ε) (swap ₛ) = PB.left-unit , Eq.refl
  qc (swap• swap• swap• c , swap• ε) (swap ₛ) = PB.left-unit , Eq.refl
  qc (swap• swap• ε , swap• swap• ε) (swap ₛ) = PB.left-unit , Eq.refl
  qc (swap• swap• swap• ε , swap• swap• ε) (swap ₛ) = PB.left-unit , Eq.refl
  qc (swap• swap• swap• ε , swap• swap• swap• ε) (swap ₛ) = PB.right-unit , Eq.refl
  qc (swap• swap• swap• swap• c , swap• swap• ε) (swap ₛ) = PB.left-unit , Eq.refl
  qc (swap• swap• swap• swap• ε , swap• swap• swap• ε) (swap ₛ) = PB.right-unit , Eq.refl
  qc (swap• swap• swap• swap• ε , swap• swap• swap• swap• ε) (swap ₛ) = PB.right-unit , Eq.refl
  qc (swap• swap• swap• swap• swap• c , swap• swap• swap• ε) (swap ₛ) = PB.right-unit , Eq.refl
  qc (swap• swap• swap• swap• swap• ε , swap• swap• swap• swap• ε) (swap ₛ) = PB.right-unit , Eq.refl
  qc (swap• swap• swap• swap• swap• ε , swap• swap• swap• swap• swap• ε) (swap ₛ) = PB.right-unit , Eq.refl
  qc (swap• swap• swap• swap• swap• swap• c , swap• swap• swap• swap• ε) (swap ₛ) = PB.right-unit , Eq.refl
  qc (swap• swap• swap• swap• swap• swap• ε , swap• swap• swap• swap• swap• ε) (swap ₛ) = PB.right-unit , Eq.refl
  qc (swap• swap• swap• swap• swap• swap• ε , swap• swap• swap• swap• swap• swap• ε) (swap ₛ) = PB.right-unit , Eq.refl
  qc (swap• swap• swap• swap• swap• swap• swap• c , swap• swap• swap• swap• swap• ε) (swap ₛ) = PB.right-unit , Eq.refl
  qc (swap• swap• swap• swap• swap• swap• swap• ε , swap• swap• swap• swap• swap• swap• ε) (swap ₛ) = PB.right-unit , Eq.refl
  qc (swap• swap• swap• swap• swap• swap• swap• ε , swap• swap• swap• swap• swap• swap• swap• ε) (swap ₛ) = PB.right-unit , Eq.refl
  qc (swap• swap• swap• swap• swap• swap• swap• swap• c , swap• swap• swap• swap• swap• swap• ε) (swap ₛ) = PB.right-unit , Eq.refl
  qc (swap• swap• swap• swap• swap• swap• swap• swap• ε , swap• swap• swap• swap• swap• swap• swap• ε) (swap ₛ) = PB.right-unit , Eq.refl
  qc (swap• swap• swap• swap• swap• swap• swap• swap• ε , swap• swap• swap• swap• swap• swap• swap• swap• ε) (swap ₛ) = PB.right-unit , Eq.refl
  qc (swap• ε , swap• ε) ((swap ₛ) ₛ) = PB.left-unit , Eq.refl
  qc (swap• ε , swap• ε) (((x ₛ) ₛ) ₛ) = PB.right-unit , Eq.refl
  qc (swap• swap• ε , swap• ε) ((swap ₛ) ₛ) = PB.left-unit , Eq.refl
  qc (swap• swap• swap• c , swap• ε) ((swap ₛ) ₛ) = PB.right-unit , Eq.refl
  qc (swap• swap• ε , swap• ε) (((swap ₛ) ₛ) ₛ) = PB.left-unit , Eq.refl
  qc (swap• swap• ε , swap• ε) ((((x ₛ) ₛ) ₛ) ₛ) = PB.right-unit , Eq.refl
  qc (swap• swap• swap• ε , swap• ε) (((swap ₛ) ₛ) ₛ) = PB.left-unit , Eq.refl
  qc (swap• swap• swap• swap• c , swap• ε) (((swap ₛ) ₛ) ₛ) = PB.right-unit , Eq.refl
  qc (swap• swap• swap• ε , swap• ε) ((((swap ₛ) ₛ) ₛ) ₛ) = PB.left-unit , Eq.refl
  qc (swap• swap• swap• ε , swap• ε) (((((x ₛ) ₛ) ₛ) ₛ) ₛ) = PB.right-unit , Eq.refl
  qc (swap• swap• swap• swap• ε , swap• ε) ((((swap ₛ) ₛ) ₛ) ₛ) = PB.left-unit , Eq.refl
  qc (swap• swap• swap• swap• swap• c , swap• ε) ((((swap ₛ) ₛ) ₛ) ₛ) = PB.right-unit , Eq.refl
  qc (swap• swap• swap• swap• ε , swap• ε) (((((swap ₛ) ₛ) ₛ) ₛ) ₛ) = PB.left-unit , Eq.refl
  qc (swap• swap• swap• swap• ε , swap• ε) ((((((x ₛ) ₛ) ₛ) ₛ) ₛ) ₛ) = PB.right-unit , Eq.refl
  qc (swap• swap• swap• swap• swap• ε , swap• ε) (((((swap ₛ) ₛ) ₛ) ₛ) ₛ) = PB.left-unit , Eq.refl
  qc (swap• swap• swap• swap• swap• swap• c , swap• ε) (((((swap ₛ) ₛ) ₛ) ₛ) ₛ) = PB.right-unit , Eq.refl
  qc (swap• swap• swap• swap• swap• ε , swap• ε) ((((((swap ₛ) ₛ) ₛ) ₛ) ₛ) ₛ) = PB.left-unit , Eq.refl
  qc (swap• swap• swap• swap• swap• ε , swap• ε) (((((((x ₛ) ₛ) ₛ) ₛ) ₛ) ₛ) ₛ) = PB.right-unit , Eq.refl
  qc (swap• swap• swap• swap• swap• swap• ε , swap• ε) ((((((swap ₛ) ₛ) ₛ) ₛ) ₛ) ₛ) = PB.left-unit , Eq.refl
  qc (swap• swap• swap• swap• swap• swap• swap• c , swap• ε) ((((((swap ₛ) ₛ) ₛ) ₛ) ₛ) ₛ) = PB.right-unit , Eq.refl
  qc (swap• swap• swap• swap• swap• swap• ε , swap• ε) (((((((swap ₛ) ₛ) ₛ) ₛ) ₛ) ₛ) ₛ) = PB.left-unit , Eq.refl
  qc (swap• swap• swap• swap• swap• swap• swap• ε , swap• ε) (((((((swap ₛ) ₛ) ₛ) ₛ) ₛ) ₛ) ₛ) = PB.left-unit , Eq.refl
  qc (swap• swap• swap• swap• swap• swap• swap• swap• c , swap• ε) (((((((swap ₛ) ₛ) ₛ) ₛ) ₛ) ₛ) ₛ) = PB.right-unit , Eq.refl
  qc (swap• swap• swap• swap• swap• swap• ε , swap• ε) ((((((((swap ₛ) ₛ) ₛ) ₛ) ₛ) ₛ) ₛ) ₛ) = PB.right-unit , Eq.refl
  qc (swap• swap• swap• swap• swap• swap• swap• ε , swap• ε) ((((((((swap ₛ) ₛ) ₛ) ₛ) ₛ) ₛ) ₛ) ₛ) = PB.left-unit , Eq.refl
  qc (swap• swap• swap• swap• swap• swap• swap• swap• ε , swap• ε) ((((((((swap ₛ) ₛ) ₛ) ₛ) ₛ) ₛ) ₛ) ₛ) = PB.left-unit , Eq.refl
  qc (swap• swap• ε , swap• swap• ε) ((swap ₛ) ₛ) = PB.left-unit , Eq.refl
  qc (swap• swap• swap• ε , swap• swap• ε) ((swap ₛ) ₛ) = PB.left-unit , Eq.refl
  qc (swap• swap• swap• swap• c , swap• swap• ε) ((swap ₛ) ₛ) = PB.left-unit , Eq.refl
  qc (swap• swap• swap• ε , swap• swap• swap• ε) ((swap ₛ) ₛ) = PB.left-unit , Eq.refl
  qc (swap• swap• swap• swap• c , swap• swap• swap• ε) ((swap ₛ) ₛ) = PB.left-unit , Eq.refl
  qc (swap• swap• swap• swap• ε , swap• swap• swap• swap• ε) ((swap ₛ) ₛ) = PB.right-unit , Eq.refl
  qc (swap• swap• swap• swap• swap• c , swap• swap• swap• swap• ε) ((swap ₛ) ₛ) = PB.right-unit , Eq.refl
  qc (swap• swap• swap• swap• swap• ε , swap• swap• swap• swap• swap• ε) ((swap ₛ) ₛ) = PB.right-unit , Eq.refl
  qc (swap• swap• swap• swap• swap• swap• c , swap• swap• swap• swap• swap• ε) ((swap ₛ) ₛ) = PB.right-unit , Eq.refl
  qc (swap• swap• swap• swap• swap• swap• ε , swap• swap• swap• swap• swap• swap• ε) ((swap ₛ) ₛ) = PB.right-unit , Eq.refl
  qc (swap• swap• swap• swap• swap• swap• swap• c , swap• swap• swap• swap• swap• swap• ε) ((swap ₛ) ₛ) = PB.right-unit , Eq.refl
  qc (swap• swap• swap• swap• swap• swap• swap• ε , swap• swap• swap• swap• swap• swap• swap• ε) ((swap ₛ) ₛ) = PB.right-unit , Eq.refl
  qc (swap• swap• swap• swap• swap• swap• swap• swap• c , swap• swap• swap• swap• swap• swap• swap• ε) ((swap ₛ) ₛ) = PB.right-unit , Eq.refl
  qc (swap• swap• swap• swap• swap• swap• swap• swap• ε , swap• swap• swap• swap• swap• swap• swap• swap• ε) ((swap ₛ) ₛ) = PB.right-unit , Eq.refl
  qc (swap• swap• ε , swap• swap• ε) (((swap ₛ) ₛ) ₛ) = PB.left-unit , Eq.refl
  qc (swap• swap• ε , swap• swap• ε) ((((x ₛ) ₛ) ₛ) ₛ) = PB.right-unit , Eq.refl
  qc (swap• swap• swap• ε , swap• swap• ε) (((swap ₛ) ₛ) ₛ) = PB.left-unit , Eq.refl
  qc (swap• swap• swap• swap• c , swap• swap• ε) (((swap ₛ) ₛ) ₛ) = PB.right-unit , Eq.refl
  qc (swap• swap• swap• ε , swap• swap• ε) ((((swap ₛ) ₛ) ₛ) ₛ) = PB.left-unit , Eq.refl
  qc (swap• swap• swap• ε , swap• swap• ε) (((((x ₛ) ₛ) ₛ) ₛ) ₛ) = PB.right-unit , Eq.refl
  qc (swap• swap• swap• swap• ε , swap• swap• ε) ((((swap ₛ) ₛ) ₛ) ₛ) = PB.left-unit , Eq.refl
  qc (swap• swap• swap• swap• swap• c , swap• swap• ε) ((((swap ₛ) ₛ) ₛ) ₛ) = PB.right-unit , Eq.refl
  qc (swap• swap• swap• swap• ε , swap• swap• ε) (((((swap ₛ) ₛ) ₛ) ₛ) ₛ) = PB.left-unit , Eq.refl
  qc (swap• swap• swap• swap• ε , swap• swap• ε) ((((((x ₛ) ₛ) ₛ) ₛ) ₛ) ₛ) = PB.right-unit , Eq.refl
  qc (swap• swap• swap• swap• swap• ε , swap• swap• ε) (((((swap ₛ) ₛ) ₛ) ₛ) ₛ) = PB.left-unit , Eq.refl
  qc (swap• swap• swap• swap• swap• swap• c , swap• swap• ε) (((((swap ₛ) ₛ) ₛ) ₛ) ₛ) = PB.right-unit , Eq.refl
  qc (swap• swap• swap• swap• swap• ε , swap• swap• ε) ((((((swap ₛ) ₛ) ₛ) ₛ) ₛ) ₛ) = PB.left-unit , Eq.refl
  qc (swap• swap• swap• swap• swap• swap• ε , swap• swap• ε) ((((((swap ₛ) ₛ) ₛ) ₛ) ₛ) ₛ) = PB.left-unit , Eq.refl
  qc (swap• swap• swap• swap• swap• swap• swap• c , swap• swap• ε) ((((((swap ₛ) ₛ) ₛ) ₛ) ₛ) ₛ) = PB.right-unit , Eq.refl
  qc (swap• swap• swap• swap• swap• ε , swap• swap• ε) (((((((swap ₛ) ₛ) ₛ) ₛ) ₛ) ₛ) ₛ) = PB.right-unit , Eq.refl
  qc (swap• swap• swap• swap• swap• ε , swap• swap• ε) ((((((((x ₛ) ₛ) ₛ) ₛ) ₛ) ₛ) ₛ) ₛ) = PB.right-unit , Eq.refl
  qc (swap• swap• swap• swap• swap• swap• ε , swap• swap• ε) (((((((swap ₛ) ₛ) ₛ) ₛ) ₛ) ₛ) ₛ) = PB.left-unit , Eq.refl
  qc (swap• swap• swap• swap• swap• swap• swap• ε , swap• swap• ε) (((((((swap ₛ) ₛ) ₛ) ₛ) ₛ) ₛ) ₛ) = PB.left-unit , Eq.refl
  qc (swap• swap• swap• swap• swap• swap• swap• swap• c , swap• swap• ε) (((((((swap ₛ) ₛ) ₛ) ₛ) ₛ) ₛ) ₛ) = PB.right-unit , Eq.refl
  qc (swap• swap• swap• swap• swap• swap• ε , swap• swap• ε) ((((((((swap ₛ) ₛ) ₛ) ₛ) ₛ) ₛ) ₛ) ₛ) = PB.right-unit , Eq.refl
  qc (swap• swap• swap• swap• swap• swap• swap• ε , swap• swap• ε) ((((((((swap ₛ) ₛ) ₛ) ₛ) ₛ) ₛ) ₛ) ₛ) = PB.left-unit , Eq.refl
  qc (swap• swap• swap• swap• swap• swap• swap• swap• ε , swap• swap• ε) ((((((((swap ₛ) ₛ) ₛ) ₛ) ₛ) ₛ) ₛ) ₛ) = PB.left-unit , Eq.refl
  qc (swap• swap• swap• ε , swap• swap• swap• ε) (((swap ₛ) ₛ) ₛ) = PB.left-unit , Eq.refl
  qc (swap• swap• swap• swap• ε , swap• swap• swap• ε) (((swap ₛ) ₛ) ₛ) = PB.left-unit , Eq.refl
  qc (swap• swap• swap• swap• swap• c , swap• swap• swap• ε) (((swap ₛ) ₛ) ₛ) = PB.left-unit , Eq.refl
  qc (swap• swap• swap• swap• ε , swap• swap• swap• swap• ε) (((swap ₛ) ₛ) ₛ) = PB.left-unit , Eq.refl
  qc (swap• swap• swap• swap• swap• ε , swap• swap• swap• swap• ε) (((swap ₛ) ₛ) ₛ) = PB.left-unit , Eq.refl
  qc (swap• swap• swap• swap• swap• ε , swap• swap• swap• swap• swap• ε) (((swap ₛ) ₛ) ₛ) = PB.right-unit , Eq.refl
  qc (swap• swap• swap• swap• swap• swap• c , swap• swap• swap• swap• ε) (((swap ₛ) ₛ) ₛ) = PB.left-unit , Eq.refl
  qc (swap• swap• swap• swap• swap• swap• ε , swap• swap• swap• swap• swap• ε) (((swap ₛ) ₛ) ₛ) = PB.right-unit , Eq.refl
  qc (swap• swap• swap• swap• swap• swap• ε , swap• swap• swap• swap• swap• swap• ε) (((swap ₛ) ₛ) ₛ) = PB.right-unit , Eq.refl
  qc (swap• swap• swap• swap• swap• swap• swap• c , swap• swap• swap• swap• swap• ε) (((swap ₛ) ₛ) ₛ) = PB.right-unit , Eq.refl
  qc (swap• swap• swap• swap• swap• swap• swap• c , swap• swap• swap• swap• swap• swap• ε) (((swap ₛ) ₛ) ₛ) = PB.right-unit , Eq.refl
  qc (swap• swap• swap• swap• swap• swap• swap• ε , swap• swap• swap• swap• swap• swap• swap• ε) (((swap ₛ) ₛ) ₛ) = PB.right-unit , Eq.refl
  qc (swap• swap• swap• swap• swap• swap• swap• swap• c , swap• swap• swap• swap• swap• swap• swap• ε) (((swap ₛ) ₛ) ₛ) = PB.right-unit , Eq.refl
  qc (swap• swap• swap• swap• swap• swap• swap• swap• ε , swap• swap• swap• swap• swap• swap• swap• swap• ε) (((swap ₛ) ₛ) ₛ) = PB.right-unit , Eq.refl
  qc (swap• swap• swap• ε , swap• swap• swap• ε) ((((swap ₛ) ₛ) ₛ) ₛ) = PB.left-unit , Eq.refl
  qc (swap• swap• swap• ε , swap• swap• swap• ε) (((((x ₛ) ₛ) ₛ) ₛ) ₛ) = PB.right-unit , Eq.refl
  qc (swap• swap• swap• swap• ε , swap• swap• swap• ε) ((((swap ₛ) ₛ) ₛ) ₛ) = PB.left-unit , Eq.refl
  qc (swap• swap• swap• swap• swap• c , swap• swap• swap• ε) ((((swap ₛ) ₛ) ₛ) ₛ) = PB.right-unit , Eq.refl
  qc (swap• swap• swap• swap• ε , swap• swap• swap• ε) (((((swap ₛ) ₛ) ₛ) ₛ) ₛ) = PB.left-unit , Eq.refl
  qc (swap• swap• swap• swap• ε , swap• swap• swap• ε) ((((((swap ₛ) ₛ) ₛ) ₛ) ₛ) ₛ) = PB.right-unit , Eq.refl
  qc (swap• swap• swap• swap• ε , swap• swap• swap• ε) (((((((x ₛ) ₛ) ₛ) ₛ) ₛ) ₛ) ₛ) = PB.right-unit , Eq.refl
  qc (swap• swap• swap• swap• swap• ε , swap• swap• swap• ε) (((((swap ₛ) ₛ) ₛ) ₛ) ₛ) = PB.left-unit , Eq.refl
  qc (swap• swap• swap• swap• swap• swap• c , swap• swap• swap• ε) (((((swap ₛ) ₛ) ₛ) ₛ) ₛ) = PB.right-unit , Eq.refl
  qc (swap• swap• swap• swap• swap• ε , swap• swap• swap• ε) ((((((swap ₛ) ₛ) ₛ) ₛ) ₛ) ₛ) = PB.left-unit , Eq.refl
  qc (swap• swap• swap• swap• swap• ε , swap• swap• swap• ε) (((((((x ₛ) ₛ) ₛ) ₛ) ₛ) ₛ) ₛ) = PB.right-unit , Eq.refl
  qc (swap• swap• swap• swap• swap• swap• ε , swap• swap• swap• ε) ((((((swap ₛ) ₛ) ₛ) ₛ) ₛ) ₛ) = PB.left-unit , Eq.refl
  qc (swap• swap• swap• swap• swap• swap• ε , swap• swap• swap• ε) (((((((swap ₛ) ₛ) ₛ) ₛ) ₛ) ₛ) ₛ) = PB.left-unit , Eq.refl
  qc (swap• swap• swap• swap• swap• swap• ε , swap• swap• swap• ε) ((((((((x ₛ) ₛ) ₛ) ₛ) ₛ) ₛ) ₛ) ₛ) = PB.right-unit , Eq.refl
  qc (swap• swap• swap• swap• swap• swap• swap• c , swap• swap• swap• ε) ((((((swap ₛ) ₛ) ₛ) ₛ) ₛ) ₛ) = PB.right-unit , Eq.refl
  qc (swap• swap• swap• swap• swap• swap• swap• ε , swap• swap• swap• ε) (((((((swap ₛ) ₛ) ₛ) ₛ) ₛ) ₛ) ₛ) = PB.left-unit , Eq.refl
  qc (swap• swap• swap• swap• swap• swap• swap• ε , swap• swap• swap• ε) ((((((((swap ₛ) ₛ) ₛ) ₛ) ₛ) ₛ) ₛ) ₛ) = PB.left-unit , Eq.refl
  qc (swap• swap• swap• swap• swap• swap• swap• swap• c , swap• swap• swap• ε) (((((((swap ₛ) ₛ) ₛ) ₛ) ₛ) ₛ) ₛ) = PB.right-unit , Eq.refl
  qc (swap• swap• swap• swap• swap• swap• swap• swap• ε , swap• swap• swap• ε) ((((((((swap ₛ) ₛ) ₛ) ₛ) ₛ) ₛ) ₛ) ₛ) = PB.left-unit , Eq.refl
  qc (swap• swap• swap• swap• ε , swap• swap• swap• swap• ε) ((((swap ₛ) ₛ) ₛ) ₛ) = PB.left-unit , Eq.refl

  qc (swap• swap• swap• swap• swap• ε , swap• swap• swap• swap• ε) ((((swap ₛ) ₛ) ₛ) ₛ) = PB.left-unit , Eq.refl
  qc (swap• swap• swap• swap• swap• swap• ε , swap• swap• swap• swap• ε) ((((swap ₛ) ₛ) ₛ) ₛ) = PB.left-unit , Eq.refl
  qc (swap• swap• swap• swap• swap• swap• swap• c , swap• swap• swap• swap• ε) ((((swap ₛ) ₛ) ₛ) ₛ) = PB.left-unit , Eq.refl
  qc (swap• swap• swap• swap• swap• ε , swap• swap• swap• swap• swap• ε) ((((swap ₛ) ₛ) ₛ) ₛ) = PB.left-unit , Eq.refl
  qc (swap• swap• swap• swap• swap• swap• c , swap• swap• swap• swap• swap• ε) ((((swap ₛ) ₛ) ₛ) ₛ) = PB.left-unit , Eq.refl
  qc (swap• swap• swap• swap• swap• swap• ε , swap• swap• swap• swap• swap• swap• ε) ((((swap ₛ) ₛ) ₛ) ₛ) = PB.right-unit , Eq.refl
  qc (swap• swap• swap• swap• swap• swap• swap• c , swap• swap• swap• swap• swap• swap• ε) ((((swap ₛ) ₛ) ₛ) ₛ) = PB.right-unit , Eq.refl
  qc (swap• swap• swap• swap• swap• swap• swap• ε , swap• swap• swap• swap• swap• swap• swap• ε) ((((swap ₛ) ₛ) ₛ) ₛ) = PB.right-unit , Eq.refl
  qc (swap• swap• swap• swap• swap• swap• swap• swap• c , swap• swap• swap• swap• swap• swap• swap• ε) ((((swap ₛ) ₛ) ₛ) ₛ) = PB.right-unit , Eq.refl
  qc (swap• swap• swap• swap• swap• swap• swap• swap• ε , swap• swap• swap• swap• swap• swap• swap• swap• ε) ((((swap ₛ) ₛ) ₛ) ₛ) = PB.right-unit , Eq.refl
  qc (swap• swap• swap• swap• ε , swap• swap• swap• swap• ε) (((((swap ₛ) ₛ) ₛ) ₛ) ₛ) = PB.left-unit , Eq.refl
  qc (swap• swap• swap• swap• ε , swap• swap• swap• swap• ε) ((((((x ₛ) ₛ) ₛ) ₛ) ₛ) ₛ) = PB.right-unit , Eq.refl
  qc (swap• swap• swap• swap• swap• ε , swap• swap• swap• swap• ε) (((((swap ₛ) ₛ) ₛ) ₛ) ₛ) = PB.left-unit , Eq.refl
  qc (swap• swap• swap• swap• swap• swap• c , swap• swap• swap• swap• ε) (((((swap ₛ) ₛ) ₛ) ₛ) ₛ) = PB.right-unit , Eq.refl
  qc (swap• swap• swap• swap• swap• ε , swap• swap• swap• swap• ε) ((((((swap ₛ) ₛ) ₛ) ₛ) ₛ) ₛ) = PB.left-unit , Eq.refl
  qc (swap• swap• swap• swap• swap• ε , swap• swap• swap• swap• ε) (((((((x ₛ) ₛ) ₛ) ₛ) ₛ) ₛ) ₛ) = PB.right-unit , Eq.refl
  qc (swap• swap• swap• swap• swap• swap• ε , swap• swap• swap• swap• ε) ((((((swap ₛ) ₛ) ₛ) ₛ) ₛ) ₛ) = PB.left-unit , Eq.refl
  qc (swap• swap• swap• swap• swap• swap• swap• c , swap• swap• swap• swap• ε) ((((((swap ₛ) ₛ) ₛ) ₛ) ₛ) ₛ) = PB.right-unit , Eq.refl
  qc (swap• swap• swap• swap• swap• swap• ε , swap• swap• swap• swap• ε) (((((((swap ₛ) ₛ) ₛ) ₛ) ₛ) ₛ) ₛ) = PB.left-unit , Eq.refl
  qc (swap• swap• swap• swap• swap• swap• ε , swap• swap• swap• swap• ε) ((((((((x ₛ) ₛ) ₛ) ₛ) ₛ) ₛ) ₛ) ₛ) = PB.right-unit , Eq.refl
  qc (swap• swap• swap• swap• swap• swap• swap• ε , swap• swap• swap• swap• ε) (((((((swap ₛ) ₛ) ₛ) ₛ) ₛ) ₛ) ₛ) = PB.left-unit , Eq.refl
  qc (swap• swap• swap• swap• swap• swap• swap• ε , swap• swap• swap• swap• ε) ((((((((swap ₛ) ₛ) ₛ) ₛ) ₛ) ₛ) ₛ) ₛ) = PB.left-unit , Eq.refl
  qc (swap• swap• swap• swap• swap• swap• swap• swap• c , swap• swap• swap• swap• ε) (((((((swap ₛ) ₛ) ₛ) ₛ) ₛ) ₛ) ₛ) = PB.right-unit , Eq.refl
  qc (swap• swap• swap• swap• swap• swap• swap• swap• ε , swap• swap• swap• swap• ε) ((((((((swap ₛ) ₛ) ₛ) ₛ) ₛ) ₛ) ₛ) ₛ) = PB.left-unit , Eq.refl
  qc (swap• swap• swap• swap• swap• ε , swap• swap• swap• swap• swap• ε) (((((swap ₛ) ₛ) ₛ) ₛ) ₛ) = PB.left-unit , Eq.refl
  qc (swap• swap• swap• swap• swap• swap• ε , swap• swap• swap• swap• swap• ε) (((((swap ₛ) ₛ) ₛ) ₛ) ₛ) = PB.left-unit , Eq.refl
  qc (swap• swap• swap• swap• swap• swap• swap• c , swap• swap• swap• swap• swap• ε) (((((swap ₛ) ₛ) ₛ) ₛ) ₛ) = PB.left-unit , Eq.refl
  qc (swap• swap• swap• swap• swap• swap• ε , swap• swap• swap• swap• swap• swap• ε) (((((swap ₛ) ₛ) ₛ) ₛ) ₛ) = PB.left-unit , Eq.refl
  qc (swap• swap• swap• swap• swap• swap• swap• ε , swap• swap• swap• swap• swap• swap• ε) (((((swap ₛ) ₛ) ₛ) ₛ) ₛ) = PB.left-unit , Eq.refl
  qc (swap• swap• swap• swap• swap• swap• swap• ε , swap• swap• swap• swap• swap• swap• swap• ε) (((((swap ₛ) ₛ) ₛ) ₛ) ₛ) = PB.right-unit , Eq.refl
  qc (swap• swap• swap• swap• swap• swap• swap• swap• c , swap• swap• swap• swap• swap• swap• ε) (((((swap ₛ) ₛ) ₛ) ₛ) ₛ) = PB.left-unit , Eq.refl
  qc (swap• swap• swap• swap• swap• swap• swap• swap• ε , swap• swap• swap• swap• swap• swap• swap• ε) (((((swap ₛ) ₛ) ₛ) ₛ) ₛ) = PB.right-unit , Eq.refl
  qc (swap• swap• swap• swap• swap• swap• swap• swap• ε , swap• swap• swap• swap• swap• swap• swap• swap• ε) (((((swap ₛ) ₛ) ₛ) ₛ) ₛ) = PB.right-unit , Eq.refl
  qc (swap• swap• swap• swap• swap• ε , swap• swap• swap• swap• swap• ε) ((((((swap ₛ) ₛ) ₛ) ₛ) ₛ) ₛ) = PB.left-unit , Eq.refl
  qc (swap• swap• swap• swap• swap• ε , swap• swap• swap• swap• swap• ε) (((((((x ₛ) ₛ) ₛ) ₛ) ₛ) ₛ) ₛ) = PB.right-unit , Eq.refl
  qc (swap• swap• swap• swap• swap• swap• ε , swap• swap• swap• swap• swap• ε) ((((((swap ₛ) ₛ) ₛ) ₛ) ₛ) ₛ) = PB.left-unit , Eq.refl
  qc (swap• swap• swap• swap• swap• swap• swap• c , swap• swap• swap• swap• swap• ε) ((((((swap ₛ) ₛ) ₛ) ₛ) ₛ) ₛ) = PB.right-unit , Eq.refl
  qc (swap• swap• swap• swap• swap• swap• ε , swap• swap• swap• swap• swap• ε) (((((((swap ₛ) ₛ) ₛ) ₛ) ₛ) ₛ) ₛ) = PB.left-unit , Eq.refl
  qc (swap• swap• swap• swap• swap• swap• ε , swap• swap• swap• swap• swap• ε) ((((((((x ₛ) ₛ) ₛ) ₛ) ₛ) ₛ) ₛ) ₛ) = PB.right-unit , Eq.refl
  qc (swap• swap• swap• swap• swap• swap• swap• ε , swap• swap• swap• swap• swap• ε) (((((((swap ₛ) ₛ) ₛ) ₛ) ₛ) ₛ) ₛ) = PB.left-unit , Eq.refl
  qc (swap• swap• swap• swap• swap• swap• swap• swap• c , swap• swap• swap• swap• swap• ε) (((((((swap ₛ) ₛ) ₛ) ₛ) ₛ) ₛ) ₛ) = PB.right-unit , Eq.refl
  qc (swap• swap• swap• swap• swap• swap• swap• ε , swap• swap• swap• swap• swap• ε) ((((((((swap ₛ) ₛ) ₛ) ₛ) ₛ) ₛ) ₛ) ₛ) = PB.left-unit , Eq.refl
  qc (swap• swap• swap• swap• swap• swap• swap• swap• ε , swap• swap• swap• swap• swap• ε) ((((((((swap ₛ) ₛ) ₛ) ₛ) ₛ) ₛ) ₛ) ₛ) = PB.left-unit , Eq.refl
  qc (swap• swap• swap• swap• swap• swap• ε , swap• swap• swap• swap• swap• swap• ε) ((((((swap ₛ) ₛ) ₛ) ₛ) ₛ) ₛ) = PB.left-unit , Eq.refl
  qc (swap• swap• swap• swap• swap• swap• swap• ε , swap• swap• swap• swap• swap• swap• ε) ((((((swap ₛ) ₛ) ₛ) ₛ) ₛ) ₛ) = PB.left-unit , Eq.refl
  qc (swap• swap• swap• swap• swap• swap• swap• swap• c , swap• swap• swap• swap• swap• swap• ε) ((((((swap ₛ) ₛ) ₛ) ₛ) ₛ) ₛ) = PB.left-unit , Eq.refl
  qc (swap• swap• swap• swap• swap• swap• swap• ε , swap• swap• swap• swap• swap• swap• swap• ε) ((((((swap ₛ) ₛ) ₛ) ₛ) ₛ) ₛ) = PB.left-unit , Eq.refl
  qc (swap• swap• swap• swap• swap• swap• swap• swap• ε , swap• swap• swap• swap• swap• swap• swap• ε) ((((((swap ₛ) ₛ) ₛ) ₛ) ₛ) ₛ) = PB.left-unit , Eq.refl
  qc (swap• swap• swap• swap• swap• swap• swap• swap• ε , swap• swap• swap• swap• swap• swap• swap• swap• ε) ((((((swap ₛ) ₛ) ₛ) ₛ) ₛ) ₛ) = PB.right-unit , Eq.refl
  qc (swap• swap• swap• swap• swap• swap• ε , swap• swap• swap• swap• swap• swap• ε) (((((((swap ₛ) ₛ) ₛ) ₛ) ₛ) ₛ) ₛ) = PB.left-unit , Eq.refl
  qc (swap• swap• swap• swap• swap• swap• ε , swap• swap• swap• swap• swap• swap• ε) ((((((((x ₛ) ₛ) ₛ) ₛ) ₛ) ₛ) ₛ) ₛ) = PB.right-unit , Eq.refl
  qc (swap• swap• swap• swap• swap• swap• swap• ε , swap• swap• swap• swap• swap• swap• ε) (((((((swap ₛ) ₛ) ₛ) ₛ) ₛ) ₛ) ₛ) = PB.left-unit , Eq.refl
  qc (swap• swap• swap• swap• swap• swap• swap• swap• c , swap• swap• swap• swap• swap• swap• ε) (((((((swap ₛ) ₛ) ₛ) ₛ) ₛ) ₛ) ₛ) = PB.right-unit , Eq.refl
  qc (swap• swap• swap• swap• swap• swap• swap• ε , swap• swap• swap• swap• swap• swap• ε) ((((((((swap ₛ) ₛ) ₛ) ₛ) ₛ) ₛ) ₛ) ₛ) = PB.left-unit , Eq.refl
  qc (swap• swap• swap• swap• swap• swap• swap• swap• ε , swap• swap• swap• swap• swap• swap• ε) ((((((((swap ₛ) ₛ) ₛ) ₛ) ₛ) ₛ) ₛ) ₛ) = PB.left-unit , Eq.refl
  qc (swap• swap• swap• swap• swap• swap• swap• ε , swap• swap• swap• swap• swap• swap• swap• ε) (((((((swap ₛ) ₛ) ₛ) ₛ) ₛ) ₛ) ₛ) = PB.left-unit , Eq.refl
  qc (swap• swap• swap• swap• swap• swap• swap• swap• ε , swap• swap• swap• swap• swap• swap• swap• ε) (((((((swap ₛ) ₛ) ₛ) ₛ) ₛ) ₛ) ₛ) = PB.left-unit , Eq.refl
  qc (swap• swap• swap• swap• swap• swap• swap• swap• ε , swap• swap• swap• swap• swap• swap• swap• swap• ε) (((((((swap ₛ) ₛ) ₛ) ₛ) ₛ) ₛ) ₛ) = PB.left-unit , Eq.refl
  qc (swap• swap• swap• swap• swap• swap• swap• ε , swap• swap• swap• swap• swap• swap• swap• ε) ((((((((swap ₛ) ₛ) ₛ) ₛ) ₛ) ₛ) ₛ) ₛ) = PB.left-unit , Eq.refl
  qc (swap• swap• swap• swap• swap• swap• swap• swap• ε , swap• swap• swap• swap• swap• swap• swap• ε) ((((((((swap ₛ) ₛ) ₛ) ₛ) ₛ) ₛ) ₛ) ₛ) = PB.left-unit , Eq.refl
  qc (swap• swap• swap• swap• swap• swap• swap• swap• ε , swap• swap• swap• swap• swap• swap• swap• swap• ε) ((((((((swap ₛ) ₛ) ₛ) ₛ) ₛ) ₛ) ₛ) ₛ) = PB.left-unit , Eq.refl

-}




{-
  aux-3 : ∀ {n} (c : C n) -> (d : df c) -> ract'' (swap• swap• swap• c , swap• swap• swap• d) swap ≡ ([ [ swap ]ʷ ]ᵣ , (swap• swap• swap• c , swap• swap• swap• d))
  aux-3 {n} ε ε = {!!}
  aux-3 {n} (swap• c) ε = {!!}
  aux-3 {n} (swap• c) (swap• d) with aux-3 c d
  aux-3 {.(suc _)} (swap• c) (swap• d) | ih = {!!} --Eq.cong (λ { (fst , fst₁ , snd) → {!!} , ({!swap• fst₁!} , {!!}) }) ih
-}



  -- ract3 {n} (swap• ε , ε) (swap ₛ) = ε , (ε , ε)
  -- ract3 {n} (swap• ε , ε) (((x ₛ) ₛ) ₛ) = [ [ x ₛ ]ʷ ]ᵣ , (swap• ε , ε)

  -- ract3 {n} (swap• swap• c , ε) ((x ₛ) ₛ) with ract3 (swap• c , ε) (x ₛ)
  -- ... | (w , (c' , d')) = fm w , swap• c' , ε
  



--  ract3 {n} (swap• ε , swap• ε) (swap ₛ) = [ [ swap ]ʷ ]ₗ , (swap• ε , swap• ε)
--  ract3 {n} (swap• swap• c , swap• ε) (swap ₛ) = ε , (swap• swap• c , swap• swap• ε)
--  ract3 {n} (swap• swap• ε , swap• swap• ε) (swap ₛ) = ε , (swap• swap• ε , swap• ε)
--  ract3 {n} (swap• swap• swap• c , swap• swap• ε) (swap ₛ) = ε , (swap• swap• swap• c , swap• ε)
--  ract3 {n} (swap• swap• swap• c , swap• swap• swap• d) (swap ₛ) = [ [ swap ₛ ]ʷ ]ᵣ , (swap• swap• swap• c , swap• swap• swap• d)
  
--  ract3 {n} (swap• ε , swap• ε) ((swap ₛ) ₛ) = ε , (swap• swap• ε , swap• ε)
  -- ract3 {n} (swap• swap• c , swap• d) ((x ₛ) ₛ) = let (w , c' , d') = ract3 (swap• c , d) (x ₛ)
  --   in fm w , ((swap• c') , (swap• d'))
  
  
  -- ract3 {n} (swap• swap• c , swap• d) ((x ₛ) ₛ) with ract3 (swap• c , d) (x ₛ)
  -- ... | (w , (c' , d')) = (fm w) , ((swap• c') , (swap• d'))

--  ract3 {n} (swap• swap• c , swap• d) ((x ₛ) ₛ) = ε , ε , ε

--  ract3 {n} (swap• ε , swap• ε) (((x ₛ) ₛ) ₛ) = [ [ x ₛ ]ʷ ]ᵣ , (swap• ε , swap• ε)


{-
    ler7b : ∀ {n} ((c , d) : CC (suc n)) w ->
      let (w' , cd') = racts3 (swap• c , swap• ε) [ [ [ w ⇑] ⇑] ⇑] in
      let (w1 , cd1) = racts3 (swap• c , ε) [ [ [ w ⇑] ⇑] ⇑] in

    ler7b {n} (ε , ε) [ x ]ʷ = Eq.refl
    ler7b {n} (ε , ε) ε = Eq.refl
    ler7b {n} (ε , ε) (w • w₁) = {!!}
    ler7b {n} (swap• c , ε) [ x ]ʷ = Eq.refl
    ler7b {n} (swap• c , ε) ε = Eq.refl
    ler7b {n} (swap• c , ε) (w • w₁) = {!!}
    ler7b {n} (swap• c , swap• d) [ x ]ʷ = Eq.refl
    ler7b {n} (swap• c , swap• d) ε = Eq.refl
    ler7b {n} (swap• c , swap• d) (w • w₁) = {!!}
-}





{-  
  lemma-rss : ∀ {n} (d : C (suc n)) g -> racts d [ g ]ʷ ≡ ract d g
  lemma-rss {n} d g = Eq.refl

  lemma-rss2 : ∀ {n} (d : C (suc n)) -> racts d ε ≡ (ε , d)
  lemma-rss2 {n} d = Eq.refl

  lemma-aa : ∀ {n} ((c , d) : (CC n)) -> aux2' c (inject₁ (inject d)) ≡ (false , c , d)
  lemma-aa {zero} (ε , ε) = Eq.refl
  lemma-aa {suc n} (ε , ε) = Eq.refl
  lemma-aa {suc n} (swap• c , ε) = Eq.refl
  lemma-aa {suc n} (swap• c , swap• d) with aux2' (swap• c) (inject₁ (inject (swap• d))) | aux2' c (inject₁ (inject d)) | lemma-aa (c , d)
  ... | (b1 , c1 , d1) | (b2 , c2 , d2) | ih rewrite (Eq.cong proj₁ ih) = ≡×≡⇒≡ (Eq.refl , Eq.cong (λ { (fst , snd) → swap• fst , swap• snd}) (Eq.cong proj₂ ih))


  mutual 
    lemma-hom : ∀ {n} -> (c : CC (suc n)) -> (w v : Word (X (suc (suc n)))) ->
      let open PB (pres n) renaming (Alphabet to Sn) using () in
      let A = S2 ⊎ Sn in
      let (w' , c') = racts2 c w in
      let (v' , c'') = racts2 c' v in
      let open PB (pres 1 ⊕ pres n) renaming ( _≈_ to _≈₁_ ; _===_ to _===₁_) using () in
      let _~_ = PW.Pointwise _≈₁_ (_≡_ {A = CC (suc n)}) in
      racts2 c (w • v) ~ (w' • v' , c'')
    lemma-hom {n} (c , d) w v with racts (inject₁ (inject d)) w
    ... | (w1 , d1) with racts d1 v | racts c w1
    ... | (v1 , dv1) | (cw1 , c1) with aux2' c1 d1 | racts c1 v1
    ... | (b2 , c2 , d2) | (wv2 , cwv2) with racts (inject₁ (inject d2)) v
    ... | (iv , id2) with racts c2 iv
    ... | (iv2 , ic3) = {!!} , {!!}

    lemma-ss : ∀ {n} -> (c : CC (suc n)) -> (w : Word (X (suc (suc n)))) ->
      let open PB (pres n) renaming (Alphabet to Sn) using () in
      let A = S2 ⊎ Sn in
      let open PB (pres 1 ⊕ pres n) renaming ( _≈_ to _≈₁_ ; _===_ to _===₁_) using () in
      let _~_ = PW.Pointwise _≈₁_ (_≡_ {A = CC (suc n)}) in
      racts'' c w ~ racts2 c w
    lemma-ss {n} (c , d) [ x ]ʷ = PB.refl , Eq.refl
    lemma-ss {n} (c , d) ε rewrite lemma-aa (c , d) = PB.sym PB.left-unit , Eq.refl
    lemma-ss {n} c@(dl , dr) (w • v) with racts'' c w
    ... | (w1 , c1) with racts'' c1 v
    ... | (v2 , c2) with racts (inject₁ (inject dr)) w
    ... | (w3 , d3) with racts d3 v
    ... | (v4 , d4) with racts dl (w3 • v4)
    ... | (wv5 , c5) with aux2' c5 d4
    ... | (b6 , c6 , d6)= begin
      (w1 • v2 , c2) ≈⟨ {!!} ⟩
      racts'' c (w • v) ≈⟨ {!!} ⟩
      racts2 c (w • v)  ≈⟨ {!!} ⟩
      {![ wv5 ]ᵣ • [ eval-bool₁ b6 ]ₗ , ?!} ∎
      where
        open PP (pres 1 ⊕ pres n) using (word-setoid)
        ts = ×-setoid word-setoid (setoid (CC (suc n)))
        open SR ts
        
-}

