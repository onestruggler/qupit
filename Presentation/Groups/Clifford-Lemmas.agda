-- This module implements 'rewrite-clifford', a complete decision
-- procedure for equality of 2-qubit Clifford operators.
--
-- This is done in a bootstrapping way: we first prove a small number
-- of lemmas, then use these to define a rewrite relation, then use
-- the rewrite relation to prove more lemmas, then define a more
-- powerful rewrite relation, and so on.

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
open import Data.Nat hiding (_^_)
open import Agda.Builtin.Nat using (_-_)
import Data.Nat as Nat
open import Data.Bool
open import Data.List hiding ([_])

open import Data.Maybe
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


module Presentation.Groups.Clifford-Lemmas where

pattern auto = Eq.refl

-- ----------------------------------------------------------------------
-- * Clifford equations

module Clifford where

  -- We consider the Clifford subset of the equational theory. This
  -- has the advantage that we can dualize any proof (i.e., exchange
  -- the roles of the 1st and 2nd qubits) without having to worry
  -- about non-Clifford relations (such as rel-A, rel-B, and rel-C,
  -- the duals of which will be proved much later).

  data Gen : Set where
    H0-gen : Gen
    S0-gen : Gen
    H1-gen : Gen
    S1-gen : Gen
    CZ-gen : Gen

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

  S0⁻¹ : Word Gen
  S0⁻¹ = S0 ^ 3

  S1⁻¹ : Word Gen
  S1⁻¹ = S1 ^ 3

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

  Ex : Word Gen
  Ex = CX • XC • CX

  Ex' : Word Gen
  Ex' = XC • CX • XC

  -- The Clifford relations. For convenience, we still take all of the
  -- Clifford+T generators, but we consider only Clifford relations.
  -- In other words, the T-generators will be considered as abstract,
  -- satisfying no relations (except commutativity with scalars).
  infix 4 _===_
  data _===_ : WRel Gen where
    order-S0 : S0 ^ 4 === ε
    order-H0 : H0 ^ 2 === ε
    order-S0H0 : (S0 • H0) ^ 3 === ε
    order-S1 : S1 ^ 4 === ε
    order-H1 : H1 ^ 2 === ε
    order-S1H1 : (S1 • H1) ^ 3 === ε
    order-CZ : CZ ^ 2 === ε
    
    comm-H0H1 : H0 • H1 === H1 • H0
    comm-H0S1 : H0 • S1 === S1 • H0
    comm-S0H1 : S0 • H1 === H1 • S0
    comm-S0S1 : S0 • S1 === S1 • S0

    comm-S0-CZ : S0 • CZ === CZ • S0
    comm-S1-CZ : S1 • CZ === CZ • S1
    rel-X0-CZ : X0 • CZ === CZ • Z1 • X0
    rel-X1-CZ : X1 • CZ === CZ • Z0 • X1
    rel-CZ-H0-CZ : CZ • H0 • CZ === S0 • H0 • CZ • S0 • H0 • S0 • S1
    rel-CZ-H1-CZ : CZ • H1 • CZ === S1 • H1 • CZ • S1 • H1 • S1 • S0


-- ----------------------------------------------------------------------
-- * Data required for applying word tactics to Clifford generators

module CommData where

  open Clifford
  open PB _===_
  
  -- Commutativity.
  comm~ : (x y : Gen) -> Maybe (([ x ]ʷ • [ y ]ʷ) ≈ ([ y ]ʷ • [ x ]ʷ))
  comm~ H0-gen H1-gen = just (axiom comm-H0H1)
  comm~ H0-gen S1-gen = just (axiom comm-H0S1)
  comm~ S0-gen H1-gen = just (axiom comm-S0H1)
  comm~ S0-gen S1-gen = just (axiom comm-S0S1)

  comm~ H1-gen H0-gen = just (sym (axiom comm-H0H1))
  comm~ H1-gen S0-gen = just (sym (axiom comm-S0H1))
  comm~ S1-gen H0-gen = just (sym (axiom comm-H0S1))
  comm~ S1-gen S0-gen = just (sym (axiom comm-S0S1))

  comm~ S0-gen CZ-gen = just (axiom comm-S0-CZ)
  comm~ S1-gen CZ-gen = just (axiom comm-S1-CZ)
  comm~ CZ-gen S0-gen = just (sym (axiom comm-S0-CZ))
  comm~ CZ-gen S1-gen = just (sym (axiom comm-S1-CZ))
  comm~ _ _ = nothing


  -- We number the generators for the purpose of ordering them.
  ord : Gen -> ℕ
  ord S0-gen = 0
  ord S1-gen = 1
  ord H0-gen = 2
  ord H1-gen = 3
  ord CZ-gen = 4

  -- Ordering of generators.
  les : Gen -> Gen -> Bool
  les x y with ord x Nat.<? ord y
  les x y | yes _ = true
  les x y | no _ = false

open import Presentation.Tactics hiding ([_])
module Commuting-Clifford = Commuting Clifford._===_ CommData.comm~ CommData.les

-- ----------------------------------------------------------------------
-- * Duality

module Clifford-Duality where

  -- Here, we provide a proof principle for duality (an equation is
  -- provable iff its dual is provable).

  open Clifford
  open PB Clifford._===_
  gen : Gen -> Word Gen
  gen = [_]ʷ
  
  -- Each generator has a dual, obtained by swapping the two qubits.
  dual-gen : Gen -> Gen
  dual-gen H0-gen = H1-gen
  dual-gen H1-gen = H0-gen
  dual-gen S0-gen = S1-gen
  dual-gen S1-gen = S0-gen
  dual-gen CZ-gen = CZ-gen

  -- Compute the dual of a word.
  dual : Word Gen -> Word Gen
  dual ([ x ]ʷ) = gen (dual-gen x)
  dual ε = ε
  dual (w • u) = dual w • dual u

  -- Lemma: duality is an involution.
  lemma-double-dual : ∀ w -> w ≡ dual (dual w)
  lemma-double-dual ([ H0-gen ]ʷ) = Eq.refl
  lemma-double-dual ([ H1-gen ]ʷ) = Eq.refl
  lemma-double-dual ([ S0-gen ]ʷ) = Eq.refl
  lemma-double-dual ([ S1-gen ]ʷ) = Eq.refl
  lemma-double-dual ([ CZ-gen ]ʷ) = Eq.refl
  lemma-double-dual ε = Eq.refl
  lemma-double-dual (w • v) = Eq.cong₂ _•_ (lemma-double-dual w) (lemma-double-dual v)

  -- Dualize a proof. Duality is useful early on. However, we will not
  -- prove the duals of axioms rel-A, rel-B, and rel-C until much
  -- later. Therefore, we work only with Clifford relations for the
  -- time being.
  lemma-dual : ∀ {w u} -> w ≈ u -> dual w ≈ dual u
  lemma-dual (axiom comm-H0H1) = axiom comm-H0H1 reversed
  lemma-dual (axiom comm-H0S1) = axiom comm-S0H1 reversed
  lemma-dual (axiom comm-S0H1) = axiom comm-H0S1 reversed
  lemma-dual (axiom comm-S0S1) = axiom comm-S0S1 reversed
  lemma-dual (axiom order-H0) = axiom order-H1
  lemma-dual (axiom order-H1) = axiom order-H0
  lemma-dual (axiom order-S0) = axiom order-S1
  lemma-dual (axiom order-S1) = axiom order-S0
  lemma-dual (axiom order-S0H0) = axiom order-S1H1
  lemma-dual (axiom order-S1H1) = axiom order-S0H0
  lemma-dual (axiom order-CZ) = axiom order-CZ
  lemma-dual (axiom comm-S0-CZ) = axiom comm-S1-CZ
  lemma-dual (axiom comm-S1-CZ) = axiom comm-S0-CZ
  lemma-dual (axiom rel-X0-CZ) = axiom rel-X1-CZ
  lemma-dual (axiom rel-X1-CZ) = axiom rel-X0-CZ
  lemma-dual (axiom rel-CZ-H0-CZ) = axiom rel-CZ-H1-CZ
  lemma-dual (axiom rel-CZ-H1-CZ) = axiom rel-CZ-H0-CZ
  lemma-dual refl = refl
  lemma-dual (sym hyp) = sym (lemma-dual hyp)
  lemma-dual (trans hyp hyp₁) = trans (lemma-dual hyp) (lemma-dual hyp₁)
  lemma-dual (cong hyp hyp₁) = cong (lemma-dual hyp) (lemma-dual hyp₁)
  lemma-dual assoc = assoc
  lemma-dual left-unit = left-unit
  lemma-dual right-unit = right-unit

  -- A proof principle for duality.
  by-duality : ∀ {w u} -> w ≈ u -> dual w ≈ dual u
  by-duality = lemma-dual

-- ----------------------------------------------------------------------
-- * Lemmas

module Clifford-Powers where

  -- This module provides a rewrite system for reducing powers of
  -- Clifford operators (for example, S⁴ → I). It also commutes
  -- generators on different qubits (for example, H1 H0 → H0 H1).
  -- Finally, it moves scalars to the end of the word. While this is
  -- not yet a very powerful rewrite system, it is a useful
  -- bootstrapping step.

  open Clifford
  open Rewriting
  
  -- The at-head tactic: apply an axiom or a lemma at the beginning of a
  -- list. See above for usage information.
  at-head : ∀ {X'} {Γ' : WRel X'} {u v k} -> let open PB Γ' in u ≈ v -> let open PP Γ' in from-list (to-list u ++ k) ≈ from-list (to-list v ++ k)
  at-head {X'} {Γ'} {u} {v} {k} hyp =
     begin from-list (to-list u ++ k)
             ≈⟨ from-list-homo (to-list u) k ⟩
         from-list (to-list u) • from-list k
             ≈⟨ cleft lemma-from-to {u} ⟩
         u • from-list k
             ≈⟨ cleft hyp ⟩
         v • from-list k
             ≈⟨ cleft lemma-from-to {v} reversed ⟩
         from-list (to-list v) • from-list k
             ≈⟨ from-list-homo (to-list v) k reversed ⟩
         from-list (to-list v ++ k) ∎
         where
         open PB Γ'
         open PP Γ'
         open SR word-setoid


  -- The in-context tactic: apply an axiom at a specified position
  -- inside a word. See above for usage information.
  in-context : ∀ {X} {Γ : WRel X} {s t pre post s2 t2 s3 t3} -> (n m : ℕ) ->
             let open PP Γ in
             let open PB Γ in
             let s' = to-list2 s
                 t' = to-list2 t
                 m' = m + length t' - length s'
             in (mysplit n m s' , mysplit n m' t' , to-list s2 , to-list t2) ≡ ((pre , s2 , post) , (pre , t2 , post) , to-list s3 , to-list t3) ->
                s3 ≈ t3 -> s ≈ t

  in-context {X} {Γ} {s} {t} {pre} {post} {s2} {t2} {s3} {t3} n m hyp lemma =
    let open PP Γ in
    let open PB Γ in
    let open SR word-setoid in
    let s' = to-list2 s
        t' = to-list2 t
        m' = m + length t' - length s'
        hyp1 = Eq.cong proj₁ hyp
        hyp2 = Eq.cong proj₁ (Eq.cong proj₂ hyp)
        hyp3 = Eq.cong proj₁ (Eq.cong proj₂ (Eq.cong proj₂ hyp))
        hyp4 = Eq.cong proj₂ (Eq.cong proj₂ (Eq.cong proj₂ hyp))
    in
    begin s
            ≈⟨ refl' (lemma-from-to2 s) reversed ⟩
        from-list2 s'
            ≈⟨ lemma-mysplit n m s' hyp1 reversed ⟩
        from-list pre • s2 • from-list post
            ≈⟨ cright cleft by-assoc hyp3 ⟩
        from-list pre • s3 • from-list post
            ≈⟨ cright cleft lemma ⟩
        from-list pre • t3 • from-list post
            ≈⟨ cright cleft by-assoc hyp4 reversed ⟩
        from-list pre • t2 • from-list post
            ≈⟨ lemma-mysplit n m' t' hyp2 ⟩
        from-list2 t'
            ≈⟨ refl' (lemma-from-to2 t) ⟩
        t ∎



  -- The rewrite-in-context tactic: given a multistep rewrite rule,
  -- prove the equality of two words ≈⟨ applying rewriting only to the ⟩
  -- subword at the specified position. See above for usage information.
  rewrite-in-context : ∀ {X Γ s t pre post s2 t2} -> (multistep : (n : ℕ) -> List X -> List X) -> (lemma-multistep : (n : ℕ) -> (xs : List X) -> let open PP Γ in let open PB Γ in from-list xs ≈ from-list (multistep n xs)) -> (n m k : ℕ) ->
             let open PP Γ in
             let open PB Γ in
             let s' = to-list2 s
                 t' = to-list2 t
                 m' = m + length t' - length s'
             in (mysplit n m s' , mysplit n m' t' , multistep k (to-list s2)) ≡ 
                ((pre , s2 , post) , (pre , t2 , post) , multistep k (to-list t2)) ->
                s ≈ t
  rewrite-in-context {X} {Γ} {s} {t} {pre} {post} {s2} {t2} multistep lemma-multistep n m k hyp =
    let open PP Γ in
    let open PB Γ in
    let open SR word-setoid in
    let s' = to-list2 s
        t' = to-list2 t
        m' = m + length t' - length s'
        hyp1 = Eq.cong proj₁ hyp
        hyp2 = Eq.cong proj₁ (Eq.cong proj₂ hyp)
        hyp3 = Eq.cong proj₂ (Eq.cong proj₂ hyp)
    in
    begin s
            ≈⟨ refl' (lemma-from-to2 s) reversed ⟩
        from-list2 s'
            ≈⟨ lemma-mysplit n m s' hyp1 reversed ⟩
        from-list pre • s2 • from-list post
            ≈⟨ cright cleft lemma-from-to {s2} reversed ⟩
        from-list pre • from-list (to-list s2) • from-list post
            ≈⟨ cright cleft (lemma-multistep k (to-list s2)) ⟩
        from-list pre • from-list (multistep k (to-list s2)) • from-list post
            ≈⟨ cright cleft refl' (Eq.cong from-list hyp3) ⟩
        from-list pre • from-list (multistep k (to-list t2)) • from-list post
            ≈⟨ cright cleft (lemma-multistep k (to-list t2)) reversed ⟩
        from-list pre • from-list (to-list t2) • from-list post
            ≈⟨ cright cleft lemma-from-to {t2} ⟩
        from-list pre • t2 • from-list post
            ≈⟨ lemma-mysplit n m' t' hyp2 ⟩
        from-list2 t'
            ≈⟨ refl' (lemma-from-to2 t) ⟩
        t ∎

  open PB _===_ hiding (_===_)
  open PP _===_


  -- ----------------------------------------------------------------------
  -- * Lemmas

  -- The following lemmas are needed to justify the rewrite steps.

  -- ----------------------------------------------------------------------
  -- * Rewrite rules for monoidal structure and order of generators

  step-order : Step-Function Gen _===_

  -- Order of generators.
  step-order (S0-gen ∷ S0-gen ∷ S0-gen ∷ S0-gen ∷ xs) = just (xs , at-head (axiom Clifford.order-S0))
  step-order (H0-gen ∷ H0-gen ∷ xs) = just (xs , at-head (axiom order-H0))
  step-order (S1-gen ∷ S1-gen ∷ S1-gen ∷ S1-gen ∷ xs) = just (xs , at-head (axiom Clifford.order-S1))
  step-order (H1-gen ∷ H1-gen ∷ xs) = just (xs , at-head (axiom order-H1))
  step-order (CZ-gen ∷ CZ-gen ∷ xs) = just (xs , at-head (axiom order-CZ))

  -- Commuting rules for unary gates.
  step-order (H1-gen ∷ H0-gen ∷ t) = just (H0-gen ∷ H1-gen ∷ t , at-head (axiom comm-H0H1 reversed))
  step-order (H1-gen ∷ S0-gen ∷ t) = just (S0-gen ∷ H1-gen ∷ t , at-head (axiom comm-S0H1 reversed))
  step-order (S1-gen ∷ H0-gen ∷ t) = just (H0-gen ∷ S1-gen ∷ t , at-head (axiom comm-H0S1 reversed))
  step-order (S1-gen ∷ S0-gen ∷ t) = just (S0-gen ∷ S1-gen ∷ t , at-head (axiom comm-S0S1 reversed))

  -- Catch-all
  step-order _ = nothing

  -- From this rewrite relation, we extract a tactic 'general-powers'.
  open Rewriting.Step (step-cong step-order) renaming (general-rewrite to general-powers) public

module Clifford-Rewriting1 where

  -- This module provides a complete rewrite system for 1-qubit
  -- Clifford operators. It is specialized toward relations on qubit 0
  -- (but can also be applied to qubit 1 via duality).

  open Commuting-Clifford
  open Rewriting
  open Clifford
  open Clifford-Duality
  open Clifford-Powers

  open PB _===_ hiding (_===_)
  open PP _===_
  open SR word-setoid


  -- ----------------------------------------------------------------------
  -- * Lemmas

  -- The following lemmas are needed to justify the rewrite steps.

  lemma-S0-H0-S0-H0 : S0 • H0 • S0 • H0 ≈ H0 • S0 • S0 • S0
  lemma-S0-H0-S0-H0 =
      begin S0 • H0 • S0 • H0
              ≈⟨ general-powers 10 auto ⟩
          (S0 • H0) ^ 3 • (H0 • S0 • S0 • S0)
              ≈⟨ cleft axiom order-S0H0 ⟩
          ε • (H0 • S0 • S0 • S0)
              ≈⟨ general-comm auto ⟩
          H0 • S0 • S0 • S0 ∎

  lemma-H0-S0-H0-S0 : H0 • S0 • H0 • S0 ≈ S0 • S0 • S0 • H0
  lemma-H0-S0-H0-S0 =
      begin H0 • S0 • H0 • S0
              ≈⟨ general-powers 10 auto ⟩
                 S0⁻¹ • (S0 • H0) ^ 3 • H0
              ≈⟨ cright cleft axiom order-S0H0  ⟩
              S0⁻¹ • ε • H0
              ≈⟨ general-comm auto ⟩
              S0 • S0 • S0 • H0 ∎

  lemma-H0-S0-S0-S0-H0 : H0 • S0 • S0 • S0 • H0 ≈ S0 • H0 • S0
  lemma-H0-S0-S0-S0-H0 =
      begin H0 • S0 • S0 • S0 • H0
              ≈⟨ general-powers 10 auto ⟩
          H0 • (S0 • S0 • S0 • H0)
              ≈⟨ cright lemma-H0-S0-H0-S0 reversed ⟩
          H0 • (H0 • S0 • H0 • S0)
              ≈⟨ general-powers 10 auto ⟩
          S0 • H0 • S0 ∎

  lemma-S0-H0-S0-S0-H0-S0 : S0 • H0 • S0 • S0 • H0 • S0 ≈ H0 • S0 • S0 • H0
  lemma-S0-H0-S0-S0-H0-S0 =
      begin S0 • H0 • S0 • S0 • H0 • S0
              ≈⟨ general-powers 10 auto ⟩
          ((S0 • H0 • S0) • (S0 • H0 • S0))
              ≈⟨ cong lemma-H0-S0-S0-S0-H0 lemma-H0-S0-S0-S0-H0 reversed ⟩
          ((H0 • S0 • S0 • S0 • H0) • (H0 • S0 • S0 • S0 • H0))
              ≈⟨ general-powers 10 auto ⟩
          H0 • S0 • S0 • H0 ∎

  lemma-H0-S0-S0-H0-S0-S0 : H0 • S0 • S0 • H0 • S0 • S0 ≈ S0 • S0 • H0 • S0 • S0 • H0
  lemma-H0-S0-S0-H0-S0-S0 =
      begin H0 • S0 • S0 • H0 • S0 • S0
              ≈⟨ general-powers 10 auto ⟩
          (H0 • S0) • (S0 • H0 • S0) • (S0)
              ≈⟨ cright cleft lemma-H0-S0-S0-S0-H0 reversed ⟩
          (H0 • S0) • (H0 • S0 • S0 • S0 • H0) • (S0)
              ≈⟨ by-assoc auto ⟩
          (H0 • S0 • H0 • S0) • (S0 • S0 • H0 • S0)
              ≈⟨ cleft lemma-H0-S0-H0-S0 ⟩
          (S0 • S0 • S0 • H0) • (S0 • S0 • H0 • S0)
              ≈⟨ general-comm auto ⟩
          (S0 • S0) • (S0 • H0 • S0 • S0 • H0 • S0)
              ≈⟨ cright lemma-S0-H0-S0-S0-H0-S0 ⟩
          (S0 • S0) • (H0 • S0 • S0 • H0)
              ≈⟨ general-comm auto ⟩
          S0 • S0 • H0 • S0 • S0 • H0 ∎

  lemma-S0-S0-S0-H0-S0-S0-H0 : S0 • S0 • S0 • H0 • S0 • S0 • H0 ≈ H0 • S0 • S0 • H0 • S0
  lemma-S0-S0-S0-H0-S0-S0-H0 =
      begin S0 • S0 • S0 • H0 • S0 • S0 • H0
              ≈⟨ general-powers 10 auto ⟩
          (S0 • S0 • S0 • H0) • (S0 • S0 • H0)
              ≈⟨ cleft lemma-H0-S0-H0-S0 reversed ⟩
          (H0 • S0 • H0 • S0) • (S0 • S0 • H0)
              ≈⟨ by-assoc auto ⟩
          (H0 • S0 • H0) • (S0 • S0 • S0 • H0)
              ≈⟨ cright lemma-H0-S0-H0-S0 reversed ⟩
          (H0 • S0 • H0) • (H0 • S0 • H0 • S0)
              ≈⟨ general-powers 10 auto ⟩
          H0 • S0 • S0 • H0 • S0 ∎

  lemma-S0-S0-S0-H0-S0-S0-S0 : S0 • S0 • S0 • H0 • S0 • S0 • S0 ≈ H0 • S0 • H0
  lemma-S0-S0-S0-H0-S0-S0-S0 =
      begin S0 • S0 • S0 • H0 • S0 • S0 • S0
              ≈⟨ general-powers 10 auto ⟩
          (S0 • S0 • S0) • (H0 • S0 • S0 • S0)
              ≈⟨ cright lemma-S0-H0-S0-H0 reversed ⟩
          (S0 • S0 • S0) • (S0 • H0 • S0 • H0)
              ≈⟨ general-powers 10 auto ⟩
          H0 • S0 • H0 ∎

  -- ----------------------------------------------------------------------
  -- * Rewrite rules for 1-qubit Clifford relations
  
  step-clifford1 : Step-Function Gen _===_

  -- Rules for unary gates.
  step-clifford1 (H0-gen ∷ H0-gen ∷ t) = just (t , at-head (axiom order-H0))
  step-clifford1 (S0-gen ∷ S0-gen ∷ S0-gen ∷ S0-gen ∷ t) = just (t , at-head (axiom order-S0))
  step-clifford1 (S0-gen ∷ H0-gen ∷ S0-gen ∷ H0-gen ∷ t) = just (H0-gen ∷ S0-gen ∷ S0-gen ∷ S0-gen ∷ t , at-head lemma-S0-H0-S0-H0)
  step-clifford1 (H0-gen ∷ S0-gen ∷ H0-gen ∷ S0-gen ∷ t) = just (S0-gen ∷ S0-gen ∷ S0-gen ∷ H0-gen ∷ t , at-head lemma-H0-S0-H0-S0)
  step-clifford1 (H0-gen ∷ S0-gen ∷ S0-gen ∷ S0-gen ∷ H0-gen ∷ t) = just (S0-gen ∷ H0-gen ∷ S0-gen ∷ t , at-head lemma-H0-S0-S0-S0-H0)
  step-clifford1 (S0-gen ∷ H0-gen ∷ S0-gen ∷ S0-gen ∷ H0-gen ∷ S0-gen ∷ t) = just (H0-gen ∷ S0-gen ∷ S0-gen ∷ H0-gen ∷ t , at-head lemma-S0-H0-S0-S0-H0-S0)
  step-clifford1 (H0-gen ∷ S0-gen ∷ S0-gen ∷ H0-gen ∷ S0-gen ∷ S0-gen ∷ t) = just (S0-gen ∷ S0-gen ∷ H0-gen ∷ S0-gen ∷ S0-gen ∷ H0-gen ∷ t , at-head lemma-H0-S0-S0-H0-S0-S0)
  step-clifford1 (S0-gen ∷ S0-gen ∷ S0-gen ∷ H0-gen ∷ S0-gen ∷ S0-gen ∷ H0-gen ∷ t) = just (H0-gen ∷ S0-gen ∷ S0-gen ∷ H0-gen ∷ S0-gen ∷ t , at-head lemma-S0-S0-S0-H0-S0-S0-H0)
  step-clifford1 (S0-gen ∷ S0-gen ∷ S0-gen ∷ H0-gen ∷ S0-gen ∷ S0-gen ∷ S0-gen ∷ t) = just (H0-gen ∷ S0-gen ∷ H0-gen ∷ t , at-head lemma-S0-S0-S0-H0-S0-S0-S0)

  step-clifford1 (H1-gen ∷ H1-gen ∷ t) = just (t , at-head (axiom order-H1))
  step-clifford1 (S1-gen ∷ S1-gen ∷ S1-gen ∷ S1-gen ∷ t) = just (t , at-head (axiom order-S1))
  step-clifford1 (S1-gen ∷ H1-gen ∷ S1-gen ∷ H1-gen ∷ t) = just (H1-gen ∷ S1-gen ∷ S1-gen ∷ S1-gen ∷ t , at-head (by-duality lemma-S0-H0-S0-H0))
  step-clifford1 (H1-gen ∷ S1-gen ∷ H1-gen ∷ S1-gen ∷ t) = just (S1-gen ∷ S1-gen ∷ S1-gen ∷ H1-gen ∷ t , at-head (by-duality lemma-H0-S0-H0-S0))
  step-clifford1 (H1-gen ∷ S1-gen ∷ S1-gen ∷ S1-gen ∷ H1-gen ∷ t) = just (S1-gen ∷ H1-gen ∷ S1-gen ∷ t , at-head (by-duality lemma-H0-S0-S0-S0-H0))
  step-clifford1 (S1-gen ∷ H1-gen ∷ S1-gen ∷ S1-gen ∷ H1-gen ∷ S1-gen ∷ t) = just (H1-gen ∷ S1-gen ∷ S1-gen ∷ H1-gen ∷ t , at-head (by-duality lemma-S0-H0-S0-S0-H0-S0))
  step-clifford1 (H1-gen ∷ S1-gen ∷ S1-gen ∷ H1-gen ∷ S1-gen ∷ S1-gen ∷ t) = just (S1-gen ∷ S1-gen ∷ H1-gen ∷ S1-gen ∷ S1-gen ∷ H1-gen ∷ t , at-head (by-duality lemma-H0-S0-S0-H0-S0-S0))
  step-clifford1 (S1-gen ∷ S1-gen ∷ S1-gen ∷ H1-gen ∷ S1-gen ∷ S1-gen ∷ H1-gen ∷ t) = just (H1-gen ∷ S1-gen ∷ S1-gen ∷ H1-gen ∷ S1-gen ∷ t , at-head (by-duality lemma-S0-S0-S0-H0-S0-S0-H0))
  step-clifford1 (S1-gen ∷ S1-gen ∷ S1-gen ∷ H1-gen ∷ S1-gen ∷ S1-gen ∷ S1-gen ∷ t) = just (H1-gen ∷ S1-gen ∷ H1-gen ∷ t , at-head (by-duality lemma-S0-S0-S0-H0-S0-S0-S0))

  -- Catch-all
  step-clifford1 _ = nothing

  -- From this rewrite relation, we extract a tactic 'rewrite-clifford1'.
  open Rewriting.Step (step-cong step-order then step-cong step-clifford1) renaming (general-rewrite to rewrite-clifford1) public

module Clifford-Rewriting where

  -- This module provides a complete rewrite system for 2-qubit
  -- Clifford operators.

  open Commuting-Clifford
  open Rewriting
  open Clifford
  open Clifford-Duality
  open Clifford-Powers
  open Clifford-Rewriting1

  open PB _===_ hiding (_===_)
  open PP _===_
  open SR word-setoid

  -- ----------------------------------------------------------------------
  -- * More lemmas
  
  -- The following lemmas are needed to justify the rewrite steps.

  lemma-S0-S0-H0-CZ : S0 • S0 • H0 • CZ ≈ H0 • CZ • X0 • S1 • S1
  lemma-S0-S0-H0-CZ =
      begin S0 • S0 • H0 • CZ
              ≈⟨ rewrite-clifford1 10 auto ⟩
          H0 • (X0 • CZ)
              ≈⟨ cright axiom rel-X0-CZ ⟩
          H0 • (CZ • Z1 • X0)
              ≈⟨ rewrite-clifford1 10 auto ⟩
          H0 • CZ • X0 • S1 • S1 ∎

  lemma-H0-S0-H0-CZ : H0 • S0 • H0 • CZ ≈ S0 • H0 • CZ • S0 • X0 • S1 • S1
  lemma-H0-S0-H0-CZ =
      begin H0 • S0 • H0 • CZ
              ≈⟨ rewrite-clifford1 10 auto ⟩
          S0 • S0 • S0 • H0 • S0 • S0 • S0 • CZ
              ≈⟨ general-comm auto ⟩
          S0 • (S0 • S0 • H0 • CZ) • (S0 • S0 • S0)
              ≈⟨ cright cleft lemma-S0-S0-H0-CZ ⟩
          S0 • (H0 • CZ • X0 • S1 • S1) • (S0 • S0 • S0)
              ≈⟨ rewrite-clifford1 20 auto ⟩
          S0 • H0 • CZ • S0 • X0 • S1 • S1 ∎

  lemma-S0-H0-CZ-H0-H1-CZ : S0 • H0 • CZ • H0 • H1 • CZ ≈ H0 • CZ • H0 • H1 • CZ • H1 • S1 • H1
  lemma-S0-H0-CZ-H0-H1-CZ =
      begin S0 • H0 • CZ • H0 • H1 • CZ
              ≈⟨ general-powers 10 auto ⟩
          (S0 • H0) • (CZ • H0 • CZ) • (CZ • H1 • CZ)
              ≈⟨ cright cleft axiom rel-CZ-H0-CZ ⟩
          (S0 • H0) • (S0 • H0 • CZ • S0 • H0 • S0 • S1) • (CZ • H1 • CZ)
              ≈⟨ rewrite-clifford1 10 auto ⟩
          H0 • S0 • S0 • S0 • CZ • S0 • H0 • S0 • S1 • CZ • H1 • CZ
              ≈⟨ general-comm auto ⟩
          H0 • CZ • S0 • S0 • S0 • S0 • H0 • S0 • S1 • CZ • H1 • CZ
              ≈⟨ rewrite-clifford1 10 auto ⟩
          (H0 • CZ • H0 • S0 • S1) • (CZ • H1 • CZ)
              ≈⟨ cright axiom rel-CZ-H1-CZ ⟩
          (H0 • CZ • H0 • S0 • S1) • (S1 • H1 • CZ • S1 • H1 • S1 • S0)
              ≈⟨ by-assoc auto ⟩
          (H0 • CZ • H0 • S0) • (S1 • S1 • H1 • CZ) • (S1 • H1 • S1 • S0)
              ≈⟨ cright cleft by-duality lemma-S0-S0-H0-CZ ⟩
          (H0 • CZ • H0 • S0) • (H1 • CZ • X1 • S0 • S0) • (S1 • H1 • S1 • S0)
              ≈⟨ general-comm auto ⟩
          H0 • CZ • H0 • H1 • CZ • S0 •  X1 • S0 • S0 • S1 • H1 • S1 • S0
              ≈⟨ rewrite-clifford1 30 auto ⟩
          H0 • CZ • H0 • H1 • CZ • H1 • S1 • H1 ∎

  lemma-H0-CZ-S0-H0-H1-CZ : H0 • CZ • S0 • H0 • H1 • CZ ≈ CZ • S0 • H0 • H1 • CZ • H0 • S0 • S0 • H0 • S1 • S1 • S1 • H1 • S1
  lemma-H0-CZ-S0-H0-H1-CZ =
      begin H0 • CZ • S0 • H0 • H1 • CZ
              ≈⟨ general-comm auto ⟩
          H0 • S0 • CZ • H0 • H1 • CZ
              ≈⟨ general-powers 10 auto ⟩
          (H0 • S0) • (CZ • H0 • CZ) • (CZ • H1 • CZ)
              ≈⟨ cright cleft axiom rel-CZ-H0-CZ ⟩
          (H0 • S0) • (S0 • H0 • CZ • S0 • H0 • S0 • S1) • (CZ • H1 • CZ)
              ≈⟨ by-assoc auto ⟩
          (X0 • CZ) • (S0 • H0 • S0 • S1 • CZ • H1 • CZ)
              ≈⟨ cleft axiom rel-X0-CZ ⟩
          (CZ • Z1 • X0) • (S0 • H0 • S0 • S1 • CZ • H1 • CZ)
              ≈⟨ rewrite-clifford1 30 auto ⟩
          (CZ • H0 • S0 • H0 • S1 • S1 • S1) • (CZ • H1 • CZ)
              ≈⟨ cright axiom rel-CZ-H1-CZ ⟩
          (CZ • H0 • S0 • H0 • S1 • S1 • S1) • (S1 • H1 • CZ • S1 • H1 • S1 • S0)
              ≈⟨ general-powers 10 auto ⟩
          (CZ • H1) • (H0 • S0 • H0 • CZ) • (S1 • H1 • S1 • S0)
              ≈⟨ cright cleft lemma-H0-S0-H0-CZ ⟩
          (CZ • H1) • (S0 • H0 • CZ • S0 • X0 • S1 • S1) • (S1 • H1 • S1 • S0)
              ≈⟨ rewrite-clifford1 20 auto ⟩
          CZ • S0 • H0 • H1 • CZ • H0 • S0 • S0 • H0 • S1 • S1 • S1 • H1 • S1 ∎

  lemma-H0-CZ-H0-H1-CZ-H0-H1-CZ : H0 • CZ • H0 • H1 • CZ • H0 • H1 • CZ ≈ CZ • H0 • H1 • CZ • H0 • H1 • CZ • H1
  lemma-H0-CZ-H0-H1-CZ-H0-H1-CZ =
      begin H0 • CZ • H0 • H1 • CZ • H0 • H1 • CZ
              ≈⟨ general-powers 10 auto ⟩
          (H0 • CZ • H0 • H1) • (CZ • H0 • CZ) • (CZ • H1 • CZ)
              ≈⟨ cright cleft axiom rel-CZ-H0-CZ ⟩
          (H0 • CZ • H0 • H1) • (S0 • H0 • CZ • S0 • H0 • S0 • S1) • (CZ • H1 • CZ)
              ≈⟨ general-comm auto ⟩
          (H0 • CZ • H1) • (H0 • S0 • H0 • CZ) • (S0 • H0 • S0 • S1 • CZ • H1 • CZ)
              ≈⟨ cright cleft lemma-H0-S0-H0-CZ ⟩
          (H0 • CZ • H1) • (S0 • H0 • CZ • S0 • X0 • S1 • S1) • (S0 • H0 • S0 • S1 • CZ • H1 • CZ)
              ≈⟨ general-comm auto ⟩
          (H0 • CZ • S0 • H0 • H1 • CZ) • (S0 • X0 • S1 • S1 • S0 • H0 • S0 • S1 • CZ • H1 • CZ)
              ≈⟨ cleft lemma-H0-CZ-S0-H0-H1-CZ ⟩
          (CZ • S0 • H0 • H1 • CZ • H0 • S0 • S0 • H0 • S1 • S1 • S1 • H1 • S1) • (S0 • X0 • S1 • S1 • S0 • H0 • S0 • S1 • CZ • H1 • CZ)
              ≈⟨ rewrite-clifford1 70 auto ⟩
          CZ • S0 • H0 • H1 • CZ • H0 • S0 • S1 • S1 • S1 • H1 • CZ • H1 • CZ
              ≈⟨ general-comm auto ⟩
          (CZ • H1 • S1 • S1 • S1) • (S0 • H0 • CZ • H0 • H1 • CZ) • (S0 • H1 • CZ)
              ≈⟨ cright cleft lemma-S0-H0-CZ-H0-H1-CZ ⟩
          (CZ • H1 • S1 • S1 • S1) • (H0 • CZ • H0 • H1 • CZ • H1 • S1 • H1) • (S0 • H1 • CZ)
              ≈⟨ general-powers 10 auto ⟩
          CZ • H1 • S1 • S1 • S1 • H0 • CZ • H0 • H1 • CZ • H1 • S1 • S0 • CZ
              ≈⟨ general-comm auto ⟩
          (CZ • H1 • S1 • S1 • S1 • H0 • CZ • H0 • H1) • (CZ • H1 • CZ) • (S0 • S1)
              ≈⟨ cright cleft axiom rel-CZ-H1-CZ ⟩
          (CZ • H1 • S1 • S1 • S1 • H0 • CZ • H0 • H1) • (S1 • H1 • CZ • S1 • H1 • S1 • S0) • (S0 • S1)
              ≈⟨ general-comm auto ⟩
          CZ • H1 • H0 • CZ • H0 • S1 • S1 • S1 • H1 • S1 • H1 • S1 • CZ • H1 • S1 • S0 • S0 • S1
              ≈⟨ rewrite-clifford1 20 auto ⟩
          (CZ • H1 • H0 • CZ • H0) • (S1 • S1 • H1 • CZ) • (H1 • S1 • S0 • S0 • S1)
              ≈⟨ cright cleft by-duality lemma-S0-S0-H0-CZ ⟩
          (CZ • H1 • H0 • CZ • H0) • (H1 • CZ • X1 • S0 • S0) • (H1 • S1 • S0 • S0 • S1)
              ≈⟨ rewrite-clifford1 20 auto ⟩
          CZ • H0 • H1 • CZ • H0 • H1 • CZ • H1 ∎

  lemma-S0-H1-CZ : S0 • H1 • CZ ≈ H1 • CZ • S0
  lemma-S0-H1-CZ = general-comm auto

  lemma-S0-S1-H1-CZ : S0 • S1 • H1 • CZ ≈ S1 • H1 • CZ • S0
  lemma-S0-S1-H1-CZ = general-comm auto

  lemma-S1-S1-H1-CZ : S1 • S1 • H1 • CZ ≈ H1 • CZ • S0 • S0 • X1
  lemma-S1-S1-H1-CZ =
      begin S1 • S1 • H1 • CZ
              ≈⟨ by-duality lemma-S0-S0-H0-CZ ⟩
          H1 • CZ • X1 • S0 • S0
              ≈⟨ general-comm auto ⟩
          H1 • CZ • S0 • S0 • X1 ∎

  lemma-S0-S0-H0-H1-CZ : S0 • S0 • H0 • H1 • CZ ≈ H0 • H1 • CZ • X0 • S1 • S1
  lemma-S0-S0-H0-H1-CZ =
      begin S0 • S0 • H0 • H1 • CZ
              ≈⟨ general-comm auto ⟩
          H1 • (S0 • S0 • H0 • CZ)
              ≈⟨ cright lemma-S0-S0-H0-CZ ⟩
          H1 • (H0 • CZ • X0 • S1 • S1)
              ≈⟨ general-comm auto ⟩
          H0 • H1 • CZ • X0 • S1 • S1 ∎

  lemma-S0-S0-H0-S1-H1-CZ : S0 • S0 • H0 • S1 • H1 • CZ ≈ H0 • S1 • H1 • CZ • X0 • S1 • S1
  lemma-S0-S0-H0-S1-H1-CZ =
      begin S0 • S0 • H0 • S1 • H1 • CZ
              ≈⟨ general-comm auto ⟩
          (S1 • H1) • (S0 • S0 • H0 • CZ)
              ≈⟨ cright lemma-S0-S0-H0-CZ ⟩
          (S1 • H1) • (H0 • CZ • X0 • S1 • S1)
              ≈⟨ general-comm auto ⟩
          H0 • S1 • H1 • CZ • X0 • S1 • S1 ∎

  lemma-H1-S1-H1-CZ : H1 • S1 • H1 • CZ ≈ S1 • H1 • CZ • S0 • S0 • S1 • X1
  lemma-H1-S1-H1-CZ =
      begin H1 • S1 • H1 • CZ
              ≈⟨ by-duality lemma-H0-S0-H0-CZ ⟩
          S1 • H1 • CZ • S1 • X1 • S0 • S0
              ≈⟨ general-comm auto ⟩
          S1 • H1 • CZ • S0 • S0 • S1 • X1 ∎

  lemma-H0-S0-H0-H1-CZ : H0 • S0 • H0 • H1 • CZ ≈ S0 • H0 • H1 • CZ • S0 • X0 • S1 • S1
  lemma-H0-S0-H0-H1-CZ =
      begin H0 • S0 • H0 • H1 • CZ
              ≈⟨ general-comm auto ⟩
          H1 • (H0 • S0 • H0 • CZ)
              ≈⟨ cright lemma-H0-S0-H0-CZ ⟩
          H1 • (S0 • H0 • CZ • S0 • X0 • S1 • S1)
              ≈⟨ general-comm auto ⟩
          S0 • H0 • H1 • CZ • S0 • X0 • S1 • S1 ∎
      
  lemma-H0-S0-H0-S1-H1-CZ : H0 • S0 • H0 • S1 • H1 • CZ ≈ S0 • H0 • S1 • H1 • CZ • S0 • X0 • S1 • S1
  lemma-H0-S0-H0-S1-H1-CZ =
      begin H0 • S0 • H0 • S1 • H1 • CZ
              ≈⟨ general-comm auto ⟩
          (S1 • H1) • (H0 • S0 • H0 • CZ)
              ≈⟨ cright lemma-H0-S0-H0-CZ ⟩
          (S1 • H1) • (S0 • H0 • CZ • S0 • X0 • S1 • S1)
              ≈⟨ general-comm auto ⟩
          S0 • H0 • S1 • H1 • CZ • S0 • X0 • S1 • S1 ∎

  lemma-S1-H1-CZ-H0-H1-CZ : S1 • H1 • CZ • H0 • H1 • CZ ≈ H1 • CZ • H0 • H1 • CZ • H0 • S0 • H0
  lemma-S1-H1-CZ-H0-H1-CZ =
      begin S1 • H1 • CZ • H0 • H1 • CZ
              ≈⟨ general-comm auto ⟩
          S1 • H1 • CZ • H1 • H0 • CZ
              ≈⟨ by-duality lemma-S0-H0-CZ-H0-H1-CZ ⟩
          H1 • CZ • H1 • H0 • CZ • H0 • S0 • H0
              ≈⟨ general-comm auto ⟩
          H1 • CZ • H0 • H1 • CZ • H0 • S0 • H0 ∎
  
  lemma-S1-H1-CZ-S0-H0-H1-CZ : S1 • H1 • CZ • S0 • H0 • H1 • CZ ≈ H1 • CZ • S0 • H0 • H1 • CZ • H0 • S0 • H0
  lemma-S1-H1-CZ-S0-H0-H1-CZ =
      begin S1 • H1 • CZ • S0 • H0 • H1 • CZ
              ≈⟨ general-comm auto ⟩
          S0 • (S1 • H1 • CZ • H1 • H0 • CZ)
              ≈⟨ cright by-duality lemma-S0-H0-CZ-H0-H1-CZ ⟩
          S0 • (H1 • CZ • H1 • H0 • CZ • H0 • S0 • H0)
              ≈⟨ general-comm auto ⟩
          H1 • CZ • S0 • H0 • H1 • CZ • H0 • S0 • H0 ∎
  
  lemma-S0-H0-H1-CZ-H0-H1-CZ : S0 • H0 • H1 • CZ • H0 • H1 • CZ ≈ H0 • H1 • CZ • H0 • H1 • CZ • H1 • S1 • H1
  lemma-S0-H0-H1-CZ-H0-H1-CZ =
      begin S0 • H0 • H1 • CZ • H0 • H1 • CZ
              ≈⟨ general-comm auto ⟩
          H1 • (S0 • H0 • CZ • H0 • H1 • CZ)
              ≈⟨ cright lemma-S0-H0-CZ-H0-H1-CZ ⟩
          H1 • (H0 • CZ • H0 • H1 • CZ • H1 • S1 • H1)
              ≈⟨ general-comm auto ⟩
          H0 • H1 • CZ • H0 • H1 • CZ • H1 • S1 • H1 ∎

  lemma-S0-H0-CZ-H0-S1-H1-CZ : S0 • H0 • CZ • H0 • S1 • H1 • CZ ≈ H0 • CZ • H0 • S1 • H1 • CZ • H1 • S1 • H1
  lemma-S0-H0-CZ-H0-S1-H1-CZ =
      begin S0 • H0 • CZ • H0 • S1 • H1 • CZ
              ≈⟨ general-comm auto ⟩
          S1 • (S0 • H0 • CZ • H0 • H1 • CZ)
              ≈⟨ cright lemma-S0-H0-CZ-H0-H1-CZ ⟩
          S1 • (H0 • CZ • H0 • H1 • CZ • H1 • S1 • H1)
              ≈⟨ general-comm auto ⟩
          H0 • CZ • H0 • S1 • H1 • CZ • H1 • S1 • H1 ∎
  
  lemma-H1-CZ-H0-S1-H1-CZ : H1 • CZ • H0 • S1 • H1 • CZ ≈ CZ • H0 • S1 • H1 • CZ • S0 • S0 • S0 • H0 • S0 • H1 • S1 • S1 • H1
  lemma-H1-CZ-H0-S1-H1-CZ =
      begin H1 • CZ • H0 • S1 • H1 • CZ
              ≈⟨ general-comm auto ⟩
          H1 • CZ • S1 • H1 • H0 • CZ
              ≈⟨ by-duality lemma-H0-CZ-S0-H0-H1-CZ ⟩
          CZ • S1 • H1 • H0 • CZ • H1 • S1 • S1 • H1 • S0 • S0 • S0 • H0 • S0
              ≈⟨ general-comm auto ⟩
          CZ • H0 • S1 • H1 • CZ • S0 • S0 • S0 • H0 • S0 • H1 • S1 • S1 • H1 ∎

  lemma-H1-CZ-S0-H0-S1-H1-CZ : H1 • CZ • S0 • H0 • S1 • H1 • CZ ≈ CZ • S0 • H0 • S1 • H1 • CZ • S0 • S0 • S0 • H0 • S0 • H1 • S1 • S1 • H1
  lemma-H1-CZ-S0-H0-S1-H1-CZ =
      begin H1 • CZ • S0 • H0 • S1 • H1 • CZ
              ≈⟨ general-comm auto ⟩
          S0 • (H1 • CZ • S1 • H1 • H0 • CZ)
              ≈⟨ cright by-duality lemma-H0-CZ-S0-H0-H1-CZ ⟩
          S0 • (CZ • S1 • H1 • H0 • CZ • H1 • S1 • S1 • H1 • S0 • S0 • S0 • H0 • S0)
              ≈⟨ general-comm auto ⟩
          CZ • S0 • H0 • S1 • H1 • CZ • S0 • S0 • S0 • H0 • S0 • H1 • S1 • S1 • H1 ∎

  lemma-H0-H1-CZ-S0-H0-H1-CZ : H0 • H1 • CZ • S0 • H0 • H1 • CZ ≈ H1 • CZ • S0 • H0 • H1 • CZ • H0 • S0 • S0 • H0 • S1 • S1 • S1 • H1 • S1
  lemma-H0-H1-CZ-S0-H0-H1-CZ =
      begin H0 • H1 • CZ • S0 • H0 • H1 • CZ
              ≈⟨ general-comm auto ⟩
          H1 • (H0 • CZ • S0 • H0 • H1 • CZ)
              ≈⟨ cright lemma-H0-CZ-S0-H0-H1-CZ ⟩
          H1 • (CZ • S0 • H0 • H1 • CZ • H0 • S0 • S0 • H0 • S1 • S1 • S1 • H1 • S1)
              ≈⟨ by-assoc auto ⟩
          H1 • CZ • S0 • H0 • H1 • CZ • H0 • S0 • S0 • H0 • S1 • S1 • S1 • H1 • S1 ∎

  lemma-H0-CZ-S0-H0-S1-H1-CZ : H0 • CZ • S0 • H0 • S1 • H1 • CZ ≈ CZ • S0 • H0 • S1 • H1 • CZ • H0 • S0 • S0 • H0 • S1 • S1 • S1 • H1 • S1
  lemma-H0-CZ-S0-H0-S1-H1-CZ =
      begin H0 • CZ • S0 • H0 • S1 • H1 • CZ
              ≈⟨ general-comm auto ⟩
          S1 • (H0 • CZ • S0 • H0 • H1 • CZ)
              ≈⟨ cright lemma-H0-CZ-S0-H0-H1-CZ ⟩
          S1 • (CZ • S0 • H0 • H1 • CZ • H0 • S0 • S0 • H0 • S1 • S1 • S1 • H1 • S1)
              ≈⟨ general-comm auto ⟩
          CZ • S0 • H0 • S1 • H1 • CZ • H0 • S0 • S0 • H0 • S1 • S1 • S1 • H1 • S1 ∎

  lemma-CZ-S0-H0-CZ : CZ • S0 • H0 • CZ ≈ S0 • S0 • H0 • CZ • S0 • H0 • S0 • S1
  lemma-CZ-S0-H0-CZ =
      begin CZ • S0 • H0 • CZ
              ≈⟨ general-comm auto ⟩
          S0 • (CZ • H0 • CZ)
              ≈⟨ cright axiom rel-CZ-H0-CZ ⟩
          S0 • (S0 • H0 • CZ • S0 • H0 • S0 • S1)
              ≈⟨ by-assoc auto ⟩
          S0 • S0 • H0 • CZ • S0 • H0 • S0 • S1 ∎

  lemma-CZ-H1-CZ : CZ • H1 • CZ ≈ S1 • H1 • CZ • S0 • S1 • H1 • S1
  lemma-CZ-H1-CZ =
      begin CZ • H1 • CZ
              ≈⟨ by-duality (axiom rel-CZ-H0-CZ) ⟩
          S1 • H1 • CZ • S1 • H1 • S1 • S0
              ≈⟨ general-comm auto ⟩
          S1 • H1 • CZ • S0 • S1 • H1 • S1 ∎

  lemma-CZ-S1-H1-CZ : CZ • S1 • H1 • CZ ≈ S1 • S1 • H1 • CZ • S0 • S1 • H1 • S1
  lemma-CZ-S1-H1-CZ =
      begin CZ • S1 • H1 • CZ
              ≈⟨ by-duality lemma-CZ-S0-H0-CZ ⟩
          S1 • S1 • H1 • CZ • S1 • H1 • S1 • S0
              ≈⟨ general-comm auto ⟩
          S1 • S1 • H1 • CZ • S0 • S1 • H1 • S1 ∎

  lemma-H1-CZ-H0-H1-CZ-H0-H1-CZ : H1 • CZ • H0 • H1 • CZ • H0 • H1 • CZ ≈ CZ • H0 • H1 • CZ • H0 • H1 • CZ • H0
  lemma-H1-CZ-H0-H1-CZ-H0-H1-CZ =
      begin H1 • CZ • H0 • H1 • CZ • H0 • H1 • CZ
              ≈⟨ general-comm auto ⟩
          H1 • CZ • H1 • H0 • CZ • H1 • H0 • CZ
              ≈⟨ by-duality (lemma-H0-CZ-H0-H1-CZ-H0-H1-CZ) ⟩
          CZ • H1 • H0 • CZ • H1 • H0 • CZ • H0
              ≈⟨ general-comm auto ⟩
          CZ • H0 • H1 • CZ • H0 • H1 • CZ • H0 ∎

  -- ----------------------------------------------------------------------
  -- * Rewrite rules for 2-qubit Clifford relations
  
  step-clifford2 : Step-Function Gen _===_

  -- Rules for binary gates.
  step-clifford2 (CZ-gen ∷ CZ-gen ∷ t) = just (t , at-head (axiom order-CZ))
  
  step-clifford2 (S1-gen ∷ CZ-gen ∷ t) = just (CZ-gen ∷ S1-gen ∷ t , at-head (axiom comm-S1-CZ))
  step-clifford2 (S0-gen ∷ CZ-gen ∷ t) = just (CZ-gen ∷ S0-gen ∷ t , at-head (axiom comm-S0-CZ))
  step-clifford2 (S0-gen ∷ H1-gen ∷ CZ-gen ∷ t) = just (H1-gen ∷ CZ-gen ∷ S0-gen ∷ t , at-head lemma-S0-H1-CZ)
  step-clifford2 (S0-gen ∷ S1-gen ∷ H1-gen ∷ CZ-gen ∷ t) = just (S1-gen ∷ H1-gen ∷ CZ-gen ∷ S0-gen ∷ t , at-head lemma-S0-S1-H1-CZ)
  
  step-clifford2 (S1-gen ∷ S1-gen ∷ H1-gen ∷ CZ-gen ∷ t) = just (H1-gen ∷ CZ-gen ∷ S0-gen ∷ S0-gen ∷ H1-gen ∷ S1-gen ∷ S1-gen ∷ H1-gen ∷ t , at-head lemma-S1-S1-H1-CZ)
  step-clifford2 (S0-gen ∷ S0-gen ∷ H0-gen ∷ CZ-gen ∷ t) = just (H0-gen ∷ CZ-gen ∷ H0-gen ∷ S0-gen ∷ S0-gen ∷ H0-gen ∷ S1-gen ∷ S1-gen ∷ t , at-head lemma-S0-S0-H0-CZ)
  step-clifford2 (S0-gen ∷ S0-gen ∷ H0-gen ∷ H1-gen ∷ CZ-gen ∷ t) = just (H0-gen ∷ H1-gen ∷ CZ-gen ∷ H0-gen ∷ S0-gen ∷ S0-gen ∷ H0-gen ∷ S1-gen ∷ S1-gen ∷ t , at-head lemma-S0-S0-H0-H1-CZ)
  step-clifford2 (S0-gen ∷ S0-gen ∷ H0-gen ∷ S1-gen ∷ H1-gen ∷ CZ-gen ∷ t) = just (H0-gen ∷ S1-gen ∷ H1-gen ∷ CZ-gen ∷ H0-gen ∷ S0-gen ∷ S0-gen ∷ H0-gen ∷ S1-gen ∷ S1-gen ∷ t , at-head lemma-S0-S0-H0-S1-H1-CZ)

  step-clifford2 (H1-gen ∷ S1-gen ∷ H1-gen ∷ CZ-gen ∷ t) = just (S1-gen ∷ H1-gen ∷ CZ-gen ∷ S0-gen ∷ S0-gen ∷ S1-gen ∷ H1-gen ∷ S1-gen ∷ S1-gen ∷ H1-gen ∷ t , at-head lemma-H1-S1-H1-CZ)
  step-clifford2 (H0-gen ∷ S0-gen ∷ H0-gen ∷ CZ-gen ∷ t) = just (S0-gen ∷ H0-gen ∷ CZ-gen ∷ S0-gen ∷ H0-gen ∷ S0-gen ∷ S0-gen ∷ H0-gen ∷ S1-gen ∷ S1-gen ∷ t , at-head lemma-H0-S0-H0-CZ)
  step-clifford2 (H0-gen ∷ S0-gen ∷ H0-gen ∷ H1-gen ∷ CZ-gen ∷ t) = just (S0-gen ∷ H0-gen ∷ H1-gen ∷ CZ-gen ∷ S0-gen ∷ H0-gen ∷ S0-gen ∷ S0-gen ∷ H0-gen ∷ S1-gen ∷ S1-gen ∷ t , at-head lemma-H0-S0-H0-H1-CZ)
  step-clifford2 (H0-gen ∷ S0-gen ∷ H0-gen ∷ S1-gen ∷ H1-gen ∷ CZ-gen ∷ t) = just (S0-gen ∷ H0-gen ∷ S1-gen ∷ H1-gen ∷ CZ-gen ∷ S0-gen ∷ H0-gen ∷ S0-gen ∷ S0-gen ∷ H0-gen ∷ S1-gen ∷ S1-gen ∷ t , at-head lemma-H0-S0-H0-S1-H1-CZ)
  
  step-clifford2 (S1-gen ∷ H1-gen ∷ CZ-gen ∷ H0-gen ∷ H1-gen ∷ CZ-gen ∷ t) = just (H1-gen ∷ CZ-gen ∷ H0-gen ∷ H1-gen ∷ CZ-gen ∷ H0-gen ∷ S0-gen ∷ H0-gen ∷ t , at-head lemma-S1-H1-CZ-H0-H1-CZ)
  step-clifford2 (S1-gen ∷ H1-gen ∷ CZ-gen ∷ S0-gen ∷ H0-gen ∷ H1-gen ∷ CZ-gen ∷ t) = just (H1-gen ∷ CZ-gen ∷ S0-gen ∷ H0-gen ∷ H1-gen ∷ CZ-gen ∷ H0-gen ∷ S0-gen ∷ H0-gen ∷ t , at-head lemma-S1-H1-CZ-S0-H0-H1-CZ)
  step-clifford2 (S0-gen ∷ H0-gen ∷ CZ-gen ∷ H0-gen ∷ H1-gen ∷ CZ-gen ∷ t) = just (H0-gen ∷ CZ-gen ∷ H0-gen ∷ H1-gen ∷ CZ-gen ∷ H1-gen ∷ S1-gen ∷ H1-gen ∷ t , at-head lemma-S0-H0-CZ-H0-H1-CZ)
  step-clifford2 (S0-gen ∷ H0-gen ∷ H1-gen ∷ CZ-gen ∷ H0-gen ∷ H1-gen ∷ CZ-gen ∷ t) = just (H0-gen ∷ H1-gen ∷ CZ-gen ∷ H0-gen ∷ H1-gen ∷ CZ-gen ∷ H1-gen ∷ S1-gen ∷ H1-gen ∷ t , at-head lemma-S0-H0-H1-CZ-H0-H1-CZ)
  step-clifford2 (S0-gen ∷ H0-gen ∷ CZ-gen ∷ H0-gen ∷ S1-gen ∷ H1-gen ∷ CZ-gen ∷ t) = just (H0-gen ∷ CZ-gen ∷ H0-gen ∷ S1-gen ∷ H1-gen ∷ CZ-gen ∷ H1-gen ∷ S1-gen ∷ H1-gen ∷ t , at-head lemma-S0-H0-CZ-H0-S1-H1-CZ)
  
  step-clifford2 (H1-gen ∷ CZ-gen ∷ H0-gen ∷ S1-gen ∷ H1-gen ∷ CZ-gen ∷ t) = just (CZ-gen ∷ H0-gen ∷ S1-gen ∷ H1-gen ∷ CZ-gen ∷ S0-gen ∷ S0-gen ∷ S0-gen ∷ H0-gen ∷ S0-gen ∷ H1-gen ∷ S1-gen ∷ S1-gen ∷ H1-gen ∷ t , at-head lemma-H1-CZ-H0-S1-H1-CZ)
  step-clifford2 (H1-gen ∷ CZ-gen ∷ S0-gen ∷ H0-gen ∷ S1-gen ∷ H1-gen ∷ CZ-gen ∷ t) = just (CZ-gen ∷ S0-gen ∷ H0-gen ∷ S1-gen ∷ H1-gen ∷ CZ-gen ∷ S0-gen ∷ S0-gen ∷ S0-gen ∷ H0-gen ∷ S0-gen ∷ H1-gen ∷ S1-gen ∷ S1-gen ∷ H1-gen ∷ t , at-head lemma-H1-CZ-S0-H0-S1-H1-CZ)
  step-clifford2 (H0-gen ∷ CZ-gen ∷ S0-gen ∷ H0-gen ∷ H1-gen ∷ CZ-gen ∷ t) = just (CZ-gen ∷ S0-gen ∷ H0-gen ∷ H1-gen ∷ CZ-gen ∷ H0-gen ∷ S0-gen ∷ S0-gen ∷ H0-gen ∷ S1-gen ∷ S1-gen ∷ S1-gen ∷ H1-gen ∷ S1-gen ∷ t , at-head lemma-H0-CZ-S0-H0-H1-CZ)
  step-clifford2 (H0-gen ∷ H1-gen ∷ CZ-gen ∷ S0-gen ∷ H0-gen ∷ H1-gen ∷ CZ-gen ∷ t) = just (H1-gen ∷ CZ-gen ∷ S0-gen ∷ H0-gen ∷ H1-gen ∷ CZ-gen ∷ H0-gen ∷ S0-gen ∷ S0-gen ∷ H0-gen ∷ S1-gen ∷ S1-gen ∷ S1-gen ∷ H1-gen ∷ S1-gen ∷ t , at-head lemma-H0-H1-CZ-S0-H0-H1-CZ)
  step-clifford2 (H0-gen ∷ CZ-gen ∷ S0-gen ∷ H0-gen ∷ S1-gen ∷ H1-gen ∷ CZ-gen ∷ t) = just (CZ-gen ∷ S0-gen ∷ H0-gen ∷ S1-gen ∷ H1-gen ∷ CZ-gen ∷ H0-gen ∷ S0-gen ∷ S0-gen ∷ H0-gen ∷ S1-gen ∷ S1-gen ∷ S1-gen ∷ H1-gen ∷ S1-gen ∷ t , at-head lemma-H0-CZ-S0-H0-S1-H1-CZ)
  
  step-clifford2 (CZ-gen ∷ H0-gen ∷ CZ-gen ∷ t) = just (S0-gen ∷ H0-gen ∷ CZ-gen ∷ S0-gen ∷ H0-gen ∷ S0-gen ∷ S1-gen ∷ t , at-head (axiom rel-CZ-H0-CZ))
  step-clifford2 (CZ-gen ∷ S0-gen ∷ H0-gen ∷ CZ-gen ∷ t) = just (S0-gen ∷ S0-gen ∷ H0-gen ∷ CZ-gen ∷ S0-gen ∷ H0-gen ∷ S0-gen ∷ S1-gen ∷ t , at-head lemma-CZ-S0-H0-CZ)
  step-clifford2 (CZ-gen ∷ H1-gen ∷ CZ-gen ∷ t) = just (S1-gen ∷ H1-gen ∷ CZ-gen ∷ S0-gen ∷ S1-gen ∷ H1-gen ∷ S1-gen ∷ t , at-head lemma-CZ-H1-CZ)
  step-clifford2 (CZ-gen ∷ S1-gen ∷ H1-gen ∷ CZ-gen ∷ t) = just (S1-gen ∷ S1-gen ∷ H1-gen ∷ CZ-gen ∷ S0-gen ∷ S1-gen ∷ H1-gen ∷ S1-gen ∷ t , at-head lemma-CZ-S1-H1-CZ)
  
  step-clifford2 (H1-gen ∷ CZ-gen ∷ H0-gen ∷ H1-gen ∷ CZ-gen ∷ H0-gen ∷ H1-gen ∷ CZ-gen ∷ t) = just (CZ-gen ∷ H0-gen ∷ H1-gen ∷ CZ-gen ∷ H0-gen ∷ H1-gen ∷ CZ-gen ∷ H0-gen ∷ t , at-head lemma-H1-CZ-H0-H1-CZ-H0-H1-CZ)
  step-clifford2 (H0-gen ∷ CZ-gen ∷ H0-gen ∷ H1-gen ∷ CZ-gen ∷ H0-gen ∷ H1-gen ∷ CZ-gen ∷ t) = just (CZ-gen ∷ H0-gen ∷ H1-gen ∷ CZ-gen ∷ H0-gen ∷ H1-gen ∷ CZ-gen ∷ H1-gen ∷ t , at-head lemma-H0-CZ-H0-H1-CZ-H0-H1-CZ)

  -- Catch-all
  step-clifford2 _ = nothing

  -- From this rewrite relation, we extract a tactic 'rewrite-clifford-aux'.
  open Rewriting.Step (step-cong step-order then step-cong step-clifford1 then step-cong step-clifford2) renaming (general-rewrite to rewrite-clifford-aux; multistep to clifford-multistep; lemma-multistep to lemma-clifford-multistep) public

  -- Finally, we take the new tactic, which is about the Clifford
  -- relations, and turn it into a tactic that works on Clifford+T
  -- relations. It works ≈⟨ ignoring T-generators. ⟩

  rewrite-clifford : (n : ℕ) -> {w u : Word Gen} -> clifford-multistep n (to-list w) ≡ clifford-multistep n (to-list u) -> w ≈ u
  rewrite-clifford n eq = (rewrite-clifford-aux n eq)


  -- We also instantiate the "rewrite-in-context" tactic from the
  -- Word-Tactics module to this rewrite system. Specifically,
  -- clifford-tactic can be used to apply Clifford rewriting to a
  -- subword inside a larger word, such as this:
  --
  -- property : X • Y • Z • A • B ≈ X • Y • Z • C • D • E
  -- property = clifford-tactic 3 2 100 auto
  --
  -- This applies 100 steps of Clifford rewriting to the subword A • B
  -- of the cleft-hand side (starting at position 3 and having length 2),
  -- and to the corresponding subword C • D • E of the cright-hand
  -- side, and checks whether a common normal form is reached.
  clifford-tactic : ∀ {s t pre post s2 t2} -> (n m k : ℕ) ->
             let s' = to-list2 s
                 t' = to-list2 t
                 m' = m + length t' - length s'
             in (mysplit n m s' , mysplit n m' t' , clifford-multistep k (to-list s2)) ≡ 
                ((pre , s2 , post) , (pre , t2 , post) , clifford-multistep k (to-list t2)) ->
                s ≈ t
  clifford-tactic = rewrite-in-context clifford-multistep lemma-clifford-multistep-inclusion
    where
      lemma-clifford-multistep-inclusion : (n : ℕ) (xs : List Gen) ->  from-list xs ≈ from-list (clifford-multistep n xs)
      lemma-clifford-multistep-inclusion n xs = (lemma-clifford-multistep n xs)

open Clifford-Rewriting using (rewrite-clifford) public

module Ex where

  data Gen : Set where
    H0-gen : Gen
    S0-gen : Gen
    H1-gen : Gen
    S1-gen : Gen
    Ex-gen : Gen

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

  Ex : Word Gen
  Ex = [ Ex-gen ]ʷ

  infix 4 _===_
  data _===_ : WRel Gen where
    order-S0 : S0 ^ 4 === ε
    order-H0 : H0 ^ 2 === ε
    order-S0H0 : (S0 • H0) ^ 3 === ε
    order-S1 : S1 ^ 4 === ε
    order-H1 : H1 ^ 2 === ε
    order-S1H1 : (S1 • H1) ^ 3 === ε

    comm-H0H1 : H0 • H1 === H1 • H0
    comm-H0S1 : H0 • S1 === S1 • H0
    comm-S0H1 : S0 • H1 === H1 • S0
    comm-S0S1 : S0 • S1 === S1 • S0

    order-Ex : Ex ^ 2 === ε
    comm-H0Ex : H0 • Ex === Ex • H1
    comm-S0Ex : S0 • Ex === Ex • S1


  open C1 renaming (module Clifford to C1)
  
  GenM = C1.Gen ⊎ C1.Gen
  infix 4 _===ₘ_
  _===ₘ_ = (C1._===_ ⸲ C1._===_ ⸲ Γₓ)
  
  M-nfp' : NFProperty' _===ₘ_
  M-nfp' = DP.NFP'.nfp' C1._===_ C1._===_ C1.Iso.clifford-nfp' C1.Iso.clifford-nfp'

  open PB _===ₘ_ using () renaming (_≈_ to _≈₁_ ; _===_ to _===₁_)-- ; refl to refl₁ ; axiom to axiom₁ ; left-unit to left-unit₁)
  open PP _===ₘ_ renaming (by-assoc to by-assoc₁ ; by-assoc-and to by-assoc-and₁) using ()

  open PB _===_ using () renaming (_≈_ to _≈₂_ ; _===_ to _===₂_)
  open PP _===_ using (by-assoc) renaming (word-setoid to ws₂)

  open PB hiding (_===_)


  lemma-comm-ExH1 : H1 • Ex ≈₂ Ex • H0
  lemma-comm-ExH1 = begin
    H1 • Ex ≈⟨ trans (sym left-unit) (_≈₂_.cong (_≈₂_.sym (_≈₂_.axiom order-Ex)) _≈₂_.refl) ⟩
    Ex ^ 2 • H1 • Ex ≈⟨ by-assoc Eq.refl ⟩
    Ex • (Ex • H1) • Ex ≈⟨ cong refl (_≈₂_.cong (_≈₂_.sym (_≈₂_.axiom comm-H0Ex)) _≈₂_.refl) ⟩
    Ex • (H0 • Ex) • Ex ≈⟨ by-assoc Eq.refl ⟩
    (Ex • H0) • Ex ^ 2 ≈⟨ trans (_≈₂_.cong _≈₂_.refl (_≈₂_.axiom order-Ex)) right-unit ⟩
    Ex • H0 ∎
    where open SR ws₂

  lemma-comm-ExS1 : S1 • Ex ≈₂ Ex • S0
  lemma-comm-ExS1 = begin
    S1 • Ex ≈⟨ trans (sym left-unit) (_≈₂_.cong (_≈₂_.sym (_≈₂_.axiom order-Ex)) _≈₂_.refl) ⟩
    Ex ^ 2 • S1 • Ex ≈⟨ by-assoc Eq.refl ⟩
    Ex • (Ex • S1) • Ex ≈⟨ cong refl (_≈₂_.cong (_≈₂_.sym (_≈₂_.axiom comm-S0Ex)) _≈₂_.refl) ⟩
    Ex • (S0 • Ex) • Ex ≈⟨ by-assoc Eq.refl ⟩
    (Ex • S0) • Ex ^ 2 ≈⟨ trans (_≈₂_.cong _≈₂_.refl (_≈₂_.axiom order-Ex)) right-unit ⟩
    Ex • S0 ∎
    where open SR ws₂

  open import Presentation.CosetNF

  data C : Set where
    cEx : C

  pattern •ε = inj₂ tt
  pattern •Ex = inj₁ cEx

  I : C ⊎ ⊤
  I = •ε
  
  f : GenM → Word Gen
  f (inj₁ C1.H-gen) = H0
  f (inj₁ C1.S-gen) = S0
  f (inj₂ C1.H-gen) = H1
  f (inj₂ C1.S-gen) = S1

  h : C ⊎ ⊤ → Gen → Word GenM × (C ⊎ ⊤)
  h •Ex H0-gen = [ C1.H ]ᵣ , •Ex
  h •Ex S0-gen = [ C1.S ]ᵣ , •Ex
  h •Ex H1-gen = [ C1.H ]ₗ , •Ex
  h •Ex S1-gen = [ C1.S ]ₗ , •Ex
  h •Ex Ex-gen = ε , •ε
  h •ε H0-gen = [ C1.H ]ₗ , •ε
  h •ε S0-gen = [ C1.S ]ₗ , •ε
  h •ε H1-gen = [ C1.H ]ᵣ , •ε
  h •ε S1-gen = [ C1.S ]ᵣ , •ε
  h •ε Ex-gen = ε , •Ex

  [_]ₒ : C → Word Gen
  [ cEx ]ₒ = Ex

  hcme : ∀ c m -> ∃ \ w -> ∃ \ c' -> ((h **) (inj₁ c) (f m)) ≡ (w , inj₁ c')
  hcme cEx (inj₁ C1.H-gen) = [ C1.H ]ᵣ , cEx , Eq.refl
  hcme cEx (inj₁ C1.S-gen) = [ C1.S ]ᵣ , cEx , Eq.refl
  hcme cEx (inj₂ C1.H-gen) = [ C1.H ]ₗ , cEx , Eq.refl
  hcme cEx (inj₂ C1.S-gen) = [ C1.S ]ₗ , cEx , Eq.refl
  
  htme : ∀ m -> ((h **) (inj₂ tt) (f m)) ≡ ([ m ]ʷ , inj₂ tt)
  htme (inj₁ C1.H-gen) = Eq.refl
  htme (inj₁ C1.S-gen) = Eq.refl
  htme (inj₂ C1.H-gen) = Eq.refl
  htme (inj₂ C1.S-gen) = Eq.refl

  infix 4 _~_
  _~_ = PW.Pointwise _≈₁_ (_≡_ {A = C ⊎ ⊤})

  htme~ : ∀ (m : GenM) -> ([ m ]ʷ , I) ~ ((h **) I (f m))
  htme~ (inj₁ C1.H-gen) = refl , Eq.refl
  htme~ (inj₁ C1.S-gen) = refl , Eq.refl
  htme~ (inj₂ C1.H-gen) = refl , Eq.refl
  htme~ (inj₂ C1.S-gen) = refl , Eq.refl

  [_]ₓ = f *

  hcme~ : ∀ (c : C) (m : GenM) -> let (w' , c' , p) = hcme c m in [ c ]ₒ • f m ≈₂ [ w' ]ₓ • [ c' ]ₒ 
  hcme~ cEx (inj₁ C1.H-gen) = _≈₂_.sym lemma-comm-ExH1
  hcme~ cEx (inj₁ C1.S-gen) = _≈₂_.sym lemma-comm-ExS1
  hcme~ cEx (inj₂ C1.H-gen) = sym (axiom comm-H0Ex)
  hcme~ cEx (inj₂ C1.S-gen) = _≈₂_.sym (_≈₂_.axiom comm-S0Ex)
  
  h-wd-ax : ∀ (c : C ⊎ ⊤){u t : Word Gen} -> u ===₂ t -> ((h **) c u) ~ ((h **) c t)
  h-wd-ax •Ex {u} {t} order-S0 = axiom (right C1.order-S) , Eq.refl
  h-wd-ax •Ex {u} {t} order-H0 = axiom (right C1.order-H) , Eq.refl
  h-wd-ax •Ex {u} {t} order-S0H0 = axiom (right C1.order-SH) , Eq.refl
  h-wd-ax •Ex {u} {t} order-S1 = axiom (left C1.order-S) , Eq.refl
  h-wd-ax •Ex {u} {t} order-H1 = axiom (left C1.order-H) , Eq.refl
  h-wd-ax •Ex {u} {t} order-S1H1 = axiom (left C1.order-SH) , Eq.refl
  h-wd-ax •Ex {u} {t} order-Ex = left-unit , Eq.refl
  h-wd-ax •Ex {u} {t} comm-H0Ex = trans right-unit (sym left-unit) , Eq.refl
  h-wd-ax •Ex {u} {t} comm-S0Ex = trans right-unit (sym left-unit) , Eq.refl
  h-wd-ax •ε {u} {t} order-S0 = axiom (left C1.order-S) , Eq.refl
  h-wd-ax •ε {u} {t} order-H0 = axiom (left C1.order-H) , Eq.refl
  h-wd-ax •ε {u} {t} order-S0H0 = axiom (left C1.order-SH) , Eq.refl
  h-wd-ax •ε {u} {t} order-S1 = axiom (right C1.order-S) , Eq.refl
  h-wd-ax •ε {u} {t} order-H1 = axiom (right C1.order-H) , Eq.refl
  h-wd-ax •ε {u} {t} order-S1H1 = axiom (right C1.order-SH) , Eq.refl
  h-wd-ax •ε {u} {t} order-Ex = left-unit , Eq.refl
  h-wd-ax •ε {u} {t} comm-H0Ex = trans right-unit (sym left-unit) , Eq.refl
  h-wd-ax •ε {u} {t} comm-S0Ex = trans right-unit (sym left-unit) , Eq.refl
  h-wd-ax •Ex comm-H0H1 = sym (axiom (mid (comm C1.H-gen C1.H-gen))) , Eq.refl 
  h-wd-ax •Ex comm-H0S1 = sym (axiom (mid (comm C1.S-gen C1.H-gen))) , Eq.refl 
  h-wd-ax •Ex comm-S0H1 = sym (axiom (mid (comm C1.H-gen C1.S-gen))) , Eq.refl  
  h-wd-ax •Ex comm-S0S1 = sym (axiom (mid (comm C1.S-gen C1.S-gen))) , Eq.refl  
  h-wd-ax •ε comm-H0H1 = axiom (mid (comm C1.H-gen C1.H-gen)) , Eq.refl  
  h-wd-ax •ε comm-H0S1 = axiom (mid (comm C1.H-gen C1.S-gen)) , Eq.refl  
  h-wd-ax •ε comm-S0H1 = axiom (mid (comm C1.S-gen C1.H-gen)) , Eq.refl  
  h-wd-ax •ε comm-S0S1 = axiom (mid (comm C1.S-gen C1.S-gen)) , Eq.refl
  
  f-wd-ax : ∀ {w v} -> w ===₁ v -> (f *) w ≈₂ (f *) v
  f-wd-ax {w} {v} (left C1.order-S) = axiom order-S0
  f-wd-ax {w} {v} (left C1.order-H) = axiom order-H0
  f-wd-ax {w} {v} (left C1.order-SH) = axiom order-S0H0
  f-wd-ax {w} {v} (right C1.order-S) = axiom order-S1
  f-wd-ax {w} {v} (right C1.order-H) = axiom order-H1
  f-wd-ax {w} {v} (right C1.order-SH) = axiom order-S1H1
  f-wd-ax {w} {v} (mid (comm C1.H-gen C1.H-gen)) = axiom comm-H0H1
  f-wd-ax {w} {v} (mid (comm C1.H-gen C1.S-gen)) = axiom comm-H0S1
  f-wd-ax {w} {v} (mid (comm C1.S-gen C1.H-gen)) = axiom comm-S0H1
  f-wd-ax {w} {v} (mid (comm C1.S-gen C1.S-gen)) = axiom comm-S0S1

  [_] : C ⊎ ⊤ -> Word Gen
  [_] = [_,_] [_]ₒ (λ v → ε)

  h=ract :  ∀ c y -> let (m' , c') = h c y in
   ([ c ] • [ y ]ʷ) ≈₂ ([ m' ]ₓ • [ c' ])
  h=ract •Ex H0-gen = sym lemma-comm-ExH1
  h=ract •Ex S0-gen = sym lemma-comm-ExS1
  h=ract •Ex H1-gen = sym (axiom comm-H0Ex)
  h=ract •Ex S1-gen = sym (axiom comm-S0Ex)
  h=ract •Ex Ex-gen = trans (axiom order-Ex) (sym right-unit)
  h=ract •ε H0-gen = trans left-unit (sym right-unit)
  h=ract •ε S0-gen = trans left-unit (sym right-unit)
  h=ract •ε H1-gen = trans left-unit (sym right-unit)
  h=ract •ε S1-gen = trans left-unit (sym right-unit)
  h=ract •ε Ex-gen = refl

  assump : CosetNF-CT-Assumptions-And-Theorems-Packed _===ₘ_ _===_
  assump = record
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
            ; h=ract = h=ract
            }

  open CosetNF-CT-Assumptions-And-Theorems-Packed assump
  
  ExM-nfp' : NFProperty' _===_
  ExM-nfp' = nfp' M-nfp'


{-
module Clifford where

  data Gen : Set where
    H0-gen : Gen
    S0-gen : Gen
    H1-gen : Gen
    S1-gen : Gen
    CZ-gen : Gen

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

  Ex : Word Gen
  Ex = CX • XC • CX

  Ex' : Word Gen
  Ex' = XC • CX • XC
  
  infix 4 _===_
  data _===_ : WRel Gen where
    order-S0 : S0 ^ 4 === ε
    order-H0 : H0 ^ 2 === ε
    order-S0H0 : (S0 • H0) ^ 3 === ε
    order-S1 : S1 ^ 4 === ε
    order-H1 : H1 ^ 2 === ε
    order-S1H1 : (S1 • H1) ^ 3 === ε
    
    comm-H0H1 : H0 • H1 === H1 • H0
    comm-H0S1 : H0 • S1 === S1 • H0
    comm-S0H1 : S0 • H1 === H1 • S0
    comm-S0S1 : S0 • S1 === S1 • S0

    order-CZ : CZ ^ 2 === ε
    comm-S0-CZ : S0 • CZ === CZ • S0
    comm-S1-CZ : S1 • CZ === CZ • S1
    rel-X0-CZ : X0 • CZ === CZ • Z1 • X0
    rel-X1-CZ : X1 • CZ === CZ • Z0 • X1
    rel-CZ-H0-CZ : CZ • H0 • CZ === S0 • H0 • CZ • S0 • H0 • S0 • S1
    rel-CZ-H1-CZ : CZ • H1 • CZ === S1 • H1 • CZ • S1 • H1 • S1 • S0
-}

{-
module C2 where
  open import Presentation.Groups.Clifford-Lemmas
  open Clifford
  
  GenM = Ex.Gen
  infix 4 _===ₘ_
  _===ₘ_ = Ex._===_
  
  ExM-nfp' = Ex.ExM-nfp'

  open PB _===ₘ_ using () renaming (_≈_ to _≈₁_ ; _===_ to _===₁_)-- ; refl to refl₁ ; axiom to axiom₁ ; left-unit to left-unit₁)
  open PP _===ₘ_ renaming (by-assoc to by-assoc₁ ; by-assoc-and to by-assoc-and₁ ; word-setoid to ws₁) using ()

  open PB _===_ using () renaming (_≈_ to _≈₂_ ; _===_ to _===₂_)
  open PP _===_ using (by-assoc ; by-assoc-and) renaming (word-setoid to ws₂)

  open PB hiding (_===_)

  open import Data.Maybe
  open import Data.Bool
  import Data.Nat as Nat
  
  module Comm where

    -- Commutativity.
    comm~ : (x y : Gen) -> Maybe (([ x ]ʷ • [ y ]ʷ) ≈₂ ([ y ]ʷ • [ x ]ʷ))
    comm~ H0-gen H1-gen = just (_≈₂_.axiom comm-H0H1)
    comm~ H0-gen S1-gen = just (_≈₂_.axiom comm-H0S1)
    comm~ S0-gen H1-gen = just (_≈₂_.axiom comm-S0H1)
    comm~ S0-gen S1-gen = just (_≈₂_.axiom comm-S0S1)

    comm~ H1-gen H0-gen = just (_≈₂_.sym (_≈₂_.axiom comm-H0H1))
    comm~ H1-gen S0-gen = just (_≈₂_.sym (_≈₂_.axiom comm-S0H1))
    comm~ S1-gen H0-gen = just (_≈₂_.sym (_≈₂_.axiom comm-H0S1))
    comm~ S1-gen S0-gen = just (_≈₂_.sym (_≈₂_.axiom comm-S0S1))

    comm~ S0-gen CZ-gen = just (_≈₂_.axiom comm-S0-CZ)
    comm~ S1-gen CZ-gen = just (_≈₂_.axiom comm-S1-CZ)
    comm~ CZ-gen S0-gen = just (_≈₂_.sym (_≈₂_.axiom comm-S0-CZ))
    comm~ CZ-gen S1-gen = just (_≈₂_.sym (_≈₂_.axiom comm-S1-CZ))
    comm~ _ _ = nothing


    -- We number the generators for the purpose of ordering them.
    ord : Gen -> ℕ
    ord S0-gen = 0
    ord S1-gen = 1
    ord H0-gen = 2
    ord H1-gen = 3
    ord CZ-gen = 4

    -- Ordering of generators.
    les : Gen -> Gen -> Bool
    les x y with ord x Nat.<? ord y
    les x y | yes _ = true
    les x y | no _ = false

  open import Presentation.CosetNF

  data C : Set where
    cCZ : C
    cCZH0 : C
    cCZH0S0 : C
    cCZH1 : C
    cCZH1S1 : C
    cCZH0H1 : C
    cCZH0H1S0 : C
    cCZH0H1S1 : C
    cCZH0H1S0S1 : C

  pattern •ε = inj₂ tt
  pattern •CZ = inj₁ cCZ
  pattern •CZH0 = inj₁ cCZH0
  pattern •CZH0S0 = inj₁ cCZH0S0
  pattern •CZH1 = inj₁ cCZH1
  pattern •CZH1S1 = inj₁ cCZH1S1
  pattern •CZH0H1 = inj₁ cCZH0H1
  pattern •CZH0H1S0 = inj₁ cCZH0H1S0
  pattern •CZH0H1S1 = inj₁ cCZH0H1S1
  pattern •CZH0H1S0S1 = inj₁ cCZH0H1S0S1

  I : C ⊎ ⊤
  I = •ε
  
  f : GenM → Word Gen
  f Ex.H0-gen = H0
  f Ex.S0-gen = S0
  f Ex.H1-gen = H1
  f Ex.S1-gen = S1
  f Ex.Ex-gen = Ex


  h : C ⊎ ⊤ → Gen → Word GenM × (C ⊎ ⊤)
  h •ε S0-gen = Ex.S0 , •ε
  h •CZ S0-gen = Ex.S0 , •CZ
  h •CZH0 S0-gen = ε , •CZH0S0
  h •CZH1 S0-gen = Ex.S0 , •CZH1
  h •CZH0S0 S0-gen = Ex.X0 • Ex.Z1 , •CZH0
  h •CZH0H1 S0-gen = ε , •CZH0H1S0
  h •CZH1S1 S0-gen = Ex.S0 , •CZH1S1
  h •CZH0H1S0 S0-gen = Ex.X0 • Ex.Z1 , •CZH0H1
  h •CZH0H1S1 S0-gen = ε , •CZH0H1S0S1
  h •CZH0H1S0S1 S0-gen = Ex.X0 • Ex.Z1 , •CZH0H1S1
  h •ε H0-gen = Ex.H0 , •ε
  h •CZ H0-gen = ε , •CZH0
  h •CZH0 H0-gen = ε , •CZ
  h •CZH1 H0-gen = ε , •CZH0H1
  h •CZH0S0 H0-gen = Ex.X0 • Ex.S0 • Ex.Z1 , •CZH0S0
  h •CZH0H1 H0-gen = ε , •CZH1
  h •CZH1S1 H0-gen = ε , •CZH0H1S1
  h •CZH0H1S0 H0-gen = Ex.X0 • Ex.S0 • Ex.Z1 , •CZH0H1S0
  h •CZH0H1S1 H0-gen = ε , •CZH1S1
  h •CZH0H1S0S1 H0-gen = Ex.X0 • Ex.S0 • Ex.Z1 , •CZH0H1S0S1
  h •ε S1-gen = Ex.S1 , •ε
  h •CZ S1-gen = Ex.S1 , •CZ
  h •CZH0 S1-gen = Ex.S1 , •CZH0
  h •CZH1 S1-gen = ε , •CZH1S1
  h •CZH0S0 S1-gen = Ex.S1 , •CZH0S0
  h •CZH0H1 S1-gen = ε , •CZH0H1S1
  h •CZH1S1 S1-gen = Ex.Z0 • Ex.X1 , •CZH1
  h •CZH0H1S0 S1-gen = ε , •CZH0H1S0S1
  h •CZH0H1S1 S1-gen = Ex.Z0 • Ex.X1 , •CZH0H1
  h •CZH0H1S0S1 S1-gen = Ex.Z0 • Ex.X1 , •CZH0H1S0
  h •ε H1-gen = Ex.H1 , •ε
  h •CZ H1-gen = ε , •CZH1
  h •CZH0 H1-gen = ε , •CZH0H1
  h •CZH1 H1-gen = ε , •CZ
  h •CZH0S0 H1-gen = ε , •CZH0H1S0
  h •CZH0H1 H1-gen = ε , •CZH0
  h •CZH1S1 H1-gen = Ex.Z0 • Ex.X1 • Ex.S1 , •CZH1S1
  h •CZH0H1S0 H1-gen = ε , •CZH0S0
  h •CZH0H1S1 H1-gen = Ex.Z0 • Ex.X1 • Ex.S1 , •CZH0H1S1
  h •CZH0H1S0S1 H1-gen = Ex.Z0 • Ex.X1 • Ex.S1 , •CZH0H1S0S1
  h •ε CZ-gen = ε , •CZ
  h •CZ CZ-gen = ε , •ε
  h •CZH0 CZ-gen = Ex.S0 • Ex.H0 • Ex.S0 • Ex.S1 , •CZH0S0
  h •CZH1 CZ-gen = Ex.S0 • Ex.S1 • Ex.H1 • Ex.S1 , •CZH1S1
  h •CZH0S0 CZ-gen = Ex.X0 • Ex.S0 • Ex.H0 • Ex.S0 • Ex.Z1 • Ex.S1 , •CZH0
  h •CZH0H1 CZ-gen = Ex.H0 • Ex.H1 • Ex.Ex , •CZH0H1
  h •CZH1S1 CZ-gen = Ex.Z0 • Ex.S0 • Ex.X1 • Ex.S1 • Ex.H1 • Ex.S1 , •CZH1
  h •CZH0H1S0 CZ-gen = Ex.H0 • Ex.H1 • Ex.Ex , •CZH0H1S0
  h •CZH0H1S1 CZ-gen = Ex.H0 • Ex.H1 • Ex.Ex , •CZH0H1S1
  h •CZH0H1S0S1 CZ-gen = Ex.H0 • Ex.H1 • Ex.Ex , •CZH0H1S0S1

  [_]ₒ : C → Word Gen
  [ cCZ ]ₒ = CZ
  [ cCZH0 ]ₒ = CZ • H0
  [ cCZH0S0 ]ₒ = CZ • H0 • S0
  [ cCZH1 ]ₒ = CZ • H1
  [ cCZH1S1 ]ₒ = CZ • H1 • S1
  [ cCZH0H1 ]ₒ = CZ • H0 • H1
  [ cCZH0H1S0 ]ₒ = CZ • H0 • H1 • S0
  [ cCZH0H1S1 ]ₒ = CZ • H0 • H1 • S1
  [ cCZH0H1S0S1 ]ₒ = CZ • H0 • H1 • S0 • S1

  infix 4 _~_
  _~_ = PW.Pointwise _≈₁_ (_≡_ {A = C ⊎ ⊤})

  [_]ₓ = f *


  hcme : ∀ c m -> ∃ \ w -> ∃ \ c' -> ((h **) (inj₁ c) (f m)) ≡ (w , inj₁ c')
  hcme cCZ Ex.H0-gen = ε , cCZH0 , Eq.refl
  hcme cCZ Ex.S0-gen = Ex.S0 , cCZ , Eq.refl
  hcme cCZ Ex.H1-gen = ε , cCZH1 , Eq.refl
  hcme cCZ Ex.S1-gen = Ex.S1 , cCZ , Eq.refl
  hcme cCZ Ex.Ex-gen = (h **) •CZ CX .proj₁ •
                        (h **) ((h **) •CZ CX .proj₂) (XC • CX) .proj₁
                        , cCZ , Eq.refl
  hcme cCZH0 Ex.H0-gen = ε , cCZ , Eq.refl
  hcme cCZH0 Ex.S0-gen = ε , cCZH0S0 , Eq.refl
  hcme cCZH0 Ex.H1-gen = ε , cCZH0H1 , Eq.refl
  hcme cCZH0 Ex.S1-gen = Ex.S1 , cCZH0 , Eq.refl
  hcme cCZH0 Ex.Ex-gen = (h **) •CZH0 CX .proj₁ •
                          (h **) ((h **) •CZH0 CX .proj₂) (XC • CX) .proj₁
                          , cCZH1 , Eq.refl
  hcme cCZH0S0 Ex.H0-gen = Ex.X0 • Ex.S0 • Ex.Z1 , cCZH0S0 , Eq.refl
  hcme cCZH0S0 Ex.S0-gen = Ex.X0 • Ex.Z1 , cCZH0 , Eq.refl
  hcme cCZH0S0 Ex.H1-gen = ε , cCZH0H1S0 , Eq.refl
  hcme cCZH0S0 Ex.S1-gen = Ex.S1 , cCZH0S0 , Eq.refl
  hcme cCZH0S0 Ex.Ex-gen = (h **) •CZH0S0 CX .proj₁ •
                            (h **) ((h **) •CZH0S0 CX .proj₂) (XC • CX) .proj₁
                            , cCZH1S1 , Eq.refl
  hcme cCZH1 Ex.H0-gen = ε , cCZH0H1 , Eq.refl
  hcme cCZH1 Ex.S0-gen = Ex.S0 , cCZH1 , Eq.refl
  hcme cCZH1 Ex.H1-gen = ε , cCZ , Eq.refl
  hcme cCZH1 Ex.S1-gen = ε , cCZH1S1 , Eq.refl
  hcme cCZH1 Ex.Ex-gen = (h **) •CZH1 CX .proj₁ •
                          (h **) ((h **) •CZH1 CX .proj₂) (XC • CX) .proj₁
                          , cCZH0 , Eq.refl
  hcme cCZH1S1 Ex.H0-gen = ε , cCZH0H1S1 , Eq.refl
  hcme cCZH1S1 Ex.S0-gen = Ex.S0 , cCZH1S1 , Eq.refl
  hcme cCZH1S1 Ex.H1-gen = Ex.Z0 • Ex.X1 • Ex.S1 , cCZH1S1 , Eq.refl
  hcme cCZH1S1 Ex.S1-gen = Ex.Z0 • Ex.X1 , cCZH1 , Eq.refl
  hcme cCZH1S1 Ex.Ex-gen = (h **) •CZH1S1 CX .proj₁ •
                            (h **) ((h **) •CZH1S1 CX .proj₂) (XC • CX) .proj₁
                            , cCZH0S0 , Eq.refl
  hcme cCZH0H1 Ex.H0-gen = ε , cCZH1 , Eq.refl
  hcme cCZH0H1 Ex.S0-gen = ε , cCZH0H1S0 , Eq.refl
  hcme cCZH0H1 Ex.H1-gen = ε , cCZH0 , Eq.refl
  hcme cCZH0H1 Ex.S1-gen = ε , cCZH0H1S1 , Eq.refl
  hcme cCZH0H1 Ex.Ex-gen = (h **) •CZH0H1 CX .proj₁ •
                            (h **) ((h **) •CZH0H1 CX .proj₂) (XC • CX) .proj₁
                            , cCZH0H1 , Eq.refl
  hcme cCZH0H1S0 Ex.H0-gen = Ex.X0 • Ex.S0 • Ex.Z1 , cCZH0H1S0 , Eq.refl
  hcme cCZH0H1S0 Ex.S0-gen = Ex.X0 • Ex.Z1 , cCZH0H1 , Eq.refl
  hcme cCZH0H1S0 Ex.H1-gen = ε , cCZH0S0 , Eq.refl
  hcme cCZH0H1S0 Ex.S1-gen = ε , cCZH0H1S0S1 , Eq.refl
  hcme cCZH0H1S0 Ex.Ex-gen = (h **) •CZH0H1S0 CX .proj₁ •
                              (h **) ((h **) •CZH0H1S0 CX .proj₂) (XC • CX) .proj₁
                              , cCZH0H1S1 , Eq.refl
  hcme cCZH0H1S1 Ex.H0-gen = ε , cCZH1S1 , Eq.refl
  hcme cCZH0H1S1 Ex.S0-gen = ε , cCZH0H1S0S1 , Eq.refl
  hcme cCZH0H1S1 Ex.H1-gen = Ex.Z0 • Ex.X1 • Ex.S1 , cCZH0H1S1 , Eq.refl
  hcme cCZH0H1S1 Ex.S1-gen = Ex.Z0 • Ex.X1 , cCZH0H1 , Eq.refl
  hcme cCZH0H1S1 Ex.Ex-gen = (h **) •CZH0H1S1 CX .proj₁ •
                              (h **) ((h **) •CZH0H1S1 CX .proj₂) (XC • CX) .proj₁
                              , cCZH0H1S0 , Eq.refl
  hcme cCZH0H1S0S1 Ex.H0-gen = Ex.X0 • Ex.S0 • Ex.Z1 , cCZH0H1S0S1 , Eq.refl
  hcme cCZH0H1S0S1 Ex.S0-gen = Ex.X0 • Ex.Z1 , cCZH0H1S1 , Eq.refl
  hcme cCZH0H1S0S1 Ex.H1-gen = Ex.Z0 • Ex.X1 • Ex.S1 , cCZH0H1S0S1 , Eq.refl
  hcme cCZH0H1S0S1 Ex.S1-gen = Ex.Z0 • Ex.X1 , cCZH0H1S0 , Eq.refl
  hcme cCZH0H1S0S1 Ex.Ex-gen = (h **) •CZH0H1S0S1 CX .proj₁ •
                                (h **) ((h **) •CZH0H1S0S1 CX .proj₂) (XC • CX) .proj₁
                                , cCZH0H1S0S1 , Eq.refl
  

  htme~ : ∀ (m : GenM) -> ([ m ]ʷ , I) ~ ((h **) I (f m))
  htme~ Ex.H0-gen = refl , Eq.refl
  htme~ Ex.S0-gen = refl , Eq.refl
  htme~ Ex.H1-gen = refl , Eq.refl
  htme~ Ex.S1-gen = refl , Eq.refl
  htme~ Ex.Ex-gen = sym claim , Eq.refl
    where
    open SR ws₁
    claim : (h **) •ε (CX • XC • CX) .proj₁ ≈₁ Ex.Ex
    claim = begin
      (h **) •ε (CX • XC • CX) .proj₁ ≈⟨ by-assoc₁ Eq.refl ⟩
      Ex.H1 • (Ex.H0 • Ex.H1) • (Ex.Ex • Ex.H1) ≈⟨ cong refl (cong (axiom Ex.comm-H0H1)
                                                               (sym (axiom Ex.comm-H0Ex))) ⟩
      Ex.H1 • (Ex.H1 • Ex.H0) • (Ex.H0 • Ex.Ex) ≈⟨ by-assoc₁ Eq.refl ⟩
      Ex.H1 ^ 2 • Ex.H0 ^ 2 • Ex.Ex ≈⟨ cong (axiom Ex.order-H1) (cong (axiom Ex.order-H0) refl) ⟩
      ε • ε • Ex.Ex ≈⟨ trans left-unit left-unit ⟩
      Ex.Ex ∎


  hcme~ : ∀ (c : C) (m : GenM) -> let (w' , c' , p) = hcme c m in [ c ]ₒ • f m ≈₂ [ w' ]ₓ • [ c' ]ₒ 
  hcme~ cCZ Ex.H0-gen = rewrite-clifford 100 Eq.refl
  hcme~ cCZ Ex.S0-gen = rewrite-clifford 100 Eq.refl
  hcme~ cCZ Ex.H1-gen = rewrite-clifford 100 Eq.refl
  hcme~ cCZ Ex.S1-gen = rewrite-clifford 100 Eq.refl
  hcme~ cCZ Ex.Ex-gen = rewrite-clifford 200 Eq.refl
  hcme~ cCZH0 Ex.H0-gen = rewrite-clifford 100 Eq.refl
  hcme~ cCZH0 Ex.S0-gen = rewrite-clifford 100 Eq.refl
  hcme~ cCZH0 Ex.H1-gen = rewrite-clifford 100 Eq.refl
  hcme~ cCZH0 Ex.S1-gen = rewrite-clifford 100 Eq.refl
  hcme~ cCZH0 Ex.Ex-gen = rewrite-clifford 100 Eq.refl
  hcme~ cCZH0S0 Ex.H0-gen = rewrite-clifford 100 Eq.refl
  hcme~ cCZH0S0 Ex.S0-gen = rewrite-clifford 100 Eq.refl
  hcme~ cCZH0S0 Ex.H1-gen = rewrite-clifford 100 Eq.refl
  hcme~ cCZH0S0 Ex.S1-gen = rewrite-clifford 100 Eq.refl
  hcme~ cCZH0S0 Ex.Ex-gen = rewrite-clifford 200 Eq.refl
  hcme~ cCZH1 Ex.H0-gen = rewrite-clifford 100 Eq.refl
  hcme~ cCZH1 Ex.S0-gen = rewrite-clifford 100 Eq.refl
  hcme~ cCZH1 Ex.H1-gen = rewrite-clifford 100 Eq.refl
  hcme~ cCZH1 Ex.S1-gen = rewrite-clifford 100 Eq.refl
  hcme~ cCZH1 Ex.Ex-gen = rewrite-clifford 100 Eq.refl
  hcme~ cCZH1S1 Ex.H0-gen = rewrite-clifford 100 Eq.refl
  hcme~ cCZH1S1 Ex.S0-gen = rewrite-clifford 100 Eq.refl
  hcme~ cCZH1S1 Ex.H1-gen = rewrite-clifford 100 Eq.refl
  hcme~ cCZH1S1 Ex.S1-gen = rewrite-clifford 100 Eq.refl
  hcme~ cCZH1S1 Ex.Ex-gen = rewrite-clifford 400 Eq.refl
  hcme~ cCZH0H1 Ex.H0-gen = rewrite-clifford 100 Eq.refl
  hcme~ cCZH0H1 Ex.S0-gen = rewrite-clifford 100 Eq.refl
  hcme~ cCZH0H1 Ex.H1-gen = rewrite-clifford 100 Eq.refl
  hcme~ cCZH0H1 Ex.S1-gen = rewrite-clifford 100 Eq.refl
  hcme~ cCZH0H1 Ex.Ex-gen = rewrite-clifford 200 Eq.refl
  hcme~ cCZH0H1S0 Ex.H0-gen = rewrite-clifford 100 Eq.refl
  hcme~ cCZH0H1S0 Ex.S0-gen = rewrite-clifford 100 Eq.refl
  hcme~ cCZH0H1S0 Ex.H1-gen = rewrite-clifford 100 Eq.refl
  hcme~ cCZH0H1S0 Ex.S1-gen = rewrite-clifford 100 Eq.refl
  hcme~ cCZH0H1S0 Ex.Ex-gen = rewrite-clifford 200 Eq.refl
  hcme~ cCZH0H1S1 Ex.H0-gen = rewrite-clifford 100 Eq.refl
  hcme~ cCZH0H1S1 Ex.S0-gen = rewrite-clifford 100 Eq.refl
  hcme~ cCZH0H1S1 Ex.H1-gen = rewrite-clifford 100 Eq.refl
  hcme~ cCZH0H1S1 Ex.S1-gen = rewrite-clifford 100 Eq.refl
  hcme~ cCZH0H1S1 Ex.Ex-gen = rewrite-clifford 400 Eq.refl
  hcme~ cCZH0H1S0S1 Ex.H0-gen = rewrite-clifford 100 Eq.refl
  hcme~ cCZH0H1S0S1 Ex.S0-gen = rewrite-clifford 100 Eq.refl
  hcme~ cCZH0H1S0S1 Ex.H1-gen = rewrite-clifford 100 Eq.refl
  hcme~ cCZH0H1S0S1 Ex.S1-gen = rewrite-clifford 100 Eq.refl
  hcme~ cCZH0H1S0S1 Ex.Ex-gen = rewrite-clifford 400 Eq.refl

  open NFProperty' ExM-nfp'
  
  h-wd-ax : ∀ (c : C ⊎ ⊤){u t : Word Gen} -> u ===₂ t -> ((h **) c u) ~ ((h **) c t)
  h-wd-ax •CZ {u} {t} order-S0 = axiom Ex.order-S0 , Eq.refl
  h-wd-ax •CZH0 {u} {t} order-S0 = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax •CZH0S0 {u} {t} order-S0 = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax •CZH1 {u} {t} order-S0 = axiom Ex.order-S0 , Eq.refl
  h-wd-ax •CZH1S1 {u} {t} order-S0 = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax •CZH0H1 {u} {t} order-S0 = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax •CZH0H1S0 {u} {t} order-S0 = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax •CZH0H1S1 {u} {t} order-S0 = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax •CZH0H1S0S1 {u} {t} order-S0 = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax •CZ {u} {t} order-H0 = left-unit , Eq.refl
  h-wd-ax •CZH0 {u} {t} order-H0 = left-unit , Eq.refl
  h-wd-ax •CZH0S0 {u} {t} order-H0 = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax •CZH1 {u} {t} order-H0 = left-unit , Eq.refl
  h-wd-ax •CZH1S1 {u} {t} order-H0 = left-unit , Eq.refl
  h-wd-ax •CZH0H1 {u} {t} order-H0 = left-unit , Eq.refl
  h-wd-ax •CZH0H1S0 {u} {t} order-H0 = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax •CZH0H1S1 {u} {t} order-H0 = left-unit , Eq.refl
  h-wd-ax •CZH0H1S0S1 {u} {t} order-H0 = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax •CZ {u} {t} order-S0H0 = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax •CZH0 {u} {t} order-S0H0 = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax •CZH0S0 {u} {t} order-S0H0 = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax •CZH1 {u} {t} order-S0H0 = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax •CZH1S1 {u} {t} order-S0H0 = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax •CZH0H1 {u} {t} order-S0H0 = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax •CZH0H1S0 {u} {t} order-S0H0 = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax •CZH0H1S1 {u} {t} order-S0H0 = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax •CZH0H1S0S1 {u} {t} order-S0H0 = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax •CZ {u} {t} order-S1 = axiom Ex.order-S1 , Eq.refl
  h-wd-ax •CZH0 {u} {t} order-S1 = axiom Ex.order-S1 , Eq.refl
  h-wd-ax •CZH0S0 {u} {t} order-S1 = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax •CZH1 {u} {t} order-S1 = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax •CZH1S1 {u} {t} order-S1 = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax •CZH0H1 {u} {t} order-S1 = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax •CZH0H1S0 {u} {t} order-S1 = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax •CZH0H1S1 {u} {t} order-S1 = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax •CZH0H1S0S1 {u} {t} order-S1 = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax •CZ {u} {t} order-H1 = left-unit , Eq.refl
  h-wd-ax •CZH0 {u} {t} order-H1 = left-unit , Eq.refl
  h-wd-ax •CZH0S0 {u} {t} order-H1 = left-unit , Eq.refl
  h-wd-ax •CZH1 {u} {t} order-H1 = left-unit , Eq.refl
  h-wd-ax •CZH1S1 {u} {t} order-H1 = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax •CZH0H1 {u} {t} order-H1 = left-unit , Eq.refl
  h-wd-ax •CZH0H1S0 {u} {t} order-H1 = left-unit , Eq.refl
  h-wd-ax •CZH0H1S1 {u} {t} order-H1 = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax •CZH0H1S0S1 {u} {t} order-H1 = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax •CZ {u} {t} order-S1H1 = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax •CZH0 {u} {t} order-S1H1 = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax •CZH0S0 {u} {t} order-S1H1 = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax •CZH1 {u} {t} order-S1H1 = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax •CZH1S1 {u} {t} order-S1H1 = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax •CZH0H1 {u} {t} order-S1H1 = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax •CZH0H1S0 {u} {t} order-S1H1 = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax •CZH0H1S1 {u} {t} order-S1H1 = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax •CZH0H1S0S1 {u} {t} order-S1H1 = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax •CZ {u} {t} comm-H0H1 = refl , Eq.refl
  h-wd-ax •CZH0 {u} {t} comm-H0H1 = refl , Eq.refl
  h-wd-ax •CZH0S0 {u} {t} comm-H0H1 = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax •CZH1 {u} {t} comm-H0H1 = refl , Eq.refl
  h-wd-ax •CZH1S1 {u} {t} comm-H0H1 = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax •CZH0H1 {u} {t} comm-H0H1 = refl , Eq.refl
  h-wd-ax •CZH0H1S0 {u} {t} comm-H0H1 = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax •CZH0H1S1 {u} {t} comm-H0H1 = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax •CZH0H1S0S1 {u} {t} comm-H0H1 = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax •CZ {u} {t} comm-H0S1 = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax •CZH0 {u} {t} comm-H0S1 = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax •CZH0S0 {u} {t} comm-H0S1 = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax •CZH1 {u} {t} comm-H0S1 = refl , Eq.refl
  h-wd-ax •CZH1S1 {u} {t} comm-H0S1 = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax •CZH0H1 {u} {t} comm-H0S1 = refl , Eq.refl
  h-wd-ax •CZH0H1S0 {u} {t} comm-H0S1 = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax •CZH0H1S1 {u} {t} comm-H0S1 = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax •CZH0H1S0S1 {u} {t} comm-H0S1 = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax •CZ {u} {t} comm-S0H1 = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax •CZH0 {u} {t} comm-S0H1 = refl , Eq.refl
  h-wd-ax •CZH0S0 {u} {t} comm-S0H1 = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax •CZH1 {u} {t} comm-S0H1 = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax •CZH1S1 {u} {t} comm-S0H1 = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax •CZH0H1 {u} {t} comm-S0H1 = refl , Eq.refl
  h-wd-ax •CZH0H1S0 {u} {t} comm-S0H1 = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax •CZH0H1S1 {u} {t} comm-S0H1 = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax •CZH0H1S0S1 {u} {t} comm-S0H1 = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax •CZ {u} {t} comm-S0S1 = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax •CZH0 {u} {t} comm-S0S1 = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax •CZH0S0 {u} {t} comm-S0S1 = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax •CZH1 {u} {t} comm-S0S1 = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax •CZH1S1 {u} {t} comm-S0S1 = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax •CZH0H1 {u} {t} comm-S0S1 = refl , Eq.refl
  h-wd-ax •CZH0H1S0 {u} {t} comm-S0S1 = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax •CZH0H1S1 {u} {t} comm-S0S1 = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax •CZH0H1S0S1 {u} {t} comm-S0S1 = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax •CZ {u} {t} order-CZ = left-unit , Eq.refl
  h-wd-ax •CZH0 {u} {t} order-CZ = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax •CZH0S0 {u} {t} order-CZ = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax •CZH1 {u} {t} order-CZ = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax •CZH1S1 {u} {t} order-CZ = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax •CZH0H1 {u} {t} order-CZ = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax •CZH0H1S0 {u} {t} order-CZ = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax •CZH0H1S1 {u} {t} order-CZ = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax •CZH0H1S0S1 {u} {t} order-CZ = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax •CZ {u} {t} comm-S0-CZ = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax •CZH0 {u} {t} comm-S0-CZ = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax •CZH0S0 {u} {t} comm-S0-CZ = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax •CZH1 {u} {t} comm-S0-CZ = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax •CZH1S1 {u} {t} comm-S0-CZ = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax •CZH0H1 {u} {t} comm-S0-CZ = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax •CZH0H1S0 {u} {t} comm-S0-CZ = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax •CZH0H1S1 {u} {t} comm-S0-CZ = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax •CZH0H1S0S1 {u} {t} comm-S0-CZ = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax •CZ {u} {t} comm-S1-CZ = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax •CZH0 {u} {t} comm-S1-CZ = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax •CZH0S0 {u} {t} comm-S1-CZ = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax •CZH1 {u} {t} comm-S1-CZ = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax •CZH1S1 {u} {t} comm-S1-CZ = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax •CZH0H1 {u} {t} comm-S1-CZ = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax •CZH0H1S0 {u} {t} comm-S1-CZ = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax •CZH0H1S1 {u} {t} comm-S1-CZ = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax •CZH0H1S0S1 {u} {t} comm-S1-CZ = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax •CZ {u} {t} rel-X0-CZ = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax •CZH0 {u} {t} rel-X0-CZ = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax •CZH0S0 {u} {t} rel-X0-CZ = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax •CZH1 {u} {t} rel-X0-CZ = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax •CZH1S1 {u} {t} rel-X0-CZ = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax •CZH0H1 {u} {t} rel-X0-CZ = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax •CZH0H1S0 {u} {t} rel-X0-CZ = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax •CZH0H1S1 {u} {t} rel-X0-CZ = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax •CZH0H1S0S1 {u} {t} rel-X0-CZ = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax •CZ {u} {t} rel-X1-CZ = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax •CZH0 {u} {t} rel-X1-CZ = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax •CZH0S0 {u} {t} rel-X1-CZ = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax •CZH1 {u} {t} rel-X1-CZ = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax •CZH1S1 {u} {t} rel-X1-CZ = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax •CZH0H1 {u} {t} rel-X1-CZ = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax •CZH0H1S0 {u} {t} rel-X1-CZ = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax •CZH0H1S1 {u} {t} rel-X1-CZ = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax •CZH0H1S0S1 {u} {t} rel-X1-CZ = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax •CZ {u} {t} rel-CZ-H0-CZ = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax •CZH0 {u} {t} rel-CZ-H0-CZ = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax •CZH0S0 {u} {t} rel-CZ-H0-CZ = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax •CZH1 {u} {t} rel-CZ-H0-CZ = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax •CZH1S1 {u} {t} rel-CZ-H0-CZ = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax •CZH0H1 {u} {t} rel-CZ-H0-CZ = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax •CZH0H1S0 {u} {t} rel-CZ-H0-CZ = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax •CZH0H1S1 {u} {t} rel-CZ-H0-CZ = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax •CZH0H1S0S1 {u} {t} rel-CZ-H0-CZ = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax •CZ {u} {t} rel-CZ-H1-CZ = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax •CZH0 {u} {t} rel-CZ-H1-CZ = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax •CZH0S0 {u} {t} rel-CZ-H1-CZ = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax •CZH1 {u} {t} rel-CZ-H1-CZ = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax •CZH1S1 {u} {t} rel-CZ-H1-CZ = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax •CZH0H1 {u} {t} rel-CZ-H1-CZ = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax •CZH0H1S0 {u} {t} rel-CZ-H1-CZ = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax •CZH0H1S1 {u} {t} rel-CZ-H1-CZ = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax •CZH0H1S0S1 {u} {t} rel-CZ-H1-CZ = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax •ε {u} {t} order-S0 = axiom Ex.order-S0 , Eq.refl
  h-wd-ax •ε {u} {t} order-H0 = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax •ε {u} {t} order-S0H0 = axiom Ex.order-S0H0 , Eq.refl
  h-wd-ax •ε {u} {t} order-S1 = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax •ε {u} {t} order-H1 = axiom Ex.order-H1 , Eq.refl
  h-wd-ax •ε {u} {t} order-S1H1 = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax •ε {u} {t} comm-H0H1 = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax •ε {u} {t} comm-H0S1 = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax •ε {u} {t} comm-S0H1 = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax •ε {u} {t} comm-S0S1 = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax •ε {u} {t} order-CZ = left-unit , Eq.refl
  h-wd-ax •ε {u} {t} comm-S0-CZ = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax •ε {u} {t} comm-S1-CZ = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax •ε {u} {t} rel-X0-CZ = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax •ε {u} {t} rel-X1-CZ = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax •ε {u} {t} rel-CZ-H0-CZ = by-equal-nf Eq.refl , Eq.refl
  h-wd-ax •ε {u} {t} rel-CZ-H1-CZ = by-equal-nf Eq.refl , Eq.refl

  lemma-order-CX : CX ^ 2 ≈₂ ε
  lemma-order-CX = begin
    CX ^ 2 ≈⟨ by-assoc Eq.refl ⟩
    (H1 • CZ) • (H1 • H1) • CZ • H1 ≈⟨ cong refl (cong (axiom order-H1) refl) ⟩
    (H1 • CZ) • ε • CZ • H1 ≈⟨ by-assoc Eq.refl ⟩
    H1 • CZ ^ 2 • H1 ≈⟨ cong refl (cong (axiom order-CZ) refl) ⟩
    H1 • ε • H1 ≈⟨ trans (cong refl left-unit)
                    (axiom order-H1) ⟩
    ε ∎
    where open SR ws₂

  lemma-order-XC : XC ^ 2 ≈₂ ε
  lemma-order-XC = begin
    XC ^ 2 ≈⟨ by-assoc Eq.refl ⟩
    (H0 • CZ) • (H0 • H0) • CZ • H0 ≈⟨ cong refl (cong (axiom order-H0) refl) ⟩
    (H0 • CZ) • ε • CZ • H0 ≈⟨ by-assoc Eq.refl ⟩
    H0 • CZ ^ 2 • H0 ≈⟨ cong refl (cong (axiom order-CZ) refl) ⟩
    H0 • ε • H0 ≈⟨ trans (cong refl left-unit)
                    (axiom order-H0) ⟩
    ε ∎
    where open SR ws₂

  lemma-order-Ex : Ex ^ 2 ≈₂ ε
  lemma-order-Ex = begin
    Ex ^ 2 ≈⟨ by-assoc Eq.refl ⟩
    (CX • XC) • (CX • CX) • XC • CX ≈⟨ cong refl (_≈₂_.cong lemma-order-CX _≈₂_.refl) ⟩
    (CX • XC) • ε • XC • CX ≈⟨ by-assoc Eq.refl ⟩
    CX • XC ^ 2 • CX ≈⟨ cong refl (_≈₂_.cong lemma-order-XC _≈₂_.refl) ⟩
    CX • ε • CX ≈⟨ by-assoc Eq.refl ⟩
    CX • CX ≈⟨ lemma-order-CX ⟩
    ε ∎
    where open SR ws₂

  lemma-order-H0Ex : H0 • Ex ≈₂ Ex • H1
  lemma-order-H0Ex = begin
    H0 • Ex ≈⟨ rewrite-clifford 100 Eq.refl ⟩
    Ex • H1 ∎
    where open SR ws₂

  f-wd-ax : ∀ {w v} -> w ===₁ v -> (f *) w ≈₂ (f *) v
  f-wd-ax {w} {v} Ex.order-S0 = axiom order-S0
  f-wd-ax {w} {v} Ex.order-H0 = axiom order-H0
  f-wd-ax {w} {v} Ex.order-S0H0 = axiom order-S0H0
  f-wd-ax {w} {v} Ex.order-S1 = axiom order-S1
  f-wd-ax {w} {v} Ex.order-H1 = axiom order-H1
  f-wd-ax {w} {v} Ex.order-S1H1 = axiom order-S1H1
  f-wd-ax {w} {v} Ex.comm-H0H1 = axiom comm-H0H1
  f-wd-ax {w} {v} Ex.comm-H0S1 = axiom comm-H0S1
  f-wd-ax {w} {v} Ex.comm-S0H1 = axiom comm-S0H1
  f-wd-ax {w} {v} Ex.comm-S0S1 = axiom comm-S0S1
  f-wd-ax {w} {v} Ex.order-Ex = lemma-order-Ex
  f-wd-ax {w} {v} Ex.comm-H0Ex = lemma-order-H0Ex
  f-wd-ax {w} {v} Ex.comm-S0Ex = rewrite-clifford 100 Eq.refl

  [_] : C ⊎ ⊤ -> Word Gen
  [_] = [_,_] [_]ₒ (λ v → ε)

  open SR ws₂
  open import Presentation.Tactics hiding ([_])
  open Commuting  _===_ Comm.comm~ Comm.les
  
  h=ract :  ∀ c y -> let (m' , c') = h c y in
   ([ c ] • [ y ]ʷ) ≈₂ ([ m' ]ₓ • [ c' ])
  h=ract •CZ H0-gen = _≈₂_.sym _≈₂_.left-unit
  h=ract •CZH0 H0-gen = trans (trans assoc (trans (cong refl (axiom order-H0)) _≈₂_.right-unit)) (sym left-unit)
  h=ract •CZH0S0 H0-gen = rewrite-clifford 100 Eq.refl
  h=ract •CZH1 H0-gen = trans assoc (trans (cong refl (sym (axiom comm-H0H1))) (_≈₂_.sym _≈₂_.left-unit))
  h=ract •CZH1S1 H0-gen = general-comm Eq.refl
  h=ract •CZH0H1 H0-gen = begin
    (CZ • H0 • H1) • H0 ≈⟨ general-comm Eq.refl ⟩
    CZ • (H0 • H0) • H1 ≈⟨ _≈₂_.cong _≈₂_.refl (_≈₂_.cong (_≈₂_.axiom order-H0) _≈₂_.refl) ⟩
    CZ • ε • H1 ≈⟨ _≈₂_.trans (_≈₂_.cong _≈₂_.refl _≈₂_.left-unit)
                    (_≈₂_.sym _≈₂_.left-unit) ⟩
    ε • CZ • H1 ∎
  h=ract •CZH0H1S0 H0-gen = rewrite-clifford 100 Eq.refl
  h=ract •CZH0H1S1 H0-gen =  begin
    (CZ • H0 • H1 • S1) • H0 ≈⟨ general-comm Eq.refl ⟩
    CZ • H0 ^ 2 • H1 • S1 ≈⟨ _≈₂_.cong _≈₂_.refl (_≈₂_.cong (_≈₂_.axiom order-H0) _≈₂_.refl) ⟩
    CZ • ε • H1 • S1 ≈⟨ by-assoc Eq.refl ⟩
    ε • CZ • H1 • S1 ∎
  h=ract •CZH0H1S0S1 H0-gen = rewrite-clifford 100 Eq.refl
  h=ract •CZ S0-gen = _≈₂_.sym (_≈₂_.axiom comm-S0-CZ)
  h=ract •CZH0 S0-gen = by-assoc Eq.refl
  h=ract •CZH0S0 S0-gen = rewrite-clifford 100 Eq.refl
  h=ract •CZH1 S0-gen = general-comm Eq.refl
  h=ract •CZH1S1 S0-gen = general-comm Eq.refl
  h=ract •CZH0H1 S0-gen = general-comm Eq.refl
  h=ract •CZH0H1S0 S0-gen = rewrite-clifford 100 Eq.refl
  h=ract •CZH0H1S1 S0-gen = general-comm Eq.refl
  h=ract •CZH0H1S0S1 S0-gen = rewrite-clifford 100 Eq.refl
  h=ract •CZ H1-gen = _≈₂_.sym _≈₂_.left-unit
  h=ract •CZH0 H1-gen = general-comm Eq.refl
  h=ract •CZH0S0 H1-gen = general-comm Eq.refl
  h=ract •CZH1 H1-gen = trans (trans assoc (trans (cong refl (axiom order-H1)) _≈₂_.right-unit)) (sym left-unit)
  h=ract •CZH1S1 H1-gen = rewrite-clifford 100 Eq.refl
  h=ract •CZH0H1 H1-gen = begin
    (CZ • H0 • H1) • H1 ≈⟨ _≈₂_.trans (_≈₂_.cong (_≈₂_.sym _≈₂_.assoc) _≈₂_.refl) _≈₂_.assoc ⟩
    (CZ • H0) • H1 • H1 ≈⟨ _≈₂_.cong _≈₂_.refl (_≈₂_.axiom order-H1) ⟩
    (CZ • H0) • ε ≈⟨ _≈₂_.trans _≈₂_.right-unit (_≈₂_.sym _≈₂_.left-unit) ⟩
    ε • CZ • H0 ∎
  h=ract •CZH0H1S0 H1-gen = begin
    (CZ • H0 • H1 • S0) • H1 ≈⟨ general-comm Eq.refl ⟩
    (CZ • H0) • (H1 • H1) • S0 ≈⟨ _≈₂_.cong _≈₂_.refl (_≈₂_.cong (_≈₂_.axiom order-H1) _≈₂_.refl) ⟩
    (CZ • H0) • ε • S0 ≈⟨ by-assoc Eq.refl ⟩
    ε • CZ • H0 • S0 ∎
  h=ract •CZH0H1S1 H1-gen = rewrite-clifford 100 Eq.refl
  h=ract •CZH0H1S0S1 H1-gen = rewrite-clifford 100 Eq.refl
  h=ract •CZ S1-gen = _≈₂_.sym (_≈₂_.axiom comm-S1-CZ)
  h=ract •CZH0 S1-gen = general-comm Eq.refl
  h=ract •CZH0S0 S1-gen = general-comm Eq.refl
  h=ract •CZH1 S1-gen = general-comm Eq.refl
  h=ract •CZH1S1 S1-gen = rewrite-clifford 100 Eq.refl
  h=ract •CZH0H1 S1-gen = rewrite-clifford 100 Eq.refl
  h=ract •CZH0H1S0 S1-gen = general-comm Eq.refl
  h=ract •CZH0H1S1 S1-gen = rewrite-clifford 100 Eq.refl
  h=ract •CZH0H1S0S1 S1-gen = rewrite-clifford 100 Eq.refl
  h=ract •CZ CZ-gen = _≈₂_.trans (_≈₂_.axiom order-CZ) (_≈₂_.sym _≈₂_.right-unit)
  h=ract •CZH0 CZ-gen = rewrite-clifford 100 Eq.refl
  h=ract •CZH0S0 CZ-gen = rewrite-clifford 100 Eq.refl
  h=ract •CZH1 CZ-gen = rewrite-clifford 100 Eq.refl
  h=ract •CZH1S1 CZ-gen = rewrite-clifford 100 Eq.refl
  h=ract •CZH0H1 CZ-gen = rewrite-clifford 100 Eq.refl
  h=ract •CZH0H1S0 CZ-gen = rewrite-clifford 100 Eq.refl
  h=ract •CZH0H1S1 CZ-gen = rewrite-clifford 100 Eq.refl
  h=ract •CZH0H1S0S1 CZ-gen = rewrite-clifford 100 Eq.refl
  h=ract •ε H0-gen = _≈₂_.trans _≈₂_.left-unit (_≈₂_.sym _≈₂_.right-unit)
  h=ract •ε S0-gen = _≈₂_.trans _≈₂_.left-unit (_≈₂_.sym _≈₂_.right-unit)
  h=ract •ε H1-gen = _≈₂_.trans _≈₂_.left-unit (_≈₂_.sym _≈₂_.right-unit)
  h=ract •ε S1-gen = _≈₂_.trans _≈₂_.left-unit (_≈₂_.sym _≈₂_.right-unit)
  h=ract •ε CZ-gen = _≈₂_.refl

  module MyCAD = CA.Data _===ₘ_ _===_ (C ⊎ ⊤) •ε f h [_]
  module MyNFP' = MyCAD.Assumptions-And-Theorems htme~ h-wd-ax f-wd-ax _≈₂_.refl h=ract
  
  C2-nfp' : NFProperty' _===_
  C2-nfp' = MyNFP'.nfp' ExM-nfp'

  -- open NFProperty' C2-nfp' renaming (nf to nfC2)
  -- t : {!nfC2 (S1 • CX)!}
  -- t = {!!}
-}
