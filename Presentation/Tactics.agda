{-# OPTIONS --safe #-}
open import Level using (0ℓ)
open import Relation.Binary using (IsEquivalence ; Setoid ; Rel)
open import Data.Product using (_,_)
open import Relation.Binary.Morphism.Definitions using (Homomorphic₂)
open import Relation.Binary.PropositionalEquality using (_≡_)
import Relation.Binary.PropositionalEquality as Eq
import Relation.Binary.Reasoning.Setoid as SR

open import Word.Base

module Presentation.Tactics where

import Presentation.Base as PB
import Presentation.Properties as PP

open import Relation.Binary.Definitions using (DecidableEquality ; Decidable)
open import Relation.Binary.Morphism.Structures using (IsRelMonomorphism)
open import Relation.Binary.PropositionalEquality using (_≡_ ; setoid)
import Relation.Binary.PropositionalEquality as Eq
open import Relation.Nullary.Decidable using (via-injection)
open import Function.Definitions using (Injective)
open import Function.Bundles using (Injection)
open import Function using (_∘_)
open import Data.Nat using (ℕ ; zero ; suc)
import Relation.Binary.Reasoning.Setoid as Eqv
open import Data.Product.Relation.Binary.Pointwise.NonDependent as PW

open import Data.Product using (_×_ ; proj₁ ; proj₂ ; ∃)
open import Data.List using (_++_ ; [] ; _∷_ ; List ; _ʳ++_)

open import Data.Maybe
open import Data.Bool
open import Data.Nat
open import Data.List hiding ([_])
open import Agda.Builtin.Nat using (_-_)

record Reveal_·_is_ {A : Set} {B : A → Set}
                    (f : (x : A) → B x) (x : A) (y : B x) : Set where
  constructor [_]
  field eq : f x ≡ y

inspect : ∀ {A : Set} {B : A → Set}
          (f : (x : A) → B x) (x : A) → Reveal f · x is f x
inspect f x = [ Eq.refl ]


-- ----------------------------------------------------------------------
-- * Tactics for commutativity

-- Definition: two generators commute under Γ.
commutes : ∀ {X} -> WRel X -> X -> X -> Set
commutes Γ x y = ([ x ]ʷ • [ y ]ʷ) ≈' ([ y ]ʷ • [ x ]ʷ)
  where
  open PB Γ renaming (_≈_ to _≈'_)

module Commuting
       {X : Set} (Γ : WRel X) 
       (comm : (x y : X) -> Maybe (commutes Γ x y))
       (less : X -> X -> Bool)
  where

  open import Presentation.Base Γ
  open import Presentation.Properties Γ

  -- This module provides some tactics for proving equations between
  -- words up to commutativity. We assume given a set X of generators,
  -- a set Γ of relations, and a semi-decidable commutativity relation
  -- (i.e., given generators x and y, comm x y either returns a proof
  -- that x and y commute, or nothing). We also assume a total
  -- ordering 'less' on generators, which is used to find canonical
  -- representatives of words up to commutativity.
  --
  -- The tactic general-comm can be used to automatically prove
  -- equalities of ground words up to commutativity It can be used,
  -- for example, as follows. Here, we assume that Z commutes with X
  -- and Y, but X does not commute with Y:
  --
  -- property : Γ ⊢ X • Y • Z ≈ Z • X • Y
  -- property = general-comm auto
  --
  -- Note that this tactic also includes associativity.

  -- ----------------------------------------------------------------------
  -- ** Canonical forms

  -- The primary engine of the commutativity tactic is the function
  -- comm-canonical, which computes the canonical form of a word
  -- modulo commutativity. The canonical form is defined to be the
  -- "smallest" word that is equivalent to the given one. Here,
  -- "smallest" is taken with respect to the reverse (or Hebrew)
  -- lexicographic order.
  --
  -- For example, consider generators A, B, C, D such that A commutes
  -- with C and D; B commutes with D; and no other pair of generators
  -- commutes. Assume A < B < C < D. Then the canonical form of
  -- B,A,D,C,A,B is D,B,C,A,A,B.
  --
  -- The reason we use the reverse lexicographic order is that it
  -- permits a convenient and efficient recursive algorithm for
  -- computing canonical forms. Namely, we can compute the canonical
  -- form of a non-empty list of generators x::xs by first computing
  -- the canonical form of xs, then inserting x in the correct
  -- position.

  -- Auxiliary function: Given ys, x, and zs, return
  -- (reverse zs1 @ ys , zs2), where zs = zs1 @ zs2 and zs1 is the
  -- longest prefix of zs all of whose elements commute with x.
  split' : List X -> X -> List X -> List X × List X
  split' ys x [] = (ys , [])
  split' ys x (z ∷ zs) with comm x z
  split' ys x (z ∷ zs) | nothing = (ys , z ∷ zs)
  split' ys x (z ∷ zs) | just _ = split' (z ∷ ys) x zs

  reverse-append = _ʳ++_

  -- Auxiliary function: Given ys, x, and zs, return reverse ys' @ zs,
  -- where ys' is the lexicographically smallest word that can be
  -- obtained by inserting x in ys. We assume that reverse ys @ zs is
  -- a canonical form.
  unsplit' : List X -> X -> List X -> List X
  unsplit' [] x zs = x ∷ zs
  unsplit' (y ∷ ys) x zs with less x y
  unsplit' (y ∷ ys) x zs | true = unsplit' ys x (y ∷ zs)
  unsplit' (y ∷ ys) x zs | false = reverse-append (y ∷ ys) (x ∷ zs)

  -- Given x and xs, where xs is already a canonical form, return the
  -- canonical form of x ∷ xs.
  insert : X -> List X -> List X
  insert x xs with split' [] x xs
  insert x xs | (ys , zs) = unsplit' ys x zs

  -- Return the canonical form of a word, modulo commutativity of
  -- generators.  Of all equivalent words, the canonical form is the
  -- least one in the reverse lexicographic order.
  comm-canonical : List X -> List X
  comm-canonical [] = []
  comm-canonical (x ∷ xs) = insert x (comm-canonical xs)

  -- ----------------------------------------------------------------------
  -- ** Properties of canonical forms.

  -- We prove various technical properties of the functions split',
  -- reverse-append, unsplit', and insert. These will be needed for
  -- proving that every word is equivalent to its canonical form.

  lemma-split'1 : (ys : List X) -> (x : X) -> (zs : List X) -> ∀ {ys' zs'} -> split' ys x zs ≡ (ys' , zs') -> from-list (reverse-append ys zs) ≈ from-list (reverse-append ys' zs')
  lemma-split'1 ys x [] Eq.refl = refl
  lemma-split'1 ys x (z ∷ zs) eq with comm x z
  lemma-split'1 ys x (z ∷ zs) Eq.refl | nothing = refl
  lemma-split'1 ys x (z ∷ zs) eq | just wit = lemma-split'1 (z ∷ ys) x zs eq


  infixr 5 _∷_

  -- A quantifier for lists. "All P xs" means that all members of xs
  -- have property P.
  data All {A : Set} (P : A -> Set) : List A -> Set where
    [] : All P []
    _∷_ : ∀ {x xs} -> P x -> All P xs -> All P (x ∷ xs)

  -- A more convenient syntax for list quantification.
  infixr 4 All
  syntax All (λ x -> B) xs = All[ x ∈ xs ] B

  -- ----------------------------------------------------------------------
  -- ** Membership

  -- The list membership relation.
  data mem {X : Set} (x : X) : List X -> Set where
    mem-head : ∀ {xs} -> mem x (x ∷ xs)
    mem-tail : ∀ {y xs} -> mem x xs -> mem x (y ∷ xs)

  -- Return the nth member of a list, if any.
  nth : {X : Set} -> ℕ -> List X -> Maybe X
  nth n [] = nothing
  nth zero (x ∷ xs) = just x
  nth (suc n) (x ∷ xs) = nth n xs

  -- Lemma: The nth member of a list is a member!
  lemma-mem-nth : ∀ {X : Set} {x : X} {xs : List X} (n : ℕ) -> nth n xs ≡ just x -> mem x xs
  lemma-mem-nth {xs = []} n ()
  lemma-mem-nth {xs = x ∷ xs} zero Eq.refl = mem-head
  lemma-mem-nth {xs = x ∷ xs} (suc n) hyp = mem-tail (lemma-mem-nth n hyp)
  
  -- The All-elimination rule.
  All-elim : ∀ {X} {x : X} {xs P} -> mem x xs -> All P xs -> P x
  All-elim mem-head (x ∷ a) = x
  All-elim (mem-tail m) (y ∷ a) = All-elim m a

  lemma-split'2 : (ys : List X) -> (x : X) -> (zs : List X) -> All[ y ∈ ys ] commutes Γ x y -> ∀ {ys' zs'} -> split' ys x zs ≡ (ys' , zs') -> All[ y ∈ ys' ] commutes Γ x y
  lemma-split'2 ys x [] ih Eq.refl = ih -- ih
  lemma-split'2 ys x (z ∷ zs) ih eq with comm x z
  lemma-split'2 ys x (z ∷ zs) ih Eq.refl | nothing = ih -- ih
  lemma-split'2 ys x (z ∷ zs) ih eq | just wit = lemma-split'2 (z ∷ ys) x zs (wit ∷ ih) eq

  lemma-reverse-append-cong : (ys : List X) -> (zs zs' : List X) -> from-list zs ≈ from-list zs' -> from-list (reverse-append ys zs) ≈ from-list (reverse-append ys zs')
  lemma-reverse-append-cong [] zs zs' hyp = hyp
  lemma-reverse-append-cong (y ∷ ys) zs zs' hyp = lemma-reverse-append-cong ys (y ∷ zs) (y ∷ zs') (cright hyp)

  gen : X -> Word X
  gen = [_]ʷ

  open SR word-setoid
  
  lemma-reverse-append : (ys : List X) -> (x : X) -> (zs : List X) -> All[ y ∈ ys ] commutes Γ x y -> from-list (x ∷ reverse-append ys zs) ≈ from-list (reverse-append ys (x ∷ zs))
  lemma-reverse-append [] x zs [] = refl
  lemma-reverse-append (y ∷ ys) x zs (h ∷ hyp) =
    let ih : from-list (x ∷ reverse-append ys (y ∷ zs)) ≈ from-list (reverse-append ys (x ∷ y ∷ zs))
        ih = lemma-reverse-append ys x (y ∷ zs) hyp

        claim : gen x • gen y • from-list zs ≈ gen y • gen x • from-list zs
        claim = begin gen x • gen y • from-list zs
                        ≈⟨ assoc reversed ⟩
                    (gen x • gen y) • from-list zs
                        ≈⟨ cleft h ⟩
                    (gen y • gen x) • from-list zs
                        ≈⟨ assoc ⟩
                    gen y • gen x • from-list zs ∎
    in
    begin from-list (x ∷ reverse-append ys (y ∷ zs))
            ≈⟨ ih ⟩
        from-list (reverse-append ys (x ∷ y ∷ zs))
            ≈⟨ lemma-reverse-append-cong ys (x ∷ y ∷ zs) (y ∷ x ∷ zs) claim ⟩
        from-list (reverse-append ys (y ∷ x ∷ zs)) ∎



  lemma-unsplit' : (ys : List X) -> (x : X) -> (zs : List X) -> All[ y ∈ ys ] commutes Γ x y -> from-list (x ∷ reverse-append ys zs) ≈ from-list (unsplit' ys x zs)
  lemma-unsplit' [] x zs hyp = refl
  lemma-unsplit' (y ∷ ys) x zs (h ∷ hyp) with less x y
  lemma-unsplit' (y ∷ ys) x zs (h ∷ hyp) | true = lemma-unsplit' ys x (y ∷ zs) hyp
  lemma-unsplit' (y ∷ ys) x zs (h ∷ hyp) | false = lemma-reverse-append (y ∷ ys) x zs (h ∷ hyp)

  lemma-insert : (x : X) -> (xs : List X) -> from-list (x ∷ xs) ≈ from-list (insert x xs)
  lemma-insert x xs with split' [] x xs | inspect (split' [] x) xs
  ... | (ys , zs) | [ eq ] =
      begin from-list (x ∷ xs)
              ≈⟨ cright lemma-split'1 [] x xs eq ⟩
          from-list (x ∷ reverse-append ys zs)
              ≈⟨ lemma-unsplit' ys x zs (lemma-split'2 [] x xs [] eq) ⟩
          from-list (unsplit' ys x zs) ∎

  -- Soundness of comm-canonical: every word is equivalent to its
  -- canonical form.
  lemma-comm-canonical : (xs : List X) -> from-list xs ≈ from-list (comm-canonical xs)
  lemma-comm-canonical [] = refl
  lemma-comm-canonical (x ∷ xs) =
    begin from-list (x ∷ xs)
            ≈⟨ cright (lemma-comm-canonical xs) ⟩
        from-list (x ∷ comm-canonical xs)
            ≈⟨ lemma-insert x (comm-canonical xs) ⟩
        from-list (insert x (comm-canonical xs)) ∎

  -- ----------------------------------------------------------------------
  -- ** The general-comm tactic

  -- A tactic for showing that two ground words are equivalent up to
  -- commutativity (and associativity). This works ≈⟨ converting both ⟩
  -- words to canonical form and checking that they are equal.
  general-comm : ∀ {w v : Word X} -> comm-canonical (to-list w) ≡ comm-canonical (to-list v) -> w ≈ v
  general-comm {w} {v} hyp =
   begin w
           ≈⟨ lemma-from-to reversed ⟩
       from-list (to-list w)
           ≈⟨ lemma-comm-canonical (to-list w) ⟩
       from-list (comm-canonical (to-list w))
           ≈⟨ refl' (Eq.cong from-list hyp) ⟩
       from-list (comm-canonical (to-list v))
           ≈⟨ lemma-comm-canonical (to-list v) reversed ⟩
       from-list (to-list v)
           ≈⟨ lemma-from-to ⟩
       v ∎


-- ----------------------------------------------------------------------
-- * Strict functions

module Strict where

  -- Apply a function to a list, after first expanding the list
  -- strictly. This is basically a trick to work around certain
  -- problems with Agda's evaluation mechanism. Agda's default
  -- mechanism for evaluating expressions can be very inefficient, and
  -- using 'strict' can occasionally speed things up.
  strict : {X : Set} {P : List X -> Set} -> (xs : List X) -> (k : (xs : List X) -> P xs) -> P xs
  strict [] k = k []
  strict (x ∷ xs) k = strict xs (\xs' -> k (x ∷ xs'))

  lemma-strict : {X : Set} {P : List X -> Set} -> (xs : List X) -> (k : (xs : List X) -> P xs) -> strict xs k ≡ k xs
  lemma-strict [] k = Eq.refl
  lemma-strict (x ∷ xs) k = lemma-strict xs (\xs' -> k (x ∷ xs'))


-- ----------------------------------------------------------------------
-- * Some tactics for proofs by rewriting

module Rewriting
  where
  
  -- This module provides some tactics for proving equations between
  -- words by using a rewrite system. To use these tactics, a
  -- particular set of single-step rewrite rules must be supplied in
  -- the form of a Step-Function. The tactic general-rewrite in the
  -- submodule Step can be used to prove that two words are equal by
  -- rewriting them both to normal form. The tactic general-rewrite in
  -- the submodule Step-With-Standardization does the same, except it
  -- also applies a user-supplied standardization function before and
  -- after each rewrite step. This is typically used to implement
  -- rewriting up to commutativity.

  infixl 4 _then_

  -- ----------------------------------------------------------------------
  -- ** Step functions

  -- The type for step functions. A step function inputs a word and
  -- outputs either Nothing (if no rewrite rule can be applied), or
  -- else a new word (the result of applying a rewrite rule), together
  -- with a proof that the original word and the rewritten word are
  -- equivalent.  For efficiency, words are here implemented as lists
  -- of generators.
  Step-Function : (X : Set) -> (Γ : WRel X) -> Set
  Step-Function X Γ = (xs : List X) -> let open PP Γ in let open PB Γ in Maybe (∃ λ (xs' : List X) -> from-list xs ≈ from-list xs')
  

  -- Sequentially combine two step functions. If the first step
  -- function successfully rewrites the word, use it; otherwise, use
  -- the second step function.
  _then_ : ∀ {X Γ} -> Step-Function X Γ -> Step-Function X Γ -> Step-Function X Γ
  (step1 then step2) xs with step1 xs
  ...                   | just res = just res
  ...                   | nothing = step2 xs

  -- Close a step function under congruence. In other words, input a
  -- step function that only rewrites the head of a list, and return a
  -- step function that rewrites anywhere within the list.
  step-cong : ∀ {X Γ} -> Step-Function X Γ -> Step-Function X Γ
  step-cong step [] = nothing
  step-cong step (h ∷ t) with step (h ∷ t)
  step-cong step (h ∷ t) | just res = just res
  step-cong step (h ∷ t) | nothing with step-cong step t
  step-cong {X} {Γ} step (h ∷ t) | nothing | just (t' , hyp) = just (h ∷ t' , (cright hyp))
    where open PB Γ
  step-cong step (h ∷ t) | nothing | nothing = nothing

  -- ----------------------------------------------------------------------
  -- ** Multistep rewriting

  module Step
         {X : Set}
         {Γ : WRel X}
         (step : Step-Function X Γ)
    where

    -- This module provides the tactic general-rewrite. Given a step
    -- function, this tactic can be used to prove that two words are
    -- equal by repeatedly applying the step function until the words
    -- are in normal form, then checking that they are equal.

    -- Users of this module typically specialize the module to a
    -- particular rewrite function. This can be done, for example, as
    -- follows:
    -- 
    -- module My-Rewrite = Rewriting.Step (step-cong my-stepfunction) renaming (general-rewrite to my-rewrite)
    --
    -- The tactic can then be used as follows:
    --
    -- open My-Rewrite
    -- property : A • B • C ≈ D • E
    -- property = my-rewrite 100 auto

    open Strict
    open PP Γ
    open PB Γ
    open SR word-setoid
    
    -- Rewrite the given word until a normal form is reached, or up to
    -- a maximum of n rewrite steps. The parameter n is needed to
    -- ensure termination.
    multistep : (n : ℕ) -> List X -> List X
    multistep zero xs = xs
    multistep (suc n) xs with strict xs step
    multistep (suc n) xs | nothing = xs
    multistep (suc n) xs | just (xs' , _) = multistep n xs'

    -- Lemma: multistep rewriting returns an equivalent word.
    lemma-multistep : (n : ℕ) -> (xs : List X) -> from-list xs ≈ from-list (multistep n xs)
    lemma-multistep zero xs = refl
    lemma-multistep (suc n) xs with strict xs step | inspect (strict xs) step
    lemma-multistep (suc n) xs | nothing | _ = refl
    lemma-multistep (suc n) xs | just (xs' , hyp) | [ eq ] =
      begin from-list xs
              ≈⟨ hyp ⟩
          from-list xs'
              ≈⟨ lemma-multistep n xs' ⟩
          from-list (multistep n xs') ∎

    -- Return the entire rewrite sequence. This is useful for
    -- debugging rewriting strategies.
    multistep-trace : (n : ℕ) -> List X -> List (List X)
    multistep-trace zero xs = xs ∷ []
    multistep-trace (suc n) xs with step xs
    multistep-trace (suc n) xs | nothing = xs ∷ []
    multistep-trace (suc n) xs | just (xs' , _) = xs ∷ multistep-trace n xs'

    -- A tactic for proving equality of ground words based on a
    -- rewrite relation. The parameter n limits the number of rewrite
    -- steps applied, and is needed to ensure termination. If n is too
    -- small, the tactic may fail.
    general-rewrite : (n : ℕ) -> {w u : Word X} -> multistep n (to-list w) ≡ multistep n (to-list u) -> w ≈ u
    general-rewrite n {w} {u} eq =
      let ws = to-list w
          us = to-list u
      in 
        begin w
                ≈⟨ lemma-from-to {w} reversed ⟩
            from-list ws
                ≈⟨ lemma-multistep n ws ⟩
            from-list (multistep n ws)
                ≈⟨ refl' (Eq.cong from-list eq) ⟩
            from-list (multistep n us)
                ≈⟨ lemma-multistep n us reversed ⟩
            from-list us
                ≈⟨ lemma-from-to {u}  ⟩
            u ∎

  -- ----------------------------------------------------------------------
  -- ** Multistep rewriting with standardization
  module Step-With-Standardization
         {X : Set}
         {Γ : WRel X}
         (step : Step-Function X Γ)
         (standardize : List X -> List X)
         (let open PP Γ)
         (let open PB Γ)
         (lemma-standardize : (xs : List X) ->  from-list xs ≈ from-list (standardize xs))
    where

    -- This module provides another version of the tactic
    -- general-rewrite that also applies a standardization function
    -- after each step. This is typically used to implement rewriting
    -- up to commutativity.
    --
    -- Users of this module typically specialize the module to a
    -- particular rewrite function and standardization function. This
    -- can be done, for example, as follows:
    --
    -- module My-Rewrite = Rewriting.Step (step-cong my-stepfunction) my-standardize my-lemma-standardize renaming (general-rewrite to my-rewrite)
    --
    -- The tactic can then be used as follows:
    --
    -- open My-Rewrite
    -- property : A • B • C ≈ D • E
    -- property = my-rewrite 100 auto
    
    open Strict
    open SR word-setoid
    
    mutual
      -- Rewrite the given word until a normal form is reached, or up
      -- to a maximum of n rewrite steps. The parameter n is needed to
      -- ensure termination. The given standardization function is
      -- applied before and after every rewrite step.
      multistep : (n : ℕ) -> List X -> List X
      multistep n xs = multistep-st n (standardize xs)

      -- Auxiliary function: multistep-st assumes that the input is
      -- already standardized.
      multistep-st : (n : ℕ) -> List X -> List X
      multistep-st zero xs = xs
      multistep-st (suc n) xs with strict xs step
      multistep-st (suc n) xs | nothing = xs
      multistep-st (suc n) xs | just (xs' , _) = multistep n xs'

    mutual
      -- Lemma: multistep rewriting returns an equivalent word.
      lemma-multistep : (n : ℕ) -> (xs : List X) -> from-list xs ≈ from-list (multistep n xs)
      lemma-multistep n xs =
        let xs' = standardize xs
        in
          begin from-list xs
                  ≈⟨ lemma-standardize xs ⟩
              from-list xs'
                  ≈⟨ lemma-multistep-st n xs' ⟩
              from-list (multistep-st n xs')
                  ≈⟨ refl ⟩
              from-list (multistep n xs) ∎

      lemma-multistep-st : (n : ℕ) -> (xs : List X) -> from-list xs ≈ from-list (multistep-st n xs)
      lemma-multistep-st zero xs = refl
      lemma-multistep-st (suc n) xs with strict xs step | inspect (strict xs) step
      lemma-multistep-st (suc n) xs | nothing | _ = refl
      lemma-multistep-st (suc n) xs | just (xs' , hyp) | [ eq ] =
        begin from-list xs
                ≈⟨ hyp ⟩
            from-list xs'
                ≈⟨ lemma-multistep n xs' ⟩
            from-list (multistep n xs') ∎

    -- Return the entire rewrite sequence. Useful for debugging
    -- rewriting strategies. Note: in the output, standardization
    -- steps will alternate with rewrite steps, even if the
    -- standardization is the identity.
    mutual
      multistep-trace : (n : ℕ) -> List X -> List (List X)
      multistep-trace n xs = xs ∷ multistep-trace-st n (standardize xs)

      multistep-trace-st : (n : ℕ) -> List X -> List (List X)
      multistep-trace-st zero xs = xs ∷ []
      multistep-trace-st (suc n) xs with step xs
      multistep-trace-st (suc n) xs | nothing = xs ∷ []
      multistep-trace-st (suc n) xs | just (xs' , _) = xs ∷ multistep-trace n xs'
  
    -- A tactic for proving equality of ground words based on a
    -- rewrite relation and a standardization function. The parameter
    -- n limits the number of rewrite steps applied, and is needed to
    -- ensure termination. If n is too small, the tactic may fail.
    general-rewrite : (n : ℕ) -> {w u : Word X} -> multistep n (to-list w) ≡ multistep n (to-list u) -> w ≈ u
    general-rewrite n {w} {u} eq =
      let ws = to-list w
          us = to-list u
      in 
        begin w
                ≈⟨ lemma-from-to {w} reversed ⟩
            from-list ws
                ≈⟨ lemma-multistep n ws ⟩
            from-list (multistep n ws)
                ≈⟨ refl' (Eq.cong from-list eq) ⟩
            from-list (multistep n us)
                ≈⟨ lemma-multistep n us reversed ⟩
            from-list us
                ≈⟨ lemma-from-to {u} ⟩
            u ∎



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
