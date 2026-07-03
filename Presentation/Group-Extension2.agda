{-# OPTIONS --safe #-}

------------------------------------------------------------------------
-- Presentations of group extensions, orientation II.
--
-- Analogue of Presentation.Group-Extension for the conjugation
-- orientation of Proposition 2.55 in the textbook:
--
--   if N has presentation < Y | S > and G/N has presentation
--   < Xbar | Rbar >, choose lifts X of Xbar in G.  A presentation of
--   G is obtained on generators Y ∪ X by:
--
--     * the kernel relations S;
--     * one corrected lift of every quotient relation;
--     * conjugation relations  y · x = x · w_xy  (x⁻¹ y x = w_xy).
--
-- The only difference from Group-Extension is the orientation of the
-- conjugation constructor:
--
--   Group-Extension  :  x · y  ≈  w_xy · x    (x y x⁻¹ = w_xy)
--   Group-Extension2 :  y · x  ≈  x · w_xy    (x⁻¹ y x = w_xy)
--
-- This module also proves Proposition 2.55 for the split case:
-- given NFProperty for S and R and two compatibility conditions on the
-- conjugation action, SplitExtensionRel2 has NFProperty' (Theorem
-- proved in module SplitProof.NFP).
------------------------------------------------------------------------

open import Level using (0ℓ)
open import Relation.Binary using (REL ; Setoid)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)
import Relation.Binary.PropositionalEquality as Eq renaming ([_] to [_]')
open import Data.Product using (∃ ; _×_ ; _,_ ; proj₁ ; proj₂ ; map)
import Data.Product.Relation.Binary.Pointwise.NonDependent as PW
open import Data.Sum using (_⊎_ ; inj₁ ; inj₂)
import Function.Construct.Composition as FCC
import Relation.Binary.Reasoning.Setoid as SR

open import Word.Base
open import Word.Properties
import Presentation.Horizontal-Syntactics as PB
import Presentation.Properties as PP
open import Presentation.Reidemeister-Schreier
open import Presentation.Construct.Base using ([_]ₗ ; [_]ᵣ)

module Presentation.Group-Extension2 where

WREL : Set -> Set -> Set₁
WREL X Y = REL (Word X) (Word Y) 0ℓ

------------------------------------------------------------------------
-- Data for the extension recipe.
-- Identical in structure to Group-Extension.ExtensionData.
------------------------------------------------------------------------

record ExtensionData {Y X : Set}
                     (S : WRel Y)
                     (R : WRel X) : Set₁ where
  field
    quotient-correction : ∀ {u v : Word X} -> R u v -> Word Y

    -- For each lifted generator x and kernel generator y,
    -- choose the kernel word w_xy with y · x = x · w_xy,
    -- i.e. x⁻¹ y x = w_xy in ordinary group notation.
    conjugation-correction : X -> Y -> Word Y


------------------------------------------------------------------------
-- The extension relation.
------------------------------------------------------------------------

data ExtensionRel2
  {Y X : Set}
  (S : WRel Y)
  (R : WRel X)
  (ext : ExtensionData S R)
  : WRel (Y ⊎ X) where

  kernel :
    ∀ {u v : Word Y} ->
    S u v ->
    ExtensionRel2 S R ext [ u ]ₗ [ v ]ₗ

  quotient :
    ∀ {u v : Word X} ->
    (ρ : R u v) ->
    ExtensionRel2 S R ext
      [ u ]ᵣ
      ([ ExtensionData.quotient-correction ext ρ ]ₗ • [ v ]ᵣ)

  -- y · x = x · w_xy  (x⁻¹ y x = w_xy)
  conjugation :
    ∀ (x : X) (y : Y) ->
    ExtensionRel2 S R ext
      ([ [ y ]ʷ ]ₗ • [ [ x ]ʷ ]ᵣ)
      ([ [ x ]ʷ ]ᵣ • [ ExtensionData.conjugation-correction ext x y ]ₗ)


------------------------------------------------------------------------
-- A direct, parameterized variant.
------------------------------------------------------------------------

data ExtensionRel2'
  {Y X : Set}
  (S : WRel Y)
  (R : WRel X)
  (quotient-correction : ∀ {u v : Word X} -> R u v -> Word Y)
  (conjugation-correction : X -> Y -> Word Y)
  : WRel (Y ⊎ X) where

  kernel :
    ∀ {u v : Word Y} ->
    S u v ->
    ExtensionRel2' S R quotient-correction conjugation-correction
      [ u ]ₗ [ v ]ₗ

  quotient :
    ∀ {u v : Word X} ->
    (ρ : R u v) ->
    ExtensionRel2' S R quotient-correction conjugation-correction
      [ u ]ᵣ
      ([ quotient-correction ρ ]ₗ • [ v ]ᵣ)

  conjugation :
    ∀ (x : X) (y : Y) ->
    ExtensionRel2' S R quotient-correction conjugation-correction
      ([ [ y ]ʷ ]ₗ • [ [ x ]ʷ ]ᵣ)
      ([ [ x ]ʷ ]ᵣ • [ conjugation-correction x y ]ₗ)


------------------------------------------------------------------------
-- The split case: quotient relators lift without correction.
------------------------------------------------------------------------

split-extension-data :
  ∀ {Y X : Set} {S : WRel Y} {R : WRel X} ->
  (conjugation-correction : X -> Y -> Word Y) ->
  ExtensionData S R
split-extension-data conjugation-correction = record
  { quotient-correction = λ _ -> ε
  ; conjugation-correction = conjugation-correction
  }

SplitExtensionRel2 :
  ∀ {Y X : Set} ->
  (S : WRel Y) ->
  (R : WRel X) ->
  (conjugation-correction : X -> Y -> Word Y) ->
  WRel (Y ⊎ X)
SplitExtensionRel2 S R conjugation-correction =
  ExtensionRel2 S R (split-extension-data conjugation-correction)


------------------------------------------------------------------------
-- Formal proof infrastructure.
--
-- Two maps:
--   1. include the kernel presentation into the extension presentation;
--   2. project the extension presentation to the quotient presentation
--      by killing kernel generators.
-- Both respect the defining relations.
------------------------------------------------------------------------

module Proof
  {Y X : Set}
  (S : WRel Y)
  (R : WRel X)
  (ext : ExtensionData S R)
  where

  Γ : WRel (Y ⊎ X)
  Γ = ExtensionRel2 S R ext

  open PB S renaming (_≈_ to _≈S_)
    using ()
  open PB R renaming (_≈_ to _≈R_ ; refl to reflR ; sym to symR ;
                      trans to transR ; cong to congR ; axiom to axiomR ;
                      left-unit to left-unitR ; right-unit to right-unitR)
    using ()
  open PB Γ renaming (_≈_ to _≈Γ_ ; axiom to axiomΓ)
    using ()

  ----------------------------------------------------------------------
  -- Kernel inclusion.
  ----------------------------------------------------------------------

  include-kernel : Y -> Word (Y ⊎ X)
  include-kernel y = [ inj₁ y ]ʷ

  include-kernel* : Word Y -> Word (Y ⊎ X)
  include-kernel* = include-kernel *

  include-kernel*≡left : ∀ (w : Word Y) -> include-kernel* w ≡ [ w ]ₗ
  include-kernel*≡left [ y ]ʷ = refl
  include-kernel*≡left ε = refl
  include-kernel*≡left (u • v) rewrite include-kernel*≡left u | include-kernel*≡left v = refl

  include-kernel-well-defined :
    ∀ {u v : Word Y} ->
    S u v ->
    include-kernel* u ≈Γ include-kernel* v
  include-kernel-well-defined {u} {v} rel
    rewrite include-kernel*≡left u | include-kernel*≡left v =
    axiomΓ (kernel rel)

  ----------------------------------------------------------------------
  -- Projection to the quotient presentation.
  ----------------------------------------------------------------------

  to-quotient : Y ⊎ X -> Word X
  to-quotient (inj₁ _) = ε
  to-quotient (inj₂ x) = [ x ]ʷ

  to-quotient* : Word (Y ⊎ X) -> Word X
  to-quotient* = to-quotient *

  left-killed :
    ∀ (w : Word Y) ->
    to-quotient* [ w ]ₗ ≈R ε
  left-killed [ y ]ʷ = reflR
  left-killed ε = reflR
  left-killed (u • v) =
    transR (congR (left-killed u) (left-killed v)) left-unitR

  right-preserved :
    ∀ (w : Word X) ->
    to-quotient* [ w ]ᵣ ≈R w
  right-preserved [ x ]ʷ = reflR
  right-preserved ε = reflR
  right-preserved (u • v) =
    congR (right-preserved u) (right-preserved v)

  quotient-tail :
    ∀ (wy : Word Y) (wx : Word X) ->
    to-quotient* ([ wy ]ₗ • [ wx ]ᵣ) ≈R wx
  quotient-tail wy wx =
    transR (congR (left-killed wy) (right-preserved wx)) left-unitR

  quotient-head :
    ∀ (x : X) (wy : Word Y) ->
    to-quotient* ([ [ x ]ʷ ]ᵣ • [ wy ]ₗ) ≈R [ x ]ʷ
  quotient-head x wy =
    transR (congR reflR (left-killed wy)) right-unitR

  to-quotient-well-defined :
    ∀ {u v : Word (Y ⊎ X)} ->
    Γ u v ->
    to-quotient* u ≈R to-quotient* v
  to-quotient-well-defined (kernel {u} {v} _) =
    transR (left-killed u) (symR (left-killed v))
  to-quotient-well-defined (quotient {u} {v} ρ) =
    transR (right-preserved u)
      (transR (axiomR ρ)
        (symR (quotient-tail
          (ExtensionData.quotient-correction ext ρ)
          v)))
  -- LHS: [y]ₗ • [x]ᵣ  projects to  ε • [x]ʷ = [x]ʷ
  -- RHS: [x]ᵣ • [w_xy]ₗ  projects to  [x]ʷ • ε = [x]ʷ
  to-quotient-well-defined (conjugation x y) =
    transR (quotient-tail [ y ]ʷ [ x ]ʷ)
      (symR (quotient-head x (ExtensionData.conjugation-correction ext x y)))

  to-quotient-preimage : Word X -> Word (Y ⊎ X)
  to-quotient-preimage = [_]ᵣ

  to-quotient-preimage-correct :
    ∀ (w : Word X) ->
    to-quotient* (to-quotient-preimage w) ≈R w
  to-quotient-preimage-correct = right-preserved

  ----------------------------------------------------------------------
  -- Exactness statement.
  ----------------------------------------------------------------------

  record ExtensionExact : Set₁ where
    field
      kernel-complete :
        ∀ (w : Word (Y ⊎ X)) ->
        to-quotient* w ≈R ε ->
        ∃ λ (wy : Word Y) -> w ≈Γ [ wy ]ₗ

      kernel-sound :
        ∀ (wy : Word Y) ->
        to-quotient* [ wy ]ₗ ≈R ε

    kernel-sound-default :
      ∀ (wy : Word Y) ->
      to-quotient* [ wy ]ₗ ≈R ε
    kernel-sound-default = left-killed


------------------------------------------------------------------------
-- Proposition 2.55 (split case).
--
-- Given:
--   • NFProperty' S  (S is a complete presentation of the kernel N)
--   • NFProperty' R  (R is a complete presentation of the quotient G/N)
--   • conj-hyp-S : the conjugation by each x respects S-equivalence
--   • conj-wd-R  : the conjugation action is well-defined on R-classes
--
-- we construct NFProperty' (SplitExtensionRel2 S R conj-corr).
--
-- The normal form is: every word in Y ⊎ X is ≈-equivalent to a unique
-- word of the shape  [wx]ᵣ • [wy]ₗ  (quotient coset on left, kernel
-- on right).  The LeftAction module from Reidemeister-Schreier provides
-- the injectivity direction; well-definedness is proved directly.
------------------------------------------------------------------------

module SplitProof
  {Y X : Set}
  (S : WRel Y)
  (R : WRel X)
  (conj-corr : X -> Y -> Word Y)
  where

  private
    Γ : WRel (Y ⊎ X)
    Γ = SplitExtensionRel2 S R conj-corr

  open PB S  renaming (_≈_ to _≈S_ ; refl to reflS ; sym to symS ; trans to transS
                       ; cong to congS ; axiom to axiomS
                       ; left-unit to left-unitS ; right-unit to right-unitS) using ()
  open PB R  renaming (_≈_ to _≈R_ ; refl to reflR ; sym to symR ; trans to transR
                       ; cong to congR ; axiom to axiomR
                       ; left-unit to left-unitR ; right-unit to right-unitR) using ()
  open PB Γ  renaming (_≈_ to _≈Γ_ ; refl to reflΓ ; sym to symΓ ; trans to transΓ
                       ; cong to congΓ ; axiom to axiomΓ
                       ; assoc to assocΓ ; left-unit to left-unitΓ ; right-unit to right-unitΓ) using ()
  open PP S  renaming (word-setoid to word-setoid-S) using ()
  open PP R  renaming (word-setoid to word-setoid-R) using ()
  open PP Γ  renaming (word-setoid to word-setoid-Γ) using ()

  -- The "right-embedding lifts to ≈Γ" fact: [c]ᵣ ≈Γ [d]ᵣ when c ≈R d.
  private
    []-cong : ∀ {c d : Word X} -> c ≈R d -> [ c ]ᵣ ≈Γ [ d ]ᵣ
    []-cong PB.refl = reflΓ
    []-cong (PB.sym h) = symΓ ([]-cong h)
    []-cong (PB.trans h₁ h₂) = transΓ ([]-cong h₁) ([]-cong h₂)
    []-cong (PB.cong h₁ h₂) = congΓ ([]-cong h₁) ([]-cong h₂)
    []-cong PB.assoc = assocΓ
    []-cong PB.left-unit = left-unitΓ
    []-cong PB.right-unit = right-unitΓ
    []-cong (PB.axiom ax) = transΓ (axiomΓ (quotient ax)) left-unitΓ

    -- Similarly for the left embedding.
    []-cong-l : ∀ {u v : Word Y} -> u ≈S v -> [ u ]ₗ ≈Γ [ v ]ₗ
    []-cong-l PB.refl = reflΓ
    []-cong-l (PB.sym h) = symΓ ([]-cong-l h)
    []-cong-l (PB.trans h₁ h₂) = transΓ ([]-cong-l h₁) ([]-cong-l h₂)
    []-cong-l (PB.cong h₁ h₂) = congΓ ([]-cong-l h₁) ([]-cong-l h₂)
    []-cong-l PB.assoc = assocΓ
    []-cong-l PB.left-unit = left-unitΓ
    []-cong-l PB.right-unit = right-unitΓ
    []-cong-l (PB.axiom ax) = axiomΓ (kernel ax)

  ----------------------------------------------------------------------
  -- Conjugation action.
  --
  -- conjss c w = the Y-word obtained by conjugating the Y-word w
  -- through the X-coset c, reading c from left to right:
  --   conjss ε         w = w
  --   conjss ([x]ʷ)    w = (conj-corr x *) w
  --   conjss (c₁ • c₂) w = conjss c₂ (conjss c₁ w)
  --
  -- The defining property is  [w]ₗ • [c]ᵣ ≈Γ [c]ᵣ • [conjss c w]ₗ.
  ----------------------------------------------------------------------

  conjss : Word X -> Word Y -> Word Y
  conjss [ x ]ʷ w = (conj-corr x *) w
  conjss ε       w = w
  conjss (c • c') w = conjss c' (conjss c w)

  -- conjss distributes over • and sends ε to ε.
  conjss-homo : ∀ (c : Word X) (u v : Word Y) -> conjss c (u • v) ≡ conjss c u • conjss c v
  conjss-homo [ x ]ʷ u v = refl
  conjss-homo ε       u v = refl
  conjss-homo (c • c') u v rewrite conjss-homo c u v | conjss-homo c' (conjss c u) (conjss c v) = refl

  conjss-ε : ∀ (c : Word X) -> conjss c ε ≡ ε
  conjss-ε [ x ]ʷ = refl
  conjss-ε ε       = refl
  conjss-ε (c • c') rewrite conjss-ε c | conjss-ε c' = refl

  ----------------------------------------------------------------------
  -- Key commutation lemma:  [w]ₗ • [c]ᵣ ≈Γ [c]ᵣ • [conjss c w]ₗ
  ----------------------------------------------------------------------

  private
    lemma-comm-gen : ∀ (x : X) (y : Y) ->
      [ [ y ]ʷ ]ₗ • [ [ x ]ʷ ]ᵣ ≈Γ [ [ x ]ʷ ]ᵣ • [ conj-corr x y ]ₗ
    lemma-comm-gen x y = axiomΓ (conjugation x y)

  private
    mutual
      lemma-comm : ∀ (c : Word X) (w : Word Y) ->
        [ w ]ₗ • [ c ]ᵣ ≈Γ [ c ]ᵣ • [ conjss c w ]ₗ
      lemma-comm c [ y ]ʷ = lemma-comm1 c y
      lemma-comm c ε =
        Eq.subst (\ □ -> [ ε ]ₗ • [ c ]ᵣ ≈Γ [ c ]ᵣ • [ □ ]ₗ) (Eq.sym (conjss-ε c))
          (transΓ left-unitΓ (symΓ right-unitΓ))
      lemma-comm c (w • v) = begin
          [ w • v ]ₗ • [ c ]ᵣ
        ≈⟨ assocΓ ⟩
          [ w ]ₗ • [ v ]ₗ • [ c ]ᵣ
        ≈⟨ congΓ reflΓ (lemma-comm c v) ⟩
          [ w ]ₗ • ([ c ]ᵣ • [ conjss c v ]ₗ)
        ≈⟨ symΓ assocΓ ⟩
          ([ w ]ₗ • [ c ]ᵣ) • [ conjss c v ]ₗ
        ≈⟨ congΓ (lemma-comm c w) reflΓ ⟩
          ([ c ]ᵣ • [ conjss c w ]ₗ) • [ conjss c v ]ₗ
        ≈⟨ assocΓ ⟩
          [ c ]ᵣ • ([ conjss c w ]ₗ • [ conjss c v ]ₗ)
        ≈⟨ congΓ reflΓ (Eq.subst (\ □ -> [ conjss c w ]ₗ • [ conjss c v ]ₗ ≈Γ [ □ ]ₗ) (Eq.sym (conjss-homo c w v)) reflΓ) ⟩
          [ c ]ᵣ • [ conjss c (w • v) ]ₗ
        ∎
        where open SR word-setoid-Γ

      lemma-comm1 : ∀ (c : Word X) (y : Y) ->
        [ [ y ]ʷ ]ₗ • [ c ]ᵣ ≈Γ [ c ]ᵣ • [ conjss c [ y ]ʷ ]ₗ
      lemma-comm1 ε y = transΓ right-unitΓ (symΓ left-unitΓ)
      lemma-comm1 [ x ]ʷ y = lemma-comm-gen x y
      lemma-comm1 (c • c') y = begin
          [ [ y ]ʷ ]ₗ • [ c • c' ]ᵣ
        ≈⟨ symΓ assocΓ ⟩
          ([ [ y ]ʷ ]ₗ • [ c ]ᵣ) • [ c' ]ᵣ
        ≈⟨ congΓ (lemma-comm1 c y) reflΓ ⟩
          ([ c ]ᵣ • [ conjss c [ y ]ʷ ]ₗ) • [ c' ]ᵣ
        ≈⟨ assocΓ ⟩
          [ c ]ᵣ • ([ conjss c [ y ]ʷ ]ₗ • [ c' ]ᵣ)
        ≈⟨ congΓ reflΓ (lemma-comm c' (conjss c [ y ]ʷ)) ⟩
          [ c ]ᵣ • ([ c' ]ᵣ • [ conjss c' (conjss c [ y ]ʷ) ]ₗ)
        ≈⟨ symΓ assocΓ ⟩
          ([ c ]ᵣ • [ c' ]ᵣ) • [ conjss c' (conjss c [ y ]ʷ) ]ₗ
        ∎
        where open SR word-setoid-Γ

  ----------------------------------------------------------------------
  -- The LeftAction:
  --   lact g c = (c', k) such that [g]ʷ • [c]ᵣ ≈Γ [c']ᵣ • [k]ₗ
  --
  -- Processing right-to-left (right fold) gives the normal form
  --   nfl(w) = w ⊛ ε = (quotient-coset, kernel-word)
  -- with the property  [coset]ᵣ • [kernel]ₗ ≈Γ w.
  ----------------------------------------------------------------------

  private
    -- Kernel embedding and coset setoid.
    f-emb : Y -> Word (Y ⊎ X)
    f-emb y = [ inj₁ y ]ʷ

    Cₛ : Setoid 0ℓ 0ℓ
    Cₛ = PP.word-setoid {X} R

    open Star-Injective-Full-Setoid S Γ Cₛ ε
      renaming (C to C-rs ; _≈ₛ_ to _≈ₛ_ ; _~_ to _~_
               ; refl~ to refl~ ; sym~ to sym~ ; trans~ to trans~)
      hiding (nf ; _⊛_)

    -- Provide a placeholder h so we can enter the f,h,h-cong module.
    -- (RS-Full is not used; we only need LeftAction below.)
    h-dummy : C-rs -> Y ⊎ X -> Word Y × C-rs
    h-dummy c _ = (ε , c)

    h-dummy-cong : ∀ {c d} g -> c ≈ₛ d -> h-dummy c g ~ h-dummy d g
    h-dummy-cong _ cd = reflS , cd

    -- The actual left action.
    lact-fn : (Y ⊎ X) -> C-rs -> C-rs × Word Y
    lact-fn (inj₁ y) c = (c , conjss c [ y ]ʷ)
    lact-fn (inj₂ x) c = ([ x ]ʷ • c , ε)

    f-emb-wd : ∀ {u v : Word Y} -> S u v -> (f-emb *) u ≈Γ (f-emb *) v
    f-emb-wd {u} {v} su =
      Eq.subst₂ _≈Γ_
        (Eq.sym (wconcatmap-[f]ʷ {f = inj₁} u))
        (Eq.sym (wconcatmap-[f]ʷ {f = inj₁} v))
        (axiomΓ (kernel su))

    [_]-R : C-rs -> Word (Y ⊎ X)
    [_]-R c = [ c ]ᵣ

    []-R-cong : ∀ {c d : C-rs} -> c ≈ₛ d -> [ c ]-R ≈Γ [ d ]-R
    []-R-cong = []-cong

    [I]-R≈ε : [ ε ]-R ≈Γ ε
    [I]-R≈ε = reflΓ

    lemma-lact-fn : ∀ g c ->
      let (c' , k') = lact-fn g c
          [_]ₓ = (f-emb *)
      in  [ g ]ʷ • [ c ]-R ≈Γ [ c' ]-R • [ k' ]ₓ
    lemma-lact-fn (inj₁ y) c = begin
        [ inj₁ y ]ʷ • [ c ]ᵣ
      ≈⟨ lemma-comm c [ y ]ʷ ⟩
        [ c ]ᵣ • [ conjss c [ y ]ʷ ]ₗ
      ≈⟨ congΓ reflΓ (Eq.subst (\ □ -> [ conjss c [ y ]ʷ ]ₗ ≈Γ □)
                                (Eq.sym (wconcatmap-[f]ʷ {f = inj₁} (conjss c [ y ]ʷ))) reflΓ) ⟩
        [ c ]ᵣ • (f-emb *) (conjss c [ y ]ʷ)
      ∎
      where open SR word-setoid-Γ
    lemma-lact-fn (inj₂ x) c = symΓ right-unitΓ

  open LeftAction f-emb h-dummy h-dummy-cong f-emb-wd [_]-R []-R-cong [I]-R≈ε lact-fn lemma-lact-fn
    hiding ([_]ₓ)

  -- nfl : Word (Y ⊎ X) → Word X × Word Y
  -- ⁻¹nfl (c , k) = [c]ᵣ • [k]ₗ
  -- ⁻¹nfl-nfl=id : [coset]ᵣ • [kernel]ₗ ≈Γ w
  -- nfl-isInjective' : coset ≈R coset' ∧ kernel ≈S kernel' → w ≈Γ v

  ----------------------------------------------------------------------
  -- Well-definedness of nfl:  w ≈Γ v → nfl(w) ~ nfl(v)
  --
  -- This is the harder direction, proved by induction on the
  -- derivation of ≈Γ.  It requires two compatibility hypotheses on
  -- conj-corr:
  --
  --   conj-hyp-S x sv :
  --     if S u v then (conj-corr x *) u ≈S (conj-corr x *) v
  --     (conjugation by x respects S-equivalence)
  --
  --   conj-wd-R rv w :
  --     if R c d then conjss c w ≈S conjss d w
  --     (the action depends only on the R-class of the coset)
  --
  -- These are stored inside module NFP so the outer module typechecks
  -- unconditionally; they are only required to conclude NFProperty'.
  ----------------------------------------------------------------------

  module NFP
    (conj-hyp-S : ∀ x {u v : Word Y} -> S u v -> (conj-corr x *) u ≈S (conj-corr x *) v)
    (conj-wd-R  : ∀ {c d : Word X} -> R c d -> ∀ (w : Word Y) -> conjss c w ≈S conjss d w)
    (nfp-S : PP.NFProperty' S)
    (nfp-R : PP.NFProperty' R)
    where

    open PP.NFProperty' nfp-S
      renaming (NF to NF-S ; nf to nf-S ; nf-cong to nf-S-cong
               ; inv-nf to inv-S ; inv-nf∘nf=id to inv-S∘nf-S=id
               ; nf-injective to nf-S-inj ; hasNFProperty to nfp-S') using ()
    open PP.NFProperty' nfp-R
      renaming (NF to NF-R ; nf to nf-R ; nf-cong to nf-R-cong
               ; inv-nf to inv-R ; inv-nf∘nf=id to inv-R∘nf-R=id
               ; nf-injective to nf-R-inj ; hasNFProperty to nfp-R') using ()

    private
      -- conjss is congruent in both arguments (needed for well-definedness).
      conjss-cong-word : ∀ (c : Word X) {u v : Word Y} -> u ≈S v -> conjss c u ≈S conjss c v
      conjss-cong-word [ x ]ʷ eq =
        Star-Congruence.lemma-f*-cong S S (conj-corr x) (conj-hyp-S x) eq
      conjss-cong-word ε eq = eq
      conjss-cong-word (c • c') eq =
        conjss-cong-word c' (conjss-cong-word c eq)

      conjss-cong-coset : ∀ {c d : Word X} -> c ≈R d -> ∀ (w : Word Y) -> conjss c w ≈S conjss d w
      conjss-cong-coset PB.refl w = reflS
      conjss-cong-coset (PB.sym h) w = symS (conjss-cong-coset h w)
      conjss-cong-coset (PB.trans h₁ h₂) w = transS (conjss-cong-coset h₁ w) (conjss-cong-coset h₂ w)
      conjss-cong-coset (PB.cong {c₁} {d₁} {c₂} {d₂} h₁ h₂) w =
        transS (conjss-cong-coset h₂ (conjss c₁ w))
               (conjss-cong-word d₂ (conjss-cong-coset h₁ w))
      conjss-cong-coset PB.assoc w = reflS
      conjss-cong-coset PB.left-unit w = reflS
      conjss-cong-coset PB.right-unit w = reflS
      conjss-cong-coset (PB.axiom ax) w = conj-wd-R ax w

      -- [u]ₗ ⊛ c = (c, conjss c u) propositionally (not definitional for compound u/c).
      nfl-kernel-eq : ∀ (u : Word Y) (c : Word X) -> ([ u ]ₗ ⊛ c) ≡ (c , conjss c u)
      nfl-kernel-eq ε c = Eq.cong (c ,_) (Eq.sym (conjss-ε c))
      nfl-kernel-eq [ y ]ʷ c = refl
      nfl-kernel-eq (u • v) c with [ v ]ₗ ⊛ c | nfl-kernel-eq v c
      nfl-kernel-eq (u • v) c | (c' , v') | ev with [ u ]ₗ ⊛ c' | nfl-kernel-eq u c'
      nfl-kernel-eq (u • v) c | (c' , v') | ev | (c'' , u') | eu =
        Eq.cong₂ _,_
          (Eq.trans (Eq.cong proj₁ eu) (Eq.cong proj₁ ev))
          (Eq.trans
            (Eq.cong₂ _•_ (Eq.trans (Eq.cong proj₂ eu)
                                     (Eq.cong (λ k -> conjss k u) (Eq.cong proj₁ ev)))
                          (Eq.cong proj₂ ev))
            (Eq.sym (conjss-homo c u v)))

      -- Quotient case lemmas: wmap inj₂ u ⊛ c has coset ≈R u • c and kernel ≈S ε.
      nfl-inj₂-coset : ∀ (u : Word X) (c : Word X) → proj₁ (wmap inj₂ u ⊛ c) ≈R u • c
      nfl-inj₂-coset ε c = symR PB.left-unit
      nfl-inj₂-coset [ x ]ʷ c = reflR
      nfl-inj₂-coset (u₁ • u₂) c
        with wmap inj₂ u₂ ⊛ c | nfl-inj₂-coset u₂ c
      ... | (c₂ , _) | r₂
        with wmap inj₂ u₁ ⊛ c₂ | nfl-inj₂-coset u₁ c₂
      ... | (c₁ , _) | r₁
        = transR r₁ (transR (congR reflR r₂) (symR PB.assoc))

      nfl-inj₂-kernel : ∀ (u : Word X) (c : Word X) → proj₂ (wmap inj₂ u ⊛ c) ≈S ε
      nfl-inj₂-kernel ε c = reflS
      nfl-inj₂-kernel [ x ]ʷ c = reflS
      nfl-inj₂-kernel (u₁ • u₂) c
        with wmap inj₂ u₂ ⊛ c | nfl-inj₂-kernel u₂ c
      ... | (c₂ , k₂) | s₂
        with wmap inj₂ u₁ ⊛ c₂ | nfl-inj₂-kernel u₁ c₂
      ... | (_ , k₁) | s₁
        = transS (congS s₁ s₂) PB.left-unit

      -- The "~" relation on the output of nfl.
      -- nfl(w) = (coset : Word X, kernel : Word Y)
      -- (c, k) ~ (d, l) iff c ≈R d ∧ k ≈S l.
      _≈~_ : Word X × Word Y -> Word X × Word Y -> Set
      (c , k) ≈~ (d , l) = (c ≈R d) × (k ≈S l)

      -- nfl-cong : w ≈Γ v → nfl(w) ≈~ nfl(v)
      -- Proved simultaneously with the coset-monotone version.
      nfl-⊛-cong-coset : ∀ (w : Word (Y ⊎ X)) {c d : Word X}
        -> c ≈R d -> (w ⊛ c) ≈~ (w ⊛ d)
      nfl-⊛-cong-word : ∀ {w v : Word (Y ⊎ X)} (c : Word X)
        -> w ≈Γ v -> (w ⊛ c) ≈~ (v ⊛ c)

      nfl-⊛-cong-coset [ inj₁ y ]ʷ cd =
        cd , conjss-cong-coset cd [ y ]ʷ
      nfl-⊛-cong-coset [ inj₂ x ]ʷ cd =
        congR reflR cd , reflS
      nfl-⊛-cong-coset ε cd = cd , reflS
      nfl-⊛-cong-coset (w • v) {c} {d} cd
        with v ⊛ c | Eq.inspect (v ⊛_) c | v ⊛ d | Eq.inspect (v ⊛_) d
      ... | (c' , kv) | Eq.[ eqc ]' | (d' , lv) | Eq.[ eqd ]'
        with nfl-⊛-cong-coset v cd
      ... | (c'd' , kvlv)
        with Eq.subst₂ _≈~_ eqc eqd (c'd' , kvlv)
      ... | (c'd'' , kvlv')
        with w ⊛ c' | Eq.inspect (w ⊛_) c' | w ⊛ d' | Eq.inspect (w ⊛_) d'
      ... | (c'' , kw) | Eq.[ eqc2 ]' | (d'' , lw) | Eq.[ eqd2 ]'
        with nfl-⊛-cong-coset w c'd''
      ... | (c''d'' , kwlw)
        with Eq.subst₂ _≈~_ eqc2 eqd2 (c''d'' , kwlw)
      ... | result =
        proj₁ result , congS (proj₂ result) kvlv'

      nfl-⊛-cong-word c PB.refl = reflR , reflS
      nfl-⊛-cong-word c (PB.sym h) =
        let (a , b) = nfl-⊛-cong-word c h in symR a , symS b
      nfl-⊛-cong-word c (PB.trans h₁ h₂) =
        let (a₁ , b₁) = nfl-⊛-cong-word c h₁
            (a₂ , b₂) = nfl-⊛-cong-word c h₂
        in transR a₁ a₂ , transS b₁ b₂
      nfl-⊛-cong-word c (PB.cong {w₁} {v₁} {w₂} {v₂} h₁ h₂)
        with w₂ ⊛ c | v₂ ⊛ c | nfl-⊛-cong-word c h₂
      ... | (c'' , kw₂) | (c' , kv₂) | (r₂ , s₂)
        with w₁ ⊛ c'' | v₁ ⊛ c'' | nfl-⊛-cong-word c'' h₁
           | v₁ ⊛ c' | nfl-⊛-cong-coset v₁ r₂
      ... | (c₂' , kw₁) | (c₁'' , kv₁'') | (r₁ , s₁)
          | (c₁' , kv₁) | (r₁' , s₁')
        = transR r₁ r₁' , congS (transS s₁ s₁') s₂
      nfl-⊛-cong-word c (PB.assoc {W} {V} {U})
        with U ⊛ c
      ... | (c₁ , _)
        with V ⊛ c₁
      ... | (c₂ , _)
        with W ⊛ c₂
      ... | _
        = reflR , PB.assoc
      nfl-⊛-cong-word c (PB.left-unit {W})
        with W ⊛ c
      ... | _
        = reflR , PB.left-unit
      nfl-⊛-cong-word c (PB.right-unit {W})
        with W ⊛ c
      ... | _
        = reflR , PB.right-unit
      -- Kernel axiom: [u]ₗ ⊛ c = (c, conjss c u), [v]ₗ ⊛ c = (c, conjss c v), need conjss c u ≈S conjss c v
      nfl-⊛-cong-word c (PB.axiom (kernel {u} {v} su))
        rewrite nfl-kernel-eq u c | nfl-kernel-eq v c
        = reflR , conjss-cong-word c (axiomS su)
      -- Quotient axiom (split: correction = ε):
      --   [u]ᵣ ⊛ c ≈~ (ε • [v]ᵣ) ⊛ c via coset ≈R u•c≈R v•c and kernel ≈S ε≈S ε•ε≈S ε•kv
      nfl-⊛-cong-word c (PB.axiom (quotient {u} {v} ru))
        with wmap inj₂ u ⊛ c | nfl-inj₂-coset u c | nfl-inj₂-kernel u c
      ... | (c_u , k_u) | r_u | s_u
        with wmap inj₂ v ⊛ c | nfl-inj₂-coset v c | nfl-inj₂-kernel v c
      ... | (c_v , k_v) | r_v | s_v
        = transR r_u (transR (congR (axiomR ru) reflR) (symR r_v)) ,
          transS s_u (transS (symS PB.left-unit) (congS reflS (symS s_v)))
      -- Conjugation axiom:
      --   ([y]ₗ • [x]ᵣ) ⊛ c: first [x]ᵣ ⊛ c = ([x]ʷ•c, ε), then [y]ₗ ⊛ ([x]ʷ•c) = ([x]ʷ•c, conjss ([x]ʷ•c) [y]ʷ)
      --   ([x]ᵣ • [cc]ₗ) ⊛ c: first [cc]ₗ ⊛ c = (c, conjss c cc), then [x]ᵣ ⊛ c = ([x]ʷ•c, ε)... wait
      --   Actually ([x]ᵣ • [cc]ₗ) ⊛ c:
      --     [cc]ₗ ⊛ c = (c, conjss c (conj-corr x y))  — but this is from right fold
      --     Hmm wait, cc = conj-corr x y : Word Y, so [cc]ₗ = wmap inj₁ cc
      --     [cc]ₗ ⊛ c = (c, conjss c cc) since cc is a Y-word
      --     then [x]ᵣ ⊛ c = ([x]ʷ • c, ε)
      --     combined: ([x]ʷ • c, ε • conjss c cc) = ([x]ʷ • c, conjss c (conj-corr x y))
      --   Both sides give ([x]ʷ • c, conjss ([x]ʷ • c) [y]ʷ) = ([x]ʷ • c, conjss c (conj-corr x y))
      --   since conjss ([x]ʷ • c) [y]ʷ = conjss c (conjss [x]ʷ [y]ʷ) = conjss c ((conj-corr x *) [y]ʷ) = conjss c (conj-corr x y)
      nfl-⊛-cong-word c (PB.axiom (conjugation x y))
        rewrite nfl-kernel-eq (conj-corr x y) c
        = reflR , transS right-unitS (symS left-unitS)

    nfl-cong : ∀ {w v : Word (Y ⊎ X)} -> w ≈Γ v -> nfl w ≈~ nfl v
    nfl-cong h = nfl-⊛-cong-word ε h

    ----------------------------------------------------------------------
    -- The normal form and NFProperty'.
    ----------------------------------------------------------------------

    nf : Word (Y ⊎ X) -> NF-R × NF-S
    nf w = let (c , k) = nfl w in (nf-R c , nf-S k)

    nf-cong : ∀ {w v : Word (Y ⊎ X)} -> w ≈Γ v -> nf w ≡ nf v
    nf-cong {w} {v} h =
      let (cr , ks) = nfl-cong h
      in PW.≡×≡⇒≡ (nf-R-cong cr , nf-S-cong ks)

    nf-inj : ∀ {w v : Word (Y ⊎ X)} -> nf w ≡ nf v -> w ≈Γ v
    nf-inj {w} {v} eq =
      let (eqR , eqS) = PW.≡⇒≡×≡ eq
      in nfl-isInjective' (nf-R-inj eqR , nf-S-inj eqS)

    inv-nf : NF-R × NF-S -> Word (Y ⊎ X)
    inv-nf (a , b) = [ inv-R a ]ᵣ • [ inv-S b ]ₗ

    private
      f-star-cong : ∀ {w v : Word Y} -> w ≈S v -> (f-emb *) w ≈Γ (f-emb *) v
      f-star-cong h = Star-Congruence.lemma-f*-cong S Γ f-emb f-emb-wd h

    inv-nf∘nf=id : ∀ {w : Word (Y ⊎ X)} -> inv-nf (nf w) ≈Γ w
    inv-nf∘nf=id {w} =
      let (c , k) = nfl w
      in begin
          [ inv-R (nf-R c) ]ᵣ • [ inv-S (nf-S k) ]ₗ
        ≈⟨ congΓ ([]-cong inv-R∘nf-R=id) ([]-cong-l inv-S∘nf-S=id) ⟩
          [ c ]ᵣ • [ k ]ₗ
        ≈⟨ Eq.subst (\ □ -> [ c ]ᵣ • □ ≈Γ w)
                    (wconcatmap-[f]ʷ {f = inj₁} k) ⁻¹nfl-nfl=id ⟩
          w
        ∎
        where open SR word-setoid-Γ

    nfp' : PP.NFProperty' Γ
    nfp' = record
      { NF = NF-R × NF-S
      ; nf = nf
      ; nf-cong = nf-cong
      ; inv-nf = inv-nf
      ; inv-nf∘nf=id = inv-nf∘nf=id
      }
