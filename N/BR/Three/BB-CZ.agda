{-# OPTIONS  --safe #-}
{-# OPTIONS  --call-by-name #-}
{-# OPTIONS --termination-depth=4 #-}
open import Level using (0ℓ)

open import Relation.Binary using (Rel)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Binary.Morphism.Definitions using (Homomorphic₂)
open import Relation.Binary.PropositionalEquality using (_≡_ ; _≢_ ; inspect ; setoid ; module ≡-Reasoning ; _≗_) renaming ([_] to [_]')
import Relation.Binary.Reasoning.Setoid as SR
import Relation.Binary.PropositionalEquality as Eq
open import Relation.Nullary.Decidable using (yes ; no)


open import Function using (_∘_ ; id)
open import Function.Definitions using (Injective)

open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂ ; map₁ ; ∃ ; Σ ; Σ-syntax)
open import Data.Product.Relation.Binary.Pointwise.NonDependent as PW using (≡×≡⇒≡ ; Pointwise ; ≡⇒≡×≡)
open import Data.Nat hiding (_^_ ; _+_ ; _*_)
open import Agda.Builtin.Nat using (_-_)
import Data.Nat as Nat
open import Data.Bool hiding (_<_ ; _≤_)
--open import Data.List using () hiding ([_] ; _++_ ; last ; head ; tail ; _∷ʳ_)
open import Data.Vec hiding ([_])
open import Data.Vec as V
open import Data.Fin hiding (_+_ ; _-_ ; _≤_ ; _<_)

open import Data.Maybe
open import Data.Sum using (_⊎_ ; inj₁ ; inj₂ ; [_,_] ; [_,_]′)
open import Data.Unit using (⊤ ; tt)
open import Data.Empty using (⊥ ; ⊥-elim)

open import Word.Base as WB hiding (wfoldl ; _* ; _^'_)
open import Word.Properties
import Presentation.Base as PB
import Presentation.Properties as PP
open PP using (NFProperty ; NFProperty')
import Presentation.CosetNF as CA
import Presentation.Reidemeister-Schreier as RS
module RSF = RS.Star-Injective-Full.Reidemeister-Schreier-Full

open import Presentation.Construct.Base hiding (_*_ ; _⊕_)
import Presentation.Construct.Properties.SemiDirectProduct2 as SDP2
import Presentation.Construct.Properties.DirectProduct as DP
import Presentation.Groups.Cyclic as Cyclic


open import Data.Fin using (Fin ; toℕ ; suc ; zero ; fromℕ)
open import Data.Fin.Properties using (suc-injective ; toℕ-inject₁ ; toℕ-fromℕ)
import Data.Nat.Properties as NP
open import Presentation.GroupLike
open import Presentation.Tactics using ()
open import Data.Nat.Primality



module N.BR.Three.BB-CZ (p-2 : ℕ) (p-prime : Prime (2+ p-2))  where

private
  variable
    n : ℕ
    
pattern auto = Eq.refl

pattern ₀ = zero
pattern ₁ = suc ₀
pattern ₂ = suc ₁
pattern ₃ = suc ₂
pattern ₅ = 5
pattern ₆ = 6
pattern ₇ = 7
pattern ₈ = 8
pattern ₉ = 9
pattern ₁₀ = 10
pattern ₁₁ = 11
pattern ₁₂ = 12
pattern ₁₃ = 13
pattern ₁₄ = 14
pattern ₁₅ = 15

pattern ₁₊ ⱼ = suc ⱼ
pattern ₂₊ ⱼ = suc (suc ⱼ)
pattern ₃₊ ⱼ = suc (suc (suc ⱼ))
pattern ₄₊ ⱼ = suc (suc (suc (suc ⱼ)))

open import Zp.ModularArithmetic
open PrimeModulus p-2 p-prime
open import N.Cosets p-2 p-prime
open import N.Symplectic p-2 p-prime
open Symplectic renaming (M to ZM)
open import N.NF1-Sym p-2 p-prime
open import N.LM-Sym p-2 p-prime

open import N.Action p-2 p-prime
open import N.Action-Lemmas p-2 p-prime
open import Algebra.Properties.Ring (+-*-ring p-2)
open import N.NF2-Sym p-2 p-prime
open LM2


open import Zp.ModularArithmetic
open import N.Lemmas-2Qupit-Sym p-2 p-prime
open import N.Lemmas-2Qupit-Sym3 p-2 p-prime
open import N.NF2-Sym p-2 p-prime
--open Lemmas-2Q 2

open import N.NF1 p-2 p-prime
open import N.Ex-Sym p-2 p-prime
open import N.Ex-Sym1 p-2 p-prime
open import N.Ex-Sym2 p-2 p-prime
open import N.Ex-Sym3 p-2 p-prime
open import N.Ex-Sym4 p-2 p-prime hiding (lemma-Ex-S^ᵏ ; lemma-Ex-S^ᵏ↑)
--open import N.Ex-Sym5 p-2 p-prime hiding (module L0)
open import N.Ex-Sym2n p-2 p-prime
open import N.Ex-Sym3n p-2 p-prime
open import N.Ex-Sym4n p-2 p-prime
open import N.Ex-Sym4n2 p-2 p-prime
open import N.Ex-Sym4n3 p-2 p-prime


open import N.Lemma-Comm-n p-2 p-prime 0
import N.Lemma-Comm-n p-2 p-prime 1 as LCn1
open import N.Completeness1-Sym p-2 p-prime renaming (module Completeness to Cp1)
open Lemmas0a
open Lemmas0a1
open Lemmas0b
open Lemmas0c
open Lemmas-Sym
open Duality

open import N.Completeness1-Sym p-2 p-prime renaming (module Completeness to CP1) using ()
--open import N.Coset2-Update-Sym p-2 p-prime renaming (module Completeness to CP2) using ()
open import N.Lemmas4-Sym p-2 p-prime as L4
open import N.Lemmas-3Q p-2 p-prime
open import N.Pushing.DH p-2 p-prime
open import N.Duality p-2 p-prime
open import N.BR.Calculations p-2 p-prime
open import N.BR.Three.Lemmas p-2 p-prime
open import N.BR.Three.Lemmas2 p-2 p-prime
open import N.BR.Three.Lemmas3 p-2 p-prime hiding (module L02)
open import N.BR.Three.Lemmas4 p-2 p-prime
open import N.BR.Three.Lemmas5 p-2 p-prime
open import N.Embeding-2n p-2 p-prime 1 renaming (f* to emb ; by-emb' to lemma-cong⇣' ; by-emb to lemma-cong⇣ )

open PB (3 QRel,_===_)
open PP (3 QRel,_===_)
-- module B2 = PB (2 QRel,_===_)
-- module P2 = PP (2 QRel,_===_)
-- module B1 = PB (1 QRel,_===_)
-- module P1 = PP (1 QRel,_===_)
open SR word-setoid
open Pattern-Assoc
open Lemmas0 1
module L02 = Lemmas0 2
open Lemmas-2Q 1
--module L2Q0 = Lemmas-2Q 0
open Sym0-Rewriting 2
open Rewriting-Powers 2
open Rewriting-Swap 2
open Rewriting-Swap0 2
open Symplectic-GroupLike
open Basis-Change _ (3 QRel,_===_) grouplike
open import N.EX-Rewriting p-2 p-prime
open Rewriting-EX 2
open Homo 2 renaming (lemma-f* to lemma-f*-EX)
open Commuting-Symplectic 1
open import Data.List hiding (reverse)
open import N.BR.Two.Lemmas p-2 p-prime hiding (sa)
open import N.BR.Two.D p-2 p-prime hiding (dir-of)
open import N.BR.Three.DD-CZ p-2 p-prime renaming (dir-of to dir-of-dd)

infixl 9 _⇣
_⇣ : Word (Gen 2) -> Word (Gen 3)
_⇣ = emb

{-
aux-BB~DD : ∀ b d -> [ (₀ , b) ∷ (₀ , d) ∷ [] ]ᵛᵇ ≈ (H ↑ ↑ • Ex • Ex ↑ • Ex) • ([ (₀ , d) ∷ (₀ , b) ∷ [] ]ᵛᵈ) • Ex • Ex ↑ • Ex • H ^ 3
aux-BB~DD b d = begin
  [ ab ∷ cd ∷ [] ]ᵛᵇ ≈⟨ cleft left-unit ⟩
  [ cd ]ᵇ ↑ • [ ab ]ᵇ ≈⟨ refl ⟩
  (Ex ↑ • CX'^ d ↑) • Ex • CX'^ b ≈⟨ sa ((□ • □ ^ 3 • □ ^ 2) • (□ • □ ^ 3 • □ ^ 2)) (□ ^ 2 • (□ ^ 2 • □) • □ • □ ^ 2 • (□ ^ 2 • □) • □) auto ⟩
  (Ex ↑ • H ↑) • (H ↑ ^ 2 • CZ^ d ↑) • H ↑ • (Ex • H) • (H ^ 2 • CZ^ b) • H ≈⟨ cright cong (lemma-cong↑ _ _ (L2Q0.lemma-semi-HH↓-CZ^k'  d )) (cright cong (rewrite-swap 100 auto) (cleft lemma-semi-HH↓-CZ^k' b)) ⟩
  (Ex ↑ • H ↑) • (CZ^ (- d) ↑ • H ↑ ^ 2) • H ↑ • (H ↑ • Ex) • (CZ^ (- b) • H ^ 2) • H ≈⟨ cright sa (□ ^ 3 • □ • □ ^ 2 • □ ^ 3 • □) (□ • □ ^ 4 • □ • □ • □ ^ 3) auto ⟩
  (Ex ↑ • H ↑) • CZ^ (- d) ↑ • H ↑ ^ 4 • Ex • CZ^ (- b) • H ^ 3 ≈⟨ cright cright trans (cleft axiom (cong↑ order-H)) left-unit ⟩
  (Ex ↑ • H ↑) • CZ^ (- d) ↑ • Ex • CZ^ (- b) • H ^ 3 ≈⟨ cleft rewrite-swap 100 auto ⟩
  (H ↑ ↑ • Ex ↑) • CZ^ (- d) ↑ • Ex • CZ^ (- b) • H ^ 3 ≈⟨ sa (□ ^ 2 • □ • □ ) (□ • □ ^ 2 • □) auto ⟩
  H ↑ ↑ • (Ex ↑ • CZ^ (- d) ↑) • Ex • CZ^ (- b) • H ^ 3 ≈⟨ cright cleft lemma-cong↑ _ _ (B2.sym (P2.word-comm (toℕ (- d)) 1 lemma-comm-Ex-CZ-n)) ⟩
  H ↑ ↑ • (CZ^ (- d) ↑ • Ex ↑) • Ex • CZ^ (- b) • H ^ 3 ≈⟨ sa (□ • □ ^ 2 • □ ^ 3) (□ ^ 2 • □ ^ 2 • □ ^ 2) auto ⟩
  (H ↑ ↑ • CZ^ (- d) ↑) • (Ex ↑ • Ex) • CZ^ (- b) • H ^ 3 ≈⟨ cright (cleft sym (by-ex {w = (EX.Ex • EX.Ex EX.↑ • EX.Ex • EX.Ex EX.↑)} {v = EX.Ex EX.↑ • EX.Ex} (rewrite-EX 100 auto))) ⟩
  (H ↑ ↑ • CZ^ (- d) ↑) • (Ex • Ex ↑ • Ex • Ex ↑) • CZ^ (- b) • H ^ 3 ≈⟨ sa (□ ^ 2 • □ ^ 4 • □ ^ 2) (□ • □ ^ 3 • (□ ^ 2 • □) • □) auto ⟩
  H ↑ ↑ • (CZ^ (- d) ↑ • (Ex • Ex ↑)) • ((Ex • Ex ↑) • CZ^ (- b)) • H ^ 3 ≈⟨ cright cong (sym (aux-[Ex-Ex↑]-CZ^k (- d))) (cleft aux-[Ex-Ex↑]-CZ^k (- b)) ⟩
  H ↑ ↑ • ((Ex • Ex ↑) • CZ^ (- d)) • (CZ^ (- b) ↑ • Ex • Ex ↑) • H ^ 3 ≈⟨ sa (□ • (□ ^ 2 • □) • □ ^ 3 • □) (□ ^ 3 • □ • □ • □ ^ 3) auto ⟩
  (H ↑ ↑ • Ex • Ex ↑) • CZ^ (- d) • CZ^ (- b) ↑ • Ex • Ex ↑ • H ^ 3 ≈⟨ cright cright cright (sym (by-ex {w = (EX.Ex EX.↑ • EX.Ex • EX.Ex EX.↑ • EX.Ex • EX.H ^ 3)} {v = EX.Ex • EX.Ex EX.↑ • EX.H ^ 3} (rewrite-EX 100 auto)) ) ⟩
  (H ↑ ↑ • Ex • Ex ↑) • CZ^ (- d) • CZ^ (- b) ↑ • Ex ↑ • Ex • Ex ↑ • Ex • H ^ 3 ≈⟨ cright cright sym assoc ⟩
  (H ↑ ↑ • Ex • Ex ↑) • CZ^ (- d) • (CZ^ (- b) • Ex) ↑ • Ex • Ex ↑ • Ex • H ^ 3 ≈⟨ cong (sym (by-ex {w = ((EX.H EX.↑ EX.↑ • EX.Ex • EX.Ex EX.↑ • EX.Ex) • EX.Ex)} {v = EX.H EX.↑ EX.↑ • EX.Ex • EX.Ex EX.↑} (rewrite-EX 100 auto)) ) (cright (cleft lemma-cong↑ _ _ (P2.word-comm (toℕ (- b)) 1 lemma-comm-Ex-CZ-n))) ⟩
  ((H ↑ ↑ • Ex • Ex ↑ • Ex) • Ex) • CZ^ (- d) • (Ex • CZ^ (- b)) ↑ • Ex • Ex ↑ • Ex • H ^ 3 ≈⟨ sym (sa (□ • (□ ^ 2 • □)• □) (□ ^ 2 • □ • □ ^ 2) auto) ⟩
  (H ↑ ↑ • Ex • Ex ↑ • Ex) • ([ cd ]ᵈ • [ ab ]ᵈ ↑) • Ex • Ex ↑ • Ex • H ^ 3 ≈⟨ cright cleft cright sym right-unit ⟩
  (H ↑ ↑ • Ex • Ex ↑ • Ex) • ([ cd ∷ ab ∷ [] ]ᵛᵈ) • Ex • Ex ↑ • Ex • H ^ 3 ∎
  where
  ab = (₀ , b)
  cd = (₀ , d)
-}



BB~DD' : ∀ b cd -> let ab = (₀ , b) in [ ab ∷ cd ∷ [] ]ᵛᵇ ≈ (H ↑ ↑ • Ex • Ex ↑ • Ex) • ([ reverse (ab ∷ cd ∷ []) ]ᵛᵈ) • Ex • Ex ↑ • Ex • H ^ 3

BB~DD' b cd@(c@₀ , d) = begin
  [ ab ∷ cd ∷ [] ]ᵛᵇ ≈⟨ cleft left-unit ⟩
  [ cd ]ᵇ ↑ • [ ab ]ᵇ ≈⟨ refl ⟩
  (Ex ↑ • CX'^ d ↑) • Ex • CX'^ b ≈⟨ sa ((□ • □ ^ 3 • □ ^ 2) • (□ • □ ^ 3 • □ ^ 2)) (□ ^ 2 • (□ ^ 2 • □) • □ • □ ^ 2 • (□ ^ 2 • □) • □) auto ⟩
  (Ex ↑ • H ↑) • (H ↑ ^ 2 • CZ^ d ↑) • H ↑ • (Ex • H) • (H ^ 2 • CZ^ b) • H ≈⟨ cright cong (lemma-cong↑ _ _ (L2Q0.lemma-semi-HH↓-CZ^k'  d )) (cright cong (rewrite-swap 100 auto) (cleft lemma-semi-HH↓-CZ^k' b)) ⟩
  (Ex ↑ • H ↑) • (CZ^ (- d) ↑ • H ↑ ^ 2) • H ↑ • (H ↑ • Ex) • (CZ^ (- b) • H ^ 2) • H ≈⟨ cright sa (□ ^ 3 • □ • □ ^ 2 • □ ^ 3 • □) (□ • □ ^ 4 • □ • □ • □ ^ 3) auto ⟩
  (Ex ↑ • H ↑) • CZ^ (- d) ↑ • H ↑ ^ 4 • Ex • CZ^ (- b) • H ^ 3 ≈⟨ cright cright trans (cleft axiom (cong↑ order-H)) left-unit ⟩
  (Ex ↑ • H ↑) • CZ^ (- d) ↑ • Ex • CZ^ (- b) • H ^ 3 ≈⟨ cleft rewrite-swap 100 auto ⟩
  (H ↑ ↑ • Ex ↑) • CZ^ (- d) ↑ • Ex • CZ^ (- b) • H ^ 3 ≈⟨ sa (□ ^ 2 • □ • □ ) (□ • □ ^ 2 • □) auto ⟩
  H ↑ ↑ • (Ex ↑ • CZ^ (- d) ↑) • Ex • CZ^ (- b) • H ^ 3 ≈⟨ cright cleft lemma-cong↑ _ _ (B2.sym (P2.word-comm (toℕ (- d)) 1 lemma-comm-Ex-CZ-n)) ⟩
  H ↑ ↑ • (CZ^ (- d) ↑ • Ex ↑) • Ex • CZ^ (- b) • H ^ 3 ≈⟨ sa (□ • □ ^ 2 • □ ^ 3) (□ ^ 2 • □ ^ 2 • □ ^ 2) auto ⟩
  (H ↑ ↑ • CZ^ (- d) ↑) • (Ex ↑ • Ex) • CZ^ (- b) • H ^ 3 ≈⟨ cright (cleft sym (by-ex {w = (EX.Ex • EX.Ex EX.↑ • EX.Ex • EX.Ex EX.↑)} {v = EX.Ex EX.↑ • EX.Ex} (rewrite-EX 100 auto))) ⟩
  (H ↑ ↑ • CZ^ (- d) ↑) • (Ex • Ex ↑ • Ex • Ex ↑) • CZ^ (- b) • H ^ 3 ≈⟨ sa (□ ^ 2 • □ ^ 4 • □ ^ 2) (□ • □ ^ 3 • (□ ^ 2 • □) • □) auto ⟩
  H ↑ ↑ • (CZ^ (- d) ↑ • (Ex • Ex ↑)) • ((Ex • Ex ↑) • CZ^ (- b)) • H ^ 3 ≈⟨ cright cong (sym (aux-[Ex-Ex↑]-CZ^k (- d))) (cleft aux-[Ex-Ex↑]-CZ^k (- b)) ⟩
  H ↑ ↑ • ((Ex • Ex ↑) • CZ^ (- d)) • (CZ^ (- b) ↑ • Ex • Ex ↑) • H ^ 3 ≈⟨ sa (□ • (□ ^ 2 • □) • □ ^ 3 • □) (□ ^ 3 • □ • □ • □ ^ 3) auto ⟩
  (H ↑ ↑ • Ex • Ex ↑) • CZ^ (- d) • CZ^ (- b) ↑ • Ex • Ex ↑ • H ^ 3 ≈⟨ cright cright cright (sym (by-ex {w = (EX.Ex EX.↑ • EX.Ex • EX.Ex EX.↑ • EX.Ex • EX.H ^ 3)} {v = EX.Ex • EX.Ex EX.↑ • EX.H ^ 3} (rewrite-EX 100 auto)) ) ⟩
  (H ↑ ↑ • Ex • Ex ↑) • CZ^ (- d) • CZ^ (- b) ↑ • Ex ↑ • Ex • Ex ↑ • Ex • H ^ 3 ≈⟨ cright cright sym assoc ⟩
  (H ↑ ↑ • Ex • Ex ↑) • CZ^ (- d) • (CZ^ (- b) • Ex) ↑ • Ex • Ex ↑ • Ex • H ^ 3 ≈⟨ cong (sym (by-ex {w = ((EX.H EX.↑ EX.↑ • EX.Ex • EX.Ex EX.↑ • EX.Ex) • EX.Ex)} {v = EX.H EX.↑ EX.↑ • EX.Ex • EX.Ex EX.↑} (rewrite-EX 100 auto)) ) (cright (cleft lemma-cong↑ _ _ (P2.word-comm (toℕ (- b)) 1 lemma-comm-Ex-CZ-n))) ⟩
  ((H ↑ ↑ • Ex • Ex ↑ • Ex) • Ex) • CZ^ (- d) • (Ex • CZ^ (- b)) ↑ • Ex • Ex ↑ • Ex • H ^ 3 ≈⟨ sym (sa (□ • (□ ^ 2 • □)• □) (□ ^ 2 • □ • □ ^ 2) auto) ⟩
  (H ↑ ↑ • Ex • Ex ↑ • Ex) • ([ cd ]ᵈ • [ ab ]ᵈ ↑) • Ex • Ex ↑ • Ex • H ^ 3 ≈⟨ cright cleft cright sym right-unit ⟩
  (H ↑ ↑ • Ex • Ex ↑ • Ex) • ([ cd ∷ ab ∷ [] ]ᵛᵈ) • Ex • Ex ↑ • Ex • H ^ 3 ∎
  where
  ab = (₀ , b)


BB~DD' b cd@(c@(₁₊ _) , d) = begin
  [ ab ∷ cd ∷ [] ]ᵛᵇ ≈⟨ cleft left-unit ⟩
  ([ c , d ]ᵇ ↑) • [ ab ]ᵇ ≈⟨ sym (cong assoc refl) ⟩
  ([ ₀ , c ]ᵇ ↑ • H ↑ ↑ • S^ -d/c ↑ ↑) • [ ab ]ᵇ ≈⟨ assoc ⟩
  [ ₀ , c ]ᵇ ↑ • (H ↑ ↑ • S^ -d/c ↑ ↑) • [ ab ]ᵇ ≈⟨ cright sym (comm-bbox-w↑↑ ab (H • S^ -d/c)) ⟩
  [ ₀ , c ]ᵇ ↑ • [ ab ]ᵇ • H ↑ ↑ • S^ -d/c ↑ ↑ ≈⟨ sym assoc ⟩
  ([ ₀ , c ]ᵇ ↑ • [ ab ]ᵇ) • H ↑ ↑ • S^ -d/c ↑ ↑ ≈⟨ cleft (cleft sym left-unit) ⟩
  ((ε • [ ₀ , c ]ᵇ ↑) • [ ab ]ᵇ) • H ↑ ↑ • S^ -d/c ↑ ↑ ≈⟨ cleft BB~DD' b ((₀ , c)) ⟩
  ((H ↑ ↑ • Ex • Ex ↑ • Ex) • ((Ex • CZ^ (- c)) • [ ab ]ᵈ ↑ • ε) • Ex • Ex ↑ • Ex • H ^ 3) • H ↑ ↑ • S^ -d/c ↑ ↑ ≈⟨ cleft cright (cleft cright right-unit) ⟩
  ((H ↑ ↑ • Ex • Ex ↑ • Ex) • ((Ex • CZ^ (- c)) • [ ab ]ᵈ ↑) • Ex • Ex ↑ • Ex • H ^ 3) • H ↑ ↑ • S^ -d/c ↑ ↑ ≈⟨ sa (□ ^ 6 • □ ^ 2) (□ • □ • □ • □ • □ • □ ^ 2 • □) auto ⟩
  (H ↑ ↑ • Ex • Ex ↑ • Ex) • ((Ex • CZ^ (- c)) • [ ab ]ᵈ ↑) • Ex • Ex ↑ • Ex • (H ^ 3 • H ↑ ↑) • S^ -d/c ↑ ↑ ≈⟨ cright cright cright cright cright (cleft lemma-comm-Hᵏ-w↑ 3 (H ↑)) ⟩
  (H ↑ ↑ • Ex • Ex ↑ • Ex) • ((Ex • CZ^ (- c)) • [ ab ]ᵈ ↑) • Ex • Ex ↑ • Ex • (H ↑ ↑ • H ^ 3) • S^ -d/c ↑ ↑ ≈⟨ cright cright cright cright  sa (□ • □ ^ 2 • □) (□ ^ 2 • □ ^ 2) auto ⟩
  (H ↑ ↑ • Ex • Ex ↑ • Ex) • ((Ex • CZ^ (- c)) • [ ab ]ᵈ ↑) • Ex • Ex ↑ • (Ex • H ↑ ↑) • H ^ 3 • S^ -d/c ↑ ↑ ≈⟨ cright cright cright cright   cong (rewrite-swap 100 auto) (lemma-comm-Hᵏ-w↑ 3 (S^ -d/c ↑)) ⟩
  (H ↑ ↑ • Ex • Ex ↑ • Ex) • ((Ex • CZ^ (- c)) • [ ab ]ᵈ ↑) • Ex • Ex ↑ • (H ↑ ↑ • Ex) • S^ -d/c ↑ ↑ • H ^ 3 ≈⟨ cright cright cright   sa (□ • □ ^ 2 • □ ^ 2) (□ ^ 2 • □ ^ 2 • □) auto ⟩
  (H ↑ ↑ • Ex • Ex ↑ • Ex) • ((Ex • CZ^ (- c)) • [ ab ]ᵈ ↑) • Ex • (Ex ↑ • H ↑ ↑) • (Ex • S^ -d/c ↑ ↑) • H ^ 3 ≈⟨ cright cright cright cong (rewrite-swap 100 auto) (cleft lemma-comm-Ex-w↑↑ (S^ -d/c)) ⟩
  (H ↑ ↑ • Ex • Ex ↑ • Ex) • ((Ex • CZ^ (- c)) • [ ab ]ᵈ ↑) • Ex • (H ↑ • Ex ↑) • (S^ -d/c ↑ ↑ • Ex) • H ^ 3 ≈⟨ cright cright sa (□ • □ ^ 2 • □ ^ 2 • □) (□ ^ 2 • □ ^ 2 • □ ^ 2) auto ⟩
  (H ↑ ↑ • Ex • Ex ↑ • Ex) • ((Ex • CZ^ (- c)) • [ ab ]ᵈ ↑) • (Ex • H ↑) • (Ex ↑ • S^ -d/c ↑ ↑) • Ex • H ^ 3 ≈⟨ cright cright cong (rewrite-swap 100 auto) (cleft lemma-cong↑ _ _ (lemma-Ex-S^ᵏ↑ 0 -d/c)) ⟩
  (H ↑ ↑ • Ex • Ex ↑ • Ex) • ((Ex • CZ^ (- c)) • [ ab ]ᵈ ↑) • (H • Ex) • (S^ -d/c ↑ • Ex ↑) • Ex • H ^ 3 ≈⟨ cright cright sa (□ ^ 2 • □ ^ 2 • □) (□ ^ 3 • □ ^ 2) auto ⟩
  (H ↑ ↑ • Ex • Ex ↑ • Ex) • ((Ex • CZ^ (- c)) • [ ab ]ᵈ ↑) • (H • Ex • S^ -d/c ↑) • Ex ↑ • Ex • H ^ 3 ≈⟨ cright cright cleft cright lemma-Ex-S^ᵏ↑ 1 -d/c ⟩
  (H ↑ ↑ • Ex • Ex ↑ • Ex) • ((Ex • CZ^ (- c)) • [ ab ]ᵈ ↑) • (H • S^ -d/c • Ex) • Ex ↑ • Ex • H ^ 3 ≈⟨ cright sa (□ ^ 2 • □ ^ 3 • □) (□ ^ 4 • □ ^ 2) auto ⟩
  (H ↑ ↑ • Ex • Ex ↑ • Ex) • ((Ex • CZ^ (- c)) • [ ab ]ᵈ ↑ • (H • S^ -d/c)) • Ex • Ex ↑ • Ex • H ^ 3 ≈⟨ cright cleft cright sym (comm-hs-w↑ -d/c [ ab ]ᵈ) ⟩
  (H ↑ ↑ • Ex • Ex ↑ • Ex) • ((Ex • CZ^ (- c)) • (H • S^ -d/c) • [ ab ]ᵈ ↑) • Ex • Ex ↑ • Ex • H ^ 3 ≈⟨ cright cleft sa (□ ^ 2 • □ ^ 2 • □) (□ ^ 4 • □) auto ⟩
  (H ↑ ↑ • Ex • Ex ↑ • Ex) • ((Ex • CZ^ (- c) • H • S^ -d/c) • [ ab ]ᵈ ↑) • Ex • Ex ↑ • Ex • H ^ 3 ≈⟨ refl ⟩
  (H ↑ ↑ • Ex • Ex ↑ • Ex) • ([ cd ]ᵈ • [ ab ]ᵈ ↑) • Ex • Ex ↑ • Ex • H ^ 3 ≈⟨ cright cleft cright sym right-unit ⟩
  (H ↑ ↑ • Ex • Ex ↑ • Ex) • ([ cd ∷ ab ∷ [] ]ᵛᵈ) • Ex • Ex ↑ • Ex • H ^ 3 ∎
  where
  c⁻¹ = ((c , λ ()) ⁻¹) .proj₁
  -d/c = - d * c⁻¹
  ab = (₀ , b)


BB~DD : ∀ ab cd -> [ ab ∷ cd ∷ [] ]ᵛᵇ ≈ (H ↑ ↑ • Ex • Ex ↑ • Ex) • ([ cd ∷ ab ∷ [] ]ᵛᵈ) • Ex • Ex ↑ • Ex • H ^ 3

BB~DD ab@(a@₀ , b) cd@(c@₀ , d) = BB~DD' b cd
BB~DD ab@(a@₀ , b) cd@(c@(₁₊ _) , d) = BB~DD' b cd

BB~DD ab@(a@(₁₊ _) , b) cd@(c , d) = begin
  [ ab ∷ cd ∷ [] ]ᵛᵇ ≈⟨ refl ⟩
  (ε • [ c , d ]ᵇ ↑) • [ ab ]ᵇ ≈⟨ sa (□ • □ ^ 4) (□ ^ 3 • □ ^ 2) auto ⟩
  ((ε • [ c , d ]ᵇ ↑) • Ex • CX'^ a) • H ↑ • S^ -b/a ↑ ≈⟨ cleft BB~DD' a cd ⟩
  ((H ↑ ↑ • Ex • Ex ↑ • Ex) • ([ cd ∷ (₀ , a) ∷ [] ]ᵛᵈ) • Ex • Ex ↑ • Ex • H ^ 3) • H ↑ • S^ -b/a ↑ ≈⟨ sa ((□ • □ • □ ^ 4) • □ ^ 2) (□ ^ 2 • □ ^ 5 • □) auto ⟩
  ((H ↑ ↑ • Ex • Ex ↑ • Ex) • ([ cd ∷ (₀ , a) ∷ [] ]ᵛᵈ)) • (Ex • Ex ↑ • Ex • H ^ 3 • H ↑) • S^ -b/a ↑ ≈⟨ cright cleft (cright cright cright general-comm auto) ⟩
  ((H ↑ ↑ • Ex • Ex ↑ • Ex) • ([ cd ∷ (₀ , a) ∷ [] ]ᵛᵈ)) • (Ex • Ex ↑ • Ex • H ↑ • H ^ 3) • S^ -b/a ↑ ≈⟨ cright cleft by-ex {w = (EX.Ex • EX.Ex EX.↑ • EX.Ex • EX.H EX.↑ • EX.H ^ 3)} {v = EX.H EX.↑ • EX.Ex • EX.Ex EX.↑ • EX.Ex • EX.H ^ 3} (rewrite-EX 100 auto) ⟩
  ((H ↑ ↑ • Ex • Ex ↑ • Ex) • ([ cd ∷ (₀ , a) ∷ [] ]ᵛᵈ)) • (H ↑ • Ex • Ex ↑ • Ex • H ^ 3) • S^ -b/a ↑ ≈⟨ cright sa (□ ^ 5 • □) (□ ^ 4 • □ ^ 2) auto ⟩
  ((H ↑ ↑ • Ex • Ex ↑ • Ex) • ([ cd ∷ (₀ , a) ∷ [] ]ᵛᵈ)) • (H ↑ • Ex • Ex ↑ • Ex) • H ^ 3 • S^ -b/a ↑ ≈⟨ cright cright lemma-comm-Hᵏ-w↑ 3 (S^ -b/a) ⟩
  ((H ↑ ↑ • Ex • Ex ↑ • Ex) • ([ cd ∷ (₀ , a) ∷ [] ]ᵛᵈ)) • (H ↑ • Ex • Ex ↑ • Ex) • S^ -b/a ↑ • H ^ 3 ≈⟨ cright sa (□ ^ 4 • □ ^ 2) (□ ^ 3 • □ ^ 2 • □) auto ⟩
  ((H ↑ ↑ • Ex • Ex ↑ • Ex) • ([ cd ∷ (₀ , a) ∷ [] ]ᵛᵈ)) • (H ↑ • Ex • Ex ↑) • (Ex • S^ -b/a ↑) • H ^ 3 ≈⟨ cright (cright cleft lemma-Ex-S^ᵏ↑ 1 -b/a) ⟩
  ((H ↑ ↑ • Ex • Ex ↑ • Ex) • ([ cd ∷ (₀ , a) ∷ [] ]ᵛᵈ)) • (H ↑ • Ex • Ex ↑) • (S^ -b/a • Ex) • H ^ 3 ≈⟨ cright sa (□ ^ 3 • □ ^ 2 • □) (□ ^ 2 • □ ^ 2 • □ ^ 2) auto ⟩
  ((H ↑ ↑ • Ex • Ex ↑ • Ex) • ([ cd ∷ (₀ , a) ∷ [] ]ᵛᵈ)) • (H ↑ • Ex) • (Ex ↑ • S^ -b/a) • Ex • H ^ 3 ≈⟨ cright (cright cleft sym (lemma-comm-Sᵏ-w↑ (toℕ -b/a) Ex)) ⟩
  ((H ↑ ↑ • Ex • Ex ↑ • Ex) • ([ cd ∷ (₀ , a) ∷ [] ]ᵛᵈ)) • (H ↑ • Ex) • (S^ -b/a • Ex ↑) • Ex • H ^ 3 ≈⟨ cright sa ((□ ^ 2) ^ 3) (□ • □ ^ 2 • □ ^ 3) auto ⟩
  ((H ↑ ↑ • Ex • Ex ↑ • Ex) • ([ cd ∷ (₀ , a) ∷ [] ]ᵛᵈ)) • H ↑ • (Ex • S^ -b/a) • Ex ↑ • Ex • H ^ 3 ≈⟨ cong (cright cong refl right-unit) (cright cleft lemma-Ex-S^ᵏ 1 -b/a) ⟩
  ((H ↑ ↑ • Ex • Ex ↑ • Ex) • ([ cd ]ᵈ • [ (₀ , a) ]ᵈ ↑)) • H ↑ • (S^ -b/a ↑ • Ex) • Ex ↑ • Ex • H ^ 3 ≈⟨ sa (□ ^ 3 • □ • □ ^ 2 • □) (□ • □ ^ 4 • □ ^ 2) auto ⟩
  (H ↑ ↑ • Ex • Ex ↑ • Ex) • ([ cd ]ᵈ • [ (₀ , a) ]ᵈ ↑ • H ↑ • S^ -b/a ↑) • Ex • Ex ↑ • Ex • H ^ 3 ≈⟨ cright cleft (cright trans assoc (sym right-unit)) ⟩
  (H ↑ ↑ • Ex • Ex ↑ • Ex) • ([ cd ∷ ab ∷ [] ]ᵛᵈ) • Ex • Ex ↑ • Ex • H ^ 3 ∎
  where
  a⁻¹ = ((a , λ ()) ⁻¹) .proj₁
  -b/a = - b * a⁻¹

aux-comm-w⇣-v↑↑ : ∀ w v -> w ⇣ • v ↑ ↑ ≈ v ↑ ↑ • w ⇣
aux-comm-w⇣-v↑↑ [ H-gen ]ʷ v = lemma-comm-H-w↑ (v ↑)
aux-comm-w⇣-v↑↑ [ S-gen ]ʷ v = lemma-comm-S-w↑ (v ↑)
aux-comm-w⇣-v↑↑ [ CZ-gen ]ʷ v = lemma-comm-CZ-w↑↑ v
aux-comm-w⇣-v↑↑ [ H-gen ↥ ]ʷ v = lemma-cong↑ _ _ (lemma-comm-H-w↑ v)
aux-comm-w⇣-v↑↑ [ S-gen ↥ ]ʷ v = lemma-cong↑ _ _ (lemma-comm-S-w↑ v)
aux-comm-w⇣-v↑↑ ε v = trans left-unit (sym right-unit)
aux-comm-w⇣-v↑↑ (w • w') v = begin
  (w • w') ⇣ • v ↑ ↑ ≈⟨ assoc ⟩
  w ⇣ • w' ⇣ • v ↑ ↑ ≈⟨ cright aux-comm-w⇣-v↑↑ w' v ⟩
  w ⇣ • v ↑ ↑ • w' ⇣ ≈⟨ sym assoc ⟩
  (w ⇣ • v ↑ ↑) • w' ⇣ ≈⟨ cleft aux-comm-w⇣-v↑↑ w v ⟩
  (v ↑ ↑ • w ⇣) • w' ⇣ ≈⟨ assoc ⟩
  v ↑ ↑ • (w • w') ⇣ ∎

aux-Ex-w⇣-Ex : ∀ w -> Ex • w ⇣ • Ex ≈ (Ex • w • Ex) ⇣
aux-Ex-w⇣-Ex [ H-gen ]ʷ = refl
aux-Ex-w⇣-Ex [ S-gen ]ʷ = refl
aux-Ex-w⇣-Ex [ CZ-gen ]ʷ = refl
aux-Ex-w⇣-Ex [ H-gen ↥ ]ʷ = refl
aux-Ex-w⇣-Ex [ S-gen ↥ ]ʷ = refl
aux-Ex-w⇣-Ex ε = refl
aux-Ex-w⇣-Ex (w • v) = begin
  Ex • (w • v) ⇣ • Ex ≈⟨ sa (□ • □ ^ 2 • □) (□ ^ 2 • □ ^ 2) auto ⟩
  (Ex • w ⇣) • v ⇣ • Ex ≈⟨ cright sym (trans (cleft rewrite-swap 100 auto) left-unit) ⟩
  (Ex • w ⇣) • (Ex • Ex) • v ⇣ • Ex ≈⟨ sa (□ ^ 2 • □ ^ 2 • □ ^ 2) (□ ^ 3 • □ ^ 3) auto ⟩
  (Ex • w ⇣ • Ex) • Ex • v ⇣ • Ex ≈⟨ cong (aux-Ex-w⇣-Ex w) (aux-Ex-w⇣-Ex v) ⟩
  (Ex • w • Ex) ⇣ • (Ex • v • Ex) ⇣ ≈⟨ sym (sa (□ ^ 2 • □ ^ 2 • □ ^ 2) (□ ^ 3 • □ ^ 3) auto) ⟩
  ((Ex • w) • (Ex • Ex) • v • Ex) ⇣ ≈⟨ lemma-cong⇣ {w = ((Ex • w) • (Ex • Ex) • v • Ex)} {((Ex • w) • ε • v • Ex)} (B2.cright B2.cleft lemma-order-Ex-n)  ⟩
  ((Ex • w) • ε • v • Ex) ⇣ ≈⟨ lemma-cong⇣ {w = ((Ex • w) • ε • v • Ex)}  {v = ((Ex • w) • v • Ex)} (B2.cright B2.left-unit)  ⟩
  ((Ex • w) • v • Ex) ⇣ ≈⟨ sa (□ ^ 2 • □ ^ 2) (□ • □ ^ 2 • □) auto ⟩
  (Ex • (w • v) • Ex) ⇣ ∎

aux-Ex↑-Ex-w↑ : ∀ w -> (Ex ↑ • Ex) • w ↑ ≈ w ⇣ • Ex ↑ • Ex
aux-Ex↑-Ex-w↑ [ H-gen ]ʷ = by-ex {w = ((EX.Ex EX.↑ • EX.Ex) • EX.H EX.↑)} {v = EX.H • EX.Ex EX.↑ • EX.Ex} (rewrite-EX 100 auto)
aux-Ex↑-Ex-w↑ [ S-gen ]ʷ = rewrite-swap 100 auto
aux-Ex↑-Ex-w↑ [ CZ-gen ]ʷ = rewrite-swap 100 auto
aux-Ex↑-Ex-w↑ [ H-gen ↥ ]ʷ = rewrite-swap 100 auto
aux-Ex↑-Ex-w↑ [ S-gen ↥ ]ʷ = rewrite-swap 100 auto
aux-Ex↑-Ex-w↑ ε = trans right-unit (sym left-unit)
aux-Ex↑-Ex-w↑ (w • v) = begin
  (Ex ↑ • Ex) • (w • v) ↑ ≈⟨ sa (□ ^ 2 • □ ^ 2) ((□ ^ 2 • □) • □) auto ⟩
  ((Ex ↑ • Ex) • w ↑) • v ↑ ≈⟨ cleft aux-Ex↑-Ex-w↑ w ⟩
  (w ⇣ • (Ex ↑ • Ex)) • v ↑ ≈⟨ assoc ⟩
  w ⇣ • (Ex ↑ • Ex) • v ↑ ≈⟨ cright aux-Ex↑-Ex-w↑ v ⟩
  w ⇣ • v ⇣ • (Ex ↑ • Ex) ≈⟨ sym assoc ⟩
  (w • v) ⇣ • Ex ↑ • Ex ∎


aux-vd'-of∘rev : vd'-of ∘ reverse ≗ reverse ∘ vd'-of
aux-vd'-of∘rev (x ∷ x₁ ∷ []) = auto


vb'-of : Vec B 2 -> Vec B 2
vb'-of = vd'-of

dir-of : Vec B 2 -> Word (Gen 2)
dir-of = dual ∘ dir-of-dd ∘ reverse

lemma-dir-and-vb' : ∀ (vb : Vec B 2) ->
  let
  dir = dir-of vb
  vb' = vb'-of vb
  in
  
  [ vb ]ᵛᵇ • CZ ↑ ≈ dir ⇣ • [ vb' ]ᵛᵇ

lemma-dir-and-vb' vb@(ab ∷ cd ∷ []) = begin
  [ vb ]ᵛᵇ • CZ ↑ ≈⟨ cleft BB~DD ab cd ⟩
  ((H ↑ ↑ • Ex • Ex ↑ • Ex) • ([ reverse vb ]ᵛᵈ) • Ex • Ex ↑ • Ex • H ^ 3) • CZ ↑ ≈⟨ sa (□ ^ 6 • □) (□ ^ 2 • □ ^ 5) auto ⟩
  ((H ↑ ↑ • Ex • Ex ↑ • Ex) • ([ reverse vb ]ᵛᵈ)) • Ex • Ex ↑ • Ex • H ^ 3 • CZ ↑ ≈⟨ cright cright cright cright general-comm auto ⟩
  ((H ↑ ↑ • Ex • Ex ↑ • Ex) • ([ reverse vb ]ᵛᵈ)) • Ex • Ex ↑ • Ex • CZ ↑ • H ^ 3 ≈⟨ cright (by-ex {w = (EX.Ex • EX.Ex EX.↑ • EX.Ex • EX.CZ EX.↑ • EX.H ^ 3)} {v = EX.CZ • EX.Ex • EX.Ex EX.↑ • EX.Ex • EX.H ^ 3} (rewrite-EX 100 auto)) ⟩
  ((H ↑ ↑ • Ex • Ex ↑ • Ex) • ([ reverse vb ]ᵛᵈ)) • CZ • Ex • Ex ↑ • Ex • H ^ 3 ≈⟨ sa (□ ^ 2 • □ ^ 2) (□ ^ 3 • □) auto ⟩
  ((H ↑ ↑ • Ex • Ex ↑ • Ex) • ([ reverse vb ]ᵛᵈ) • CZ) • Ex • Ex ↑ • Ex • H ^ 3 ≈⟨ cleft cright lemma-dir-and-vd' vd ⟩
  ((H ↑ ↑ • Ex • Ex ↑ • Ex) • (dir' ↑ • [ vd' ]ᵛᵈ)) • Ex • Ex ↑ • Ex • H ^ 3 ≈⟨ cleft sa (□ ^ 4 • □ ^ 2) (□ ^ 2 • (□ ^ 2 • □) • □) auto ⟩
  ((H ↑ ↑ • Ex) • ((Ex ↑ • Ex) • dir' ↑) • [ vd' ]ᵛᵈ) • Ex • Ex ↑ • Ex • H ^ 3 ≈⟨ cleft ( (cong (sym (lemma-comm-Ex-w↑↑ H)) (cleft aux-Ex↑-Ex-w↑ dir'))) ⟩
  ((Ex • H ↑ ↑) • (dir' ⇣ • (Ex ↑ • Ex)) • [ vd' ]ᵛᵈ) • Ex • Ex ↑ • Ex • H ^ 3 ≈⟨ cleft sa (□ ^ 2 • □ ^ 3 • □) (□ ^ 3 • □ ^ 2 • □) auto ⟩
  ((Ex • H ↑ ↑ • dir' ⇣) • (Ex ↑ • Ex) • [ vd' ]ᵛᵈ) • Ex • Ex ↑ • Ex • H ^ 3 ≈⟨ cleft cleft (cright sym (aux-comm-w⇣-v↑↑ dir' H)) ⟩
  ((Ex • dir' ⇣ • H ↑ ↑) • (Ex ↑ • Ex) • [ vd' ]ᵛᵈ) • Ex • Ex ↑ • Ex • H ^ 3 ≈⟨ cleft cleft sym assoc ⟩
  (((Ex • dir' ⇣) • H ↑ ↑) • (Ex ↑ • Ex) • [ vd' ]ᵛᵈ) • Ex • Ex ↑ • Ex • H ^ 3 ≈⟨ cleft (cleft (cright rewrite-swap 100 auto)) ⟩
  (((Ex • dir' ⇣) • (Ex • H ↑ ↑ • Ex)) • (Ex ↑ • Ex) • [ vd' ]ᵛᵈ) • Ex • Ex ↑ • Ex • H ^ 3 ≈⟨ sa (((□ ^ 2 • □ ^ 3) • □ ^ 2 • □) • □ ) (□ ^ 3 • □ ^ 4 • □ ^ 2) auto ⟩
  (Ex • dir' ⇣ • Ex) • ((H ↑ ↑ • Ex • Ex ↑ • Ex) • [ vd' ]ᵛᵈ • Ex • Ex ↑ • Ex • H ^ 3) ≈⟨ cleft aux-Ex-w⇣-Ex dir' ⟩
  (Ex • dir' • Ex) ⇣ • ((H ↑ ↑ • Ex • Ex ↑ • Ex) • [ vd' ]ᵛᵈ • Ex • Ex ↑ • Ex • H ^ 3) ≈⟨ cleft lemma-cong⇣ (B2.sym (lemma-Ex-dual dir'))  ⟩
  (dual dir') ⇣ • ((H ↑ ↑ • Ex • Ex ↑ • Ex) • [ vd' ]ᵛᵈ • Ex • Ex ↑ • Ex • H ^ 3) ≈⟨ cright cright cleft refl' (Eq.cong [_]ᵛᵈ (aux-vd'-of∘rev vb)) ⟩
  (dual dir') ⇣ • ((H ↑ ↑ • Ex • Ex ↑ • Ex) • [ reverse (vd'-of vb) ]ᵛᵈ • Ex • Ex ↑ • Ex • H ^ 3) ≈⟨ cright sym (BB~DD (V.head vb') (V.head (V.drop 1 vb'))) ⟩
  dir ⇣ • [ vb' ]ᵛᵇ ∎
  where
  dir = dir-of vb
  vb' = vb'-of vb
  vd = reverse vb
  dir' = dir-of-dd vd
  vd' = vd'-of vd

