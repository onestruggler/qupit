{-# OPTIONS_GHC -w #-}

import Data.List
import Prelude hiding (Right, Left)

import NewBoxRel hiding (main, eg_pcirs)
import qualified Cir2Tikz as CT
import Cir2Tikz (tikz_of_cir, tikz_of_rels, tikz_of_pcir, Circuit,
                  PositionSpec (PositionSpec),
                  Direction (Up , Down , Right , Left , LU , LD , RU , RD))

-- Write a group of relations to a .tikz file.
writeGroup :: FilePath -> [Rel] -> IO ()
writeGroup fname rels =
    writeFile (fname ++ ".tikz") (CT.tikz_of_rels $ map rel_trans rels)

-- The raw box_rels_* data in NewBoxRel.hs is already in circuit order
-- (leftmost gate = first applied), matching the tikz convention.
-- Only box_def is stored in matrix-mult order and needs reversal.

rev :: (String, Rel) -> Rel
rev = ro_rel . snd

------------------------------------------------------------------------
-- BoxRelations.agda — grouped by theorem
------------------------------------------------------------------------

-- Box definitions are in matrix-mult order → reverse to get circuit order.
rels_def :: [Rel]
rels_def = map rev box_def

------------------------------------------------------------------------
-- One qupit (module One)
------------------------------------------------------------------------

-- A←H : [x]ᵃ • H ≈ dir • [x']ᵃ
rels_AH :: [Rel]
rels_AH = map snd box_rels_HA

-- A←S : [x]ᵃ • S ≈ dir • [x']ᵃ
rels_AS :: [Rel]
rels_AS = map snd box_rels_SA

-- E←S : [b]ᵉ • S ≈ [b−1]ᵉ
rels_ES :: [Rel]
rels_ES = map snd box_rels_SE

------------------------------------------------------------------------
-- Two qupit (module Two)
------------------------------------------------------------------------

-- L←CZ : [l]ˡ • CZ ≈ dir • [l']ˡ
rels_LCZ :: [Rel]
rels_LCZ = map snd box_rels_CZL

-- B←H↑-S↑-S : [b]ᵇ • [g]ʷ ≈ dir • [b']ᵇ
-- box_rels_HB already includes box_rels_HB_dual_HD and box_rels_StB_dual_SbD.
rels_BH :: [Rel]
rels_BH = map snd box_rels_HB

-- D←H-S↑-S-CZ : [d]ᵈ • [g]ʷ ≈ Sᵉ • dir↑ • [d']ᵈ
rels_DH :: [Rel]
rels_DH = map snd (box_rels_HD ++ box_rels_SbD ++ box_rels_StD ++ box_rels_CZD)

------------------------------------------------------------------------
-- Three qupit (module Three)
------------------------------------------------------------------------

-- BB←CZ↑ : [vb]ᵛᵇ • CZ↑ ≈ dir⇣ • [vb']ᵛᵇ
rels_BBCZ :: [Rel]
rels_BBCZ = map snd box_rels_CZBB

-- B↑←CZ : [b]ᵇ↑ • CZ ≈ dir • [b]ᵇ↑
rels_BCZ :: [Rel]
rels_BCZ = map snd box_rels_CZBt

-- DD←CZ : [vd]ᵛᵈ • CZ ≈ dir↑ • [vd']ᵛᵈ
rels_DDCZ :: [Rel]
rels_DDCZ = map snd box_rels_CZDD

------------------------------------------------------------------------
-- lemma-S↓HCZH proof steps (N/Ex.agda, line 100)
-- Wire convention: 0 = bottom (↓/no decoration), 1 = top (↑), CZ acts on wires 0 and 1.
-- Circuits are in circuit order (leftmost gate = first applied to state).
------------------------------------------------------------------------

-- selinger-c11 axiom: CZ • H↓ • CZ ≡_s S⁻¹↓ • H↓ • S⁻¹↓ • CZ • H↓ • S⁻¹↓ • S⁻¹↑
rels_selinger :: [Rel]
rels_selinger = [
    Rel CT.Symplectic
        (Cir [CZ 0 1, H 0, CZ 0 1] (Spec ""))
        (Cir [Se 1 "p-1", Se 0 "p-1", H 0, CZ 0 1, Se 0 "p-1", H 0, Se 0 "p-1"] (Spec ""))
        (Spec "")]

-- Hadamard conjugation of S⁻¹: H • S⁻¹ • H ≡_s S • H • S
rels_hsh :: [Rel]
rels_hsh = [
    Rel CT.Symplectic
        (Cir [H 0, Se 0 "p-1", H 0] (Spec ""))
        (Cir [S 0, H 0, S 0]        (Spec ""))
        (Spec "")]

-- Main theorem: S • H • CZ • H ≡_s H • CZ • H • CZ • S↑ • S
rels_shczh :: [Rel]
rels_shczh = [
    Rel CT.Symplectic
        (Cir [H 0, CZ 0 1, H 0, S 0]              (Spec ""))
        (Cir [S 0, S 1, CZ 0 1, H 0, CZ 0 1, H 0] (Spec ""))
        (Spec "")]

-- Proof chain (vertical, top = RHS of theorem, bottom = LHS):
--   H•CZ•H•CZ•S↑•S
--     ≡_s  (selinger-c11 on inner CZ•H•CZ, then cancel S⁻¹↑•S↑ and S⁻¹↓•S)
--   H•S⁻¹↓•H↓•S⁻¹↓•CZ•H↓
--     ≡_s  (H•S⁻¹•H = S•H•S, then cancel S•S⁻¹)
--   S•H•CZ•H
proof_shczh :: [(CT.Circuit, PositionSpec)]
proof_shczh = map pcir_trans
    [ (Cir [S 0, S 1, CZ 0 1, H 0, CZ 0 1, H 0]            (Spec ""), PositionSpec Down "\\equiv_s")
    , (Cir [H 0, CZ 0 1, Se 0 "p-1", H 0, Se 0 "p-1", H 0] (Spec ""), PositionSpec Down "\\equiv_s")
    , (Cir [H 0, CZ 0 1, H 0, S 0]                          (Spec ""), PositionSpec Down "")
    ]

------------------------------------------------------------------------
-- Big Project: Proof chains for all box relations
-- Pattern: show (1) LHS, (2) expanded box definition, (3) RHS.
-- Box defs in circuit order (reversed from matrix-mult order in box_def):
--   A[0b]  = [Mul[b]]
--   A[ab]  = [Se -b/a, H, Mul[a]]          (a≠0)
--   E[b]   = [Se -b]
--   D[0b]  = [CZe(1,0,-b), Ex]
--   D[ab]  = [Se -b/a, H, CZe(1,0,-a), Ex] (a≠0)
--   B[0b]  = [CXe(1,0,b), Ex]
--   B[ab]  = [Se(1,-b/a), H(1), CXe(1,0,a), Ex] (a≠0)
------------------------------------------------------------------------

-- E←S: S•E[b] = E[b−1]
chain_se :: [(CT.Circuit, PositionSpec)]
chain_se = map pcir_trans
  [ (Cir [S 0, E 0 "{b}"]    (Spec ""), PositionSpec Down "=")
  , (Cir [S 0, Se 0 "{-b}"]  (Spec ""), PositionSpec Down "=")
  , (Cir [Se 0 "{1-b}"]      (Spec ""), PositionSpec Down "=")
  , (Cir [E 0 "{b-1}"]       (Spec ""), PositionSpec Down "")
  ]

-- A←H: H•A[0b] = A[b0]
chain_ah_0b :: [(CT.Circuit, PositionSpec)]
chain_ah_0b = map pcir_trans
  [ (Cir [H 0, A 0 "{0b}"] (Spec ""), PositionSpec Down "=")
  , (Cir [H 0, Mul 0 "b"]  (Spec ""), PositionSpec Down "=")
  , (Cir [A 0 "{b0}"]      (Spec ""), PositionSpec Down "")
  ]

-- A←H: H•A[a0] = A[0,−a]
--   expand A[a0]=M[a]·H  →  H•H•M[a]  ≡_s[HHM] M[-a]  =fold A[0,-a]
chain_ah_a0 :: [(CT.Circuit, PositionSpec)]
chain_ah_a0 = map pcir_trans
  [ (Cir [H 0, A 0 "{a0}"]       (Spec ""), PositionSpec Down "=")
  , (Cir [H 0, H 0, Mul 0 "a"]   (Spec ""), PositionSpec Down "\\equiv_s")
  , (Cir [Mul 0 "-a"]            (Spec ""), PositionSpec Down "=")
  , (Cir [A 0 "{0,-a}"]          (Spec ""), PositionSpec Down "")
  ]

-- A←H: H•A[ab] = S^{1/(ab)}•A[b,−a]
chain_ah_ab :: [(CT.Circuit, PositionSpec)]
chain_ah_ab = map pcir_trans
  [ (Cir [H 0, A 0 "{ab}"]                        (Spec ""), PositionSpec Down "=")
  , (Cir [H 0, Se 0 "{-b/a}", H 0, Mul 0 "a"]     (Spec ""), PositionSpec Down "\\equiv_s")
  , (Cir [Se 0 "{1/(ab)}", A 0 "{b,-a}"]           (Spec ""), PositionSpec Down "")
  ]

-- A←S: S•A[0b] = S^{1/b^2}•A[0b]
chain_sa_0b :: [(CT.Circuit, PositionSpec)]
chain_sa_0b = map pcir_trans
  [ (Cir [S 0, A 0 "{0b}"]             (Spec ""), PositionSpec Down "=")
  , (Cir [S 0, Mul 0 "b"]              (Spec ""), PositionSpec Down "\\equiv_s")
  , (Cir [A 0 "{0b}", Se 0 "{1/b^2}"]  (Spec ""), PositionSpec Down "")
  ]

-- A←S: S•A[ab] = A[a,b−a]
chain_sa_ab :: [(CT.Circuit, PositionSpec)]
chain_sa_ab = map pcir_trans
  [ (Cir [S 0, A 0 "{ab}"]                        (Spec ""), PositionSpec Down "=")
  , (Cir [S 0, Se 0 "{-b/a}", H 0, Mul 0 "a"]     (Spec ""), PositionSpec Down "=")
  , (Cir [Se 0 "{(a-b)/a}", H 0, Mul 0 "a"]       (Spec ""), PositionSpec Down "=")
  , (Cir [A 0 "{a,b-a}"]                          (Spec ""), PositionSpec Down "")
  ]

-- D←H: H↓•D[00] = D[00]•H↑   (key: H↓•Ex = Ex•H↑)
chain_hd_00 :: [(CT.Circuit, PositionSpec)]
chain_hd_00 = map pcir_trans
  [ (Cir [H 0, D 0 "{00}"]    (Spec ""), PositionSpec Down "=")
  , (Cir [H 0, Ex 0]          (Spec ""), PositionSpec Down "\\equiv_s")
  , (Cir [Ex 0, H 1]          (Spec ""), PositionSpec Down "=")
  , (Cir [D 0 "{00}", H 1]    (Spec ""), PositionSpec Down "")
  ]

-- D←H: H↓•D[0b] = D[b0]
chain_hd_0b :: [(CT.Circuit, PositionSpec)]
chain_hd_0b = map pcir_trans
  [ (Cir [H 0, D 0 "{0b}"]             (Spec ""), PositionSpec Down "=")
  , (Cir [H 0, CZe 1 0 "{-b}", Ex 0]  (Spec ""), PositionSpec Down "=")
  , (Cir [D 0 "{b0}"]                  (Spec ""), PositionSpec Down "")
  ]

-- D←H: H↓•D[a0] = H^2↑•D[0,−a]
--   expand D[a0] → CZ^{-a}·H² =[HH-CZ] H²·CZ^a =[Ex-slide H²] (across Ex) → fold
chain_hd_a0 :: [(CT.Circuit, PositionSpec)]
chain_hd_a0 = map pcir_trans
  [ (Cir [H 0, D 0 "{a0}"]                   (Spec ""), PositionSpec Down "=")
  , (Cir [H 0, H 0, CZe 1 0 "{-a}", Ex 0]    (Spec ""), PositionSpec Down "\\equiv_s")
  , (Cir [CZe 1 0 "a", H 0, H 0, Ex 0]       (Spec ""), PositionSpec Down "\\equiv_s")
  , (Cir [CZe 1 0 "a", Ex 0, H 1, H 1]       (Spec ""), PositionSpec Down "=")
  , (Cir [D 0 "{0,-a}", He 1 "2"]            (Spec ""), PositionSpec Down "")
  ]

-- D←H: H↓•D[ab] = Mul↑[b/a]•S↑[b/a]•D[b,−a]
chain_hd_ab :: [(CT.Circuit, PositionSpec)]
chain_hd_ab = map pcir_trans
  [ (Cir [H 0, D 0 "{ab}"]                                       (Spec ""), PositionSpec Down "=")
  , (Cir [H 0, Se 0 "{-b/a}", H 0, CZe 1 0 "{-a}", Ex 0]        (Spec ""), PositionSpec Down "\\equiv_s")
  , (Cir [D 0 "{b,-a}", Se 1 "{b/a}", Mul 1 "{b/a}"]            (Spec ""), PositionSpec Down "")
  ]

-- D←S↓: S↓•D[0b] = D[0b]•S↑
--   expand → S past CZ [comm-CZ-S] → S↓ across Ex → S↑ [Ex-slide] → fold
chain_sd_0b :: [(CT.Circuit, PositionSpec)]
chain_sd_0b = map pcir_trans
  [ (Cir [S 0, D 0 "{0b}"]            (Spec ""), PositionSpec Down "=")
  , (Cir [S 0, CZe 1 0 "{-b}", Ex 0]  (Spec ""), PositionSpec Down "\\equiv_s")
  , (Cir [CZe 1 0 "{-b}", S 0, Ex 0]  (Spec ""), PositionSpec Down "\\equiv_s")
  , (Cir [CZe 1 0 "{-b}", Ex 0, S 1]  (Spec ""), PositionSpec Down "=")
  , (Cir [D 0 "{0b}", S 1]            (Spec ""), PositionSpec Down "")
  ]

-- D←S↓: S↓•D[ab] = D[a,b−a]
chain_sd_ab :: [(CT.Circuit, PositionSpec)]
chain_sd_ab = map pcir_trans
  [ (Cir [S 0, D 0 "{ab}"]                                   (Spec ""), PositionSpec Down "=")
  , (Cir [S 0, Se 0 "{-b/a}", H 0, CZe 1 0 "{-a}", Ex 0]    (Spec ""), PositionSpec Down "=")
  , (Cir [Se 0 "{(a-b)/a}", H 0, CZe 1 0 "{-a}", Ex 0]      (Spec ""), PositionSpec Down "=")
  , (Cir [D 0 "{a,b-a}"]                                     (Spec ""), PositionSpec Down "")
  ]

-- D←S↑: S↑•D[ab] = D[ab]•S↓
--   expand → S↑ commutes through bottom-wire gates [comm-S↑ / comm-CZ-S↑]
--        → S↑ across Ex → S↓ [Ex-slide] → fold
chain_std :: [(CT.Circuit, PositionSpec)]
chain_std = map pcir_trans
  [ (Cir [S 1, D 0 "{ab}"]                                 (Spec ""), PositionSpec Down "=")
  , (Cir [S 1, Se 0 "{-b/a}", H 0, CZe 1 0 "{-a}", Ex 0]   (Spec ""), PositionSpec Down "\\equiv_s")
  , (Cir [Se 0 "{-b/a}", H 0, CZe 1 0 "{-a}", S 1, Ex 0]   (Spec ""), PositionSpec Down "\\equiv_s")
  , (Cir [Se 0 "{-b/a}", H 0, CZe 1 0 "{-a}", Ex 0, S 0]   (Spec ""), PositionSpec Down "=")
  , (Cir [D 0 "{ab}", S 0]                                 (Spec ""), PositionSpec Down "")
  ]

-- D←CZ: CZ•D[0b] = D[0,b−1]   (key: CZ•CZ^{−b} = CZ^{1−b})
chain_czd_0b :: [(CT.Circuit, PositionSpec)]
chain_czd_0b = map pcir_trans
  [ (Cir [CZ 0 1, D 0 "{0b}"]             (Spec ""), PositionSpec Down "=")
  , (Cir [CZ 0 1, CZe 1 0 "{-b}", Ex 0]  (Spec ""), PositionSpec Down "=")
  , (Cir [CZe 1 0 "{1-b}", Ex 0]         (Spec ""), PositionSpec Down "=")
  , (Cir [D 0 "{0,b-1}"]                 (Spec ""), PositionSpec Down "")
  ]

-- D←CZ: CZ•D[ab] = S^a↓•H↑•S^{−1/a}↑•H^3↑•D[a,b−1]
--   expand → CZ past S^{-b/a} [comm-CZ-S] → CZ·H·CZ core [aux-CZ-H-CZ]
--        + Ex-slides & CX↔CZ cleanup → fold
-- D←CZ, a≠0: fully inlined to axioms (N/BR/Two/D.agda:249).
-- CX'^{-a} expanded as H³·CZ^{-a}·H.
chain_czd_ab :: [(CT.Circuit, PositionSpec)]
chain_czd_ab = map pcir_trans
  [ (Cir [CZ 0 1, D 0 "{ab}"]                                                                 (Spec ""), PositionSpec Down "=")
  , (Cir [CZ 0 1, Se 0 "{-b/a}", H 0, CZe 1 0 "{-a}", Ex 0]                                   (Spec ""), PositionSpec Down "\\equiv_s")
  , (Cir [Se 0 "{-b/a}", CZ 0 1, H 0, CZe 1 0 "{-a}", Ex 0]                                   (Spec ""), PositionSpec Down "\\equiv_s")
  , (Cir [Se 0 "{-b/a}", Se 0 "{1/a}", CXe 1 0 "{-a}", Se 0 "{-1/a}", Se 1 "{a}", H 0, Ex 0]  (Spec ""), PositionSpec Down "\\equiv_s")
  , (Cir [Se 0 "{(1-b)/a}", CXe 1 0 "{-a}", Se 0 "{-1/a}", Se 1 "{a}", H 0, Ex 0]             (Spec ""), PositionSpec Down "\\equiv_s")
  , (Cir [Se 0 "{(1-b)/a}", CXe 1 0 "{-a}", Se 0 "{-1/a}", Se 1 "{a}", Ex 0, H 1]             (Spec ""), PositionSpec Down "\\equiv_s")
  , (Cir [Se 0 "{(1-b)/a}", H 0, CZe 1 0 "{-a}", He 0 "3", Se 0 "{-1/a}", Se 1 "{a}", Ex 0, H 1]  (Spec ""), PositionSpec Down "\\equiv_s")
  , (Cir [Se 0 "{(1-b)/a}", H 0, CZe 1 0 "{-a}", He 0 "3", Se 0 "{-1/a}", Ex 0, Se 0 "{a}", H 1]  (Spec ""), PositionSpec Down "\\equiv_s")
  , (Cir [Se 0 "{(1-b)/a}", H 0, CZe 1 0 "{-a}", He 0 "3", Ex 0, Se 1 "{-1/a}", Se 0 "{a}", H 1]  (Spec ""), PositionSpec Down "\\equiv_s")
  , (Cir [Se 0 "{(1-b)/a}", H 0, CZe 1 0 "{-a}", Ex 0, He 1 "3", Se 1 "{-1/a}", Se 0 "{a}", H 1]  (Spec ""), PositionSpec Down "\\equiv_s")
  , (Cir [Se 0 "{(1-b)/a}", H 0, CZe 1 0 "{-a}", Ex 0, He 1 "3", Se 1 "{-1/a}", H 1, Se 0 "{a}"]  (Spec ""), PositionSpec Down "=")
  , (Cir [D 0 "{a,b-1}", He 1 "3", Se 1 "{-1/a}", H 1, Se 0 "{a}"]                            (Spec ""), PositionSpec Down "")
  ]

-- B←H↑: H↑•B[00] = B[00]•H↓   (key: H↑•Ex = Ex•H↓)
chain_hb_00 :: [(CT.Circuit, PositionSpec)]
chain_hb_00 = map pcir_trans
  [ (Cir [H 1, B 0 "{00}"]    (Spec ""), PositionSpec Down "=")
  , (Cir [H 1, Ex 0]          (Spec ""), PositionSpec Down "\\equiv_s")
  , (Cir [Ex 0, H 0]          (Spec ""), PositionSpec Down "=")
  , (Cir [B 0 "{00}", H 0]    (Spec ""), PositionSpec Down "")
  ]

-- B←H↑: H↑•B[0b] = B[b0]
chain_hb_0b :: [(CT.Circuit, PositionSpec)]
chain_hb_0b = map pcir_trans
  [ (Cir [H 1, B 0 "{0b}"]          (Spec ""), PositionSpec Down "=")
  , (Cir [H 1, CXe 1 0 "b", Ex 0]   (Spec ""), PositionSpec Down "=")
  , (Cir [B 0 "{b0}"]               (Spec ""), PositionSpec Down "")
  ]

-- B←H↑: H↑•B[a0] = H^2↓•B[0,−a]   (up/down dual of D←H a0)
--   expand → CX^a·H²↑ =[HH-CX] H²↑·CX^{-a} =[Ex-slide H²↑→H²↓] → fold
chain_hb_a0 :: [(CT.Circuit, PositionSpec)]
chain_hb_a0 = map pcir_trans
  [ (Cir [H 1, B 0 "{a0}"]                  (Spec ""), PositionSpec Down "=")
  , (Cir [H 1, H 1, CXe 1 0 "a", Ex 0]      (Spec ""), PositionSpec Down "\\equiv_s")
  , (Cir [CXe 1 0 "-a", H 1, H 1, Ex 0]     (Spec ""), PositionSpec Down "\\equiv_s")
  , (Cir [CXe 1 0 "-a", Ex 0, H 0, H 0]     (Spec ""), PositionSpec Down "=")
  , (Cir [B 0 "{0,-a}", He 0 "2"]           (Spec ""), PositionSpec Down "")
  ]

-- B←H↑: H↑•B[ab] = Mul↓[b/a]•S↓[b/a]•B[b,−a]
chain_hb_ab :: [(CT.Circuit, PositionSpec)]
chain_hb_ab = map pcir_trans
  [ (Cir [H 1, B 0 "{ab}"]                                   (Spec ""), PositionSpec Down "=")
  , (Cir [H 1, Se 1 "{-b/a}", H 1, CXe 1 0 "a", Ex 0]        (Spec ""), PositionSpec Down "\\equiv_s")
  , (Cir [B 0 "{b,-a}", Se 0 "{b/a}", Mul 0 "{b/a}"]         (Spec ""), PositionSpec Down "")
  ]

-- B←S↑: S↑•B[0b] = B[0b]•S↓   (up/down dual of D←S↓ 0b)
--   expand → S↑ past CX [comm-CX-S↑] → S↑ across Ex → S↓ [Ex-slide] → fold
chain_stb_0b :: [(CT.Circuit, PositionSpec)]
chain_stb_0b = map pcir_trans
  [ (Cir [S 1, B 0 "{0b}"]          (Spec ""), PositionSpec Down "=")
  , (Cir [S 1, CXe 1 0 "b", Ex 0]   (Spec ""), PositionSpec Down "\\equiv_s")
  , (Cir [CXe 1 0 "b", S 1, Ex 0]   (Spec ""), PositionSpec Down "\\equiv_s")
  , (Cir [CXe 1 0 "b", Ex 0, S 0]   (Spec ""), PositionSpec Down "=")
  , (Cir [B 0 "{0b}", S 0]          (Spec ""), PositionSpec Down "")
  ]

-- B←S↑: S↑•B[ab] = B[a,b−a]
chain_stb_ab :: [(CT.Circuit, PositionSpec)]
chain_stb_ab = map pcir_trans
  [ (Cir [S 1, B 0 "{ab}"]                                   (Spec ""), PositionSpec Down "=")
  , (Cir [S 1, Se 1 "{-b/a}", H 1, CXe 1 0 "a", Ex 0]        (Spec ""), PositionSpec Down "=")
  , (Cir [Se 1 "{(a-b)/a}", H 1, CXe 1 0 "a", Ex 0]          (Spec ""), PositionSpec Down "=")
  , (Cir [B 0 "{a,b-a}"]                                      (Spec ""), PositionSpec Down "")
  ]

-- B←S↓: S↓•B[00] = B[00]•S↑   (key: S↓•Ex = Ex•S↑)
chain_sb_00 :: [(CT.Circuit, PositionSpec)]
chain_sb_00 = map pcir_trans
  [ (Cir [S 0, B 0 "{00}"]    (Spec ""), PositionSpec Down "=")
  , (Cir [S 0, Ex 0]          (Spec ""), PositionSpec Down "\\equiv_s")
  , (Cir [Ex 0, S 1]          (Spec ""), PositionSpec Down "=")
  , (Cir [B 0 "{00}", S 1]    (Spec ""), PositionSpec Down "")
  ]

-- B←S↓: S↓•B[0b] = CZ^{−b}•S^{b^2}↓•S↑•B[0b]
--   expand → CX-S conj [CX^b·S↓ = S↓·S^{b²}↑·CZ^{-b}·CX^b] → Ex-slides+comm-Ex-CZ → fold
chain_sb_0b :: [(CT.Circuit, PositionSpec)]
chain_sb_0b = map pcir_trans
  [ (Cir [S 0, B 0 "{0b}"]                                       (Spec ""), PositionSpec Down "=")
  , (Cir [S 0, CXe 1 0 "b", Ex 0]                                (Spec ""), PositionSpec Down "\\equiv_s")
  , (Cir [CXe 1 0 "b", CZe 0 1 "{-b}", Se 1 "{b^2}", S 0, Ex 0]  (Spec ""), PositionSpec Down "\\equiv_s")
  , (Cir [B 0 "{0b}", S 1, Se 0 "{b^2}", CZe 0 1 "{-b}"]         (Spec ""), PositionSpec Down "")
  ]

-- B←S↓: S↓•B[ab] = CZ^{−a}•S^{a^2}↓•S↑•B[ab]
--   expand → S↓ past the (H·S^{-b/a})↑ head [comm-S-w↑] → CX-S conj on CX^a·S↓ + Ex-slides → fold
chain_sb_ab :: [(CT.Circuit, PositionSpec)]
chain_sb_ab = map pcir_trans
  [ (Cir [S 0, B 0 "{ab}"]                                    (Spec ""), PositionSpec Down "=")
  , (Cir [S 0, Se 1 "{-b/a}", H 1, CXe 1 0 "a", Ex 0]        (Spec ""), PositionSpec Down "\\equiv_s")
  , (Cir [Se 1 "{-b/a}", H 1, S 0, CXe 1 0 "a", Ex 0]        (Spec ""), PositionSpec Down "\\equiv_s")
  , (Cir [B 0 "{ab}", S 1, Se 0 "{a^2}", CZe 0 1 "{-a}"]      (Spec ""), PositionSpec Down "")
  ]

-- B↑←CZ: CZ↓•B↑[0b] = CZ^{−b}↓•CZ↑•Ex↓•B↑[0b]
chain_czbat_0b :: [(CT.Circuit, PositionSpec)]
chain_czbat_0b = map pcir_trans
  [ (Cir [CZ 0 1, B 1 "{0b}"]                               (Spec ""), PositionSpec Down "=")
  , (Cir [CZ 0 1, CXe 2 1 "b", Ex 1]                        (Spec ""), PositionSpec Down "\\equiv_s")
  , (Cir [CXe 2 1 "b", CZe 2 0 "{-b}", CZ 0 1, Ex 1]        (Spec ""), PositionSpec Down "\\equiv_s")
  , (Cir [CXe 2 1 "b", CZe 2 0 "{-b}", Ex 1, CZe 2 0 ""]    (Spec ""), PositionSpec Down "\\equiv_s")
  , (Cir [CXe 2 1 "b", Ex 1, CZe 1 0 "{-b}", CZe 2 0 ""]    (Spec ""), PositionSpec Down "=")
  , (Cir [B 1 "{0b}", CZe 1 0 "{-b}", CZe 2 0 ""]           (Spec ""), PositionSpec Down "")
  ]

-- B↑←CZ: CZ↓•B↑[ab] = CZ^{−a}↓•CZ↑•Ex↓•B↑[ab]
chain_czbat_ab :: [(CT.Circuit, PositionSpec)]
chain_czbat_ab = map pcir_trans
  [ (Cir [CZ 0 1, B 1 "{ab}"]                                              (Spec ""), PositionSpec Down "=")
  , (Cir [CZ 0 1, Se 2 "{-b/a}", H 2, CXe 2 1 "a", Ex 1]                   (Spec ""), PositionSpec Down "\\equiv_s")
  , (Cir [Se 2 "{-b/a}", H 2, CZ 0 1, CXe 2 1 "a", Ex 1]                   (Spec ""), PositionSpec Down "\\equiv_s")
  , (Cir [Se 2 "{-b/a}", H 2, CXe 2 1 "a", CZe 2 0 "{-a}", CZ 0 1, Ex 1]   (Spec ""), PositionSpec Down "\\equiv_s")
  , (Cir [Se 2 "{-b/a}", H 2, CXe 2 1 "a", CZe 2 0 "{-a}", Ex 1, CZe 2 0 ""]  (Spec ""), PositionSpec Down "\\equiv_s")
  , (Cir [Se 2 "{-b/a}", H 2, CXe 2 1 "a", Ex 1, CZe 1 0 "{-a}", CZe 2 0 ""]  (Spec ""), PositionSpec Down "=")
  , (Cir [B 1 "{ab}", CZe 1 0 "{-a}", CZe 2 0 ""]                          (Spec ""), PositionSpec Down "")
  ]

-- DD←CZ: 4 cases (direct ≡_s, intermediate too complex to inline)
chain_czdd_1 :: [(CT.Circuit, PositionSpec)]
chain_czdd_1 = map pcir_trans
  [ (Cir [CZ 0 1, D 1 "{0b}", D 0 "{0d}"]                       (Spec ""), PositionSpec Down "=")
  , (Cir [CZ 0 1, CZe 2 1 "{-b}", Ex 1, CZe 1 0 "{-d}", Ex 0]  (Spec ""), PositionSpec Down "\\equiv_s")
  , (Cir [CZe 2 1 "{-b}", CZ 0 1, Ex 1, Ex 0, CZe 1 0 "{-d}"]  (Spec ""), PositionSpec Down "\\equiv_s")
  , (Cir [CZe 2 1 "{-b}", Ex 1, Ex 0, CZ 1 2, CZe 1 0 "{-d}"]  (Spec ""), PositionSpec Down "\\equiv_s")
  , (Cir [CZe 2 1 "{-b}", Ex 1, Ex 0, CZe 1 0 "{-d}", CZ 1 2]  (Spec ""), PositionSpec Down "\\equiv_s")
  , (Cir [CZe 2 1 "{-b}", Ex 1, CZe 1 0 "{-d}", Ex 0, CZ 1 2]  (Spec ""), PositionSpec Down "=")
  , (Cir [D 1 "{0b}", D 0 "{0d}", CZ 1 2]                       (Spec ""), PositionSpec Down "")
  ]

-- DD←CZ, case d1=(0,b) lower, d2=(a,b) upper (a≠0): agda case 3 (DD-CZ.agda:368).
-- Fully inlined to axioms. CZ02 = CZe 2 0 (wires 0,2); CX'^k expanded as H³·CZ·H.
chain_czdd_2 :: [(CT.Circuit, PositionSpec)]
chain_czdd_2 = map pcir_trans
  [ (Cir [CZ 0 1, D 1 "{ab}", D 0 "{0d}"]                                                      (Spec ""), PositionSpec Down "=")
  , (Cir [CZ 0 1, Se 1 "{-b/a}", H 1, CZe 2 1 "{-a}", Ex 1, CZe 1 0 "{-d}", Ex 0]              (Spec ""), PositionSpec Down "\\equiv_s")
  , (Cir [Se 1 "{-b/a}", CZ 0 1, H 1, CZe 2 1 "{-a}", Ex 1, CZe 1 0 "{-d}", Ex 0]              (Spec ""), PositionSpec Down "\\equiv_s")
  , (Cir [Se 1 "{-b/a}", CXe 2 1 "{-a}", CZe 2 0 "{a}", CZ 0 1, H 1, Ex 1, CZe 1 0 "{-d}", Ex 0]  (Spec ""), PositionSpec Down "\\equiv_s")
  , (Cir [Se 1 "{-b/a}", CXe 2 1 "{-a}", CZe 2 0 "{a}", CZ 0 1, Ex 1, H 2, CZe 1 0 "{-d}", Ex 0]  (Spec ""), PositionSpec Down "\\equiv_s")
  , (Cir [Se 1 "{-b/a}", CXe 2 1 "{-a}", CZe 2 0 "{a}", CZ 0 1, Ex 1, CZe 1 0 "{-d}", Ex 0, H 2]  (Spec ""), PositionSpec Down "\\equiv_s")
  , (Cir [Se 1 "{-b/a}", CXe 2 1 "{-a}", CZe 2 0 "{a}", CZ 0 1, Ex 1, Ex 0, CZe 1 0 "{-d}", H 2]  (Spec ""), PositionSpec Down "\\equiv_s")
  , (Cir [Se 1 "{-b/a}", CXe 2 1 "{-a}", CZe 2 0 "{a}", Ex 1, Ex 0, CZ 1 2, CZe 1 0 "{-d}", H 2]  (Spec ""), PositionSpec Down "\\equiv_s")
  , (Cir [Se 1 "{-b/a}", CXe 2 1 "{-a}", CZe 2 0 "{a}", Ex 1, Ex 0, CZe 1 0 "{-d}", CZ 1 2, H 2]  (Spec ""), PositionSpec Down "\\equiv_s")
  , (Cir [Se 1 "{-b/a}", CXe 2 1 "{-a}", Ex 1, CZe 1 0 "{a}", CZe 1 0 "{-d}", Ex 0, CZ 1 2, H 2]  (Spec ""), PositionSpec Down "\\equiv_s")
  , (Cir [Se 1 "{-b/a}", CXe 2 1 "{-a}", Ex 1, CZe 1 0 "{a-d}", Ex 0, CZ 1 2, H 2]              (Spec ""), PositionSpec Down "\\equiv_s")
  , (Cir [Se 1 "{-b/a}", H 1, CZe 2 1 "{-a}", He 1 "3", Ex 1, CZe 1 0 "{a-d}", Ex 0, CZ 1 2, H 2]  (Spec ""), PositionSpec Down "\\equiv_s")
  , (Cir [Se 1 "{-b/a}", H 1, CZe 2 1 "{-a}", Ex 1, He 2 "3", CZe 1 0 "{a-d}", Ex 0, CZ 1 2, H 2]  (Spec ""), PositionSpec Down "\\equiv_s")
  , (Cir [Se 1 "{-b/a}", H 1, CZe 2 1 "{-a}", Ex 1, CZe 1 0 "{a-d}", He 2 "3", Ex 0, CZ 1 2, H 2]  (Spec ""), PositionSpec Down "\\equiv_s")
  , (Cir [Se 1 "{-b/a}", H 1, CZe 2 1 "{-a}", Ex 1, CZe 1 0 "{a-d}", Ex 0, He 2 "3", CZ 1 2, H 2]  (Spec ""), PositionSpec Down "=")
  , (Cir [D 1 "{ab}", D 0 "{0,d-a}", Sep, He 2 "3", CZ 1 2, H 2]                               (Spec ""), PositionSpec Down "")
  ]

chain_czdd_3 :: [(CT.Circuit, PositionSpec)]
chain_czdd_3 = map pcir_trans
  [ (Cir [CZ 0 1, D 1 "{0b}", D 0 "{cd}"]                                          (Spec ""), PositionSpec Down "=")
  , (Cir [CZ 0 1, CZe 2 1 "{-b}", Ex 1, Se 0 "{-d/c}", H 0, CZe 1 0 "{-c}", Ex 0]  (Spec ""), PositionSpec Down "\\equiv_s")
  , (Cir [D 1 "{0,b-c}", D 0 "{c,d}", He 1 "3", CZ 1 2, H 1]                       (Spec ""), PositionSpec Down "")
  ]

chain_czdd_4 :: [(CT.Circuit, PositionSpec)]
-- DD←CZ, both a,c≠0: agda case 4 (DD-CZ.agda:410). Convention swap a1=c,a2=a.
-- Core: lemma-CZ02^k-CZ^l↑-CZ (the two-pair analogue of CZ-H-CZ). CZ02=CZe 2 0,
-- CX02=CXe 2 0. Final cleanup (Ex-slides + S-merges + CX'-fold) shown as one step.
chain_czdd_4 = map pcir_trans
  [ (Cir [CZ 0 1, D 1 "{ab}", D 0 "{cd}"]                                                                          (Spec ""), PositionSpec Down "=")
  , (Cir [CZ 0 1, Se 1 "{-b/a}", H 1, CZe 2 1 "{-a}", Ex 1, Se 0 "{-d/c}", H 0, CZe 1 0 "{-c}", Ex 0]             (Spec ""), PositionSpec Down "\\equiv_s")
  , (Cir [Se 1 "{-b/a}", CZ 0 1, H 1, CZe 2 1 "{-a}", Ex 1, Se 0 "{-d/c}", H 0, CZe 1 0 "{-c}", Ex 0]             (Spec ""), PositionSpec Down "\\equiv_s")
  , (Cir [Se 1 "{-b/a}", CZ 0 1, H 1, CZe 2 1 "{-a}", Se 0 "{-d/c}", H 0, Ex 1, CZe 1 0 "{-c}", Ex 0]             (Spec ""), PositionSpec Down "\\equiv_s")
  , (Cir [Se 1 "{-b/a}", CZ 0 1, Se 0 "{-d/c}", H 1, CZe 2 1 "{-a}", H 0, CZe 2 0 "{-c}", Ex 1, Ex 0]             (Spec ""), PositionSpec Down "\\equiv_s")
  , (Cir [Se 1 "{-b/a}", Se 0 "{-d/c}", CZ 0 1, H 1, CZe 2 1 "{-a}", H 0, CZe 2 0 "{-c}", Ex 1, Ex 0]             (Spec ""), PositionSpec Down "\\equiv_s")
  , (Cir [Se 1 "{-b/a}", Se 0 "{-d/c}", Se 1 "{c/a}", CXe 2 1 "{-a}", Se 1 "{-c/a}", Se 0 "{a/c}", CXe 2 0 "{-c}", Se 0 "{-a/c}", CZ 0 1, H 1, H 0, Ex 1, Ex 0]  (Spec ""), PositionSpec Down "\\equiv_s")
  , (Cir [D 1 "{a,b-c}", D 0 "{c,d-a}", Sep, He 1 "3", Se 1 "{-a/c}", He 2 "3", Se 2 "{-c/a}", CZ 1 2, H 2, H 1]  (Spec ""), PositionSpec Down "")
  ]

-- BB←CZ↑: 4 cases (dual to DD←CZ)
chain_czbb_1 :: [(CT.Circuit, PositionSpec)]
chain_czbb_1 = map pcir_trans
  [ (Cir [CZ 1 2, B 0 "{0b}", B 1 "{0d}"]                      (Spec ""), PositionSpec Down "=")
  , (Cir [CZ 1 2, CXe 1 0 "b", Ex 0, CXe 2 1 "d", Ex 1]        (Spec ""), PositionSpec Down "\\equiv_s")
  , (Cir [B 0 "{0b}", B 1 "{0d}", CZ 0 1]                      (Spec ""), PositionSpec Down "")
  ]

chain_czbb_2 :: [(CT.Circuit, PositionSpec)]
chain_czbb_2 = map pcir_trans
  [ (Cir [CZ 1 2, B 0 "{ab}", B 1 "{0d}"]                                          (Spec ""), PositionSpec Down "=")
  , (Cir [CZ 1 2, Se 1 "{-b/a}", H 1, CXe 1 0 "a", Ex 0, CXe 2 1 "d", Ex 1]        (Spec ""), PositionSpec Down "\\equiv_s")
  , (Cir [B 0 "{ab}", B 1 "{0,d-a}", Sep, He 0 "3", CZ 0 1, H 0]                   (Spec ""), PositionSpec Down "")
  ]

chain_czbb_3 :: [(CT.Circuit, PositionSpec)]
chain_czbb_3 = map pcir_trans
  [ (Cir [CZ 1 2, B 0 "{0b}", B 1 "{cd}"]                                          (Spec ""), PositionSpec Down "=")
  , (Cir [CZ 1 2, CXe 1 0 "b", Ex 0, Se 2 "{-d/c}", H 2, CXe 2 1 "c", Ex 1]        (Spec ""), PositionSpec Down "\\equiv_s")
  , (Cir [B 0 "{0,b-c}", B 1 "{c,d}", Sep, He 1 "3", CZ 0 1, H 1]                  (Spec ""), PositionSpec Down "")
  ]

chain_czbb_4 :: [(CT.Circuit, PositionSpec)]
chain_czbb_4 = map pcir_trans
  [ (Cir [CZ 1 2, B 0 "{ab}", B 1 "{cd}"]                                                                        (Spec ""), PositionSpec Down "=")
  , (Cir [CZ 1 2, Se 1 "{-b/a}", H 1, CXe 1 0 "a", Ex 0, Se 2 "{-d/c}", H 2, CXe 2 1 "c", Ex 1]                   (Spec ""), PositionSpec Down "\\equiv_s")
  , (Cir [B 0 "{a,b-c}", B 1 "{c,d-a}", Sep, He 1 "3", Se 1 "{-a/c}", He 0 "3", Se 0 "{-c/a}", CZ 0 1, H 0, H 1]  (Spec ""), PositionSpec Down "")
  ]

-- L←CZ: 8 cases
chain_lcz_1 :: [(CT.Circuit, PositionSpec)]
chain_lcz_1 = map pcir_trans
  [ (Cir [CZ 0 1, A 1 "{0b}"]                  (Spec ""), PositionSpec Down "=")
  , (Cir [CZ 0 1, Mul 1 "b"] (Spec ""), PositionSpec Down "\\equiv_s")
  , (Cir [A 1 "{0b}", CZe 0 1 "{1/b}"]         (Spec ""), PositionSpec Down "")
  ]

chain_lcz_2 :: [(CT.Circuit, PositionSpec)]
chain_lcz_2 = map pcir_trans
  [ (Cir [CZ 0 1, A 1 "{ab}"]                                        (Spec ""), PositionSpec Down "=")
  , (Cir [CZ 0 1, Se 1 "{-b/a}", H 1, Mul 1 "a"] (Spec ""), PositionSpec Down "\\equiv_s")
  , (Cir [A 0 "{0,-a}", B 0 "{ab}", He 0 "3", CZe 0 1 "{1/a}", H 0] (Spec ""), PositionSpec Down "")
  ]

chain_lcz_3 :: [(CT.Circuit, PositionSpec)]
-- L←CZ case 3 (A[0b]·B[00]): fully inlined (L-CZ.agda:477). Cir M[b]·CZ=CZ^{1/b}·M[b].
chain_lcz_3 = map pcir_trans
  [ (Cir [CZ 0 1, A 0 "{0b}", B 0 "{00}"]            (Spec ""), PositionSpec Down "=")
  , (Cir [CZ 0 1, Mul 0 "b", Ex 0]                   (Spec ""), PositionSpec Down "\\equiv_s")
  , (Cir [Mul 0 "b", CZe 0 1 "{1/b}", Ex 0]          (Spec ""), PositionSpec Down "\\equiv_s")
  , (Cir [Mul 0 "b", Ex 0, CZe 0 1 "{1/b}"]          (Spec ""), PositionSpec Down "=")
  , (Cir [A 0 "{0b}", B 0 "{00}", CZe 0 1 "{1/b}"]   (Spec ""), PositionSpec Down "")
  ]

chain_lcz_4 :: [(CT.Circuit, PositionSpec)]
-- L←CZ case 4 (A[0b]·B[0d]): fully inlined (L-CZ.agda:507). CX^d·CZ spawns S↑, slid to S↓.
chain_lcz_4 = map pcir_trans
  [ (Cir [CZ 0 1, A 0 "{0b}", B 0 "{0d}"]                                          (Spec ""), PositionSpec Down "=")
  , (Cir [CZ 0 1, Mul 0 "b", CXe 1 0 "d", Ex 0]                                    (Spec ""), PositionSpec Down "\\equiv_s")
  , (Cir [Mul 0 "b", CZe 0 1 "{1/b}", CXe 1 0 "d", Ex 0]                           (Spec ""), PositionSpec Down "\\equiv_s")
  , (Cir [Mul 0 "b", CXe 1 0 "d", CZe 0 1 "{1/b}", Se 1 "{-2d/b}", Ex 0]           (Spec ""), PositionSpec Down "\\equiv_s")
  , (Cir [Mul 0 "b", CXe 1 0 "d", CZe 0 1 "{1/b}", Ex 0, Se 0 "{-2d/b}"]           (Spec ""), PositionSpec Down "\\equiv_s")
  , (Cir [Mul 0 "b", CXe 1 0 "d", Ex 0, CZe 0 1 "{1/b}", Se 0 "{-2d/b}"]           (Spec ""), PositionSpec Down "=")
  , (Cir [A 0 "{0b}", B 0 "{0d}", CZe 0 1 "{1/b}", Se 0 "{-2d/b}"]                 (Spec ""), PositionSpec Down "")
  ]

chain_lcz_5 :: [(CT.Circuit, PositionSpec)]
chain_lcz_5 = map pcir_trans
  [ (Cir [CZ 0 1, A 0 "{0b}", B 0 "{cd}"]                                              (Spec ""), PositionSpec Down "=")
  , (Cir [CZ 0 1, Mul 0 "b", Se 1 "{-d/c}", H 1, CXe 1 0 "c", Ex 0] (Spec ""), PositionSpec Down "\\equiv_s")
  , (Cir [A 0 "{0,b-c}", B 0 "{cd}", He 0 "3", CZe 0 1 "{1/b}", H 0, Mul 0 "{b/(b-c)}"] (Spec ""), PositionSpec Down "")
  ]

chain_lcz_6 :: [(CT.Circuit, PositionSpec)]
chain_lcz_6 = map pcir_trans
  [ (Cir [CZ 0 1, A 0 "{0b}", B 0 "{bd}"]               (Spec ""), PositionSpec Down "=")
  , (Cir [CZ 0 1, Mul 0 "b", Se 1 "{-d/b}", H 1, CXe 1 0 "b", Ex 0] (Spec ""), PositionSpec Down "\\equiv_s")
  , (Cir [A 1 "{bd}", Sep, H 0, CZe 0 1 "{-1/b}", H 0]  (Spec ""), PositionSpec Down "")
  ]

chain_lcz_7 :: [(CT.Circuit, PositionSpec)]
chain_lcz_7 = map pcir_trans
  [ (Cir [CZ 0 1, A 0 "{ab}", B 0 "{0d}"]     (Spec ""), PositionSpec Down "=")
  , (Cir [CZ 0 1, Se 0 "{-b/a}", H 0, Mul 0 "a", CXe 1 0 "d", Ex 0] (Spec ""), PositionSpec Down "\\equiv_s")
  , (Cir [A 0 "{a,b}", B 0 "{0,d-a}"]         (Spec ""), PositionSpec Down "")
  ]

chain_lcz_8 :: [(CT.Circuit, PositionSpec)]
chain_lcz_8 = map pcir_trans
  [ (Cir [CZ 0 1, A 0 "{ab}", B 0 "{cd}"]                               (Spec ""), PositionSpec Down "=")
  , (Cir [CZ 0 1, Se 0 "{-b/a}", H 0, Mul 0 "a", Se 1 "{-d/c}", H 1, CXe 1 0 "c", Ex 0] (Spec ""), PositionSpec Down "\\equiv_s")
  , (Cir [A 0 "{a,b-c}", B 0 "{c,d-a}", H 0, Se 0 "{-a/c}", He 0 "3"] (Spec ""), PositionSpec Down "")
  ]

------------------------------------------------------------------------
-- Layer-0 lemma library (test3.tex §"Axioms and core lemmas").
-- These single-qupit lemmas are the leaves every box-relation step
-- bottoms out in; each box-relation ≡_s step is tagged with one of them.
-- (M[a] is rendered with the Mul gate carrying an "M_…" label.)
------------------------------------------------------------------------

-- M-mul (axiom): M[a]•M[b] = M[ab]
lib_mmul :: [(CT.Circuit, PositionSpec)]
lib_mmul = map pcir_trans
  [ (Cir [Mul 0 "M_a", Mul 0 "M_b"] (Spec ""), PositionSpec Down "=")
  , (Cir [Mul 0 "M_{ab}"]           (Spec ""), PositionSpec Down "")
  ]

-- semi-MS (axiom): S•M[b] ≡_s M[b]•S^{1/b^2}
lib_semims :: [(CT.Circuit, PositionSpec)]
lib_semims = map pcir_trans
  [ (Cir [S 0, Mul 0 "M_b"]                 (Spec ""), PositionSpec Down "\\equiv_s")
  , (Cir [Mul 0 "M_b", Se 0 "{1/b^2}"]      (Spec ""), PositionSpec Down "")
  ]

-- HHM (H^2 = M[-1], then M-mul): H•H•M[a] ≡_s M[-a]
lib_hhm :: [(CT.Circuit, PositionSpec)]
lib_hhm = map pcir_trans
  [ (Cir [H 0, H 0, Mul 0 "M_a"] (Spec ""), PositionSpec Down "\\equiv_s")
  , (Cir [Mul 0 "M_{-a}"]        (Spec ""), PositionSpec Down "")
  ]

writeChain :: FilePath -> [(CT.Circuit, PositionSpec)] -> IO ()
writeChain fname ch = writeFile ("chains/" ++ fname ++ ".tikz") (CT.tikz_of_pcir ch)

-- Split a long chain into page-segments of ~n circuits, written as
-- fname_p1, fname_p2, ...  Consecutive segments overlap on the boundary
-- circuit (shown at the bottom of one page and the top of the next) for
-- visual continuity; the boundary circuit's trailing connective is blanked
-- so no arrow dangles off the page bottom.
writeChainSplit :: Int -> FilePath -> [(CT.Circuit, PositionSpec)] -> IO ()
writeChainSplit n fname ch =
    mapM_ (\(i, seg) -> writeFile ("chains/" ++ fname ++ "_p" ++ show i ++ ".tikz")
                                  (CT.tikz_of_pcir seg))
          (zip [1 :: Int ..] (chunksOverlap n ch))

chunksOverlap :: Int -> [(CT.Circuit, PositionSpec)] -> [[(CT.Circuit, PositionSpec)]]
chunksOverlap n xs
  | length xs <= n = [xs]
  | otherwise      = clearLast (take n xs) : chunksOverlap n (drop (n - 1) xs)
  where
    clearLast ys = init ys ++ [(fst (last ys), PositionSpec Down "")]

------------------------------------------------------------------------
-- Main: generate one tikz file per theorem group.
------------------------------------------------------------------------

main :: IO ()
main = do
    writeGroup "def"  rels_def
    writeGroup "ah"   rels_AH
    writeGroup "as"   rels_AS
    writeGroup "es"   rels_ES
    writeGroup "lcz"  rels_LCZ
    writeGroup "bh"   rels_BH
    writeGroup "dh"   rels_DH
    writeGroup "bbcz" rels_BBCZ
    writeGroup "bcz"  rels_BCZ
    writeGroup "ddcz" rels_DDCZ
    writeGroup "selinger"    rels_selinger
    writeGroup "hsh"         rels_hsh
    writeGroup "shczh"       rels_shczh
    writeFile  "shczh_chain.tikz" (CT.tikz_of_pcir proof_shczh)
    -- Layer-0 lemma library (top-level .tikz, referenced by test3.tex §Layer 0)
    writeFile  "lib_mmul.tikz"   (CT.tikz_of_pcir lib_mmul)
    writeFile  "lib_semims.tikz" (CT.tikz_of_pcir lib_semims)
    writeFile  "lib_hhm.tikz"    (CT.tikz_of_pcir lib_hhm)
    -- E←S
    writeChain "chain_se"        chain_se
    -- A←H
    writeChain "chain_ah_0b"     chain_ah_0b
    writeChain "chain_ah_a0"     chain_ah_a0
    writeChain "chain_ah_ab"     chain_ah_ab
    -- A←S
    writeChain "chain_sa_0b"     chain_sa_0b
    writeChain "chain_sa_ab"     chain_sa_ab
    -- D←H
    writeChain "chain_hd_00"     chain_hd_00
    writeChain "chain_hd_0b"     chain_hd_0b
    writeChain "chain_hd_a0"     chain_hd_a0
    writeChain "chain_hd_ab"     chain_hd_ab
    -- D←S↓
    writeChain "chain_sd_0b"     chain_sd_0b
    writeChain "chain_sd_ab"     chain_sd_ab
    -- D←S↑
    writeChain "chain_std"       chain_std
    -- D←CZ
    writeChain "chain_czd_0b"    chain_czd_0b
    writeChainSplit 7 "chain_czd_ab" chain_czd_ab
    -- B←H↑
    writeChain "chain_hb_00"     chain_hb_00
    writeChain "chain_hb_0b"     chain_hb_0b
    writeChain "chain_hb_a0"     chain_hb_a0
    writeChain "chain_hb_ab"     chain_hb_ab
    -- B←S↑
    writeChain "chain_stb_0b"    chain_stb_0b
    writeChain "chain_stb_ab"    chain_stb_ab
    -- B←S↓
    writeChain "chain_sb_00"     chain_sb_00
    writeChain "chain_sb_0b"     chain_sb_0b
    writeChain "chain_sb_ab"     chain_sb_ab
    -- B↑←CZ
    writeChain "chain_czbat_0b"  chain_czbat_0b
    writeChain "chain_czbat_ab"  chain_czbat_ab
    -- DD←CZ
    writeChain "chain_czdd_1"    chain_czdd_1
    writeChainSplit 9 "chain_czdd_2" chain_czdd_2
    writeChain "chain_czdd_3"    chain_czdd_3
    writeChainSplit 5 "chain_czdd_4" chain_czdd_4
    -- BB←CZ↑
    writeChain "chain_czbb_1"    chain_czbb_1
    writeChain "chain_czbb_2"    chain_czbb_2
    writeChain "chain_czbb_3"    chain_czbb_3
    writeChain "chain_czbb_4"    chain_czbb_4
    -- L←CZ
    writeChain "chain_lcz_1"     chain_lcz_1
    writeChain "chain_lcz_2"     chain_lcz_2
    writeChain "chain_lcz_3"     chain_lcz_3
    writeChain "chain_lcz_4"     chain_lcz_4
    writeChain "chain_lcz_5"     chain_lcz_5
    writeChain "chain_lcz_6"     chain_lcz_6
    writeChain "chain_lcz_7"     chain_lcz_7
    writeChain "chain_lcz_8"     chain_lcz_8
    putStrLn "Done: all .tikz files written."
