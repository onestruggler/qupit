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
chain_ah_a0 :: [(CT.Circuit, PositionSpec)]
chain_ah_a0 = map pcir_trans
  [ (Cir [H 0, A 0 "{a0}"]       (Spec ""), PositionSpec Down "=")
  , (Cir [H 0, H 0, Mul 0 "a"]   (Spec ""), PositionSpec Down "\\equiv_s")
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
chain_hd_a0 :: [(CT.Circuit, PositionSpec)]
chain_hd_a0 = map pcir_trans
  [ (Cir [H 0, D 0 "{a0}"]                   (Spec ""), PositionSpec Down "=")
  , (Cir [H 0, H 0, CZe 1 0 "{-a}", Ex 0]    (Spec ""), PositionSpec Down "\\equiv_s")
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
chain_sd_0b :: [(CT.Circuit, PositionSpec)]
chain_sd_0b = map pcir_trans
  [ (Cir [S 0, D 0 "{0b}"]            (Spec ""), PositionSpec Down "=")
  , (Cir [S 0, CZe 1 0 "{-b}", Ex 0]  (Spec ""), PositionSpec Down "\\equiv_s")
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
chain_std :: [(CT.Circuit, PositionSpec)]
chain_std = map pcir_trans
  [ (Cir [S 1, D 0 "{ab}"]    (Spec ""), PositionSpec Down "\\equiv_s")
  , (Cir [D 0 "{ab}", S 0]    (Spec ""), PositionSpec Down "")
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
chain_czd_ab :: [(CT.Circuit, PositionSpec)]
chain_czd_ab = map pcir_trans
  [ (Cir [CZ 0 1, D 0 "{ab}"]                                       (Spec ""), PositionSpec Down "=")
  , (Cir [CZ 0 1, Se 0 "{-b/a}", H 0, CZe 1 0 "{-a}", Ex 0]        (Spec ""), PositionSpec Down "\\equiv_s")
  , (Cir [D 0 "{a,b-1}", He 1 "3", Se 1 "{-1/a}", H 1, Se 0 "a"]   (Spec ""), PositionSpec Down "")
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

-- B←H↑: H↑•B[a0] = H^2↓•B[0,−a]
chain_hb_a0 :: [(CT.Circuit, PositionSpec)]
chain_hb_a0 = map pcir_trans
  [ (Cir [H 1, B 0 "{a0}"]                  (Spec ""), PositionSpec Down "=")
  , (Cir [H 1, H 1, CXe 1 0 "a", Ex 0]      (Spec ""), PositionSpec Down "\\equiv_s")
  , (Cir [B 0 "{0,-a}", He 0 "2"]           (Spec ""), PositionSpec Down "")
  ]

-- B←H↑: H↑•B[ab] = Mul↓[b/a]•S↓[b/a]•B[b,−a]
chain_hb_ab :: [(CT.Circuit, PositionSpec)]
chain_hb_ab = map pcir_trans
  [ (Cir [H 1, B 0 "{ab}"]                                   (Spec ""), PositionSpec Down "=")
  , (Cir [H 1, Se 1 "{-b/a}", H 1, CXe 1 0 "a", Ex 0]        (Spec ""), PositionSpec Down "\\equiv_s")
  , (Cir [B 0 "{b,-a}", Se 0 "{b/a}", Mul 0 "{b/a}"]         (Spec ""), PositionSpec Down "")
  ]

-- B←S↑: S↑•B[0b] = B[0b]•S↓
chain_stb_0b :: [(CT.Circuit, PositionSpec)]
chain_stb_0b = map pcir_trans
  [ (Cir [S 1, B 0 "{0b}"]          (Spec ""), PositionSpec Down "=")
  , (Cir [S 1, CXe 1 0 "b", Ex 0]   (Spec ""), PositionSpec Down "\\equiv_s")
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
chain_sb_0b :: [(CT.Circuit, PositionSpec)]
chain_sb_0b = map pcir_trans
  [ (Cir [S 0, B 0 "{0b}"]                                    (Spec ""), PositionSpec Down "=")
  , (Cir [S 0, CXe 1 0 "b", Ex 0]                             (Spec ""), PositionSpec Down "\\equiv_s")
  , (Cir [B 0 "{0b}", S 1, Se 0 "{b^2}", CZe 0 1 "{-b}"]      (Spec ""), PositionSpec Down "")
  ]

-- B←S↓: S↓•B[ab] = CZ^{−a}•S^{a^2}↓•S↑•B[ab]
chain_sb_ab :: [(CT.Circuit, PositionSpec)]
chain_sb_ab = map pcir_trans
  [ (Cir [S 0, B 0 "{ab}"]                                    (Spec ""), PositionSpec Down "=")
  , (Cir [S 0, Se 1 "{-b/a}", H 1, CXe 1 0 "a", Ex 0]        (Spec ""), PositionSpec Down "\\equiv_s")
  , (Cir [B 0 "{ab}", S 1, Se 0 "{a^2}", CZe 0 1 "{-a}"]      (Spec ""), PositionSpec Down "")
  ]

-- B↑←CZ: CZ↓•B↑[0b] = CZ^{−b}↓•CZ↑•Ex↓•B↑[0b]
chain_czbat_0b :: [(CT.Circuit, PositionSpec)]
chain_czbat_0b = map pcir_trans
  [ (Cir [CZ 0 1, B 1 "{0b}"]                                (Spec ""), PositionSpec Down "=")
  , (Cir [CZ 0 1, CXe 2 1 "b", Ex 1]                         (Spec ""), PositionSpec Down "\\equiv_s")
  , (Cir [B 1 "{0b}", Ex 0, CZ 1 2, Ex 0, CZe 0 1 "{-b}"]   (Spec ""), PositionSpec Down "")
  ]

-- B↑←CZ: CZ↓•B↑[ab] = CZ^{−a}↓•CZ↑•Ex↓•B↑[ab]
chain_czbat_ab :: [(CT.Circuit, PositionSpec)]
chain_czbat_ab = map pcir_trans
  [ (Cir [CZ 0 1, B 1 "{ab}"]                                (Spec ""), PositionSpec Down "=")
  , (Cir [CZ 0 1, Se 2 "{-b/a}", H 2, CXe 2 1 "a", Ex 1]    (Spec ""), PositionSpec Down "\\equiv_s")
  , (Cir [B 1 "{ab}", Ex 0, CZ 1 2, Ex 0, CZe 0 1 "{-a}"]   (Spec ""), PositionSpec Down "")
  ]

-- DD←CZ: 4 cases (direct ≡_s, intermediate too complex to inline)
chain_czdd_1 :: [(CT.Circuit, PositionSpec)]
chain_czdd_1 = map pcir_trans
  [ (Cir [CZ 0 1, D 1 "{0b}", D 0 "{0d}"]        (Spec ""), PositionSpec Down "\\equiv_s")
  , (Cir [D 1 "{0b}", D 0 "{0d}", CZ 1 2]         (Spec ""), PositionSpec Down "")
  ]

chain_czdd_2 :: [(CT.Circuit, PositionSpec)]
chain_czdd_2 = map pcir_trans
  [ (Cir [CZ 0 1, D 1 "{ab}", D 0 "{0d}"]                           (Spec ""), PositionSpec Down "\\equiv_s")
  , (Cir [D 1 "{ab}", D 0 "{0,d-a}", Sep, He 2 "3", CZ 1 2, H 2]   (Spec ""), PositionSpec Down "")
  ]

chain_czdd_3 :: [(CT.Circuit, PositionSpec)]
chain_czdd_3 = map pcir_trans
  [ (Cir [CZ 0 1, D 1 "{0b}", D 0 "{cd}"]                           (Spec ""), PositionSpec Down "\\equiv_s")
  , (Cir [D 1 "{0,b-c}", D 0 "{c,d}", He 1 "3", CZ 1 2, H 1]       (Spec ""), PositionSpec Down "")
  ]

chain_czdd_4 :: [(CT.Circuit, PositionSpec)]
chain_czdd_4 = map pcir_trans
  [ (Cir [CZ 0 1, D 1 "{ab}", D 0 "{cd}"]                                                                            (Spec ""), PositionSpec Down "\\equiv_s")
  , (Cir [D 1 "{a,b-c}", D 0 "{c,d-a}", Sep, He 1 "3", Se 1 "{-a/c}", He 2 "3", Se 2 "{-c/a}", CZ 1 2, H 2, H 1]  (Spec ""), PositionSpec Down "")
  ]

-- BB←CZ↑: 4 cases (dual to DD←CZ)
chain_czbb_1 :: [(CT.Circuit, PositionSpec)]
chain_czbb_1 = map pcir_trans
  [ (Cir [CZ 1 2, B 0 "{0b}", B 1 "{0d}"]        (Spec ""), PositionSpec Down "\\equiv_s")
  , (Cir [B 0 "{0b}", B 1 "{0d}", CZ 0 1]         (Spec ""), PositionSpec Down "")
  ]

chain_czbb_2 :: [(CT.Circuit, PositionSpec)]
chain_czbb_2 = map pcir_trans
  [ (Cir [CZ 1 2, B 0 "{ab}", B 1 "{0d}"]                          (Spec ""), PositionSpec Down "\\equiv_s")
  , (Cir [B 0 "{ab}", B 1 "{0,d-a}", Sep, He 0 "3", CZ 0 1, H 0]  (Spec ""), PositionSpec Down "")
  ]

chain_czbb_3 :: [(CT.Circuit, PositionSpec)]
chain_czbb_3 = map pcir_trans
  [ (Cir [CZ 1 2, B 0 "{0b}", B 1 "{cd}"]                          (Spec ""), PositionSpec Down "\\equiv_s")
  , (Cir [B 0 "{0,b-c}", B 1 "{c,d}", Sep, He 1 "3", CZ 0 1, H 1] (Spec ""), PositionSpec Down "")
  ]

chain_czbb_4 :: [(CT.Circuit, PositionSpec)]
chain_czbb_4 = map pcir_trans
  [ (Cir [CZ 1 2, B 0 "{ab}", B 1 "{cd}"]                                                                            (Spec ""), PositionSpec Down "\\equiv_s")
  , (Cir [B 0 "{a,b-c}", B 1 "{c,d-a}", Sep, He 1 "3", Se 1 "{-a/c}", He 0 "3", Se 0 "{-c/a}", CZ 0 1, H 0, H 1]  (Spec ""), PositionSpec Down "")
  ]

-- L←CZ: 8 cases
chain_lcz_1 :: [(CT.Circuit, PositionSpec)]
chain_lcz_1 = map pcir_trans
  [ (Cir [CZ 0 1, A 1 "{0b}"]                  (Spec ""), PositionSpec Down "\\equiv_s")
  , (Cir [A 1 "{0b}", CZe 0 1 "{1/b}"]         (Spec ""), PositionSpec Down "")
  ]

chain_lcz_2 :: [(CT.Circuit, PositionSpec)]
chain_lcz_2 = map pcir_trans
  [ (Cir [CZ 0 1, A 1 "{ab}"]                                        (Spec ""), PositionSpec Down "\\equiv_s")
  , (Cir [A 0 "{0,-a}", B 0 "{ab}", He 0 "3", CZe 0 1 "{1/a}", H 0] (Spec ""), PositionSpec Down "")
  ]

chain_lcz_3 :: [(CT.Circuit, PositionSpec)]
chain_lcz_3 = map pcir_trans
  [ (Cir [CZ 0 1, A 0 "{0b}", B 0 "{00}"]                  (Spec ""), PositionSpec Down "\\equiv_s")
  , (Cir [A 0 "{0b}", B 0 "{00}", CZe 0 1 "{1/b}"]         (Spec ""), PositionSpec Down "")
  ]

chain_lcz_4 :: [(CT.Circuit, PositionSpec)]
chain_lcz_4 = map pcir_trans
  [ (Cir [CZ 0 1, A 0 "{0b}", B 0 "{0d}"]                           (Spec ""), PositionSpec Down "\\equiv_s")
  , (Cir [A 0 "{0b}", B 0 "{0d}", Se 0 "{-2d/b}", CZe 0 1 "{1/b}"] (Spec ""), PositionSpec Down "")
  ]

chain_lcz_5 :: [(CT.Circuit, PositionSpec)]
chain_lcz_5 = map pcir_trans
  [ (Cir [CZ 0 1, A 0 "{0b}", B 0 "{cd}"]                                              (Spec ""), PositionSpec Down "\\equiv_s")
  , (Cir [A 0 "{0,b-c}", B 0 "{cd}", He 0 "3", CZe 0 1 "{1/b}", H 0, Mul 0 "{b/(b-c)}"] (Spec ""), PositionSpec Down "")
  ]

chain_lcz_6 :: [(CT.Circuit, PositionSpec)]
chain_lcz_6 = map pcir_trans
  [ (Cir [CZ 0 1, A 0 "{0b}", B 0 "{bd}"]               (Spec ""), PositionSpec Down "\\equiv_s")
  , (Cir [A 1 "{bd}", Sep, H 0, CZe 0 1 "{-1/b}", H 0]  (Spec ""), PositionSpec Down "")
  ]

chain_lcz_7 :: [(CT.Circuit, PositionSpec)]
chain_lcz_7 = map pcir_trans
  [ (Cir [CZ 0 1, A 0 "{ab}", B 0 "{0d}"]     (Spec ""), PositionSpec Down "\\equiv_s")
  , (Cir [A 0 "{a,b}", B 0 "{0,d-a}"]         (Spec ""), PositionSpec Down "")
  ]

chain_lcz_8 :: [(CT.Circuit, PositionSpec)]
chain_lcz_8 = map pcir_trans
  [ (Cir [CZ 0 1, A 0 "{ab}", B 0 "{cd}"]                               (Spec ""), PositionSpec Down "\\equiv_s")
  , (Cir [A 0 "{a,b-c}", B 0 "{c,d-a}", H 0, Se 0 "{-a/c}", He 0 "3"] (Spec ""), PositionSpec Down "")
  ]

writeChain :: FilePath -> [(CT.Circuit, PositionSpec)] -> IO ()
writeChain fname ch = writeFile ("chains/" ++ fname ++ ".tikz") (CT.tikz_of_pcir ch)

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
    writeChain "chain_czd_ab"    chain_czd_ab
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
    writeChain "chain_czdd_2"    chain_czdd_2
    writeChain "chain_czdd_3"    chain_czdd_3
    writeChain "chain_czdd_4"    chain_czdd_4
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
