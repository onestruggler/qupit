{-# OPTIONS_GHC -w #-}
module NewBoxRel where

import System.Environment
import Data.List
import Prelude hiding (Right, Left)

import qualified Cir2Tikz as CT
import Cir2Tikz (Circuit, PositionSpec (PositionSpec), Direction (Up , Down , Right , Left , LU , LD , RU , RD) )

main = do 
    putStrLn $ CT.tikz_of_rels $ map rel_trans $ map snd $ all_rels


main_eg = do 
    putStrLn "\n\nCircuit example:\n\n"
    putStrLn $ CT.tikz_of_cir $ cir_trans $ Cir eg1 spec1  
    putStrLn "\n\nRelation example:\n\n"
    putStrLn $ CT.tikz_of_rel $ rel_trans $ Rel CT.Def (Cir eg1 spec1) (Cir eg2 spec2) rspec
    
eg1 :: [UserGate]
eg1 = [
  H 0,
  Se 1 "3",
  He 2 "ab",
  B 0 "0,-a",
  CX 1 2,
  CZ 1 2,
  CXe 2 1 "4",
  CZe 3 4 "a",
  Mul 0 "1"
  ]

eg2 :: [UserGate]
eg2 = [
  Mul 0 "a",
  He 3 "3",
  Se 0 "ab",
  D 0 "0,-a",
  CX 1 2,
  CZ 1 2,
  CZe 2 1 "4",
  CXe 3 4 "a",
  He 0 "1"
  ]

spec1 :: Spec 
spec1 = Spec "$a \\neq 1$"

spec2 :: Spec 
spec2 = Spec "$c \\neq 1$"


rspec :: Spec 
rspec = Spec "$ab \\neq 1$"


eg_pcirs :: [(Cir , PositionSpec)]
eg_pcirs =
  [
    (Cir eg1 (Spec "eg1") , PositionSpec Up "\\Rightarrow"),
    (Cir eg2 (Spec "eg2") , PositionSpec Right "\\mapsto"),
    (Cir eg1 (Spec "eg1 again") , PositionSpec RU "\\rightarrow"),
    (Cir eg2 (Spec "eg2 again") , PositionSpec RU "\\rightarrow")
  ]
























data UserGate = Sep | H Int | He Int String | S Int | Se Int String | Z Int | Ze Int String | X Int | Xe Int String | CX Int Int | CZ Int Int | CXe Int Int String | CZe Int Int String | A Int String | B Int String | E Int String | D Int String | Mul Int String | Ex Int deriving (Show, Eq, Ord, Read)

data Spec = Spec String deriving (Show, Eq, Ord, Read)
data Cir = Cir [UserGate] Spec deriving (Show, Eq, Ord, Read)
data Rel = Rel CT.RelType Cir Cir Spec deriving (Show, Eq, Ord, Read)

gate_trans :: UserGate -> CT.Gate
gate_trans (Sep) = CT.Sep
gate_trans (H k) = CT.Gate CT.H k ""
gate_trans (He k e) = CT.Gate CT.H k ("^{" ++ e ++ "}")
gate_trans (S k) = CT.Gate CT.S k ""
gate_trans (Se k e) = CT.Gate CT.S k ("^{" ++ e ++ "}")
gate_trans (X k) = CT.Gate CT.X k ""
gate_trans (Xe k e) = CT.Gate CT.X k ("^{" ++ e ++ "}")
gate_trans (Z k) = CT.Gate CT.Z k ""
gate_trans (Ze k e) = CT.Gate CT.Z k ("^{" ++ e ++ "}")
gate_trans (CX k l) = CT.Ctrl k "" $ CT.Gate CT.Oplus l ""
gate_trans (Ex k) = CT.Gate CT.Ex k ""
gate_trans (CXe k l e) = CT.Ctrl k e $ CT.Gate CT.Oplus l ""
gate_trans (CZ k l) = CT.Ctrl k "" $ CT.Gate CT.Dot l ""
gate_trans (CZe k l e) = CT.Ctrl k e $ CT.Gate CT.Dot l ""
gate_trans (A k s) = CT.Gate (CT.Box CT.A) k s
gate_trans (E k s) = CT.Gate (CT.Box CT.E) k s
gate_trans (B k s) = CT.Gate (CT.Box CT.B) k s
gate_trans (D k s) = CT.Gate (CT.Box CT.D) k s
gate_trans (Mul k s) = CT.Gate CT.Mul k s


cir_trans :: Cir -> CT.Circuit
cir_trans (Cir gl (Spec sp)) = CT.Cir (map gate_trans gl) sp

rel_trans :: Rel -> CT.Relation
rel_trans (Rel rt c1 c2 (Spec sp)) = CT.Rel rt (cir_trans c1) (cir_trans c2) sp

data Command = PrintR Rel | PrintC Cir deriving (Show, Eq, Ord, Read)

exec :: Command -> IO ()
exec (PrintR rel) = putStrLn $ CT.tikz_of_rel $ rel_trans rel
exec (PrintC cir) = putStrLn $ CT.tikz_of_cir $ cir_trans cir

parse :: String -> Command
parse str = if h == "Rel" then PrintR rel else PrintC cir
  where
    h = drop 1 $ head $ words $ dropWhile (' ' == ) str
    ls = lines str
    ls' = filter (\l -> let hw = head (words l) in hw /= "Spec" || hw /= "Comment" ) ls
    specs = map (\l -> unwords $ drop 1 $ words l) $ filter (\l -> let hw = head (words l) in hw == "Spec" ) ls
    uls' = filter (\ x -> '(' /= x || ')' /= x) $ unlines ls'
    ws = words uls'
    ws' = if h == "Rel" then drop 1 ws else ws
    cir = Cir ((read $ unwords $ takeWhile (\ w -> not (isSuffixOf "Cir" w)) $ drop 1 ws') :: [UserGate]) (Spec (specs !! 0))
    cir' = Cir (read $ unwords $ takeWhile (\ w -> not (isSuffixOf "Cir" w)) $ drop 1 $ takeWhile (\ w -> not (isSuffixOf "Cir" w)) $ drop 1 ws') (Spec (specs !! 1))
    rel = Rel (read (head ws)) cir cir' (Spec (specs !! 2))
    

parse' :: String -> Command
parse' str = if h == "Rel" then PrintR rel else PrintC cir
  where
    h = drop 1 $ head $ words $ dropWhile (' ' == ) str
    ls = lines str
    ls' = filter (\l -> let hw = head (words l) in hw /= "Spec" || hw /= "Comment" ) ls
    specs = map (\l -> unwords $ drop 1 $ words l) $ filter (\l -> let hw = head (words l) in hw == "Spec" ) ls
    uls' = filter (\ x -> '(' /= x || ')' /= x) $ unlines ls'
    ws = words uls'
    ws' = if h == "Rel" then drop 1 ws else ws
    cir = Cir ((read $ unwords $ takeWhile (\ w -> not (isSuffixOf "Cir" w)) $ drop 1 ws') :: [UserGate]) (Spec (specs !! 0))
    cir' = Cir (read $ unwords $ takeWhile (\ w -> not (isSuffixOf "Cir" w)) $ drop 1 $ takeWhile (\ w -> not (isSuffixOf "Cir" w)) $ drop 1 ws') (Spec (specs !! 1))
    rel = Rel (read (head ws)) cir cir' (Spec (specs !! 2))
    

main' = do
  as <- getArgs
  print as
  let str = head as
  exec (read str)

ro_cir :: Cir -> Cir
ro_cir (Cir gl sp) = Cir (reverse gl) sp

ro_rel :: Rel -> Rel
ro_rel (Rel rt l r sp) = Rel rt (ro_cir l) (ro_cir r) sp

ro_srel (s , r) = (s , ro_rel r)

-- rels are in circuit order; defs are in matrix mult order
all_rels = box_def
  ++ map (\(x , y) -> (x ,ro_rel y))
  (box_rels_HA
  ++ box_rels_SA
  ++ box_rels_SE
  ++ box_rels_CZL
  ++ box_rels_HB
  ++ box_rels_HD
  ++ box_rels_SbD
  ++ box_rels_StD
  ++ box_rels_CZD
  ++ box_rels_CZDD
  ++ box_rels_CZBB
  ++ box_rels_CZBt)

box_def :: [(String, Rel)]
box_def = [

  ("zmul" , Rel CT.Def (Cir [Mul 0 "b"] (Spec "")) (Cir [Se 0 "1/b", H 0, Se 0 "b", H 0, Se 0 "1/b", H 0] (Spec "")) (Spec "$b\\neq 0$")),
  
  ("abox0b" , Rel CT.Def (Cir [A 0 "{0b}"] (Spec "")) (Cir [Mul 0 "b"] (Spec "")) (Spec "$b\\neq 0$")), 

  ("aboxab" , Rel CT.Def (Cir [A 0 "{ab}"] (Spec "")) (Cir [Mul 0 "a", H 0, Se 0 "-b/a"] (Spec "")) (Spec "$a\\neq 0$")),
  
  ("bbox0b" , Rel CT.Def (Cir [B 0 "{0b}"] (Spec "")) (Cir [Ex 0, CXe 1 0 "b"] (Spec "")) (Spec "")),
  
  ("bbox00" , Rel CT.Def (Cir [B 0 "{ab}"] (Spec "")) (Cir [Ex 0,CXe 1 0 "a",H 1,Se 1 "-b/a"] (Spec "")) (Spec "$a\\neq 0$")),

  ("dbox0b" , Rel CT.Def (Cir [D 0 "{0b}"] (Spec "")) (Cir [Ex 0, CZe 1 0 "-b"] (Spec "")) (Spec "")),
  
  ("dbox00" , Rel CT.Def (Cir [D 0 "{ab}"] (Spec "")) (Cir [Ex 0,CZe 1 0 "-a",H 0,Se 0 "-b/a"] (Spec "")) (Spec "$a\\neq 0$")),

  ("eboxb" , Rel CT.Def (Cir [E 0 "{b}"] (Spec "")) (Cir [Se 0 "-b"] (Spec "")) (Spec ""))
  
          ]


box_rels_HA :: [(String, Rel)]
box_rels_HA = [
  ("HA0b" , Rel CT.Symplectic (Cir [H 0, A 0 "{0b}"] (Spec "")) (Cir [A 0 "{b0}"] (Spec "")) (Spec "$b\\neq 0$")),
  ("HAa0" , Rel CT.Symplectic (Cir [H 0, A 0 "{a0}"] (Spec "")) (Cir [A 0 "{0,-a}"] (Spec "")) (Spec "$a\\neq 0$")),
  ("HAab" , Rel CT.Symplectic (Cir [H 0, A 0 "{ab}"] (Spec "")) (Cir [A 0 "{b,-a}", Se 0 "1/(ab)"] (Spec "")) (Spec "$a,b\\neq 0$"))

           ]


box_rels_SA :: [(String, Rel)]
box_rels_SA = [
  ("SA0b" , Rel CT.Symplectic (Cir [S 0, A 0 "{0b}"] (Spec "")) (Cir [A 0 "{0b}", Se 0 "1/b^2"] (Spec "")) (Spec "$b\\neq 0$")),
  ("SAab" , Rel CT.Symplectic (Cir [S 0, A 0 "{ab}"] (Spec "")) (Cir [A 0 "{a,b-a}"] (Spec "")) (Spec "$a\\neq 0$"))

           ]


box_rels_SE :: [(String, Rel)]
box_rels_SE = [
  ("SA" , Rel CT.Symplectic (Cir [S 0, E 0 "{b}"] (Spec "")) (Cir [E 0 "{b-1}"] (Spec "")) (Spec ""))

           ]


box_rels_CZL :: [(String, Rel)]
box_rels_CZL = [
  ("CZA0b" , Rel CT.Symplectic (Cir [CZ 0 1, A 1 "{0b}"] (Spec "")) (Cir [A 1 "{0b}", CZe 0 1 "1/b"] (Spec "")) (Spec "$b\\neq 0$")),
  ("CZAab" , Rel CT.Symplectic (Cir [CZ 0 1, A 1 "{ab}"] (Spec "")) (Cir [A 0 "{0,-a}", B 0 "{ab}", He 0 "3",  CZe 0 1 "1/a", H 0 ] (Spec "")) (Spec "$a\\neq 0$")),
  
  ("CZA0bB00" , Rel CT.Symplectic (Cir [CZ 0 1, A 0 "{0b}", B 0 "{00}"] (Spec "")) (Cir [A 0 "{0b}", B 0 "{00}",  CZe 0 1 "1/b" ] (Spec "")) (Spec "$b\\neq 0$")),
  ("CZA0bB0d" , Rel CT.Symplectic (Cir [CZ 0 1, A 0 "{0b}", B 0 "{0d}"] (Spec "")) (Cir [A 0 "{0b}", B 0 "{0d}",  Se 0 "-2d/b", CZe 0 1 "1/b" ] (Spec "")) (Spec "$b,d\\neq 0$")),
  ("CZA0bBcd:b/=c" , Rel CT.Symplectic (Cir [CZ 0 1, A 0 "{0b}", B 0 "{cd}"] (Spec "")) (Cir [A 0 "{0,b-c}", B 0 "{cd}", He 0 "3", CZe 0 1 "1/b" ,  H 0,  Mul 0 "b/(b-c)"] (Spec "")) (Spec "$b,c,b-c\\neq 0$")),
  ("CZA0bBcd:b==c" , Rel CT.Symplectic (Cir [CZ 0 1, A 0 "{0b}", B 0 "{cd}"] (Spec "")) (Cir [A 1 "{bd}",  Sep, H 0, CZe 0 1 "-1/b" ,  H 0] (Spec "")) (Spec "$b=c\\neq 0$")),
  ("CZAabB0d" , Rel CT.Symplectic (Cir [CZ 0 1, A 0 "{ab}", B 0 "{0d}"] (Spec "")) (Cir [A 0 "{a,b}", B 0 "{0,d-a}"] (Spec "")) (Spec "$a\\neq 0$")),
  ("CZAabBcd" , Rel CT.Symplectic (Cir [CZ 0 1, A 0 "{ab}", B 0 "{cd}"] (Spec "")) (Cir [A 0 "{a,b-c}", B 0 "{c,d-a}",  H 0, Se 0 "-a/c" ,  He 0 "3"] (Spec "")) (Spec "$a,c\\neq 0$"))

           ]


box_rels_HB :: [(String, Rel)]
box_rels_HB = box_rels_HB_dual_HD ++ box_rels_StB_dual_SbD ++ [
  ("HB" , Rel CT.Symplectic (Cir [S 0, B 0 "{00}"] (Spec "")) (Cir [B 0 "{00}", S 1] (Spec "")) (Spec "")),
  ("HB" , Rel CT.Symplectic (Cir [S 0, B 0 "{0b}"] (Spec "")) (Cir [B 0 "{0b}", S 1, Se 0 "b^2", CZe 0 1 "-b"] (Spec "")) (Spec "$b\\neq 0$")),
  ("HB" , Rel CT.Symplectic (Cir [S 0, B 0 "{ab}"] (Spec "")) (Cir [B 0 "{ab}", S 1, Se 0 "a^2", CZe 0 1 "-a"] (Spec "")) (Spec "$a\\neq 0$"))

           ]


box_rels_HB_dual_HD :: [(String, Rel)]
box_rels_HB_dual_HD = [
  ("HDd" , Rel CT.Symplectic (Cir [H 1, B 0 "{00}"] (Spec "")) (Cir [B 0 "{00}", H 0] (Spec "")) (Spec "")),
  ("HDd" , Rel CT.Symplectic (Cir [H 1, B 0 "{0b}"] (Spec "")) (Cir [B 0 "{b0}"] (Spec "")) (Spec "$b\\neq 0$")),
  ("HDd" , Rel CT.Symplectic (Cir [H 1, B 0 "{a0}"] (Spec "")) (Cir [B 0 "{0,-a}", He 0 "2"] (Spec "")) (Spec "$a\\neq 0$")),
  ("HDd" , Rel CT.Symplectic (Cir [H 1, B 0 "{ab}"] (Spec "")) (Cir [B 0 "{b,-a}", Se 0 "b/a", Mul 0 "b/a"] (Spec "")) (Spec "$a,b\\neq 0$"))
  
           ]

box_rels_StB_dual_SbD :: [(String, Rel)]
box_rels_StB_dual_SbD = [
  ("SDd" , Rel CT.Symplectic (Cir [S 1, B 0 "{0b}"] (Spec "")) (Cir [B 0 "{0b}", S 0] (Spec "")) (Spec "")),
  ("SDd" , Rel CT.Symplectic (Cir [S 1, B 0 "{ab}"] (Spec "")) (Cir [B 0 "{a,b-a}"] (Spec "")) (Spec "$a\\neq 0$"))
  
           ]


box_rels_HD :: [(String, Rel)]
box_rels_HD = [
  ("HD" , Rel CT.Symplectic (Cir [H 0, D 0 "{00}"] (Spec "")) (Cir [D 0 "{00}", H 1] (Spec "")) (Spec "")),
  ("HD" , Rel CT.Symplectic (Cir [H 0, D 0 "{0b}"] (Spec "")) (Cir [D 0 "{b0}"] (Spec "")) (Spec "$b\\neq 0$")),
  ("HD" , Rel CT.Symplectic (Cir [H 0, D 0 "{a0}"] (Spec "")) (Cir [D 0 "{0,-a}", He 1 "2"] (Spec "")) (Spec "$a\\neq 0$")),
  ("HD" , Rel CT.Symplectic (Cir [H 0, D 0 "{ab}"] (Spec "")) (Cir [D 0 "{b,-a}", Se 1 "b/a", Mul 1 "b/a"] (Spec "")) (Spec "$a,b\\neq 0$"))
  
           ]


box_rels_SbD :: [(String, Rel)]
box_rels_SbD = [
  ("SD" , Rel CT.Symplectic (Cir [S 0, D 0 "{0b}"] (Spec "")) (Cir [D 0 "{0b}", S 1] (Spec "")) (Spec "")),
  ("SD" , Rel CT.Symplectic (Cir [S 0, D 0 "{ab}"] (Spec "")) (Cir [D 0 "{a,b-a}"] (Spec "")) (Spec "$a\\neq 0$"))
  
           ]

box_rels_StD :: [(String, Rel)]
box_rels_StD = [
  ("SD" , Rel CT.Symplectic (Cir [S 1, D 0 "{ab}"] (Spec "")) (Cir [D 0 "{ab}", S 0] (Spec "")) (Spec ""))
  
           ]

box_rels_CZD :: [(String, Rel)]
box_rels_CZD = [
  ("CZD" , Rel CT.Symplectic (Cir [CZ 0 1, D 0 "{0b}"] (Spec "")) (Cir [D 0 "{0,b-1}"] (Spec "")) (Spec "")),
  ("CZD" , Rel CT.Symplectic (Cir [CZ 0 1, D 0 "{ab}"] (Spec "")) (Cir [D 0 "{a,b-1}", He 1 "3", Se 1 "-1/a" ,  H 1, Se 0 "a"] (Spec "")) (Spec "$a\\neq 0$"))

             ]



box_rels_CZDD :: [(String, Rel)]
box_rels_CZDD = [
  ("CZD" , Rel CT.Symplectic (Cir [CZ 0 1, D 1 "{0b}", D 0 "{0d}"] (Spec "")) (Cir [D 1 "{0b}", D 0 "{0d}", CZ 1 2] (Spec "")) (Spec "")),
  ("CZD" , Rel CT.Symplectic (Cir [CZ 0 1, D 1 "{ab}", D 0 "{0d}"] (Spec "")) (Cir [D 1 "{ab}", D 0 "{0,d-a}", Sep, He 2 "3", CZ 1 2, H 2] (Spec "")) (Spec "$a\\neq 0$")),
  ("CZD" , Rel CT.Symplectic (Cir [CZ 0 1, D 1 "{0b}", D 0 "{cd}"] (Spec "")) (Cir [D 1 "{0,b-c}", D 0 "{c,d}" ,He 1 "3", CZ 1 2, H 1] (Spec "")) (Spec "$c\\neq 0$")),
  ("CZD" , Rel CT.Symplectic (Cir [CZ 0 1, D 1 "{ab}", D 0 "{cd}"] (Spec "")) (Cir [D 1 "{a,b-c}", D 0 "{c,d-a}", Sep, He 1 "3", Se 1 "-a/c", He 2 "3", Se 2 "-c/a", CZ 1 2, H 2, H 1] (Spec "")) (Spec "$a,c\\neq 0$"))


             ]


box_rels_CZBB :: [(String, Rel)]
box_rels_CZBB = [
  ("CZD" , Rel CT.Symplectic (Cir [CZ 1 2, B 0 "{0b}", B 1 "{0d}"] (Spec "")) (Cir [B 0 "{0b}", B 1 "{0d}", CZ 0 1] (Spec "")) (Spec "")),
  ("CZD" , Rel CT.Symplectic (Cir [CZ 1 2, B 0 "{ab}", B 1 "{0d}"] (Spec "")) (Cir [B 0 "{ab}", B 1 "{0,d-a}", Sep, He 0 "3", CZ 0 1, H 0] (Spec "")) (Spec "$a\\neq 0$")),
  ("CZD" , Rel CT.Symplectic (Cir [CZ 1 2, B 0 "{0b}", B 1 "{cd}"] (Spec "")) (Cir [B 0 "{0,b-c}", B 1 "{c,d}", Sep , He 1 "3", CZ 0 1, H 1] (Spec "")) (Spec "$c\\neq 0$")),
  ("CZD" , Rel CT.Symplectic (Cir [CZ 1 2, B 0 "{ab}", B 1 "{cd}"] (Spec "")) (Cir [B 0 "{a,b-c}", B 1 "{c,d-a}", Sep, He 1 "3", Se 1 "-a/c", He 0 "3", Se 0 "-c/a", CZ 0 1, H 0, H 1] (Spec "")) (Spec "$a,c\\neq 0$"))


             ]

box_rels_CZBt :: [(String, Rel)]
box_rels_CZBt = [
  ("SD" , Rel CT.Symplectic (Cir [CZ 0 1, B 1 "{0b}"] (Spec "")) (Cir [B 1 "{0b}", Ex 0, CZ 1 2, Ex 0, CZe 0 1 "-b"] (Spec "")) (Spec "")),
  ("SD" , Rel CT.Symplectic (Cir [CZ 0 1, B 1 "{ab}"] (Spec "")) (Cir [B 1 "{ab}", Ex 0, CZ 1 2, Ex 0, CZe 0 1 "-a"] (Spec "")) (Spec "$a\\neq 0$"))
  
           ]

pcir_trans :: (Cir, PositionSpec) -> (Circuit, PositionSpec)
pcir_trans (c , p) = (cir_trans c, p)
