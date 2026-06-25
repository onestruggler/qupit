{-# OPTIONS_GHC -w #-}
module Cir2Tikz where

import Data.String
import Data.List
import Text.Printf
import Control.Monad.State

import qualified Data.Map as Map
import Data.Map (Map)
import Prelude hiding (Right, Left)

type Arity = Int


data BoxType = A | B | D | E | L Int | M Int | LM Int deriving (Show, Eq, Ord)

data GateType = H | S | Z | X | Y | Ex | Box BoxType | Oplus | Dot | Mul deriving (Show, Eq, Ord)

-- Erase edges must be drawed at last. An erase egde is just a white
-- edge.
data WireType = Bit | QBit | Control | Swap | Black | White | Erase deriving (Show, Eq, Ord)

arity_b :: BoxType -> Arity
arity_b A = 1
arity_b E = 1
arity_b B = 2
arity_b D = 2
arity_b (L h) = h
arity_b (M h) = h
arity_b (LM h) = h


arity :: GateType -> Arity
arity H = 1
arity S = 1
arity Oplus = 1
arity Dot = 1
arity Z = 1
arity X = 1
arity Ex = 2
arity (Box bt) = arity_b bt
arity Mul = 1

-- In Ctrl i s g, s is the parameter for control dot, which will be
-- put above the dot. (This not always works the best).
data Gate = Gate GateType Int String | Ctrl Int String Gate | Sep deriving (Show, Eq, Ord)

width_between_two_gates = 1 -- tikz length unit
width_between_a_gate_and_empty = 1
height_between_two_wires = 2
height_between_two_vertical_arranged_circuits = 3.5
standard_gate_width = 1.5
standard_gate_height = 1.5 -- single qubit gate
standard_binary_gate_height = 3 -- binary qubit gate
standard_nary_gate_height k = k + 1 -- k qubit gate

-- a modified version of length function on Strings.
string_width :: String -> Float
string_width str = fromIntegral lc * 0.1 + fromIntegral lo * 0.25
  where
    commas = filter (\x -> x == ',') str
    lc = length commas
    lo = length str - lc

width :: Gate -> Float
width (Gate Oplus _ str) = standard_gate_width
width (Gate Dot _ str) = standard_gate_width
width (Gate (Box bt) _ str) = standard_gate_width + (fromIntegral l * 0.25)
  where
    l = length $ filter (\x -> not (elem x "{},^_$")) str
width (Gate _ _ str) = if l < 4 then standard_gate_width else 1 + standard_gate_width
  where
    l = length $ filter (\x -> not (elem x "{},^_$")) str
width (Ctrl k str g) = width g

-- a circuit is a list of gates together with some specification on
-- gate parameters.

data Circuit = Cir [Gate] String deriving (Show, Eq, Ord)

-- A relaiton is a pair of circuits together with some specification
-- on gate parameters and a Relation type.

data RelType = Def | Symplectic | SymplecticPauli | Clifford | Empty | RightArrow deriving (Show, Eq, Ord, Read)
data Relation = Rel RelType Circuit Circuit String deriving (Show, Eq, Ord)

target_wire_of :: Gate -> [Int]
target_wire_of Sep = []
target_wire_of (Gate gt w str) = [w .. w + arity gt - 1]
target_wire_of (Ctrl k str g) = target_wire_of g

wires_of_gate :: Gate -> [Int]
wires_of_gate (Sep) = []
wires_of_gate (Ctrl k str g) = k : wires_of_gate g
wires_of_gate (Gate gt w str) = [w .. w + arity gt - 1]

-- return list of gates only on a particular wire.
gates_on_wire :: Circuit -> Int -> [Gate]
gates_on_wire (Cir gl sp) k  = filter (f k) gl
  where
    f :: Int -> Gate -> Bool
    f k (Gate gt w s) = elem k [w .. w + arity gt - 1]

-- return all wires in a circuit.
wires_of_cir :: Circuit -> [Int]
wires_of_cir (Cir gl sp) = [minimum t .. maximum t]
  where
    t = nub $ concat $ map wires_of_gate gl

-- If a gate is any of CZ, CCZ,..., pick maximum wire index as the
-- control qubit. Later, this can be extended to any controlled
-- diagnoal gates like CS, CCT, etc.
maximize_ctrl_wire1 :: Gate -> Gate
maximize_ctrl_wire1 (Ctrl k sp (Gate Dot l sp')) = Ctrl k' sp  (Gate Dot l' sp')
  where
    k' = maximum [k , l]
    l' = minimum [k , l]
maximize_ctrl_wire1 (Ctrl k sp g2@(Ctrl k2 sp2 (Gate Dot l sp'))) = Ctrl k' sp  (Ctrl k2'' sp2' g3)
  where
    g2'@(Ctrl k2' sp2' g3) = maximize_ctrl_wire1 g2
    k' = maximum [k , k2']
    k2'' = minimum [k , k2']
maximize_ctrl_wire1 g = g    

maximize_ctrl_wire :: Circuit -> Circuit
maximize_ctrl_wire (Cir gl sp) = Cir gl' sp
  where
    gl' = map maximize_ctrl_wire1 gl



-- go through gate list and assign node index and node x-coordinates.
assign_nodes_x_to_gates_lm :: Float -> Circuit -> [(Gate , Float)]
assign_nodes_x_to_gates_lm lm (Cir gl sp) = aux Map.empty gl
  where
    -- Map Int Float is a memory that keeps track of the x coord that
    -- has been assigned to a particular wire.
    aux :: Map Int Float -> [Gate] -> [(Gate , Float)]
    aux mem [] = []
    aux mem (h@Sep : t) = [(h , x)] ++ aux mem' t
      where
        rm = maximum $ map (\k -> Map.findWithDefault lm k mem) (wires_of_cir (Cir (h : t) ""))
        x = rm
        mem' = (Map.fromList (map (\k -> (k,rm)) (wires_of_cir (Cir (h : t) ""))))
        
    aux mem (h@(Ctrl w str g) : t) = [(h , x)] ++ aux mem' t
      where
        rm = maximum $ map (\k -> Map.findWithDefault lm k mem) (wires_of_gate h)
        x = rm + width h / 2 + 1
        rm' = rm + width h + 1
        -- note that Map.union favors the left argument.
        mem' = Map.union (Map.fromList (map (\k -> (k,rm')) (wires_of_gate h))) mem

    aux mem (h@(Gate gt w str):t) = [(h , x)] ++ aux mem' t
      where
        rm = maximum $ map (\k -> Map.findWithDefault lm k mem) (wires_of_gate h)
        x = rm + width h / 2 + 1
        rm' = rm + width h + 1
        -- note that Map.union favors the left argument.
        mem' = Map.union (Map.fromList (map (\k -> (k,rm')) (wires_of_gate h))) mem 


assign_nodes_x_to_gates = assign_nodes_x_to_gates_lm 0



width_of_cir :: Circuit -> Float
width_of_cir cir@(Cir gl sp) = 1 + if max_x == 0 then 1 else max_x + 0.75
  where
    gn = assign_nodes_x_to_gates cir
    (gm , max_x) = maximumBy (\(f1,s1) (f2,s2) -> compare s1 s2) gn


height_of_cir :: Circuit -> Float
height_of_cir cir@(Cir gl sp) = fromIntegral (( ws - 1 + (if sp == "" then 0 else 1)) * 2)
  where
    ws' = nub $ sort $ wires_of_cir cir
    ws = maximum ws' - minimum ws' + 1
    

-- ymid does not count the caption node.  
ymid_of_cir :: Circuit -> Float
ymid_of_cir cir@(Cir gl sp) =
  if odd l then mid else mid - 1
  where
    ws = nub $ sort $ wires_of_cir cir
    l = length ws
    hl = l `div` 2
    mid = fromIntegral $ head ws + 2 * hl


class TikzPrint a where
  tprint :: a -> String

data NodeType = NONE | CTRL | GATE | TARG | BT BoxType deriving (Eq, Ord, Show)
instance TikzPrint NodeType where
  tprint NONE = "none"
  tprint CTRL = "cnot ctrl"
  tprint TARG = "cnot targ"
  tprint GATE = "gate"
  tprint (BT bt) = show bt

type Id = String

--- A node is (id , nt , label, x , y).
data Node = Node Id NodeType String Float Float deriving (Eq, Ord, Show)
instance TikzPrint Node where
  tprint (Node id nt label x y) = printf "\\node [style=%s] (%s) at (%f, %f) {$%s$};\n" (tprint nt) id x y label

--- An edge is (wiretype, id, id).
data Edge = Edge WireType Id Id deriving (Eq, Ord)
instance TikzPrint Edge where
  tprint (Edge QBit idl idr) = printf "\\draw (%s.center) to (%s.center);\n" idl idr
  tprint (Edge Swap idl idr) = printf "\\draw (%s.center) to (%s.center);\n" idl idr
  tprint (Edge Erase idl idr) = printf "\\draw [color=white] (%s.center) to (%s.center);\n" idl idr
  tprint _ = error "Edge tprint: wire type undefined"

-- Rectangular region, on which a single circuit is drawing on. Given
-- a bottom left coordinate, by calculating the width and height of
-- the circuit we can decide the region.

-- RR bottom left top right.
data RectRegion = RR Float Float Float Float deriving (Eq, Ord, Show)

type TikzState = (Float, Float, String)

nt_of_gate :: Gate -> NodeType
nt_of_gate (Gate Oplus _ _) = TARG
nt_of_gate (Gate Dot _ _) = CTRL
nt_of_gate (Gate Ex _ _) = NONE
nt_of_gate (Gate (Box bt) _ _) = BT bt
nt_of_gate (Gate _ _ _) = GATE

nodes_of_cir :: Float -> Float -> Circuit -> [Node]
nodes_of_cir b l cir@(Cir gl sp) = ns
  where
    xs = assign_nodes_x_to_gates_lm l cir
    prefix = "l" ++ show (round l)
    unJust (Just x) = x
    ns = map (\gx@(g@(Gate _ w str), x) -> Node (prefix ++ show (unJust (elemIndex gx xs))) (nt_of_gate g) str x (fromIntegral w * 2) ) xs

-- draw a gate with node-name and x-coord; if the gate is a controlled
-- gate, also output the (ctrl, target) pair; if the gate is Swap,
-- draw four nodes and also output two pairs for cross wires.
draw_gate_yshift :: Float -> (Gate, String, Float) -> (String , [(WireType , (String, String))])

-- cnot targ is used in the .tikzstyles file for \oplus (it should be
-- called "oplus"). This is another way to draw not gate.
draw_gate_yshift yshift (Sep, i , x) = (printf "\\node [style=none] (%s) at (%f, %f) {$%s$};\n" i x (fromIntegral 0 * 2 + yshift :: Float) "" , [])
draw_gate_yshift yshift (Gate Oplus w str, i , x) = (printf "\\node [style=cnot targ] (%s) at (%f, %f) {$%s$};\n" i x (fromIntegral w * 2 + yshift :: Float) str , [])

-- Another way to draw Z gate.
draw_gate_yshift yshift (Gate Dot w str, i , x) = (printf "\\node [style=cnot ctrl] (%s) at (%f, %f) {$%s$};\n" i x (fromIntegral w * 2 + yshift :: Float) str , [])

draw_gate_yshift yshift (Gate Mul w str, i , x) = (printf "\\node [style=gate] (%s) at (%f, %f) {$%s$};\n"i x (fromIntegral w * 2 + yshift :: Float) str , [])

draw_gate_yshift yshift (Gate Ex w str, i , x) = (
  printf "\\node [style=none] (%stl) at (%f, %f) {$%s$};\n"i (x - 0.75) ((y + yshift) + 2) str ++
  printf "\\node [style=none] (%sbl) at (%f, %f) {$%s$};\n"i (x - 0.75) (y + yshift) str ++
  printf "\\node [style=none] (%sbr) at (%f, %f) {$%s$};\n"i (x + 0.75) (y + yshift) str ++
  printf "\\node [style=none] (%str) at (%f, %f) {$%s$};\n"i (x + 0.75) ((y + yshift) + 2) str ++
  printf "\\node [style=none] (%sftl) at (%f, %f) {};\n"i (x - 0.75) ((y + yshift) + 2 + 0.15) ++
  printf "\\node [style=none] (%sfbr) at (%f, %f) {};\n"i (x + 0.75) ((y + yshift) - 0.15) ,
  wps)
  where
    wps =
      (Erase , (i++"ftl" , i ++ "fbr")) :
      (Black , (i++"bl" , i ++ "tr")) :
      (Black , (i++"tl" , i ++ "br")) :
      []
    y = (fromIntegral (w * 2) :: Float)


draw_gate_yshift yshift (Gate (Box bt) w str, i , x) = (printf "\\node [style=%s box] (%s) at (%f, %f) {$%s$};\n" (show bt) i x (fromIntegral w * 2 + yshift + (fromIntegral (arity_b bt - 1)) :: Float) (show bt ++ "_{" ++ str ++ "}") , [])

draw_gate_yshift yshift (Gate gt w str, i , x) = (printf "\\node [style=gate] (%s) at (%f, %f) {$%s$};\n" i x (fromIntegral w * 2 + yshift :: Float) (show gt ++ str) , [])
-- cnot ctrl is used in the .tikzstyles file for any kinds of
-- control. (it should be called "dot")
draw_gate_yshift yshift (Ctrl w str g, i , x) = (
  (if bb then
    printf "\\node [style=cnot ctrl, label={above:$%s$}] (%s) at (%f, %f) {};\n" str i x (fromIntegral w * 2 + yshift :: Float) else
    printf "\\node [style=cnot ctrl, label={above:$%s$}] (%s) at (%f, %f) {};\n" "" i x (fromIntegral w * 2 + yshift :: Float) ++ 
    printf "\\node [style=none, label={[yshift=0.5em]$%s$}] (%s) at (%f, %f) {};\n" str (i++"tarab") x (fromIntegral w' * 2 + yshift :: Float))
    ++ ihd
  , cts')
  where
    bb = w >= head (target_wire_of g)
    w' = if w >= head (target_wire_of g) then w else head (target_wire_of g)
    (ihd , cts) = draw_gate_yshift yshift (g , i++"t" , x)
    cts' = (Control , (i , i ++ "t")) : cts





-- draw a gate with node-name and x-coord; if the gate is a controlled
-- gate, also output the (ctrl, target) pair; if the gate is Swap,
-- draw four nodes and also output two pairs for cross wires.
draw_gate :: (Gate, String, Float) -> (String , [(WireType , (String, String))])

-- cnot targ is used in the .tikzstyles file for \oplus (it should be
-- called "oplus"). This is another way to draw not gate.
draw_gate (Gate Oplus w str, i , x) = (printf "\\node [style=cnot targ] (%s) at (%f, %f) {$%s$};\n" i x (fromIntegral w * 2 :: Float) str , [])

-- Another way to draw Z gate.
draw_gate (Gate Dot w str, i , x) = (printf "\\node [style=cnot ctrl] (%s) at (%f, %f) {$%s$};\n" i x (fromIntegral w * 2 :: Float) str , [])

draw_gate (Gate Mul w str, i , x) = (printf "\\node [style=gate] (%s) at (%f, %f) {$%s$};\n"i x (fromIntegral w * 2 :: Float) str , [])

draw_gate (Gate Ex w str, i , x) = (
  printf "\\node [style=none] (%stl) at (%f, %f) {$%s$};\n"i (x - 0.75) (y + 2) str ++
  printf "\\node [style=none] (%sbl) at (%f, %f) {$%s$};\n"i (x - 0.75) y str ++
  printf "\\node [style=none] (%sbr) at (%f, %f) {$%s$};\n"i (x + 0.75) y str ++
  printf "\\node [style=none] (%str) at (%f, %f) {$%s$};\n"i (x + 0.75) (y + 2) str ++
  printf "\\node [style=none] (%sftl) at (%f, %f) {};\n"i (x - 0.75) (y + 2 + 0.15) ++
  printf "\\node [style=none] (%sfbr) at (%f, %f) {};\n"i (x + 0.75) (y - 0.15) ,
  wps)
  where
    wps =
      (Erase , (i++"ftl" , i ++ "fbr")) :
      (Black , (i++"bl" , i ++ "tr")) :
      (Black , (i++"tl" , i ++ "br")) :
      []
    y = (fromIntegral (w * 2) :: Float)


draw_gate (Gate (Box bt) w str, i , x) = (printf "\\node [style=%s box] (%s) at (%f, %f) {$%s$};\n" (show bt) i x (fromIntegral w * 2 + (fromIntegral (arity_b bt - 1)) :: Float) (show bt ++ "_{" ++ str ++ "}") , [])

draw_gate (Gate gt w str, i , x) = (printf "\\node [style=gate] (%s) at (%f, %f) {$%s$};\n" i x (fromIntegral w * 2 :: Float) (show gt ++ str) , [])
-- cnot ctrl is used in the .tikzstyles file for any kinds of
-- control. (it should be called "dot")
draw_gate (Ctrl w str g, i , x) = (
  printf "\\node [style=cnot ctrl, label={above:$%s$}] (%s) at (%f, %f) {};\n" str i x (fromIntegral w' * 2 :: Float) ++ ihd
  , cts')
  where
    w' = if w >= head (target_wire_of g) then w else head (target_wire_of g)
    (ihd , cts) = draw_gate (g , i++"t" , x)
    cts' = (Control , (i , i ++ "t")) : cts

draw_gates_yshift_lm :: Float -> Float -> Circuit -> (String , [(WireType , (String, String))])
draw_gates_yshift_lm yshift lm cir@(Cir gl sp) = (concat fdgs , nub (concat sdgs))
  where
    gn = assign_nodes_x_to_gates_lm lm cir
    prefix = "n" ++ show (round lm :: Int) ++ "y" ++ show (round yshift :: Int)
    gnn = zipWith (\ a (b , c) -> (b , a , c)) (map (prefix++) $ map show [0..length gl]) gn
    dgs = map (draw_gate_yshift yshift) gnn
    fdgs = map fst dgs
    sdgs = map snd dgs


draw_gates :: Float -> Float -> Circuit -> (String , [(WireType , (String, String))])
draw_gates = draw_gates_yshift_lm 


-- draw all qubit wire ends.
draw_invisible_nodes :: Circuit -> (String , [(WireType, (String, String))])
draw_invisible_nodes = draw_invisible_nodes_yshift_lm 0 0

draw_invisible_nodes_lm :: Float -> Circuit -> (String , [(WireType, (String, String))])
draw_invisible_nodes_lm lm cir@(Cir gl sp) = (str , lrs')
  where
    ws = nub $ sort $ wires_of_cir cir
    wd = width_of_cir cir
    prefix = if lm == 0 then "" else "lm"
    lnns = (map (prefix++) $ map ("el"++) $ map show ws)
    rnns = (map (prefix++) $ map ("er"++) $ map show ws)
    lcoords :: [(Float, Float)]
    lcoords = map (\ w -> (lm , fromIntegral w * 2)) ws
    rcoords = map (\ w -> (lm + wd, fromIntegral w * 2)) ws
    qwns = zip (lnns ++ rnns) (lcoords ++ rcoords)
    draw1 :: (String, (Float, Float)) -> String
    draw1 (n, (x , y)) = printf "\\node [style=none] (%s) at (%f, %f){};\n" n x y
    str = concat $ map draw1 qwns
    lrs = zip lnns rnns
    lrs' = map (\x -> (QBit, x)) lrs


draw_invisible_nodes_yshift_lm :: Float -> Float -> Circuit -> (String , [(WireType, (String, String))])
draw_invisible_nodes_yshift_lm yshift lm cir@(Cir gl sp) = (str , lrs')
  where
    ws' = nub $ sort $ wires_of_cir cir
    ws = [minimum ws' .. maximum ws']
    wd = width_of_cir cir
    prefix = "lm" ++ show (round lm :: Int)
    lnns = (map (prefix++) $ map (\ x -> "el"++ x ++ show (round yshift)) $ map show ws)
    rnns = (map (prefix++) $ map (\ x -> "er"++ x ++ show (round yshift)) $ map show ws)
    lcoords :: [(Float, Float)]
    lcoords = map (\ w -> (lm , fromIntegral w * 2)) ws
    rcoords = map (\ w -> (lm + wd, fromIntegral w * 2)) ws
    qwns = zip (lnns ++ rnns) (lcoords ++ rcoords)
    draw1 :: (String, (Float, Float)) -> String
    draw1 (n, (x , y)) = printf "\\node [style=none] (%s) at (%f, %f){};\n" n x (y + yshift)
    str = concat $ map draw1 qwns
    lrs = zip lnns rnns
    lrs' = map (\x -> (QBit, x)) lrs



wire_layer_header = "\\begin{pgfonlayer}{edgelayer}\n"
wire_layer_ender = "\\end{pgfonlayer}\n"

node_layer_header = "\\begin{pgfonlayer}{nodelayer}\n"
node_layer_ender = "\\end{pgfonlayer}\n"

tikz_header = "\\begin{tikzpicture}\n"
tikz_ender = "\\end{tikzpicture}\n"


-- for drawing qubit wire, control wire, and swap wire.
draw_lines :: [(WireType, (String, String))] -> String
draw_lines [] = ""
draw_lines ((QBit, (l,r)):t) = "\\draw (" ++  l ++ ".center) to (" ++  r ++ ".center);\n" ++ draw_lines t
draw_lines ((Control, (l,r)):t) = "\\draw (" ++  l ++ ".center) to (" ++  r ++ ".center);\n" ++ draw_lines t
draw_lines ((White, (l,r)):t) = "\\draw [color=white] (" ++  l ++ ".center) to (" ++  r ++ ".center);\n" ++ draw_lines t
draw_lines ((Erase, (l,r)):t) = "\\fill [white] (" ++ l ++ ".center) rectangle (" ++ r ++ ".center);\n" ++ draw_lines t
draw_lines ((Black, (l,r)):t) = "\\draw (" ++  l ++ ".center) to (" ++  r ++ ".center);\n" ++ draw_lines t

draw_cir_spec :: Circuit -> String
draw_cir_spec = draw_cir_spec_yshift_lm 6 0

draw_cir_spec_yshift_lm :: Float -> Float -> Circuit -> String
draw_cir_spec_yshift_lm yshift lm cir@(Cir gl sp) = printf "\\node [style=none, label={above:%s}] (%sspec) at (%f, %f) {};\n" sp prefix x (y + yshift)
  where
    prefix = if lm == 0 then "" else "lm" ++ (printf "%d" (round lm :: Int))
    x :: Float
    x = lm + width_of_cir cir / 2
    bot = minimum $ wires_of_cir cir
    y :: Float
    y = fromIntegral bot - 2


draw_cir_spec_lm :: Float -> Circuit -> String
draw_cir_spec_lm lm cir@(Cir gl sp) = printf "\\node [style=none, label={above:%s}] (%sspec) at (%f, %f) {};\n" sp prefix x y
  where
    prefix = if lm == 0 then "" else "lm" ++ (printf "%d" (round lm :: Int))
    x :: Float
    x = lm + width_of_cir cir / 2
    bot = minimum $ wires_of_cir cir
    y :: Float
    y = fromIntegral bot - 2

tikz_of_cir_yshift_lm :: Float -> Float -> Circuit -> String
tikz_of_cir_yshift_lm  yshift' lm cir@(Cir gl sp) = tns ++ tws
  where
    yshift = if sp == "" then yshift' else yshift' + 2
    cir' = maximize_ctrl_wire cir
    (gs , cts) = draw_gates_yshift_lm yshift lm cir'
    (is , lrs) = draw_invisible_nodes_yshift_lm yshift lm cir'
    ls = lrs ++ cts
    tns = node_layer_header ++ gs ++ is ++ (if sp == "" then "" else draw_cir_spec_yshift_lm yshift lm cir) ++ node_layer_ender
    tws = wire_layer_header ++ draw_lines ls ++ wire_layer_ender



tikz_of_cir :: Circuit -> String
tikz_of_cir cir@(Cir gl sp) = tikz_header ++ tikz_of_cir_yshift_lm 0 0 cir ++ tikz_ender

sign_of_reltype :: RelType -> String
sign_of_reltype Def = "\\equiv"
sign_of_reltype Symplectic = "\\equiv_{s}"

wires_of_rel :: Relation -> [Int]
wires_of_rel (Rel rt cir cir1 rsp) = wires_of_cir cir ++ wires_of_cir cir1

draw_rel_sign :: Relation -> String
draw_rel_sign (Rel rt cir@(Cir gl sp) cir1@(Cir gl1 sp1) rsp) = printf "\\node [style=none] (equiv) at (%f, %f) {$%s$};\n" x y (sign_of_reltype rt)
  where
    x :: Float
    x = width_of_cir cir + 1
    y :: Float
    y = ymid_of_cir cir


draw_rel_sign_yshift :: Float -> Relation -> String
draw_rel_sign_yshift yshift (Rel rt cir@(Cir gl sp) cir1@(Cir gl1 sp1) rsp) = printf "\\node [style=none] (equiv) at (%f, %f) {$%s$};\n" x y (sign_of_reltype rt)
  where
    x :: Float
    x = width_of_cir cir + 1
    y :: Float
    y = ymid_of_cir cir + yshift


draw_rel_spec :: Relation -> String
draw_rel_spec rel@(Rel rt cir@(Cir gl sp) cir1@(Cir gl1 sp1) rsp) = if rsp == "" then "" else printf "\\node [style=none,label={right:%s}] (rspec) at (%f, %f) {};\n" rsp  x y
  where
    x :: Float
    x = width_of_cir cir + 1 + width_of_cir cir1 + 1.5
    y :: Float
    y = ymid_of_cir cir1

draw_rel_spec_yshift :: Float -> Relation -> String
draw_rel_spec_yshift yshift rel@(Rel rt cir@(Cir gl sp) cir1@(Cir gl1 sp1) rsp) = if rsp == "" then "" else printf "\\node [style=none,label={right:%s}] (rspec) at (%f, %f) {};\n" rsp  x y
  where
    x :: Float
    x = width_of_cir cir + 1 + width_of_cir cir1 + 1.5
    y :: Float
    y = ymid_of_cir cir1 + yshift


width_of_rel :: Relation -> Float
width_of_rel rel@(Rel rt cir@(Cir gl sp) cir1@(Cir gl1 sp1) rsp) = x
  where
    l = length $ filter (\x -> not (elem x "{},^_$")) rsp
    x :: Float
    x = width_of_cir cir + 1 + width_of_cir cir1 + 1.5 + (fromIntegral l / 2)
    


tikz_of_rel :: Relation -> String
tikz_of_rel rel@(Rel rt cir@(Cir gl sp) cir1@(Cir gl1 sp1) rsp) = tikz_header ++ dc1 ++ draw_rel_sign rel ++ dc2 ++ draw_rel_spec rel ++ tikz_ender
  where
    dc1 = tikz_of_cir_yshift_lm 0 0 cir
    lm = width_of_cir cir + 2
    dc2 = tikz_of_cir_yshift_lm 0 lm cir1

tikz_of_rel_noheader_ender_yshift :: Float -> Relation -> String
tikz_of_rel_noheader_ender_yshift yshift rel@(Rel rt cir@(Cir gl sp) cir1@(Cir gl1 sp1) rsp) = dc1 ++ draw_rel_sign_yshift yshift rel ++ dc2 ++ draw_rel_spec_yshift yshift rel
  where
    dc1 = tikz_of_cir_yshift_lm yshift 0 cir
    lm = width_of_cir cir + 2
    dc2 = tikz_of_cir_yshift_lm yshift lm cir1


height_of_rel :: Relation  -> Float
height_of_rel rel@(Rel rt cir@(Cir gl sp) cir1@(Cir gl1 sp1) rsp) = max w1 w2
  where
    w1 = height_of_cir cir
    w2 = height_of_cir cir1


tikz_of_rels_yshift :: Float -> [Relation] -> (String, Float)
tikz_of_rels_yshift y [rel] = (tikz_of_rel_noheader_ender_yshift y rel, y + height_of_rel rel + 2.5)
tikz_of_rels_yshift y (h:t) = (tikz_of_rel_noheader_ender_yshift (snd ih) h ++ (fst ih), height_of_rel h + 2.5 + (snd ih))
  where
    ih = tikz_of_rels_yshift y t


tikz_of_rels :: [Relation] -> String
tikz_of_rels rs = tikz_header ++ (fst $ tikz_of_rels_yshift 0 rs) ++ tikz_ender


data Direction = Up | Down | Right | Left | LU | LD | RU | RD deriving (Show, Eq, Ord)
data PositionSpec = PositionSpec Direction String deriving (Show, Eq, Ord)

-- Note: in [(cir1, pspec1), (cir2, pspec2) ...], pspec1 specifies the
-- relative position of cir2 w.r.t cir1, and the connective between
-- them. The last pspec is discarded.
tikz_of_pcir_xy :: Float -> Float -> [(Circuit, PositionSpec)] -> String
tikz_of_pcir_xy xshift yshift [h] = dh
  where
    (hc , hp@(PositionSpec dir si)) = h
    dh = tikz_of_cir_yshift_lm yshift xshift hc
tikz_of_pcir_xy xshift yshift (h:t) = dh ++ draw_connective ++ ihc
  where
    (hc , hp@(PositionSpec dir si)) = h
    dh = tikz_of_cir_yshift_lm yshift xshift hc
    (x' , y') = case dir of
      Right -> (xshift + width_of_cir hc + 2, yshift)
      Left -> (xshift - (width_of_cir hc + 2), yshift)
      Down -> (xshift , yshift - (height_of_cir hc + height_between_two_vertical_arranged_circuits))
      Up -> (xshift , yshift + (height_of_cir hc + 2))
      RU -> (xshift + (width_of_cir hc + 2), yshift + (height_of_cir hc + 2))
      RD -> (xshift + (width_of_cir hc + 2), yshift - (height_of_cir hc + 2))
      LD -> (xshift - (width_of_cir hc + 2), yshift - (height_of_cir hc + 2))
      LU -> (xshift - (width_of_cir hc + 2), yshift + (height_of_cir hc + 2))

    hw = width_of_cir hc / 2
    hh = height_of_cir hc / 2
    draw_connective :: String
    draw_connective = case dir of
      Right -> printf "\\node [style=none] (equiv) at (%f, %f) {$%s$};\n" (x' - 1) (yshift + hh) si
      Left -> printf "\\node [style=none,rotate=180] (equiv) at (%f, %f) {$%s$};\n" (x' + 1) (yshift + hh) si
      Down -> printf "\\node [style=none,rotate=-90] (equiv) at (%f, %f) {$%s$};\n" (xshift + hw) (yshift - height_between_two_vertical_arranged_circuits / 2) si
      Up -> printf "\\node [style=none,rotate=90] (equiv) at (%f, %f) {$%s$};\n" (xshift + hw) (y' - 1) si
      LU -> printf "\\node [style=none,rotate=135] (equiv) at (%f, %f) {$%s$};\n" (x' + 1) (y' - 1) si
      LD -> printf "\\node [style=none,rotate=-135] (equiv) at (%f, %f) {$%s$};\n" (x' + 1) (y' + 1) si
      RD -> printf "\\node [style=none,rotate=-45] (equiv) at (%f, %f) {$%s$};\n" (x' - 1) (y' + 1) si
      RU -> printf "\\node [style=none,rotate=45] (equiv) at (%f, %f) {$%s$};\n" (x' - 1) (y' - 1) si

    ihc = tikz_of_pcir_xy x' y' t
    
tikz_of_pcir cir = tikz_header ++ tikz_of_pcir_xy 0 0 cir ++ tikz_ender
