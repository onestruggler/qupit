
class ToAgda a where
  toagda :: a -> String

instance ToAgda Gate where
  toagda X = "X"
  toagda Z = "Z"
  toagda H = "H"
  toagda HH = "HH"
  toagda S = "S"
  toagda T = "T"
  toagda Iz = "ζ"

instance ToAgda a => ToAgda [a] where
  toagda [] = "ε"
  toagda [h] = toagda h
  toagda (h : t) = toagda h ++ toagda t

c1 = [[], [X], [X,X]]
c2 = [[], [S], [S,S]]
cc = [[], [X], [X,X], [X,S], [X,X,S], [X,S,X], [X,X,S,X],[X,S,X,X], [X,X,S,X,X]]

toagdaC1 :: [Gate] -> String
toagdaC1 x = toagda x ++ "-cr"

toagdaCs :: [[Gate]] -> String
toagdaCs xss = intercalate "\n" $ map (\x -> toagda x ++ "-cr : C") xss

xss :: [[Gate]]
xss = [replicate k Iz ++ replicate l S | k <- [0..8], l <- [0..8]]

find_action c y = find (\(xs, c') -> xs ++ c' == c ++ [y]) [(xs, c') | xs <- xss, c' <- cc]

h_table = [((c, y), (xs, c')) | y <- [Iz,S,X], c <- cc, let Just (xs, c') = find_action c y] 

toagda_gen :: Gate -> String
toagda_gen X = "X-gen"
toagda_gen Z = "Z-gen"
toagda_gen S = "S-gen"
toagda_gen H = "H-gen"
toagda_gen HH = "HH-gen"
toagda_gen T = "T-gen"
toagda_gen Iz = "ζ-gen"

toagda_cir :: [Gate] -> String
toagda_cir [] = "ε"
toagda_cir xs = intercalate " • " $ map toagda xs

toagda_htable1 ((c, y), (xs, c')) = "h " ++ toagdaC1 c ++ " " ++ toagda_gen y ++ " = " ++  toagda_cir xs ++ " , " ++ toagdaC1 c'

toagda_htable xs = intercalate "\n" $ map toagda_htable1 xs


toagda_sem1 x = "[ " ++ toagdaC1 x ++ " ] = " ++ toagda_cir x
toagda_sem xs = intercalate "\n" $ map toagda_sem1 xs
