-- Inf2d Assignment 1 2013-14
-- PLEASE DO NOT SUBMIT THIS FILE

module Examples where

import Data.List
import Data.Maybe
import CSPframework

{-
Some examples of constraints and CSPs.

Petros Papapanagiotou
School of Informatics
University of Edinburgh
2014

-}

-- *******************************************
-- ** Examples of Relations and Constraints **
-- *******************************************

-- Binary constraint stating that two variables must be different.
varsDiffConstraint :: Var -> Var -> Constraint
varsDiffConstraint a b = CT (a ++ " /= " ++ b,[a,b],varsDiff)

-- Relation that ensures two variables are different.
-- It is satisfied if either variable is unassigned.
varsDiff :: Relation
varsDiff vars assignment = not $ valsEq (lookupVar assignment a) (lookupVar assignment b)
  where a = head vars
        b = head $ tail vars


-- N-ary constraint stating that all variables in a list must have have distinct values.
allDiffConstraint :: [Var] -> Constraint
allDiffConstraint vs = CT ("All Diff: " ++ (show vs),vs,allDiff)

-- Relation that ensures a list of variables are all different.
-- Ignores unassigned variables.
allDiff :: Relation
allDiff vs a = length l == length (nub l) 
  where l = filter isJust $ map (lookupVar a) vs



-- N-ary constraint stating that the sum of a list of variables must have a specific value.
sumConstraint :: [Var] -> Int -> Constraint
sumConstraint vs i = CT (showsum ++ " = " ++ (show i),vs,haveSum i)
  where showsum =  (\l -> foldl (\a b ->  a ++ " + " ++ b) (head l) (tail l)) $ vs

-- Relation that ensures the sum of the variables is equal to the given value.
-- It is satisfied if at least one of the variables is unassigned.
haveSum :: Int -> Relation
haveSum sum vars assignment
  | t = (foldl (+) 0 $ map fromJust l) == sum
  | otherwise = True
    where l = map (lookupVar assignment) vars
          t = all isJust l
                                
          
-- **********************
-- ** Examples of CSPs **
-- **********************
          
-- Example 1: Map of Australia
          
colours = [1..3]

ausRegions :: [Var]
ausRegions = ["WA","NSW","NT","Q","V","SA"]

ausDomains :: Domains
ausDomains = map (\r -> (r,colours)) ausRegions

ausCsp :: CSP
ausCsp = CSP ("Map of Australia",
           ausDomains, [
             (varsDiffConstraint "WA" "NT"),
             (varsDiffConstraint "NT" "Q"),
             (varsDiffConstraint "SA" "WA"),
             (varsDiffConstraint "SA" "Q"),
             (varsDiffConstraint "SA" "NT"),
             (varsDiffConstraint "Q"  "NSW"),
             (varsDiffConstraint "SA" "NSW"),
             (varsDiffConstraint "SA" "V"),
             (varsDiffConstraint "V"  "NSW")
             ])


-- Example 2: Map of Scotland

mapRegions :: [Var]
mapRegions = ["ARGYLL","ARRAN","LOTHIAN","BORDERS","CENTRAL","D&G","FIFE","GRAMPIAN","HIGHLAND","ISLAY","MULL","ORKNEY","SKYE","STRATHCLYDE","TAYSIDE"]

mapDomains :: Domains
mapDomains = map (\ r -> (r,colours)) mapRegions

mapCsp = CSP ("Map of Scotland",
           mapDomains, [
             (varsDiffConstraint  "ORKNEY"      "HIGHLAND" ),
             (varsDiffConstraint  "SKYE"        "HIGHLAND" ),
             (varsDiffConstraint  "MULL"        "HIGHLAND" ),
             (varsDiffConstraint  "GRAMPIAN"    "HIGHLAND" ),
             (varsDiffConstraint  "TAYSIDE"     "HIGHLAND" ),
             (varsDiffConstraint  "ARGYLL"      "HIGHLAND" ),
             (varsDiffConstraint  "GRAMPIAN"    "TAYSIDE" ),
             (varsDiffConstraint  "MULL"        "ARGYLL" ),
             (varsDiffConstraint  "TAYSIDE"     "ARGYLL" ),
             (varsDiffConstraint  "CENTRAL"     "ARGYLL" ),
             (varsDiffConstraint  "ARRAN"       "ARGYLL" ),
             (varsDiffConstraint  "ISLAY"       "ARGYLL" ),
             (varsDiffConstraint  "STRATHCLYDE" "ARGYLL" ),
             (varsDiffConstraint  "MULL"        "ISLAY" ),
             (varsDiffConstraint  "FIFE"        "TAYSIDE" ),
             (varsDiffConstraint  "CENTRAL"     "TAYSIDE" ),
             (varsDiffConstraint  "ARRAN"       "STRATHCLYDE" ),
             (varsDiffConstraint  "FIFE"        "CENTRAL") ,
             (varsDiffConstraint  "FIFE"        "LOTHIAN" ),
             (varsDiffConstraint  "STRATHCLYDE" "CENTRAL" ),
             (varsDiffConstraint  "STRATHCLYDE" "LOTHIAN" ),
             (varsDiffConstraint  "STRATHCLYDE" "BORDERS" ),
             (varsDiffConstraint  "STRATHCLYDE" "D&G" ),
             (varsDiffConstraint  "BORDERS"     "D&G" ),
             (varsDiffConstraint  "BORDERS"     "LOTHIAN" )
             ])
          

-- Example 3: 3x3 Magic Square

ms3x3Domains :: Domains
ms3x3Domains = [("x1",[1..9]),("x2",[1..9]),("x3",[1..9]),("y1",[1..9]),("y2",[1..9]),("y3",[1..9]),("z1",[1..9]),("z2",[1..9]),("z3",[1..9])]

ms3x3Csp = CSP ("Magic Square 3x3",
                 ms3x3Domains,[
                   (allDiffConstraint (map fst ms3x3Domains)),
                   (sumConstraint ["x1", "x2", "x3"] 15), -- row 1
                   (sumConstraint ["y1", "y2", "y3"] 15), -- row 2
                   (sumConstraint ["z1", "z2", "z3"] 15), -- row 3
                   (sumConstraint ["x1", "y1", "z1"] 15), -- column 1
                   (sumConstraint ["x2", "y2", "z2"] 15), -- column 2
                   (sumConstraint ["x3", "y3", "z3"] 15), -- column 3
                   (sumConstraint ["x1", "y2", "z3"] 15), -- diagonal 1
                   (sumConstraint ["x3", "y2", "z1"] 15)  -- diagonal 2
                   ])

sudokuVars :: [Var]
sudokuVars = foldl union [] $ map (\x -> map (\y -> (++) x $ show y) [1..9]) ["a","b","c","d","e","f","g","h","i"]

sudokuDomains :: Domains
sudokuDomains = map (\r -> (r,[1..9])) sudokuVars

sudokuCsp :: CSP
sudokuCsp = CSP ("Sudoku!",
           sudokuDomains, [
             (allDiffConstraint $ map (\y -> (++) "a" $ show y) [1..9]),
             (allDiffConstraint $ map (\y -> (++) "b" $ show y) [1..9]),
             (allDiffConstraint $ map (\y -> (++) "c" $ show y) [1..9]),
             (allDiffConstraint $ map (\y -> (++) "d" $ show y) [1..9]),
             (allDiffConstraint $ map (\y -> (++) "e" $ show y) [1..9]),
             (allDiffConstraint $ map (\y -> (++) "f" $ show y) [1..9]),
             (allDiffConstraint $ map (\y -> (++) "g" $ show y) [1..9]),
             (allDiffConstraint $ map (\y -> (++) "h" $ show y) [1..9]),
             (allDiffConstraint $ map (\y -> (++) "i" $ show y) [1..9]),
             
             (allDiffConstraint ["a1","b1","c1","d1","e1","f1","g1","h1","i1"]),
             (allDiffConstraint ["a2","b2","c2","d2","e2","f2","g2","h2","i2"]),
             (allDiffConstraint ["a3","b3","c3","d3","e3","f3","g3","h3","i3"]),
             (allDiffConstraint ["a4","b4","c4","d4","e4","f4","g4","h4","i4"]),
             (allDiffConstraint ["a5","b5","c5","d5","e5","f5","g5","h5","i5"]),
             (allDiffConstraint ["a6","b6","c6","d6","e6","f6","g6","h6","i6"]),
             (allDiffConstraint ["a7","b7","c7","d7","e7","f7","g7","h7","i7"]),
             (allDiffConstraint ["a8","b8","c8","d8","e8","f8","g8","h8","i8"]),
             (allDiffConstraint ["a9","b9","c9","d9","e9","f9","g9","h9","i9"]),
             
             (allDiffConstraint ["a1","a2","a3","b1","b2","b3","c1","c2","c3"]),
             (allDiffConstraint ["a4","a5","a6","b4","b5","b6","c4","c5","c6"]),
             (allDiffConstraint ["a7","a8","a9","b7","b8","b9","c7","c8","c9"]),
             (allDiffConstraint ["d1","d2","d3","e1","e2","e3","f1","f2","f3"]),
             (allDiffConstraint ["d4","d5","d6","e4","e5","e6","f4","f5","f6"]),
             (allDiffConstraint ["d7","d8","d9","e7","e8","e9","f7","f8","f9"]),
             (allDiffConstraint ["g1","g2","g3","h1","h2","h3","i1","i2","i3"]),
             (allDiffConstraint ["g4","g5","g6","h4","h5","h6","i4","i5","i6"]),
             (allDiffConstraint ["g7","g8","g9","h7","h8","h9","i7","i8","i9"])
             ])

sudoku vals = foldl (\c (x,y) -> setDomain (x,[y]) c) sudokuCsp vals

sudoku1 = sudoku [("a3",3),("a5",2),("a7",6),
                  ("b1",9),("b4",3),("b6",5),("b9",1),
                  ("c3",1),("c4",8),("c6",6),("c7",4),
                  ("d3",8),("d4",1),("d6",2),("d7",9),
                  ("e1",7),("e9",8),
                  ("f3",6),("f4",7),("f6",8),("f7",2),
                  ("g3",2),("g4",6),("g6",9),("g7",5),
                  ("h1",8),("h4",2),("h6",3),("h9",9),
                  ("i3",5),("i5",1),("i7",3)
                  ]

sudokuCompetition = sudoku [("a1",3),("a3",6),("a4",8),
                             ("b1",1),("b3",9),("b6",5),
                             ("c5",7),("c8",2),
                             ("d1",4),("d4",7),("d9",1),
                             ("e1",9),("e9",7),
                             ("f1",6),("f6",8),("f9",5),
                             ("g2",4),("g5",8),
                             ("h4",2),("h7",1),("h9",6),
                             ("i6",1),("i7",8),("i9",3)
                             ]

showSudokuNode csp assignment pos
                 | length (getDomain pos csp) == 1 = show $ head $ getDomain pos csp
                 | isNothing val = " "
                 | otherwise = show $ fromJust val
                 where val = lookupVar assignment pos

sudokuTable csp assignment = toTable $ cspVars csp   
             where toTable l
                    | l == [] = []
                    | otherwise =  (map (showSudokuNode csp assignment) $ take 9 l) : (toTable $ drop 9 l)

showSudoku csp assignment = sep ++ (foldl1 foldtable $ map showRow $ sudokuTable csp assignment) ++ sep
            where showRow rw = "| " ++ (foldl1 foldrow rw) ++ " |\n"
                  foldrow x y = x ++ " | " ++ y
                  foldtable x y = x ++ sep ++ y
                  sep = "+" ++ (concat $ replicate 9 "---+") ++ "\n" 

printSudoku :: CSP -> IO()
printSudoku csp = putStr $ showSudoku csp []

trySudoku :: CSP -> (CSP -> (Maybe Assignment,Int)) -> IO()
trySudoku csp f
           | isNothing result = putStr $ "Nothing!\n Visited nodes: " ++ (show nodes) ++ "\n"
           | otherwise = putStr $ (showSudoku csp (fromJust result)) ++ "Visited nodes: " ++ (show nodes) ++ "\n"
           where (result,nodes) = f csp
