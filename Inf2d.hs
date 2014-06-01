-- Inf2d Assignment 1 2013-14 
-- Matriculation number: 

module Inf2d where

import Data.List
import Data.Maybe
import CSPframework
import Examples

{- NOTES:

-- DO NOT CHANGE THE NAMES OR TYPE DEFINITIONS OF THE FUNCTIONS!
You can write new auxillary functions, but don't change the names or type definitions 
of the functions which you are asked to implement.

-- Comment your code.

-- You should submit this file, and only this file, when you have finished the assignment.

-- The deadline is: 3rd of March 2014, 4pm.

-- See the reference manual for more information on the datatypes and functions of the framework.

-- See www.haskell.org for haskell revision.

-- Useful haskell topics, which you should revise:
-- Recursion
-- The Maybe monad
-- Higher-order functions
-- List processing functions: map, foldl, filter, sortBy etc.

-}

-------------------------------------------------
-- (3) Sudoku problem
-------------------------------------------------

-- (3.i) Variables & values

--naming the Queens from 1 to the input value, example : queenVars 2 = ["Q1", "Q2"], etc.

queenVars :: Int -> [Var]
queenVars x = queens2
              where queens = [1..x]
                    queens1 = map (show) queens
                    queens2 = map ( "Q" ++) queens1

--Since Each queen number corresponds to the row that they are in, each queen domain would 
--have a value that coreespond the column the are which strats from 1 to the board-size.
                    
queenDomains :: Int -> Domains
queenDomains x = [(v, [1..x]) | v <- (queenVars x)]

-- (3.ii) Constraints

--if the difference betwenn  the row position of two queens is the same as the difference between the cloumn position of 2 queens,
--it mean they are indeed on the same diagonal, (unless one or both of them are not assigned yet which return true because we wouldn't have any problem)

diagonalRelation :: Relation
diagonalRelation vars assignment
                 |(isAssigned assignment v1 && isAssigned assignment v2) = not (deltaX == deltaY)
                 | otherwise = True
                   where deltaX = abs(fromJust(lookupVar assignment v1) - fromJust(lookupVar assignment v2)) -- Diffreence in column
                         v1 = head vars
                         v2 = head (tail vars)
                         deltaY = abs(y1 - y2)            -- difference in row
                         y1 = read(tail(v1)) :: Int
                         y2 = read(tail(v2)) :: Int



-- Binary constraint stating that two variables differ by exactly n.

diagonalConstraint :: Var -> Var -> Constraint
diagonalConstraint a b = CT (a ++ " and " ++ b ++ " not in the same diagonal",[a,b],diagonalRelation)

-- (3.iii) N-Queens CSP

------A function that removes an item from a list

removeItem _ []                 = []
removeItem x (y:ys) | x == y    = removeItem x ys
                    | otherwise = y : removeItem x ys

-----"ApplyDiagonalConstraint" is a function that takes a variable and a list of variables and apply Constraint between that variable and all the varibale  -----in the list except the variable itself , because for example we dont want to apply the doiagonal Constraint betwwen Q1 and Q1!

applyDiagonalConstraint :: Var -> [Var] -> [Constraint]
applyDiagonalConstraint x queens = map (diagonalConstraint x) queens2            
                            where              
                               queens2 = removeItem x queens  --because we dont want to consider the DiagonalConstarint between a queen and itself!! (wouldn't make sensce)

-----"ApplyDiagonalConstraint2" is a function that takes 2 list of variable and apply the constraint between all variables from the two list(except if two  -----variable are identical.  

applyDiagonalConstraint2 :: [Var] -> [Var] -> [Constraint]     
applyDiagonalConstraint2 [] [] = []
applyDiagonalConstraint2 [] bs = []
applyDiagonalConstraint2 as [] = []
applyDiagonalConstraint2 (a:as) bs = (applyDiagonalConstraint a bs) ++ (applyDiagonalConstraint2 as (removeItem a bs))          

queenCsp :: Int -> CSP
queenCsp n = CSP ((show n) ++ "-Queens Problem",
             queenDomains n, [
		allDiffConstraint(queenVars n)        -----we dont want our queens to be in the same row.
               ] ++ diagonals)
             where
               diagonals = applyDiagonalConstraint2 (queenVars n) (queenVars n)  -------we dont want our queens to be in the same diagonal.

-------------------------------------------------
-- (4.1) Forward Checking
-------------------------------------------------

-- (4.1.i) Forward check for infernce:

--It checks if the values in domain of a vriable is consistent with a given assignment , it refreshes the domain and gives the new domain
               
domainHelper :: CSP -> Assignment -> Var -> Domain -> Domain
domainHelper csp assignment var [] = []
domainHelper csp assignment var (i:domain)  
       | isConsistentValue csp assignment (var, i) = (i : l) ++ domainHelper csp assignment var domain 
       | otherwise = l ++ domainHelper csp assignment var domain                                              
       where
         l = []
                                                                       
--For a variable, it delets the inconsistent values with respect to a given assignment(using domainHelper) and 
--set the new domain in the csp and return that csp.
          
domainHelper2 :: CSP -> Assignment -> Var -> CSP
domainHelper2 csp assignment var = setDomain (var, newDomain) csp
                          where
                            newDomain = domainHelper csp assignment var domain
                            domain = getDomain var csp

--it updates the domain of a lsit of variables with respect to an assignment and then returns the new csp.                          
                                                           
cspFinder :: CSP -> Assignment -> [Var] -> CSP
cspFinder csp a [] = csp
cspFinder csp a (n:ns) = domainHelper2 (cspFinder csp a ns) a n

-- this checks that none of the variables in a csp has empty domain.

boolCheck :: CSP -> [Var] -> Bool
boolCheck csp [] = True
boolCheck csp  (v:var)
        | (getDomain v csp == []) = False
        | otherwise = True && (boolCheck csp var)
          

forwardcheck :: CSP -> Assignment -> Var -> (CSP, Bool)
forwardcheck csp assignment var = (newCsp, bool)
           where
             neighbourVars = [ n | n <- allNeighboursOf var csp, isAssigned assignment n == False]
             newCsp = cspFinder csp assignment neighbourVars
             bool = boolCheck newCsp neighbourVars
               

-- (4.1.ii) Algorithm: 

f :: (CSP, Bool) -> CSP       -----same as fst but made my coding faster and it is a bit more clear for me than fst.
f (a, b) = a

g :: (CSP, Bool) -> Bool
g (a, b) = b

fcRecursion :: CSP -> Assignment -> (Maybe Assignment, Int)
fcRecursion csp assignment =
  if (isComplete csp assignment) then (Just assignment,0)
    else findConsistentValue $ getDomain var csp
      where var = firstUnassignedVar assignment csp
            findConsistentValue vals = 
              case vals of  -- recursion over the possible values 
                            -- instead of for-each loop
                []     -> (Nothing,0)
                val:vs -> 
                  if (isConsistentValue csp assignment (var,val) && snd (forwardcheck csp (assign (var, val) assignment) var)) ---because we do not wish to waste our time searching in nodes which will result in one of the domains being empty. 
                  then if (isNothing result) 
                       then (ret,nodes+nodes'+1)
                       else (result,nodes+1)
                  else (ret,nodes'+1)
                     where (result,nodes) = fcRecursion newCsp $ assign (var,val) assignment
                           (ret,nodes') = findConsistentValue vs
                           newCsp = f (forwardcheck csp (assign (var, val) assignment) var)      ---- instead of recusion on the original csp, we apply forward checking on the csp first and then recurse on the new csp.



fc :: CSP -> (Maybe Assignment,Int)
fc csp = fcRecursion csp []


-------------------------------------------------
-- (4.2) Minimum Remaining Values (MRV)
-------------------------------------------------

-- (4.2.i) Sorting function for variables based on the MRV heuristic:

mrvCompare :: CSP -> Var -> Var -> Ordering
mrvCompare csp v1 v2 = compare a b
                        where
                          a = length $ getDomain v1 csp
                          b = length $ getDomain v2 csp


-- (4.2.ii) Get next variable according to MRV for the FC algorithm:

unassignedVarNumbers :: Assignment -> [Var] -> [Var]
unassignedVarNumbers a [] = []
unassignedVarNumbers assignment (v:vs)  
                     | isAssigned assignment v = list ++ unassignedVarNumbers assignment vs 
                     | otherwise = v:list ++ unassignedVarNumbers assignment vs                             
                     where              
                       list = []               

getMRVVariable :: Assignment -> CSP -> Var 
getMRVVariable assignment csp = head list
                  where
                   vars = unassignedVarNumbers assignment (cspVars csp)
                   list = sortBy (mrvCompare csp) vars
                                                       

-- (4.2.iii) FC + MRV algorithm

fcMRVRecursion :: CSP -> Assignment -> (Maybe Assignment, Int)
fcMRVRecursion csp assignment =
  if (isComplete csp assignment) then (Just assignment,0)
    else findConsistentValue $ getDomain var csp
      where var = getMRVVariable assignment csp    -- instead of chosing the first unassigned variable, we chose the most restricted variable.
            findConsistentValue vals = 
              case vals of  -- recursion over the possible values 
                            -- instead of for-each loop
                []     -> (Nothing,0)
                val:vs -> 
                  if (isConsistentValue csp assignment (var,val) && g (forwardcheck csp (assign (var, val) assignment) var)) 
                  then if (isNothing result) 
                       then (ret,nodes+nodes'+1)
                       else (result,nodes+1)
                  else (ret,nodes'+1)
                     where (result,nodes) = fcMRVRecursion newCsp $ assign (var,val) assignment
                           (ret,nodes') = findConsistentValue vs
                           newCsp = f (forwardcheck csp (assign (var, val) assignment) var)




fcMRV :: CSP -> (Maybe Assignment,Int)
fcMRV csp = fcMRVRecursion csp []


-------------------------------------------------
-- (4.3) Least Constraining Value (LCV)
-------------------------------------------------

-- (4.3.i) Function that returns the number of choices available for all neighbours
--         of a variable:
 
numChoices :: CSP -> Assignment -> Var -> Int
numChoices csp assignment var = sum list2
                                where
                                  neighbours = removeDuplicates $ allNeighboursOf var csp
                                  list = [domainHelper csp assignment x (getDomain x csp)| x <- neighbours]
                                  list2 = [length x | x <- list]


-- (4.3.ii) Function that sorts the domain of a variable based on the LCV heuristic.

-- a function that removes the duplicaated items in a list

removeDuplicates :: Eq a => [a] -> [a]
removeDuplicates = rdHelper []
    where rdHelper seen [] = seen
          rdHelper seen (x:xs)
              | x `elem` seen = rdHelper seen xs
              | otherwise = rdHelper (seen ++ [x]) xs

-- a function that shows an ordering between the numchoices of two values for a variable in a csp with respect to some asignment              
 
lcvSorting :: CSP -> Var -> Assignment -> Int -> Int -> Ordering
lcvSorting csp var assignment x1 x2 = compare a b
            where
                assignment1 = [AV(var, x1)] ++ assignment
                assignment2 = [AV(var, x2)] ++ assignment
                a = numChoices csp assignment1 var
                b = numChoices csp assignment2 var


lcvSort :: CSP -> Assignment -> Var -> [Int]
lcvSort csp assignment var = reverse list2               ----since we want the value with the most numchoices in the head of the list, we reverse the list
        where 
            list1 = [ x | x <- domainHelper csp assignment var (getDomain var csp)]  ----get the (updated w.r.t assignment) domain in list1
            list2 = sortBy (lcvSorting csp var assignment) list1    --- sort it using lcvSorting function
          


-- (4.3.iii) FC + LCV algorithm

fcLCVRecursion :: CSP -> Assignment -> (Maybe Assignment, Int)
fcLCVRecursion csp assignment =
   if (isComplete csp assignment) then (Just assignment,0)
    else findConsistentValue $ lcvSort csp assignment var --- instead of do findConsisenValue on the domain, we do it on the sorted domain
      where var = firstUnassignedVar assignment csp
            findConsistentValue vals = 
              case vals of  -- recursion over the possible values 
                            -- instead of for-each loop
                []     -> (Nothing,0)
                val:vs -> 
                  if (isConsistentValue csp assignment (var,val) && g (forwardcheck csp (assign (var, val) assignment) var)) 
                  then if (isNothing result) 
                       then (ret,nodes+nodes'+1)
                       else (result,nodes+1)
                  else (ret,nodes'+1)
                     where (result,nodes) = fcLCVRecursion newCsp $ assign (var,val) assignment
                           (ret,nodes') = findConsistentValue vs
                           newCsp = f (forwardcheck csp (assign (var, val) assignment) var)
                           


fcLCV :: CSP -> (Maybe Assignment,Int)
fcLCV csp = fcLCVRecursion csp []

-- (4.3.iv) FC + MRV + LCV algorithm

fcMRV_LCVRecursion :: CSP -> Assignment -> (Maybe Assignment, Int)
fcMRV_LCVRecursion csp assignment =
  if (isComplete csp assignment) then (Just assignment,0)
    else findConsistentValue $ lcvSort csp assignment var
      where var = getMRVVariable assignment csp
            findConsistentValue vals = 
              case vals of  -- recursion over the possible values 
                            -- instead of for-each loop
                []     -> (Nothing,0)
                val:vs -> 
                  if (isConsistentValue csp assignment (var,val) && g (forwardcheck csp (assign (var, val) assignment) var)) 
                  then if (isNothing result) 
                       then (ret,nodes+nodes'+1)
                       else (result,nodes+1)
                  else (ret,nodes'+1)
                     where (result,nodes) = fcMRVRecursion newCsp $ assign (var,val) assignment
                           (ret,nodes') = findConsistentValue vs
                           newCsp = f (forwardcheck csp (assign (var, val) assignment) var)



fcMRV_LCV :: CSP -> (Maybe Assignment,Int)
fcMRV_LCV csp = fcMRV_LCVRecursion csp []



-------just testing

--c = queenCsp 8
--v = "Q1"       
--v2 = "Q2"
--vs = cspVars c
--a = [AV(v, 2), AV(v2, 4)]
--d = getDomain v c
--c2 = f (forwardcheck c a v)
--a2 = [AV(v, 1)]

-------

-------------------------------------------------
-- (5) Evaluation
-------------------------------------------------
{-
  (5.ii) Table:

----------+--------+--------+--------+---------+----------+---------+-----------+
          |   BT   |   FC   | FC+MRV | FC+LCV  |FC+MRV+LCV|   AC3   |AC3+MRV+LCV|
----------+--------+--------+--------+---------+----------+---------+-----------+
ausCsp    |   37   |   11   |   6    |   11    |    6     |    9    |     6     |
mapCsp    |   1176 |   23   |   15   |   23    |    15    |    15   |     15    |
ms3x3Csp  |   3654 |   195  |   110  |   188   |    61    |xxxxxxxxx|xxxxxxxxxxx|
8-Queens  |   876  |   88   |   75   |   76    |    35    |    20   |     18    |
12-Queens |   3066 |   193  |   153  |   417   |    119   |    41   |     49    |
----------+--------+--------+--------+---------+----------+---------+-----------+

  (5.iii - 5.iv) Report:

- Your report must be no longer than one A4 page for the first four algorithms
  and another maximum half page for AC3 and AC3+MRV+LCV.
- Write your report starting here. -
-------------------------------------------------
**Comapring BT and FC:
**All the values for FC are less(better) than BT which is expected, because in Fc we kepp reducing the domain of
 remaining variables, each time we loop, so there will be less values to check compare to BT. the more searching 
 needs to be done,the better our FC helps to minimize the number of nodes. but when there is small numbers of 
 nodes(totally) like in the first exaomle, there is not much difference in the number of nodes. 

**Comapring FC and FC_MRV:
**All the values for FC_MRV are better than FC, which makes sence because by picking the value with the 
 minimum-remaining-value, there is a good chance that we reach a solution faster and not having to backtrack
 any more (comapre to FC).

**Comapring FC and FC_LCV:
**If we compare FC_LCV and FC, we see that the number of nodes are sometimes better for FC and sometimes better for
 FC_LCV and sometimes equal. my expectation was that FC_LCV should reduce the number of nodes in the search tree 
 most of the times. But in these examples, chosing the least-constranting-value only helped in the magic square 
 (third exapmle) and the 8-queen-problem(queenCsp 8). Also in the last expamle (queenCsp 12) we get a number of nodes
 which is extremly highr than doing Forward-Checking only! I assume the explaination for this is that by chosing the
 least-constraning-value of the domains, we search the most-likely values first before others, but most-likely values
 of the domain are not always the solution! In some cases, the solution may involve the values that allows few
 choices for the domain of other variables. So 12-queen-problem might be on these cases. 

**Comparing FC_MRV and FC_LCV:
**All the values for FC_MRV are better than FC_LCV, sometimes it works much better than LCV like 12-queen-problem,
 and sometimes it works with almost the same effect as LCV like 8-queen-problem. These results shows us that chosing
 the variable with is basically a better method than the least-constraining-value method (even though they are 
 completely different methods). But it might be the case that MRV forks better for these 5 exaples than LCV, but 
 this might not be always true.

**Comparing FC_MRV and FC_MRV_LCV:
**In the last three examples, the FC_MRV_LCV reduced the number of nodes by a reasonable amount. But for the ausCsp 
 and mapCsp, the number of nodes are exatctly the same(even though we get different solutions). This might be because
 of the fact that 6 and 15 are the most opimal solution so that adding the LCV method to FC_MRV couldn't decrease 
 the number of nodes. we can conculde that FC_MRV_LCV works better than FC_MRV. But some csps might exists that
 chosing the least-constaining-value might increase the number of nodes (as observed in comparing FC_LCV and FC).

**Comparing FC and AC3 and:
**All the the number of nodes for AC3 are better(less) than FC. So applying Arc consistency helps to minimize the 
 number of nodes, better than Forward checking, which is expected since the arc consitency reduces more values from
 the domain of variables than forward checking. This is also true  for AC3+MRV+LCV.

**Comparing FC_MRV_LCV and AC3:
**In the first exapmle(ausCsp), FC_MRV_LCV beats AC3 by 3 nodes (which is rather samll). In the second case(mapCsp),
 they are equaly good because they both get most optimal number of nodes(15). In the queens problem, AC3 is doing 
 quite better than FC_MRV_LCV, especially in the 12-queen-problem. I find this a bit surprising because in 
 FC_MRV_LCV, not only FC is removing inconsistent value, but we are searching the most likely nodes first, while in
 arc consistency, we are only removing incorrect values from the domain. 

 **AC_MRV_LCV is giving optimal results for the first two cases, and the best result for the 8-queen-problem compare
  to others. but the surprising fact is that in 12-queen-problem, it is slightly weaker than AC3! This supports my 
  conclusion eralier, that in 12-queen-problem, the solution is NOT made up of values that has the least-constaring 
  power.    

-------------------------------------------------
- End of report-
-}


-------------------------------------------------
-- (6) Arc Consistency
-------------------------------------------------


-- (6.i) Checks if there exists at least one value in a list of values that if 
-- assigned to the given variable the assignment will be consistent.

existsConsistentValue :: CSP -> Var -> Int -> Var -> [Int] -> Bool
existsConsistentValue csp var1 x var2 [] = False
existsConsistentValue csp var1 x var2 (y:ys) 
                      | isConsistentValue csp assignment (var2, y) = True
                      | otherwise = False || existsConsistentValue csp var1 x var2 ys
                      where
                          assignment = [AV(var1, x)]


-- (6.ii) AC-3 constraint propagation

----it refreshes the domain of a variable with respect to an arc.

reviseDomain :: CSP -> Var -> Domain -> Var -> Domain -> Domain
reviseDomain csp var1 [] var2 ys = []
reviseDomain csp var1 (x:xs) var2 ys
       | existsConsistentValue csp var1 x var2 ys = (x : l) ++ reviseDomain csp var1 xs var2 ys 
       | otherwise = l ++ reviseDomain csp var1 xs var2 ys                                            
       where
         l = []
                                                                       
----it takes two variables and uses the "reviseDomain" function to update the domain of the first variable with respect to its arc to the second variable.
          
getRevisedCsp :: CSP -> Var -> Var -> CSP
getRevisedCsp csp var1 var2 = setDomain (var1, d) csp
                          where
                            d = reviseDomain csp var1 domain1 var2 domain2 
                            domain1 = getDomain var1 csp
                            domain2 = getDomain var2 csp
                           
                                                          
revise :: CSP -> Var -> Var -> (CSP,Bool)
revise csp var1 var2 = (newCsp, bool)
                      where
                        newCsp = getRevisedCsp csp var1 var2
                        bool = (getDomain var1 csp) /= (getDomain var1 newCsp)
                     
-- (6.iii) AC-3 constraint propagation

----ac3CheckCsp obtains the updated (arcConsisted) csp , but doesn't concern about if it is true or false.

ac3CheckCsp :: CSP -> [(Var, Var)] -> CSP
ac3CheckCsp csp [] = csp
ac3CheckCsp csp ((var1, var2):vs) 
            | g (revise csp var1 var2) = ac3CheckCsp newCsp newVs
            | otherwise =  ac3CheckCsp newCsp vs
            where
              newVs = vs ++ [ (v, var1) | v <- (removeDuplicates $ allNeighboursOf var1 csp), v /= var2]
              newCsp = f $ revise csp var1 var2   


ac3Check :: CSP -> [(Var,Var)] -> (CSP,Bool)
ac3Check csp vars = (newCsp, bool)
                                where
                                    newCsp = ac3CheckCsp csp vars
                                    bool = boolCheck newCsp (cspVars newCsp)


-- (6.iv) AC-3 algorithm

-------for a given csp, variable and an assignment, we want to find all arcs for that variable. this is the job of getVars. getVars takes a csp, assignment and a variable and returns all the arcs of that variable unless they are assined already.

getVars :: CSP -> Assignment -> Var -> [(Var, Var)]
getVars csp assignment var = [(var, v) | v <- removeDuplicates $ allNeighboursOf var csp, isAssigned assignment v == False ]

-----getArcs is similar to getVars but it does getVars for a list of variables. so basically applying getArcs to a csp, its variables with an empty assinment will return ALL the arcs exists in the csp. 

getArcs :: CSP -> Assignment -> [Var] -> [(Var, Var)]
getArcs csp assignment [] = []
getArcs csp assignment (v:vs) = getVars csp assignment v ++ getArcs csp assignment vs

ac3Recursion :: CSP -> Assignment -> (Maybe Assignment, Int)
ac3Recursion csp assignment =
    if (isComplete csp assignment) then (Just assignment,0)
    else findConsistentValue $ getDomain var csp
      where var = firstUnassignedVar assignment csp
            findConsistentValue vals = 
              case vals of  -- recursion over the possible values 
                            -- instead of for-each loop
                []     -> (Nothing,0)
                val:vs -> 
                  if (isConsistentValue csp assignment (var,val)) 
                  then if (isNothing result) 
                       then (ret,nodes+nodes'+1)
                       else (result,nodes+1)
                  else (ret,nodes'+1)
                     where (result,nodes) = ac3Recursion (f $ ac3Check (setDomain(var,[val]) csp) (getArcs csp assignment (cspVars csp))) $ assign (var,val) assignment
                           (ret,nodes') = findConsistentValue vs
                           
                           

ac3 :: CSP -> (Maybe Assignment,Int)
ac3 csp = ac3Recursion csp []


-- (6.v) AC-3 algorithm + MRV heuristic + LCV heuristic

ac3MRV_LCVRecursion :: CSP -> Assignment -> (Maybe Assignment, Int)
ac3MRV_LCVRecursion csp assignment =
    if (isComplete csp assignment) then (Just assignment,0)
    else findConsistentValue $ lcvSort csp assignment var
      where var = firstUnassignedVar assignment csp
            findConsistentValue vals = 
              case vals of  -- recursion over the possible values 
                            -- instead of for-each loop
                []     -> (Nothing,0)
                val:vs -> 
                  if (isConsistentValue csp assignment (var,val)  && g (forwardcheck csp (assign (var, val) assignment) var)) 
                  then if (isNothing result) 
                       then (ret,nodes+nodes'+1)
                       else (result,nodes+1)
                  else (ret,nodes'+1)
                     where (result,nodes) = ac3Recursion (f $ ac3Check (setDomain(var,[val]) newCsp) (getArcs newCsp assignment (cspVars newCsp))) $ assign (var,val) assignment
                           (ret,nodes') = findConsistentValue vs
                           newCsp = f (forwardcheck csp (assign (var, val) assignment) var)


ac3MRV_LCV :: CSP -> (Maybe Assignment,Int)
ac3MRV_LCV csp = ac3MRV_LCVRecursion csp []

----just Testing

--babak = queenCsp 3
--babakA = [AV("Q1", 1), AV("Q2", 3)]
--bd1 = getDomain "Q1" babak
--bd2 = getDomain "Q2" babak 
--babakVars = (getVars babak [] "Q1") ++ (getVars babak [] "Q2") ++ (getVars babak [] "Q3")
--bvs = (cspVars babak)

------
------just Testing

--test1 csp = ac3Check csp $ [ func constraint | constraint <- cspConstraints csp] ++ [ func1 constraint | constraint <- cspConstraints csp] 
--func constraint = ( head $ scope constraint, head $ tail $ scope constraint ) 
--func1 constraint = ( head $ tail $ scope constraint, head $ scope constraint ) 
--ausCsp1 = delDomainVal ("SA",1) $ delDomainVal ("NSW",1) $ delDomainVal ("NSW",3) $ ausCsp

------
---justTesting
                       
---atest = [AV("Q1", 8), AV("Q2", 4), AV("Q3", 1), AV("Q4", 3), AV("Q5", 6), AV("Q6", 2), AV("Q7", 7), AV("Q8", 5)]                       
                       
-----   
-------------------------------------------------
