module Zvalue where

import Data.List

type Nonterm = String
type Terminal = String

data Rule = LeafRule Nonterm Terminal | NonLeafRule Nonterm Nonterm Nonterm | NonLeafRule2 Nonterm Nonterm Nonterm Nonterm deriving (Eq,Show)
data Expression = Variable Int | Constant Float | Add Expression Expression | OneMinus Expression | Mult Expression Expression | Divide Expression Expression deriving (Eq, Show)

--------------------------------

rule1 = [NonLeafRule "S 0 1" "S 0 1" "S 1 1",
         LeafRule "S 0 1" "a",
         NonLeafRule "S 1 1" "S 1 1" "S 1 1",
         LeafRule "S 1 1" "a"]

rule2 = [NonLeafRule2 "S 0 2" "S 0 1" "A 1 2" "S 2 2",
         LeafRule "S 0 1" "b",
         LeafRule "A 1 2" "a",
         NonLeafRule2 "S 2 2" "S 2 2" "A 2 2" "S 2 2",
         LeafRule "S 2 2" "a",
         LeafRule "S 2 2" "b",
         LeafRule "A 2 2" "a" ]

rule3 = [NonLeafRule2 "S 0 2" "NP 0 1" "V 1 2" "S 2 2",
         NonLeafRule2 "S 2 2" "NP 2 2" "V 2 2" "S 2 2",
         NonLeafRule "S 2 2" "NP 2 2" "VP 2 2",
         LeafRule "NP 2 2" "John",
         LeafRule "NP 2 2" "Mary",
         LeafRule "V 2 2" "believed",
         LeafRule "V 2 2" "knew",
         LeafRule "VP 2 2" "ran",
         LeafRule "NP 0 1" "Mary",
         LeafRule "V 1 2" "believed"]

rule4 = [NonLeafRule2 "S 0 2" "NP 0 1" "V 1 2" "S 2 2",
         NonLeafRule "S 0 2" "NP 0 1" "V 1 2",
         NonLeafRule2 "S 2 2" "NP 2 2" "V 2 2" "S 2 2",
         NonLeafRule "S 2 2" "NP 2 2" "VP 2 2",
         LeafRule "NP 2 2" "John",
         LeafRule "NP 2 2" "Mary",
         LeafRule "V 2 2" "believed",
         LeafRule "V 2 2" "knew",
         LeafRule "VP 2 2" "ran",
         LeafRule "NP 0 1" "Mary",
         LeafRule "V 1 2" "believed"]


--------------------------------
-- assigning probabilities to rules

f :: [Rule] -> [(Rule, Expression)]
f rl = fhelper [] rl 0 rl

-- keep track of the nonterms of assigned rules and their expressions
-- save the record of all the rules
-- keep track of last variable used
-- and update the list of rules that need assignment
fhelper :: [(Nonterm, Expression)] -> [Rule] -> Int -> [Rule] -> [(Rule, Expression)]
fhelper nt rules lastExp rl = case rl of
                [] -> []
                (x:xs) -> case x of 
                          LeafRule nonterm term ->
                              if ((numberInNT nt nonterm) + 1) < (numberInRule rules nonterm) then
                                  -- eg. there are 3 rule of S -> ..., but we only assigned less than 2 of them
                                  [(x, Variable (lastExp + 1))] ++ (fhelper (nt ++ [(nonterm, Variable (lastExp + 1))]) rules (lastExp + 1) xs)
                              else
                                  [(x, simplify (OneMinus (findd nt nonterm)))] ++ (fhelper (nt ++ [(nonterm, simplify (OneMinus (findd nt nonterm)))]) rules (lastExp) xs)
                          NonLeafRule nt1 nt2 nt3 ->
                              if ((numberInNT nt nt1) + 1) < (numberInRule rules nt1) then
                                  -- this is the last rule with Nonterm nt1 in the list
                                  [(x, Variable (lastExp + 1))] ++ (fhelper (nt ++ [(nt1, Variable (lastExp + 1))]) rules (lastExp + 1) xs)
                              else
                                  [(x, simplify (OneMinus (findd nt nt1)))] ++ (fhelper (nt ++ [(nt1, simplify (OneMinus (findd nt nt1)))]) rules (lastExp) xs)
                          NonLeafRule2 nt1 nt2 nt3 nt4 ->
                              if ((numberInNT nt nt1) + 1) < (numberInRule rules nt1) then
                                  -- this is the last rule with Nonterm nt1 in the list
                                  [(x, Variable (lastExp + 1))] ++ (fhelper (nt ++ [(nt1, Variable (lastExp + 1))]) rules (lastExp + 1) xs)
                              else
                                  [(x, simplify (OneMinus (findd nt nt1)))] ++ (fhelper (nt ++ [(nt1, simplify (OneMinus (findd nt nt1)))]) rules (lastExp) xs)


findd :: [(Nonterm, Expression)] -> Nonterm -> Expression
findd nts nt = case nts of
              [] -> Constant 0
              ((nonterm, exp):xs) ->
                  if nonterm == nt then
                      simplify (Add exp (findd xs nt))
                  else
                      findd xs nt

numberInNT :: [(Nonterm, Expression)] -> Nonterm -> Int
numberInNT nts nt = case nts of
                    [] -> 0
                    ((nonterm, exp):xs) -> 
                        if nonterm == nt then
                            1 + (numberInNT xs nt)
                        else
                            numberInNT xs nt

numberInRule :: [Rule] -> Nonterm -> Int
numberInRule rl nt = case rl of
                      [] -> 0
                      (x:xs) -> case x of
                                LeafRule nonterm term ->
                                    if nonterm == nt then
                                        1 + (numberInRule xs nt)
                                    else
                                        numberInRule xs nt
                                NonLeafRule nt1 nt2 nt3 -> 
                                    if nt1 == nt then
                                        1 + (numberInRule xs nt)
                                    else
                                        numberInRule xs nt
                                NonLeafRule2 nt1 nt2 nt3 nt4 ->
                                    if nt1 == nt then
                                        1 + (numberInRule xs nt)
                                    else
                                        numberInRule xs nt


--------------------------------
-- FOR EASY CASES when
-- epison and S_m_n -> ... S_m_n ... does not both occur in this grammar

lgnum :: [(Rule, Expression)] -> String -> String
lgnum set n = case set of
            [] -> n
            ((rl, exp):xs) -> case rl of
                              LeafRule nonterm term -> 
                                  if ((words nonterm) !! 2) > n then
                                      lgnum xs ((words nonterm) !! 2)
                                  else
                                      lgnum xs n
                              NonLeafRule nt1 nt2 nt3 ->
                                  if ((words nt1) !! 2) > n then
                                      lgnum xs ((words nt1) !! 2)
                                  else
                                      lgnum xs n
                              NonLeafRule2 nt1 nt2 nt3 nt4 ->
                                  if ((words nt1) !! 2) > n then
                                      lgnum xs ((words nt1) !! 2)
                                  else
                                      lgnum xs n

z :: [(Rule, Expression)] -> Nonterm -> Expression
z set nt = zz set set nt

-- helper function of z that keeps the original set but also find the
-- nonterm in the further updated set
zz :: [(Rule, Expression)] -> [(Rule, Expression)] -> Nonterm -> Expression
zz orgset set nt = case set of 
                   [] -> Constant 0
                   ((rl, exp):xs) -> case rl of
                                     LeafRule nonterm term -> 
                                         if nonterm == nt then
                                             if ((words nonterm) !! 1) == (lgnum orgset "0") then
                                                 Constant 1
                                             else
                                                 simplify (Add exp (zz set xs nt))
                                         else
                                             zz set xs nt 
                                     NonLeafRule nt1 nt2 nt3 ->
                                         if nt1 == nt then
                                             if ((words nt1) !! 1) == (lgnum orgset "0") then
                                             -- check if it's X_n_n, which 
                                                 Constant 1
                                             else if (nt2 == nt1) || (nt3 == nt1) then
                                                 if nt2 == nt1 then
                                                     simplify (Divide (zz set xs nt) (OneMinus (simplify (Mult exp (z set nt3)))))
                                                 else
                                                     simplify (Divide (zz set xs nt) (OneMinus (simplify (Mult exp (z set nt2)))))
                                             else
                                                 simplify (Add (simplify (Mult exp (simplify (Mult (z set nt2) (z set nt3))))) (zz set xs nt))
                                         else
                                             zz set xs nt
                                     NonLeafRule2 nt1 nt2 nt3 nt4 ->
                                         if nt1 == nt then
                                             if ((words nt1) !! 1) == (lgnum orgset "0") then
                                                 Constant 1
                                             else if (nt2 == nt1) || (nt3 == nt1) || (nt4 == nt1) then
                                                 if nt2 == nt1 then
                                                     simplify (Divide (zz set xs nt) (OneMinus (simplify (Mult exp (Mult (z set nt3) (z set nt4))))))
                                                 else if nt3 == nt1 then
                                                     simplify (Divide (zz set xs nt) (OneMinus (simplify (Mult exp (Mult (z set nt2) (z set nt4))))))
                                                 else
                                                     simplify (Divide (zz set xs nt) (OneMinus (simplify (Mult exp (Mult (z set nt2) (z set nt3))))))
                                             else
                                                 simplify (Add (simplify (Mult exp (simplify (Mult (z set nt2) (simplify (Mult (z set nt3) (z set nt4))))))) (zz set xs nt))
                                         else
                                             zz set xs nt

simplify :: Expression -> Expression
simplify exp = case factorize exp of 
               Add a b ->
                   if a == Constant 0.0 then
                       b
                   else if b == Constant 0.0 then
                       a
                   else if (b == OneMinus a) || (a == OneMinus b) then
                       Constant 1
                   else
                       factorize exp
               Mult a b -> 
                   if a == Constant 1.0 then
                       b
                   else if b == Constant 1.0 then
                       a
                   else if (a == Constant 0.0) || (b == Constant 0.0) then
                       Constant 0
                   else
                       factorize exp
               Divide a b ->
                   if a == b then
                       Constant 1
                   else if b == Constant 1.0 then
                       a
                   else
                       factorize exp
               OneMinus a ->
                   if a == Constant 0.0 then
                       Constant 1
                   else if a == Constant 1.0 then
                       Constant 0
                   else factorize exp
               Variable i -> Variable i
               Constant f -> Constant f

-- No Mult or Divide factors
factors :: Expression -> [(Expression, Expression)]
factors (Variable i) = [(Variable i, Constant 1)]

factors (Constant f) = [(Constant f, Constant 1)]
-- the constant here can only be 1

factors (Add e1 e2) = [(x1, Add y1 y2) | (x1, y1) <- factors e1, (x2, y2) <- factors e2, x1 == x2] 
                      ++ [(Add e1 e2, Constant 1)]

factors (OneMinus e1) = [(OneMinus e1, Constant 1)]

factors (Mult e1 e2) = [(e1, e2)]
                       ++ [(x, Mult y e2) | (x,y) <- factors e1]
                       ++ [(y, Mult x e2) | (x,y) <- factors e1]
                       ++ [(x, Mult y e1) | (x,y) <- factors e2]
                       ++ [(y, Mult x e1) | (x,y) <- factors e2]

factors (Divide e1 e2) = [(x, Divide y e2) | (x,y) <- factors e1]
                         ++ [(Divide (Constant 1) x, Divide y e2) | (x,y) <- factors e2]


factorize :: Expression -> Expression
factorize (Variable i) = Variable i
factorize (Constant f) = Constant f
factorize (Add e1 e2) = case (intersectBy (\(x1, y1) (x2, y2) -> x1 == x2) (factors e1) (factors e2)) of
                        [] -> Add e1 e2
                        [(Constant 1.0, Constant 1.0)] -> Add e1 e2
                        ((x, y):xs) -> Mult x (factorize (Add (extract x (factors e1)) (extract x (factors e2))))

factorize (OneMinus e1) = OneMinus e1

factorize (Mult e1 e2) = Mult e1 e2

factorize (Divide e1 e2) = case (intersectBy (\(x1, y1) (x2, y2) -> x1 == x2) (factors e1) (factors e2)) of
                           [] -> Divide e1 e2
                           [(Constant 1.0, Constant 1.0)] -> Divide e1 e2
                           ((x, y):xs) -> factorize (Divide (extract x (factors e1)) (extract x (factors e2)))
                           -- remember to simplify again


extract :: Expression -> [(Expression, Expression)] -> Expression
extract e exp = case exp of
             [] -> Constant 0
             ((x, y):xs) -> if x == e then
                                y
                            else
                                extract e xs

-- check their maximum common factor
--check :: [(Expression, Expression)] -> [(Expression, Expression)] -> (Expression, Expression, Expression)
--check exp1 exp2 = case exp1 of