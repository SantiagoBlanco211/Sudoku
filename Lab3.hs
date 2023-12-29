module Lab3 where
------------------- Estudiante/s -------------------
-- Nombres y apellidos: Santiago Blanco
-- Números: 282654
----------------------------------------------------

import Prelude
import Data.List

----------------------------------------------------------------------------------
-- Formalización del lenguaje y otros elementos
----------------------------------------------------------------------------------
type Var = String
type I = [(Var, Bool)]
type Razonamiento = ([L], L)
type Nat = Int

data L = V Var 
       | Neg L 
       | And L L 
       | Or  L L 
       | Imp L L
       | Iff L L
       deriving (Eq)
   
data Clase = Tau | Contra | Cont | Sat | Fal   
   
top = Or (V "ñ") (Neg(V "ñ"))
bot = And (V "ñ") (Neg(V "ñ"))

-- 1)
-- Pre: recibe una lista de asignaciones de valores de verdad sobre variables
-- Pos: retorna True si y solo si la lista no tiene pares complementarios
esConsistente :: [(Var, Bool)] -> Bool
esConsistente [] = True
esConsistente ((i,d):xs) = not (elem (i,not d) xs) && esConsistente xs

-- 2)
-- Pre: recibe una interpretación dada como lista de asignaciones (no vacía, consistente) 
-- Pos: retorna la interpretación expresada como una conjunción de literales
--Hecha en clase con Tomas
int2f :: I -> L
int2f ((i,d):xs)
 |xs == [] = lit
 |otherwise = And lit (int2f xs)
  where
    lit = if (d==False) then Neg (V i) else (V i) 

-- 3)
--Funcion auxiliar:
satAux2 :: [L] -> [(Var, Bool)] -> Bool
satAux2 [] i = esConsistente i
satAux2 ((Neg (Neg f)):xs) i = satAux2 (f:xs) i
satAux2 ((V p): xs) i = satAux2 xs ((p, True):i)
satAux2 ((Neg(V p)):xs) i = satAux2 xs ((p, False):i)
satAux2 ((And f1 f2):xs) i = satAux2 (f1:f2:xs) i
satAux2 ((Or f1 f2):xs) i = satAux2 (f1:xs) i || satAux2 (f2:xs) i
satAux2 ((Imp f1 f2):xs) i = satAux2 (Neg f1:xs) i || satAux2 (f2:xs) i
satAux2 ((Iff f1 f2):xs) i = satAux2 (f1:f2:xs) i || satAux2 (Neg f1:Neg f2:xs) i
satAux2 (Neg(And f1 f2):xs) i = satAux2 (Neg f1:xs) i || satAux2 (Neg f2:xs) i
satAux2 (Neg(Or f1 f2):xs) i = satAux2 (Neg f1:Neg f2:xs) i
satAux2 (Neg(Imp f1 f2):xs) i = satAux2 (f1:Neg f2:xs) i
satAux2 (Neg(Iff f1 f2):xs) i = satAux2 (Neg f1:f2:xs) i || satAux2 (f1:Neg f2:xs) i

-- Pre: recibe una fórmula f de LP
-- Pos: retorna True si y solo si f es sat
-- Hecha en clase con Juan
sat :: L -> Bool
sat f = satAux2 [f] []

-- 4)
--Funcion auxiliar:

-- Pre: recibe una fórmula f de LP
-- Pos: retorna una pareja (b,m) tal que: 
-- b es True  y m es modelo de f , ssi f es sat
-- b es False y m es vacío       , ssi f no es sat
satM :: L -> (Bool, I)
satM f = if (sat f) then (True, satMAux f (vars f)) else (False,[])

satMAux:: L->[Var]->I
satMAux f [] = []
satMAux f (x:xs) = if sat (sust x bot f) then (x,False):(satMAux (sust x bot f) xs) else (x,True):(satMAux(sust x top f) xs)


-- 5)
-- Pre: recibe una fórmula f de LP
-- Pos: retorna la cantidad de modelos de f
satC :: L -> Nat
satC f = case (satM f) of{
 (True,i)-> 1+ satC(And f (Neg(int2f i))) ;
 (False, _)-> 0;
}

-- 6)
-- Pre: recibe una fórmula f de LP y una clase de fórmulas C
-- Pos: retorna True si y solo si f está en C
es :: L -> Clase -> Bool
es f Sat = sat f
es f Tau = sat f
es f Contra = sat (Neg f)
es f Cont = es f Sat && es f Fal
es f Fal = es f Contra || not (sat f)

-- 7)
-- Pre: recibe un razonamiento r
-- Pos: retorna r expresado como una fórmula de LP
raz2f :: Razonamiento -> L
raz2f (p,c) = Imp (bigAnd p) c

bigAnd :: [L] -> L
bigAnd [] = top
bigAnd [x] = x
bigAnd (x:xs) = And x (bigAnd xs)

-- 8)     
-- Pre: recibe un razonamiento r
-- Pos: retorna una pareja (b,m) tal que: 
--        b es True  y m es vacío                   , ssi r es válido
--        b es False y m es un contraejemplo de r   , ssi f no es válido
--Hecho en clase
validez :: Razonamiento -> (Bool, I)
validez = \r -> case (snd(satM(Neg(raz2f r)))) of{
  [] -> (True, []);
  (x:xs) -> (False, snd(satM(Neg(raz2f r))));
}

-- 9)
-- Pre: recibe una fórmula f de LP
-- Pos: retorna f en FND

-- Ejercicio con ayuda hecho en clase (con Juan)
-- Funcion auxiliar:
auxFnd :: L -> L -> L
auxFnd = \l -> \d -> case (satM l) of{
 (True,i) -> auxFnd (And l (Neg (int2f i))) (Or d (int2f i));
 (False,_) -> d;
}

fnd :: L -> L 
fnd = \l -> auxFnd l bot; 
----------------------------------------------------------------------------------
-- Algunas funciones auxiliares 
----------------------------------------------------------------------------------
vars :: L -> [Var]
vars (V p)       = [p]
vars (Neg a)     = vars a
vars (a `And` b) = nub $ vars a ++ vars b
vars (a `Or` b)  = nub $ vars a ++ vars b
vars (a `Imp` b) = nub $ vars a ++ vars b
vars (a `Iff` b) = nub $ vars a ++ vars b  

sust :: Var -> L -> L -> L
sust v f (V p)
  | p == v     = f
  | otherwise  = V p
sust v f (Neg f1)      = Neg (sust v f f1)
sust v f (f1 `And` f2) = (sust v f f1) `And` (sust v f f2)
sust v f (f1 `Or`  f2) = (sust v f f1) `Or`  (sust v f f2)
sust v f (f1 `Imp` f2) = (sust v f f1) `Imp` (sust v f f2)
sust v f (f1 `Iff` f2) = (sust v f f1) `Iff` (sust v f f2)

----------------------------------------------------------------------------------
-- Pretty Printing (rudimentario)
----------------------------------------------------------------------------------
instance Show L where
  show (V p)         = p
  show (Neg (Neg a)) = "¬" ++ show (Neg a)
  show (Neg (V p))   = "¬ " ++ show (V p)
  show (Neg a)       = "¬ (" ++ show a ++ ")"
  show (a `And` b)   = "(" ++ show a ++ ") /\\ (" ++ show b ++ ")"
  show (a `Or` b)    = "(" ++ show a ++ ") \\/ (" ++ show b ++ ")"
  show (a `Imp` b)   = "(" ++ show a ++ ") --> (" ++ show b ++ ")"
  show (a `Iff` b)   = "(" ++ show a ++ ") <-> (" ++ show b ++ ")"