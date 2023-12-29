module Lab4 where
------------------- Estudiante/s -------------------
-- Nombres y apellidos: Santiago Blanco
-- Números: 282654
----------------------------------------------------

import Prelude
import Data.List

import Lab3

----------------------------------------------------------------------------------
-- Sudoku
----------------------------------------------------------------------------------

type Config = [(Int,Int,Int)]

bigAndS :: [Nat] -> (Nat->L) -> L
bigAndS [] f = top
bigAndS [x] f = f x
bigAndS (x:xs) f =(f x) `And` (bigAndS xs f)

bigOrS :: [Nat] -> (Nat->L) -> L
bigOrS [] f = bot
bigOrS [x] f = f x
bigOrS (x:xs) f =(f x) `Or` (bigOrS xs f)

contiene :: Var -> Nat -> Nat -> Nat -> L
contiene prefijo i j k = V (prefijo ++ show i ++ show j ++ show k)

leer :: Config -> L
leer [(a,b,c)] = contiene "p" a b c
leer ((a,b,c):xs) = And (contiene "p" a b c) (leer xs)

-- Pre: recibe un número cuadrado n y una configuración inicial c para jugar un Sudoku de tamaño nXn
-- Pos: retorna una fórmula de LP formalizando el problema de resolver el Sudoku de tamaño nXn 
--      partiendo de la configuración c

-- Las 4 condiciones:
verificarFilas :: Nat -> L
verificarFilas n = bigAndS [1..n] (\f->bigAndS [1..n] (\k-> bigOrS [1..n] (\c-> contiene "p" f c k)))

verificarColumna :: Nat -> L
verificarColumna n = bigAndS [1..n] (\c->bigAndS [1..n] (\k-> bigOrS [1..n] (\f-> contiene "p" f c k)))

verificarRegion :: Nat -> L
verificarRegion n = bigAndS [0..(isqrt n)-1] (\rf-> bigAndS [0..(isqrt n)-1] (\rc -> bigAndS [1..n] (\k -> bigOrS [1..(isqrt n)] (\f-> bigOrS [1..(isqrt n)] (\c-> contiene "p" ((rf * (isqrt n)) + f) ((rc * (isqrt n)) + c) k)))))

verificarCelda :: Nat -> L
verificarCelda n = bigAndS [1..n] (\f->bigAndS [1..n] (\c-> bigOrS [1..n] (\k-> contiene "p" f c k `And` bigAndS ([1..n]\\[k]) (\l -> Neg(contiene "p" f c l)))))

sudoku :: Nat -> Config -> L
sudoku n config = bigAnd[(verificarFilas n),(verificarColumna n),(verificarRegion n),(verificarCelda n),(leer config)]


-- Configuración inicial para un Sudoku 2x2
c_n4 :: Config
c_n4 = [(2, 1, 3), (4, 1, 2), (3, 3, 2), (3, 4, 1),
 (4, 3, 3), (4, 4, 4)]


-- Configuración inicial para un Sudoku 3x3
c_n9 :: Config
c_n9 = [(1, 3, 9), (2, 2, 7),(3, 2, 3), (1, 4, 5),
 (2, 5, 4), (2, 6, 8), (1, 7, 2), (1, 9, 8),
 (4, 2, 8), (6, 2, 2), (6, 3, 5), (4, 4, 4),
 (6, 5, 6), (4, 7, 5), (6, 7, 9), (7, 3, 6),
 (8, 3, 8), (9, 1, 7), (7, 4, 2), (7, 6, 9),
 (9, 5, 8), (9, 6, 6), (7, 8, 7), (8, 7, 3),
 (8, 8, 5), (9, 9, 2)]

----------------------------------------------------------------------------------
-- Algunas funciones auxiliares 
----------------------------------------------------------------------------------

-- Pre: recibe un natural n.
-- Pos: devuelve la raiz cuadrada entera de n.
isqrt :: Nat -> Nat
isqrt 0 = 0
isqrt n = if (r+1)*(r+1) <= n then r+1 else r
          where 
            r = isqrt (n-1)

-- Pre: recibe una fórmula de LP.
-- Pos: pretty printing de la fórmula en formato SMT-LIB, esto es: parentizada y prefija.
toPrefix :: L -> String
toPrefix (V p)       = p
toPrefix (Neg a)     = "(not " ++ toPrefix a ++ ")"
toPrefix (a `And` b) = "(and " ++ toPrefix a ++ " " ++ toPrefix b ++ ")"
toPrefix (a `Or` b)  = "(or "  ++ toPrefix a ++ " " ++ toPrefix b ++ ")"
toPrefix (a `Imp` b) = "(=> "  ++ toPrefix a ++ " " ++ toPrefix b ++ ")"
toPrefix (a `Iff` b) = "(= "   ++ toPrefix a ++ " " ++ toPrefix b ++ ")"