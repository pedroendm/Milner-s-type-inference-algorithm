import Data.List
import Control.Monad.State
import Data.Maybe

type Id = String

data Type = TypeVariable Id
          | Comp Type Type
          deriving (Eq, Show)

fvType :: Type -> [Type]
fvType (TypeVariable id) = [(TypeVariable id)]
fvType (Comp t1 t2) = fvType t1 ++ fvType t2

typeToString :: Type -> String
typeToString (TypeVariable x) = x
typeToString (Comp t1 t2) = "(" ++ typeToString t1 ++ " -> " ++ typeToString t2 ++ ")"

data Term = TermVariable Id
          | Application Term Term
          | Abstraction Term Term
          deriving (Eq, Show)

fvTerm :: Term -> [Term]
fvTerm (TermVariable id) = [(TermVariable id)]
fvTerm (Application t1 t2) = fvTerm t1 ++ fvTerm t2
fvTerm (Abstraction t1 t2) = (fvTerm t2) \\ [t1] 

termToString :: Term -> String
termToString (TermVariable x) = x
termToString (Application m1 m2) = "(" ++ termToString m1 ++ termToString m2 ++ ")"
termToString (Abstraction (TermVariable x) m) = "(\\" ++ x ++ "." ++ termToString m ++ ")"

type Basis = [(Term, Type)]

type Substitution = [(Type, Type)]

composeSubstitution :: Substitution -> Substitution -> Substitution
composeSubstitution [] ys = ys
composeSubstitution ((a,b):xs) ys = case lookup b ys of
                            Just c -> (a,c) : composeSubstitution xs ys
                            Nothing -> (a,b) : composeSubstitution xs ys

applySubstitutionType :: Substitution -> Type -> Type
applySubstitutionType s (TypeVariable id) = case lookup (TypeVariable id) s of
                                        Just t -> t
                                        Nothing -> TypeVariable id 
applySubstitutionType s (Comp t1 t2) =  Comp (applySubstitutionType s t1) (applySubstitutionType s t2) 

applySubstitutionBasis :: Substitution -> Basis -> Basis
applySubstitutionBasis s b = map (\(x, y) -> (x, applySubstitutionType s y)) b


_unify :: Type -> Type -> Substitution
_unify (TypeVariable id) t | not $ elem (TypeVariable id) (fvType t) = [((TypeVariable id), t)]
                           | (TypeVariable id) == t  = []
                           | otherwise               = error "fail in unification"
_unify (Comp t1 t2) (TypeVariable id) = _unify (TypeVariable id) (Comp t1 t2)
_unify (Comp t1 t2) (Comp t3 t4) = let s1 = _unify t2 t4
                                  in composeSubstitution s1 (_unify (applySubstitutionType s1 t1) (applySubstitutionType s1 t3)) 

unify :: [(Type, Type)] -> Substitution
unify [(t1, t2)] = _unify t1 t2 
unify ((t1, t2):t) = _unify t1 t2 ++ unify (map (\(x, y) -> (applySubstitutionType (_unify t1 t2) x, applySubstitutionType (_unify t1 t2) y))  t)

_equations :: [Term] -> Basis -> Basis -> [(Type, Type)]
_equations [] g1 g2 = []
_equations (v:vs) g1 g2 = let
                            d1 = fromJust $ lookup v g1
                            d2 = fromJust $ lookup v g2
                          in if d1 == d2 then _equations vs g1 g2 else (d1, d2) : _equations vs g1 g2 

t :: Int -> Term -> (Int, Basis, Type)
t c (TermVariable id)   = (c+1, [(TermVariable id, TypeVariable ("a" ++ show c))], TypeVariable ("a" ++ show c))
t c (Application m1 m2) = let
                            (c', b_m1, t_m1)  = t c  m1
                            (c'', b_m2, t_m2) = t c' m2
                            vs = intersect (fvTerm m1) (fvTerm m2)
                            g1 = filter (\(v,d) -> elem v vs) b_m1
                            g2 = filter (\(v,d) -> elem v vs) b_m2
                            s = unify ((_equations vs g1 g2) ++ [(t_m1, Comp t_m2 (TypeVariable ("a" ++ show c'')))])
                          in (c'' + 1, applySubstitutionBasis s (b_m1++b_m2), applySubstitutionType s (TypeVariable ("a" ++ show c'')))
t c (Abstraction (TermVariable x) n) = let 
                            (c', b_n, t_n) = t c n
                            in case lookup (TermVariable x) b_n of
                              Just t  -> (c' + 1, filter (\(v, d) -> v /= (TermVariable x)) b_n, Comp t t_n)
                              Nothing -> (c' + 1, b_n, Comp (TypeVariable ("a" ++ show c')) t_n)

typify :: Term -> IO ()
typify m = do 
  putStrLn  $ "Term: " ++ termToString m
  let (_, b, s) = t 1 m
  putStrLn  $ "Basis: {" ++ (intercalate ", " (map (\(v,d) -> termToString v ++ ": " ++ typeToString d) b)) ++ "}"
  putStrLn  $ "Type: " ++ typeToString s
  putStrLn  "\n"

main = do
    let terms = ([ TermVariable "x",
                   Application (TermVariable "x") (TermVariable "y"),
                   Abstraction (TermVariable "x") (TermVariable "x"),
                   Abstraction (TermVariable "x") (TermVariable "y"),
                   Abstraction (TermVariable "x") (Abstraction (TermVariable "y") (Abstraction (TermVariable "z") (Application (TermVariable "x") (Application (TermVariable "y") (TermVariable "z"))))),
                   Abstraction (TermVariable "x") (Abstraction (TermVariable "y") (Abstraction (TermVariable "z") (Application (Application (TermVariable "x") (TermVariable "z")) (TermVariable "y")))),
                   Abstraction (TermVariable "x") (Abstraction (TermVariable "y") (Application (Application (TermVariable "x") (TermVariable "y")) (TermVariable "y"))),
                   Abstraction (TermVariable "x") (Abstraction (TermVariable "y") (Abstraction (TermVariable "z") (Application (Application (TermVariable "x") (TermVariable "z")) (Application (TermVariable "y") (TermVariable "z")))))])

    mapM_ typify terms