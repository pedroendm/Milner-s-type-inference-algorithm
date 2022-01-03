import Data.List
import Data.Maybe

type Id = String

data Term = TermVariable Id
          | Application Term Term
          | Abstraction Term Term
          deriving (Eq, Show)

fvTerm :: Term -> [Term]
fvTerm (TermVariable id)                  = [(TermVariable id)]
fvTerm (Application t1 t2)                = fvTerm t1 ++ fvTerm t2
fvTerm (Abstraction (TermVariable id) t2) = fvTerm t2 \\ [(TermVariable id)] 

termToString :: Term -> String
termToString (TermVariable x)                 = x
termToString (Application m1 m2)              = "(" ++ termToString m1 ++ termToString m2 ++ ")"
termToString (Abstraction (TermVariable x) m) = "(\\" ++ x ++ "." ++ termToString m ++ ")"

data Type = TypeVariable Id
          | Comp Type Type
          deriving (Eq, Show)

fvType :: Type -> [Type]
fvType (TypeVariable id) = [(TypeVariable id)]
fvType (Comp t1 t2)      = fvType t1 ++ fvType t2

typeToString :: Type -> String
typeToString (TypeVariable x) = x
typeToString (Comp t1 t2)     = "(" ++ typeToString t1 ++ " -> " ++ typeToString t2 ++ ")"

type Basis = [(Term, Type)]

type Substitution = [(Type, Type)]

composeSubstitution :: Substitution -> Substitution -> Substitution
composeSubstitution [] ys         = ys
composeSubstitution ((a,b):xs) ys = case lookup b ys of
                                      Just c -> (a,c) : composeSubstitution xs ys
                                      Nothing -> (a,b) : composeSubstitution xs ys

applySubstitutionType :: Substitution -> Type -> Type
applySubstitutionType s (TypeVariable id) = case lookup (TypeVariable id) s of
                                              Just t -> t
                                              Nothing -> TypeVariable id 
applySubstitutionType s (Comp t1 t2)      = Comp (applySubstitutionType s t1) (applySubstitutionType s t2) 

applySubstitutionBasis :: Substitution -> Basis -> Basis
applySubstitutionBasis s b = map (\(x, y) -> (x, applySubstitutionType s y)) b

unifyEquation :: Type -> Type -> Substitution
unifyEquation (TypeVariable id) t | not $ elem (TypeVariable id) (fvType t) = [((TypeVariable id), t)]
                                  | (TypeVariable id) == t                  = []
                                  | otherwise                               = error "failed unification"
unifyEquation (Comp t1 t2) (TypeVariable id) = unifyEquation (TypeVariable id) (Comp t1 t2)
unifyEquation (Comp t1 t2) (Comp t3 t4)      = let s1 = unifyEquation t2 t4
                                               in composeSubstitution s1 (unifyEquation (applySubstitutionType s1 t1) (applySubstitutionType s1 t3)) 

unifyEquations :: [(Type, Type)] -> Substitution
unifyEquations [(t1, t2)]   = unifyEquation t1 t2 
unifyEquations ((t1, t2):t) = unifyEquation t1 t2 ++ unifyEquations (map (\(x, y) -> (applySubstitutionType (unifyEquation t1 t2) x, applySubstitutionType (unifyEquation t1 t2) y))  t)

generateEquations :: [Term] -> Basis -> Basis -> [(Type, Type)]
generateEquations [] g1 g2     = []
generateEquations (v:vs) g1 g2 = let
                                  d1 = fromJust $ lookup v g1
                                  d2 = fromJust $ lookup v g2
                                 in if d1 == d2 then generateEquations vs g1 g2 else (d1, d2) : generateEquations vs g1 g2 

t :: Int -> Term -> (Int, Basis, Type)
t c (TermVariable id)                = (c+1, [(TermVariable id, TypeVariable ("a" ++ show c))], TypeVariable ("a" ++ show c))
t c (Application m1 m2)              = let
                                         (c', b_m1, t_m1)  = t c  m1
                                         (c'', b_m2, t_m2) = t c' m2
                                         vs                = intersect (fvTerm m1) (fvTerm m2)
                                         g1                = filter (\(v,d) -> elem v vs) b_m1
                                         g2                = filter (\(v,d) -> elem v vs) b_m2
                                         s                 = unifyEquations $ (generateEquations vs g1 g2) ++ [(t_m1, Comp t_m2 (TypeVariable ("a" ++ show c'')))]
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
                   Application (Abstraction (TermVariable "x") (TermVariable "x")) (TermVariable "y"),
                   Application (TermVariable "x") (Application (TermVariable "y") (Application (TermVariable "z") (Application (TermVariable "w") (TermVariable "t")))),
                   Abstraction (TermVariable "x") (TermVariable "x"),
                   Abstraction (TermVariable "x") (TermVariable "y"),
                   Abstraction (TermVariable "x") (Abstraction (TermVariable "y") (Abstraction (TermVariable "z") (Application (TermVariable "x") (Application (TermVariable "y") (TermVariable "z"))))),
                   Abstraction (TermVariable "x") (Abstraction (TermVariable "y") (Abstraction (TermVariable "z") (Application (Application (TermVariable "x") (TermVariable "z")) (TermVariable "y")))),
                   Abstraction (TermVariable "x") (Abstraction (TermVariable "y") (Application (Application (TermVariable "x") (TermVariable "y")) (TermVariable "y"))),
                   Abstraction (TermVariable "x") (Abstraction (TermVariable "y") (Abstraction (TermVariable "z") (Application (Application (TermVariable "x") (TermVariable "z")) (Application (TermVariable "y") (TermVariable "z")))))])

    mapM_ typify terms