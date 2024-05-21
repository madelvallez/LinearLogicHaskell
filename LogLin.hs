module LogLin (LL(..), areNegation) where
------------------FORMULES DE LL-----------------------------
data LL = Bot | Un | Top | Zero
        | Var String
        | Not LL
        | Tensor LL LL | Parr LL LL
        | Plus LL LL | With LL LL 
        | OfCourse LL | WhyNot LL   
    deriving Show 

---------------------EGALITE DE FORMULES ----------------------
instance Eq LL where
    f1 == f2 = case (f1,f2) of
        (Bot,Bot) -> True
        (Un,Un) -> True
        (Top,Top) -> True 
        (Zero,Zero) -> True
        (Var s1, Var s2) -> s1==s2
        (Not g1, Not g2) -> g1 == g2
        (OfCourse g1, OfCourse g2) -> g1 == g2
        (WhyNot g1, WhyNot g2) -> g1 == g2
        (Tensor g d, Tensor g' d') -> g==g' && d==d'
        (Parr g d, Parr g' d') -> g==g' && d==d'
        (Plus g d, Plus g' d') -> g==g' && d==d'
        (With g d, With g' d') -> g==g' && d==d'
        (_,_) -> False

f1 :: LL
f1 = Parr (Var "A") (Not (Var "A"))
f2 :: LL
f2 = OfCourse (With (Var "A") (Var "B"))

--------------------- F NEGATION DE G ---------------------------

descendreNot :: LL -> LL  --applique une négation à f en la descendant au plus profond dans la formule
descendreNot f = case f of
    Bot -> Un
    Un -> Bot
    Top -> Zero
    Zero -> Top
    Var v -> Not (Var v)
    Not f -> f
    Tensor f g -> Parr (descendreNot f) (descendreNot g) 
    Parr f g -> Tensor (descendreNot f) (descendreNot g) 
    Plus f g -> With (descendreNot f) (descendreNot g)  
    With f g -> Plus (descendreNot f) (descendreNot g)  
    OfCourse f -> WhyNot (descendreNot f) 
    WhyNot f -> OfCourse (descendreNot f)

descendreLesNot :: LL -> LL  --fait decendre au plus bas tout les Not de la formule
descendreLesNot f = case f of
    Bot -> Bot
    Un -> Un
    Top -> Top
    Zero -> Zero
    Var v -> Var v
    Not (Var v) -> Not (Var v)
    Not f -> descendreLesNot (descendreNot f)
    Tensor f g -> Tensor (descendreLesNot f) (descendreLesNot g) 
    Parr f g -> Parr (descendreLesNot f) (descendreLesNot g) 
    Plus f g -> Plus (descendreLesNot f) (descendreLesNot g)  
    With f g -> With (descendreLesNot f) (descendreLesNot g)  
    OfCourse f -> OfCourse (descendreLesNot f) 
    WhyNot f -> WhyNot (descendreLesNot f)

areNegation :: LL -> LL -> Bool
areNegation f g = (descendreLesNot f) == (descendreLesNot (Not g))

f3 :: LL
f3 = Tensor (Not (Var "A")) (Var "A")       --neg de f1
f4 :: LL
f4 = Not(OfCourse (With (Var "A") (Var "B")))   -- neg de f2 not descendus
f5 :: LL
f5 = WhyNot (Not (With (Var "A") (Var "B")))    -- neg de f2 not partiellement descendue
f6 :: LL
f6 = Tensor (Not (Var "A")) (Not (Not (Var "A")))


---------------------EQUIVALENCE DE FOMULES----------------------------
{-
Elements à considerer :
    - associativite des oerateurs binaires
    - commutativite 
    - distri de MLL sur ALL
    - regle de De Morgan
    - Idempotence des 
-}