import Prelude

------------------FORMULES DE LL-----------------------------
data LL = Bot | Un | Top | Zero
        | Var String
        | Not LL
        | Tensor LL LL | Parr LL LL
        | Plus LL LL | With LL LL 
        | OfCourse LL | WhyNot LL   
    deriving Show 

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

------------------SEQUENTS UNILATERES---------------------------------------
newtype Sequent = Sequent [LL] deriving Show

retireSiAppartient :: LL -> Sequent -> (Sequent, Bool)
retireSiAppartient e l  = case l of
    Sequent [] -> (Sequent [], False)
    Sequent (e':t) -> let (Sequent t',b) = retireSiAppartient e (Sequent t) in
        if (e==e') 
        then (Sequent t,True) 
        else (Sequent (e':t'),b)

instance Eq Sequent where
    -- Egalité si les deux séquents contenent les mêmes formules
    s1 == s2 = case (s1, s2) of
        (Sequent [],Sequent []) -> True
        (Sequent (h1:t1),s2) -> 
            let (s2',appartient) = retireSiAppartient h1 s2 
            in if appartient then (Sequent t1) == s2' else False
        (_,_) -> False

