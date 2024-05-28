module LogLin (LL(..), areNegation) where
------------------LL FORMULAS-----------------------------
data LL = Bot | Un | Top | Zero
        | Var String
        | Not LL
        | Tensor LL LL | Parr LL LL
        | Plus LL LL | With LL LL 
        | OfCourse LL | WhyNot LL   
    deriving Show 

---------------------FORMULE'S EQUALITY----------------------
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

--------------------- F NEGATION OF G ---------------------------

takeNotDown :: LL -> LL  --applies negation and get it as deep as possible in the formula's tree
takeNotDown f = case f of
    Bot -> Un
    Un -> Bot
    Top -> Zero
    Zero -> Top
    Var v -> Not (Var v)
    Not f -> f
    Tensor f g -> Parr (takeNotDown f) (takeNotDown g) 
    Parr f g -> Tensor (takeNotDown f) (takeNotDown g) 
    Plus f g -> With (takeNotDown f) (takeNotDown g)  
    With f g -> Plus (takeNotDown f) (takeNotDown g)  
    OfCourse f -> WhyNot (takeNotDown f) 
    WhyNot f -> OfCourse (takeNotDown f)

takeNotsDown :: LL -> LL  --takes down all negation as deep as possible
takeNotsDown f = case f of
    Bot -> Bot
    Un -> Un
    Top -> Top
    Zero -> Zero
    Var v -> Var v
    Not (Var v) -> Not (Var v)
    Not f -> takeNotsDown (takeNotDown f)
    Tensor f g -> Tensor (takeNotsDown f) (takeNotsDown g) 
    Parr f g -> Parr (takeNotsDown f) (takeNotsDown g) 
    Plus f g -> Plus (takeNotsDown f) (takeNotsDown g)  
    With f g -> With (takeNotsDown f) (takeNotsDown g)  
    OfCourse f -> OfCourse (takeNotsDown f) 
    WhyNot f -> WhyNot (takeNotsDown f)

areNegation :: LL -> LL -> Bool
areNegation f g = (takeNotsDown f) == (takeNotsDown (Not g))

f3 :: LL
f3 = Tensor (Not (Var "A")) (Var "A")       -- = f1 negation
f4 :: LL
f4 = Not(OfCourse (With (Var "A") (Var "B")))   -- f2 negation, not still high
f5 :: LL
f5 = WhyNot (Not (With (Var "A") (Var "B")))    -- f2 negation, not partially taken down
f6 :: LL
f6 = Tensor (Not (Var "A")) (Not (Not (Var "A")))   -- f1 negation, with involution

main = 
    if areNegation f1 f3 == False then
        error "areNegation f1 f3 == False"
    else if areNegation f2 f4  == False then
        error "areNegation f2 f4  == False "
    else if areNegation f2 f5  == False then
        error "areNegation f2 f5  == False "
    else if areNegation f1 f5  == False then
        error "areNegation f1 f5  == False "
    else
        print "Tests OK"