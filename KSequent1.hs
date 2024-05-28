module KSequent1 (Sequent(..), Proof(..), isValidProof, getProduction,getConclusion, isRedex, isCutRooted, isLeftChildCutRooted, isRightChildCutRooted) where
import LogLin 
------------------UNILETERAL SEQUENTS---------------------------------------
newtype Sequent = Sequent [LL] deriving Show

removeIfIn :: LL -> Sequent -> (Sequent, Bool)
removeIfIn e l  = case l of
    Sequent [] -> (Sequent [], False)
    Sequent (e':t) -> let (Sequent t',b) = removeIfIn e (Sequent t) in
        if (e==e') 
        then (Sequent t,True) 
        else (Sequent (e':t'),b)

instance Eq Sequent where
    -- Egalité si les deux séquents contenent les mêmes formules
    s1 == s2 = case (s1, s2) of
        (Sequent [],Sequent []) -> True
        (Sequent (h1:t1),s2) -> 
            let (s2',belong) = removeIfIn h1 s2 
            in if belong then (Sequent t1) == s2' else False
        (_,_) -> False

isWhyNotSequent :: Sequent -> Bool
isWhyNotSequent (Sequent s) = case s of
    [] -> True
    ((WhyNot f):q) ->  isWhyNotSequent (Sequent q)
    _ -> False

whyNotSequent = Sequent [WhyNot(Var "A"), WhyNot(Tensor a b)]
notWhyNotSequent = Sequent [Var "A", WhyNot(Tensor a b)]
notWhyNotSequent2 = Sequent [WhyNot(Var "A"),Var "A", WhyNot(Tensor a b)]
notWhyNotSequent3 = Sequent [WhyNot(Var "A"), WhyNot(Var "A"), Tensor a b]

---- Rules and Proof
data Proof = AxRule LL LL
    | AxUn 
    | TopRule [LL]
--    | ExRule [LL] LL LL [LL] Proof
    | CutRule LL [LL] LL [LL] Proof Proof
    | TensorRule LL [LL] LL [LL] Proof Proof
    | ParrRule LL LL [LL] Proof
    | BotRule [LL] Proof
    | PlusLRule LL LL [LL] Proof   -- left part added
    | PlusRRule LL LL [LL] Proof   -- right part added
    | WithRule LL LL [LL] Proof Proof
    | PromRule LL [LL] Proof
    | DerRule LL [LL] Proof
    | AffRule LL [LL] Proof
    | ContrRule LL [LL] Proof
    deriving Show


a::LL
a = Var "A"
b::LL
b = Var "B"
p1 :: Proof
p1 = TensorRule a [WhyNot (Not a)] b [WhyNot (Not b)]
                    (DerRule (Not a) [a]
                        (AxRule a (Not a)))
                    (DerRule (Not b) [b]
                        (AxRule b (Not b)))

p2 :: Proof
p2 = ParrRule (WhyNot (Not a)) (WhyNot (Not b)) [OfCourse (Tensor a b)]
                (PromRule (Tensor a b) [WhyNot (Not a) , WhyNot (Not b)] 
                    p1)

isPartition :: [LL] -> [LL] -> [LL] -> Bool -- check if the two first lists makes a partition of the third one
isPartition gamma delta union = 
    let seq1 = Sequent (gamma++delta) in
    let seq2 = Sequent union in
        seq1 == seq2

getConclusion :: Proof -> Sequent
getConclusion p = case p of
    AxRule f g -> Sequent [f,g]
    AxUn -> Sequent [Un]
    TopRule gamma -> Sequent (Top:gamma)
--    ExRule gamma f g delta _ -> Sequent (f:g:(gamma ++ delta))
    CutRule _ gamma _ delta _ _ -> Sequent (gamma ++ delta)
    TensorRule f gamma g delta _ _ -> Sequent ((Tensor f g):(delta ++ gamma))
    ParrRule f g gamma _ -> Sequent ((Parr f g):gamma)
    BotRule gamma _ -> Sequent (Bot:gamma)
    PlusLRule f g gamma _ -> Sequent ((Plus f g):gamma)
    PlusRRule f g gamma _ -> Sequent ((Plus f g):gamma)
    WithRule f g gamma _ _ -> Sequent ((With f g):gamma)
    PromRule f gamma _ -> Sequent ((OfCourse f):gamma)
    DerRule f gamma _ -> Sequent ((WhyNot f):gamma)
    AffRule f gamma _ -> Sequent ((WhyNot f) : gamma)
    ContrRule f gamma _ -> Sequent ((WhyNot f):gamma)



getProduction :: Proof -> [LL]     --returns a list with the formulas created by the last rule
getProduction (AxRule a aOrtho) =  [a, aOrtho]
getProduction AxUn =  [Un]
getProduction (TopRule _) =  [Top]
getProduction (CutRule _ _ _ _ _ _ ) =  []
getProduction (TensorRule a _ b _ _ _ )=  [Tensor a b]
getProduction (ParrRule a b _ _) =  [Parr a b]
getProduction (BotRule _ _) =  [Bot]
getProduction (PlusRRule a b _ _) =  [Plus a b]
getProduction (PlusLRule a b _ _) =  [Plus a b]
getProduction (WithRule a b _ _ _) =  [With a b]
getProduction (PromRule a _ _) =  [OfCourse a]
getProduction (DerRule a _ _) =  [WhyNot a]
getProduction (AffRule a _ _) =  [WhyNot a]
getProduction (ContrRule a _ _) =  [WhyNot a]

isAxRuleRooted :: Proof -> Bool
isAxRuleRooted (AxRule _ _) = True
isAxRuleRooted _ = False

isRedex ::Proof -> Bool
isRedex (CutRule f _ fOrtho _ p1 p2) = 
    (isAxRuleRooted p1)
    || (isAxRuleRooted p2)
    || ((f `elem` (getProduction p1)) && (fOrtho `elem` (getProduction p2)))
isRedex _ = False 

isCutRooted :: Proof -> Bool
isCutRooted (CutRule _ _ _ _ _ _) = True
isCutRooted _ = False

isLeftChildCutRooted :: Proof -> Bool -- teste si un Proof cutRooted à sa sousProof gauche cutRooted
isLeftChildCutRooted (CutRule _ _ _ _ pch _) = isCutRooted pch
isLeftChildCutRooted _ = False

isRightChildCutRooted :: Proof -> Bool -- teste si un Proof cutRooted à sa sousProof gauche cutRooted
isRightChildCutRooted (CutRule _ _ _ _ _ pch) = isCutRooted pch
isRightChildCutRooted _ = False

isValidProof :: Proof -> Bool
isValidProof p = case p of
    AxRule f g -> 
        areNegation f g       -- 
    AxUn -> 
        True
    TopRule _ -> 
        True
    -- ExRule gamma f g delta p -> 
    --     (Sequent(f:g:(gamma++delta)) == (getConclusion p))
    --     &&(isValidProof p)
    CutRule f gamma g delta pg pd -> 
        (areNegation f g)
        &&(Sequent(f:gamma)==(getConclusion pg))
        &&(Sequent(g:delta)==(getConclusion pd))
        &&(isValidProof pg)&&(isValidProof pd)
    TensorRule f gamma g delta pg pd -> 
        (Sequent(f:gamma)==(getConclusion pg))
        &&(Sequent(g:delta)==(getConclusion pd))
        &&(isValidProof pg)&&(isValidProof pd)
    ParrRule f g gamma p ->
        (Sequent(f:g:gamma)==(getConclusion p))
        && (isValidProof p)
    BotRule gamma p -> 
        (Sequent gamma == (getConclusion p))
        &&(isValidProof p)
    PlusLRule f g gamma p ->
        (Sequent(g:gamma)==(getConclusion p))
        &&(isValidProof p)
    PlusRRule f g gamma p ->
        (Sequent(f:gamma)==(getConclusion p))
        &&(isValidProof p)
    WithRule f g gamma pg pd ->
        (Sequent(f:gamma)==(getConclusion pg))
        &&(Sequent(g:gamma)==(getConclusion pd))
        &&(isValidProof pg)&&(isValidProof pd)
    PromRule f gamma p ->
        (isWhyNotSequent (Sequent gamma))
        &&(Sequent(f:gamma)==(getConclusion p))
        &&(isValidProof p)
    DerRule f gamma p ->
        (Sequent(f:gamma)==(getConclusion p))
        &&(isValidProof p)
    AffRule f gamma p ->
        (Sequent gamma ==(getConclusion p))
        &&(isValidProof p)
    ContrRule f gamma p ->
        (Sequent((WhyNot f):(WhyNot f):gamma)==(getConclusion p))
        &&(isValidProof p)

pn1 :: Proof --invalid : CutRule negation criteria
pn1 = CutRule (Plus a a) [Not a] (With a a) [Not a] 
            (PlusRRule a a [Not a] 
                (AxRule a (Not a)))
            (WithRule a a [Not a] (
                AxRule a (Not a)) (
                AxRule a (Not a)))

pn2 :: Proof  -- invalid : AxRule negation criteria
pn2 = AxRule (Tensor a b) (Tensor (Not a) (Not b))

pn3 :: Proof   -- invalid because of WithRule's gamma
pn3 = WithRule a a [Plus (Not a) b , Plus (Not a) a]
                (PlusRRule (Not a) b [a] 
                    (AxRule a (Not a)))
                (PlusRRule (Not a) a [a]
                    (AxRule a (Not a)))

pn4 :: Proof
pn4 = AffRule a [Not a] (AxRule a (Not a))

pn5 :: Proof
pn5 = PromRule a [Not a] (AxRule a (Not a))

pn6 :: Proof
pn6 = DerRule (Not a) [Tensor a a]
        (TensorRule a [Not a] a [Not a]
            (AxRule a (Not a))
            (AxRule a (Not a)))

main = 
    if not $ isWhyNotSequent whyNotSequent then
        error "isWhyNotSequent whyNotSequent == False"
    else if isWhyNotSequent notWhyNotSequent then
        error "isWhyNotSequent notWhyNotSequent == True"
    else if isWhyNotSequent notWhyNotSequent2 then
        error "isWhyNotSequent notWhyNotSequent2 == True"
    else if isWhyNotSequent notWhyNotSequent3 then
        error "isWhyNotSequent notWhyNotSequent3 == True"
    else if isValidProof pn1 then
        error "isValidProof pn1"
    else if isValidProof pn2 then
        error "isValidProof pn2"
    else if isValidProof pn3 then
        error "isValidProof pn3"
    else if not $ isValidProof pn4 then
        error "not isValidProof pn4"
    else if not $ isValidProof pn5 then
        error "not isValidProof pn5"
    else if not $ isValidProof pn6 then
        error "Not isValidProof pn6"
    else
        print "Tests OK"