module KSequent1 (Sequent, Preuve(..), isValidProof) where
import LogLin 
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

isWhyNotSequent :: Sequent -> Bool
isWhyNotSequent (Sequent s) = case s of
    [] -> True
    ((WhyNot f):q) ->  isWhyNotSequent (Sequent q)
    _ -> False

whyNotSequent = Sequent [WhyNot(Var "A"), WhyNot(Tensor a b)]
pasWhyNotSequent = Sequent [Var "A", WhyNot(Tensor a b)]
pasWhyNotSequent2 = Sequent [WhyNot(Var "A"),Var "A", WhyNot(Tensor a b)]
pasWhyNotSequent3 = Sequent [WhyNot(Var "A"), WhyNot(Var "A"), Tensor a b]

---- Regles et Preuve
{-data StructurePreuve = Axiome LL LL
                    | Regle1 LL [LL] StructurePreuve
                    | Regle2 LL [LL] StructurePreuve StructurePreuve
-}

-- data Axiome = Axiome {f :: LL, fOrtho :: LL}
-- data AxiomeUn = AxiomeUn {un :: LL} 
-- data ExangeRule = ExangeRule {gamma :: [LL], f :: LL, g:: LL, delta :: [LL]}
-- data CoupureRule = CoupureRule {gamma :: [LL], f :: LL, fOrtho :: LL, delta :: [LL]}

data Preuve = AxRule LL LL
    | AxUn 
    | TopRule [LL]
    | ExRule [LL] LL LL [LL] Preuve
    | CutRule LL [LL] LL [LL] Preuve Preuve
    | TensorRule LL [LL] LL [LL] Preuve Preuve
    | ParrRule LL LL [LL] Preuve
    | BotRule [LL] Preuve
    | PlusGRule LL LL [LL] Preuve   -- le membre de gauche est ajouté
    | PlusDRule LL LL [LL] Preuve   -- le membre de droite est ajouté
    | WithRule LL LL [LL] Preuve Preuve
    | PromRule LL [LL] Preuve
    | DerRule LL [LL] Preuve
    | AffRule LL [LL] Preuve
    | ContrRule LL [LL] Preuve

a::LL
a = Var "A"
b::LL
b = Var "B"
p1 :: Preuve
p1 = TensorRule a [WhyNot (Not a)] b [WhyNot (Not b)]
                    (DerRule (Not a) [a]
                        (AxRule a (Not a)))
                    (DerRule (Not b) [b]
                        (AxRule b (Not b)))

p2 :: Preuve
p2 = ParrRule (WhyNot (Not a)) (WhyNot (Not b)) [OfCourse (Tensor a b)]
                (PromRule (Tensor a b) [WhyNot (Not a) , WhyNot (Not b)] 
                    p1)

estPartition :: [LL] -> [LL] -> [LL] -> Bool -- teste si les deux premières listes sont une partition de la troixieme
estPartition gamma delta union = 
    let seq1 = Sequent (gamma++delta) in
    let seq2 = Sequent union in
        seq1 == seq2

getConclusion :: Preuve -> Sequent
getConclusion p = case p of
    AxRule f g -> Sequent [f,g]
    AxUn -> Sequent [Un]
    TopRule gamma -> Sequent (Top:gamma)
    ExRule gamma f g delta _ -> Sequent (f:g:(gamma ++ delta))
    CutRule _ gamma _ delta _ _ -> Sequent (gamma ++ delta)
    TensorRule f gamma g delta _ _ -> Sequent ((Tensor f g):(delta ++ gamma))
    ParrRule f g gamma _ -> Sequent ((Parr f g):gamma)
    BotRule gamma _ -> Sequent (Bot:gamma)
    PlusGRule f g gamma _ -> Sequent ((Plus f g):gamma)
    PlusDRule f g gamma _ -> Sequent ((Plus f g):gamma)
    WithRule f g gamma _ _ -> Sequent ((With f g):gamma)
    PromRule f gamma _ -> Sequent ((OfCourse f):gamma)
    DerRule f gamma _ -> Sequent ((WhyNot f):gamma)
    AffRule f gamma _ -> Sequent ((WhyNot f) : gamma)
    ContrRule f gamma _ -> Sequent (f:gamma)

isValidProof :: Preuve -> Bool
isValidProof p = case p of
    AxRule f g -> 
        areNegation f g       -- 
    AxUn -> 
        True
    TopRule _ -> 
        True
    ExRule gamma f g delta p -> 
        (Sequent(f:g:(gamma++delta)) == (getConclusion p))
        &&(isValidProof p)
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
    PlusGRule f g gamma p ->
        (Sequent(g:gamma)==(getConclusion p))
        &&(isValidProof p)
    PlusDRule f g gamma p ->
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

pn1 :: Preuve --fausse sur negation de cutrule
pn1 = CutRule (Plus a a) [Not a] (With a a) [Not a] 
            (PlusDRule a a [Not a] 
                (AxRule a (Not a)))
            (WithRule a a [Not a] (
                AxRule a (Not a)) (
                AxRule a (Not a)))

pn2 :: Preuve  -- faux sur negation axiomme
pn2 = AxRule (Tensor a b) (Tensor (Not a) (Not b))

pn3 :: Preuve   -- faux sur gamma de WithRule
pn3 = WithRule a a [Plus (Not a) b , Plus (Not a) a]
                (PlusDRule (Not a) b [a] 
                    (AxRule a (Not a)))
                (PlusDRule (Not a) a [a]
                    (AxRule a (Not a)))

pn4 :: Preuve
pn4 = AffRule a [Not a] (AxRule a (Not a))

pn5 :: Preuve
pn5 = PromRule a [Not a] (AxRule a (Not a))

pn6 :: Preuve
pn6 = DerRule (Not a) [Tensor a a]
        (TensorRule a [Not a] a [Not a]
            (AxRule a (Not a))
            (AxRule a (Not a)))

