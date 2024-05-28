module ElimCut(elimCut) where
import LogLin
import KSequent1
import Data.List

removeNTimes :: Eq a => Int-> a -> [a] -> [a]
removeNTimes 0 f l = l
removeNTimes n f [] = error "Not enough element in the list"
removeNTimes n f (f':t) 
    | f == f' = removeNTimes (n-1) f t
    | otherwise = (f':removeNTimes n f t)



applyRedex :: Proof -> Proof     -- applies the redex on the root of the proof
applyRedex p = case p of
    CutRule _ _ _ _ (AxRule _ _) p2 -> p2
    CutRule _ _ _ _ p1 (AxRule _ _) -> p1

    CutRule  fcut gammaCut fOthoCut deltaCut
        (TensorRule b gamma1 c gamma2 p1 p2 )
        (ParrRule bOrtho cOrtho delta p3)
        -> CutRule b gamma1 bOrtho (gamma2++delta)
                p1
                (CutRule c gamma2 cOrtho (bOrtho:delta) p2 p3)

    CutRule  fcut gammaCut fOthoCut deltaCut
        (ParrRule bOrtho cOrtho delta p1)
        (TensorRule b gamma1 c gamma2 p2 p3 )
        -> CutRule cOrtho (delta++gamma1) c gamma2 
            (CutRule bOrtho delta b gamma1 p1 p2)
            p3

    CutRule Un gamma Bot delta AxUn (BotRule deltaBot p) -> p
    CutRule Bot gamma Un delta (BotRule deltaBot p) AxUn -> p

    CutRule f gamma fOrtho delta 
        (PlusRRule fPlus gPlus gammaPlus p1)
        (WithRule fWith gWith deltaWith p2 p3)
        -> CutRule fPlus gammaPlus fWith deltaWith p1 p2

    CutRule f gamma fOrtho delta
        (WithRule a b gammaWith p1 p2)
        (PlusRRule aOrtho bOrtho deltaPlus p3)
        -> CutRule a gammaWith aOrtho deltaPlus p1 p3

    CutRule f gamma fOrtho delta 
        (PlusLRule fPlus gPlus gammaPlus p1)
        (WithRule fWith gWith deltaWith p2 p3)
        -> CutRule gPlus gammaPlus gWith deltaWith p1 p3

    CutRule f gamma fOrtho delta
        (WithRule a b gammaWith p1 p2)
        (PlusLRule aOrtho bOrtho deltaPlus p3)
        -> CutRule b gammaWith bOrtho deltaPlus p2 p3

    CutRule fOC gammaWN fOrthoWN delta 
        (PromRule f gammaProm p1)
        (DerRule fOrtho deltaDer p2)
        -> CutRule f gammaProm fOrtho delta p1 p2

    CutRule fWN gamma fOrthoOC deltaWN
        (DerRule f gammaDer p1)
        (PromRule fOrtho delta p2)
        -> CutRule f gamma fOrtho delta p1 p2

    CutRule fOC gammaWN fOrthoWN delta 
        (PromRule f gamma p1)
        (AffRule fOrtho deltaAff p2)
        -> let iterateWhyNotRule gamma proof = case gamma of
                [] -> proof
                (f:gamma') -> let Sequent delta = getConclusion proof in
                    let WhyNot f' = f in
                    iterateWhyNotRule gamma'(AffRule f' delta proof)
            in iterateWhyNotRule gamma p2

    CutRule fWN gamma fOrthoWN deltaCut
        (AffRule f gammaAff p1)
        (PromRule fOrtho deltaWN p2)
        -> let iterateAffRule gamma proof = case gamma of
                [] -> proof
                (f:gamma') -> let Sequent delta = getConclusion proof in
                    let WhyNot f' = f in
                    iterateAffRule gamma'(AffRule f' delta proof)
            in iterateAffRule deltaWN p1

    CutRule fOC gammaWN fOrthoWN delta
        (PromRule f gamma p1)
        (ContrRule fOrtho deltaContr p2)
        -> let iterateContrRule gammaWN proof = case gammaWN of
                [] -> proof
                (f:gammaWN') -> 
                    let Sequent gamma' = (getConclusion proof)
                    in let gamma = removeNTimes 2 f gamma'
                    in let WhyNot f' = f
                    in iterateContrRule gammaWN' (ContrRule f' gamma proof)
           in let subProof = CutRule fOC gammaWN fOrthoWN (gammaWN++delta)
                                (PromRule f gamma p1)
                                (CutRule fOC gammaWN fOrthoWN (fOrthoWN:delta)
                                    (PromRule f gamma p1)
                                    p2)
           in iterateContrRule gammaWN subProof

    CutRule fWN gamma fOrthoOC deltaWN
        (ContrRule fWN' gammaContr p1)
        (PromRule fOrtho deltaWN' p2)
        -> let iterateContrRule gammaWN proof = case gammaWN of
                [] -> proof
                (f:gammaWN') -> 
                    let Sequent gamma' = getConclusion proof 
                    in let gamma = removeNTimes 2 f gamma'
                    in iterateContrRule gammaWN' (ContrRule f gamma proof)
           in let subProof = CutRule fWN (fWN:gamma++deltaWN) fOrthoOC deltaWN
                                (CutRule fWN (fWN:gamma) fOrthoOC deltaWN 
                                    p1
                                    (PromRule fOrtho deltaWN p2))
                                (PromRule fOrtho deltaWN p2)
           in iterateContrRule deltaWN subProof





getCutStatus :: Proof -> (Bool,Bool,Bool,Bool)   
    --gives the following infos  
    --  - CutRule's left-child's Rule is cutted
    --  - CutRule's right-child's Rule is cutted
    --  - CutRule's left-child's Rule is a PromRule
    --  - CutRule's right-child's Rule is a PromRule
getCutStatus (CutRule f gamma fOrtho delta p1 p2) =
    (f `elem` getProduction p1 , fOrtho `elem` getProduction p2, isPromRooted p1, isPromRooted p2)
getCutStatus _ = error "getCutStatus only works on cutRooted Proofs"

isPromRooted :: Proof -> Bool
isPromRooted (PromRule _ _ _) = True 
isPromRooted _ = False

applyComm :: Proof -> Proof
applyComm p  = case (getCutStatus p) of
    (False, _, True, True) -> applyLeftComm p
    (False, _, True, False) -> applyRightComm p 
    (_, False, True, True) -> applyRightComm p
    (_, False, False, True) -> applyLeftComm p 
    (True,_,_,_) -> applyRightComm p 
    (_,True,_,_) -> applyLeftComm p 
    _ -> applyLeftComm p


applyLeftComm :: Proof -> Proof
applyLeftComm (CutRule f gammaCut fOrtho delta 
                (ParrRule a b gammaParr p1)
                p2 ) =
    let gamma = filter ((/=) f) gammaParr in
        ParrRule a b (gamma++delta) 
            (CutRule f (a:b:gamma) fOrtho delta p1 p2)
applyLeftComm (CutRule c gammaCut cOrtho delta 
        (TensorRule a gammaG b gammaD p1 p2) 
        p3) 
    |c `elem` gammaG =
        let (gamma, gamma') = (filter ((/=) c) gammaG ,gammaD) in
        TensorRule a (gamma++delta) b gamma' 
            (CutRule c (a:gamma) cOrtho delta p1 p3)
            p2 
    |c `elem` gammaD =
        let (gamma,gamma') = (gammaG, filter ((/=) c) gammaD) in
        TensorRule a gamma b (gamma'++delta)
            p1
            (CutRule c (b:gamma') cOrtho delta p2 p3) 
    | otherwise = 
        error "Invalid proof"
applyLeftComm (CutRule c gammaCut cOrtho delta
        (BotRule gamma p1)
        p2) =
    BotRule (gamma++delta) (CutRule c gamma cOrtho delta p1 p2)
applyLeftComm (CutRule c gammaCut cOrtho delta 
                (WithRule a b gammaWith p1 p2) 
                p3) =
    let gamma = filter ((/=) c) gammaWith in
    WithRule a b (gamma++delta)
        (CutRule c (a:gamma) cOrtho delta p1 p3)
        (CutRule c (b:gamma) cOrtho delta p2 p3)
applyLeftComm (CutRule c gammaCut cOrtho delta (TopRule gammaTop) p) =
    let gamma = filter ((/=) c) gammaTop in
    TopRule (gamma++delta)
applyLeftComm (CutRule c gammaCut cOrtho delta
        (PlusRRule a b gammaPlus p1)
        p2) =
    let gamma = filter ((/=) c) gammaPlus in
        PlusRRule a b (gamma++delta) 
            (CutRule c (a:gamma) cOrtho delta p1 p2)
applyLeftComm (CutRule c gammaCut cOrtho delta
        (PlusLRule a b gammaPlus p1)
        p2) =
    let gamma = filter ((/=) c) gammaPlus in
        PlusLRule a b (gamma++delta) 
            (CutRule c (b:gamma) cOrtho delta p1 p2)
applyLeftComm (CutRule c gamma cOrtho deltaCut
        p1 
        (PlusLRule a b deltaPlus p2)) =
    let delta = filter ((/=) cOrtho) deltaPlus in
        PlusLRule a b (gamma++delta)
            (CutRule c gamma cOrtho (b:delta) p1 p2)
applyLeftComm (CutRule cWN gammaCut cOrthoOC wndelta 
                (PromRule a gammaProm p1)
                (PromRule cOrtho delta p2))
        | OfCourse cOrtho == cOrthoOC  =
            let gamma = (filter ((/=) cWN) gammaProm) in
            PromRule a (gamma++delta) 
                (CutRule cWN (a:gamma) cOrthoOC delta
                    p1
                    (PromRule cOrtho wndelta p2))
        | otherwise = error "Not a OfCourse commutation case"
applyLeftComm (CutRule c gammaCut cOrtho delta
                (DerRule a gammaWN p1)
                p2) =
    let gamma = filter ((/=) c) gamma in
        DerRule a (gamma++delta)
            (CutRule c (a:gamma) cOrtho delta p1 p2)
applyLeftComm (CutRule c gammaCut cOrtho delta
                (ContrRule a gammaContr p1)
                p2) =
    let gamma = (filter ((/=) c) gammaContr) in
    ContrRule a (gamma++delta) 
        (CutRule c ((WhyNot a) : (WhyNot a) : gamma) cOrtho delta p1 p2)
applyLeftComm (CutRule c gammaCut cOrtho delta
                (AffRule a gammaAff p1)
                p2) =
    let gamma = filter ((/=)c) gammaAff in
    AffRule a (gamma++delta) 
        (CutRule c gamma cOrtho delta p1 p2)




applyRightComm :: Proof -> Proof
applyRightComm (CutRule f gamma fOrtho deltaCut
                p1
                (ParrRule a b deltaParr p2))=
    let delta = filter ((/=) fOrtho) deltaParr in
        ParrRule a b (gamma++delta)
            (CutRule f gamma fOrtho (a:b:delta) p1 p2) 
applyRightComm (CutRule c gamma cOrtho deltaCut
        (p1)
        (TensorRule a deltaG b deltaD p2 p3))
    |cOrtho `elem` deltaG =
        let (delta, delta') = (filter ((/=) cOrtho) deltaG, deltaD) in
        (TensorRule a (gamma++delta) b delta' 
            (CutRule c gamma cOrtho (a:delta) p1 p2)
            p3)
    |cOrtho `elem` deltaD =
        let (delta,delta') = (deltaG, filter ((/=) cOrtho) deltaD) in
        TensorRule a delta b (gamma++delta')
            p2
            (CutRule c gamma cOrtho (b:delta') p1 p3)
    |otherwise = 
        error "Invalid Proof"
applyRightComm (CutRule c gamma cOrtho deltaCut
        p1 
        (BotRule deltaBot p2)) =
    let delta = (filter (/= cOrtho) deltaBot) in
    BotRule (gamma++delta) (CutRule c gamma cOrtho delta p1 p2)
applyRightComm (CutRule c gamma cOrtho deltaCut
                p1
                (WithRule a b deltaWith p2 p3)) =
    let delta = filter ((/=) cOrtho) deltaWith in
        (WithRule a b (gamma++delta)
            (CutRule c gamma cOrtho (a:delta) p1 p2) 
            (CutRule c gamma cOrtho (b:delta) p1 p3))
applyRightComm (CutRule c gamma cOrtho deltaCut p (TopRule deltaTop)) =
    let delta = filter ((/=) cOrtho) deltaTop in
        TopRule (gamma++delta)
applyRightComm (CutRule c gamma cOrtho deltaCut
                p1
                (PlusRRule a b deltaPlus p2)) =
    let delta = filter ((/=) cOrtho ) deltaPlus in
        (PlusRRule a b (gamma++delta) 
            (CutRule c gamma cOrtho (a:delta) p1 p2))
applyRightComm (CutRule c gamma cOrtho deltaCut
                p1 
                (PlusLRule a b deltaPlus p2)) =
    let delta = filter ((/=) cOrtho) deltaPlus in
        (PlusLRule a b (gamma++delta)
            (CutRule c gamma cOrtho (b:delta) p1 p2))
applyRightComm (CutRule cOC gammaWN cOrthonWN deltaCut
                (PromRule c gammaWNProm p1)
                (PromRule a deltaWNProm p2))
        |cOC == OfCourse c =
            let deltaWN = filter ((/=)cOrthonWN) deltaWNProm in
            PromRule a (gammaWN++deltaWN) 
                (CutRule cOC gammaWN cOrthonWN (a:deltaWN) 
                    (PromRule c gammaWN p1)
                    p2)
        |otherwise = error "Not a OfCourse commutation case"
applyRightComm (CutRule c gamma cOrtho deltaCut 
                p1
                (DerRule a deltaDer p2)) =
    let delta = (filter ((/=) cOrtho) deltaDer) in
    DerRule a (gamma++delta) 
        (CutRule c gamma cOrtho (a:delta) p1 p2)
applyRightComm (CutRule c gamma cOrtho deltaCut
                p1
                (ContrRule a deltaContr p2)) =
    let delta = filter ((/=) cOrtho) deltaContr in
        ContrRule a (gamma++delta)
            (CutRule c gamma cOrtho delta p1 p2)
applyRightComm (CutRule c gamma cOrtho deltaCut
                p1
                (AffRule a deltaAff p2)) =
    let delta = filter ((/=)cOrtho) deltaAff in
    AffRule a (gamma++delta)
        (CutRule c gamma cOrtho delta p1 p2)
    







elimCut :: Proof -> Proof
elimCut p
    | isRedex p = 
        let (CutRule f gamma fOrtho delta p1 p2) = p in
        let p1' = elimCut p1 in
        let p2' = elimCut p2 in
        elimCut (applyRedex (CutRule f gamma fOrtho delta p1' p2'))
    | isCutRooted p =
        if (isLeftChildCutRooted p) then        -- Eliminate children's CutRule before
            let CutRule f gam fO del p1 p2 = p in
            let p1' = elimCut p1 in
                elimCut (CutRule f gam fO del p1' p2)
        else if (isRightChildCutRooted p) then
            let CutRule f gam fO del p1 p2 = p in
            let p2' = elimCut p2 in
                elimCut (CutRule f gam fO del p1 p2')
        else let p' = applyComm p in elimCut p'
    | otherwise = case p of                     --Gofurther in the Proof to find a CutRule (or the end of the Proof)
        (TensorRule f gamma g delta p1 p2) ->
            let p1' = elimCut p1 in
            let p2' = elimCut p2 in
            (TensorRule f gamma g delta p1' p2')
        (ParrRule f g gamma p1) ->
            let p1' = elimCut p1 in
                (ParrRule f g gamma p1')
        (BotRule gamma p1) ->
            let p1' = elimCut p1 in
            (BotRule gamma p1')
        (PlusRRule f g gamma p1) ->
            let p1' = elimCut p1 in
            (PlusRRule f g gamma p1')
        (PlusLRule f g gamma p1) ->
            let p1' = elimCut p1 in
            (PlusLRule f g gamma p1')
        (WithRule f g gamma p1 p2) ->
            let p1' = elimCut p1 in
            let p2' = elimCut p2 in
            (WithRule f g gamma p1' p2')
        (PromRule f gamma p1) ->
            let p1' = elimCut p1 in
            (PromRule f gamma p1')
        (DerRule f gamma p1) ->
            let p1' = elimCut p1 in
            (DerRule f gamma p1')
        (AffRule f gamma p1) ->
            let p1' = elimCut p1 in
            (AffRule f gamma p1')
        (ContrRule f gamma p1) ->
            let p1' = elimCut p1 in
            (ContrRule f gamma p1')
        p -> p  --Cas Axiomes
