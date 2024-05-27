import LogLin
import KSequent1

getProduit :: Preuve -> Sequent     --revoie un sequent avec les formules introduites par la dernière règle appliquée
getProduit (AxRule a aOrtho) = Sequent [a, aOrtho]
getProduit AxUn = Sequent [Un]
getProduit (TopRule _) = Sequent [Top]
getProduit (CutRule _ _ _ _ _ _ ) = Sequent []
getProduit (TensorRule a _ b _ _ _ )= Sequent [Tensor a b]
getProduit (ParrRule a b _ _) = Sequent [Parr a b]
getProduit (BotRule _ _) = Sequent [Bot]
getProduit (PlusDRule a b _ _) = Sequent [Plus a b]
getProduit (PlusGRule a b _ _) = Sequent [Plus a b]
getProduit (WithRule a b _ _ _) = Sequent [With a b]
getProduit (PromRule a _ _) = Sequent [OfCourse a]
getProduit (DerRule a _ _) = Sequent [WhyNot a]
getProduit (AffRule a _ _) = Sequent [WhyNot a]
getProduit (ContrRule a _ _) = Sequent [WhyNot a]

isRedex ::Preuve -> Bool
isRedex (CutRule f _ fOrtho _ p1 p2) = (f `elem` (getProduit p1)) && (fOrtho `elem` (getProduit p2))
isRedex _ = False 

isCutRooted :: Preuve -> Bool
isCutRooted (CutRule _ _ _ _ _ _) = True
isCutRooted _ = False

elimCut :: Preuve -> Preuve
elimCut p
    | isRedex p = 
        let (CutRule f gamma fOrtho delta p1 p2) = p in
        let p1' = elimCut p1 in
        let p2' = elimCut p2 in
        elimCut (applyRedex (CutRule f gamma fOrtho delta p1' p2'))
    | isCutRooted p = 
        let p' = applyComm p in
        elimCut p'
    | otherwise = case p of
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
        (PlusDRule f g gamma p1) ->
            let p1' = elimCut p1 in
            (PlusDRule f g gamma p1')
        (PlusGRule f g gamma p1) ->
            let p1' = elimCut p1 in
            (PlusGRule f g gamma p1')
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





applyComm :: Preuve -> Preuve
applyComm (CutRule f gamma fOrtho delta p1 p2)
    | (getProduit p1) /= f =
        applyLeftComm (CutRule f gamma fOrtho delta p1 p2)
    | (getProduit p2) /= fOrtho =
        applyRightComm (CutRule f gamma fOrtho delta p1 p2)
    | otherwise =
        error "Not a commutation case"
applyComm _ = error "Not a commutation case"

applyLeftComm :: Preuve -> Preuve
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
        (PlusDRule a b gammaPlus p1)
        p2) =
    let gamma = filter ((/=) c) gammaPlus in
        PlusDRule a b (gamma++delta) 
            (CutRule c (a:gamma) cOrtho delta p1 p2)
applyLeftComm (CutRule c gammaCut cOrtho delta
        (PlusGRule a b gammaPlus p1)
        p2) =
    let gamma = filter ((/=) c) gammaPlus in
        PlusGRule a b (gamma++delta) 
            (CutRule c (b:gamma) cOrtho delta p1 p2)
applyLeftComm (CutRule c gamma cOrtho deltaCut
        p1 
        (PlusGRule a b deltaPlus p2)) =
    let delta = filter ((/=) cOrtho) deltaPlus in
        PlusGRule a b (gamma++delta)
            (CutRule c gamma cOrtho (b:delta) p1 p2)




applyRightComm :: Preuve -> Preuve
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
        let (delta,delta') = (deltaG, filter ((/=) c) deltaD) in
        TensorRule a delta b (gamma++delta')
            p2
            (CutRule c gamma cOrtho (b:delta') p1 p3)
    |otherwise = 
        error "Invalid Proof"
applyRightComm (CutRule c gamma cOrtho deltaCut
        p1 
        (BotRule delta p2)) =
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
                (PlusDRule a b deltaPlus p2)) =
    let delta = filter ((/=) c ) deltaPlus in
        (PlusDRule a b (gamma++delta) 
            (CutRule c gamma cOrtho (a:delta) p1 p2))
applyRightComm (CutRule c gamma cOrtho deltaCut
                p1 
                (PlusGRule a b deltaPlus p2)) =
    let delta = filter ((/=) cOrtho) deltaPlus in
        (PlusGRule a b (gamma++delta)
            (CutRule c gamma cOrtho (b:delta) p1 p2))


