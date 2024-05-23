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