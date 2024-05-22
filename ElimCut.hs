
import LogLin
import KSequent1

applyRedex :: Preuve -> Preuve     -- reduit p qui commence par un redex (rien sinon)
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
        (PlusDRule fPlus gPlus gammaPlus p1)
        (WithRule fWith gWith deltaWith p2 p3)
        -> CutRule fPlus gammaPlus fWith deltaWith p1 p2

    CutRule f gamma fOrtho delta
        (WithRule a b gammaWith p1 p2)
        (PlusDRule aOrtho bOrtho deltaPlus p3)
        -> CutRule a gammaWith aOrtho deltaPlus p1 p3

    CutRule f gamma fOrtho delta 
        (PlusGRule fPlus gPlus gammaPlus p1)
        (WithRule fWith gWith deltaWith p2 p3)
        -> CutRule gPlus gammaPlus gWith deltaWith p1 p3

    CutRule f gamma fOrtho delta
        (WithRule a b gammaWith p1 p2)
        (PlusGRule aOrtho bOrtho deltaPlus p3)
        -> CutRule b gammaWith bOrtho deltaPlus p2 p3


