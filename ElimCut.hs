
import KSequent

applyRedex :: Preuve -> Preuve     -- reduit p qui commence par un redex (rien sinon)
applyRedex p = case p of
    CutRule _ _ _ _ (AxRule _ _) p2 -> p2
    CutRule _ _ _ _ p1 (AxRule _ _) -> p1
    CutRule  fcut fOthoCut gammaCut deltaCut
        (TensorRule fTen gTen gamma1 gamma2 pTen1 pTen2 )
        (ParrRule fParr gParr delta pParr)
    -> CutRule()
    ....