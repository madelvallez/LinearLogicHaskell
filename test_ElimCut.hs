import ElimCut
import LogLin
import KSequent1
a::LL 
a = Var "A"
b::LL
b = Var "B"
c::LL
c=Var "C"

pcom1::Preuve   --Comm gauche Parr / Redex Ax
pcom1 = CutRule (Tensor (Not a) (Not b)) [Parr a b] (Parr a b) [Tensor (Not a) (Not b)]
            (ParrRule a b [Tensor (Not a) (Not b)]
                (TensorRule (Not a) [a] (Not b) [b]
                    (AxRule a (Not a))
                    (AxRule b (Not b))))
            (AxRule (Parr a b) (Tensor (Not a) (Not b)))

pcom1'::Preuve   --Comm droite Parr / Redex Ax
pcom1' = CutRule (Parr a b) [Tensor (Not a) (Not b)] (Tensor (Not a) (Not b)) [Parr a b]
            (AxRule (Parr a b) (Tensor (Not a) (Not b)))
            (ParrRule a b [Tensor (Not a) (Not b)]
                (TensorRule (Not a) [a] (Not b) [b]
                    (AxRule a (Not a))
                    (AxRule b (Not b))))

pcom1''::Preuve   --Comm droite Parr / Redex Ax
pcom1'' = CutRule (Tensor (Not a) (Not b)) [Parr a b] (Parr a b) [Tensor (Not a) (Not b)] 
            (AxRule (Parr a b) (Tensor (Not a) (Not b)))
            (ParrRule a b [Tensor (Not a) (Not b)]
                (TensorRule (Not a) [a] (Not b) [b]
                    (AxRule a (Not a))
                    (AxRule b (Not b))))

pcom2 :: Preuve         -- Comm G Bot / Redex Ax
pcom2 = CutRule (Parr a (Not a)) [Bot] (Tensor (Not a) a) [Parr a (Not a)]
            (BotRule [Parr a (Not a)]
                (ParrRule a (Not a) []
                    (AxRule a (Not a))))
            (AxRule (Parr a (Not a)) (Tensor (Not a) a))

pcom2' :: Preuve        -- Comm D Bot / Redex Ax
pcom2' = CutRule (Tensor (Not a) a) [Parr a (Not a)]  (Parr a (Not a)) [Bot]
            (AxRule (Parr a (Not a)) (Tensor (Not a) a))
            (BotRule [Parr a (Not a)]
                (ParrRule a (Not a) []
                    (AxRule a (Not a))))

pcom3::Preuve       --CommG Tensor G /puis Redex Un
pcom3 = CutRule Bot [Tensor (Not a) (Not b), a, b] Un []
            (TensorRule (Not a) [a, Bot] (Not b) [b]
                (BotRule [Not a, a]
                    (AxRule (Not a) a ))
                (AxRule (Not b) b ))
            AxUn

pcom3'::Preuve       --CommG Tensor D /puis Redex Un
pcom3' = CutRule Bot [Tensor a b, (Not a), (Not b)] Un []
            (TensorRule a [Not a] b [Not b, Bot]
                (AxRule a (Not a))
                (BotRule [b, Not b]
                    (AxRule  b (Not b))))
            AxUn
            
pcom3''::Preuve         --CommD Tensor G /puis Redex Un
pcom3'' = CutRule Un [] Bot [Tensor (Not a) (Not b), a, b] 
            AxUn
            (TensorRule (Not a) [a, Bot] (Not b) [b]
                (BotRule [Not a, a]
                    (AxRule (Not a) a ))
                (AxRule (Not b) b)) 
            
pcom3'''::Preuve        --CommD Ttensor D /puis redex Un
pcom3''' = CutRule Un [] Bot [Tensor a b, (Not a), (Not b)]  
            AxUn
            (TensorRule a [Not a] b [Not b, Bot]
                (AxRule a (Not a))
                (BotRule [b, Not b]
                    (AxRule  b (Not b))))
            
pcom4::Preuve       --Comm G With / redex Ax
pcom4 = CutRule c [With (WhyNot a) (WhyNot b), Not c] (Not c) [c]
            (WithRule (WhyNot a) (WhyNot b) [c, Not c]
                (AffRule a [c, Not c]
                    (AxRule c (Not c)))
                (AffRule b [c, Not c]
                    (AxRule c (Not c))))
            (AxRule c (Not c))

pcom4'::Preuve
pcom4' = CutRule (Not c) [c] c [With (WhyNot a) (WhyNot b), Not c] 
            (AxRule c (Not c))
            (WithRule (WhyNot a) (WhyNot b) [c, Not c]
                (AffRule a [c, Not c]
                    (AxRule c (Not c)))
                (AffRule b [c, Not c]
                    (AxRule c (Not c))))
            
pcomplus::Preuve        --Comm G Bot/ (Comm D Parr /puis redex Ten)
pcomplus = CutRule (Tensor (Not a) a) [Parr a (Not a)] (Parr a (Not a)) [Bot]
            (ParrRule a (Not a) [Tensor (Not a) a]
                (TensorRule (Not a) [a] a [Not a]
                    (AxRule a (Not a))
                    (AxRule a (Not a))))
            (BotRule [Parr a (Not a)]
                (ParrRule a (Not a) []
                    (AxRule a (Not a))))

pred1 :: Preuve
pred1 = CutRule (With (WhyNot a) (WhyNot b)) [c, Not c] (Plus (OfCourse (Not a)) (OfCourse (Not b))) [WhyNot a]
            pcom4
            (PlusDRule (OfCourse (Not a)) (OfCourse (Not b)) [WhyNot a]
                (PromRule (Not a) [WhyNot a]
                    (DerRule a [Not a]
                        (AxRule a (Not a)))))

f :: LL
f= Tensor (Tensor (Not a) a) (Parr (Not a) a)
fOrtho :: LL
fOrtho = Parr (Parr a (Not a)) (Tensor a (Not a))
pred2 :: Preuve
pred2 = CutRule f [Parr a (Not a)] fOrtho []
            (TensorRule (Tensor (Not a) a) [Parr a (Not a)] (Parr (Not a) a) []
                (AxRule (Parr a (Not a)) (Tensor (Not a) a))
                (ParrRule (Not a) a []
                    (AxRule a (Not a))))
            (ParrRule (Parr a (Not a)) (Tensor a (Not a)) []
                (ParrRule a (Not a) [Tensor a (Not a)]
                    (TensorRule a [Not a] (Not a) [a]
                        (AxRule a (Not a))
                        (AxRule a (Not a)))))

pred3 :: Preuve
pred3 = CutRule (OfCourse a) [WhyNot (Not a)] (WhyNot (Not a)) [OfCourse c, WhyNot (Not c)]
            (PromRule a [WhyNot (Not a)]
                (DerRule (Not a) [a]
                    (AxRule a (Not a))))
            (PromRule c [WhyNot (Not a), WhyNot (Not c)]
                (AffRule (Not a) [c, WhyNot (Not c)]
                    (DerRule (Not c) [c]
                    (AxRule c (Not c)))))

pred4 :: Preuve
pred4 = CutRule (OfCourse (Not a)) [WhyNot a] (WhyNot a) [Not a]
        (PromRule (Not a) [WhyNot a]
            (DerRule a [Not a]
                (AxRule a (Not a))))
        (ContrRule a [Not a]
            (AffRule a [ WhyNot a,Not a]
                (DerRule a [Not a]
                    (AxRule a (Not a)))))

pred5 :: Preuve
pred5 = CutRule (WhyNot (Not a)) [OfCourse c, WhyNot (Not c)] (OfCourse a) [Plus (WhyNot (Not a)) b]
            (PromRule c [WhyNot (Not a), WhyNot (Not c)]
                (AffRule (Not a) [c, WhyNot (Not c)]
                    (DerRule (Not c) [c]
                        (AxRule c (Not c)))))
            (PlusDRule (WhyNot (Not a)) b [OfCourse a]
                (PromRule a [WhyNot (Not a)]
                    (DerRule (Not a) [a]
                        (AxRule a (Not a)))))

main = 
    if not (isValidProof (elimCut pcom1)) then
        error "isValidProof (elimCut pcom1) == False"
    else if not (isValidProof (elimCut pcom1')) then
        error "isValidProof (elimCut pcom1') == False"
    else if not (isValidProof (elimCut pcom1'')) then
        error "isValidProof (elimCut pcom1'') == False"
    else if not (isValidProof (elimCut pcom2)) then
        error "isValidProof (elimCut pcom2) == False"
    else if not (isValidProof (elimCut pcom2')) then
        error "isValidProof (elimCut pcom2') == False"
    else if not (isValidProof (elimCut pcom3)) then
        error "isValidProof (elimCut pcom3) == False"
    else if not (isValidProof (elimCut pcom3')) then
        error "isValidProof (elimCut pcom3') == False"
    else if not (isValidProof (elimCut pcom3'')) then
        error "isValidProof (elimCut pcom3'') == False"
    else if not (isValidProof (elimCut pcom3''')) then
        error "isValidProof (elimCut pcom3''') == False"
    else if not (isValidProof (elimCut pcom4)) then
        error "isValidProof (elimCut pcom4) == False"
    else if not (isValidProof (elimCut pcom4')) then
        error "isValidProof (elimCut pcom4') == False"
    else if not (isValidProof (elimCut pcomplus)) then
        error "isValidProof (elimCut pcomplus) == False"
    else if not (isValidProof (elimCut pred1)) then
        error "isValidProof (elimCut pred1) == False"
    else if  not (isValidProof (elimCut pred2)) then
        error "isValidProof (elimCut pred2) == False"
    else if not (isValidProof (elimCut pred3)) then
        error "isValidProof (elimCut pred3) == False"
    else if  not (isValidProof (elimCut pred4)) then
        error "isValidProof (elimCut pred4) == False"
    else if  not (isValidProof (elimCut pred5)) then
        error "isValidProof (elimCut pred5) == False"
    else 
        print "Tests OK"