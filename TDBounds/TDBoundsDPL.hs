{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE BlockArguments #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use :" #-}



import Prelude hiding ((*), (!))
import LambdaCalc
import TDBoundsPretty ( showParse, showParse', prettyProof , outTrees', withDens, withoutDens)
import TDBoundsCFG
import Data.Maybe ( fromMaybe )


demoLex :: Lexicon
demoLex = map mkLex
  [ ("x"            , [( Nothing, Var  , effB E                                  )] ++
                      [( Nothing, Var  , V                                       )])
  , ("x2"           , [( Nothing, Var  , effR G (effR I (effW T E))              )] ++
                      [( Nothing, Var  , V                                       )])
  , ("lower"        , [( Nothing, Op   , effB (effR I T) :->
                                         effB T              )])
  , ("left"         , [( Nothing, Pred1, effR I (E :-> T)                        )])
  , ("left2"        , [( Nothing, Pred1, effR I (E :-> T)                        )])
  , ("bathroom"     , [( Nothing, Pred1, effR I (E :-> T)                        )])
  , ("bathroom2"    , [( Nothing, Pred1, effR (Tpl G I) (E :-> T)                )])
  , ("groundfloor"  , [( Nothing, Pred1, effR I (E :-> T)                        )])
  , ("not"          , [( Nothing, Conn3, T :-> T                                 )])
  -- , ("and"          , [( Nothing, Conn2, T :-> T :-> T                           )])
  , ("and"          , [( Nothing, Conn2, effB T :-> effB T :-> effB T            )])
  , ("bexists"      , [( Nothing, Q    , V :-> effB T :->
                                         effB T              )])
  , ("bexists2"     , [( Nothing, Q    , V :-> effR G (effR I (effW T T)) :->
                                         effR G (effR I (effW T T))              )])
  , ("pfoc"         , [( Nothing, Op   , effR I (E :-> T) :->
                                         effC (effB T) 
                                              (effB T) 
                                              (effR I (E :-> T))                 )])
  , ("pfoc2"        , [( Nothing, Op   , effR I (E :-> T) :->
                                         effC (effR G (effR I (effW T T))) 
                                              (effR G (effR I (effW T T)))
                                              (effR I (E :-> T))                 )])
  , ("true1"         , [(Nothing,  Prop , effR (Tpl G I) (effW T T))])
  , ("true2"         , [(Nothing, Prop, T)])

  ]
  where
    first  (a,s,t) f = (f a, s, t)
    second (s , a) f = (s , f s a)
    mkLex w = second w $ \s -> map (`first` fromMaybe (make_con s))
  --   idTerm = let a = make_var "a" in a ! a
  --   pushTerm = let x = make_var "x" in x ! (x * x)

  --   ann = make_con "a"
  --   mary = make_con "m"
  --   x2 = let g = make_var "g" in g ! (g % make_con "x") % make_con "$\\neq$" % make_con "\\#" * (g % make_con "x")
  --   left = let w = make_var "w" in w ! (make_con "left" % w)
  --   bexists =
  --       let v = make_var "v" in
  --       let p = make_var "p" in
  --       let a = make_var "a" in
  --       let g = make_var "g" in
  --           v ! p ! g !
  --               ( ((make_con "$\\exists$" % a) % _2 (p % (g % make_con "[" % v % make_con "$\\rightarrow$" % a % make_con "]")) ) % make_con "$\\Rightarrow$" % _2 (p % g)) *
  --               ((make_con "$\\exists$" % a )% _2 (p % (g % make_con "[" % v % make_con "$\\rightarrow$" % a % make_con "]")))

-- a toy Context-Free Grammar
demoCFG :: CFG
demoCFG = curry \case
  (Pred1, Var  ) -> [Prop]
  (Conn2, Prop ) -> [Conn1]
  (Prop , Conn1) -> [Prop]
  (Q    , Var  ) -> [Conn3]
  (Conn3, Prop ) -> [Prop]
  (Op   , Prop ) -> [Prop]
  (Op   , Pred1) -> [Pred1]
  (_    , _    ) -> []






{- Test cases -}

s1 = "left2 x2"
t1 = effR (Tpl G I) (effW T T)
t1alt = effR G (effR I (effW T T))

s1simple = "left x"
t1simple = effB (effR I T)


s2 = "bexists x"
t2 = effR (Tpl G I) (effW T T) :-> effR (Tpl G I) (effW T T)

s3 = "lower left x"
t3 = effB T



s4 = "bexists2 x2 left2 x2"
t4 = effR G (effR I (effW T T))

s5 = "pfoc2 left2"
t5 = effC (effR (Tpl G I) (effW T T)) (effR (Tpl G I) (effW T T)) (effR I (E :-> T))
t5alt = effC (effR G (effR I (effW T T))) (effR G (effR I (effW T T))) (effR I (E :-> T))

s6 = "pfoc2 left2 x2"
t6 = effC (effR (Tpl G I) (effW T T)) (effR (Tpl G I) (effW T T)) (effR (Tpl G I) (effW T (effR I T)))
t6alt = effC (effR G (effR I (effW T T))) (effR G (effR I (effW T T))) (effR G (effR I (effW T T)))
t6alt2 = effR G (effR I (effW T T))


s7 = "lower pfoc left x"
t7 = effC (effR (Tpl G I) (effW T T)) (effR (Tpl G I) (effW T T)) (effR (Tpl G I) (effW T T))
t7alt = effR (Tpl G I) (effW T T)

s8 = "bexists x lower pfoc left x"
t8 = effC (effB T) (effB T) (effB T)
t8alt = effB T
-- t8alt = effR (Tpl G I) (effW T T)

s9 = "not bexists2 x2 pfoc2 left2 x2"
t9 = effR G (effR I (effW T T))
t9alt = effC (effR (Tpl G I) (effW T T)) (effR (Tpl G I) (effW T T)) (effR (Tpl G I) (effW T T))

s9simple = "not bexists x lower pfoc bathroom x"
t9simple = effB T

s10 = "lower bathroom x and lower bathroom x"
t10 = effB T

s11 = "not bexists x lower bathroom x and lower pfoc bathroom x"
t11 = effB T

s12 = "bathroom2 x"
t12 = effR (Tpl G I) (effW T T)

{- Testing helper function -}

main :: IO ()
-- main = mapM_ putStrLn ps --  ++ qs
main = outTrees' withoutDens demoCFG demoLex (hasType t11) s11
  where
    ps = [s10] >>= fromMaybe ["No parse"] . showParse demoCFG demoLex
    -- qs = fromMaybe ["No parse"] $ showParse' demoCFG demoLex (hasType T) prettyProof s6

