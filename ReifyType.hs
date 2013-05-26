{-# LANGUAGE ViewPatterns #-}
module ReifyType (typeOf) where

import Language.Haskell.TH
import Language.Haskell.TH.Syntax

import Data.List

-- ghci> $(typeOf "reverse") == "∀a. ([a] -> [a])"
-- True

typeOf :: String -> Q Exp
typeOf name = do
    (VarI _ ty _ _) <- reify (mkName name)
    stringE (toS ty)

toS ty =
  case ty of
    ForallT tyVarBndrs cxt ty' -> concatMap ((\a -> "∀" ++ a ++ ". ") . getName) tyVarBndrs ++ concatMap showPred cxt ++ toS ty'
    VarT name                  -> niceName name
    ConT name                  -> niceName name
    TupleT int                 -> "Tuple" ++ show int
    ArrowT                     -> "(->)"
    ListT                      -> "[]"
    AppT ArrowT ty'            -> toS ty' ++ " ->"
    AppT ListT ty'
                               -> "[" ++ toS ty' ++ "]"
    (matchTupleT -> Just tys)  -> "(" ++ intercalate "," (map toS tys) ++ ")"
    AppT ty' ty''              -> "(" ++ toS ty' ++ " " ++ toS ty'' ++ ")"
    SigT ty' kind              -> "?" -- FIXME

showPred (ClassP name tys) = intercalate " " (niceName name : map toS tys) ++  " => "
showPred (EqualP ty1 ty2)  = "?" -- FIXME


getName (PlainTV name)    = niceName name
getName (KindedTV name _) = niceName name

niceName (Name (OccName n) _) = n

matchTupleT = go 0 []
 where go n tys (TupleT m) | n == m = Just tys
       go n tys (AppT ty ty')       = go (succ n) (ty':tys) ty
       go _ _   _                   = Nothing
