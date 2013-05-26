{-# LANGUAGE TemplateHaskell, RankNTypes #-}
module Template where

import Language.Haskell.TH
import Language.Haskell.TH.ExpandSyns (expandSyns)
import Control.Applicative ((<*>),pure)
import Control.Monad
import Data.Traversable (traverse, Traversable)
import Text.PrettyPrint.HughesPJ

generateGenericTraversal gadt = do
     TyConI (DataD _ typeName _ cs _) <- reify gadt
     [e| \expr use -> $(let matchFor (ForallC [] _ ty) = matchFor ty -- We have to strip off at least one all-quantifier.
                            matchFor (NormalC name tys) = do
                              let handle ty = case ty of
                                                (_, AppT (ConT typeName') _) | typeName == typeName' ->
                                                   [e|use|]
                                                (_, AppT outer_ty (AppT (ConT typeName') _)) | typeName == typeName' -> do
                                                   True <- isInstance ''Traversable [outer_ty]
                                                   [e|traverse|] `appE` [e|use|] -- Getting around some wierd type checking error with [e| traverse use |]
                                                _ ->
                                                   [e|pure|]
                              let xs  = [mkName ('x':show i) | i <- [1..length tys]]
                              let lhs = conP name $ map varP xs
                                  rhs = foldl (\exprQ (x,ty) -> [e| $(exprQ) <*> $(handle ty) $(varE x) |])
                                              ([e|pure|] `appE` conE name)
                                              (zip xs tys)
                              match lhs (normalB rhs) []
                        in caseE [e|expr|] (map matchFor cs) ) |]

{-
g ::            Applicative c =>
                Expr t ->
                (forall s. Expr s -> c (Expr s)) ->
                c (Expr t)
g expr use =
    case expr of
        RelatedByL r1 r2 r3    -> pure RelatedByL      <*> use  r1 <*> use  r2 <*> use  r3
        ImplL      l1 l2       -> pure ImplL           <*> use  l1 <*> use  l2
        AndL       l1 l2       -> pure AndL            <*> use  l1 <*> use  l2
        ForAllL    v  l        -> pure ForAllL         <*> pure v  <*> use  l
        BottomL                -> pure BottomL
        TopL                   -> pure TopL
        RespectsL  r c         -> pure RespectsL       <*> use r   <*> pure c

        VarR       v           -> pure VarR            <*> pure v
        LiftR      c  rs       -> pure LiftR           <*> pure c  <*> sequenceA (map use rs)
        FunR       r1 r2       -> pure FunR            <*> use  r1 <*> use  r2
        ProductR   r1 r2       -> pure ProductR        <*> use  r1 <*> use  r2
        ForAllR    v  r        -> pure ForAllR         <*> pure v  <*> use  r
        AppR       r1 r2       -> pure AppR            <*> use  r1 <*> use  r2
        CompR      r1 r2       -> pure CompR           <*> use  r1 <*> use  r2
        InstantiatedToR  r1 r2 -> pure InstantiatedToR <*> use  r1 <*> use  r2
        DomainR    r           -> pure DomainR         <*> use  r
        CoDomainR  r           -> pure CoDomainR       <*> use  r
        IdR                    -> pure IdR
        EmptyR                 -> pure EmptyR
        MemberR                -> pure MemberR
        RelationsR ps          -> pure RelationsR      <*> pure ps
        ConstraintR  c  v  r   -> pure ConstraintR     <*> pure c  <*> pure v  <*> use r
        SetR         r1 r2 l   -> pure SetR            <*> use  r1 <*> use  r2 <*> use l
        UnionR       r1 r2     -> pure UnionR          <*> use  r1 <*> use  r2

        TypeVar         v      -> pure TypeVar         <*> pure v
        TypeConst       v      -> pure TypeConst       <*> pure v
        TypeApp         c  ts  -> pure TypeApp         <*> pure c  <*> sequenceA (map use ts)
        Function        t1 t2  -> pure Function        <*> use  t1 <*> use  t2
        ProductType     t1 t2  -> pure ProductType     <*> use  t1 <*> use  t2
        ListType        t      -> pure ListType        <*> use  t
        ForAllType      v  t   -> pure ForAllType      <*> pure v  <*> use  t
        Constraint   c  v  t   -> pure Constraint      <*> pure c  <*> pure v  <*> use t    
-}


generatePrettyPrinter gadt = do
     TyConI (DataD _ typeName _ cs _) <- reify gadt
     [e| let pp :: $(conT typeName) t -> Doc; pp expr =
                  parens $(let matchFor (ForallC [] _ ty) = matchFor ty -- We have to strip off at least one all-quantifier.
                               matchFor (NormalC name tys) = do
                                          let handle ty = case ty of
                                                            (_, AppT (ConT typeName') _) | typeName == typeName' ->
                                                               [e|pp|]
                                                            (_, AppT outer_ty (AppT (ConT typeName') _)) | typeName == typeName' -> do
                                                               True <- isInstance ''Traversable [outer_ty]
                                                               [e|hsep . map pp|]
                                                            _ ->
                                                               [e|text.show|]
                                          let xs  = [mkName ('x':show i) | i <- [1..length tys]]
                                          let lhs = conP name $ map varP xs
                                              rhs = [e| $([e|text|] `appE` stringE (nameBase name)) <+> $(
                                                      foldr (\(x,ty) exprQ -> [e| $(handle ty) $(varE x) $$ $(exprQ) |])
                                                            [e|empty|]
                                                            (zip xs tys)) |]
                                          match lhs (normalB rhs) []
                                    in caseE [e|expr|] (map matchFor cs) ) in pp|]

generateTeXPrettyPrinter gadt = do
     TyConI (DataD _ typeName _ cs _) <- reify gadt
     [e| let pp :: $(conT typeName) t -> Doc; pp expr =
                  $(let matchFor (ForallC [] _ ty) = matchFor ty -- We have to strip off at least one all-quantifier.
                        matchFor (NormalC name tys) = do
                          let handle s_ty = case s_ty of
                                            (_, AppT (ConT typeName') _) | typeName == typeName' ->
                                               [e|braces . pp|]
                                            (_, AppT outer_ty (AppT (ConT typeName') _)) | typeName == typeName' -> do
                                               True <- isInstance ''Traversable [outer_ty]
                                               [e|braces . hsep . map (braces . pp)|]
                                            (_, ty1) -> do
                                               ty1' <- expandSyns ty1
                                               ty2  <- [t| [Char] |]
                                               if ty1' == ty2
                                                  then [e|braces . text|]
                                                  else [e|braces . text . show|]
                          let xs  = [mkName ('x':show i) | i <- [1..length tys]]
                          let lhs = conP name $ map varP xs
                              rhs = [e| $([e|text.('\\':)|] `appE` stringE (nameBase name)) <+> $(
                                      foldr (\(x,ty) exprQ -> [e| $(handle ty) $(varE x) $$ $(exprQ) |])
                                            [e|empty|]
                                            (zip xs tys)) |]
                          match lhs (normalB rhs) []
                    in caseE [e|expr|] (map matchFor cs) ) in pp|]

generateJSONPrettyPrinter gadt = do
     TyConI (DataD _ typeName _ cs _) <- reify gadt
     [e| let pp :: $(conT typeName) t -> Doc; pp expr =
                         $(let matchFor (ForallC [] _ ty) = matchFor ty -- We have to strip off at least one all-quantifier.
                               matchFor (NormalC name tys) = do
                                          let handle ty = case ty of
                                                            (_, AppT (ConT typeName') _) | typeName == typeName' ->
                                                               [e|pp|]
                                                            (_, AppT outer_ty (AppT (ConT typeName') _)) | typeName == typeName' -> do
                                                               True <- isInstance ''Traversable [outer_ty]
                                                               [e|hsep . map pp|]
                                                            _ ->
                                                               [e|text.show|]
                                          let xs  = [mkName ('x':show i) | i <- [1..length tys]]
                                          let lhs = conP name $ map varP xs
                                              rhs = [e| text "[\"" <> $([e|text|] `appE` stringE (nameBase name)) <> text "\"" <> $(
                                                      foldr (\(x,ty) exprQ -> [e| text "," <+> $(handle ty) $(varE x) <> $(exprQ) |])
                                                            [e|empty|]
                                                            (zip xs tys)) <> text "]" |]
                                          match lhs (normalB rhs) []
                                    in caseE [e|expr|] (map matchFor cs) ) in pp|]
