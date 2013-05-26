{-# LANGUAGE GADTs, EmptyDataDecls, Rank2Types, StandaloneDeriving #-}
{-# LANGUAGE ImpredicativeTypes #-} -- deprecated, currently used for 'choiceList', 'rewrite', and 'rewriteEQ'
{-# LANGUAGE TypeSynonymInstances, FlexibleInstances #-} -- Used for the Show (Rewrite (Expr t)) instance
{-# LANGUAGE NoMonoLocalBinds #-} -- Needed to make the "case expr of" style of GADT matching possible in GHC7
{-# LANGUAGE TemplateHaskell #-} -- Generating definitions of traversals and pretty printers out of the GADT definition
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# OPTIONS_GHC
    -Wall
    -fno-warn-missing-signatures
    -fno-warn-unused-do-bind
    -fno-warn-type-defaults
    -fno-warn-name-shadowing
    -fno-warn-deprecated-flags
#-}
module Core where

{- TODO
 -
 - * Special handling of binary operators
 - * Sum and product types
 - * More helpful parser errors
 - * Error message propagation, e.g. from parseType to pc
 -}

{- Imports [[[ -}
import Prelude hiding (all, seq, repeat) -- Name clash with strategy combinators
import Control.Monad
import Control.Monad.State
import Control.Monad.Reader
import Control.Monad.Writer hiding ((<>))
import Control.Applicative hiding ((<|>))
--import Data.Traversable (sequenceA)
--import Data.Monoid

import Text.PrettyPrint.HughesPJ

import qualified Text.ParserCombinators.Parsec as Pc
import Text.ParserCombinators.Parsec ((<|>))
import Data.List (union, (\\), intercalate, nub)

import Template -- (generateGenericTraversal)

-- ]]]

{- Data types [[[ -}

{- A GADT is used to represent both relational and logical expressions.
 - This allows us to "unfold" the inital parametricity condition into
 - a theorem by using combinations of single step rewrite rules.
 -}

data Expr t where

    -- Logical expressions
    RelatedByL :: Expr Relational -> Expr Relational -> Expr Relational -> Expr Logical
    ImplL      :: Expr Logical -> Expr Logical -> Expr Logical
    AndL       :: Expr Logical -> Expr Logical -> Expr Logical
    ForAllL    :: VariableName -> Expr Logical -> Expr Logical
    BottomL    :: Expr Logical
    TopL       :: Expr Logical
    RespectsL  :: Model -> Expr Relational -> Constraint -> Expr Logical
    NotEqualL  :: Expr Relational -> Expr Relational -> Expr Logical

    -- Relational expressions
    VarR       :: VariableName -> Expr Relational
    LiftR      :: TypeConstructor -> [Expr Relational] -> Expr Relational
    LiftFixR   :: TypeConstructor -> [Expr Relational] -> Expr Relational
    FunR       :: Expr Relational -> Expr Relational -> Expr Relational
    FunSeqR    :: Expr Relational -> Expr Relational -> Expr Relational
    FunSeqIneqR:: Expr Relational -> Expr Relational -> Expr Relational
    ProductR   :: Expr Relational -> Expr Relational -> Expr Relational
    ForAllR    :: Properties -> VariableName -> Expr Relational -> Expr Relational
    --ForAllFixR :: VariableName -> Expr Relational -> Expr Relational
    --ForAllSeqR :: VariableName -> Expr Relational -> Expr Relational
    AppR       :: Expr Relational -> Expr Relational -> Expr Relational
    CompR      :: Expr Relational -> Expr Relational -> Expr Relational
    DomainR    :: Expr Relational -> Expr Relational
    CoDomainR  :: Expr Relational -> Expr Relational
    IdR        :: Expr Relational
    EmptyR     :: Expr Relational
    MemberR    :: Expr Relational
    BottomR    :: Expr Relational
    RelationsR :: Properties -> Expr Relational
    ConstraintR:: Model -> Constraint -> VariableName -> Expr Relational -> Expr Relational
    SetR       :: Expr Relational -> Expr Relational -> Expr Logical -> Expr Relational
    UnionR     :: Expr Relational -> Expr Relational -> Expr Relational
    NoMoreDefinedR :: Expr Relational

    InstantiatedToR :: Expr Relational -> Expr Relational -> Expr Relational

    -- Expressions representing Haskell types
    VarT        :: VariableName -> Expr Type
    ConstT      :: VariableName -> Expr Type
    AppT        :: TypeConstructor -> [Expr Type] -> Expr Type
    FunctionT   :: Expr Type -> Expr Type -> Expr Type
    ProductT    :: Expr Type -> Expr Type -> Expr Type
    ListT       :: Expr Type -> Expr Type
    ForAllT     :: VariableName -> Expr Type -> Expr Type
    ConstraintT :: Constraint -> VariableName -> Expr Type -> Expr Type


data Relational -- Phantom type
data Logical    -- Phantom type
data Type       -- Phantom type

type VariableName = String
type TypeConstructor = String

type Properties = [Property]

data Property = IsFunction
              | IsAdmissible
              | IsStrict
              | IsBottomReflecting
              | IsTotal
              | IsLeftClosed
    deriving (Show, Eq)

type Model = Expr Type -> Expr Relational -- The language model in form of a type-interpretation function

instance Show Model where
   show _ = "<model>"
instance Eq Model where
   (==) _ _ = True

type Constraint = String -- The name of a type class

instance Show (Expr t) where
    show = show . pp'
deriving instance Eq (Expr t) -- requires GHC 6.12

-- ]]]

-- Sample expression - The parametricity condition for functions on lists,
--                     e.g. reverse :: [a] -> [a]:
example_reverse =
    (RelatedByL (VarR "r")
                (VarR "r")
                (ForAllR [] "X" (FunR (LiftR "[]" [VarR "X"])
                                      (LiftR "[]" [VarR "X"]))))



type Rule m = forall t. Expr t -> RewriteT m (Expr t)

{- Rules (single-step) [[[ -}

{- Unfolding definitions [[[ -}

def_ForAllR :: MonadPlus m => Rule m
def_ForAllR (RelatedByL x y (ForAllR properties v r)) =
    rewriteEQ ("def_ForAllR", def_ForAllR)
              (ForAllL v
                (ImplL (RelatedByL (VarR v) (RelationsR properties) MemberR)
                       (RelatedByL (instantiatedToR x (DomainR   (VarR v)))
                                   (instantiatedToR y (CoDomainR (VarR v)))
                                   r)))
def_ForAllR _ = mzero

def_ConstraintR :: MonadPlus m => Rule m
def_ConstraintR (RelatedByL x y (ConstraintR m c v r)) =
    rewriteEQ ("def_ConstraintR", def_ConstraintR)
              (ImplL (RespectsL m (VarR v) c)
                     (RelatedByL x y r))
def_ConstraintR _ = mzero

--instantiatedToR = InstantiatedToR
instantiatedToR = const

def_FunR :: MonadPlus m => Rule m
def_FunR (RelatedByL x y (FunR r1 r2)) = do
    v <- newVariableName "v" [x,y,r1,r2]
    w <- newVariableName "w" [x,y,r1,r2]
    rewriteEQ ("def_FunR", def_FunR)
              (ForAllL v
               (ForAllL w
                (ImplL (RelatedByL (VarR v)
                                   (VarR w)
                                   r1)
                       (RelatedByL (AppR x (VarR v))
                                   (AppR y (VarR w))
                                   r2))))
def_FunR _ = mzero


{-
def_ForAllFixR :: MonadPlus m => Rule m
def_ForAllFixR (RelatedByL x y (ForAllFixR v r)) =
    rewriteEQ ("def_ForAllFixR", def_ForAllFixR)
              (ForAllL v
                (ImplL (RelatedByL (VarR v) (RelationsR [IsAdmissible]) MemberR)
                       (RelatedByL (instantiatedToR x (DomainR   (VarR v)))
                                   (instantiatedToR y (CoDomainR (VarR v)))
                                   r)))
def_ForAllFixR _ = mzero


def_ForAllSeqR :: MonadPlus m => Rule m
def_ForAllSeqR (RelatedByL x y (ForAllSeqR v r)) =
    rewriteEQ ("def_ForAllSeqR", def_ForAllSeqR)
              (ForAllL v
                (ImplL (RelatedByL (VarR v) (RelationsR [IsAdmissible, IsStrict]) MemberR)
                       (RelatedByL (instantiatedToR x (DomainR   (VarR v)))
                                   (instantiatedToR y (CoDomainR (VarR v)))
                                   r)))
def_ForAllSeqR _ = mzero
-}

def_FunSeqR :: MonadPlus m => Rule m
def_FunSeqR (RelatedByL f g (FunSeqR r1 r2)) = do
    x <- newVariableName "x" [f,g,r1,r2]
    y <- newVariableName "y" [f,g,r1,r2]
    rewriteEQ ("def_FunSeqR", def_FunSeqR)
              (AndL (equivL (isNotBottomL f)
                            (isNotBottomL g))
                    (ForAllL x
                       (ForAllL y
                       (ImplL (RelatedByL (VarR x)
                                          (VarR y)
                                          r1)
                              (RelatedByL (AppR f (VarR x))
                                          (AppR g (VarR y))
                                          r2)))))
def_FunSeqR _ = mzero

def_FunSeqIneqR :: MonadPlus m => Rule m
def_FunSeqIneqR (RelatedByL f g (FunSeqIneqR r1 r2)) = do
    x <- newVariableName "x" [f,g,r1,r2]
    y <- newVariableName "y" [f,g,r1,r2]
    rewriteEQ ("def_FunSeqIneqR", def_FunSeqIneqR)
              (AndL (ImplL (isNotBottomL f)
                           (isNotBottomL g)) -- Does not introduce a bottom
                    (ForAllL x
                       (ForAllL y
                       (ImplL (RelatedByL (VarR x)
                                          (VarR y)
                                          r1)
                              (RelatedByL (AppR f (VarR x))
                                          (AppR g (VarR y))
                                          r2)))))
def_FunSeqIneqR _ = mzero


isNotBottomL r = NotEqualL r BottomR
equivL l1 l2 = ImplL l1 l2 `AndL` ImplL l2 l1

equalsL r1 r2 = RelatedByL r1 r2 IdR

-- ]]]

{- Specialization to functions and related simplifications. [[[ -}

{- Specialization rule.
 -
 - Uses the "mustPermitStrengthening" guard to ensure correctness.
 -}
spec_fun :: MonadPlus m => Rule m
spec_fun (RelationsR properties) = do
    mustPermitStrengthening
    guard (IsFunction `notElem` properties) -- Not already a function
    rewrite ("spec_fun", spec_fun)
            (RelationsR (IsFunction : properties))
spec_fun _ = mzero


fun_elim_retval :: MonadPlus m => Rule m
fun_elim_retval (ForAllL o (ImplL (RelatedByL i (VarR o') f)
                                  l)) =
    do  guard (o  == o')
        guard (f /= IdR)
        mustBeFunction f
        l' <- l `withSubstitution` (o, AppR f i)
        rewrite ("fun_elim_retval", fun_elim_retval)
                (ImplL (RelatedByL i
                                   (domain f)
                                   MemberR)
                       l')
fun_elim_retval _ = mzero


fun_mem2eq :: MonadPlus m => Rule m
fun_mem2eq (RelatedByL i o f) = do
    guard (f /= IdR)
    mustBeFunction f
    rewrite ("fun_mem2eq", fun_mem2eq)
            (RelatedByL (AppR f i) o IdR)
fun_mem2eq _ = mzero


fun_sc_pointfree :: MonadPlus m => Rule m
fun_sc_pointfree (RelatedByL x y (FunR f g)) = do
    mustBeFunction f
    mustBeFunction g
    rewrite ("fun_sc_pointfree", fun_sc_pointfree)
            (RelatedByL (CompR f x) (CompR y g) IdR)
fun_sc_pointfree _ = mzero


fun_pointfree :: MonadPlus m => Rule m
fun_pointfree (ForAllL v (ImplL (RelatedByL (VarR v') (DomainR f) MemberR)
                                (RelatedByL lhs rhs IdR))) = do
    guard (v == v')
    mustBeFunction f
    (fs, a) <- matchNestedApps lhs
    (gs, b) <- matchNestedApps rhs
    guard (v == a)
    guard (v == b)
    let lhs_pf = foldr1 CompR fs
    let rhs_pf = foldr1 CompR gs
    rewrite ("fun_pointfree", fun_pointfree)
            (RelatedByL lhs_pf rhs_pf IdR)
  where
    matchNestedApps :: MonadPlus m => Expr t -> RewriteT m ([Expr t], VariableName)
    matchNestedApps (AppR f r@(AppR _ _)) = do
        (fs, x) <- matchNestedApps r
        return (f:fs, x)
    matchNestedApps (AppR f (VarR x)) = return ([f], x)
    matchNestedApps _ = mzero
fun_pointfree _ = mzero

{-
fun_introduce_point :: MonadPlus m => Rule m
fun_introduce_point (RelatedByL f g IdR) = do
    mustBeFunction f
    mustBeFunction g
    v <- newVariableName
    rewrite ("fun_introduce_point", fun_introduce_point)
            (ForAllL v (RelatedByL (AppR f (VarR v)) (AppR g (VarR v)) IdR))
fun_introduce_point _ = mzero
-}

-- ]]]

{- Pointed <-> Pointfree [[[ -}

elim_point :: MonadPlus m => Rule m
elim_point (ForAllL v (RelatedByL (AppR f (VarR v1)) (AppR g (VarR v2)) IdR)) = do
    -- "f" and "g" are functions since they are applied to something.
    guard (v == v1)
    guard (v == v2)
    rewrite ("elim_point", elim_point)
            (RelatedByL f g IdR)
elim_point _ = mzero

introduce_point :: MonadPlus m => Rule m
introduce_point (RelatedByL (CompR f1 f2) (CompR g1 g2) IdR) = do
    v <- newVariableName "v" [f1,f2,g1,g2]
    rewrite ("introduce_point", introduce_point)
            (ForAllL v (RelatedByL (AppR f1 (AppR f2 (VarR v)))
                                   (AppR g1 (AppR g2 (VarR v)))
                                   IdR))
introduce_point _ = mzero

-- ]]]

{- Specialization to constant functions and related simplifications. [[[ -}

spec_const :: MonadPlus m => Rule m
spec_const (ForAllL v (ImplL (RelatedByL (VarR v') (RelationsR _) MemberR)
                             (ForAllL c l))) = do
    mustPermitWeakening
    guard (v == v')
    l' <- l `withSubstitution` (v, (AppR (VarR "const") (VarR c)))
    rewrite ("spec_const", spec_const)
            (ForAllL c l')
spec_const _ = mzero

elim_const :: MonadPlus m => Rule m
elim_const (AppR (AppR (VarR "const") c) _) = do
    rewrite ("elim_const", elim_const)
            c
elim_const _ = mzero

-- ]]]

{- Specialization to the identity function and related simplifications. [[[ -}

-- FIXME Is this allowed?
spec_id2 :: MonadPlus m => Rule m
spec_id2 (RelatedByL r1 r2 (ForAllR _ _ _)) =
    rewrite ("spec_id2", spec_id2)
        (RelatedByL r1 r2 IdR)
spec_id2 _ = mzero

spec_id :: MonadPlus m => Rule m
spec_id (ForAllL v (ImplL (RelatedByL (VarR v') (RelationsR _) MemberR)
                          l)) = do
    mustPermitWeakening
    guard (v == v')
    l' <- l `withSubstitution` (v, IdR)
    rewrite ("spec_id", spec_id)
            l'
spec_id _ = mzero

elim_id :: MonadPlus m => Rule m
elim_id (ForAllL v (ImplL (RelatedByL r (VarR v') IdR) l)) = do
    guard (v == v')
    l' <- l `withSubstitution` (v, r)
    rewrite ("elim_id", elim_id)
            l'
elim_id _ = mzero

def_ListR_IdR :: MonadPlus m => Rule m
def_ListR_IdR (LiftR "[]" [IdR]) = do
    rewrite ("def_ListR_IdR", def_ListR_IdR) IdR
def_ListR_IdR _ = mzero

elim_CompR_IdR :: MonadPlus m => Rule m
elim_CompR_IdR (CompR f IdR) = rewrite ("elim_CompR_IdR", elim_CompR_IdR) f
elim_CompR_IdR (CompR IdR f) = rewrite ("elim_CompR_IdR", elim_CompR_IdR) f
elim_CompR_IdR _             = mzero

-- ]]]

{- Specialization to the empty relation and related simplifications. [[[ -}

spec_empty :: MonadPlus m => Rule m
spec_empty (ForAllL v (ImplL (RelatedByL (VarR v') (RelationsR _) MemberR)
                             l)) = do
    mustPermitWeakening
    guard (v == v')
    l' <- l `withSubstitution` (v, EmptyR)
    rewrite ("spec_empty", spec_empty)
            l'
spec_empty _ = mzero

elim_empty :: MonadPlus m => Rule m
elim_empty (RelatedByL _ _ EmptyR) = do
    rewrite ("elim_empty", elim_empty)
            BottomL
elim_empty _ = mzero

elim_ForAllL :: MonadPlus m => Rule m
-- TODO Make this more general: Unwrap l if l does not contain v.
elim_ForAllL (ForAllL _v BottomL) = do
    rewrite ("elim_ForAllL", elim_ForAllL)
            BottomL
elim_ForAllL (ForAllL _v TopL) = do
    rewrite ("elim_ForAllL", elim_ForAllL)
            TopL
elim_ForAllL _ = mzero

introduce_TopL :: MonadPlus m => Rule m
introduce_TopL (ImplL BottomL _) = do
   rewrite ("introduce_TopL", introduce_TopL)
           TopL
introduce_TopL _ = mzero

elim_TopL :: MonadPlus m => Rule m
elim_TopL (ImplL TopL l) = do
   rewrite ("elim_TopL", elim_TopL)
           l
elim_TopL _ = mzero

empty_def_ListR :: MonadPlus m => Rule m
empty_def_ListR (RelatedByL v w (LiftR "[]" [EmptyR])) = do
   rewrite ("empty_def_ListR", empty_def_ListR)
           (AndL (RelatedByL (VarR "[]") w IdR)
                 (RelatedByL (VarR "[]") v IdR))
empty_def_ListR _ = mzero

and2impl :: MonadPlus m => Rule m
and2impl (ImplL (AndL l1 l2) l3) = do
   rewriteEQ ("and2impl", and2impl)
             (ImplL l1 (ImplL l2 l3))
and2impl _ = mzero

-- {}* = {([],[])}
{-
empty_def_ListR :: MonadPlus m => Rule m
empty_def_ListR (ListR EmptyR) = do
    rewrite (SingletonR (VarR "[]") (VarR "[]"))


elim_singleton (RelatedByL (VarR x) (VarR y) (SingletonR r1 r2)) = do
    rewrite (AndL (RelatedByL (VarR x) r1 IdR)
                 (RelatedByL (VarR y) r2 IdR))

-}
{-
elim_singleton (ForAllL x (ForAllL y
                 (ImplL (RelatedByL (VarR x') (VarR y') (SingletonR r1 r2))
                        r3) = do
    guard (x == x')
    guard (y == y')
    r `withSubstitution` (x, r1)
      `withSubstitution` (y, r2)
-}

-- ]]]

{- Specialization to complete relations and related simplifications. [[[ -}

spec_complete :: MonadPlus m => Rule m
spec_complete (ForAllL v (ImplL (RelatedByL (VarR v') (RelationsR _) MemberR)
                                l)) = do
    mustPermitWeakening
    guard (v == v')
    l' <- l `withSubstitution` (v, ProductR (VarR "?") (VarR "?"))
    rewrite ("spec_complete", spec_complete)
            l'
spec_complete _ = mzero

elim_ListR_complete :: MonadPlus m => Rule m
elim_ListR_complete (RelatedByL r1 r2 (LiftR "[]" [ProductR _ _])) = do
    rewrite ("elim_ListR_complete", elim_ListR_complete)
            (RelatedByL (lengthR r1) (lengthR r2) IdR)
elim_ListR_complete _ = mzero

lengthR r = AppR (VarR "length") r

elim_complete :: MonadPlus m => Rule m
elim_complete (RelatedByL _r1 _r2 (ProductR _ _)) = do
    rewrite ("elim_complete", elim_complete)
            TopL -- FIXME This is only true if the expressions are not constrained otherwise.
elim_complete _ = mzero

-- ]]]

{- Replace certain equations with known functions. [[[ -}

eq_id :: MonadPlus m => Rule m
eq_id (ForAllL v (RelatedByL body (AppR f pattern) IdR)) = do
   guard (pattern == VarR v)
   guard (body    == VarR v)
   rewriteEQ ("eq_id", eq_id)
             (RelatedByL IdR f IdR)
eq_id _ = mzero

-- ]]]

{- Miscellaneous simplifications. [[[ -}

empty_elim_InstantiatedToR :: MonadPlus m => Rule m
empty_elim_InstantiatedToR (InstantiatedToR r1 r2) = do
   guard (r2 == CoDomainR EmptyR ||
          r2 == DomainR EmptyR)
   rewrite ("empty_elim_InstantiatedToR", empty_elim_InstantiatedToR)
           r1
empty_elim_InstantiatedToR _ = mzero

elim_AndL_idempotence :: MonadPlus m => Rule m
elim_AndL_idempotence (AndL l1 l2) = do
   guard (l1 == l2)
   rewriteEQ ("elim_AndL_idempotence", elim_AndL_idempotence)
             l1
elim_AndL_idempotence _ = mzero

impl2and :: MonadPlus m => Rule m
impl2and (ImplL l1 (ImplL l2 l3)) = do
    rewrite ("impl2and", impl2and)
            (ImplL (AndL l1 l2) l3)
impl2and _ = mzero

-- ]]]

{-  [[[ -}

data Constructor = Cns [Expr Relational] ([Expr Relational] -> Expr Relational)
type ADT = (String, [Expr Relational] -> [Constructor])

knownADTs :: ADTSpec
knownADTs liftR =
            [ ("[]", \[a] -> [ Cns []                  (\[]     -> VarR "[]")                     -- []
                             , Cns [a, liftR "[]" [a]] (\[x,xs] -> VarR "(:)" `AppR` x `AppR` xs) -- (:) a ([] a)
                             ])
            , ("Maybe", \[a] -> [ Cns []  (\[]  -> VarR "Nothing")       -- Nothing
                                , Cns [a] (\[x] -> VarR "Just" `AppR` x) -- Just a
                               ])
            ]

type ADTSpec = Lift -> [ADT]
type Lift = String -> [Expr Relational] -> Expr Relational

lift2set :: (MonadPlus m, Functor m) => ADTSpec -> Rule m
lift2set knownADTs expr = case expr of
   (LiftR tcons rs)    -> l2s_ LiftR    tcons rs
   (LiftFixR tcons rs) -> UnionR botbot <$> l2s_ LiftFixR tcons rs
   _ -> mzero
 where
   l2s_ liftR tcons rs = do
      adt <- lookupM tcons (knownADTs liftR)
      sets <- forM (adt rs) $ \(Cns d f) -> do
            (a,b) <- liftM unzip $ forM d $ \r -> do
                              let (x,y) = goodNames r
                              x' <- newVariableName x [r]
                              y' <- newVariableName y [r]
                              return (VarR x', VarR y')
            return $ SetR (f a) (f b) (foldr AndL TopL [ RelatedByL p q r | (p,q,r) <- zip3 a b d])
      rewrite ("lift2set", lift2set knownADTs)
               (foldr1 UnionR sets)

lookupM :: (MonadPlus m, Eq a) => a -> [(a, b)] -> m b
lookupM k = maybe mzero return . lookup k

goodNames :: Expr t -> (VariableName, VariableName)
goodNames (LiftR "[]" _) = ("xs","ys")
goodNames _              = ("x","y")


knownTypeClasses :: TypeClassSpec
knownTypeClasses = [ ("Eq", \a -> [ (VarR "(==)", FunctionT a (FunctionT a (ConstT "Bool")))
                                  ])
                   , ("Monoid", \a -> [ (VarR "mempty",  a)
                                      , (VarR "mappend", FunctionT a (FunctionT a a))
                                      ])
                   ]

type TypeClassSpec = [(String, Expr Type -> [(Expr Relational, Expr Type)])]

respects2rel :: MonadPlus m => TypeClassSpec -> Rule m
respects2rel knownTypeClasses (RespectsL asRelation r typeclass) = do
    methods <- lookupM typeclass knownTypeClasses
    v <- newVariableName "a" []
    rewrite ("respects2rel", respects2rel knownTypeClasses)
            (foldr AndL TopL [RelatedByL f f r' | (f,t) <- methods (VarT v), let r' = subst v r (asRelation t)])
respects2rel _ _ = mzero


subst v value t =
   let Just t' = runRewrite $ full_td substitute t
       substitute :: MonadPlus m => Rule m
       substitute (VarR v') | v == v' = return value
       substitute e                   = return e
   in t'


-- ]]]

-- ]]]

{- Rules (aggregate) [[[ -}

-- All simplifications
simplify :: MonadPlus m => Rule m
simplify = repeat $ once_td $ choiceList
    [ fun_sc_pointfree
    , fun_pointfree
    , fun_mem2eq
    , fun_elim_retval
    , elim_empty
    , elim_id
    , elim_ForAllL
    , elim_point
    , elim_const
    , def_ListR_IdR
    , elim_CompR_IdR
    , introduce_TopL
    , elim_TopL
    , empty_def_ListR
    , and2impl
    , empty_elim_InstantiatedToR
    , elim_AndL_idempotence
    , eq_id
    , elim_ListR_complete
    , elim_complete
    ]

-- Unfold all definitions
def_all = repeat (once_td def_any)
--def_all = innermost def_any

-- Any definition
def_any = choiceList [ def_ForAllR, def_FunR, def_ConstraintR, def_FunSeqR, def_FunSeqIneqR ] -- def_ForAllFixR, def_ForAllSeqR,


th_full = def_all

th_pointfree = def_all >>> once_td spec_fun
                       >>> simplify

th_contradiction = def_all >>> (once_td spec_id >>> simplify >>> once_td spec_empty >>> simplify
                                    `choice`
                                once_td spec_empty >>> simplify)

(>>>) = seq


-- Remove type instantiation information for readability.
remove_instantiations = innermost kill_InstantiatedToR
   where
      -- Removing only some instantiations is confusing,
      -- so we don't expose this rule.
      kill_InstantiatedToR :: MonadPlus m => Rule m
      kill_InstantiatedToR (InstantiatedToR r _) = return r
      kill_InstantiatedToR _                     = mzero


rename old new = full_td (try (rn old new))

rn :: MonadPlus m => VariableName -> VariableName -> Rule m
rn old new (VarR v)      | v == old = return (VarR new)
rn old new (ForAllL v l) | v == old = return (ForAllL new l)
rn old new (VarT v)   | v == old = return (VarT new)
rn old new (ForAllT v t) | v == old = return (ForAllT new t)
rn _   _   _                        = mzero


-- FIXME Do we really want to do that?
renameBound :: MonadPlus m => VariableName -> VariableName -> Rule m
renameBound old new = full_td rule
    where rule :: MonadPlus m => Rule m
          rule (ForAllL    v l) | v == old = liftM (ForAllL    new) (l `withSubstitution` (old, VarR new))
          rule (ForAllR ps v r) | v == old = liftM (ForAllR ps new) (r `withSubstitution` (old, VarR new))
          rule x                           = return x

-- ]]]

type Query r = forall t. Expr t -> r

{- Illustrative queries [[[ -}

count :: Query (Sum Int)
count _ = Sum 1

{- > -- Each term counts as one:
 - > count e
 - Sum {getSum = 1}
 - > -- This term has three direct subterms:
 - > allTU count e
 - Sum {getSum = 3}
 - > -- In total, there are nine subterms in the whole tree:
 - > full_tdTU count e
 - Sum {getSum = 9}
 -}


type QueryPlus r = MonadPlus m => Query (m r)

named :: VariableName -> QueryPlus VariableName
named v (VarR v') | v==v' = return v
named _ _                 = mzero

{- > oneTU (named "r") e :: Maybe VariableName
 - Just "r"
 - > oneTU (named "X") e :: Maybe VariableName
 - Nothing
 - > find_td (named "X") e :: Maybe VariableName
 - Just "X"
 - > find_td (named "X") e :: [VariableName]
 - ["X","X"]
 -}

vname :: QueryPlus VariableName
vname (VarR v) = return v
vname _        = mzero

{- > -- Is there a variable name?
 - > find_td vname e :: Maybe VariableName
 - Just "r"
 - > -- Get a list of all variable names:
 - > find_td vname e :: [VariableName]
 - ["r","r","X","X"]
 -}

tname :: QueryPlus VariableName
tname (VarT v) = return v
tname _           = mzero

freeNames :: QueryPlus VariableName                   -- extract name
          -> Query ([VariableName] -> [VariableName]) -- bind names
          -> Query [VariableName]                     -- return free names
freeNames extractName bindNames = freeNames'
  where
    freeNames' :: Query [VariableName]
    freeNames' expr =
        extractName expr `union` bindNames expr (nub $ allTU freeNames' expr)

lifts :: QueryPlus TypeConstructor
lifts (LiftR    c _) = return c
lifts (LiftFixR c _) = return c
lifts _              = mzero

respects :: QueryPlus Constraint
respects (RespectsL _ _ c) = return c
respects _                 = mzero

-- ]]]

{- Helper functions/combinators used by some rules [[[ -}

-- Only apply rule if the quantified VariableName is v.
ifNamed :: MonadPlus m => Rule m -> VariableName -> Rule m
ifNamed rule v e@(ForAllL v' _) = do
    guard (v == v')
    rule e
ifNamed _ _ _ = mzero

doesNotContain :: Expr t -> VariableName -> Bool
doesNotContain haystack needle =
    {- We can make Bool a Monoid by using the All wrapper.
     - This combines our results with (&&).
     - This does the right thing because needle is not
     - in haystack if and only if this is true for *all*
     - subterms of haystack.
     -}
    getAll (full_tdTU query haystack)
       where query :: Query All
             query (VarR v) = All (v /= needle)
             query _        = All True


{- Monadic guard against incorrectly applied specializations. -}
mustPermitStrengthening :: MonadPlus m => RewriteT m ()
mustPermitStrengthening = do
    direction <- getPermittedDirection
    guard (direction == Stronger)

{- Monadic guard against incorrectly applied specializations. -}
mustPermitWeakening :: MonadPlus m => RewriteT m ()
mustPermitWeakening = do
    direction <- getPermittedDirection
    guard (direction == Weaker)

mustBeFunction :: MonadPlus m => Expr Relational -> RewriteT m ()
mustBeFunction f = do
    props <- getProperties f
    guard (elem IsFunction props)

withSubstitution :: Monad m => Expr t -> (VariableName, Expr Relational) -> RewriteT m (Expr t)
withSubstitution expr (name, value) = full_td rule expr
        where rule :: Monad m => Rule m
              rule (VarR name') | name == name' = return value
              rule x                            = return x

domain = DomainR

getProperties :: MonadPlus m => Expr Relational -> RewriteT m Properties
getProperties (AppR _ _) =
    return [IsFunction]  -- FIXME Is this true?
getProperties (VarR "const") =
    return [IsFunction]
getProperties (VarR name) = do
    preconditions <- ask
    return (concatMap f preconditions)
  where
    f :: Expr t -> Properties
    f (RelatedByL (VarR name') (RelationsR ps) MemberR) | name == name' = ps
    f _ = mzero
getProperties (LiftR _ [r]) =
    getProperties r  -- FIXME Is this true?
getProperties IdR =
    return [IsFunction]
getProperties _ = mzero

newVariableName :: Monad m => String -> [Expr t] -> RewriteT m VariableName
newVariableName prefix subterms = do
    namesInScope <- getNamesInScope
    let namesInSubterms = concatMap (find_td vname) subterms
        desiredNames    = [prefix] ++ [prefix ++ show n | n <- [0..]]
        possibleNames   = (desiredNames \\ namesInScope) \\ namesInSubterms
    return (head possibleNames)

-- ]]]

{- "Rewrite" monad (stack) and corresponding "runRewrite" [[[ -}

type RewriteT m = ReaderT Preconditions
                   (ReaderT PermittedDirection
                    (ReaderT PathSpec
                     (ReaderT [VariableName]
                       (WriterT [RewriteStep m]
                        (WriterT (First (Expr Logical))
                         m)))))
type Preconditions = [Expr Logical]
data PermittedDirection = Weaker | Stronger deriving (Show, Eq)
type Position = Int


class Monad m => Rewrite m where
   withPrecondition      :: m (Expr Logical) -> Expr Logical -> m (Expr Logical)
   toggleDirection       :: m a -> m a
   getPermittedDirection :: m PermittedDirection
   atPosition            :: m a -> Int -> m a
   getPath               :: m PathSpec

instance Monad m => Rewrite (RewriteT m) where
   withPrecondition rw_l precond = local (precond:) rw_l

   toggleDirection = mapReaderT (local toggle)
      where toggle Weaker   = Stronger
            toggle Stronger = Weaker

   getPermittedDirection = lift ask

   atPosition rw pos = mapReaderT (mapReaderT (local changePath)) $ rw
      where changePath ns    = ns ++ [pos]

   getPath = lift (lift ask)

tellRewriteStep :: Monad m => Kind -> PathSpec -> String -> Rule m -> RewriteT m ()
tellRewriteStep kind path name rule = do
    tell [RewriteStep kind path name rule]

getPosition :: MonadPlus m => RewriteT m Position
getPosition = do
    path <- getPath
    guard (not (null path))
    return (last path)
    -- This way, missing positional information results in
    -- failure of the rewrite operation.


{- Use this instead of return in rewrite rules.
 -
 - The rule itself and its name have to be provided.
 - This information is used to reconstruct the rule
 - applications in form of a proof log with intermediate
 - steps.
 -}
rewrite :: Monad m => (Name, Rule m) -> Expr t -> RewriteT m (Expr t)
rewrite (name, rule) expr = do
    path <- getPath
    tellRewriteStep IMPL path name rule
    return expr

{- Same as 'rewrite' except from marking the rewrite step
 - as an equivalence instead of an implication.
 -}
rewriteEQ :: Monad m => (Name, Rule m) -> Expr t -> RewriteT m (Expr t)
rewriteEQ (name, rule) expr = do
    path <- getPath
    tellRewriteStep EQUIV path name rule
    return expr

{- Use this instead of return when providing the source expression -}
returnSrc :: Monad m => Expr Logical -> RewriteT m (Expr Logical)
returnSrc expr = tellSourceExpr expr >> return expr

tellSourceExpr :: Monad m => Expr Logical -> RewriteT m ()
tellSourceExpr = lift . lift . lift . lift . lift . tell . First . Just


getNamesInScope :: Monad m => RewriteT m [VariableName]
getNamesInScope = lift (lift (lift ask))

isInScope :: Monad m => VariableName -> RewriteT m Bool
isInScope v = do
   names <- getNamesInScope
   return (v `elem` names)

inScopeOf :: Monad m => [VariableName] -> RewriteT m a -> RewriteT m a
inScopeOf names = mapReaderT (mapReaderT (mapReaderT (local addNames)))
    where addNames = (names++)


runRewrite :: (Functor m, Monad m) => RewriteT m a -> m a
runRewrite = fmap fst . runRewriteWithLog

runRewriteWithLog :: (Functor m, Monad m) => RewriteT m a -> m (a, [RewriteStep m])
runRewriteWithLog = fmap fst . runRewriteWithLog'

runRewriteWithLog' = runWriterT
                   . runWriterT
                   . flip runReaderT []      -- no names in scope
                   . flip runReaderT []      -- no positional information
                   . flip runReaderT Weaker
                   . flip runReaderT []      -- no preconditions

sourceExpr :: (Monad m, Functor m) => RewriteT m a -> m (Expr Logical)
sourceExpr = join . fmap (maybe (fail "No source-expression set") return) . fmap getFirst . fmap snd . runRewriteWithLog' -- FIXME store this somewhere else

-- ]]]

{- Rewrite steps [[[ -}

data RewriteStep m = RewriteStep Kind PathSpec Name (Rule m)
data Kind = IMPL
          | EQUIV
    deriving (Show)
type PathSpec = [Int] -- The path from the root down to the affected expression in terms,
                      -- given as the number of the traversed child on each level.
type Name = String -- The name of the rule, should be the function name.

instance Show (RewriteStep _m) where
    show (RewriteStep _kind path name _rule) =
        name ++ " @" ++ show path

replayStep :: MonadPlus m => RewriteStep m -> Rule m
replayStep (RewriteStep _kind path _name rule) = pathToTraversal path rule

{- Rewrite steps (example):
 -
 - These can by 'replay'ed and applied to the parametricity condition of "[a]->[a]",
 - yielding Wadlers first example.
 -}
steps = [ RewriteStep EQUIV []      "def_ForAllR"      def_ForAllR
        , RewriteStep IMPL  [1,1,2] "spec_fun"         spec_fun
        , RewriteStep IMPL  [1,2]   "fun_sc_pointfree" fun_sc_pointfree
        ]

replay :: MonadPlus m => [RewriteStep m] -> Rule m
replay steps expr = foldM (flip ($)) expr (map replayStep steps)


data Derivation m = Derivation [Expr Logical] [RewriteStep m]

derivation :: (MonadPlus m, Functor m) => RewriteT m (Expr Logical) -> m (Derivation m)
derivation rw = do
    (_,steps) <- runRewriteWithLog rw
    expr      <- sourceExpr rw
    exprs     <- intermediates expr steps
    return (Derivation exprs steps)

{- Generate all intermediate expressions that occur when replaying a list
 - of rewrite steps one-by-one.
 -
 - Note that we really get a step-by-step proof log, even if the we did
 - the actual rewrite that generated the steps "in one go".
 -}
intermediates :: (MonadPlus m, Functor m) => Expr t -> [RewriteStep m] -> m [Expr t]
intermediates expr steps  =
    runRewrite $ sequence
               $ scanl (\e r -> e >>= r) (return expr)
               $ map (\s -> replayStep s) steps


-- ]]]

{- Convenience operators and functions for use in the ghci prompt [[[ -}

{- Usage example:
 -
 - > pc "[a]->[a]" >>= def_ForAllR >>= once_td spec_fun >>= simplify
 -
 - or, in single steps:
 -
 - > pc "[a]->[a]"
 - > it >>= def_ForAllR       -- unfold the outermost forall
 - > it >>= once_td spec_fun  -- specialize the resulting relation to a function
 - > it >>= simplify          -- simplify the resulting theorem
 -
 - To see the full derivation, do this afterwards:
 - > derive it
 -
 -}


{- Print the rules that were used in this rewrite. -}
trace :: RewriteT Maybe (Expr Logical) -> IO (RewriteT Maybe (Expr Logical))
trace rw = do
    let (Just (_,steps)) = runRewriteWithLog rw
    forM_ steps print
    return rw

{- Print the full derivation / proof log for this rewrite.
 -
 - This relies on the Derivation being shown by the ghci prompt.
 -}
derive :: RewriteT Maybe (Expr Logical) -> IO (Derivation Maybe)
derive = maybe (fail "Derivation not possible. (Did you set the source expression?)") return
       . derivation

{- Parametricity condition for a type given as string.
 -
 - Sets the returned expression as the source expression for the whole
 - rewrite operation. This makes it possible to replay the rewrite steps
 - later, e.g. to generate a proof log.
 -}
pc :: [Char] -> RewriteT Maybe (Expr Logical)
pc = either (fail . show) returnSrc . fmap (RelatedByL (VarR "f") (VarR "f") . parametricity) . parseType


-- Automatically perform the rewrite to show the result.
instance Show (RewriteT Maybe (Expr t)) where
    show = show . runRewrite

-- Format the derivation nicely. 'derive' relies on this.
instance Show (Derivation _m) where
  show (Derivation exprs steps) =
     -- 'steps' is one shorter than 'exprs' since the first element
     -- of 'exprs' is the original expression.
     intercalate "\n" $ map (\(e,s) -> e ++ s)
                      $ zip (map show exprs) $ "" : map (("\t by " ++) . show) steps

{- Show the abstract syntax tree of the expression
 -}
ast :: RewriteT Maybe (Expr t) -> IO Doc
ast = maybe (fail "") return . fmap pp . runRewrite

{-
vars :: String -> Rule
vars wishlist expr = do
   let names = (\\["[]", "const", "length", "?"]) $ nub $ find_td vname expr
   seqList (zipWith rename names (words wishlist)) expr
-}

-- ]]]

{- Strategy combinators [[[ -}

{- Primitives [[[ -}

identity :: Monad m => Rule m
identity =
    return

alwaysFail :: MonadPlus m => Rule m
alwaysFail =
    const mzero

seq :: Monad m => Rule m -> Rule m -> Rule m
seq r1 r2 e =
    r1 e >>= r2

seqTU :: Monoid r => Query r -> Query r -> Query r
seqTU q1 q2 e =
    q1 e `mappend` q2 e

choice :: MonadPlus m => Rule m -> Rule m -> Rule m
choice r1 r2 e =
    r1 e `mplus` r2 e

choiceTU :: MonadPlus m => Query (m r) -> Query (m r) -> Query (m r)
choiceTU q1 q2 e =
    q1 e `mplus` q2 e

-- FIXME This needs a better name.
--       It fulfills the role of Lämmels and Vissers 'hfoldr', but isn't really a fold.
g ::            Applicative c =>
                Expr t ->
                (forall s. Expr s -> c (Expr s)) ->
                c (Expr t)
g = $(generateGenericTraversal ''Expr) -- Automatically generated. See FTTemplate.hs.


newtype Q  tu    tp = Q  { unQ  :: tu         }
newtype M2 m1 m2 tp = M2 { unM2 :: m1 (m2 tp) }
newtype QM m  tu tp = QM { unQM :: m tu       }


instance Functor (Q r) where
    fmap _ (Q x)  = (Q x)
instance Monoid r => Applicative (Q r) where
    (Q x) <*> (Q y) = Q (x `mappend` y)
    pure = const (Q mempty)

instance (Monad m, Functor f) => Functor (M2 m f) where
    fmap f (M2 mx)  = M2 $ do { x <- mx; return (fmap f x) }
instance (Monad m, Applicative f) => Applicative (M2 m f) where
    (M2 mh) <*> (M2 mx) = M2 $ do { h <- mh; x <- mx; return (h <*> x) }
    pure = M2 . return . pure

instance MonadPlus m => Functor (QM m r) where
    fmap _ (QM mx) = QM mx
instance MonadPlus m => Applicative (QM m r) where
    (QM mx) <*> (QM my) = QM (mx `mplus` my)
    pure = const (QM mzero)


allTU :: Monoid r => Query r -> Query r
allTU query expr = unQ (g expr q)
    where q = Q . query


data Outcome a = Success a a | Failure a deriving Show

instance Functor Outcome where
    fmap f (Success x x') = Success (f x) (f x')
    fmap f (Failure x)    = Failure (f x)

instance Applicative Outcome where
    (Success f f') <*> (Success x _x') = Success (f x) (f' x )
    (Success f f') <*> (Failure x    ) = Success (f x) (f' x )
    (Failure f   ) <*> (Success x  x') = Success (f x) (f  x')
    (Failure f   ) <*> (Failure x    ) = Failure (f x)
    pure = Failure


oneM :: MonadPlus m => (forall t. Expr t -> m (Expr t)) -> Expr t -> m (Expr t)
oneM rule e = outcome2m =<< (unM2 $ g e q)
    where q x = M2 $ (rule x >>= \x' -> return (Success x x')) `mplus` (return (Failure x))
          outcome2m (Success _ e') = return e'
          outcome2m (Failure _   ) = mzero



oneTU :: MonadPlus m => Query (m r) -> Query (m r)
oneTU query e = unQM $ g e q
    where q x = QM (query x)


{- We will now define a combinator that is specific to Rewrite in which we can
 - introduce all of the special behaviour that our rules rely on.
 - The combinators 'all' and 'one' (and therefore all traversals) will be derived
 - from this one.
 -}

{- Apply the rule to the nth child.
 -}
nthChild :: Monad m => Int -> Rule m -> Rule m
-- Special case for traversing the left-hand part of an implication:
nthChild 1 rule (ImplL l1 l2) = flip atPosition 1 $ return ImplL `ap` toggleDirection (rule l1) `ap` return l2
-- Special case for traversing the right-hand part of an implication:
nthChild 2 rule (ImplL l1 l2) = flip atPosition 2 $ return ImplL `ap` return l1                 `ap` (rule l2 `withPrecondition` l1)
-- General case:
-- We wrap a state monad around the rule result type to track the current subterm number.
-- Apart from being used to decide whether to apply the rule,
-- this number is made available to the rule (see 'getPosition', 'getPath') by passing it
-- to 'atPosition'.
-- Note that the 'WrapMonad'/'unwrapMonad' is used here
-- to make Rewrite an applicative functor.
nthChild n rule expr = unwrapMonad $ fst $ flip runState 0 $ unM2 (g expr q)
    where q x = M2 $ do
            modify (+1)
            m <- get
            return $ WrapMonad (if m==n then (names `inScopeOf` rule x `atPosition` m) else identity x)
          names = qname expr

qname :: QueryPlus VariableName
qname (ForAllT v _) = return v
qname (ForAllR  _ v _) = return v
qname (ForAllL    v _) = return v
qname _                = mzero


-- "all" and "one" can now be derived from nthChild,
-- using allTU to query for the total number of children.

all :: Monad m => Rule m -> Rule m
all rule expr =
    let (Sum n) = allTU count expr
        f e m = nthChild m rule e
    in foldM f expr [1..n]

one :: MonadPlus m => Rule m -> Rule m
one rule expr =
    let (Sum n) = allTU count expr
        go (m:ms) rw = go ms (rw `mplus` nthChild m rule expr)
        go []     rw = rw
    in go [1..n] mzero

-- ]]]

{- Higher level strategies [[[ -}

try :: MonadPlus m => Rule m -> Rule m
try rule = choice rule identity

repeat :: MonadPlus m => Rule m -> Rule m
repeat rule = try (rule `seq` repeat rule)

repeatN :: MonadPlus m => Int -> Rule m -> Rule m
repeatN 0 _    = identity
repeatN n rule = try (rule `seq` repeatN (n-1) rule)

choiceList :: MonadPlus m => [Rule m] -> Rule m
choiceList (r:rs) = choice r (choiceList rs)
choiceList []     = alwaysFail

seqList :: MonadPlus m => [Rule m] -> Rule m 
seqList (r:rs) = seq r (seqList rs)
seqList []     = identity

-- ]]]

{- Traversal combinators [[[ -}

full_td :: Monad m => Rule m -> Rule m
full_td rule = rule `seq` all (full_td rule)

full_tdTU :: Monoid r => Query r -> Query r
full_tdTU query = query `seqTU` allTU (full_tdTU query)

once_td :: MonadPlus m => Rule m -> Rule m
once_td rule = rule `choice` one (once_td rule)

once_bu :: MonadPlus m => Rule m -> Rule m
once_bu rule = one (once_bu rule) `choice` rule

find_td :: MonadPlus m => Query (m r) -> Query (m r)
find_td query = query `choiceTU` oneTU (find_td query)

innermost :: MonadPlus m => Rule m -> Rule m
innermost rule = all (innermost rule)
                        `seq`
                 try (rule `seq` innermost rule)


{- Traverse the expression along the given path and apply the rule at the end.
 -
 - We can't put "[Int] -> Rule -> Rule" as a type here.
 - With that type, the body would be "less polymorphic than expected".
 - FIXME Sadly, I don't understand the difference. :(
 -}
pathToTraversal :: Monad m => [Int] -> Rule m -> (Expr t -> RewriteT m (Expr t))
pathToTraversal path rule = unwrapRule (foldr nthChild' rule' path)
    where
       -- The primed functions are like the unprimed but using a
       -- newtype wrapper around "Rule".
       nthChild' n r = WrapRule (nthChild n (unwrapRule r))
       rule' = WrapRule rule

newtype WrappedRule m = WrapRule { unwrapRule :: Rule m }


-- ]]]

-- ]]]

{- Pretty printing [[[ -}


-- Pretty print the AST
pp :: Expr t -> Doc
pp = $(generatePrettyPrinter ''Expr)

-- Pretty print the AST as JSON
json :: Expr t -> Doc
json = $(generateJSONPrettyPrinter ''Expr)

-- Pretty print as a mathematical formula
pp' :: Expr t -> Doc
pp' = pp
  where
    pp :: Expr t -> Doc
    pp expr =
     case expr of
        RelatedByL r1 r2 IdR     -> pp r1 <+> text "=" <+> pp r2
        RelatedByL r1 r2 MemberR -> pp r1 <+> text "∈" <+> pp r2
        RelatedByL r1 r2 r3      -> ppPair r1 r2 <+> text "∈" <+> pp r3
        ImplL      l1 l2         -> parens $ pp l1 $$ (text "⇒" <+> pp l2)
        AndL       l1 l2         -> parens $ pp l1 $$ (text "∧" <+> pp l2)
        ForAllL    v  l          -> parens $ text "∀" <+> text v <> text "." <+> pp l
        BottomL                  -> text "⊥"
        TopL                     -> text "⊤"
        RespectsL  _m  r  c      -> pp r <+> text "respects" <+> text c
        NotEqualL  r1 r2         -> pp r1 <+> text "≠" <+> pp r2

        VarR       v             -> text v
        LiftR      "[]" [r]      -> pp r <> text "*"
        LiftR      c  rs         -> parens $ text "lift_" <> text c <+> hsep (map pp rs)
        LiftFixR   c  rs         -> parens $ text "liftᶠ_" <> text c <+> hsep (map pp rs)
        FunR       r1 r2         -> parens $ pp r1 <+> text "→" <+> pp r2
        FunSeqR    r1 r2         -> parens $ pp r1 <+> text "→ˢ" <+> pp r2
        FunSeqIneqR r1 r2        -> parens $ pp r1 <+> text "→⁽ˢ⁺ᒼ⁾" <+> pp r2 

        ProductR   r1 r2         -> parens $ pp r1 <+> text "×" <+> pp r2
        ForAllR []  v  r         -> parens $ text "∀" <+> text v <> text "." <+> pp r
        ForAllR _ps v  r         -> parens $ text "∀*" <+> text v <> text "." <+> pp r
        --ForAllR [] v  r          -> parens $ text "∀ᶠ" <+> text v <> text "." <+> pp r
        --ForAllR [] v  r          -> parens $ text "∀ˢ" <+> text v <> text "." <+> pp r
        AppR       r1 r2@(VarR _)-> pp r1  <+> pp r2  -- no parenthesis if argument is not a complex value
        AppR       r1 r2         -> parens $ pp r1  <+> pp r2
        CompR      r1 r2         -> parens $ pp r1  <+> text "∘" <+> pp r2
        InstantiatedToR  r1 r2   -> pp r1 <> text "_" <> pp r2
        DomainR    r             -> text "𝛛" <> pp r
        CoDomainR  r             -> text "𝐜" <> pp r
        IdR                      -> text "id"
        EmptyR                   -> text "{}"
        MemberR                  -> text "MemberR"
        BottomR                  -> text "⊥"
        RelationsR [IsFunction]  -> text "FUN"
        RelationsR []            -> text "REL"
        RelationsR _ps           -> text "???"
        ConstraintR _m c  v  r    -> text c <+> text v <+> text "=>" <+> pp r
        SetR       r1 r2 TopL    -> text "{" <> ppPair r1 r2 <> text "}"
        SetR       r1 r2 l       -> text "{" <> ppPair r1 r2 <+> text "|" <+> pp l <> text "}"
        UnionR     r1 r2         -> pp r1 <+> text "∪" <+> pp r2
        NoMoreDefinedR           -> text "⊑"

        VarT         v        -> text v
        ConstT       v        -> text v
        AppT         c  ts    -> parens $ text c <+> hsep (map pp ts)
        FunctionT        t1 t2    -> parens $ pp t1 <+> text "→" <+> pp t2
        ProductT     t1 t2    -> parens $ pp t1 <+> text "×" <+> pp t2
        ListT        t        -> pp t <> text "*"
        ForAllT      v  t     -> parens $ text "∀" <+> text v <> text "." <+> pp t
        --ForAllT   cs v  t     -> parens $ text "∀_" <> ppList cs <+> text v <> text "." <+> pp t
        ConstraintT     c  v  t  -> text c <+> text v <+> text "=>" <+> pp t

    ppPair x y = text "(" <> pp x <> text ", " <> pp y <> text ")"
    --ppList xs  = text ("{" ++ intercalate "," (map show xs) ++ "}")

-- Pretty print as TeX
tex :: Expr t -> Doc
tex expr = case expr of
        RelationsR [IsFunction] -> text "\\FUN"
        RelationsR []           -> text "\\REL"
        RelationsR _ps          -> text "\\unknown"
        _                       -> $(generateTeXPrettyPrinter ''Expr) expr

-- Pretty print a complete derivation as mathematical formulae
-- TODO
--ppD :: Derivation -> Doc

-- Pretty print a complete derivation as TeX
texD :: Derivation Maybe -> Doc
texD (Derivation exprs steps) =
     vcat [ begin "derivation"
          , vcat $ map (\(e,s) -> step s e)
                 $ zip exprs $ Nothing : map Just steps
          , end   "derivation"
          ]
  where
    cmd = text . ('\\':)
    begin = cmd
    end   = cmd . ("end"++)
    step Nothing expr =
        cmd "RewriteStep" <+> braces (text "")
                          <+> braces (text "")
                          <+> braces (tex expr)
    step (Just (RewriteStep kind _path name _rule)) expr =
        cmd "RewriteStep" <+> braces (text (show kind)) -- IMPL or EQUIV
                          <+> braces (text name)
                          <+> braces (tex expr)

-- ]]]

{- Interpretation of type expressions / Language models [[[ -}

parametricity :: Expr Type -> Expr Relational
parametricity =
    asRelation_basic

asRelation_basic, asRelation_fix     , asRelation_seq
                , asRelation_fix_ineq, asRelation_seq_ineq :: Model

asRelation_basic = asRelation
  where
    {- Language model: basic -}
    asRelation :: Expr Type -> Expr Relational
    asRelation (VarT v)            = VarR v
    asRelation (ConstT _v)         = IdR
    asRelation (AppT  c ts)        = LiftR c (map asRelation ts)
    asRelation (FunctionT t1 t2)   = FunR (asRelation t1) (asRelation t2)
    asRelation (ProductT t1 t2)    = LiftR "(,)" [asRelation t1, asRelation t2]
    asRelation (ListT t')          = LiftR "[]" [asRelation t']
    asRelation (ForAllT v t')      = ForAllR [] v (asRelation t')
    asRelation (ConstraintT c v t) = ConstraintR asRelation c v (asRelation t)

{- In the language model with fix, FunR and LiftR need to be distinguished
 - from their unpointed versions.
 -}

asRelation_fix = asRelation
  where
    {- Language model: fix -}
    asRelation :: Expr Type -> Expr Relational
    asRelation (VarT v)            = VarR v
    asRelation (ConstT _v)         = IdR `mappend` botbot
    asRelation (AppT  c ts)        = LiftFixR c (map asRelation ts)
    asRelation (FunctionT t1 t2)   = FunR (asRelation t1) (asRelation t2)
    asRelation (ProductT t1 t2)    = LiftFixR "(,)" [asRelation t1, asRelation t2]
    asRelation (ListT t')          = LiftFixR "[]" [asRelation t']
    asRelation (ForAllT v t')      = ForAllR [IsAdmissible] v (asRelation t')
    asRelation (ConstraintT c v t) = ConstraintR asRelation c v (asRelation t)

botbot = SetR BottomR BottomR TopL

instance Monoid (Expr Relational) where
   mappend = UnionR
   mempty  = EmptyR

asRelation_seq = asRelation
  where
    {- Language model: seq -}
    asRelation :: Expr Type -> Expr Relational
    asRelation (VarT v)            = VarR v
    asRelation (ConstT _v)         = IdR `mappend` botbot
    asRelation (AppT  c ts)        = LiftFixR c (map asRelation ts)
    asRelation (FunctionT t1 t2)   = FunSeqR (asRelation t1) (asRelation t2)
    asRelation (ProductT t1 t2)    = LiftFixR "(,)" [asRelation t1, asRelation t2]
    asRelation (ListT t')          = LiftFixR "[]" [asRelation t']
    asRelation (ForAllT v t')      = ForAllR [IsAdmissible,IsLeftClosed] v (asRelation t')
    asRelation (ConstraintT c v t) = ConstraintR asRelation c v (asRelation t)

asRelation_fix_ineq = asRelation
  where
    {- Language model: seq -}
    asRelation :: Expr Type -> Expr Relational
    asRelation (VarT v)            = VarR v
    asRelation (ConstT _v)         = NoMoreDefinedR
    asRelation (AppT  c ts)        = NoMoreDefinedR `CompR` LiftFixR c (map asRelation ts)
    asRelation (FunctionT t1 t2)   = FunR (asRelation t1) (asRelation t2)
    asRelation (ProductT t1 t2)    = NoMoreDefinedR `CompR` LiftFixR "(,)" [asRelation t1, asRelation t2]
    asRelation (ListT t')          = NoMoreDefinedR `CompR` LiftFixR "[]" [asRelation t']
    asRelation (ForAllT v t')      = ForAllR [IsAdmissible,IsBottomReflecting] v (asRelation t')
    asRelation (ConstraintT c v t) = ConstraintR asRelation c v (asRelation t)

asRelation_seq_ineq = asRelation
  where
    {- Language model: seq -}
    asRelation :: Expr Type -> Expr Relational
    asRelation (VarT v)            = VarR v
    asRelation (ConstT _v)         = NoMoreDefinedR
    asRelation (AppT  c ts)        = NoMoreDefinedR `CompR` LiftFixR c (map asRelation ts)
    asRelation (FunctionT t1 t2)   = FunSeqIneqR (asRelation t1) (asRelation t2)
    asRelation (ProductT t1 t2)    = NoMoreDefinedR `CompR` LiftFixR "(,)" [asRelation t1, asRelation t2]
    asRelation (ListT t')          = NoMoreDefinedR `CompR` LiftFixR "[]" [asRelation t']
    asRelation (ForAllT v t')      = ForAllR [IsAdmissible,IsTotal,IsLeftClosed] v (asRelation t')
    asRelation (ConstraintT c v t) = ConstraintR asRelation c v (asRelation t)

-- ]]]

{- Simple Parser [[[ -}

parseType = Pc.parse (type_p >>= passThrough Pc.eof >>= return . allQuantifyFreeVariables) "(input)"

passThrough p r = p >> return r

allQuantifyFreeVariables :: Expr Type -> Expr Type
allQuantifyFreeVariables t = foldr ForAllT t (freeTypeNames t)

freeTypeNames :: Expr Type -> [VariableName]
freeTypeNames = freeNames tname bindNames
  where
    bindNames :: Expr t -> [VariableName] -> [VariableName]
    bindNames (ForAllT name _) names = names \\ [name]
    bindNames _                   names = names


{- Grammar for type expressions: -}
type_p =  Pc.try fun_p
      <|> nonfun_p
nonfun_p =  list_p
        <|> fa_p
        <|> var_p
        <|> Pc.try tc_p
        <|> Pc.try app_p
        <|> const_p
        <|> Pc.try prodtype_p
        <|> ptype_p
list_p = do
    Pc.char '['
    t <- type_p
    Pc.char ']'
    return $ ListT t
var_p = liftM VarT varname_p
tc_p = do
    constraint <- tc1_p <|> tcN_p
    Pc.string " => "
    t <- type_p
    return $ constraint t
tc1_p = do
    tc <- typename_p
    Pc.char ' '
    v  <- varname_p
    return $ ConstraintT tc v
tcN_p = do
    Pc.char '('
    cs <- Pc.sepBy1 tc1_p comma_p
    Pc.char ')'
    return $ foldr1 (.) cs
app_p = do
    c <- typename_p
    Pc.char ' '
    ts <- Pc.sepBy1 type_p (Pc.char ' ')
    return $ AppT c ts
const_p = do
    c <- typename_p
    return $ ConstT c
fun_p = do
    t1 <- nonfun_p
    Pc.string " -> " <|> Pc.string "->"
    t2 <- type_p
    return $ FunctionT t1 t2
ptype_p = do
    Pc.char '('
    t <- type_p
    Pc.char ')'
    return t
prodtype_p = do
    Pc.char '('
    t1 <- type_p
    Pc.char ','
    Pc.optional (Pc.char ' ')
    t2 <- type_p
    Pc.char ')'
    return $ ProductT t1 t2
fa_p = do
    Pc.string "∀" <|> Pc.string "forall "
    vs <- varname_p `Pc.sepEndBy1` Pc.char ' '
    Pc.string ". "
    t <- type_p
    return $ foldr (\v t'->ForAllT v t') t vs
varname_p = Pc.many1 Pc.lower
typename_p = do
    x  <- Pc.upper
    xs <- Pc.many Pc.alphaNum
    return (x:xs)
comma_p = do
    c <- Pc.char ','
    Pc.optional (Pc.char ' ')
    return c

-- ]]]

-- vim:foldenable:foldmethod=marker:foldmarker=[[[,]]]
