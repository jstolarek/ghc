-- The @FamInst@ type: family instance heads

{-# LANGUAGE CPP, GADTs, DataKinds #-}

module FamInst (
        FamInstEnvs, tcGetFamInstEnvs,
        checkFamInstConsistency, tcExtendLocalFamInstEnv,
        tcLookupFamInst,
        tcLookupDataFamInst, tcLookupDataFamInst_maybe,
        tcInstNewTyCon_maybe, tcTopNormaliseNewTypeTF_maybe,
        newFamInst,

        -- * Injectivity
        makeInjectivityErrors, conflictInjInstErr, unusedInjectiveVarsErr,
        tfHeadedErr, bareVariableInRHSErr
    ) where

import HscTypes
import FamInstEnv
import InstEnv( roughMatchTcs )
import Coercion    hiding ( substTy )
import TcEvidence
import LoadIface
import TcRnMonad
import SrcLoc
import TyCon
import CoAxiom
import DynFlags
import Module
import Outputable
import UniqFM
import FastString
import Util
import RdrName
import DataCon ( dataConName )
import Maybes
import TcMType
import TcType
import Name
import VarSet
import Control.Monad
import Data.Map (Map)
import qualified Data.Map as Map
import Control.Arrow ( first, second )

#include "HsVersions.h"

{-
************************************************************************
*                                                                      *
                 Making a FamInst
*                                                                      *
************************************************************************
-}

-- All type variables in a FamInst must be fresh. This function
-- creates the fresh variables and applies the necessary substitution
-- It is defined here to avoid a dependency from FamInstEnv on the monad
-- code.

newFamInst :: FamFlavor -> CoAxiom Unbranched -> TcRnIf gbl lcl FamInst
-- Freshen the type variables of the FamInst branches
-- Called from the vectoriser monad too, hence the rather general type
newFamInst flavor axiom@(CoAxiom { co_ax_branches = FirstBranch branch
                                 , co_ax_tc = fam_tc })
  | CoAxBranch { cab_tvs = tvs
               , cab_lhs = lhs
               , cab_rhs = rhs } <- branch
  = do { (subst, tvs') <- freshenTyVarBndrs tvs
       ; return (FamInst { fi_fam      = tyConName fam_tc
                         , fi_flavor   = flavor
                         , fi_tcs      = roughMatchTcs lhs
                         , fi_tvs      = tvs'
                         , fi_tys      = substTys subst lhs
                         , fi_rhs      = substTy  subst rhs
                         , fi_axiom    = axiom }) }

{-
************************************************************************
*                                                                      *
        Optimised overlap checking for family instances
*                                                                      *
************************************************************************

For any two family instance modules that we import directly or indirectly, we
check whether the instances in the two modules are consistent, *unless* we can
be certain that the instances of the two modules have already been checked for
consistency during the compilation of modules that we import.

Why do we need to check?  Consider
   module X1 where                module X2 where
    data T1                         data T2
    type instance F T1 b = Int      type instance F a T2 = Char
    f1 :: F T1 a -> Int             f2 :: Char -> F a T2
    f1 x = x                        f2 x = x

Now if we import both X1 and X2 we could make (f2 . f1) :: Int -> Char.
Notice that neither instance is an orphan.

How do we know which pairs of modules have already been checked?  Any pair of
modules where both modules occur in the `HscTypes.dep_finsts' set (of the
`HscTypes.Dependencies') of one of our directly imported modules must have
already been checked.  Everything else, we check now.  (So that we can be
certain that the modules in our `HscTypes.dep_finsts' are consistent.)
-}

-- The optimisation of overlap tests is based on determining pairs of modules
-- whose family instances need to be checked for consistency.
--
data ModulePair = ModulePair Module Module

-- canonical order of the components of a module pair
--
canon :: ModulePair -> (Module, Module)
canon (ModulePair m1 m2) | m1 < m2   = (m1, m2)
                         | otherwise = (m2, m1)

instance Eq ModulePair where
  mp1 == mp2 = canon mp1 == canon mp2

instance Ord ModulePair where
  mp1 `compare` mp2 = canon mp1 `compare` canon mp2

instance Outputable ModulePair where
  ppr (ModulePair m1 m2) = angleBrackets (ppr m1 <> comma <+> ppr m2)

-- Sets of module pairs
--
type ModulePairSet = Map ModulePair ()

listToSet :: [ModulePair] -> ModulePairSet
listToSet l = Map.fromList (zip l (repeat ()))

checkFamInstConsistency :: [Module] -> [Module] -> TcM ()
checkFamInstConsistency famInstMods directlyImpMods
  = do { dflags     <- getDynFlags
       ; (eps, hpt) <- getEpsAndHpt
       ; let { -- Fetch the iface of a given module.  Must succeed as
               -- all directly imported modules must already have been loaded.
               modIface mod =
                 case lookupIfaceByModule dflags hpt (eps_PIT eps) mod of
                   Nothing    -> panic "FamInst.checkFamInstConsistency"
                   Just iface -> iface

             ; hmiModule     = mi_module . hm_iface
             ; hmiFamInstEnv = extendFamInstEnvList emptyFamInstEnv
                               . md_fam_insts . hm_details
             ; hpt_fam_insts = mkModuleEnv [ (hmiModule hmi, hmiFamInstEnv hmi)
                                           | hmi <- eltsUFM hpt]
             ; groups        = map (dep_finsts . mi_deps . modIface)
                                   directlyImpMods
             ; okPairs       = listToSet $ concatMap allPairs groups
                 -- instances of okPairs are consistent
             ; criticalPairs = listToSet $ allPairs famInstMods
                 -- all pairs that we need to consider
             ; toCheckPairs  = Map.keys $ criticalPairs `Map.difference` okPairs
                 -- the difference gives us the pairs we need to check now
             }

       ; mapM_ (check hpt_fam_insts) toCheckPairs
       }
  where
    allPairs []     = []
    allPairs (m:ms) = map (ModulePair m) ms ++ allPairs ms

    check hpt_fam_insts (ModulePair m1 m2)
      = do { env1 <- getFamInsts hpt_fam_insts m1
           ; env2 <- getFamInsts hpt_fam_insts m2
           ; mapM_ (checkForConflicts (emptyFamInstEnv, env2))
                   (famInstEnvElts env1)
           ; mapM_ (checkForInjectivityConflicts (emptyFamInstEnv,env2))
                   (famInstEnvElts env1)
 }


getFamInsts :: ModuleEnv FamInstEnv -> Module -> TcM FamInstEnv
getFamInsts hpt_fam_insts mod
  | Just env <- lookupModuleEnv hpt_fam_insts mod = return env
  | otherwise = do { _ <- initIfaceTcRn (loadSysInterface doc mod)
                   ; eps <- getEps
                   ; return (expectJust "checkFamInstConsistency" $
                             lookupModuleEnv (eps_mod_fam_inst_env eps) mod) }
  where
    doc = ppr mod <+> ptext (sLit "is a family-instance module")

{-
************************************************************************
*                                                                      *
        Lookup
*                                                                      *
************************************************************************

Look up the instance tycon of a family instance.

The match may be ambiguous (as we know that overlapping instances have
identical right-hand sides under overlapping substitutions - see
'FamInstEnv.lookupFamInstEnvConflicts').  However, the type arguments used
for matching must be equal to or be more specific than those of the family
instance declaration.  We pick one of the matches in case of ambiguity; as
the right-hand sides are identical under the match substitution, the choice
does not matter.

Return the instance tycon and its type instance.  For example, if we have

 tcLookupFamInst 'T' '[Int]' yields (':R42T', 'Int')

then we have a coercion (ie, type instance of family instance coercion)

 :Co:R42T Int :: T [Int] ~ :R42T Int

which implies that :R42T was declared as 'data instance T [a]'.
-}

tcLookupFamInst :: FamInstEnvs -> TyCon -> [Type] -> Maybe FamInstMatch
tcLookupFamInst fam_envs tycon tys
  | not (isOpenFamilyTyCon tycon)
  = Nothing
  | otherwise
  = case lookupFamInstEnv fam_envs tycon tys of
      match : _ -> Just match
      []        -> Nothing

-- | If @co :: T ts ~ rep_ty@ then:
--
-- > instNewTyCon_maybe T ts = Just (rep_ty, co)
--
-- Checks for a newtype, and for being saturated
-- Just like Coercion.instNewTyCon_maybe, but returns a TcCoercion
tcInstNewTyCon_maybe :: TyCon -> [TcType] -> Maybe (TcType, TcCoercion)
tcInstNewTyCon_maybe tc tys = fmap (second TcCoercion) $
                              instNewTyCon_maybe tc tys

-- | Like 'tcLookupDataFamInst_maybe', but returns the arguments back if
-- there is no data family to unwrap.
-- Returns a Representational coercion
tcLookupDataFamInst :: FamInstEnvs -> TyCon -> [TcType]
                    -> (TyCon, [TcType], Coercion)
tcLookupDataFamInst fam_inst_envs tc tc_args
  | Just (rep_tc, rep_args, co)
      <- tcLookupDataFamInst_maybe fam_inst_envs tc tc_args
  = (rep_tc, rep_args, co)
  | otherwise
  = (tc, tc_args, mkReflCo Representational (mkTyConApp tc tc_args))

tcLookupDataFamInst_maybe :: FamInstEnvs -> TyCon -> [TcType]
                          -> Maybe (TyCon, [TcType], Coercion)
-- ^ Converts a data family type (eg F [a]) to its representation type (eg FList a)
-- and returns a coercion between the two: co :: F [a] ~R FList a
tcLookupDataFamInst_maybe fam_inst_envs tc tc_args
  | isDataFamilyTyCon tc
  , match : _ <- lookupFamInstEnv fam_inst_envs tc tc_args
  , FamInstMatch { fim_instance = rep_fam
                 , fim_tys      = rep_args } <- match
  , let ax     = famInstAxiom rep_fam
        rep_tc = dataFamInstRepTyCon rep_fam
        co     = mkUnbranchedAxInstCo Representational ax rep_args
  = Just (rep_tc, rep_args, co)

  | otherwise
  = Nothing

-- | 'tcTopNormaliseNewTypeTF_maybe' gets rid of top-level newtypes,
-- potentially looking through newtype instances.
--
-- It is only used by the type inference engine (specifically, when
-- soliving 'Coercible' instances), and hence it is careful to unwrap
-- only if the relevant data constructor is in scope.  That's why
-- it get a GlobalRdrEnv argument.
--
-- It is careful not to unwrap data/newtype instances if it can't
-- continue unwrapping.  Such care is necessary for proper error
-- messages.
--
-- It does not look through type families.
-- It does not normalise arguments to a tycon.
--
-- Always produces a representational coercion.
tcTopNormaliseNewTypeTF_maybe :: FamInstEnvs
                              -> GlobalRdrEnv
                              -> Type
                              -> Maybe (TcCoercion, Type)
tcTopNormaliseNewTypeTF_maybe faminsts rdr_env ty
-- cf. FamInstEnv.topNormaliseType_maybe and Coercion.topNormaliseNewType_maybe
  = fmap (first TcCoercion) $ topNormaliseTypeX_maybe stepper ty
  where
    stepper = unwrap_newtype `composeSteppers` unwrap_newtype_instance

    -- For newtype instances we take a double step or nothing, so that
    -- we don't return the reprsentation type of the newtype instance,
    -- which would lead to terrible error messages
    unwrap_newtype_instance rec_nts tc tys
      | Just (tc', tys', co) <- tcLookupDataFamInst_maybe faminsts tc tys
      = modifyStepResultCo (co `mkTransCo`) $
        unwrap_newtype rec_nts tc' tys'
      | otherwise = NS_Done

    unwrap_newtype rec_nts tc tys
      | data_cons_in_scope tc
      = unwrapNewTypeStepper rec_nts tc tys

      | otherwise
      = NS_Done

    data_cons_in_scope :: TyCon -> Bool
    data_cons_in_scope tc
      = isWiredInName (tyConName tc) ||
        (not (isAbstractTyCon tc) && all in_scope data_con_names)
      where
        data_con_names = map dataConName (tyConDataCons tc)
        in_scope dc    = not $ null $ lookupGRE_Name rdr_env dc

{-
************************************************************************
*                                                                      *
        Extending the family instance environment
*                                                                      *
************************************************************************
-}

-- Add new locally-defined family instances
tcExtendLocalFamInstEnv :: [FamInst] -> TcM a -> TcM a
tcExtendLocalFamInstEnv fam_insts thing_inside
 = do { env <- getGblEnv
      ; (inst_env', fam_insts') <- foldlM addLocalFamInst
                                       (tcg_fam_inst_env env, tcg_fam_insts env)
                                       fam_insts
      ; let env' = env { tcg_fam_insts    = fam_insts'
                       , tcg_fam_inst_env = inst_env' }
      ; setGblEnv env' thing_inside
      }

-- Check that the proposed new instance is OK,
-- and then add it to the home inst env
-- This must be lazy in the fam_inst arguments, see Note [Lazy axiom match]
-- in FamInstEnv.hs
addLocalFamInst :: (FamInstEnv,[FamInst])
                -> FamInst
                -> TcM (FamInstEnv, [FamInst])
addLocalFamInst (home_fie, my_fis) fam_inst
        -- home_fie includes home package and this module
        -- my_fies is just the ones from this module
  = do { traceTc "addLocalFamInst" (ppr fam_inst)

       ; isGHCi <- getIsGHCi
       ; mod <- getModule
       ; traceTc "alfi" (ppr mod $$ ppr isGHCi)

           -- In GHCi, we *override* any identical instances
           -- that are also defined in the interactive context
           -- See Note [Override identical instances in GHCi] in HscTypes
       ; let home_fie'
               | isGHCi    = deleteFromFamInstEnv home_fie fam_inst
               | otherwise = home_fie

           -- Load imported instances, so that we report
           -- overlaps correctly
       ; eps <- getEps
       ; let inst_envs  = (eps_fam_inst_env eps, home_fie')
             home_fie'' = extendFamInstEnv home_fie fam_inst

           -- Check for conflicting instance decls and injectivity violations
       ; no_conflict    <- checkForConflicts            inst_envs fam_inst
       ; injectivity_ok <- checkForInjectivityConflicts inst_envs fam_inst

       ; if no_conflict && injectivity_ok then
            return (home_fie'', fam_inst : my_fis)
         else
            return (home_fie,   my_fis) }

{-
************************************************************************
*                                                                      *
        Checking an instance against conflicts with an instance env
*                                                                      *
************************************************************************

Check whether a single family instance conflicts with those in two instance
environments (one for the EPS and one for the HPT).
-}

checkForConflicts :: FamInstEnvs -> FamInst -> TcM Bool
checkForConflicts inst_envs fam_inst
  = do { let conflicts = lookupFamInstEnvConflicts inst_envs fam_inst
             no_conflicts = null conflicts
       ; traceTc "checkForConflicts" $
         vcat [ ppr (map fim_instance conflicts)
              , ppr fam_inst
              -- , ppr inst_envs
         ]
       ; unless no_conflicts $ conflictInstErr fam_inst conflicts
       ; return no_conflicts }

-- | Checks whether a new open type family equation can be added without
-- violating injectivity annotation supplied by the user. Returns True when
-- this is possible and False if adding this equation would violate injectivity
-- annotation.
checkForInjectivityConflicts :: FamInstEnvs -> FamInst -> TcM Bool
checkForInjectivityConflicts instEnvs famInst
    | isTypeFamilyTyCon tycon
      -- type family is injective in at least one argument
    , Just inj <- familyTyConInjectivityInfo tycon = do
    { let -- see Note [Injectivity annotation check] in FamInstEnv
          errs = makeInjectivityErrors famInst inj fi_tys fi_rhs
                     (lookupFamInstEnvInjectivityConflicts inj instEnvs famInst)
                     (conflictInjInstErr     makeFamInstsErr)
                     (unusedInjectiveVarsErr makeFamInstsErr)
                     (tfHeadedErr            makeFamInstsErr)
                     (bareVariableInRHSErr   makeFamInstsErr)
    ; mapM_ (\(err, span) -> setSrcSpan span $ addErr err) errs
    ; return (null errs)
    }
    -- if there was no injectivity annotation or tycon does not represent a
    -- type family we report no conflicts
    | otherwise = return True
    where tycon = famInstTyCon famInst

-- | Builds a list of injectivity errors together with their source locations.
-- This combinator gathers common error-checking logic for open and closed type
-- families.
makeInjectivityErrors
   :: a                                  -- Thing for which we perform checks
                                         -- and generate injectivity errors
                                         -- (FamInst or CoAxBranch)
   -> [Bool]                             -- Injectivity annotation
   -> (a -> [Type])                      -- Accessing types in the LHS of thing
   -> (a ->  Type )                      -- Accessing the RHS of thing
   -> [a]                                -- List of injectivity conflicts
   -> (a -> [a]      -> (SDoc, SrcSpan)) -- Generates errors for inj. conflicts
   -> (a -> TyVarSet -> (SDoc, SrcSpan)) -- Ditto for unused injective vars
   -> (a             -> (SDoc, SrcSpan)) -- Ditto for top-level type families
   -> (a -> [Type]   -> (SDoc, SrcSpan)) -- Ditto for bare variable in RHS
   -> [(SDoc, SrcSpan)]
makeInjectivityErrors thing inj lhs rhs conflicts conflictErr unusedInjVarsErr
    tfHeadedErr bareVarInRHSErr =
  let are_conflicts  = not $ null conflicts
      unused_inj_tvs = unusedInjTvsInRHS inj (lhs thing) (rhs thing)
      inj_tvs_unused = not $ isEmptyVarSet unused_inj_tvs
      tf_headed      = isTFHeaded (rhs thing)
      bare_variables = bareTvInRHSViolated (lhs thing) (rhs thing)
      wrong_bare_rhs = not $ null bare_variables
      errorIf p f    = if p then [f] else []
   in    errorIf are_conflicts  (conflictErr      thing conflicts     )
      ++ errorIf inj_tvs_unused (unusedInjVarsErr thing unused_inj_tvs)
      ++ errorIf tf_headed      (tfHeadedErr      thing               )
      ++ errorIf wrong_bare_rhs (bareVarInRHSErr  thing bare_variables)


conflictInstErr :: FamInst -> [FamInstMatch] -> TcRn ()
conflictInstErr fam_inst conflictingMatch
  | (FamInstMatch { fim_instance = confInst }) : _ <- conflictingMatch
  = let (err, span) = makeFamInstsErr
                            (text "Conflicting family instance declarations:")
                            [fam_inst, confInst]
    in setSrcSpan span $ addErr err
  | otherwise
  = panic "conflictInstErr"

-- | Type of functions that use error message and a list of things (FamInst or
-- CoAxiom) to build full error message (with a source location) for injective
-- type families.
type InjErrorBuilder a = SDoc -> [a] -> (SDoc, SrcSpan)

-- | Build error message for equations violating injectivity annotation.
conflictInjInstErr :: InjErrorBuilder a -> a -> [a] -> (SDoc, SrcSpan)
conflictInjInstErr errorBuilder tyfamEqn conflictingEqns
  | confEqn : _ <- conflictingEqns
  = errorBuilder empty [confEqn, tyfamEqn]
  | otherwise
  = panic "conflictInjInstErr"

-- | Build error message for equation with injective type variables unused in
-- the RHS.
unusedInjectiveVarsErr :: InjErrorBuilder a -> a -> TyVarSet -> (SDoc, SrcSpan)
unusedInjectiveVarsErr errorBuilder tyfamEqn unused_tyvars
  = errorBuilder (mkUnusedInjectiveVarsErr unused_tyvars) [tyfamEqn]

-- | Build error message for equation that has a type family call at the top
-- level of RHS
tfHeadedErr :: InjErrorBuilder a -> a -> (SDoc, SrcSpan)
tfHeadedErr errorBuilder famInst
  = errorBuilder (text "RHS of injective type family equation cannot" <+>
                  text "be a type family:") [famInst]

-- | Build error message for equation that has a bare type variable in the RHS
-- but LHS pattern is not a bare type variable.
bareVariableInRHSErr :: InjErrorBuilder a -> a -> [Type] -> (SDoc, SrcSpan)
bareVariableInRHSErr errorBuilder famInst tys
  = errorBuilder (text "RHS of injective type family equation is a bare" <+>
                  text "type variable" $$
                  text "but these LHS type and kind patterns are not bare" <+>
                  text "variables:" <+> pprQuotedList tys) [famInst]


-- | Error message for injective type variables unused in the RHS.
mkUnusedInjectiveVarsErr :: TyVarSet -> SDoc
mkUnusedInjectiveVarsErr unused_tyvars =
    let tyVars = varSetElems $ filterVarSet isTypeVar unused_tyvars
        kiVars = varSetElems $ filterVarSet isKindVar unused_tyvars
        tyVarsSDoc
            = if not (null tyVars)
              then text "Injective type variable" <> plural tyVars <+>
                   pprQuotedList tyVars <+> doOrDoes tyVars <+>
                   text "not appear on injective position."
              else empty
        kiVarsSDoc
            = if not (null kiVars)
              then text "Injective kind variable" <> plural kiVars <+>
                   pprQuotedList kiVars <+> isOrAre kiVars <+>
                   text "not inferable from the RHS type variables."
              else empty
    in tyVarsSDoc $$ kiVarsSDoc $$ text "In the RHS of type family equation:"

makeFamInstsErr :: SDoc -> [FamInst] -> (SDoc, SrcSpan)
makeFamInstsErr herald insts
  = ASSERT( not (null insts) )
    ( hang herald'
         2 (vcat [ pprCoAxBranchHdr (famInstAxiom fi) 0
                 | fi <- sorted ])
    , srcSpan )
 where
   herald' = text "Type family equation" <> plural insts <+> text "violate" <>
             thirdPerson insts <+> text "injectivity annotation" <>
             irregularPlural insts dot colon $$ herald
             -- Above is an ugly hack.  We want this: "sentence. herald:" (note
             -- the dot and colon).  But if herald is empty we want "sentence:"
             -- (note the colon).  We can't test herald for emptiness so we rely
             -- on the fact that herald is empty only when there is more than
             -- one element in insts.  If herald is non empty it must end with a
             -- colon.
   getSpan = getSrcLoc . famInstAxiom
   sorted  = sortWith getSpan insts
   fi1     = head sorted
   srcSpan = coAxBranchSpan (coAxiomSingleBranch (famInstAxiom fi1))
   -- The sortWith just arranges that instances are dislayed in order
   -- of source location, which reduced wobbling in error messages,
   -- and is better for users

tcGetFamInstEnvs :: TcM FamInstEnvs
-- Gets both the external-package inst-env
-- and the home-pkg inst env (includes module being compiled)
tcGetFamInstEnvs
  = do { eps <- getEps; env <- getGblEnv
       ; return (eps_fam_inst_env eps, tcg_fam_inst_env env) }
