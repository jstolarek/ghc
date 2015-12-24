module Type where
import TyCon
import Var ( TyVar )
import {-# SOURCE #-} TyCoRep( Type, Kind, VisibilityFlag )

isPredTy     :: Type -> Bool
isCoercionTy :: Type -> Bool

mkAppTy :: Type -> Type -> Type
piResultTy :: Type -> Type -> Type

typeKind :: Type -> Kind
eqType :: Type -> Type -> Bool

coreViewOneStarKind :: Type -> Maybe Type

tagVisibility :: TyCon -> (a -> Type) -> [a] -> [(a,VisibilityFlag)]

coreView :: Type -> Maybe Type

tyCoVarsOfTypesWellScoped :: [Type] -> [TyVar]
