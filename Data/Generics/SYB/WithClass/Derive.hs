{-# LANGUAGE TemplateHaskell, CPP #-}
{-# OPTIONS_GHC -fno-warn-missing-signatures #-}
-- We can't warn about missing sigs as we have a group of decls in
-- quasi-quotes that we're going to put in a class instance

--
-- Ulf Norell, 2004
-- Started this module.
--
-- Sean Seefried, 2004
-- Extension for data definitions with type variables; comments added.
-- http://www.haskell.org/pipermail/template-haskell/2005-January/000393.html
--
-- Simon D. Foster, 2004--2005
-- Extended to work with SYB3.
--
-- Ralf Lammel, 2005
-- Integrated with SYB3 source distribution.
--

module Data.Generics.SYB.WithClass.Derive where

import Language.Haskell.TH
import Data.List
import Control.Monad
import Data.Generics.SYB.WithClass.Basics

--
-- | Takes the name of an algebraic data type, the number of type parameters
--   it has and creates a Typeable instance for it.
deriveTypeablePrim :: Name -> Int -> Q [Dec]
deriveTypeablePrim name nParam
#ifdef __HADDOCK__
 = undefined
#else
 = case index names nParam of
   Just (className, methodName) ->
       let moduleString = case nameModule name of
                          Just m -> m ++ "."
                          Nothing -> ""
           typeString = moduleString ++ nameBase name
#if MIN_VERSION_base(4,7,0)
           body = [| mkTyConApp (mkTyCon3 $(litE $ stringL typeString)) [] |]
#else
           body = [| mkTyConApp (mkTyCon $(litE $ stringL typeString)) [] |]
#endif
           method = funD methodName [clause [wildP] (normalB body) []]
       in sequence [ instanceD (return [])
                               (conT className `appT` conT name)
                               [ method ]
                   ]
   Nothing -> error ("Typeable classes can only have a maximum of " ++
                     show (length names + 1) ++ " parameters")
 where index [] _ = Nothing
       index (x:_) 0 = Just x
       index (_:xs) n = index xs (n - 1)
       names = [(''Typeable, 'typeOf),
                (''Typeable1, 'typeOf1),
                (''Typeable2, 'typeOf2),
                (''Typeable3, 'typeOf3),
                (''Typeable4, 'typeOf4),
                (''Typeable5, 'typeOf5),
                (''Typeable6, 'typeOf6),
                (''Typeable7, 'typeOf7)]
#endif

type Constructor = (Name,         -- Name of the constructor
                    Int,          -- Number of constructor arguments
                    Maybe [Name], -- Name of the field selector, if any
                    [Type])       -- Type of the constructor argument

-- | Takes a name of a algebraic data type, the number of parameters it
--   has and a list of constructor pairs.  Each one of these constructor
--   pairs consists of a constructor name and the number of type
--   parameters it has.  The function returns an automatically generated
--   instance declaration for the Data class.
--
--   Doesn't do gunfold, dataCast1 or dataCast2
deriveDataPrim :: Name -> [Type] -> [Constructor] -> Q [Dec]
deriveDataPrim name typeParams cons =
#ifdef __HADDOCK__
 undefined
#else
 do theDataTypeName <- newName $ "dataType_sybwc_" ++ show name
    constrNames <- mapM (\(conName,_,_,_) -> newName $ "constr_sybwc_" ++ show conName) cons
    let constrExps = map varE constrNames

    let mkConstrDec :: Name -> Constructor -> Q [Dec]
        mkConstrDec decNm (constrName, _, mfs, _) =
          do let constrString = nameBase constrName
                 fieldNames = case mfs of
                              Nothing -> []
                              Just fs -> map nameBase fs
                 fixity (':':_)  = [| Infix |]
                 fixity _        = [| Prefix |]
                 body = [| mkConstr $(varE theDataTypeName)
                                    constrString
                                    fieldNames
                                    $(fixity constrString)
                         |]
             sequence [ sigD decNm [t| Constr |],
                        funD decNm [clause [] (normalB body) []]
                      ]
    conDecss <- zipWithM mkConstrDec constrNames cons
    let conDecs = concat conDecss
    sequence (
     -- Creates
     -- constr :: Constr
     -- constr = mkConstr dataType "DataTypeName" [] Prefix
     map return conDecs ++
     [ -- Creates
       -- dataType :: DataType
       sigD theDataTypeName [t| DataType |]
     , -- Creates
       -- dataType = mkDataType <name> [<constructors]
       let nameStr = nameBase name
           body = [| mkDataType nameStr $(listE constrExps) |]
       in funD theDataTypeName [clause [] (normalB body) []]
     , -- Creates
       -- instance (Data ctx Int, Sat (ctx Int), Sat (ctx DataType))
       --       => Data ctx DataType
       instanceD context (dataCxt myType)
       [ -- Define the gfoldl method
         do f <- newName "_f"
            z <- newName "z"
            x <- newName "x"
            let -- Takes a pair (constructor name, number of type
                -- arguments) and creates the correct definition for
                -- gfoldl. It is of the form
                --     z <constr name> `f` arg1 `f` ... `f` argn
                mkMatch (c, n, _, _)
                 = do args <- replicateM n (newName "arg")
                      let applyF e arg = [| $(varE f) $e $(varE arg) |]
                          body = foldl applyF [| $(varE z) $(conE c) |] args
                      match (conP c $ map varP args) (normalB body) []
                matches = map mkMatch cons
            funD 'gfoldl [ clause (wildP : map varP [f, z, x])
                                  (normalB $ caseE (varE x) matches)
                                  []
                         ]
       , -- Define the gunfold method
         do k <- newName "_k"
            z <- newName "z"
            c <- newName "c"
            let body = if null cons
                       then [| error "gunfold : Type has no constructors" |]
                       else caseE [| constrIndex $(varE c) |] matches
                mkMatch n (cn, i, _, _)
                 = match (litP $ integerL n)
                         (normalB $ reapply (appE (varE k))
                                            i
                                            [| $(varE z) $(conE cn) |]
                         )
                         []
                   where reapply _ 0 f = f
                         reapply x j f = x (reapply x (j-1) f)
                fallThroughMatch
                 = match wildP (normalB [| error "gunfold: fallthrough" |]) []
                matches = zipWith mkMatch [1..] cons ++ [fallThroughMatch]
            funD 'gunfold [clause (wildP : map varP [k, z, c])
                                  (normalB body)
                                  []
                          ]
       , -- Define the toConstr method
         do x <- newName "x"
            let mkSel (c, n, _, _) e = match (conP c $ replicate n wildP)
                                             (normalB e)
                                             []
                body = caseE (varE x) (zipWith mkSel cons constrExps)
            funD 'toConstr [ clause [wildP, varP x]
                                    (normalB body)
                                    []
                           ]
       , -- Define the dataTypeOf method
         funD 'dataTypeOf [ clause [wildP, wildP]
                                   (normalB $ varE theDataTypeName)
                                   []
                          ]
       ]
     ])
 where notTyVar (VarT _) = False
       notTyVar _        = True
       applied (AppT f _) = applied f
       applied x = x
       types = [ t | (_, _, _, ts) <- cons, t <- ts, notTyVar t ]

       myType = foldl AppT (ConT name) typeParams
       dataCxt typ = conT ''Data `appT` varT (mkName "ctx") `appT` return typ
       dataCxt' typ = return $ ClassP ''Data [VarT (mkName "ctx"), typ]
       satCxt typ = return $ ClassP ''Sat [VarT (mkName "ctx") `AppT` typ]
       dataCxtTypes = filter (\x -> applied x /= ConT name) $ nub (typeParams ++ types)
       satCxtTypes = nub (myType : types)
       context = cxt (map dataCxt' dataCxtTypes ++ map satCxt satCxtTypes)
#endif

deriveMinimalData :: Name -> Int  -> Q [Dec]
deriveMinimalData name nParam  = do
#ifdef __HADDOCK__
    undefined
#else
    decs <- qOfDecs
    params <- replicateM nParam (newName "a")
    let typeQParams = map varT params
        context = cxt (map (\typ -> classP ''Data [typ]) typeQParams)
        instanceType = foldl appT (conT name) typeQParams
    inst <-instanceD context
                     (conT ''Data `appT` instanceType)
                     (map return decs)
    return [inst]

 where qOfDecs =
           [d| gunfold _ _ _ = error "gunfold not defined"
               toConstr x    = error ("toConstr not defined for " ++
                                  show (typeOf x))
               dataTypeOf x = error ("dataTypeOf not implemented for " ++
                                show (typeOf x))
               gfoldl _ z x = z x
             |]
#endif

{- instance Data NameSet where
   gunfold _ _ _ = error ("gunfold not implemented")
   toConstr x = error ("toConstr not implemented for " ++ show (typeOf x))
   dataTypeOf x = error ("dataTypeOf not implemented for " ++ show (typeOf x))
   gfoldl f z x = z x -}

typeInfo :: Dec
         -> Q (Name,            -- Name of the datatype
               [Name],          -- Names of the type parameters
               [Constructor])   -- The constructors
typeInfo d
 = case d of
   DataD    _ n ps cs _ -> return (n, map varName ps, map conA cs)
   NewtypeD _ n ps c  _ -> return (n, map varName ps, [conA c])
   _ -> error ("derive: not a data type declaration: " ++ show d)
 where conA (NormalC c xs)   = (c, length xs, Nothing, map snd xs)
       conA (InfixC x1 c x2) = conA (NormalC c [x1, x2])
       conA (ForallC _ _ c)  = conA c
       conA (RecC c xs)      = let getField (n, _, _) = n
                                   getType  (_, _, t) = t
                                   fields = map getField xs
                                   types  = map getType xs
                               in (c, length xs, Just fields, types)
       varName (PlainTV n) = n
       varName (KindedTV n _) = n

--
-- | Derives the Data and Typeable instances for a single given data type.
--
deriveOne :: Name -> Q [Dec]
deriveOne n =
 do info <- reify n
    case info of
        TyConI d -> deriveOneDec d
        _ -> error ("derive: can't be used on anything but a type " ++
                    "constructor of an algebraic data type")

deriveOneDec :: Dec -> Q [Dec]
deriveOneDec dec =
 do (name, param, cs) <- typeInfo dec
    t <- deriveTypeablePrim name (length param)
    d <- deriveDataPrim name (map VarT param) cs
    return (t ++ d)

deriveOneData :: Name -> Q [Dec]
deriveOneData n =
 do info <- reify n
    case info of
        TyConI i -> do
            (name, param, cs) <- typeInfo i
            deriveDataPrim name (map VarT param) cs
        _ -> error ("derive: can't be used on anything but a type " ++
                    "constructor of an algebraic data type")


--
-- | Derives Data and Typeable instances for a list of data
--   types. Order is irrelevant. This should be used in favour of
--   deriveOne since Data and Typeable instances can often depend on
--   other Data and Typeable instances - e.g. if you are deriving a
--   large, mutually recursive data type.  If you splice the derived
--   instances in one by one you will need to do it in depedency order
--   which is difficult in most cases and impossible in the mutually
--   recursive case. It is better to bring all the instances into
--   scope at once.
--
--  e.g. if
--     data Foo = Foo Int
--  is declared in an imported module then
--     $(derive [''Foo])
--  will derive the instances for it
derive :: [Name] -> Q [Dec]
derive names = do
  decss <- mapM deriveOne names
  return (concat decss)


deriveDec :: [Dec] -> Q [Dec]
deriveDec decs = do
  decss <- mapM deriveOneDec decs
  return (concat decss)


deriveData :: [Name] -> Q [Dec]
deriveData names = do
  decss <- mapM deriveOneData names
  return (concat decss)

deriveTypeable :: [Name] -> Q [Dec]
deriveTypeable names = do
  decss <- mapM deriveOneTypeable names
  return (concat decss)

deriveOneTypeable :: Name -> Q [Dec]
deriveOneTypeable n =
 do info <- reify n
    case info of
        TyConI i -> do
             (name, param, _) <- typeInfo i
             deriveTypeablePrim name (length param)
        _ -> error ("derive: can't be used on anything but a type " ++
                    "constructor of an algebraic data type")


--
-- | This function is much like deriveOne except that it brings into
--   scope an instance of Data with minimal definitions. gfoldl will
--   essentially leave a data structure untouched while gunfoldl,
--   toConstr and dataTypeOf will yield errors.
--
--   This function is useful when you are certain that you will never
--   wish to transform a particular data type.  For instance you may
--   be transforming another data type that contains other data types,
--   some of which you wish to transform (perhaps recursively) and
--   some which you just wish to return unchanged.
--
--   Sometimes you will be forced to use deriveMinimalOne because you
--   do not have access to the contructors of the data type (perhaps
--   because it is an Abstract Data Type). However, should the
--   interface to the ADT be sufficiently rich it is possible to
--   define you're own Data and Typeable instances.
deriveMinimalOne :: Name -> Q [Dec]
deriveMinimalOne n =
 do info <- reify n
    case info of
        TyConI i -> do
            (name, param, _) <- typeInfo i
            t <- deriveTypeablePrim name (length param)
            d <- deriveMinimalData name (length param)
            return (t ++ d)
        _ -> error ("deriveMinimal: can't be used on anything but a " ++
                    "type constructor of an algebraic data type")


deriveMinimal :: [Name] -> Q [Dec]
deriveMinimal names = do
   decss <- mapM deriveMinimalOne names
   return (concat decss)

