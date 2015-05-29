{-# LANGUAGE TemplateHaskell, FlexibleInstances,
             UndecidableInstances, OverlappingInstances, CPP,
             MultiParamTypeClasses #-}
#if MIN_VERSION_base(4,7,0)
{-# LANGUAGE StandaloneDeriving, DeriveDataTypeable #-}
#endif
{-# OPTIONS_GHC -fno-warn-orphans #-}
-- This is a module full of orphans, so don't warn about them

module Data.Generics.SYB.WithClass.Instances () where

import Data.Generics.SYB.WithClass.Basics
import Data.Generics.SYB.WithClass.Derive

import Data.Array
import Data.ByteString.Char8 (ByteString)
import qualified Data.ByteString.Lazy as L (ByteString)
import Data.Int              -- So we can give Data instance for Int8, ...
import Data.Word             -- So we can give Data instance for Word8, ...
import GHC.Real( Ratio(..) ) -- So we can give Data instance for Ratio
import System.IO             -- So we can give Data instance for IO, Handle
import GHC.Ptr               -- So we can give Data instance for Ptr
import GHC.ForeignPtr        -- So we can give Data instance for ForeignPtr
import GHC.Stable            -- So we can give Data instance for StablePtr
import GHC.ST                -- So we can give Data instance for ST
import Data.IORef            -- So we can give Data instance for IORef
import Control.Concurrent.MVar   -- So we can give Data instance for MVar & Co.
import qualified Data.Map as M
import qualified Data.Set as S

------------------------------------------------------------------------------
--
-- Instances of the Data class for Prelude-like types.
-- We define top-level definitions for representations.
--
------------------------------------------------------------------------------


falseConstr :: Constr
falseConstr  = mkConstr boolDataType "False" [] Prefix
trueConstr :: Constr
trueConstr   = mkConstr boolDataType "True"  [] Prefix
boolDataType :: DataType
boolDataType = mkDataType "Prelude.Bool" [falseConstr,trueConstr]

instance Sat (ctx Bool) =>
         Data ctx Bool where
  toConstr _ False = falseConstr
  toConstr _ True  = trueConstr
  gunfold _ _ z c  = case constrIndex c of
                       1 -> z False
                       2 -> z True
                       _ -> error "gunfold Bool"
  dataTypeOf _ _ = boolDataType


------------------------------------------------------------------------------


charType :: DataType
charType = mkStringType "Prelude.Char"

instance Sat (ctx Char) =>
         Data ctx Char where
  toConstr _ x = mkStringConstr charType [x]
  gunfold _ _ z c = case constrRep c of
                      (StringConstr [x]) -> z x
                      _ -> error "gunfold Char"
  dataTypeOf _ _ = charType


------------------------------------------------------------------------------


floatType :: DataType
floatType = mkFloatType "Prelude.Float"

instance Sat (ctx Float) =>
         Data ctx Float where
  toConstr _ x = mkFloatConstr floatType (realToFrac x)
  gunfold _ _ z c = case constrRep c of
                      (FloatConstr x) -> z (realToFrac x)
                      _ -> error "gunfold Float"
  dataTypeOf _ _ = floatType


------------------------------------------------------------------------------


doubleType :: DataType
doubleType = mkFloatType "Prelude.Double"

instance Sat (ctx Double) =>
         Data ctx Double where
  toConstr _ = mkFloatConstr floatType
  gunfold _ _ z c = case constrRep c of
                      (FloatConstr x) -> z x
                      _ -> error "gunfold Double"
  dataTypeOf _ _ = doubleType


------------------------------------------------------------------------------


intType :: DataType
intType = mkIntType "Prelude.Int"

instance Sat (ctx Int) =>
         Data ctx Int where
  toConstr _ x = mkIntConstr intType (fromIntegral x)
  gunfold _ _ z c = case constrRep c of
                      (IntConstr x) -> z (fromIntegral x)
                      _ -> error "gunfold Int"
  dataTypeOf _ _ = intType


------------------------------------------------------------------------------


integerType :: DataType
integerType = mkIntType "Prelude.Integer"

instance Sat (ctx Integer) =>
         Data ctx Integer where
  toConstr _ = mkIntConstr integerType
  gunfold _ _ z c = case constrRep c of
                      (IntConstr x) -> z x
                      _ -> error "gunfold Integer"
  dataTypeOf _ _ = integerType


------------------------------------------------------------------------------


int8Type :: DataType
int8Type = mkIntType "Data.Int.Int8"

instance Sat (ctx Int8) =>
         Data ctx Int8 where
  toConstr _ x = mkIntConstr int8Type (fromIntegral x)
  gunfold _ _ z c = case constrRep c of
                      (IntConstr x) -> z (fromIntegral x)
                      _ -> error "gunfold Int8"
  dataTypeOf _ _ = int8Type


------------------------------------------------------------------------------


int16Type :: DataType
int16Type = mkIntType "Data.Int.Int16"

instance Sat (ctx Int16) =>
         Data ctx Int16 where
  toConstr _ x = mkIntConstr int16Type (fromIntegral x)
  gunfold _ _ z c = case constrRep c of
                      (IntConstr x) -> z (fromIntegral x)
                      _ -> error "gunfold Int16"
  dataTypeOf _ _ = int16Type


------------------------------------------------------------------------------


int32Type :: DataType
int32Type = mkIntType "Data.Int.Int32"

instance Sat (ctx Int32) =>
         Data ctx Int32 where
  toConstr _ x = mkIntConstr int32Type (fromIntegral x)
  gunfold _ _ z c = case constrRep c of
                      (IntConstr x) -> z (fromIntegral x)
                      _ -> error "gunfold Int32"
  dataTypeOf _ _ = int32Type


------------------------------------------------------------------------------


int64Type :: DataType
int64Type = mkIntType "Data.Int.Int64"

instance Sat (ctx Int64) =>
         Data ctx Int64 where
  toConstr _ x = mkIntConstr int64Type (fromIntegral x)
  gunfold _ _ z c = case constrRep c of
                      (IntConstr x) -> z (fromIntegral x)
                      _ -> error "gunfold Int64"
  dataTypeOf _ _ = int64Type


------------------------------------------------------------------------------


wordType :: DataType
wordType = mkIntType "Data.Word.Word"

instance Sat (ctx Word) =>
         Data ctx Word where
  toConstr _ x = mkIntConstr wordType (fromIntegral x)
  gunfold _ _ z c = case constrRep c of
                      (IntConstr x) -> z (fromIntegral x)
                      _ -> error "gunfold Word"
  dataTypeOf _ _ = wordType


------------------------------------------------------------------------------


word8Type :: DataType
word8Type = mkIntType "Data.Word.Word8"

instance Sat (ctx Word8) =>
         Data ctx Word8 where
  toConstr _ x = mkIntConstr word8Type (fromIntegral x)
  gunfold _ _ z c = case constrRep c of
                      (IntConstr x) -> z (fromIntegral x)
                      _ -> error "gunfold Word8"
  dataTypeOf _ _ = word8Type


------------------------------------------------------------------------------


word16Type :: DataType
word16Type = mkIntType "Data.Word.Word16"

instance Sat (ctx Word16) =>
         Data ctx Word16 where
  toConstr _ x = mkIntConstr word16Type (fromIntegral x)
  gunfold _ _ z c = case constrRep c of
                      (IntConstr x) -> z (fromIntegral x)
                      _ -> error "gunfold Word16"
  dataTypeOf _ _ = word16Type


------------------------------------------------------------------------------


word32Type :: DataType
word32Type = mkIntType "Data.Word.Word32"

instance Sat (ctx Word32) =>
         Data ctx Word32 where
  toConstr _ x = mkIntConstr word32Type (fromIntegral x)
  gunfold _ _ z c = case constrRep c of
                      (IntConstr x) -> z (fromIntegral x)
                      _ -> error "gunfold Word32"
  dataTypeOf _ _ = word32Type


------------------------------------------------------------------------------


word64Type :: DataType
word64Type = mkIntType "Data.Word.Word64"

instance Sat (ctx Word64) =>
         Data ctx Word64 where
  toConstr _ x = mkIntConstr word64Type (fromIntegral x)
  gunfold _ _ z c = case constrRep c of
                      (IntConstr x) -> z (fromIntegral x)
                      _ -> error "gunfold Word64"
  dataTypeOf _ _ = word64Type




------------------------------------------------------------------------------


ratioConstr :: Constr
ratioConstr = mkConstr ratioDataType ":%" [] Infix
ratioDataType :: DataType
ratioDataType = mkDataType "GHC.Real.Ratio" [ratioConstr]

instance (Sat (ctx (Ratio a)), Data ctx a, Integral a) =>
          Data ctx (Ratio a) where
  toConstr _ _ = ratioConstr
  gunfold _ k z c | constrIndex c == 1 = k (k (z (:%)))
  gunfold _ _ _ _ = error "gunfold Ratio"
  dataTypeOf _ _  = ratioDataType


------------------------------------------------------------------------------


nilConstr :: Constr
nilConstr    = mkConstr listDataType "[]" [] Prefix
consConstr :: Constr
consConstr   = mkConstr listDataType "(:)" [] Infix
listDataType :: DataType
listDataType = mkDataType "Prelude.[]" [nilConstr,consConstr]

instance (Sat (ctx [a]), Data ctx a) =>
         Data ctx [a] where
  gfoldl _ _ z []     = z []
  gfoldl _ f z (x:xs) = z (:) `f` x `f` xs
  toConstr _ []    = nilConstr
  toConstr _ (_:_) = consConstr
  gunfold _ k z c = case constrIndex c of
                      1 -> z []
                      2 -> k (k (z (:)))
                      _ -> error "gunfold List"
  dataTypeOf _ _ = listDataType
  dataCast1 _ f = gcast1 f

------------------------------------------------------------------------------


nothingConstr :: Constr
nothingConstr = mkConstr maybeDataType "Nothing" [] Prefix
justConstr :: Constr
justConstr    = mkConstr maybeDataType "Just"    [] Prefix
maybeDataType :: DataType
maybeDataType = mkDataType "Prelude.Maybe" [nothingConstr,justConstr]

instance (Sat (ctx (Maybe a)), Data ctx a) =>
          Data ctx (Maybe a) where
  gfoldl _ _ z Nothing  = z Nothing
  gfoldl _ f z (Just x) = z Just `f` x
  toConstr _ Nothing  = nothingConstr
  toConstr _ (Just _) = justConstr
  gunfold _ k z c = case constrIndex c of
                      1 -> z Nothing
                      2 -> k (z Just)
                      _ -> error "gunfold Maybe"
  dataTypeOf _ _ = maybeDataType
  dataCast1 _ f  = gcast1 f


------------------------------------------------------------------------------


ltConstr :: Constr
ltConstr         = mkConstr orderingDataType "LT" [] Prefix
eqConstr :: Constr
eqConstr         = mkConstr orderingDataType "EQ" [] Prefix
gtConstr :: Constr
gtConstr         = mkConstr orderingDataType "GT" [] Prefix
orderingDataType :: DataType
orderingDataType = mkDataType "Prelude.Ordering" [ltConstr,eqConstr,gtConstr]

instance Sat (ctx Ordering) =>
         Data ctx Ordering where
  gfoldl _ _ z LT  = z LT
  gfoldl _ _ z EQ  = z EQ
  gfoldl _ _ z GT  = z GT
  toConstr _ LT  = ltConstr
  toConstr _ EQ  = eqConstr
  toConstr _ GT  = gtConstr
  gunfold _ _ z c = case constrIndex c of
                      1 -> z LT
                      2 -> z EQ
                      3 -> z GT
                      _ -> error "gunfold Ordering"
  dataTypeOf _ _ = orderingDataType


------------------------------------------------------------------------------


leftConstr :: Constr
leftConstr     = mkConstr eitherDataType "Left"  [] Prefix
rightConstr :: Constr
rightConstr    = mkConstr eitherDataType "Right" [] Prefix
eitherDataType :: DataType
eitherDataType = mkDataType "Prelude.Either" [leftConstr,rightConstr]

instance (Sat (ctx (Either a b)), Data ctx a, Data ctx b) =>
          Data ctx (Either a b) where
  gfoldl _ f z (Left a)   = z Left  `f` a
  gfoldl _ f z (Right a)  = z Right `f` a
  toConstr _ (Left _)  = leftConstr
  toConstr _ (Right _) = rightConstr
  gunfold _ k z c = case constrIndex c of
                      1 -> k (z Left)
                      2 -> k (z Right)
                      _ -> error "gunfold Either"
  dataTypeOf _ _ = eitherDataType
  dataCast2 _ f  = gcast2 f


------------------------------------------------------------------------------


--
-- A last resort for functions
--

instance (Sat (ctx (a -> b)), Data ctx a, Data ctx b) =>
          Data ctx (a -> b) where
  toConstr _ _   = error "toConstr"
  gunfold _ _ _  = error "gunfold (->)"
  dataTypeOf _ _ = mkNorepType "Prelude.(->)"
  dataCast2 _ f  = gcast2 f


------------------------------------------------------------------------------


tuple0Constr :: Constr
tuple0Constr = mkConstr tuple0DataType "()" [] Prefix
tuple0DataType :: DataType
tuple0DataType = mkDataType "Prelude.()" [tuple0Constr]

instance (Sat (ctx ())) =>
          Data ctx () where
  toConstr _ _    = tuple0Constr
  gunfold _ _ z c | constrIndex c == 1 = z ()
  gunfold _ _ _ _ = error "gunfold ()"
  dataTypeOf _ _  = tuple0DataType


------------------------------------------------------------------------------


tuple2Constr :: Constr
tuple2Constr = mkConstr tuple2DataType "(,)" [] Infix
tuple2DataType :: DataType
tuple2DataType = mkDataType "Prelude.(,)" [tuple2Constr]

instance (Sat (ctx (a,b)), Data ctx a, Data ctx b) =>
          Data ctx (a,b) where
  gfoldl _ f z (a,b) = z (,) `f` a `f` b
  toConstr _ _    = tuple2Constr
  gunfold _ k z c | constrIndex c == 1 = k (k (z (,)))
  gunfold _ _ _ _ = error "gunfold (,)"
  dataTypeOf _ _  = tuple2DataType
  dataCast2 _ f   = gcast2 f


------------------------------------------------------------------------------


tuple3Constr :: Constr
tuple3Constr = mkConstr tuple3DataType "(,,)" [] Infix
tuple3DataType :: DataType
tuple3DataType = mkDataType "Prelude.(,)" [tuple3Constr]

instance (Sat (ctx (a,b,c)), Data ctx a, Data ctx b, Data ctx c) =>
          Data ctx (a,b,c) where
  gfoldl _ f z (a,b,c) = z (,,) `f` a `f` b `f` c
  toConstr _ _    = tuple3Constr
  gunfold _ k z c | constrIndex c == 1 = k (k (k (z (,,))))
  gunfold _ _ _ _ = error "gunfold (,,)"
  dataTypeOf _ _  = tuple3DataType

------------------------------------------------------------------------------


tuple4Constr :: Constr
tuple4Constr = mkConstr tuple4DataType "(,,,)" [] Infix
tuple4DataType :: DataType
tuple4DataType = mkDataType "Prelude.(,,,)" [tuple4Constr]

instance (Sat (ctx (a,b,c,d)), Data ctx a, Data ctx b, Data ctx c, Data ctx d) =>
          Data ctx (a,b,c,d) where
  gfoldl _ f z (a,b,c,d) = z (,,,) `f` a `f` b `f` c `f` d
  toConstr _ _ = tuple4Constr
  gunfold _ k z c = case constrIndex c of
                      1 -> k (k (k (k (z (,,,)))))
                      _ -> error "gunfold (,,,)"
  dataTypeOf _ _ = tuple4DataType


------------------------------------------------------------------------------


tuple5Constr :: Constr
tuple5Constr = mkConstr tuple5DataType "(,,,,)" [] Infix
tuple5DataType :: DataType
tuple5DataType = mkDataType "Prelude.(,,,,)" [tuple5Constr]

instance (Sat (ctx (a,b,c,d,e)), Data ctx a, Data ctx b, Data ctx c, Data ctx d, Data ctx e) =>
          Data ctx (a,b,c,d,e) where
  gfoldl _ f z (a,b,c,d,e) = z (,,,,) `f` a `f` b `f` c `f` d `f` e
  toConstr _ _ = tuple5Constr
  gunfold _ k z c = case constrIndex c of
                      1 -> k (k (k (k (k (z (,,,,))))))
                      _ -> error "gunfold (,,,,)"
  dataTypeOf _ _ = tuple5DataType


------------------------------------------------------------------------------


tuple6Constr :: Constr
tuple6Constr = mkConstr tuple6DataType "(,,,,,)" [] Infix
tuple6DataType :: DataType
tuple6DataType = mkDataType "Prelude.(,,,,,)" [tuple6Constr]

instance (Sat (ctx (a,b,c,d,e,f)), Data ctx a, Data ctx b, Data ctx c, Data ctx d, Data ctx e, Data ctx f) =>
          Data ctx (a,b,c,d,e,f) where
  gfoldl _ f z (a,b,c,d,e,f') = z (,,,,,) `f` a `f` b `f` c `f` d `f` e `f` f'
  toConstr _ _ = tuple6Constr
  gunfold _ k z c = case constrIndex c of
                      1 -> k (k (k (k (k (k (z (,,,,,)))))))
                      _ -> error "gunfold (,,,,,)"
  dataTypeOf _ _ = tuple6DataType


------------------------------------------------------------------------------


tuple7Constr :: Constr
tuple7Constr = mkConstr tuple7DataType "(,,,,,,)" [] Infix
tuple7DataType :: DataType
tuple7DataType = mkDataType "Prelude.(,,,,,,)" [tuple7Constr]

instance (Sat (ctx (a,b,c,d,e,f,g)), Data ctx a, Data ctx b, Data ctx c, Data ctx d, Data ctx e, Data ctx f, Data ctx g) =>
          Data ctx (a,b,c,d,e,f,g) where
  gfoldl _ f z (a,b,c,d,e,f',g) =
    z (,,,,,,) `f` a `f` b `f` c `f` d `f` e `f` f' `f` g
  toConstr _ _ = tuple7Constr
  gunfold _ k z c = case constrIndex c of
                      1 -> k (k (k (k (k (k (k (z (,,,,,,))))))))
                      _ -> error "gunfold (,,,,,,)"
  dataTypeOf _ _ = tuple7DataType


------------------------------------------------------------------------------


instance Sat (ctx TypeRep) =>
         Data ctx TypeRep where
  toConstr _ _   = error "toConstr"
  gunfold _ _ _  = error "gunfold TypeRep"
  dataTypeOf _ _ = mkNorepType "Data.Typeable.TypeRep"


------------------------------------------------------------------------------


instance Sat (ctx TyCon) =>
         Data ctx TyCon where
  toConstr _ _   = error "toConstr"
  gunfold _ _ _  = error "gunfold TyCon"
  dataTypeOf _ _ = mkNorepType "Data.Typeable.TyCon"


------------------------------------------------------------------------------


-- INSTANCE_TYPEABLE0(DataType,dataTypeTc,"DataType")
#if MIN_VERSION_base(4,7,0)
deriving instance Typeable DataType
#else
#ifndef __HADDOCK__
$(deriveTypeable [''DataType])
#endif
#endif

instance Sat (ctx DataType) =>
         Data ctx DataType where
  toConstr _ _   = error "toConstr"
  gunfold _ _ _  = error "gunfold DataType"
  dataTypeOf _ _ = mkNorepType "Data.Generics.Basics.DataType"


------------------------------------------------------------------------------


instance (Sat (ctx (IO a)), Typeable a) =>
          Data ctx (IO a) where
  toConstr _ _   = error "toConstr"
  gunfold _ _ _  = error "gunfold IO"
  dataTypeOf _ _ = mkNorepType "GHC.IOBase.IO"


------------------------------------------------------------------------------


instance Sat (ctx Handle) =>
         Data ctx Handle where
  toConstr _ _   = error "toConstr"
  gunfold _ _ _  = error "gunfold Handle"
  dataTypeOf _ _ = mkNorepType "GHC.IOBase.Handle"


------------------------------------------------------------------------------


instance (Sat (ctx (Ptr a)), Typeable a) =>
          Data ctx (Ptr a) where
  toConstr _ _   = error "toConstr"
  gunfold _ _ _  = error "gunfold Ptr"
  dataTypeOf _ _ = mkNorepType "GHC.Ptr.Ptr"


------------------------------------------------------------------------------


instance (Sat (ctx (StablePtr a)), Typeable a) =>
          Data ctx (StablePtr a) where
  toConstr _ _   = error "toConstr"
  gunfold _ _ _  = error "gunfold StablePtr"
  dataTypeOf _ _ = mkNorepType "GHC.Stable.StablePtr"


------------------------------------------------------------------------------


instance (Sat (ctx (IORef a)), Typeable a) =>
          Data ctx (IORef a) where
  toConstr _ _   = error "toConstr"
  gunfold _ _ _  = error "gunfold IORef"
  dataTypeOf _ _ = mkNorepType "GHC.IOBase.IORef"


------------------------------------------------------------------------------


instance (Sat (ctx (ForeignPtr a)), Typeable a) =>
          Data ctx (ForeignPtr a) where
  toConstr _ _   = error "toConstr"
  gunfold _ _ _  = error "gunfold ForeignPtr"
  dataTypeOf _ _ = mkNorepType "GHC.ForeignPtr.ForeignPtr"


------------------------------------------------------------------------------


instance (Sat (ctx (ST s a)), Typeable s, Typeable a) =>
          Data ctx (ST s a) where
  toConstr _ _   = error "toConstr"
  gunfold _ _ _  = error "gunfold ST"
  dataTypeOf _ _ = mkNorepType "GHC.ST.ST"


------------------------------------------------------------------------------

{-
instance Sat (ctx ThreadId) =>
         Data ctx ThreadId where
  toConstr _ _   = error "toConstr"
  gunfold _ _ _  = error "gunfold ThreadId"
  dataTypeOf _ _ = mkNorepType "GHC.Conc.ThreadId"


------------------------------------------------------------------------------


instance (Sat (ctx (TVar a)), Typeable a) =>
          Data ctx (TVar a) where
  toConstr _ _   = error "toConstr"
  gunfold _ _ _  = error "gunfold TVar"
  dataTypeOf _ _ = mkNorepType "GHC.Conc.TVar"-}


------------------------------------------------------------------------------


instance (Sat (ctx (MVar a)), Typeable a) =>
          Data ctx (MVar a) where
  toConstr _ _   = error "toConstr"
  gunfold _ _ _  = error "gunfold MVar"
  dataTypeOf _ _ = mkNorepType "GHC.Conc.MVar"


------------------------------------------------------------------------------


{-instance (Sat (ctx (STM a)), Typeable a) =>
          Data ctx (STM a) where
  toConstr _ _   = error "toConstr"
  gunfold _ _ _  = error "gunfold STM"
  dataTypeOf _ _ = mkNorepType "GHC.Conc.STM"-}


------------------------------------------------------------------------------
-- The following instances were adapted from various modules within the Data
-- namespace. Until GHC takes onboard SYB3, they'll have to stay in here.
------------------------------------------------------------------------------

instance (Sat (ctx [b]), Sat (ctx (Array a b)), Typeable a, Data ctx b, Data ctx [b], Ix a) =>
          Data ctx (Array a b) where
  gfoldl _ f z a = z (listArray (bounds a)) `f` (elems a)
  toConstr _ _   = error "toConstr"
  gunfold _ _ _  = error "gunfold Array"
  dataTypeOf _ _ = mkNorepType "Data.Array.Array"

------------------------------------------------------------------------------


emptyMapConstr :: Constr
emptyMapConstr     = mkConstr mapDataType "empty"  [] Prefix
insertMapConstr :: Constr
insertMapConstr    = mkConstr mapDataType "insert" [] Prefix
mapDataType :: DataType
mapDataType = mkDataType "Data.Map.Map" [emptyMapConstr,insertMapConstr]

instance (Sat (ctx (M.Map a b)), Data ctx a, Data ctx b, Ord a) =>
          Data ctx (M.Map a b) where
  gfoldl _ f z m = case M.minViewWithKey m of
                     Nothing -> z M.empty
                     Just ((k,a),m') -> z M.insert `f` k `f` a `f` m' 
  toConstr _ m | M.size m == 0 = emptyMapConstr
               | otherwise     = insertMapConstr
  gunfold _ k z c = case constrIndex c of
                      1 -> z M.empty
                      2 -> k (k (k (z M.insert)))
                      _ -> error "gunfold Map"
  dataTypeOf _ _ = mapDataType
  dataCast2 _ f  = gcast2 f

------------------------------------------------------------------------------


emptySetConstr :: Constr
emptySetConstr     = mkConstr mapDataType "empty"  [] Prefix
insertSetConstr :: Constr
insertSetConstr    = mkConstr mapDataType "insert" [] Prefix
setDataType :: DataType
setDataType = mkDataType "Data.Set.Set" [emptySetConstr,insertSetConstr]

instance (Sat (ctx (S.Set a)), Data ctx a, Ord a) =>
          Data ctx (S.Set a ) where
  gfoldl _ f z s = case S.minView s of
                     Nothing -> z S.empty
                     Just (a,s') -> z S.insert `f` a `f` s' 
  toConstr _ m | S.size m == 0 = emptySetConstr
               | otherwise     = insertSetConstr
  gunfold _ k z c = case constrIndex c of
                      1 -> z S.empty
                      2 -> k (k (z S.insert))
                      _ -> error "gunfold Set"
  dataTypeOf _ _ = setDataType
  dataCast1 _ f  = gcast1 f

------------------------------------------------------------------------------

$( deriveData [''ByteString] )
$( deriveData [''L.ByteString] )
