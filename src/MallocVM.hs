{-# LANGUAGE MultiParamTypeClasses, BinaryLiterals #-}
module MallocVM (
  eval,
  run,
  exec,
  VM(..),
  word2obj, obj2word,
  Object(..),
  Insn(..),
  --store, load, 
  alloc,
  testDslFib,
  showSECD,
  evalVM
  ) where
       
import Foreign.Ptr
import Foreign.Marshal.Alloc
import Foreign.Marshal.Array
import Foreign.Storable

import Data.Bits
import Data.Ratio
import Data.Word
import Data.Int
import Data.Maybe
import Control.Monad.State
import Control.Monad

import qualified Test.QuickCheck as Q
import qualified Test.QuickCheck.Monadic as QM

import WordData

type MWord = IntPtr

data VM = VM { regS :: MWord
             , regE :: MWord 
             , regC :: MWord
             , regD :: MWord
             , regFP :: MWord 
             } deriving (Eq, Show)

memorySize :: Int
--memorySize = 1024 * 100
memorySize = 50

--memorySize = 3

initVM :: IO VM
initVM = do
  p <- mallocArray memorySize :: IO (Ptr Int)
  let q = ptrToIntPtr p
  let z = obj2word Nil
  return $ VM z z z z q 

-- Utility
run :: StateT VM IO a -> IO (a, VM)
run f = initVM >>= runStateT f
eval :: StateT VM IO a -> IO a
eval f = initVM >>= evalStateT f
exec :: StateT VM IO a -> IO VM
exec f = initVM >>= execStateT f

-- memory access

-- FIXME allocation error check
alloc :: StateT VM IO ()
alloc = modify $ \(VM s e c d fp) -> VM s e c d (fp + 8)

-- load はポインタを受けとり Object を返す
load :: MWord -> StateT VM IO Object
load p = do { x <- liftIO $ peek (intPtrToPtr p); return $ word2obj x }

store :: MWord -> MWord -> StateT VM IO ()
store p x = liftIO $ poke (intPtrToPtr p) x

-- register access

storeS :: MWord -> StateT VM IO ()
storeS s' = modify $ \vm -> vm { regS = s' }
storeE :: MWord -> StateT VM IO ()
storeE e' = modify $ \vm -> vm { regE = e' }
storeC :: MWord -> StateT VM IO ()
storeC c' = modify $ \vm -> vm { regC = c' }
storeD :: MWord -> StateT VM IO ()
storeD d' = modify $ \vm -> vm { regD = d' }

storeFP :: MWord -> StateT VM IO () 
storeFP fp' = modify $ \vm -> vm { regFP = fp' }

data Insn = NIL | LD | LDC | SEL | JOIN | ATOM | MUL | LDF | CONS | AP | RTN 
          | DUM | RAP | ADD | SUB | LTN | GTN
          deriving (Eq, Ord, Show, Enum)

data Object = Fxnum Fx 
            | Cons MWord MWord
            | Nil
            | B Bool
            | I Insn
            | Omega
            deriving (Eq, Ord)

instance Show Object where
  show (Fxnum n) = "Fxnum " ++ show n
  show (Cons x y) = "Cons " ++ show x ++ " " ++ show y
  show Nil = "Nil"
  show (B x) = "B " ++ show x
  show (I i) = "I " ++ show i
  show Omega = "Omega"

{-
[Object Tags]
---- ---- ---- ---- ---- ---- ---- --00 Fxnum
---- ---- ---- ---- ---- ---- ---- -001 Cons
---- ---- ---- ---- ---- ---- ---- -111 Immediate
[Immediate Tag]
---- ---- ---- ---- ---- ---- 0000 1111 Char
---- ---- ---- ---- ---- ---- 1001 1111 True
---- ---- ---- ---- ---- ---- 0001 1111 False
---- ---- ---- ---- ---- ---- 0100 1111 Nil
  
---- ---- ---- ---- ---- ---- 0000 0111 Insn
---- ---- ---- ---- ---- ---- 1111 0111 Omega
-}

fxnumShift, boolShift, insnShift :: Int
fxnumMask, boolMask, consMask, insnMask :: MWord
fxnumTag, boolTag, consTag, insnTag :: MWord
immediateTrue, immediateFalse, immediateNil, immediateOmega :: MWord
fxnumShift = 2
fxnumMask = 0b11
fxnumTag = 0
boolMask = 0b0011111
boolTag = 0b0011111
immediateTrue =  0b10011111
immediateFalse = 0b00011111
boolShift = 7
consMask = 0b111
consTag = 0b001
insnMask = 0b11111111
insnTag =  0b00000111
insnShift = 8
immediateNil = 0b01001111
immediateOmega = 0b11110111

typeOf :: MWord -> String
typeOf x | (x .&. fxnumMask == fxnumTag) && 
             isFxnum (fromEnum (x `shiftR` fxnumShift)) = "Fxnum"
typeOf x | x .&. boolMask == boolTag = "B"
typeOf x | x .&. consMask == consTag = "Cons"
typeOf x | x .&. insnMask == insnTag = "I"
typeOf x | x == immediateNil = "Nil"
typeOf x | x == immediateOmega = "Omega"
typeOf x = "unkown type" ++ show x


-- Tagged Value
word2obj :: MWord -> Object
word2obj x | (x .&. fxnumMask == fxnumTag) && 
             isFxnum (fromEnum (x `shiftR` fxnumShift)) =
  Fxnum $ fromIntegral (x `shiftR` fxnumShift)

word2obj x | (x .&. fxnumMask == fxnumTag) && 
             not (isFxnum (fromEnum (x `shiftR` fxnumShift))) =
  error $ "fxnumTag, but not in range: " ++ show x

word2obj x | x .&. boolMask == boolTag =
  B (fromEnum (x `shiftR` boolShift) == 1)
word2obj x | x .&. consMask == consTag =
  Cons (x - 1) (x - 1 + 8) -- address 2 つ。
word2obj x | x .&. insnMask == insnTag =
  I (toEnum (fromEnum (x `shiftR` insnShift)))
word2obj x | x == immediateNil = Nil
word2obj x | x == immediateOmega = Omega
word2obj x = error $ "word2obj: Unknown word: " ++ show x

obj2word :: Object -> MWord
obj2word (Fxnum x) = fromIntegral (x `shiftL` fxnumShift)

obj2word (B True) = immediateTrue
obj2word (B False) = immediateFalse
obj2word (Cons x _) = x + 1
obj2word (I i) = toEnum (fromEnum i) `shiftL` insnShift .|. insnTag
obj2word Nil = immediateNil
obj2word Omega = immediateOmega
  
tagCons p = p .|. 1
untagCons p = p `xor` 1

consp p = (ptrToIntPtr p .|. 1) == 1

-- cons, car, obj は Object を処理する
cons :: Object -> Object -> StateT VM IO Object
-- cons x y = do
--   fp <- gets regFP
--   store fp (obj2word x)
--   alloc
--   fp' <- gets regFP
--   store fp' (obj2word y)
--   alloc
--   return $ Cons fp fp'
cons x y = do
  -- malloc
  p <- liftIO $ (mallocArray 2 :: IO (Ptr Int))
  storeFP (ptrToIntPtr p)
  
  fp <- gets regFP
  store fp (obj2word x)
  alloc
  fp' <- gets regFP
  store fp' (obj2word y)
  alloc
  return $ Cons fp fp'

car :: Object -> StateT VM IO Object
car (Cons p _) = load p

cdr :: Object -> StateT VM IO Object
cdr (Cons _ p) = load p

caar = car <=< car
cadr = car <=< cdr
cdar = cdr <=< car
cddr = cdr <=< cdr
caddr = car <=< cdr <=< cdr
cdddr = cdr <=< cdr <=< cdr
cdaar = cdr <=< car <=< car

--
showResult = do
  s <- loadS
  x <- car s
  str <- showObject x
  liftIO $ print str

showVM = showSECD
showSECD = do
  s <- showObject =<< getReg regS
  e <- showObject =<< getReg regE
  c <- showObject =<< getReg regC
  d <- showObject =<< getReg regD
  return $ s ++ " " ++ e ++ " " ++ c ++ " " ++ d

showObject :: Object -> StateT VM IO String
showObject x = case x of
  Fxnum n -> return $ show (toInteger n)
  Cons a b -> showCons a b
  Nil -> return "()"
  B True -> return "#t"
  B False -> return "#f"
  I i -> return $ show i
  Omega -> return "W"

showCons :: MWord -> MWord -> StateT VM IO String
showCons x y = iter1 x y "("
  where
    iter1 :: MWord -> MWord -> String -> StateT VM IO String
    iter1 a b buf = do
      v <- load a
      str <- showObject v
      iter2 b (buf ++ str)
    iter2 :: MWord -> String -> StateT VM IO String
    iter2 b buf = do
      v <- load b
      case v of
        Cons z1 z2 -> iter1 z1 z2 (buf ++ " ")
        Nil -> return $ buf ++ ")"
        _ -> do 
          str <- showObject v
          return $ buf ++ " . " ++ str ++ ")"

--------------------------------
-- DSL
--------------------------------
append x p2 = if x == Nil then
                 return p2
               else do
                 x' <- car x
                 y <- cdr x
                 cons x' =<< append y p2

asm1 :: Insn -> StateT VM IO ()
asm1 i = do
  c <- getReg regC
  p <- cons (I i) Nil
  c' <- append c p
  modify $ \vm -> vm { regC = obj2word c' }
  
nil = asm1 NIL

ldc n = do -- c -> (c LDC n)
  c <- getReg regC
  p <- cons (Fxnum n) Nil
  p' <- cons (I LDC ) p -- (LDC n)
  c' <- append c p' -- (c LDC n)
  modify $ \vm -> vm { regC = obj2word c' }

add = asm1 ADD -- c -> c ADD
sub = asm1 SUB
mul = asm1 MUL
gtn = asm1 GTN
ltn = asm1 LTN

sel ct cf = do
  asm1 SEL
  -- 一旦 (C) から ((C)) を作り、これからロードする
  -- ct と区別できるように保護する。
  c <- getReg regC
  -- 
  ck <- cons c Nil
  modify $ \vm -> vm { regC = obj2word ck }
  -- ct のロード
  ct
  -- ((C) . ct)
  cc <- car =<< getReg regC
  ct' <- cdr =<< getReg regC
  c1 <- append cc =<< cons ct' Nil
  modify $ \vm ->  vm { regC = obj2word c1 }
  -- cf のロード
  c' <- getReg regC
  ck2 <- cons c' Nil
  modify $ \vm -> vm { regC = obj2word ck2 }
  -- (.. (SEL (ct')))
  cf
  -- ((SEL (ct')) . cf)
  cc' <- car =<< getReg regC
  cf' <- cdr =<< getReg regC
  c2 <- append cc' =<< cons cf' Nil
  modify $ \vm -> vm { regC = obj2word c2 }
  
join_ = asm1 JOIN -- c -> c JOIN 
atom = asm1 ATOM -- c -> c ATOM
ld (i, j) = do -- c LD (i . j)
  asm1 LD
  c <- getReg regC  
  p <- cons (Fxnum i) (Fxnum j) -- (i.j)
  p' <- cons p Nil --((i.j))
  c' <- append c p'
  modify $ \vm -> vm { regC = obj2word c' }
  
cons_ = asm1 CONS
rtn = asm1 RTN
ap_ = asm1 AP
-- f は命令列 ex. do { ... }
ldf f = do
  asm1 LDF -- (c -> c LDF)
  c <- getReg regC
  c' <- cons c Nil -- (c LDF)
  modify $ \vm -> vm { regC = obj2word c' }
  f -- 命令を登録 -- (c LDF) (f)
  c'' <- getReg regC
  p <- cdr c'' -- ((f))
  l1 <- car c'' -- (c LDF)
  l2 <- cons p Nil
  c''' <- append l1 l2 -- append (c LDF) ((f))
  modify $ \vm -> vm { regC = obj2word c''' }

dum = asm1 DUM
rap = asm1 RAP
-- DSL end

-- Evaluator
getReg :: MonadState s m => (s -> MWord) -> m Object
getReg f = liftM word2obj $ gets f

loadS :: StateT VM IO Object
loadS = getReg regS
loadE :: StateT VM IO Object
loadE = getReg regE
loadC :: StateT VM IO Object
loadC = getReg regC
loadD :: StateT VM IO Object
loadD = getReg regD

opNIL :: StateT VM IO ()
opNIL = do
  s <- loadS
  c <- loadC
  s' <- cons Nil s
  c' <- cdr c
  modify $ \vm -> vm { regS = obj2word s', regC = obj2word c' }

-- s e (LDC x.c) d -> (x.s) e c d
opLDC :: StateT VM IO ()
opLDC = do
  n <- cadr =<< loadC
  s' <- cons n =<< loadS
  c' <- cddr =<< loadC
  modify $ \vm -> vm { regS = obj2word s', regC = obj2word c' }

opSEL :: StateT VM IO ()
opSEL = do -- (x.s) e (SEL ct cf .c') d -> s e cx (c'.d) where cx = ct if x = #t
  s <- loadS
  s' <- cdr s
  x <- car s
  c <- loadC
  ct <- (car <=< cdr) c
  cf <- (car <=< cdr <=< cdr) c
  d <- loadD
  c' <- (cdr <=< cdr <=< cdr) c
  d' <- cons c' d
  cx <- case x of 
    B True -> return ct 
    B False -> return cf
    _ -> error $ "expect B Bool but got: " ++ show x
  modify $ \vm -> vm { regS = obj2word s', regC = obj2word cx, regD = obj2word d' }
  
opJOIN :: StateT VM IO ()  
opJOIN = do -- s e (JOIN.c) (cr.d') -> s e cr d'
  d <- loadD
  cr <- car d
  d' <- cdr d
  modify $ \vm -> vm { regC = obj2word cr, regD = obj2word d' }

opATOM :: StateT VM IO ()
opATOM = do
  s <- loadS
  x <- car s
  s' <- cdr s
  b <- case x of
    Cons _ _ -> return False
    _ -> return True
  s'' <- cons (B b) s'
  c <- loadC
  c' <- cdr c
  modify $ \vm -> vm { regS = obj2word s'', regC = obj2word c' }

-- s e (LD (i.j).c) d   ->  (locate((i.j),e).s) e c d
opLD :: StateT VM IO ()
opLD = do
  s <- loadS
  e <- loadE  
  c <- loadC
  ij <- cadr c
  x <- locate ij e
  --
  s' <- cons x s
  c' <- cddr c
  modify $ \vm -> vm { regS = obj2word s', regC = obj2word c' }


-- list operator
nth 0 p = car p
nth i p = do 
  p' <- cdr p
  nth (i - 1) p'

locate :: Object -> Object -> StateT VM IO Object
locate ij e = do
  Fxnum i <- car ij
  Fxnum j <- cdr ij
  nth (j - 1) =<< nth (i - 1) e

-- binary operation
--  (a b.s) e (OP.c) d   ->   ((a OP b).s) e c d
opBin :: (Object -> Object -> Object) -> StateT VM IO ()
opBin f = do
  s <- cddr =<< loadS
  c <- loadC
  a <- car =<< loadS
  b <- cadr =<< loadS
  s' <- cons (a `f` b) s
  c' <- cdr c
  modify $ \vm -> vm { regS = obj2word s', regC = obj2word c' }

opBinNum :: (Fx -> Fx -> Fx) -> StateT VM IO ()
opBinNum f = opBin $ \(Fxnum a) (Fxnum b) -> Fxnum (a `f` b)

opBinNumBool :: (Fx -> Fx -> Bool) -> StateT VM IO ()
opBinNumBool f = opBin $ \(Fxnum a) (Fxnum b) -> B (a `f` b)

type Op = StateT VM IO ()
-- s e (LDF f.c) d            ->  ((f.e).s) e c d  
opLDF :: Op
opLDF = do
  f <- cadr =<< loadC
  e <- loadE
  p <- cons f e
  s' <- cons p =<< loadS
  c' <- cddr =<< loadC
  modify $ \vm -> vm { regS = obj2word s', regC = obj2word c' }
  
-- (a b.s') e (OP.c) d   ->   ((a.b).s') e c d
opCONS :: Op
opCONS = do
  s <- loadS
  a <- car s
  b <- cadr s
  s' <- cddr s
  p <- cons a b
  s'' <- cons p s'
  c' <- cdr =<< loadC
  modify $ \vm -> vm { regS = obj2word s'', regC = obj2word c' }

-- ((f.e') v.s') e (AP.c') d    ->  NIL (v.e') f (s' e c'.d)  
opAP :: Op
opAP = do
  s <- loadS
  f <- caar s
  e' <- cdar s
  v <- cadr s
  s' <- cddr s
  e <- loadE
  c <- loadC
  c' <- cdr c
  e'' <- cons v e'
  d' <- cons s' =<< cons e =<< cons c' =<< loadD
  modify $ \vm -> vm { regS = obj2word Nil, regE = obj2word e'',
                       regC = obj2word f, regD = obj2word d' }
-- (x.z) e' (RTN.q) (s e c.d) ->  (x.s) e c d  
opRTN :: Op
opRTN = do
  x <- car =<< loadS
  s <- car =<< loadD
  e <- cadr =<< loadD
  c <- caddr =<< loadD
  d <- cdddr =<< loadD
  s' <- cons x s
  modify $ \vm -> vm { regS = obj2word s', regE = obj2word e, 
                       regC = obj2word c, regD = obj2word d }
-- s e (DUM.c) d  ->  s (W.e) c d
opDUM :: Op
opDUM = do
  e' <- cons Omega =<< loadE
  c <- cdr =<< loadC
  modify $ \vm -> vm { regE = obj2word e', regC = obj2word c }
  
-- ((f.(W.e)) v.s') (W.e) (RAP.c) d ->  nil rplaca((W.e),v) f (s' e c.d)
opRAP :: Op
opRAP = do
  f <- caar =<< loadS
  we <- cdar =<< loadS
  v <- cadr =<< loadS
  s' <- cddr =<< loadS
  c <- cdr =<< loadC
  e <- cdr =<< loadE
  rplaca we v
  d' <- cons s' =<< cons e =<< cons c =<< loadD

  modify $ \vm -> vm { regS = obj2word Nil, regE = obj2word we,
                       regC = obj2word f, regD = obj2word d' }

rplaca :: Object -> Object -> StateT VM IO ()                  
rplaca (Cons p _) v = store p (obj2word v)
  
--
evalVM :: StateT VM IO ()  
evalVM = do
  evalVM1;
  c <- loadC
  unless (c == Nil) evalVM

evalVM1 = do
  c <- loadC
  op <- car c
  -- liftIO $ putStrLn (" == " ++ show op ++ " ==")
  case op of
    I x -> case x of
      NIL -> opNIL
      LDC -> opLDC
      ADD -> opBinNum (+)
      SUB -> opBinNum (-)
      MUL -> opBinNum (*)
      LTN -> opBinNumBool (<)
      GTN -> opBinNumBool (>)
      SEL -> opSEL
      JOIN -> opJOIN
      ATOM -> opATOM
      LD -> opLD
      LDF -> opLDF
      CONS -> opCONS
      AP -> opAP
      RTN -> opRTN
      DUM -> opDUM
      RAP -> opRAP
    _ -> error $ "Expect Insn but got: " ++ show op
  return ()
  
-- FIB
-- run $ testDslFib 10 >> evalVM >> showSECD  
testDslFib x = do { 
  dum;
  nil;
  ldf (do { 
          ldc 2;
          ld (1,1);
          ltn;
          sel 
          (do { ld (1,1); join_ })
          (do { nil; ldc 2; ld (1,1); sub; cons_;
                ld (2,1); ap_; nil; ldc 1; ld (1,1);
                sub; cons_; ld (2,1); ap_; add; join_});
          rtn; });
  cons_; 
  ldf (do { nil; ldc x; cons_; ld (1,1); ap_; rtn });
  rap; 
  }

-- hello :: IO ()
-- hello = do { print $ mkMsg } where mkMsg = "Hello, World!"

-- zerop x = do
--   v <- x
--   return $ B (v == Fxnum 0)

-- if' :: StateT VM IO Object -> StateT VM IO Object -> StateT VM IO Object -> StateT VM IO Object
-- if' test conseq alt = do
--   x <- test
--   if x == B True then conseq else alt

-- ltn x y = do
--   Fxnum v1 <- x
--   Fxnum v2 <- y
--   return $ B (v1 < v2)

----------------
-- test
----------------
instance Q.Arbitrary Insn where
  arbitrary = Q.oneof (map return [ NIL .. ])

instance Q.Arbitrary Object where
  arbitrary = Q.oneof [ return Nil 
                      , return $ B True
                      , return $ B False
                      , do { x <- Q.arbitrary; return $ Fxnum x }
                      , do { x <- Q.arbitrary; return $ I x }
                      ]

-- prop_test010 v1 v2 = QM.monadicIO $ do 
--   (y, x) <- QM.run $ eval $ do
--     p0 <- reg regFP
--     -- -- store p x = liftIO $ poke p (obj2word x)
--     liftIO $ poke (intPtrToPtr p0) (obj2word v1)
--     alloc
--     p1 <- reg regFP
--     --store p1 v2
--     liftIO $ poke (intPtrToPtr p1) (obj2word v2)
--     alloc
--     x <- liftIO $ peek (castPtr (intPtrToPtr p0))
--     y <- liftIO $ peek (intPtrToPtr p1)
--     return (y, x)
--   QM.assert $ (v1, v2) == (x, y)

prop_test011 = QM.monadicIO $ do
  (fp0, fp1) <- QM.run $ eval $ do
    fp0 <- gets regFP
    alloc
    alloc
    alloc
    alloc
    fp1 <- gets regFP
    return (fp0, fp1)
  QM.assert $ fp1 > fp0

-- 任意の要素で cons を生成して car/cdr を取得すると元と一致する
prop_test020 v1 v2 = QM.monadicIO $ do 
  (y, x) <- QM.run $ eval $ do
    p <- cons v1 v2
    x <- car p
    y <- cdr p
    return (y, x)
  QM.assert $ (v1, v2) == (x, y)

-- 任意の3要素で cons を生成して取得し、もとの要素と一致する
prop_test021 v1 v2 v3 = QM.monadicIO $ do 
  (a, b, c) <- QM.run $ eval $ do
    p <- cons v1 v2 -- (v1 v2)
    q <- cons v3 p -- (v3 v1 v2)
    x <- car q -- v3
    y <- cdr q -- (v1 v2)
    z <- car y -- v1
    w <- cdr y -- v2
    return (z, w, x)
  QM.assert $ (v1, v2, v3) == (a, b, c)

-- 任意の2要素で list を生成する
prop_test022 v1 v2 = QM.monadicIO $ do 
  (a, b) <- QM.run $ eval $ do
    p <- cons v1 Nil -- (v1)
    q <- cons v2 p -- (v2 v1)
    x <- car q -- v2
    z <- car =<< cdr q
    return (z, x)
  QM.assert $ (v1, v2) == (a, b)

-- 任意の要素で cons を生成して car/cdr を取得すると元と一致する
prop_test030 v1 = QM.monadicIO $ do 
  x <- QM.run $ eval ((car =<<) (cons v1 Nil))
  QM.assert $ x == v1

prop_test031 v1 v2 = QM.monadicIO $ do 
  x <- QM.run $ eval ((cdr =<<) (cons v1 v2))
  QM.assert $ x == v2

-- cadr
prop_test032 v1 v2 = QM.monadicIO $ do 
  -- x <- QM.run $ eval ((car' . cdr') 
  --                     (cons' (return v1) (cons' (return v2) (return Nil))))
  
  -- (car (cdr (cons v1 (cons v1 nil)))) == v2
  x <- QM.run $ eval (((car <=< cdr) =<<)
                      (cons v1 =<< cons v2 Nil))
  QM.assert $ x == v2
-- caddr
-- prop_test033 v1 v2 v3 = QM.monadicIO $ do 
--   x <- QM.run $ eval ((car' . cdr' . cdr') 
--                       (cons' (return v1) 
--                        (cons' (return v2) 
--                         (cons' (return v3) (return Nil)))))
--   QM.assert $ x == v3

-- reg
prop_test040 = QM.monadicIO $ do 
  x <- QM.run $ eval $ do
    -- s を Nil に設定する
    s0 <- gets regS
    storeS (obj2word Nil)
    s' <- gets regS
    return (word2obj s')
  QM.assert $ x == Nil
  
prop_test041 v1 v2 = QM.monadicIO $ do 
  x <- QM.run $ eval $ do
    -- s を v1 . v2 に設定する
    p <- cons v2 Nil -- (v2)
    q <- cons v1 p -- (v1 v2)
    s0 <- gets regS
    storeS (obj2word q)
    s' <- gets regS
    car (word2obj s')
  QM.assert $ x == v1
  
prop_test042 v1 v2 = QM.monadicIO $ do 
  x <- QM.run $ eval $ do
    -- s を (v1 v2 . s) に設定する
    s0 <- gets regS    
    p <- cons v2 (word2obj s0) -- (v2 . s)
    q <- cons v1 p -- (v1 v2 . s)
    storeS (obj2word q)
    s' <- gets regS -- (v1 v2 . s)
    car (word2obj s') -- v1
  QM.assert $ x == v1
  
-- ldc + eval
prop_test050 n = QM.monadicIO $ do
  Fxnum x <- QM.run $ eval $ do
    ldc n
    evalVM
    s <- loadS
    car s
  QM.assert $ x == n

-- binary op
prop_test060 n m = QM.monadicIO $ do
  Fxnum x <- QM.run $ eval $ do
    ldc n
    ldc m
    add
    evalVM
    s <- loadS
    car s
  QM.assert $ x == n + m


-- test000 :: IO MWord
-- test000 = do
--   vm <- initVM
--   poke (regFP vm) 13
--   peek (regFP vm)

-- test001 :: StateT VM IO ()
-- test001 = do
--   vm <- get
--   liftIO $ print vm
--   return ()

-- -- alloc 前後の FP を印字して確認する。
-- test002 :: StateT VM IO ()
-- test002 = do
--   vm <- get
--   liftIO $ print vm
--   alloc
--   liftIO $ print vm
--   return ()

-- test003 :: StateT VM IO ()
-- test003 = do
--   p0 <- reg regFP
--   liftIO $ poke p0 13
--   alloc
--   p1 <- reg regFP
--   liftIO $ poke p1 9
--   alloc
--   x <- liftIO $ peek p0
--   y <- liftIO $ peek p1
--   liftIO $ print x
--   liftIO $ print y
--   return ()

-- | 
-- Word <-> Object conversion.
-- >>> word2obj (obj2word (Fxnum 0))
-- Fxnum Fx 0
-- >>> word2obj (obj2word (Fxnum 13))
-- Fxnum Fx 13
-- >>> word2obj (obj2word (Fxnum 13))
-- Fxnum Fx 13
-- >>> word2obj (obj2word (I NIL))
-- I NIL
-- >>> word2obj (obj2word (I LD))
-- I LD

-- | 
-- Word <-> Object  
-- prop> word2obj (obj2word x) == x

prop_wordobj x = word2obj (obj2word x) == x

prop_insnobj x = word2obj (obj2word (I x)) == I x

-- 循環チェック

cycle1 :: Int -> Int -> [Int]
cycle1 r m = filter (\x -> (x `mod` m) == ((x * r) `mod` m)) [1..]


  