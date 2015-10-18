{-# LANGUAGE MultiParamTypeClasses, BinaryLiterals #-}
module IORefVM (
  test060,
  initSECD,
  SECD
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
import Data.IORef
import Control.Monad.State
import Control.Monad

import qualified Test.QuickCheck as Q
import qualified Test.QuickCheck.Monadic as QM
--------------------------------------------------------------------------------
-- Value, Cons
--------------------------------------------------------------------------------
data Insn = NIL | LD | LDC | SEL | JOIN | ATOM | MUL | LDF | CONS | AP | RTN 
          | DUM | RAP | ADD | SUB | LTN | GTN
          deriving (Eq, Ord, Show, Enum)

data Value = Fxnum Int | Nil | Ref (IORef Cons) | B Bool | I Insn | W deriving Eq
data Cons = Cons Value Value deriving Eq

instance Show Value where
  show (Fxnum x) = show x
  show Nil = "()"
  show (Ref p) = "#x"
  show (I i) = show i

instance Show Cons where
  show (Cons x y) = "Cons " ++ show x ++ " " ++ show y

car,cdr :: Value -> IO Value
car (Ref p) = do
  Cons a _ <- readIORef p
  return a
car _ = error "car expect cons"

cdr (Ref p) = do
  Cons _ a <- readIORef p
  return a
cdr _ = error "cdr expect cons"
-- cXr
caar,cadr,cdar,cddr,caadr,caddr,cdddr,cdaar,cdadr :: Value -> IO Value
caar = car <=< car
cadr = car <=< cdr
cdar = cdr <=< car
cddr = cdr <=< cdr
caadr = car <=< car <=< cdr
caddr = car <=< cdr <=< cdr
cdddr = cdr <=< cdr <=< cdr
cdaar = cdr <=< car <=< car
cdadr = cdr <=< car <=< cdr
  
cons :: Value -> Value -> IO Value
cons x y = do
  p <- newIORef $ Cons x y
  return $ Ref p

showValue :: Value -> IO ()
showValue (Fxnum x) = putStr (show x)
showValue Nil = putStr "()"
showValue (Ref p) = do
  putStr "("
  v <- readIORef p
  showCons1 v
showValue (I i) = putStr (show i)

showCons1 :: Cons -> IO ()
showCons1 (Cons x y) = do
  showValue x
  showCons2 y

showCons2 :: Value -> IO ()
showCons2 x = case x of
  Nil -> putStr ")"
  Ref p -> do
    putStr " "
    q <- readIORef p
    showCons1 q
  _ -> do
    putStr " . "
    showValue x
    putStr ")"

--
data SECD = SECD Value Value Value Value deriving (Eq, Show)

initSECD = SECD Nil Nil Nil Nil

showSECD :: StateT SECD IO ()
showSECD = do
  SECD s e c d <- get
  liftIO $ showValue s
  liftIO $ putStr " "
  liftIO $ showValue e
  liftIO $ putStr " "
  liftIO $ showValue c
  liftIO $ putStr " "
  liftIO $ showValue d

eval :: StateT SECD IO ()
eval = do
  eval1
  SECD s e c d <- get
  unless (c == Nil) eval

eval1 :: StateT SECD IO ()
eval1 = do
  SECD s e c d <- get
  op <- liftIO $ car c
  -- liftIO $ putStrLn $ "op=" ++ show op
  case op of
    -- s e (NIL.c) d ->  (nil.s) e c d
    I NIL -> do
      s' <- liftIO (cons Nil s)
      c' <- liftIO (cdr c)
      put $ SECD s' e c' d
    -- s e (LDC x.c) d -> (x.s) e c d
    I LDC -> do
      n  <- liftIO (cadr c)
      s' <- liftIO (cons n s)
      c' <- liftIO (cddr c)
      put $ SECD s' e c' d
    -- binOp
    --  (a b.s) e (OP.c) d   ->   ((a OP b).s) e c d
    I ADD -> do
      Fxnum a <- liftIO (car s)
      Fxnum b <- liftIO (cadr s)
      let v = Fxnum (a + b)
      s' <- liftIO (cddr s)
      s'' <- liftIO (cons v s')
      c' <- liftIO (cdr c)
      put $ SECD s'' e c' d
    I SUB -> do
      Fxnum a <- liftIO (car s)
      Fxnum b <- liftIO (cadr s)
      let v = Fxnum (a - b)
      s' <- liftIO (cddr s)
      s'' <- liftIO (cons v s')
      c' <- liftIO (cdr c)
      put $ SECD s'' e c' d
    I LTN -> do
      Fxnum a <- liftIO (car s)
      Fxnum b <- liftIO (cadr s)
      let v = B (a < b)
      s' <- liftIO (cddr s)
      s'' <- liftIO (cons v s')
      c' <- liftIO (cdr c)
      put $ SECD s'' e c' d
    -- I MUL -> opBinNum (*)
    
    -- (x.s) e (SEL ct cf .c) d -> s e cx (c.d) where cx = ct if x = #t
    I SEL -> do
      s' <- liftIO (cdr s)
      x  <- liftIO (car s)
      ct <- liftIO (cadr c)
      cf <- liftIO (caddr c)
      c' <- liftIO (cdddr c)
      d' <- liftIO (cons c' d)
      put $ SECD s' e (if x == B True then ct else cf) d'
    -- s e (JOIN.c) (cr.d') -> s e cr d'
    I JOIN -> do
      cr <- liftIO (car d)
      d' <- liftIO (cdr d)
      put $ SECD s e cr d'
    -- (x.s) e (ATOM.c) d -> (#t.s) e c d
    I ATOM -> do
      x  <- liftIO (car s)
      let b = case x of
            Ref _ -> False
            _ -> True
      s' <- liftIO (cons (B b) s)
      c' <- liftIO (cdr c)
      put $ SECD s' e c' d
    -- s e (LD (i.j).c) d   ->  (locate((i.j),e).s) e c d
    I LD -> do
      i  <- liftIO (caadr c)
      j  <- liftIO (cdadr c)
      x  <- liftIO (locate i j e)
      s' <- liftIO (cons x s)
      c' <- liftIO (cddr c)
      put $ SECD s' e c' d
    -- s e (LDF f.c) d ->  ((f.e).s) e c d  
    I LDF -> do
      f  <- liftIO (cadr c)
      c' <- liftIO (cddr c)
      p  <- liftIO (cons f e)
      s' <- liftIO (cons p s)
      put $ SECD s' e c' d
    -- (a b.s') e (OP.c) d -> ((a.b).s') e c d
    I CONS -> do
      a   <- liftIO (car s)
      b   <- liftIO (cadr s)
      s'  <- liftIO (cddr s)
      p   <- liftIO (cons a b)
      s'' <- liftIO (cons p s')
      c'  <- liftIO (cdr c)
      put $ SECD s'' e c' d
    -- ((f.e') v.s') e (AP.c') d    ->  NIL (v.e') f (s' e c'.d)
    I AP -> do
      f   <- liftIO (caar s)
      e'  <- liftIO (cdar s)
      v   <- liftIO (cadr s)
      s'  <- liftIO (cddr s)
      c'  <- liftIO (cdr c)
      e'' <- liftIO (cons v e')
      d1  <- liftIO (cons c' d)
      d2  <- liftIO (cons e d1)
      d'  <- liftIO (cons s' d2)
      put $ SECD Nil e'' f d'
    -- (x.z) e' (RTN.q) (s e c.d) ->  (x.s) e c d        
    I RTN -> do
      x   <- liftIO (car s)
      s'  <- liftIO (car d)
      e'  <- liftIO (cadr d)
      c'  <- liftIO (caddr d)
      d'  <- liftIO (cdddr d)
      s'' <- liftIO (cons x s')
      put $ SECD s'' e' c' d'
    -- s e (DUM.c) d  ->  s (W.e) c d      
    I DUM -> do
      e'  <- liftIO (cons W e)
      c'  <- liftIO (cdr c)
      put $ SECD s e' c' d
    -- ((f.(W.e)) v.s') (W.e) (RAP.c) d ->  nil rplaca((W.e),v) f (s' e c.d)
    I RAP -> do
      f   <- liftIO (caar s)
      we  <- liftIO (cdar s)
      v   <- liftIO (cadr s)
      s'  <- liftIO (cddr s)
      c'  <- liftIO (cdr c)
      -- rplaca
      let (Ref p) = we
      e' <- liftIO (cdr e)
      liftIO $ writeIORef p (Cons v e')
      --
      d0  <- liftIO (cons c' d)
      d1  <- liftIO (cons e' d0)
      d'  <- liftIO (cons s' d1)
      put $ SECD Nil we f d'
      
nth 0 p = car p
nth i p = do
  p' <- cdr p
  nth (i - 1) p'

locate :: Value -> Value -> Value -> IO Value
locate (Fxnum i) (Fxnum j) e = do
  e' <- nth (i - 1) e
  nth (j - 1) e'

test020 :: StateT SECD IO ()
test020 = do
  SECD s e c d <- get
  s' <- liftIO $ cons (Fxnum 3) s
  modify $ \(SECD s e c d) -> SECD s' e c d
  showSECD
  liftIO $ putStrLn ""

test021 = do
  SECD s e c d <- get
  c' <- liftIO $ cons (I NIL) c
  put $ SECD s e c' d
  showSECD
  liftIO $ putStrLn ""
  eval1
  showSECD
  liftIO $ putStrLn ""
  
test022 = do
  SECD s e c d <- get
  c' <- liftIO $ cons (Fxnum 13) c
  c'' <- liftIO $ cons (I LDC) c'
  put $ SECD s e c'' d
  showSECD
  liftIO $ putStrLn ""
  eval1
  showSECD
  liftIO $ putStrLn ""

list1 x = liftIO $ cons x Nil
list2 x0 x1 = do
  p  <- list1 x1
  liftIO $ cons x0 p
list3 x0 x1 x2 = do
  p  <- list2 x1 x2
  liftIO $ cons x0 p
list4 x0 x1 x2 x3 = do
  p  <- list3 x1 x2 x3
  liftIO $ cons x0 p

list (x:[]) = list1 x
list (x:xs) = do
  p <- list xs
  liftIO $ cons x p


test030 = do
   SECD s e c d <- get
   c' <- list1 (I NIL)
   put $ SECD s e c' d
   showSECD
   liftIO $ putStrLn ""
test031 = do
   SECD s e c d <- get
   c' <- list2 (I LDC) (Fxnum 17)
   put $ SECD s e c' d
   showSECD
   liftIO $ putStrLn ""
test032 = do
   SECD s e c d <- get
   c' <- list [I LDC, Fxnum 17, I LDC, Fxnum 9]
   put $ SECD s e c' d
   showSECD
   liftIO $ putStrLn ""

-- Example. ((lambda (x y) (+ x y)) 2 3) compiles to
--       (NIL LDC 3 CONS LDC 2 CONS LDF (LD (1.2) LD (1.1) + RTN) AP)

test050 :: StateT SECD IO ()
test050 = do
  SECD s e c d <- get
  a1 <- liftIO $ cons (Fxnum 1) (Fxnum 2)
  a2 <- liftIO $ cons (Fxnum 1) (Fxnum 1)
  p  <- list [I LD, a1, I LD, a2, I ADD, I RTN]
  c' <- list [I NIL, I LDC, Fxnum 3,
              I CONS, I LDC, Fxnum 2,
              I CONS, I LDF, p, I AP]
  put $ SECD s e c' d
  showSECD
  liftIO $ putStrLn ""
  eval
  showSECD
  liftIO $ putStrLn ""

test060 :: Int -> StateT SECD IO ()
test060 x = do
  SECD s e c d <- get
  a11   <- liftIO $ cons (Fxnum 1) (Fxnum 1)
  a11'  <- liftIO $ cons (Fxnum 1) (Fxnum 1)
  a11'' <- liftIO $ cons (Fxnum 1) (Fxnum 1)
  a11'''<- liftIO $ cons (Fxnum 1) (Fxnum 1)
  a11''''<- liftIO $ cons (Fxnum 1) (Fxnum 1)
  a21   <- liftIO $ cons (Fxnum 2) (Fxnum 1)
  a21'  <- liftIO $ cons (Fxnum 2) (Fxnum 1)
  ct    <- list [I LD, a11', I JOIN]
  cf    <- list [I NIL, I LDC, Fxnum 2, I LD, a11'', I SUB, I CONS,
                 I LD, a21, I AP, I NIL, I LDC, Fxnum 1, I LD, a11''',
                 I SUB, I CONS, I LD, a21', I AP, I ADD, I JOIN]
  f     <- list [I LDC, Fxnum 2, I LD, a11, I LTN, I SEL, 
                 ct, cf, I RTN]
  g     <- list [I NIL, I LDC, Fxnum x, I CONS, I LD, a11'''', I AP, I RTN]
  c' <- list [I DUM, I NIL, I LDF, f, I CONS, I LDF, g, I RAP]
  put $ SECD s e c' d
  showSECD
  liftIO $ putStrLn ""
  eval
  liftIO $ putStrLn "done."
  SECD s0 _ _ _ <- get
  liftIO $ putStr "s="
  liftIO $ showValue s0
  liftIO $ putStrLn ""
  -- SECD slast _ _ _ <- get
  -- liftIO $ showValue slast
  -- liftIO $ putStrLn ""


----

test001 = do -- (5 . 3)
  x <- newIORef $ Cons (Fxnum 5) (Fxnum 3)
  s <- readIORef x
  putStrLn $ "x = " ++ show s

test002 = do -- (5 7)
  x <- newIORef $ Cons (Fxnum 7) Nil
  y <- newIORef $ Cons (Fxnum 5) (Ref x)
  putStrLn "----"
  Cons a b <- readIORef y -- a = 5, b = (7)
  putStrLn $ "a = " ++ show a
  putStrLn $ "b = " ++ show b
  case b of
    Ref p -> do {
      z <- readIORef p;
      putStrLn $ "z = " ++ show z
      }

test003 = do -- (5 7)
  x <- newIORef $ Cons (Fxnum 7) Nil
  y <- newIORef $ Cons (Fxnum 5) (Ref x)
  putStrLn "----"
  Cons a b <- readIORef y -- a = 5, b = (7)
  putStrLn $ "a = " ++ show a
  putStrLn $ "b = " ++ show b
  case b of
    Ref p -> do {
      z <- readIORef p;
      putStrLn $ "z = " ++ show z
      }
  -- set! で y を変更しても x には影響なし
  writeIORef y (Cons (Fxnum 9) Nil)
  putStrLn "----"
  putStrLn "y="
  readIORef y >>= print
  putStrLn "x="
  readIORef x >>= print
--
test010 = do -- (10 3)
  x <- newIORef $ Cons (Fxnum 3) Nil
  let x' = Ref x
  y <- newIORef $ Cons (Fxnum 10) x'
  let y' = Ref y
  putStrLn "----"
  v1 <- car y' -- (car (10 3))
  print v1
  v2 <- cdr y' -- (cdr (10 3)) = (3)
  print v2
  v3 <- (car <=< cdr) y' -- (car (cdr (10 3))) = 3
  print v3

test011 = do -- cons
  x <- cons (Fxnum 8) Nil
  print x
  v1 <- car x
  print v1
  v2 <- cdr x
  print v2
  y <- cons (Fxnum 21) x 
  print y
  v3 <- car y
  print v3
  v4 <- (car <=< cdr) y
  print v4

test012 = do -- cons
  x <- cons (Fxnum 8) Nil
  showValue x
  putStrLn ""
  y <- cons (Fxnum 21) x 
  showValue y
  putStrLn ""
  z <- cons x x
  showValue z
  putStrLn ""

