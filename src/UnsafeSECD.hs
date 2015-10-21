module UnsafeSECD (
  test060,
  eval,
  Insn(..),
  Value(..),
  Cons(..),
  car,cdr,caar,cadr,cdar,cddr,caadr,caddr,cdddr,cdaar,cdadr,
  ) where
       
import Data.IORef
import Control.Monad
import System.IO.Unsafe

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
  show (Ref _) = "#x"
  show (B b) = if b then "#t" else "#f"  
  show (I i) = show i
  show W = "W"

instance Show Cons where
  show (Cons x y) = "Cons " ++ show x ++ " " ++ show y

car,cdr :: Value -> IO Value
car (Ref p) = do
  Cons a _ <- readIORef p
  return a
car x = error $ "car expect cons : " ++ show x

cdr (Ref p) = do
  Cons _ a <- readIORef p
  return a
cdr x = error $ "cdr expect cons :" ++ show x
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
showValue (B b) = case b of
  True -> putStr "#t"
  False -> putStr "#f"
showValue (I i) = putStr (show i)
showValue W = putStr "W"

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

-- SECD register
{-# NOINLINE _s #-}
_s,_e,_c,_d :: IORef Value    
_s = unsafePerformIO (newIORef Nil)
{-# NOINLINE _e #-}
_e = unsafePerformIO (newIORef Nil)
{-# NOINLINE _c #-}
_c = unsafePerformIO (newIORef Nil)
{-# NOINLINE _d #-}
_d = unsafePerformIO (newIORef Nil)
-- setter
setS,setE,setC,setD :: Value -> IO ()
setS = writeIORef _s
setE = writeIORef _e
setC = writeIORef _c
setD = writeIORef _d
-- getter
getS,getE,getC,getD :: IO Value
getS = readIORef _s
getE = readIORef _e
getC = readIORef _c
getD = readIORef _d
-- show
showSECD :: IO ()
showSECD = do
  s <- getS
  e <- getE
  c <- getC
  d <- getD
  
  showValue s
  putStr " "
  showValue e
  putStr " "
  showValue c
  putStr " "
  showValue d
-- evaluator
eval :: IO ()
eval = do
  eval1
  c <- getC
  unless (c == Nil) eval

eval1 :: IO ()
eval1 = do
  s <- getS
  e <- getE
  c <- getC
  d <- getD
  op <- car c

  case op of
    -- s e (NIL.c) d ->  (nil.s) e c d
    I NIL -> do
      s' <- cons Nil s
      c' <- cdr c
      setS s'
      setC c'
    -- s e (LDC x.c) d -> (x.s) e c d
    I LDC -> do
      n  <- cadr c
      s' <- cons n s
      c' <- cddr c
      setS s'
      setC c'
    -- binOp
    --  (a b.s) e (OP.c) d   ->   ((a OP b).s) e c d
    I ADD -> do
      Fxnum a <- car s
      Fxnum b <- cadr s
      let v = Fxnum (a + b)
      s' <- cddr s
      s'' <- cons v s'
      c' <- cdr c
      setS s''
      setC c'
    I SUB -> do
      Fxnum a <- car s
      Fxnum b <- cadr s
      let v = Fxnum (a - b)
      s' <- cddr s
      s'' <- cons v s'
      c' <- cdr c
      setS s''
      setC c'
    I LTN -> do
      Fxnum a <- car s
      Fxnum b <- cadr s
      let v = B (a < b)
      s' <- cddr s
      s'' <- cons v s'
      c' <- cdr c
      setS s''
      setC c'
    -- (x.s) e (SEL ct cf .c) d -> s e cx (c.d) where cx = ct if x = #t
    I SEL -> do
      s' <- cdr s
      x  <- car s
      ct <- cadr c
      cf <- caddr c
      c' <- cdddr c
      d' <- cons c' d
      setS s'
      setC (if x == B True then ct else cf)
      setD d'
    -- s e (JOIN.c) (cr.d') -> s e cr d'
    I JOIN -> do
      cr <- car d
      d' <- cdr d
      setC cr
      setD d'
    -- (x.s) e (ATOM.c) d -> (#t.s) e c d
    I ATOM -> do
      x  <- car s
      let b = case x of
            Ref _ -> False
            _ -> True
      s' <- cons (B b) s
      c' <- cdr c
      setS s'
      setC c'
    -- s e (LD (i.j).c) d   ->  (locate((i.j),e).s) e c d
    I LD -> do
      i  <- caadr c
      j  <- cdadr c
      x  <- locate i j e
      s' <- cons x s
      c' <- cddr c
      setS s'
      setC c'
    -- s e (LDF f.c) d ->  ((f.e).s) e c d  
    I LDF -> do
      f  <- cadr c
      c' <- cddr c
      p  <- cons f e
      s' <- cons p s
      setS s'
      setC c'
    -- (a b.s') e (OP.c) d -> ((a.b).s') e c d
    I CONS -> do
      a   <- car s
      b   <- cadr s
      s'  <- cddr s
      p   <- cons a b
      s'' <- cons p s'
      c'  <- cdr c
      setS s''
      setC c'
    -- ((f.e') v.s') e (AP.c') d    ->  NIL (v.e') f (s' e c'.d)
    I AP -> do
      f   <- caar s
      e'  <- cdar s
      v   <- cadr s
      s'  <- cddr s
      c'  <- cdr c
      e'' <- cons v e'
      d1  <- cons c' d
      d2  <- cons e d1
      d'  <- cons s' d2
      setS Nil
      setE e''
      setC f
      setD d'
    -- (x.z) e' (RTN.q) (s e c.d) ->  (x.s) e c d        
    I RTN -> do
      x   <- car s
      s'  <- car d
      e'  <- cadr d
      c'  <- caddr d
      d'  <- cdddr d
      s'' <- cons x s'
      setS s''
      setE e'
      setC c'
      setD d'
    -- s e (DUM.c) d  ->  s (W.e) c d      
    I DUM -> do
      e'  <- cons W e
      c'  <- cdr c
      setE e'
      setC c'
    -- ((f.(W.e)) v.s') (W.e) (RAP.c) d ->  nil rplaca((W.e),v) f (s' e c.d)
    I RAP -> do
      f   <- caar s
      we  <- cdar s
      v   <- cadr s
      s'  <- cddr s
      c'  <- cdr c
      -- rplaca
      let (Ref p) = we
      e' <- cdr e
      writeIORef p (Cons v e')
      --
      d0  <- cons c' d
      d1  <- cons e' d0
      d'  <- cons s' d1
      setS Nil
      setE we
      setC f
      setD d'
    x -> error $ "expect (I Insn) but got : " ++ show x

nth :: Int -> Value -> IO Value
nth 0 p = car p
nth i p = do
  p' <- cdr p
  nth (i - 1) p'

locate :: Value -> Value -> Value -> IO Value
locate (Fxnum i) (Fxnum j) e = do
  e' <- nth (i - 1) e
  nth (j - 1) e'
locate _ _ _ = error "invalid args"

test022 = do
  s <- getS
  e <- getE
  c <- getC
  d <- getD
  
  c' <- cons (Fxnum 13) c
  c'' <- cons (I LDC) c'
  
  setC c''

  showSECD
  putStrLn ""
  eval
  showSECD
  putStrLn ""

list :: [Value] -> IO Value
list (x:[]) = cons x Nil
list (x:xs) = do
  p <- list xs
  cons x p
list [] = return Nil

-- test060 23
test060 :: Int -> IO ()
test060 x = do
  setS Nil
  setE Nil
  setD Nil
  
  a11   <- cons (Fxnum 1) (Fxnum 1)
  a11'  <- cons (Fxnum 1) (Fxnum 1)
  a11'' <- cons (Fxnum 1) (Fxnum 1)
  a11'''<- cons (Fxnum 1) (Fxnum 1)
  a11''''<- cons (Fxnum 1) (Fxnum 1)
  a21   <- cons (Fxnum 2) (Fxnum 1)
  a21'  <- cons (Fxnum 2) (Fxnum 1)
  ct    <- list [I LD, a11', I JOIN]
  cf    <- list [I NIL, I LDC, Fxnum 2, I LD, a11'', I SUB, I CONS,
                 I LD, a21, I AP, I NIL, I LDC, Fxnum 1, I LD, a11''',
                 I SUB, I CONS, I LD, a21', I AP, I ADD, I JOIN]
  f     <- list [I LDC, Fxnum 2, I LD, a11, I LTN, I SEL, 
                 ct, cf, I RTN]
  g     <- list [I NIL, I LDC, Fxnum x, I CONS, I LD, a11'''', I AP, I RTN]
  c     <- list [I DUM, I NIL, I LDF, f, I CONS, I LDF, g, I RAP]
  setC c
  showSECD
  putStrLn ""
  eval
  showSECD
  putStrLn ""


