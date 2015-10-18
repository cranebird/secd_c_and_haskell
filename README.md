# secd_c_and_haskell
Implement SECD machine in C and Haskell.

- csecd.c: C version. no GC.
- UnsafeSECD.hs: SECD as top level mutable variable (with unsafePerformIO). as fast as C version. no GC.
- IORefVM.hs: StateT Monad + IORef. slow. no GC.
- MallocVM.hs: StateT Monad + Foreign.Marshal.Alloc. slow. no GC.