module Door3

%default total

data DoorState = DoorOpen | DoorClosed

data DoorCmd : Type -> (pre, post : DoorState) -> Type where
  Open     : DoorCmd () DoorClosed DoorOpen
  Close    : DoorCmd () DoorOpen DoorClosed
  RingBell : DoorCmd () DoorClosed DoorClosed

  GetStr   : DoorCmd String st st
  PutStr   : String -> DoorCmd  () st st 
  
  Pure     : a -> DoorCmd a st st
  (>>=)    : DoorCmd a before1 after1 -> (a -> DoorCmd b after1 after2) -> DoorCmd b before1 after2


showDoorCmd : DoorCmd ty pre post -> String
showDoorCmd {pre = DoorClosed} {post = DoorOpen} Open = "Open"
showDoorCmd {pre = DoorOpen} {post = DoorClosed} Close = "Close"
showDoorCmd {pre = DoorClosed} {post = DoorClosed} RingBell = "Ring Bell"
showDoorCmd {pre = pre} {post = pre} GetStr = "GetStr"
showDoorCmd {pre = pre} {post = pre} (PutStr x) = "PutStr"
showDoorCmd {pre = pre} {post = pre} (Pure x) = "Pure"
showDoorCmd {pre = pre} {post = post} (x >>= f) = ">>="


Show (DoorCmd ty pre post) where
  show = showDoorCmd



    
doorProg : DoorCmd () DoorClosed DoorClosed
doorProg = do RingBell
              Open
              Close


runDoor : DoorCmd a before after -> IO a
runDoor Open = do putStrLn "open1"
                  pure ()
runDoor Close = do putStrLn "close"
                   pure ()
runDoor RingBell = do putStrLn "ring-bell"
                      pure ()
runDoor GetStr = do str <- getLine
                    pure str
runDoor (PutStr s) = do putStrLn s
                        pure ()
runDoor (Pure x) = pure x
runDoor (cmd >>= cont) = do cmd' <- runDoor cmd
                            runDoor (cont cmd')


data DoorIO : Type -> (pre, post : DoorState) -> Type where
  Do   : DoorCmd a before1 after1 ->  (a -> Inf (DoorIO b after1 after2)) -> DoorIO b before1 after2
  Done : a -> DoorIO a st st

namespace DoorDo
  (>>=) : DoorCmd a before1 after1 ->  (a -> Inf (DoorIO b after1 after2)) -> DoorIO b before1 after2
  (>>=) = Do
  

data Fuel = Dry | More (Lazy Fuel)

partial
forever : Fuel
forever = More forever


run : Fuel -> DoorIO a before after -> IO (Maybe a)
run (More fuel) (Do cmd cont) = do v <- runDoor cmd
                                   run fuel (cont v)
run (More fuel) (Done x) = do putStrLn "Done!"
                              pure $ Just x
run Dry _ = do putStrLn "dry fuel"
               pure Nothing

doorProg1 : DoorIO String DoorClosed DoorClosed
doorProg1 = do Open
               Close
               PutStr "Enter your name:"
               name <- GetStr 
               RingBell
               Done name
               

-- nix-shell -p gmp -p gcc
-- :exec run forever doorProg1
