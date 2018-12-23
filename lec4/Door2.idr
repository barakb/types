module Door2

data DoorState = DoorOpen | DoorClosed

data DoorCmd : Type -> (pre, post : DoorState) -> Type where
  Open : DoorCmd () DoorClosed DoorOpen
  Close : DoorCmd () DoorOpen DoorClosed
  Ring : DoorCmd () DoorClosed DoorClosed
  
  Pure : a -> DoorCmd a before after
  (>>=) : DoorCmd a before1 after1 -> (a -> DoorCmd b after1 after2) -> DoorCmd b before1 after2
  
doorProg : DoorCmd () DoorClosed DoorClosed
doorProg = do
           Open
           Close
--           Open 
--           Ring
           
