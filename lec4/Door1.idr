module Door1


data DoorCmd : Type -> Type where
  Open : DoorCmd ()
  Close : DoorCmd ()
  Ring : DoorCmd ()
  
  Pure : a -> DoorCmd a
  (>>=) : DoorCmd a -> (a -> DoorCmd b) -> DoorCmd b
  
doorProg : DoorCmd ()
doorProg = do
           Open
           Close
           Open 
           Ring
           
