def StateM.update [Monad m] (f: σ -> σ): StateT σ m Unit := 
  StateT.modifyGet <| fun s => ((), f s)