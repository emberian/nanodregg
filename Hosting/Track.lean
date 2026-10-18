/-
# Hosting.Track — what a follower holds of the World, by id, read by one reader

`hosting-broker` follows the World for two things: the operator's allowances (`Allow.allowanceOf`)
and the resident grains whose broker sockets keybroker serves (`Controller.residentOf`, HOSTING-26).
Both are the same act: at the open, every live id is read; after each catch-up, every id the new
Turns touched or bore is read again and every other binding kept. `Proofs.Allowance.update_tracks`:
with HOSTING-10's batch frame, the bindings are exactly the World's readable cells, for any reader.
-/
import Hosting.Controller

namespace Nanodregg.Hosting.Track

open Nanodregg.Kernel

variable {D : Type} [Ord D] [DecidableEq D] {α : Type}

/-- The value `read` gives the live cell at id `i` of `w`. -/
def readAt (E : Env D) (read : Cell → Option α) (w : World D) (i : D) : Option α :=
  (w.live E i).bind read

/-- The bindings once the ids `ids` were touched: each touched id is read again, every other binding
kept. -/
def update (E : Env D) (read : Cell → Option α) (w : World D) (cur : List (D × α)) (ids : List D) :
    List (D × α) :=
  cur.filter (fun p => !ids.contains p.1) ++
    ids.eraseDups.filterMap fun i => (readAt E read w i).map (i, ·)

/-- A catch-up: the World `w'` the tail reached and the Turns it absorbed; every id they touched or
bore (`Controller.touchedIds`) is read again (`Proofs.Allowance.absorb_tracks`). -/
def absorb (E : Env D) (read : Cell → Option α) (w' : World D) (held : List (D × α))
    (turns : List (Turn D)) : List (D × α) :=
  update E read w' held (Controller.touchedIds turns)

end Nanodregg.Hosting.Track
