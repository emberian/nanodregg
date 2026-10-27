/-
# Spec.Sim.Durable2 — the in-place keep and the resume built over a keep (§5 D3)

Tooling (closure C9). `durableResumeVia keep` is the resident's resume (`Hosting.Resident.resumeOps`)
with its keep arm the given keep, so a lazy keep is also the resume's keep, as in the code
(`resumeOps` calls `keepOps`). `inPlaceKeep` writes the kept name in place, with every sync the
deployed keep runs. `durableWhere` is a resident's place, for the floor's witness.
-/
import Spec.Sim.Run
import Hosting.Resident.Volume

namespace Nanodregg.Spec

open Nanodregg.Hosting.Resident

/-- The resume over a keep: forget what is absent, keep again what is held, nothing for an
unreadable entry (`resumeOps` with `keepOps` replaced by `keep`). -/
def durableResumeVia (keep : Where → String → List FsOp) (w : Where) : Option (Option String) → List FsOp
  | none => forgetOps w
  | some (some s) => keep w s
  | some none => []

/-- **The in-place keep**: the kept name removed, created, its directory synced, the text written
and synced, the directory synced again; no fresh copy renamed over it. -/
def inPlaceKeep (w : Where) (s : String) : List FsOp :=
  [.removeIfExists w.kept, .create w.kept, .syncDir w.vol, .write s, .sync, .syncDir w.vol]

/-- A resident's place: its volume and kept name. -/
def durableWhere : Where :=
  { conf := ⟨.empty, .empty, 0, .empty, .empty⟩, member := "m", broker := "b", vol := "vol",
    kept := "vol/kept", noted := "vol/withdrawn" }

end Nanodregg.Spec
