/-
P11a interface witnesses for de Alfaro–Henzinger, Interface Automata (2001),
PDF p10 (Definitions 14–15 and Theorem 4).
-/
import Lang.Contextual.P5

namespace Nanodregg.Lang.Contextual.P5.Interfaces

/-- de Alfaro–Henzinger Theorem 4, PDF p10: a stateful peer asks seven then
accepts either Boolean response, repeatedly. -/
def sevenPeer : Machine Bool Bool Nat where
  receive s _ := if s then some false else none
  emit s := if s then [] else [(7, true)]

/-- de Alfaro–Henzinger Definition 14(2), PDF p10: these receivers initially
enable the same label; only the specification also accepts the second request. -/
def twiceReceiver (repeatable : Bool) : Machine Bool Unit Unit where
  receive s _ := if !s || repeatable then some true else none
  emit _ := []

end Nanodregg.Lang.Contextual.P5.Interfaces
