/-
# Host.Proofs.Follow — follow's own constants against the kernel bounds they must meet

* `window_le_windowMax` — the window follow signs every call and read envelope with (`window`) is
  within `Kernel.Bounds.windowMax`, the widest window `Envelope.check` accepts (PROTOCOL-27,
  `wideWindow`). Without it a window above the bound would refuse every read, by name but at run time.
-/
import Host.Follow

namespace Nanodregg.Host.Follow

theorem window_le_windowMax : window ≤ Kernel.Bounds.windowMax := by decide

end Nanodregg.Host.Follow
