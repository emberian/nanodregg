/-
# Host.Proofs.Page — a log page always has room for the next event

`Page.walkTurns` stops a page when the next event does not fit the budget. With the deployed
budget that can only happen after at least one event: every event fits an empty page
(`budget_fits_event`), so a page short of the tip is never empty (PROTOCOL's follow refuses an
empty page short of the tip as `badResult`).
-/
import Host.Page

namespace Nanodregg.Host.Page

theorem budget_fits_event : Kernel.Bounds.eventBytesMax + 4 ≤ budget := by decide

end Nanodregg.Host.Page
