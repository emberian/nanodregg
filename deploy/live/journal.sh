# deploy/live/journal.sh — sourced by harness.sh and broker.sh (OPS-16, GATES-5's fail-open finding).
#
# Every journal read a row judges is THIS run's: `jr ARGS…` is `journalctl --user ARGS…` after the
# cursor `journal_mark` recorded, never the unit's whole history (a kept unit link keeps one journal,
# so a previous run's `Start request repeated too quickly` or `STATUS follow` used to satisfy a row
# of this one). `journal_mark REPORT_DIR` is itself a plant: a marker written BEFORE the cursor must
# be invisible to `jr` and one written AFTER it visible, or the run is refused by name
# (`journal-reads-only-this-run FAIL`, exit 2): a filter that sees everything, or nothing, would
# make every journal row unjudgeable. Waits are bounded (10 s each).
JOURNAL_TAG=nd-ops-live-journal
CUR=
jr() { [ -n "$CUR" ] || return 1; journalctl --user "$@" --after-cursor="$CUR" -o cat --no-pager 2>/dev/null; }
journal_seen() { # TAG TEXT [after-cursor]: TEXT is in TAG's lines (all of them, or after CUR)
  if [ -n "${3:-}" ]; then jr -t "$1" | grep -qxF "$2"
  else journalctl --user -t "$1" -o cat --no-pager 2>/dev/null | grep -qxF "$2"; fi; }
journal_mark() { # REPORT_DIR
  local n="$$-$RANDOM-$(date +%s%N)" end
  local stale="stale $n" fresh="fresh $n"
  echo "$stale" | systemd-cat -t "$JOURNAL_TAG" || { echo "ROW journal-reads-only-this-run FAIL :: systemd-cat failed"; exit 2; }
  end=$((SECONDS+10)); until journal_seen "$JOURNAL_TAG" "$stale"; do
    [ $SECONDS -ge $end ] && { echo "ROW journal-reads-only-this-run FAIL :: the stale marker never reached the journal"; exit 2; }; sleep 0.2; done
  CUR=$(journalctl --user --show-cursor -n 0 --no-pager 2>/dev/null | sed -n 's/^-- cursor: //p')
  [ -n "$CUR" ] || { echo "ROW journal-reads-only-this-run FAIL :: no journal cursor"; exit 2; }
  echo "$CUR" > "$1/journal-cursor"
  echo "$fresh" | systemd-cat -t "$JOURNAL_TAG"
  end=$((SECONDS+10)); until journal_seen "$JOURNAL_TAG" "$fresh" after; do
    [ $SECONDS -ge $end ] && { echo "ROW journal-reads-only-this-run FAIL :: the filter does not see this run's marker"; exit 2; }; sleep 0.2; done
  if journal_seen "$JOURNAL_TAG" "$stale" after; then
    echo "ROW journal-reads-only-this-run FAIL :: a line from before the run passes the filter"; exit 2; fi
  echo "ROW journal-reads-only-this-run PASS :: cursor $1/journal-cursor; the marker before it hidden, the one after it seen"; }
