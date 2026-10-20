"""gates/land.py — the landing queue: which green lander may compare-and-swap main, and when (GATES-19).

  land.py --queue DIR --ticket FILE --repo DIR --ref REF --new COMMIT --base COMMIT [--deadline S]
  land.py --charge --ticket FILE --before N

Every lander holds a ticket, DIR/<seq>.<pid> (gate-lib.sh new_ticket), flock'd by the lander's
outer scripts/commit for as long as it lives: a lander that dies, however it dies, releases its
ticket by the kernel, so there is no stale-ticket logic (the slot locks' reasoning). The file holds
how many times this lander has been DISPLACED: judged green against a main that had moved by the
time it reached the head.

The order is VERDICT READINESS with an AGE BOUND (ROOT 10-19), not arrival:
- a lander still being judged blocks nobody; the head is whichever lander is green and whose base is
  still main. Checking that and the CAS happen under one flock (DIR/land.flock), so two ready landers
  are serialized, and the one that finds main moved is displaced (exit 75) and re-bases;
- a lander displaced TWICE is head regardless: until it lands or dies, no lander with fewer than two
  displacements (or a younger ticket) lands; they wait, printing whom they wait for. Two
  twice-displaced landers go oldest ticket first. The bound: a lander lands within three passes
  unless another reached two displacements before it.
The CAS stays the proof: `update-ref REF NEW BASE` writes only when REF is still BASE.
Exit 0 = landed; 75 = not landed, re-read main and re-base (displaced, a refused CAS counted as one,
or the deadline passed waiting for a twice-displaced lander: then the count does not rise); 2 = a
tool failure. Nothing is landed except by the CAS.

--charge (GATES-20b, LANG-21's finding): the outer scripts/commit asks, after an exit 75, whether it
is charged to the lander's retry budget (COMMIT_RETRIES). Only a displacement while NOT head is: a
lander displaced AGE_BOUND times is head regardless, and a head displaced again lost a tie to an
older head (blockers() lets nothing else land), so it waits for the tie winners and never fails for
them. LANG-21's c1166ce gave up after five displacements, three of them as head. A deadline wait
(the count unchanged) is not charged either. Exit 0 = charged, 1 = not charged.

--fast (GATES-22): a FAST lander (scripts/commit's default: judged in minutes) holds no ticket and is never
counted: it lands by the compare-and-swap, or exits 75 (main moved) and re-bases. It lets a FULL lander displaced
AGE_BOUND times land first (that one's judge is ~40 min and would otherwise never win a race against landings
every ~25 min), for at most --deadline (default 3600 s), then lands anyway and says whom it passed: a stalled head
must not stop every landing.
"""
import argparse
import fcntl
import os
import subprocess
import sys
import time

AGE_BOUND = 2


def count(t: str) -> int:
    try:
        s = open(t, encoding="utf-8").read().strip()
    except OSError:
        return 0
    return int(s) if s.isdigit() else 0


def alive(t: str) -> bool:
    """A ticket whose flock someone holds. A dead one older than ten minutes is removed (a lander
    killed by SIGKILL never ran its own trap); a fresh one is left alone: it may be a ticket whose
    owner has created it and not yet locked it."""
    try:
        fd = os.open(t, os.O_RDONLY)
    except OSError:
        return False
    try:
        fcntl.flock(fd, fcntl.LOCK_EX | fcntl.LOCK_NB)
    except BlockingIOError:
        os.close(fd)
        return True
    try:
        if time.time() - os.fstat(fd).st_mtime > 600:
            os.unlink(t)
    except OSError:
        pass
    os.close(fd)
    return False


def seq(t: str) -> int:
    return int(os.path.basename(t).split(".")[0])


def blockers(q: str, me: str) -> list[str]:
    """The live twice-displaced tickets this lander must let land first."""
    mine = count(me)
    out = []
    for n in sorted(os.listdir(q)):
        t = os.path.join(q, n)
        if not n[:1].isdigit() or "." not in n or os.path.abspath(t) == os.path.abspath(me):
            continue
        if count(t) >= AGE_BOUND and (mine < AGE_BOUND or seq(t) < seq(me)) and alive(t):
            out.append(t)
    return out


def charge(ticket: str, before: int) -> int:
    now = count(ticket)
    if before >= AGE_BOUND:
        print(f"queue: not charged: displaced while head ({before} displacements before; an older head landed first, a tie)")
        return 1
    if now == before:
        print("queue: not charged: no displacement (waited for a head past the deadline)")
        return 1
    print(f"queue: charged: displaced while not head (now {now} times)")
    return 0


def fast(q: str, repo: str, ref: str, new: str, base: str, deadline: int) -> int:
    end = time.monotonic() + deadline
    said = None
    while True:
        lk = os.open(os.path.join(q, "land.flock"), os.O_RDWR | os.O_CREAT, 0o664)
        fcntl.flock(lk, fcntl.LOCK_EX)
        try:
            cur = subprocess.run(["git", "-C", repo, "rev-parse", ref], capture_output=True, text=True)
            if cur.returncode != 0:
                print(f"queue: cannot read {ref}: {cur.stderr.strip()}")
                return 2
            if cur.stdout.strip() != base:
                print(f"queue: main moved from {base[:12]} to {cur.stdout.strip()[:12]} under this fast verdict; re-basing")
                return 75
            heads = [os.path.join(q, n) for n in sorted(os.listdir(q))
                     if n[:1].isdigit() and "." in n and count(os.path.join(q, n)) >= AGE_BOUND and alive(os.path.join(q, n))]
            late = time.monotonic() > end
            if not heads or late:
                if heads:
                    print(f"queue: waited {deadline} s for {' '.join(os.path.basename(h) for h in heads)}; landing past it")
                r = subprocess.run(["git", "-C", repo, "update-ref", ref, new, base], capture_output=True, text=True)
                if r.returncode != 0:
                    print(f"queue: the compare-and-swap refused: {r.stderr.strip()}")
                    return 75
                print("queue: fast; landed by compare-and-swap")
                return 0
        finally:
            os.close(lk)
        names = " ".join(os.path.basename(h) for h in heads)
        if names != said:
            print(f"queue: a full lander displaced {AGE_BOUND} times lands first: waiting for {names}", flush=True)
            said = names
        time.sleep(5)


def main() -> int:
    if "--fast" in sys.argv[1:]:
        fp = argparse.ArgumentParser()
        fp.add_argument("--fast", action="store_true")
        for f in ("--queue", "--repo", "--ref", "--new", "--base"):
            fp.add_argument(f, required=True)
        fp.add_argument("--deadline", type=int, default=3600)
        f = fp.parse_args()
        return fast(f.queue, f.repo, f.ref, f.new, f.base, f.deadline)
    if "--charge" in sys.argv[1:]:
        cp = argparse.ArgumentParser()
        cp.add_argument("--charge", action="store_true")
        cp.add_argument("--ticket", required=True)
        cp.add_argument("--before", required=True)
        c = cp.parse_args()
        return charge(c.ticket, int(c.before) if c.before.strip().isdigit() else 0)
    ap = argparse.ArgumentParser()
    for f in ("--queue", "--ticket", "--repo", "--ref", "--new", "--base"):
        ap.add_argument(f, required=True)
    ap.add_argument("--deadline", type=int, default=7200)
    a = ap.parse_args()
    end = time.monotonic() + a.deadline
    said = None
    while True:
        lk = os.open(os.path.join(a.queue, "land.flock"), os.O_RDWR | os.O_CREAT, 0o664)
        fcntl.flock(lk, fcntl.LOCK_EX)
        try:
            cur = subprocess.run(["git", "-C", a.repo, "rev-parse", a.ref], capture_output=True, text=True)
            if cur.returncode != 0:
                print(f"queue: cannot read {a.ref}: {cur.stderr.strip()}")
                return 2
            if cur.stdout.strip() != a.base:
                n = count(a.ticket) + 1
                with open(a.ticket, "w", encoding="utf-8") as fh:
                    fh.write(f"{n}\n")
                print(f"queue: displaced (now {n} times; from {AGE_BOUND} this lander is head regardless): main moved "
                      f"from {a.base[:12]} to {cur.stdout.strip()[:12]} under its verdict")
                return 75
            b = blockers(a.queue, a.ticket)
            if not b:
                r = subprocess.run(["git", "-C", a.repo, "update-ref", a.ref, a.new, a.base], capture_output=True, text=True)
                if r.returncode != 0:
                    n = count(a.ticket) + 1
                    with open(a.ticket, "w", encoding="utf-8") as fh:
                        fh.write(f"{n}\n")
                    print(f"queue: the compare-and-swap refused (displaced, now {n} times): {r.stderr.strip()}")
                    return 75
                print(f"queue: head (displaced {count(a.ticket)} times); landed by compare-and-swap")
                return 0
        finally:
            os.close(lk)
        names = " ".join(f"{os.path.basename(t)} (displaced {count(t)})" for t in b)
        if names != said:
            print(f"queue: waiting for {names}: displaced {AGE_BOUND} times, it is head regardless (GATES-19)", flush=True)
            said = names
        if time.monotonic() > end:
            print(f"queue: waited {a.deadline} s for {names}; not landed; re-reading main")
            return 75
        time.sleep(5)


if __name__ == "__main__":
    sys.exit(main())
