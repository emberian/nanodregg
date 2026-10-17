# Run the RENDERED nd-hosted-follow@ ExecStart through the real nd-supervise parser (the fd1d4b2
# lesson: a unit that renders is not a unit that starts), each rendered path or variable replaced
# by a scratch value; an unmapped path or variable fails the run before anything starts.
# DIR must not exist; it is the only place written.
# usage: python3 deploy/live/follow-argv.py deploy/units/linux/nd-hosted-follow@.service DIR ND_SUPERVISE HOST
import os, subprocess, sys
unit, d, sup, host = sys.argv[1:5]
line = next(l for l in open(unit) if l.startswith("ExecStart="))[len("ExecStart="):].split()
os.makedirs(d)
for sub in ["follow", "store", "hide-etc", "hide-home"]:
    os.makedirs(os.path.join(d, sub))
os.chmod(os.path.join(d, "follow"), 0o2710)
m = {"/opt/nd/bin/nd-supervise": sup, "/opt/nd/bin/host": host,
     "/run/nd-follow/%i.sock": os.path.join(d, "follow", "w.sock"),
     "/srv/nd-hosted/worlds/%i/store": os.path.join(d, "store"),
     "/etc/nd": os.path.join(d, "hide-etc"), "/home": os.path.join(d, "hide-home"),
     "${ND_GID}": str(os.getgid()), "${ND_MEMBER}": "00" * 32, "${ND_GRANT}": "00" * 32}
argv = [m.get(w, w) for w in line]
unmapped = [w for w in line if w not in m and (w.startswith("/") or w.startswith("$"))]
assert not unmapped, unmapped
print("ARGV", " ".join(argv))
r = subprocess.run(argv, stdin=subprocess.DEVNULL, capture_output=True, text=True, timeout=60)
print("EXIT", r.returncode)
print("STDERR", r.stderr.strip())
