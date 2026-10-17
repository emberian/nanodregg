# deploy/live/unit-argv.py UNIT DIR WORD=VALUE... -- run a RENDERED unit's ExecStart through the
# real programs (the fd1d4b2 lesson: a unit that renders is not a unit that starts), each rendered
# word named on the command line replaced by its VALUE (`{DIR}` in a VALUE is DIR), and each
# `Environment=` value likewise (passed as the program's environment). A rendered
# absolute path or ${VAR} with no value, or a value no word asks for, fails before anything runs.
# DIR must not exist; it is made, with every `mkdir:PATH` / `mkdir2710:PATH` word-less entry, and
# is the only place written. Prints ARGV, EXIT and STDERR.
import os, subprocess, sys
unit, d, pairs = sys.argv[1], sys.argv[2], sys.argv[3:]
os.makedirs(d)
m, used = {}, set()
for p in pairs:
    k, v = p.split("=", 1)
    v = v.replace("{DIR}", d)
    if k == "mkdir":
        os.makedirs(v, exist_ok=True)
    elif k == "mkdir2710":
        os.makedirs(v, exist_ok=True); os.chmod(v, 0o2710)
    else:
        m[k] = v
line = next(l for l in open(unit) if l.startswith("ExecStart="))[len("ExecStart="):].split()
argv = []
for w in line:
    if w in m:
        argv.append(m[w]); used.add(w)
    elif w.startswith("/") or w.startswith("$") or "%" in w:
        sys.exit(f"the rendered word {w} has no value")
    else:
        argv.append(w)
env = dict(os.environ)
for l in open(unit):
    if l.startswith("Environment="):
        for kv in l[len("Environment="):].split():
            k, v = kv.split("=", 1)
            if v in m:
                v = m[v]; used.add(kv.split("=", 1)[1])
            elif v.startswith("/") or "%" in v:
                sys.exit(f"the rendered value {k}={v} has no value")
            env[k] = v
            print("ENV", f"{k}={v}")
extra = set(m) - used
if extra:
    sys.exit(f"values no rendered word asks for: {sorted(extra)}")
print("ARGV", " ".join(argv))
r = subprocess.run(argv, stdin=subprocess.DEVNULL, capture_output=True, text=True, timeout=60, env=env)
print("EXIT", r.returncode)
print("STDERR", r.stderr.strip())
