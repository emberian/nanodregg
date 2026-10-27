"""Prove gates/size_limit.py can fail (gates/journal_plants.py's pattern): a control tree holding a
1048577-byte file is red by name, an allow row admits it while its ceiling and malformed rows go
red, and a mutant with the size comparison disabled lets the over-limit file escape."""
import argparse
import os
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
AT_LIMIT, OVER_LIMIT, ABOVE_CEILING = 1048576, 1048577, 2000001


def run_gate(script: str, root: str) -> subprocess.CompletedProcess:
    return subprocess.run([sys.executable, "-I", script, root], capture_output=True, text=True)


def control(root: str) -> None:
    for rel, n in (("small/ok.bin", AT_LIMIT), ("big/blob.bin", OVER_LIMIT)):
        path = os.path.join(root, rel)
        os.makedirs(os.path.dirname(path), exist_ok=True)
        with open(path, "wb") as fh:
            fh.write(b"\0" * n)


def write_table(root: str, text: str) -> None:
    table = os.path.join(root, "gates", "size-allow.tsv")
    os.makedirs(os.path.dirname(table), exist_ok=True)
    with open(table, "w", encoding="utf-8") as fh:
        fh.write(text)


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--real", nargs=3, metavar=("ROOT", "PATH", "BYTES"))
    a = ap.parse_args()
    real = os.path.join(HERE, "size_limit.py")
    with tempfile.TemporaryDirectory() as d:
        tree = os.path.join(d, "control")
        control(tree)
        r = run_gate(real, tree)
        assert r.returncode == 1, "control: a tree with a 1048577-byte file must be red"
        assert "big/blob.bin: 1048577 bytes" in r.stdout, "control: the red must name big/blob.bin at 1048577 bytes"
        assert "small/ok.bin" not in r.stdout, "control: the 1048576-byte file must not be named"

        write_table(tree, "# path\tbytes-ceiling\treason\nbig/blob.bin\t2000000\tthe plant's synthetic blob\n")
        r = run_gate(real, tree)
        assert r.returncode == 0, "allow: a row with the file under its ceiling admits the 1048577-byte file"
        with open(os.path.join(tree, "big", "blob.bin"), "wb") as fh:
            fh.write(b"\0" * ABOVE_CEILING)
        r = run_gate(real, tree)
        assert r.returncode == 1, "allow: a file grown above its ceiling must be red"
        assert "exceeds its allowlist ceiling 2000000" in r.stdout, "allow: the red must name the ceiling"
        write_table(tree, "# path\tbytes-ceiling\treason\nbig/blob.bin\t5\tunder the limit, so malformed\n")
        r = run_gate(real, tree)
        assert r.returncode == 1, "allow: a malformed row must be red"
        assert "gates/size-allow.tsv:2" in r.stdout, "allow: the red must name the malformed row's line"

        # An export (scripts/gate-lib.sh materialize) holds untracked build output beside the tracked
        # files: its index names what is tracked, and only that is judged.
        g = os.path.join(d, "repo.git", ".git")
        os.makedirs(g)
        subprocess.run(["git", "init", "-q", "--bare", g], check=True)
        exp = os.path.join(g, "standing", "tree")
        for rel, n in (("testground/kernel.wasm", 5_000_000), ("tracked/big.bin", OVER_LIMIT)):
            os.makedirs(os.path.dirname(os.path.join(exp, rel)), exist_ok=True)
            with open(os.path.join(exp, rel), "wb") as fh:
                fh.write(b"\0" * n)
        env = dict(os.environ, GIT_DIR=g, GIT_WORK_TREE=exp, GIT_INDEX_FILE=exp + ".index")
        subprocess.run(["git", "update-index", "--add", "tracked/big.bin"], check=True, env=env, cwd=exp)
        r = run_gate(real, exp)
        assert r.returncode == 1 and "tracked/big.bin: 1048577 bytes" in r.stdout, "export: a tracked over-limit file must be red"
        assert "kernel.wasm" not in r.stdout, "export: an untracked 5 MB file must not be named"
        subprocess.run(["git", "update-index", "--force-remove", "tracked/big.bin"], check=True, env=env, cwd=exp)
        r = run_gate(real, exp)
        assert r.returncode == 0, "export: with nothing over the limit tracked, an untracked 5 MB file is not red"

        source = open(real, encoding="utf-8").read()
        n = source.count("size > LIMIT")
        assert n == 1, f"mutant: 'size > LIMIT' occurs {n} times in gates/size_limit.py, expected exactly 1"
        mutant = os.path.join(d, "mutant", "size_limit.py")
        os.makedirs(os.path.dirname(mutant), exist_ok=True)
        with open(mutant, "w", encoding="utf-8") as fh:
            fh.write(source.replace("size > LIMIT", "size > LIMIT * 0 + 10**18"))
        mutant_tree = os.path.join(d, "mutant-tree")
        control(mutant_tree)
        r = run_gate(mutant, mutant_tree)
        assert r.returncode == 0, "mutant: with the size comparison disabled the 1048577-byte file escapes"
        print("PLANT RED: size comparison disabled -> the 1048577-byte file escapes; the real gate refuses it")

    if a.real:
        root, path, byt = a.real
        r = run_gate(real, root)
        assert r.returncode == 1, "real: this tree is over the limit and the real gate must be red"
        assert f"{path}: {byt} bytes" in r.stdout, f"real: the red must name {path} at {byt} bytes"
    print("SIZE_LIMIT PLANTS GREEN")
    return 0


if __name__ == "__main__":
    sys.exit(main())
