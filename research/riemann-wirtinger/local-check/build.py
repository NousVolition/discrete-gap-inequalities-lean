"""Compile named local Lean modules using explicitly supplied, existing dependencies."""
from pathlib import Path
import argparse, hashlib, json, os, re, subprocess, sys, time

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--lean", required=True, type=Path)
    parser.add_argument("--packages", required=True, type=Path)
    parser.add_argument("modules", nargs="+")
    args = parser.parse_args()
    root = Path(__file__).resolve().parent
    env = dict(os.environ)
    libraries = [root] + [p / ".lake/build/lib/lean" for p in args.packages.iterdir()
                          if (p / ".lake/build/lib/lean").is_dir()]
    env["LEAN_PATH"] = os.pathsep.join(map(str, libraries))
    env["LEAN_NUM_THREADS"] = "4"
    version = subprocess.check_output([str(args.lean), "--version"], text=True).strip()
    for name in args.modules:
        if not re.fullmatch(r"[A-Za-z][A-Za-z0-9_]*", name):
            raise ValueError("Invalid module name")
        source = root / (name + ".lean")
        before = hashlib.sha256(source.read_bytes()).hexdigest()
        started = time.monotonic()
        result = subprocess.run([str(args.lean), "-o", name + ".olean", name + ".lean"],
                                cwd=root, env=env, capture_output=True, text=True,
                                encoding="utf-8", errors="replace", timeout=240)
        (root / (name + ".log")).write_text(result.stdout + result.stderr, encoding="utf-8")
        assert hashlib.sha256(source.read_bytes()).hexdigest() == before
        report = {"module": name, "source_file": source.name, "source_sha256": before,
                  "exit_code": result.returncode, "lean": version,
                  "elapsed_seconds": round(time.monotonic() - started, 3)}
        (root / (name + ".build.json")).write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
        print(result.stdout + result.stderr, end="", flush=True)
        print(json.dumps(report), flush=True)
        if result.returncode:
            return result.returncode
    return 0

if __name__ == "__main__":
    sys.exit(main())
