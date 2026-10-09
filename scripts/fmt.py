#!/usr/bin/env python3
"""Format project Lean sources with leanfmt's default width (90 columns).

Adapted from FLARE's formatter wrapper. Include untracked sources, preserve
NUL-delimited Git paths, and restore any file with non-whitespace changes.
"""

import argparse
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]


def source_files():
    output = subprocess.check_output(
        ["git", "ls-files", "--cached", "--others", "--exclude-standard", "-z", "--", "*.lean"],
        cwd=ROOT,
    ).decode()
    return sorted({name for name in output.split("\0") if name and (ROOT / name).is_file()})


def format_files(files, *, check=False, jobs=4):
    if not files:
        raise RuntimeError("No Lean files found; refusing an empty formatting run")
    originals = {name: (ROOT / name).read_bytes() for name in files} if not check else {}
    command = ["lake", "exe", "fmt", "--jobs", str(jobs)]
    if check:
        command.append("--check")
    result = subprocess.call([*command, *files], cwd=ROOT)
    damaged = []
    for name, original in originals.items():
        path = ROOT / name
        if "".join(original.decode().split()) != "".join(path.read_text().split()):
            path.write_bytes(original)
            damaged.append(name)
    if damaged:
        print("Restored files after non-whitespace changes:\n" + "\n".join(damaged), file=sys.stderr)
        return 1
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true", help="check without rewriting")
    parser.add_argument("--jobs", type=int, default=4, help="formatter workers (default: 4)")
    args = parser.parse_args()
    if args.jobs < 1:
        parser.error("--jobs must be positive")
    return format_files(source_files(), check=args.check, jobs=args.jobs)


if __name__ == "__main__":
    try:
        sys.exit(main())
    except subprocess.CalledProcessError as error:
        sys.exit(error.returncode)
    except RuntimeError as error:
        print(error, file=sys.stderr)
        sys.exit(1)
