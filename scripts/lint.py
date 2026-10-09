#!/usr/bin/env python3
"""Check Kalman source hygiene, module boundaries, and completed proofs.

Like FLARE's lint driver, use Lean's dependency reader and include untracked
sources. Kalman's existing build targets supply specification and axiom audits.
Formatting is checked separately with leanfmt, whose default width is 90.
"""

import argparse
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
import subprocess
import sys

from fmt import source_files

ROOT = Path(__file__).resolve().parents[1]
ENTRY_POINTS = {
    "Kalman.lean",
    "Kalman/Tests/Specification.lean",
    "Kalman/Tests/ProofAudit.lean",
    "Kalman/Tests/FloatImplementations.lean",
    "Lint.lean",
}


def run(args, *, capture=False):
    return subprocess.run(args, cwd=ROOT, text=True, capture_output=capture, check=True)


def text_issues(name, source):
    issues = []
    if source and not source.endswith("\n"):
        issues.append(f"{name}: missing final newline")
    for number, line in enumerate(source.splitlines(), 1):
        if line.endswith((" ", "\t")):
            issues.append(f"{name}:{number}: trailing whitespace")
        if "\t" in line:
            issues.append(f"{name}:{number}: tab character")
    return issues


def reachable(graph, roots):
    seen = set()
    pending = list(roots)
    while pending:
        node = pending.pop()
        if node not in seen:
            seen.add(node)
            pending.extend(graph.get(node, ()))
    return seen


def layout_issues(graph):
    issues = []
    for name in sorted(ENTRY_POINTS - graph.keys()):
        issues.append(f"Missing lint entry point: {name}")
    for name in sorted(graph.keys() - reachable(graph, ENTRY_POINTS)):
        issues.append(f"Lean file outside the import closure: {name}")

    active, done = set(), set()

    def visit(name):
        if name in active:
            raise RuntimeError(f"Import cycle through {name}")
        if name in done:
            return
        active.add(name)
        for dependency in sorted(graph.get(name, ())):
            visit(dependency)
        active.remove(name)
        done.add(name)

    try:
        for name in sorted(graph):
            visit(name)
    except RuntimeError as error:
        issues.append(str(error))

    exported = reachable(graph, {"Kalman.lean"})
    for name in sorted(graph):
        if not name.startswith("Kalman/"):
            if name not in ENTRY_POINTS:
                issues.append(f"Unexpected Lean file outside the module trees: {name}")
            continue
        if name.startswith("Kalman/Tests/"):
            continue
        if name not in exported:
            issues.append(f"Kalman.lean does not expose {name}")
        if len(Path(name).parts) < 3:
            issues.append(f"Keep Kalman/ free of top-level Lean files: {name}")
        dependencies = reachable(graph, {name}) - {name}
        if "Kalman.lean" in dependencies:
            issues.append(f"{name}: library module imports the public entry point")
        forbidden = ("Kalman/Tests/",)
        if name.startswith("Kalman/Definitions/"):
            forbidden += ("Kalman/Implementation/", "Kalman/Proofs/")
        elif name.startswith("Kalman/Implementation/Correctness/"):
            forbidden += ("Kalman/Proofs/",)
        elif name.startswith("Kalman/Implementation/"):
            forbidden += ("Kalman/Proofs/", "Kalman/Implementation/Correctness/")
        elif not name.startswith("Kalman/Proofs/"):
            issues.append(f"Unrecognized module tree: {name}")
        for dependency in sorted(dependencies):
            if dependency.startswith(forbidden):
                issues.append(f"{name}: forbidden transitive dependency on {dependency}")
    return issues


def check_imports(files, jobs):
    own_files = set(files)

    def dependencies(name):
        result = run(["lake", "env", "lean", "--src-deps", name], capture=True)
        own = set()
        for line in result.stdout.splitlines():
            path = Path(line).resolve()
            if path.is_relative_to(ROOT):
                relative = path.relative_to(ROOT).as_posix()
                if relative in own_files:
                    own.add(relative)
        return name, own

    with ThreadPoolExecutor(max_workers=jobs) as pool:
        graph = dict(pool.map(dependencies, files))
    issues = layout_issues(graph)
    if issues:
        raise RuntimeError("Module layout:\n" + "\n".join(issues))
    print(f"Import closure and transitive layer boundaries pass ({len(files)} Lean files).", flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--jobs", type=int, default=4, help="import-check workers (default: 4)")
    parser.add_argument("--style-only", action="store_true", help="run only fast source hygiene checks")
    args = parser.parse_args()
    if args.jobs < 1:
        parser.error("--jobs must be positive")
    files = source_files()
    if not files:
        raise RuntimeError("No Lean files found; refusing an empty lint run")
    issues = [issue for name in files for issue in text_issues(name, (ROOT / name).read_text())]
    if issues:
        raise RuntimeError("Source hygiene:\n" + "\n".join(issues))
    print(f"Source hygiene passes ({len(files)} Lean files, including untracked files).", flush=True)
    if not args.style_only:
        run(["lake", "build"])
        check_imports(files, args.jobs)
        print("Lean extra linters, specification checks, and theorem axiom audit pass.", flush=True)
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except subprocess.CalledProcessError as error:
        if error.stdout:
            print(error.stdout, file=sys.stderr)
        if error.stderr:
            print(error.stderr, file=sys.stderr)
        sys.exit(error.returncode)
    except RuntimeError as error:
        print(error, file=sys.stderr)
        sys.exit(1)
