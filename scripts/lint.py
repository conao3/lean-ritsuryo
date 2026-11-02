import subprocess
import sys

SUFFIXES = (".lean", ".md", ".py", ".nix", ".toml", ".yml", ".json", ".csv")
MAX_LEAN_LINE = 100


def tracked_files():
    out = subprocess.run(
        ["git", "ls-files", "--cached", "--others", "--exclude-standard"],
        check=True,
        capture_output=True,
        text=True,
    ).stdout
    return [f for f in out.splitlines() if f.endswith(SUFFIXES) or f == "Makefile"]


def check(path):
    problems = []
    with open(path, encoding="utf-8") as f:
        text = f.read()
    if text and not text.endswith("\n"):
        problems.append(f"{path}: missing final newline")
    for i, line in enumerate(text.splitlines(), 1):
        if line != line.rstrip():
            problems.append(f"{path}:{i}: trailing whitespace")
        if path.endswith(".lean"):
            if "\t" in line:
                problems.append(f"{path}:{i}: tab character")
            if len(line) > MAX_LEAN_LINE and not path.endswith("Generated.lean"):
                problems.append(f"{path}:{i}: line longer than {MAX_LEAN_LINE}")
    return problems


def main():
    problems = [p for f in tracked_files() for p in check(f)]
    for p in problems:
        print(p, file=sys.stderr)
    return 1 if problems else 0


if __name__ == "__main__":
    sys.exit(main())
