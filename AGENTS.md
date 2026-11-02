# AGENTS.md

`lean-ritsuryo` computes Japanese statutory periods (民法 140〜143 条, 国税通則法 10 条, 民事訴訟法 95 条, 年齢計算ニ関スル法律, 祝日法) in Lean 4, with proofs attached to the functions the CLI runs. The Lake package and the CLI are `ritsuryo`; the root namespace is `Ritsuryo`.

## Layout

- `Ritsuryo/Law.lean`: the statutes referenced by the library, with their e-Gov law IDs.
- `Ritsuryo/Basis.lean`: the `@[ritsuryo_basis "<statute>" "<provision>"]` and `@[ritsuryo_proof "<ID>"]` attributes. Library modules load it with `meta import`, so the CLI binary does not link `Lean`.
- `Ritsuryo/Audit.lean` and `BasisReport.lean`: `lake exe basis-report` renders `docs/basis.md`; `--check` fails on a public definition without a basis, a theorem using an axiom other than `propext`, `Classical.choice`, `Quot.sound`, or a missing design ID.
- `Main.lean`: the `ritsuryo` CLI.
- `Tests/`, `TestMain.lean`: the test executable run by `lake test`.
- `scripts/`: repository checks.

## Conventions

- Every library file is a `module`. Definition files use `@[expose] public section` so proofs in other modules can unfold them; library code loads `Ritsuryo.Basis` with `meta import`.
- Each public definition under `Ritsuryo.Calendar`, `Ritsuryo.Period`, and `Ritsuryo.Holiday` carries `@[ritsuryo_basis]`. Each theorem listed in the design carries `@[ritsuryo_proof "<ID>"]`.
- Proofs use core tactics only (`omega`, `decide`, `simp`, `grind`). `sorry`, `admit`, and `native_decide` do not appear in theorems.
- Docstrings quote statute text; other comments are not added.
- Commit messages, comments, and docs are in English. Statute quotes and CLI output strings stay in Japanese where the statute uses them.

## Verification

Run everything inside the devShell:

```console
$ nix develop --command make check
$ nix build
```

After adding or renaming a `.lean` file, run `git add -N <file>` before `nix build` (the flake only sees tracked files). After changing an attribute, regenerate the report with `make basis`.
