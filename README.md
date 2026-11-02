# lean-ritsuryo

Japanese statutory period computations implemented in Lean 4, with proofs attached to the functions the CLI runs. The library covers 民法 第140条〜第143条, 年齢計算ニ関スル法律, 国税通則法 第10条, 民事訴訟法 第95条, and 国民の祝日に関する法律 第2条・第3条. The Lake package and the CLI are `ritsuryo`.

Each computation has two definitions: a spec that copies the structure of the provision, and an implementation the CLI runs. The theorems prove that they agree on every input, plus properties such as monotonicity and the least-holiday property of the rollover rules. `docs/basis.md` maps every provision to its spec, implementation, and theorems; `docs/interpretation.md` records how each provision is read.

## Commands

```console
$ nix develop                # Lean 4.35.0 (lake), make, python3, hyperfine
$ make check                 # format, lint, holiday data check, lake build (proofs), tests, basis report and axiom audit
$ make basis                 # regenerate docs/basis.md from the @[ritsuryo_basis] attributes
$ make holidays              # regenerate Ritsuryo/Holiday/Data/Generated.lean from data/syukujitsu.csv
$ make fetch-holidays        # download the Cabinet Office CSV, then regenerate
$ nix build                  # build the CLI into ./result/bin/ritsuryo
$ nix run . -- help
```

## CLI

The CLI takes input in the AWS CLI grammar: `ritsuryo [global options] <command> <subcommand> [--parameter value ...]`. Parameters are named `--kebab-case`; booleans are `--flag` / `--no-flag`; lists are space-separated values; a value starting with `file://` is read from the file. `--cli-input-json` takes all parameters as a JSON object whose keys are the PascalCase parameter names, and `--generate-cli-skeleton input|output` prints the input or output template. `help` works at every level (`ritsuryo help`, `ritsuryo period help`, `ritsuryo period compute-expiry help`).

| command | subcommand | Computes |
|---|---|---|
| `period` | `compute-expiry` | The last day of a period in days, weeks, months, or years (`--rule civil` for 民法 140〜143 条, `--rule national-tax-general` for 国税通則法 10 条 1 項), optionally rolled over with `--rollover-rule` |
| `period` | `compute-rollover` | Rollover of a date under `civil-142`, `civil-procedure-95`, or `national-tax-10` |
| `age` | `get-attainment-date` | The day a person attains an age |
| `age` | `compute-age` | The age at the end of a day |
| `holiday` | `list-holidays` | The year's holidays with their class (祝日法 2 条, 3 条 2 項, 3 条 3 項, special laws) |
| `holiday` | `check-holiday` | Which holiday classes and rollover rules apply to a date |

```console
$ ritsuryo period compute-expiry --event-date 2026-12-15 --weeks 2 --rollover-rule civil-procedure-95
$ ritsuryo age get-attainment-date --birth-date 2008-02-29 --age 18
$ ritsuryo age compute-age --birth-date 2008-02-29 --as-of 2026-02-28 --output table
$ ritsuryo holiday list-holidays --year 2027 --output text
$ ritsuryo period compute-expiry --generate-cli-skeleton input > input.json
$ ritsuryo period compute-expiry --cli-input-json file://input.json
```

Output keys are PascalCase: `Result`, `Steps` (start date, corresponding day, last day before rollover, skipped days), `Basis` (statute, provision, e-Gov law ID), `Assumptions` (the readings and inputs the result depends on), `Data` (the holiday CSV's source, Last-Modified, SHA-256, and year range when holidays were used), and `SchemaVersion`. `--output` is `json` (default), `text` (tab-separated, AWS style), or `table`.

Exit codes: 0 success, 252 command or parameter error, 254 input outside what the computation covers (nonexistent date, a year outside the holiday data, an as-of date before the birth date), 255 any other failure.

## Proved properties

All theorems are checked by `lake build`; none uses `sorry`, `admit`, or `native_decide`. `lake exe basis-report --check` fails if a public theorem depends on an axiom other than `propext`, `Classical.choice`, and `Quot.sound`, or if a design ID below has no theorem.

| ID | Theorem | Statement |
|---|---|---|
| CAL-1 | `Date.cal1_ofDays_toDays` | date → day number → date is the identity on valid proleptic Gregorian dates (`Int` years) |
| CAL-2 | `Date.cal2_toDays_ofDays` | day number → date → day number is the identity on all `Int`, and the date is valid |
| CAL-3 | `Date.cal3_lt_iff` | lexicographic date order equals day-number order |
| CAL-4 | `Date.cal4_nextDate` | the naive next day (month end, year end, leap years by cases) is day number + 1 |
| CAL-5 | `Date.cal5_weekday` | the weekday is the day number mod 7, and the next day has the next weekday |
| CAL-6 | `Date.cal6_daysInMonth` | month lengths match the day numbers, and February has 29 days exactly when 閏年ニ関スル件 (in 皇紀) makes the year a leap year |
| PER-1 | `Period.per1_compute_eq_spec` | the CLI's start date, corresponding day, and last day equal the 民法 140・143 条 spec |
| PER-2 | `Period.per2_from_beginning` | the 143 条 2 項 formula gives the calendar result for periods starting on the 1st, on 1 January, and on Sunday |
| PER-3 | `Period.per3_weeks_years` | n weeks equals 7n days; n years equals 12n months |
| PER-4 | `Period.per4_not_additive`, `Period.per4_bound` | 1 month + 1 month from 2025-01-31 ends on 03-31 but 2 months ends on 03-30; chaining is always 0〜3 days later |
| PER-5 | `Period.per5_monotone` | the last day is monotone in the event date and in the length |
| PER-6 | `Period.per6_months_from_event` | n months after an event end at the end of the month if the event is a month end, else on the event's day n months later (or that month's end) |
| PER-7 | `Period.per7_national_tax_general` | 国税通則法 10 条 1 項 gives the same last day as 民法 for days, months, and years |
| AGE-1 | `Period.Age.age1_attainment` | the attainment day is the day before the corresponding day; 29 February births attain on 28 February |
| AGE-2 | `Period.Age.age2_monotone_and_steps` | the age is exact between attainment days, monotone in the date, and steps by exactly 1 at each attainment day |
| ROL-1 | `Period.rol1_least_non_holiday` | the rollover result is on or after the date, not a holiday, and every day in between is a holiday |
| ROL-2 | `Period.rol2_idempotent_monotone` | rollover is idempotent, monotone in the date, and monotone in the holiday set |
| ROL-3 | `Period.rol3_procedure_vs_tax` | 国税通則法 10 条 2 項 with 1/2・1/3 as general holidays equals 民事訴訟法 95 条 3 項, and they agree on every other day either way |
| HOL-1 | `Holiday.hol1_derivation` | the 振替休日 and 国民の休日 functions equal the wording of 祝日法 3 条 2 項・3 項 |
| HOL-2 | `Holiday.hol2_nthMonday` | `nthMonday` returns a Monday whose day is in the n-th 7-day block of the month |
| HOL-C1 (check) | `Holiday.holc1_csv_rest_days` | for every year in the CSV, deriving 3 条 2 項・3 項 (in the version in force on each day) from the non-"休日" rows yields exactly the "休日" rows; decided by the kernel |

## Holiday data

`data/syukujitsu.csv` is the Cabinet Office CSV (https://www8.cao.go.jp/chosei/shukujitsu/syukujitsu.csv, Shift_JIS, Last-Modified 2026-02-02T00:30:17Z): 1,067 rows from 1955-01-01 to 2027-11-23, of which 116 are "休日", 2 are "休日（祝日扱い）", and 4 are special-law days (結婚の儀 ×2, 大喪の礼, 即位礼正殿の儀). `scripts/gen_holidays.py` turns it into per-year tables in `Ritsuryo/Holiday/Data/Generated.lean`; the build does not use the network. The `Holiday data` workflow downloads the CSV monthly, runs `make check` on it, and opens a pull request when it changed.

## Measurements

Measured on x86_64-linux (NixOS, 14 hardware threads).

| Item | Measured | How |
|---|---|---|
| CLI binary (nixpkgs `lean4` 4.35.0) | 2,040,288 bytes | `stat -c %s .lake/build/bin/ritsuryo` |
| Its shared libraries | `libstdc++`, `libgmp`, `libuv`, `libssl`, `libcrypto`, `libm`, `libdl`, `libgcc_s`, `libpthread`, `libc`, interpreter and all from `/nix/store` | `readelf -d`, `ldd` |
| CLI startup | `--version` 8.8 ms ± 1.8 ms; `period compute-expiry` with 民訴 rollover 9.4 ms ± 1.9 ms; `holiday list-holidays --output table` 9.9 ms ± 1.6 ms; 12.5〜14.5 MiB peak memory | `hyperfine -N --warmup 20 --runs 300` |
| CLI binary (upstream `leanprover/lean4:v4.35.0` via elan) | 3,066,224 bytes; needs only `libc`, `libm`, `libdl`, `libpthread`, `libgcc_s`, `ld-linux` (the Lean runtime, GMP, and libuv are linked statically); `--version` 5.0 ms ± 0.9 ms | `lake build ritsuryo` with the elan toolchain, `readelf -d`. On NixOS elan patches the interpreter and RUNPATH to `/nix/store`, so portability to other distributions still has to be checked on a GitHub-hosted runner |
| Upstream toolchain | 92.5 s to install, 3,138,011,370 bytes unpacked | `elan toolchain install leanprover/lean4:v4.35.0`, `du -sb` |
| Clean build | 19.9 s for the library, all proofs, and the CLI (`lake build` after `rm -rf .lake`); `Ritsuryo.Holiday.Check` (HOL-C1) takes 7.5 s of it, `Ritsuryo.Calendar.Proofs` 5.3 s | wall clock, per-module times from Lake |
| HOL-C1 by `decide` | 8.3 s with `decide +kernel`, 14.3 s with plain `decide`, for 1955〜2027 | `lake env lean` on the check minus the 1.0 s import baseline |
| Every-day variant of HOL-C1 | 29 s for 10 years (3,652 days) with `decide +kernel` | the same, comparing the derivation with the CSV on every day; the shipped check evaluates only the days after a 国民の祝日 |

Binary size depends on how the library loads its attribute. The attribute module imports `Lean`; library modules load it with `meta import`, so the CLI does not link `Lean`:

| Program | Size | Startup |
|---|---|---|
| hello world, non-`module` `Main.lean` | 3,276,456 bytes | 8.7 ms ± 1.6 ms |
| prints a date from the library, which loads the attribute with plain `import Lean` | 140,294,384 bytes | 48.2 ms ± 8.6 ms |
| same program, library modules use `meta import` | 1,546,056 bytes | 8.5 ms ± 1.7 ms |
| same program plus `import Lean.Data.Json` | 134 MiB | 51.4 ms ± 9.4 ms |

The CLI therefore uses its own JSON module (`Ritsuryo/Cli/Json.lean`) rather than `Lean.Json`.

Distribution: the Nix flake (`nix run github:conao3/lean-ritsuryo`) for v0.1.0. Release binaries for GitHub Releases are to be built with the upstream toolchain on GitHub-hosted runners, whose output needs only glibc.

## Layout

```
Ritsuryo/
  Law.lean, Basis.lean, Audit.lean   statutes and e-Gov IDs, @[ritsuryo_basis], report and audit
  Calendar/                          Date, day numbers, weekday, CAL proofs
  Period/
    Spec/                            民法 138〜143 条, 142 条, 民事訴訟法 95 条, 国税通則法 10 条
    HolidayClass.lean, Impl.lean, Age.lean, Rollover.lean
    Proofs/                          PER, AGE, ROL proofs
  Holiday/
    Spec.lean, Proofs.lean           祝日法 2 条・3 条, HOL proofs
    Data.lean, Data/Generated.lean   CSV tables
    Lookup.lean, Check.lean          lookup, era-aware derivation, HOL-C1
  Cli/                               JSON, argument parsing, rendering, command table
Main.lean                            the ritsuryo CLI
BasisReport.lean                     lake exe basis-report
Tests/, TestMain.lean                lake test
scripts/                             CSV generator, lint, CLI tests
data/                                the Cabinet Office CSV
docs/                                basis.md (generated), interpretation.md
```

## License

Apache-2.0
