# Measurements

The numbers behind the build and packaging decisions. Measured on x86_64-linux (NixOS, 14 hardware threads) with Lean 4.35.0.

## The library loads its attribute with `meta import`

The attribute module `Ritsuryo.Basis` imports `Lean`. A plain `import` of it would link all of `Lean` into every program that uses the library.

Loading it with `meta import` keeps the attribute at compile time only, and the binary stays the size of hello world:

| Program | Size | Startup |
|---|---|---|
| hello world, non-`module` `Main.lean` | 3,276,456 bytes | 8.7 ms ± 1.6 ms |
| prints a date from the library, which loads the attribute with plain `import Lean` | 140,294,384 bytes | 48.2 ms ± 8.6 ms |
| same program, library modules use `meta import` | 1,546,056 bytes | 8.5 ms ± 1.7 ms |
| same program plus `import Lean.Data.Json` | 134 MiB | 51.4 ms ± 9.4 ms |

## The CLI has its own JSON module

`Lean.Data.Json` pulls in `Lean` the same way: the last row above is 134 MiB and starts in 51 ms. The CLI reads and writes JSON with `Ritsuryo/Cli/Json.lean` and stays at a few MB.

## Release builds use the upstream toolchain

The nixpkgs `lean4` links its runtime libraries from `/nix/store`, so that binary runs only where those store paths exist. The upstream toolchain links the Lean runtime, GMP, and libuv statically, which leaves only the C library:

| Build | Size | Shared libraries |
|---|---|---|
| nixpkgs `lean4` 4.35.0 (`nix build`) | 2,609,384 bytes | `libstdc++`, `libgmp`, `libuv`, `libssl`, `libcrypto`, `libm`, `libdl`, `libgcc_s`, `libpthread`, `libc`, all from `/nix/store` |
| upstream `leanprover/lean4:v4.35.0` (v0.5.0 release, x86_64-linux) | 3,586,512 bytes | `libc`, `libm`, `libpthread`, `libdl`, `librt`, `ld-linux` |

Each release runner pays for the upstream toolchain: 92.5 s to install and 3,138,011,370 bytes unpacked (`elan toolchain install leanprover/lean4:v4.35.0`, `du -sb`).

## HOL-C1 is decided by the kernel on the days after a 国民の祝日

`decide +kernel` checks HOL-C1 for 1955〜2027 in 8.3 s. Plain `decide` takes 14.3 s.

The shipped check evaluates only the days after a 国民の祝日, where a 振替休日 or 国民の休日 can arise. Comparing the derivation with the CSV on every day takes 29 s for 10 years (3,652 days) alone.

Times are `lake env lean` on the check minus the 1.0 s import baseline.

## Build time

A clean `lake build` (library, all proofs, CLI, after `rm -rf .lake/build`) takes 26.1 s wall clock. The longest modules, from Lake's per-module times:

| Module | Time |
|---|---|
| `Ritsuryo.Tax.Proofs.Income` | 14 s |
| `Ritsuryo.Tax.Proofs.Penalty` | 14 s (in parallel with the one above) |
| `Ritsuryo.Holiday.Check` (HOL-C1) | 9.0 s |
| `Ritsuryo.Calendar.Proofs` | 6.5 s |
| `Ritsuryo.Holiday.Article2Check` (HOL-C2) | 4.1 s |
