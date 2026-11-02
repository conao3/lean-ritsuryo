# lean-ritsuryo

Japanese statutory computations (periods under 民法 140〜143 条 and the procedural and tax rules built on them) implemented in Lean 4, with proofs attached to the functions the CLI runs. The Lake package and the CLI are `ritsuryo`.

## Commands

```console
$ nix develop                # Lean 4.35.0 (lake), make, python3, hyperfine
$ make check                 # format, lint, lake build (proofs), lake test, basis report and axiom audit
$ make basis                 # regenerate docs/basis.md from the @[ritsuryo_basis] attributes
$ nix build                  # build the CLI into ./result/bin/ritsuryo
$ nix run . -- help
```

## M0 measurements

Measured on x86_64-linux (NixOS) with nixpkgs `lean4` 4.35.0.

| Binary | Size | Startup (hyperfine, 300 runs, mean ± σ) | Peak memory |
|---|---|---|---|
| hello world, non-`module` `Main.lean` | 3,276,456 bytes | 8.7 ms ± 1.6 ms | 12.9 MiB |
| prints a date from the library, library uses plain `import Lean` for its attribute | 140,294,384 bytes | 48.2 ms ± 8.6 ms | 77.2 MiB |
| same program, library is a `module` that loads the attribute with `meta import` | 1,546,056 bytes | 8.5 ms ± 1.7 ms | 12.2 MiB |

Startup is `hyperfine -N --warmup 20 --runs 300 .lake/build/bin/ritsuryo`. The library therefore uses the Lean module system and loads `Ritsuryo.Basis` (which imports `Lean`) only at compile time.

`ldd` of the nixpkgs-built binary lists `libstdc++.so.6`, `libgmp.so.10`, `libuv.so.1`, `libssl.so.3`, `libcrypto.so.3`, `libm`, `libdl`, `libgcc_s`, `libpthread`, `libc`, all from `/nix/store`. The ELF interpreter is also a `/nix/store` path, so this binary runs only where those store paths exist.

Distribution for v0.1.0: the Nix flake (`nix run github:conao3/lean-ritsuryo`). Prebuilt binaries for GitHub Releases need a build with the upstream Lean release toolchain; see the toolchain measurement below.

## License

Apache-2.0
