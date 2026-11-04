{
  description = "Japanese statutory period computation with Lean 4 proofs";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixpkgs-unstable";
    flake-parts.url = "github:hercules-ci/flake-parts";
    treefmt-nix.url = "github:numtide/treefmt-nix";
  };

  outputs =
    inputs@{ flake-parts, ... }:
    flake-parts.lib.mkFlake { inherit inputs; } {
      systems = [
        "x86_64-linux"
        "aarch64-darwin"
      ];

      imports = [ inputs.treefmt-nix.flakeModule ];

      perSystem =
        { pkgs, ... }:
        {
          packages.default = pkgs.stdenv.mkDerivation {
            pname = "ritsuryo";
            version = "0.5.0";
            src = pkgs.lib.cleanSource ./.;
            nativeBuildInputs = [ pkgs.lean4 ];
            buildPhase = ''
              runHook preBuild
              export HOME="$TMPDIR"
              lake build ritsuryo
              runHook postBuild
            '';
            installPhase = ''
              runHook preInstall
              install -Dm755 .lake/build/bin/ritsuryo "$out/bin/ritsuryo"
              runHook postInstall
            '';
            meta = {
              description = "Japanese statutory period computation with Lean 4 proofs";
              homepage = "https://github.com/conao3/lean-ritsuryo";
              license = pkgs.lib.licenses.asl20;
              mainProgram = "ritsuryo";
              platforms = pkgs.lib.platforms.unix;
            };
          };

          devShells.default = pkgs.mkShell {
            packages = with pkgs; [
              lean4
              gnumake
              hyperfine
              python3
            ];
          };

          treefmt.programs = {
            nixfmt.enable = true;
            ruff-format.enable = true;
          };
        };
    };
}
