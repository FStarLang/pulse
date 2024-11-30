{
  inputs = {
    nixpkgs.url = "github:cachix/devenv-nixpkgs/rolling";
    systems.url = "github:nix-systems/default";
    fstar.url = "github:FStarLang/FStar/a94456863e3f971a7c63a64aca1a07d2cd9eb9a1";
    devenv.url = "github:cachix/devenv";
    devenv.inputs.nixpkgs.follows = "nixpkgs";
    flake-parts.url = "github:hercules-ci/flake-parts";
    treefmt-nix.url = "github:numtide/treefmt-nix";
    treefmt-nix.inputs.nixpkgs.follows = "nixpkgs";
  };

  nixConfig = {
    extra-trusted-public-keys = "devenv.cachix.org-1:w1cLUi8dv3hnoSPGAuibQv+f9TZLr6cv/Hm9XgU50cw=";
    extra-substituters = "https://devenv.cachix.org";
  };

  outputs = { self, ... }@inputs:

    inputs.flake-parts.lib.mkFlake { inherit inputs; } rec {

      systems = inputs.nixpkgs.lib.systems.flakeExposed;
      imports = [
        inputs.treefmt-nix.flakeModule
      ];

      perSystem = { pkgs, config, system, ... }: {

        treefmt.config = {
          projectRootFile = "flake.nix";
          flakeFormatter = true;
          flakeCheck = true;
          programs = {
            nixpkgs-fmt.enable = true;
            deadnix.enable = true;
            statix.enable = true;
          };
        };

        packages.pulse-dune = pkgs.ocaml-ng.ocamlPackages_4_14.buildDunePackage rec {

          pname = "pulse-dune";
          version = "2024.06.02";
          sourceRoot = "${src.name}/src/ocaml";

          src = pkgs.fetchFromGitHub {
            owner = "FStarLang";
            repo = pname;
            rev = "v${version}";
            hash = "sha256-jRm21FtPorAW/eQlXbqPyo2Ev0Kdv0evvGmSoPpNE7A=";
          };

          inherit (inputs.fstar.packages.${system}.fstar-dune) nativeBuildInputs;

          buildInputs = inputs.fstar.packages.${system}.fstar-dune.buildInputs ++ [ inputs.fstar.packages.${system}.fstar-dune ];

        };

        packages.pulse = pkgs.stdenv.mkDerivation rec {

          pname = "pulse";
          version = "2024.06.02";

          src = pkgs.fetchFromGitHub {
            owner = "FStarLang";
            repo = pname;
            rev = "v${version}";
            hash = "sha256-jRm21FtPorAW/eQlXbqPyo2Ev0Kdv0evvGmSoPpNE7A=";
          };

          inherit (inputs.fstar.packages.${system}.fstar-dune) nativeBuildInputs;

          buildInputs = inputs.fstar.packages.${system}.fstar-dune.buildInputs ++ [
            inputs.fstar.packages.${system}.fstar
            pkgs.which
          ];
          PATH = "${inputs.fstar.packages.${system}.fstar}/bin:$PATH";

          enableParallelBuilding = true;

          installPhase = ''
            PREFIX=$out make install
          '';

        };

        packages.pulse-exe = pkgs.writeShellScriptBin "pulse.exe" ''
          exec ${inputs.fstar.packages.${system}.fstar}/bin/fstar.exe "$1" \
            --include ${config.packages.pulse}/lib/pulse \
            --include ${config.packages.pulse}/lib/pulse/c \
            --include ${config.packages.pulse}/lib/pulse/core \
            --include ${config.packages.pulse}/lib/pulse/lib \
            --include ${config.packages.pulse}/lib/pulse/lib/class \
            --include ${config.packages.pulse}/lib/pulse/lib/ml \
            --include ${config.packages.pulse}/lib/pulse/lib/pledge \
            --load_cmxs pulse \
            "$@"
        '';

        devShells = {
          default = inputs.devenv.lib.mkShell {
            inherit inputs pkgs;
            modules = [
              {
                # https://devenv.sh/reference/options/
                packages = [
                  inputs.fstar.packages.${system}.z3
                ] ++ (with inputs.fstar.packages.${system}.ocamlPackages; [
                  menhir
                  batteries
                  menhirLib
                  pprint
                  ppx_deriving
                  ppx_deriving_yojson
                  ppxlib
                  process
                  sedlex
                  stdint
                  yojson
                  zarith
                ]);

                env.OCAMLPATH = "${inputs.fstar.packages.${system}.fstar}/lib/ocaml/4.14.1/site-lib";
                env.PULSE_HOME = ".";
                enterShell = ''
                  export PATH="${inputs.fstar.packages.${system}.fstar}/bin:$PATH"
                '';

                languages.ocaml = {
                  enable = true;
                  packages = inputs.fstar.packages.${system}.ocamlPackages;
                };

                scripts.pulse.exec = ''
                  fstar.exe $1 \
                    --include ./lib/pulse/lib/class \
                    --include ./lib/pulse/lib/pledge \
                    --include ./lib/pulse/lib/pulse \
                    --include ./lib/pulse/lib/pulse/core \
                    --include ./lib/pulse/lib/pulse/lib \
                    --load_cmxs lib/pulse/pulse
                '';
              }
            ];
          };
        };

        packages = {
          devenv-up = self.devShells.${system}.default.config.procfileScript;
          devenv-test = self.devShells.${system}.default.config.test;

          inherit (inputs.fstar.packages.${system}) fstar fstar-dune;
        };

      };
    };
}
