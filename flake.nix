{
  inputs = {
    devenv.inputs.nixpkgs.follows = "nixpkgs";
    devenv.url = "github:cachix/devenv";
    flake-parts.url = "github:hercules-ci/flake-parts";
    fstar.url = "github:FStarLang/FStar/v2025.02.17";
    nixpkgs.url = "github:cachix/devenv-nixpkgs/rolling";
    treefmt-nix.inputs.nixpkgs.follows = "nixpkgs";
    treefmt-nix.url = "github:numtide/treefmt-nix";
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

        packages.pulse = pkgs.stdenv.mkDerivation rec {

          pname = "pulse";
          version = "84b3fc39e2ba16059408d4df039d4a03efa85b16";

          src = pkgs.fetchFromGitHub {
            owner = "FStarLang";
            repo = pname;
            rev = "${version}";
            hash = "sha256-Cg6z4pbSbPIaU1Jfcw78XVTxqLq5Jt+CajoyxHaeCVo=";
          };

          inherit (inputs.fstar.packages.${system}.fstar) nativeBuildInputs;

          buildInputs = inputs.fstar.packages.${system}.fstar.buildInputs ++ [
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
            --include ${config.packages.pulse}/lib/pulse/checker \
            --include ${config.packages.pulse}/lib/pulse/extraction \
            --include ${config.packages.pulse}/lib/pulse/lib \
            --include ${config.packages.pulse}/lib/pulse/ml \
            --include ${config.packages.pulse}/lib/pulse/syntax_extension \
            --load_cmxs pulse \
            "$@"
        '';

        devShells = {
          default = inputs.devenv.lib.mkShell {
            inherit inputs pkgs;
            modules = [
              {
                # https://devenv.sh/reference/options/
                packages = with inputs.fstar.packages.${system}; [ z3 ];

                env.FSTAR_EXE = "${inputs.fstar.packages.${system}.fstar}/bin/fstar.exe";
                env.FSTAR_HOME = "${inputs.fstar.packages.${system}.fstar}/lib/fstar";
                env.PULSE_HOME = "${config.packages.pulse}/lib/pulse";
                env.OCAMLPATH = "${inputs.fstar.packages.${system}.fstar}/lib/ocaml/4.14.1/site-lib";
                enterShell = ''
                  export PATH="${inputs.fstar.packages.${system}.fstar}/bin:$PATH"
                '';

                languages.rust = {
                  enable = true;
                };

                scripts.pulse.exec = ''
                  fstar.exe $1 \
                    --include ./lib/pulse/lib/class \
                    --include ./lib/pulse/lib/pledge \
                    --include ./lib/pulse/lib/pulse \
                    --include ./lib/pulse/lib/pulse/core \
                    --include ./lib/pulse/lib/pulse/lib \
                    --load_cmxs lib/pulse/pulse \
                    "$@"
                '';
              }
            ];
          };
        };

        packages = {
          default = config.packages.pulse;

          devenv-up = self.devShells.${system}.default.config.procfileScript;
          devenv-test = self.devShells.${system}.default.config.test;

          inherit (inputs.fstar.packages.${system}) fstar;
        };

      };
    };
}
