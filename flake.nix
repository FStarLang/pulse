{
  inputs = {
    devenv.inputs.nixpkgs.follows = "nixpkgs";
    devenv.url = "github:cachix/devenv";
    flake-parts.url = "github:hercules-ci/flake-parts";
    fstar.url = "github:FStarLang/FStar/v2025.02.17";
    nixpkgs.url = "github:cachix/devenv-nixpkgs/rolling";
  };

  nixConfig = {
    extra-trusted-public-keys = "devenv.cachix.org-1:w1cLUi8dv3hnoSPGAuibQv+f9TZLr6cv/Hm9XgU50cw=";
    extra-substituters = "https://devenv.cachix.org";
  };

  outputs = { self, ... }@inputs:

    inputs.flake-parts.lib.mkFlake { inherit inputs; } {

      systems = inputs.nixpkgs.lib.systems.flakeExposed;
      imports = [ ];

      perSystem = { pkgs, config, system, ... }: {

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

        packages.rustast-bindings = pkgs.rustPlatform.buildRustPackage rec {
          inherit (config.packages.pulse) version src;
          inherit (inputs.fstar.packages.${system}.fstar) nativeBuildInputs;
          pname = "rustast-bindings";
          sourceRoot = "${src.name}/pulse2rust/src/ocaml";
          cargoLock = {
            lockFile = ./pulse2rust/src/ocaml/Cargo.lock;
          };
          postPatch = ''
            ln -s ${./pulse2rust/src/ocaml/Cargo.lock} Cargo.lock
          '';
        };

        packages.extract = pkgs.stdenv.mkDerivation {
          pname = "extract";
          inherit (config.packages.pulse) version;
          src = pkgs.fetchFromGitHub {
            owner = "FStarLang";
            repo = "pulse";
            rev = "42842b823c45f83376b65bc10ffa803ad6f21dc4";
            hash = "sha256-CRlrfiDXoSn9s0tiU4dunsUsUu00jb8U9/QApfu+Qtw=";
          };
          sourceRoot = "source/pulse2rust/src";
          buildInputs = [
            inputs.fstar.packages.${system}.fstar
            pkgs.which
          ];
          PATH = "${inputs.fstar.packages.${system}.fstar}/bin:$PATH";

          installPhase = ''
            mkdir -p $out/ocaml/generated
            cp -r ocaml/generated $out/ocaml
          '';
        };

        packages.pulse2rust = inputs.fstar.inputs.nixpkgs.legacyPackages.${system}.ocaml-ng.ocamlPackages_4_14.buildDunePackage rec {
          inherit (config.packages.pulse) version src;
          pname = "main";
          sourceRoot = "${src.name}/pulse2rust/src/ocaml";

          nativeBuildInputs = inputs.fstar.packages.${system}.fstar.nativeBuildInputs ++ [ inputs.fstar.packages.${system}.fstar ];
          buildInputs = inputs.fstar.packages.${system}.fstar.buildInputs ++ [ inputs.fstar.packages.${system}.fstar ];

          buildPhase = ''
            eval $(${inputs.fstar.packages.${system}.fstar}/bin/fstar.exe --ocamlenv)
            mkdir -p $out/bin
            dune build main.exe --build-dir=$out/bin
          '';

          postPatch = ''
            ln -s ${./pulse2rust/src/dune-project} dune-project
            ln -s ${config.packages.rustast-bindings}/lib/librustast_bindings.a librustast_bindings.a
            mkdir -p ocaml/generated
            cp -r ${config.packages.extract}/ocaml/generated ocaml
          '';

          # overwrites the default dune installPhase
          installPhase = '''';

          meta.mainProgram = "default/ocaml/main.exe";
        };

        devShells = {
          default = inputs.devenv.lib.mkShell {
            inherit inputs pkgs;
            modules = [
              {
                # https://devenv.sh/reference/options/
                env.FSTAR_EXE = "${inputs.fstar.packages.${system}.fstar}/bin/fstar.exe";
                env.FSTAR_HOME = "${inputs.fstar.packages.${system}.fstar}/lib/fstar";
                env.PULSE_HOME = "${config.packages.pulse}/lib/pulse";

                languages.rust = {
                  enable = true;
                };
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
