{
  inputs = {
    flake-parts.url = "github:hercules-ci/flake-parts";
    fstar.url = "github:FStarLang/FStar/v2025.03.25";
    nixpkgs.url = "github:nixos/nixpkgs/nixos-unstable";
  };

  outputs = { ... }@inputs:

    inputs.flake-parts.lib.mkFlake { inherit inputs; } {

      systems = inputs.nixpkgs.lib.systems.flakeExposed;
      imports = [ ];

      perSystem = { pkgs, config, system, ... }: {

        packages.pulse = pkgs.stdenv.mkDerivation rec {

          pname = "pulse";
          version = "9a03472d2c366bde5f7b0497bf3356dd445ce207";
          src = pkgs.fetchFromGitHub {
            owner = "FStarLang";
            repo = pname;
            rev = "${version}";
            hash = "sha256-YgWxnX+gCVYx+CCIuprDYKewyEaSekqAilB96eyq+fk=";
          };

          inherit (pkgs.fstar) nativeBuildInputs;
          buildInputs = pkgs.fstar.buildInputs ++ [
            pkgs.fstar
            pkgs.which
          ];
          PATH = "${pkgs.fstar}/bin:$PATH";

          enableParallelBuilding = true;

          installPhase = ''
            PREFIX=$out make install
          '';

        };

        packages.pulse-exe = pkgs.writeShellScriptBin "pulse.exe" ''
          exec ${pkgs.fstar}/bin/fstar.exe "$1" \
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
          inherit (pkgs.fstar) nativeBuildInputs;
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
            pkgs.fstar
            pkgs.which
          ];
          PATH = "${pkgs.fstar}/bin:$PATH";

          installPhase = ''
            mkdir -p $out/ocaml/generated
            cp -r ocaml/generated $out/ocaml
          '';
        };

        packages.pulse2rust = inputs.fstar.inputs.nixpkgs.legacyPackages.${system}.ocaml-ng.ocamlPackages_4_14.buildDunePackage rec {
          inherit (config.packages.pulse) version src;
          pname = "main";
          sourceRoot = "${src.name}/pulse2rust/src/ocaml";

          nativeBuildInputs = pkgs.fstar.nativeBuildInputs ++ [ pkgs.fstar ];
          buildInputs = pkgs.fstar.buildInputs ++ [ pkgs.fstar ];

          buildPhase = ''
            eval $(${pkgs.fstar}/bin/fstar.exe --ocamlenv)
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

        packages.fstar = pkgs.fstar;

        packages.default = config.packages.pulse;

      };
    };
}