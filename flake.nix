{
  description = "Sources for siraben.dev";
  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    utils.url = "github:numtide/flake-utils";
  };

  outputs = { self, nixpkgs, utils, ... }:
    utils.lib.eachDefaultSystem (system:
      let
        pkgs = import nixpkgs { inherit system; };
        jekyll_env = pkgs.bundlerEnv {
          name = "jekyll_env";
          ruby = pkgs.ruby;
          gemdir = ./.;
        };
      in
      {
        packages.default = pkgs.stdenv.mkDerivation {
          pname = "siraben.dev";
          version = "head";
          src = ./.;
          buildInputs = [ jekyll_env ];
          buildPhase = ''
            JEKYLL_ENV=production jekyll build --destination $out/public
          '';
          dontInstall = true;
        };

        devShells.default = pkgs.mkShell {
          buildInputs = [ jekyll_env ];
          shellHook = ''
            echo "Jekyll dev environment ready. Run 'jekyll serve' to start."
          '';
        };
      }
    );
}
