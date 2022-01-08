{
  description = "Sources for siraben.github.io";
  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    utils.url = "github:numtide/flake-utils";
    flake-compat = {
      url = "github:edolstra/flake-compat";
      flake = false;
    };
  };

  outputs = { self, nixpkgs, utils, ... }:
    utils.lib.eachDefaultSystem (system:
      with import nixpkgs { inherit system; };
      let
        jekyll_env = bundlerEnv rec {
          name = "jekyll_env";
          inherit ruby;
          gemdir = ./.;
        };
      in
        {
          defaultPackage = stdenv.mkDerivation {
            pname = "siraben.github.io";
            version = "head";
            src = ./.;
            buildInputs = [ jekyll_env ];
            buildPhase = ''
              JEKYLL_ENV=production jekyll build --destination $out/public
            '';
            dontInstall = true;
          };
          devShell = stdenv.mkDerivation rec {
            src = ./.;
            name = "jekyll_env";
            buildInputs = [ jekyll_env ];
          };
        }
    );
}
