{ srcs ? import ./nix/sources.nix, pkgs ? import srcs.nixpkgs {} }:
with pkgs;

let
  jekyll_env = bundlerEnv rec {
    name = "jekyll_env";
    inherit ruby;
    gemdir = ./.;
  };
in
stdenv.mkDerivation rec {
  name = "jekyll_env";
  buildInputs = [ jekyll_env ];
}
