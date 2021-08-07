{ srcs ? import ./nix/sources.nix, nixpkgs ? srcs.nixpkgs }

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
