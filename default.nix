(import (
  let
    lock = builtins.fromJSON (builtins.readFile ./flake.lock);
  in fetchTarball {
    url = "https://github.com/edolstra/flake-compat/archive/${lock.nodes.flake-compat.locked.rev}.tar.gz";
    sha256 = lock.nodes.flake-compat.locked.narHash; }
) {
  src =  ./.;
}).defaultNix

  
# { srcs ? import ./nix/sources.nix, pkgs ? import srcs.nixpkgs {} }:
# with pkgs;

# let
#   jekyll_env = bundlerEnv rec {
#     name = "jekyll_env";
#     inherit ruby;
#     gemdir = ./.;
#   };
# in
# stdenv.mkDerivation rec {
#   name = "jekyll_env";
#   buildInputs = [ jekyll_env ];
# }
