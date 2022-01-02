{ srcs ? import ./nix/sources.nix, pkgs ? import srcs.nixpkgs {} }:
with pkgs;

stdenv.mkDerivation {
  name = "env";
  buildInputs = [
    ruby.devEnv
    git
    sqlite
    libpcap
    postgresql
    libxml2
    libxslt
    pkg-config
    bundix
    gnumake
  ];
}
