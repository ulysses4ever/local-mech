let
  pkgs = import <nixpkgs> {};
in pkgs.mkShell {
  packages = [
    pkgs.rocq-core
    pkgs.rocqPackages.stdlib
  ];
}
