{
  description = "Agda with 1lab";

  inputs = {
    flake-utils.url = "github:numtide/flake-utils";
    onelab = {
      url = "github:the1lab/1lab?rev=e5a99a399a3c58922adef713f38314805810937c";
      flake = false;
    };
  };

  outputs =
    {
      self,
      flake-utils,
      onelab,
    }:
    let
      overlay =
        final: prev:
        let
          Agda = prev.labHaskellPackages.Agda.nodebug.overrideAttrs (previousAttrs: {
            meta = (previousAttrs.meta or { }) // {
              mainProgram = "agda";
            };
          });
          agdaPackages = (prev.agdaPackages.override { inherit Agda; }).overrideScope (
            self: super: {
              _1lab = super._1lab.overrideAttrs {
                version = "0-unstable-2026-05-18";
                src = onelab;
              };
            }
          );
        in
        {
          inherit agdaPackages;
          agda = agdaPackages.agda;
        };
    in
    flake-utils.lib.eachDefaultSystem (
      system:
      let
        pkgs =
          (import (onelab + "/support/nix/nixpkgs.nix") {
            inherit system;
          }).extend
            overlay;
      in
      {
        devShells.default = pkgs.mkShell {
          buildInputs = [
            (pkgs.agda.withPackages (p: [ p._1lab ]))
          ];
        };
      }
    );
}
