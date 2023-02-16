{
  description = "agda-unimath";

  inputs = {
    # TODO: Move to unstable when https://github.com/NixOS/nixpkgs/pull/215925
    # merges, needed for Agda 2.6.3
    nixpkgs.url = "github:NixOS/nixpkgs/haskell-updates";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = { self, nixpkgs, flake-utils }:
    flake-utils.lib.eachDefaultSystem
      (system:
        let
          pkgs = nixpkgs.legacyPackages."${system}";
          agda = pkgs.agda;
        in
        {
          devShells.default = pkgs.mkShell {
            name = "agda-unimath";

            # Build tools
            nativeBuildInputs = [
              agda
              # part of `make check`
              pkgs.time
            ];

            # Runtime dependencies
            buildInputs = [ ];
          };

          devShell = self.devShells."${system}".default;
        });
}
