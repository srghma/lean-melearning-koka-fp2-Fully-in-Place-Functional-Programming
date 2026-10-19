{
  description = "Rust tail-rec vs iter reverse benchmark";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
  };

  outputs = { nixpkgs, ... }:
    let
      systems = [ "x86_64-linux" "aarch64-linux" "x86_64-darwin" "aarch64-darwin" ];
      forEachSystem = nixpkgs.lib.genAttrs systems;
    in {
      devShells = forEachSystem (system: {
        default = nixpkgs.legacyPackages.${system}.mkShell {
          packages = with nixpkgs.legacyPackages.${system}; [
            cargo
            rustc
            lld
          ];
          out = "/tmp/nix-shell-out";
          shellHook = ''
            export NIX_LDFLAGS=""
            export CARGO_TARGET_DIR="/tmp/rust_reverse_bench_target"
          '';
        };
      });
    };
}
