with import <nixpkgs> {};
mkShell {
  nativeBuildInputs = [ autoPatchelfHook ];
  buildInputs = [ glibc gmp zlib ];
  shellHook = ''
    autoPatchelf ./mathsat
  '';
}
