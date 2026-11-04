#!/usr/bin/env bash
# Run from any directory, with the selected Rocq toolchain on PATH.
set -euo pipefail
export LC_ALL=C
cd "$(dirname "$0")/.."

expected=(
  BC BCBinary BCI BCI_to_BC BCLib BCUnary BC_to_BCI BC_to_Cobham
  Bitstring Cobham CobhamBinary CobhamLib CobhamUnary Cobham_to_BC Lib MultiPoly
)
sources=(src/BellantoniCook/*.v)
test "${#sources[@]}" -eq "${#expected[@]}"
for module in "${expected[@]}"; do
  test -f "src/BellantoniCook/$module.v"
done

coqc --version
test "$(coqc --print-version | cut -d ' ' -f 1)" = "9.3.0"

# Do not suppress warnings: BCI's historical postfix notation still emits one.
# make check invokes coqchk on every module and propagates its exit status.
make clean && make check

for module in "${expected[@]}"; do
  test -s "src/BellantoniCook/$module.vo"
done

tracked_files=$(git ls-files)
if printf '%s\n' "$tracked_files" | grep -E '(^|/)(Makefile\.coq(\.conf)?|\.Makefile\.coq\.d|META(\.bellantonicook)?|\.(lia|nia)\.cache|.*\.(vo|vos|vok|glob|aux))$'; then
  echo 'Compilation artifacts must not be tracked by Git.' >&2
  exit 1
fi

echo 'Compiled and kernel-checked all 16 BellantoniCook modules.'
