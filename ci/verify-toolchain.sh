#!/usr/bin/env bash
set -euo pipefail
export LC_ALL=C

# setup-ocaml exports OPAMCOLOR=always. Even --short output can contain ANSI
# escapes, including with --columns=package. Request plain output explicitly.
if ! installed_packages=$(opam list --installed --short --columns=package --color=never); then
  echo '::error::Unable to query the installed OPAM packages.' >&2
  exit 1
fi
printf 'Installed OPAM packages (name.version):\n%s\n' "$installed_packages"

for expected in \
  ocaml.5.3.0 \
  rocq-core.9.3.0 \
  rocq-runtime.9.3.0 \
  coq-core.9.3.0 \
  rocq-stdlib.9.2.0; do
  if ! grep -Fxq -- "$expected" <<< "$installed_packages"; then
    package_name=${expected%%.*}
    actual=$(awk -F . -v name="$package_name" '$1 == name' <<< "$installed_packages")
    printf '::error::Expected installed package %s; found %s.\n' \
      "$expected" "${actual:-no installed version of this package}" >&2
    exit 1
  fi
  printf 'Verified package: %s\n' "$expected"
done

if ! ocaml_version=$(opam exec -- ocamlc -version); then
  echo '::error::Unable to execute ocamlc in the selected OPAM switch.' >&2
  exit 1
fi
if [[ "$ocaml_version" != '5.3.0' ]]; then
  printf '::error::Expected ocamlc version 5.3.0; got %q.\n' "$ocaml_version" >&2
  exit 1
fi
printf 'Verified ocamlc: %s\n' "$ocaml_version"
