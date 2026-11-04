# BellantoniCook

[![Rocq 9.3](https://github.com/sylvainheraud/bellantonicook/actions/workflows/rocq.yml/badge.svg?branch=master)](https://github.com/sylvainheraud/bellantonicook/actions/workflows/rocq.yml?query=branch%3Amaster)

It was developed by Sylvain Heraud and David Nowak.

This is a deep embedding of Bellantoni and Cook's syntactic characterization of polytime functions. We prove formally that it is correct and complete with respect to the original characterization by Cobham that required a bound to be proved manually. Compared to the paper proof by Bellantoni and Cook, we have been careful in making our proof fully constructive so that we obtain more precise bounding polynomials and more efficient translations between the two characterizations. Another difference is that we consider functions on bitstrings instead of functions on positive integers. This formalization is described in:

Sylvain Heraud and David Nowak.
_A formalization of polytime functions._
In Interactive Theorem Proving - Second International Conference, ITP 2011, Berg en Dal, The Netherlands, August 22-25, 2011. Proceedings, volume 6898 of Lecture Notes in Computer Science, pages 119--134.
Springer, 2011.

The 2026 technical modernization makes this historical development build and
pass kernel checking with Rocq 9.3.0. It preserves the mathematical definitions
and results; it does not claim a new mathematical result. The
[historical repository maintained by David Nowak](https://github.com/davidnowak/bellantonicook)
remains the reference for the original development.

## License

BellantoniCook is distributed under the **CeCILL Free Software License
Agreement version 2.1** (SPDX: `CECILL-2.1`). See [LICENSE](LICENSE).

The `LICENSE` file has contained the full CeCILL 2.1 text since the initial
2018 import ([`de94ed60`](https://github.com/davidnowak/bellantonicook/commit/de94ed60da2a92f3724136e525f84493579f29f7)).
The original README and OPAM metadata instead mentioned `CeCILL-A`, which
is not an official designation in the CeCILL license family. The 2026
metadata correction aligns those references with the existing `LICENSE`
file. The original license text, historical commits, and proof sources are
unchanged; no relicensing is intended.

This alignment resolves the repository's inconsistent labels but is not
independent evidence of both original authors' legal intentions.

## Building

### Rocq 9.3.0

This version ports all 16 Coq source files to Rocq 9.3.0 and its standard
library. Install Rocq and the standard library in your chosen environment,
with `coqc`, `coq_makefile`, and `coqchk` available on `PATH`.

For an isolated OPAM environment matching the compiler and proof-library
versions used by CI (OPAM must already be initialized):

```sh
opam switch create . ocaml-base-compiler.5.3.0 --no-install
opam install --yes rocq-core.9.3.0 coq-core.9.3.0 rocq-stdlib.9.2.0
eval "$(opam env)"
```

`rocq-core.9.3.0` depends on `rocq-runtime.9.3.0`. The separate
`coq-core.9.3.0` compatibility package supplies the `coqc`, `coq_makefile`,
and `coqchk` commands used by this project. The standard library is versioned
separately. The `rocq-prover`
package is a meta-package; its version is not the Rocq executable version.
Do not install the historical `opam/opam` file for this port.

Build the library and independently check every compiled module:

```sh
make
make check
```

For a complete rebuild, run `make clean` followed by `make check`.
`make install` remains optional and installs into the active Rocq environment.
The build uses Rocq 9.3's Findlib package scheme (`bellantonicook`).

The port preserves the historical mathematical definitions, theorem statements,
section hypotheses, and bitstring conventions, including `cond`.
The historical Coq sources are authoritative if they differ from the paper;
the port does not change their semantics to match the publication.
`Lib.v` supplies compatibility abbreviations for renamed standard-library
objects and proved arithmetic identities. The historical `omega` calls use
`lia`; the old propositional parity predicates use the corresponding inductive
predicates `Nat.Even_alt` and `Nat.Odd_alt`, not the boolean parity functions.

The historical eliminators for the five types containing nested lists are
provided explicitly and registered with Rocq. Their proof terms and types
are preserved; registering a list `All` scheme instead would change the
automatically generated induction principles.

One parsing warning remains intentionally in `BCI.v`: the historical postfix
composition notation `h (nl, sl)` has precedence 50. Moving it to the recommended
precedence 1 makes ordinary applications such as `f (projIn 0)` fail to
parse, because the notation now expects a comma inside the parentheses.
Its original declaration is retained, and no warnings are hidden.
All other warnings from a clean build have been removed. Warnings are not
treated globally as errors while this compatibility warning remains.

Inspect the logical assumptions of the central results with:

```sh
coqtop -q -R src/BellantoniCook BellantoniCook <<'EOF'
Require Import BellantoniCook.BC_to_Cobham BellantoniCook.Cobham_to_BC.
Print Assumptions BC_to_Cobham.BC_to_Cobham_correct.
Print Assumptions BC_to_Cobham.BC_to_Cobham_bounded.
Print Assumptions Cobham_to_BC.Cobham_to_BC_correct.
Print Assumptions Cobham_to_BC.Cobham_to_BC_inf.
Print Assumptions Cobham_to_BC.rec_simulation_correct.
Print Assumptions BC.sem_cost_correct.
Print Assumptions BC.sem_cost_bounded.
EOF
```

All seven results report `Closed under the global context` on Rocq 9.3.0.
This means no global axioms are used; the explicit premises in their types
remain essential. In particular, `sem_cost_bounded` is parameterized by the
primitive costs, their polynomial bounds, and the required arity conditions.
Use `About BC.sem_cost_bounded.` to inspect its complete type.

### Continuous integration

[The GitHub Actions workflow](.github/workflows/rocq.yml) runs on pushes,
pull requests, and manual dispatch. It uses Ubuntu 24.04, OCaml 5.3.0,
Rocq 9.3.0, and Stdlib 9.2.0. The action revisions are pinned to full commit
identifiers. OPAM installs the dependencies from scratch and records the
resolved package versions in the job log; transitive OPAM dependencies and
the hosted operating-system image are not frozen bit for bit.

The workflow runs `opam exec -- bash ci/check.sh`. This script checks the
expected 16 source files, executes `make clean && make check`, checks the
16 compiled objects, and rejects tracked compilation artifacts. `make check`
invokes `coqchk` on all 16 module names. A compiler or checker failure makes
the job fail. The remaining notation warning stays visible.

Run the same checks locally with:

```sh
opam exec -- bash ci/check.sh
```

Successful local checks do not establish that a hosted Actions run has passed;
that requires publishing the branch and inspecting the actual run.

### Historical version

Commit `1f03b9296104646ddc2b2b4b12e35a6619c17a99` preserves the 2018 sources.
Its README reports compatibility with Coq 8.6.0 through 8.8.1. The historical `opam/` dependency constraints remain for the older Coq
packaging; only the license metadata has been aligned with the existing
`LICENSE` text. This OPAM file does not describe installation of the Rocq 9.3
port. The build instructions above apply to this
version. No historical Coq compiler was used to validate the port.
