# Reproduce the fixed proof

Use the full commit supplied in the submission, not the mutable branch tip.
The project root contains `lean-toolchain`, `lakefile.toml` and `lake-manifest.json`.

Lean: `leanprover/lean4:v4.34.1` (compiler
`5045d0056413266e57c625dcd7c365b10e377c52`).

| Dependency | Locked revision |
| --- | --- |
| mathlib | `d13f23b723b8a846827a245b89c10fc7d3f11612` |
| plausible | `118aa17ee84656b8bd727fef7c458ee8c833385c` |
| LeanSearchClient | `ddf04cf3949fa556442341e87d47f9f6e6074707` |
| importGraph | `e928b72544873815af278d38681b31c0293588e3` |
| proofwidgets | `106ff4fafc74ef4ac99d81dbf3ab399118f497a5` |
| aesop | `355695d523e41d0554926416cba2a2b3544fbbc9` |
| Qq | `6a489d9af5d0c47e5b259e2e8bcdfc1811b5a259` |
| batteries | `f2effa3d803fda822b1f97b806c47cf2adfbcbc2` |
| Cli | `e92c9f15fdfacc8536f31cfb3b7ad26c3c8cd204` |

With Git, elan and that toolchain installed, clone the authorized public original
repository after release, check out the selected full commit, and run:

```sh
lake exe cache get
lake clean
lake build
lake env lean StatementAudit.lean
lake env leanchecker --verbose Erdos1173 StatementAudit
lake env leanchecker --fresh --verbose StatementAudit
```

Dependency download requires network access. The checks themselves can run
without network after the dependencies and public cache are installed. Do not
run `lake update`: the lockfile already fixes the dependency versions. No global
resource settings or changes to another project's source tree are required.

Expected result: every command exits successfully. `StatementAudit.lean` prints
the types, relevant definitions and the complete transitive axiom lists for:

```text
Erdos1173.counterexample_isSetMapping
Erdos1173.counterexample_no_large_free_set
Erdos1173.erdos_1173_counterexample
Erdos1173.erdos_1173_negative
StatementAudit.original_statement_bridge
```

Each axiom list is exactly `[propext, Classical.choice, Quot.sound]`. There must
be no `sorryAx`, native-computation axiom, or custom unproved proof axiom.
The GCH hypothesis must remain explicit in the statement printed by the audit.

`leanchecker` is the official Lean kernel replay program. `--fresh` replays the
entire imported proof environment; it is not an independently implemented
external checker. The public library cache may be reused, but this is different
from a full rebuild of every dependency from source.
