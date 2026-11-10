# Completed verification and limits

Verification source: private original commit `e8c481bba7f41f0fa5b846e78807b3bf6db881ff`, 9 November 2026.
The five proof/build specification files here are byte-identical to that source.
Their SHA-256 values are in `verification/source-hashes.json`.

| Actual check at the original source | Result |
| --- | --- |
| Original-source correspondence and exact independent bridge | Pass, full original GCH question. |
| Windows Lean 4.34.1 source and bridge compilation | Exit 0. |
| Windows pinned `lake -v build` | Exit 0, 965 jobs. |
| Five complete transitive axiom audits | Only propext, Classical.choice, Quot.sound. |
| Windows official kernel replay | Exit 0. |
| Windows fresh imported-environment kernel replay | Exit 0. |
| All nine dependency revisions and tracked-tree status | Match lockfile; clean. |
| Isolated Linux source and bridge compilation | Exit 0. |
| Isolated Linux official kernel replay | Exit 0. |
| Isolated Linux fresh replay | Exit 0, 374.71 seconds. |

The Linux check used the exact same source with the official Linux toolchain,
`bubblewrap --unshare-all --clearenv`, no network or credentials, read-only tools
and dependency cache, and a writable private checkout. An initial Linux load
failed because the copied cache omitted `.ir.sig` files. The missing 946 files
were supplied and hash-checked, then all Linux checks passed without changing
the proof. The failed attempt is preserved privately and is not concealed.

The JSP `audit.py preflight` check also passed. Its `run` subcommand was not
executed; the source, statement, axioms, replay and isolation checks above were
run explicitly. No full automated skill-run receipt is claimed.

The copied logs in `verification/windows` and `verification/linux` are original
check output, with any local absolute paths replaced by `[PRIVATE_CHECKOUT]`.
The original unredacted evidence remains private. Packaging checks are recorded
outside this repository and identify its final commit.

## Mathematical reread

The paper was checked from its hypotheses to the conclusion: the sequence space
has the required size; the subset family is enumerable; each stage has at most
mu requests; each bounded depth has fewer than mu requests; selected points are
distinct from their center; intersections have a common finite-depth bound;
every large set has a small dense subset and a sufficiently late center outside
it; and transport preserves all conditions. No additional set-theoretic
principle is introduced. The exact GCH instance is also checked by the formal
bridge. The additional generality in the paper has a direct mathematical proof,
not a claimed generalized formal theorem.

## Limits of the conclusion

These are contributor-side, AI-assisted checks. No independent human verifier,
organizer acceptance, prize eligibility decision, external independent checker,
or priority ruling is asserted. The official replay uses Lean's own kernel.
Mathlib was not entirely rebuilt from source. The 2015 article in
`RELATED_WORK.md` has not been read in full, so novelty is not cleared.

## Release preparation checks

The packaged proof at commit
`82fe055ec3e396a22fbfe4d00dad47cadd1e452f` was additionally checked on
10 November 2026: two successful 965-job builds (including one with cache
downloading disabled), direct statement and axiom checks, and official kernel
replay. The kernel replay exited 0 after 98 seconds. A further 107 package
checks covered file digests, the original-statement references, manuscript,
and the catalog-only patch. `verification/packaged-checks.json` records the
completed proof checks. Subsequent release edits change documentation only;
the five proof and build inputs retain identical Git blobs. No new fresh
kernel replay is claimed for the documentation-only release.
