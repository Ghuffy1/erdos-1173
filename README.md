# A set mapping with small intersections and no large free set

**Private preparation copy. Publication has not been authorized.**

Will Howe, Grant Huffman, Jensen Kohlmeyer, and Liam Kruer, in alphabetical surname order.

The [paper](paper/A_Set_Mapping_With_No_Large_Free_Set.pdf) proves that if mu is
uncountable, cf(mu) = aleph_0 and 2^mu = mu^+, there is a self-avoiding set mapping
on mu^+ with rows of size at most mu, pairwise intersections of size less than mu,
and no free subset of size mu^+. In particular it gives a negative answer to
[Erdős problem 1173](https://www.erdosproblems.com/1173) under the question's GCH
assumption. The [source manuscript](paper/A_Set_Mapping_With_No_Large_Free_Set.tex)
contains the full proof and is independent of the formal verification material.

The formalization proves the full original GCH instance. It does not formalize
the paper's additional arbitrary-singular-cardinal generality.

## Files and targets

- `Erdos1173.lean`: construction and negative answer.
- `StatementAudit.lean`: separately stated exact-original-problem bridge.
- `STATEMENT.md`: original problem, correspondence and coverage matrix.
- `REPRODUCE.md`: fixed toolchain, dependencies, commands and expected axioms.
- `VERIFICATION.md`: actual completed checks and their limits.
- `AUTHORS.md`: requested joint credit and explicit AI involvement.
- `RELATED_WORK.md`: checked sources and the unresolved 2015 full-text comparison.

The principal declarations are `Erdos1173.erdos_1173_counterexample`,
`Erdos1173.erdos_1173_negative`, and `StatementAudit.original_statement_bridge`.
All five audited targets depend only on `propext`, `Classical.choice`, and
`Quot.sound`. GCH is an explicit hypothesis, not a hidden proof axiom.

## Status

The original proof sources were checked at private commit `e8c481bba7f41f0fa5b846e78807b3bf6db881ff`.
The proof, bridge, toolchain, build file and lockfile here are byte-for-byte
identical. No third-party private material or private development history is
included in this preparation repository.

This is a complete proof submission candidate, not an accepted prize record.
No firstness claim, organizer verification, independent human referee report,
arXiv acceptance, or prize award is asserted. The 2015 paper identified in
`RELATED_WORK.md` remains unread in full; its possible overlap is unresolved.

The planned public destination, only after explicit authorization, is
`https://github.com/Ghuffy1/erdos-1173`. That repository has not been created by this preparation.
