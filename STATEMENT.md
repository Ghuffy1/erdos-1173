# Original statement and complete correspondence

Source: [Erdős problem 1173](https://www.erdosproblems.com/1173).
Primary historical source: P. Erdős and A. Hajnal, *Unsolved and solved problems
in set theory*, Proceedings of Symposia in Pure Mathematics 25 (1974), 269–287,
Problem 35, printed p. 278. The correction there identifies the desired free set
size as aleph_(omega+1). The earlier 1971 list, printed p. 34, Problem 35, must be
read together with this correction. The 1999 collection *Some of Paul's favorite
problems*, Problem 7.88, supplies a later formulation.

Assume GCH. For a self-avoiding map f from omega_(omega+1) to subsets of that
ordinal, suppose every f(alpha) has cardinality at most aleph_omega, and every
intersection f(alpha) cap f(beta), for alpha != beta, has size less than
aleph_omega. The question asks whether f must have a free set of size
aleph_(omega+1). Here free means that for distinct a,b in the set, b is not in f(a).

The answer established here is negative. One such f is constructed and every
subset Y of size aleph_(omega+1) has distinct a,b in Y with b in f(a).

## Fixed reference statement

The comparison reference is proposed for maintainer review, not represented as a
JSP-approved statement: `google-deepmind/formal-conjectures`, commit
`3afb9beda5bcb9933e6e10276e87f8ccfd851222`,
`FormalConjectures/ErdosProblems/1173.lean` (blob
`d52baa912d26d201cbde876941a244102b8090fb`). Its GCH definition is in
`FormalConjecturesForMathlib/SetTheory/Cardinal/ContinuumHypothesis.lean`
(blob `2dc4ec4a8da10e05826166610abdb06faa1f4f25`).

The exact independently written target is `StatementAudit.OriginalCounterexample`
at `StatementAudit.lean:10`. `StatementAudit.original_statement_bridge` proves it
at line 19. No construction-specific predicate appears in its specification.

| Original condition | Coverage |
| --- | --- |
| GCH | Explicit sole mathematical premise of the final theorems; the definition quantifies over all universe-zero ordinals. |
| Domain omega_(omega+1) | `(ω_ (ω + 1 : Ordinal.{0})).ToType`, exactly, not a smaller domain. |
| Self-avoidance | `Erdos1173.counterexample_isSetMapping`, first conjunct. |
| All row sizes at most aleph_omega | Same declaration, second conjunct. |
| All distinct-row intersections strictly smaller than aleph_omega | Same declaration, third conjunct; no uniform smaller bound assumed. |
| No free set of cardinality aleph_(omega+1) | `Erdos1173.counterexample_no_large_free_set`; the bridge explicitly provides a forbidden pair in every such Y. |
| Negative answer to the universal question | `Erdos1173.erdos_1173_negative`. |

## Exposition-to-formalization correspondence

The paper uses the alphabet mu and its increasing subcardinals; the proof uses
the disjoint union of representatives of aleph_n. Both alphabets have cardinality
aleph_omega, and their bounded parts have smaller cardinality. Finite prefixes
give the same sequence-space construction. The paper enumerates every mu-sized
subset; the code injects that family into the same ordinal index, which suffices.
The code injects the active requests into the alphabet, a restriction of the
paper's schedule for all earlier indices. Neither difference alters any bound.

The cardinal estimates, bounded-depth exception bound, separation of distinct
prefixes, small dense subset, late center outside that subset, and transport by
bijection are all proved. No countable union of arbitrary sets of size less than
aleph_omega is assumed small. The intersection argument takes a union of only
two sets bounded by the same infinite aleph_N.

The paper's Theorem 1.1 is proved directly for any uncountable cardinal of
countable cofinality satisfying 2^mu = mu^+. Its Corollary 3.1 is the exact
formalized GCH case. The formal theorem does not assert or prove GCH itself.

## Proposed JSP mapping

The mathematical description matches JSP-000978, catalog-0901-1000.md.
JSP numbers and Erdős problem numbers are distinct; JSP-000978 is not Erdős 978.
The catalog description is abbreviated, so this exact correspondence and the
historical sources are submitted for maintainer review.
