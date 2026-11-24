# A quantitative lower-tail bound for random stable matchings

In a market with $n$ participants on each of two sides, each participant independently chooses a uniformly random strict ranking of the other side. A complete matching is stable if no unmatched pair both prefer each other to their assigned partners. Let $S_n$ be the number of stable matchings.

There are absolute constants $C,t_0>0$ such that for each fixed $0<t<t_0$,

$$
\limsup_{n\to\infty}\mathbb{P}(S_n\le t\,n\log n)
\le C t^2\log(e/t).
$$

The bound makes explicit how the asymptotic probability of a small count decreases as the threshold $t$ decreases.

## Authorship

The fixed-threshold lower-tail result is joint work by Bo Cowgill and Will Cook. It builds on Bo Cowgill's earlier proof of the qualitative Lennon–Pittel conjecture. [Palomar v3][v3]

Bo Cowgill maintains this Lean project. OpenAI Codex was used to formalize the proof in Lean and assist with verification.

## Formal statement

[Challenge.lean](Challenge.lean) states `LennonPittel.fixed_threshold_lower_tail` and defines the finite model. A profile consists of $2n$ permutations, each sending a candidate to that candidate's rank. The uniform law on the finite profile type gives each ranking independently and uniformly. The stable matching count uses the exclusion of strict blocking pairs.

The constants precede the quantifier over $t$, and $t$ is fixed before $n$ tends to infinity. The probability includes equality at the threshold.

[Solution.lean](Solution.lean) supplies the proof from [FixedThreshold.lean](LennonPittel/Quantitative/FixedThreshold.lean). A working paper version is forthcoming.

## Proof outline

1. Weight each sole exposed rotation by its length. The resulting bounds on expected participation below $b\sqrt n$ and above $A\sqrt n$, divided by $n\log n$, have limiting orders $b^2$ and $\exp(-A^2/32)$.
2. Use the rotation walk to find enough eligible anchors between these cutoffs. At each such anchor, count matchings obtained by undoing small compatible rotations. The conditional mean of this count is bounded below by an absolute multiple of $(b/A)n\log n$ when enough anchors are present.
3. Use the centered second moment for the count at fixed cutoffs. The probability of going below half the conditional-mean floor is bounded by the probability of too few anchors plus a term tending to zero. Taking $A^2$ proportional to $\log(e/t)$ and $b$ proportional to $tA$ gives the stated rate.

## Local verification

Run these commands from the project root with Elan installed.

```sh
lake exe cache get
lake --wfail build Solution
```

On Linux with Bubblewrap and unprivileged user namespaces, run `scripts/verify-comparator.sh`. On macOS, run `scripts/verify-comparator.sh --local-exports` from a trusted checkout. The macOS command compares exports from separate local builds with Comparator's sandbox disabled. Both commands use Lean Comparator with NanoDa and con-ron. The Challenge contains one deliberate `sorry` at the headline statement. The comparator axiom allowlist is `propext`, `Quot.sound`, and `Classical.choice`. [Palomar submission guide][palomar]

The project uses Apache-2.0. See [LICENSE](LICENSE) and [formalization.yaml](formalization.yaml) for attribution and provenance.

[v3]: https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-07-000001&version=3
[palomar]: https://palomar-registry.org/how-to-submit
