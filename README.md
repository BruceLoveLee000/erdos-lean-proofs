# Erdős problem proofs in Lean

Lean 4 proofs of [Erdős problems](https://www.erdosproblems.com/) and of cases of them, stated
against the definitions in
[google-deepmind/formal-conjectures](https://github.com/google-deepmind/formal-conjectures).
Each problem has its own directory under `ErdosProofs/`, with the Lean files and a README that
gives the statement, what is proved, the idea of the proof, and how the proof was found.

| Problem | Directory | Proved | Status of the problem |
| --- | --- | --- | --- |
| [881](https://www.erdosproblems.com/881) | [`ErdosProofs/Erdos881`](ErdosProofs/Erdos881) | the case `k = 2`, and a 1980 question of Erdős and Nathanson | open for `k ≥ 3` |

## Build

```bash
lake exe cache get
lake build
```

Every theorem listed in a problem README depends only on the axioms `propext`,
`Classical.choice` and `Quot.sound`. Each problem directory has an `Axioms.lean` module whose build
prints them.

## Palomar projects

[`palomar/erdos881-k2`](palomar/erdos881-k2) is a self-contained copy of the Problem 881 proof
in the layout of the [Palomar registry](https://palomar-registry.org): a Mathlib-only
`Challenge.lean`, a `Solution.lean`, a Comparator configuration and a `formalization.yaml`. It
builds on a newer Lean toolchain than the rest of the repository, so it has its own
`lean-toolchain` and Lake files; build it from its own directory.

## How these proofs are found

The proofs come from an automated search with AI models in the
[tokens-as-parameters](https://github.com/BruceLoveLee000/tokens-as-parameters) framework and are
checked by the Lean kernel. Each problem README describes the search that produced its proof.
If you know an earlier proof of a result here, please open an issue.

## License

Apache License 2.0. See [LICENSE](LICENSE).
