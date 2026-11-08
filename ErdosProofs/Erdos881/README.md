# Erdős Problem 881, case k = 2

[Problem 881](https://www.erdosproblems.com/881): let `A ⊆ ℕ` be an additive basis of order `k`
that is minimal, in the sense that `A \ B` is not a basis of order `k` for any infinite `B ⊆ A`.
Must some infinite `B ⊆ A` leave `A \ B` a basis of order `k + 1`? The problem is open.

[`K2.lean`](K2.lean) proves:

| Theorem | Statement |
| --- | --- |
| `Erdos881K2.infinite_deletion_of_two_basis` | Every asymptotic basis of order 2 contains an infinite set whose removal leaves an asymptotic basis of order 3. No minimality is assumed. |
| `Erdos881K2.erdos_881_two` | The case `k = 2` of `Erdos881.erdos_881`, in the formal-conjectures statement. |
| `Erdos881K2.not_minimal_three_of_two_basis` | No minimal asymptotic basis of order 3 is an asymptotic basis of order 2. Erdős and Nathanson asked this in *Minimal asymptotic bases for the natural numbers*, J. Number Theory 12 (1980), p. 155, and proved the weaker statement for order 4. |

The cases `k = 0` and `k = 1` are easy; the cases `k ≥ 3` remain open. A write-up posted on the
problem's forum claims a counterexample for every `k ≥ 2`; the theorem above rules this out for
`k = 2`.

The definitions follow formal-conjectures: `h • A` is the sumset of exactly `h` elements, and
`0` may belong to `A`. The result also holds when a basis of order `h` means "at most `h`
summands": apply the theorem to `A ∪ {0}` and remove `0` from the deleted set.

We found no earlier proof of these statements in the literature we checked. If you know one,
please open an issue.

## How the proof works

The proof splits on whether some positive difference `d` occurs infinitely often in `A`, that
is, whether `b` and `b + d` are both in `A` for infinitely many `b`.

1. **A repeated difference.** Then there are fixed `x ≠ y` in `A` and infinitely many `b ∈ A` with
   `b + x` and `b + y` both sums of two elements of `A \ {b}`. Choose infinitely many such `b`,
   sparse enough that none is used in another's representations and all in one residue class,
   and delete them. A large `n` missing from the threefold sumset would need `n = x + u + v` and
   `n = y + p + q` with `u, v, p, q` all deleted, which the residue class rules out.
2. **Infinite gaps.** Delete elements one at a time, protecting the representations already used
   and keeping one coverage threshold throughout. This can only get stuck at a trap: a finite
   deletion after which only finitely many single elements are removable. In a two-basis with
   infinite gaps there is no trap: three far-apart anchors show that a removal can destroy only
   boundedly many targets.

## Check it

From the repository root:

```bash
lake exe cache get
lake build ErdosProofs.Erdos881.Axioms
```

The build prints the axioms of each theorem; each lists only `propext`, `Classical.choice` and
`Quot.sound`.

## How this proof was found

The proof was found by an automated search with AI models in the
[tokens-as-parameters](https://github.com/BruceLoveLee000/tokens-as-parameters) framework,
with GPT-6.1 agents working in parallel and web research enabled, and then checked by the Lean kernel. The search ran on the
full statement of Problem 881 and settled `k = 2` as a subgoal. The proof in this repository is the
search's Lean code, reduced to the declarations the three theorems use; the comments and this
README were rewritten with Claude (Anthropic). No human wrote the mathematical argument.
