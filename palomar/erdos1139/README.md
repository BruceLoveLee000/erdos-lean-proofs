# Erdős Problem 1139 (Palomar project)

This directory is a self-contained Lean project in the layout of the
[Palomar registry](https://palomar-registry.org). It contains the proof of
[Erdős Problem 1139](https://www.erdosproblems.com/1139) from
[`ErdosProofs/Erdos1139`](../../ErdosProofs/Erdos1139), ported so that it builds on Lean v4.35.0
with Mathlib alone.

## The problem and the result

Let `1 ≤ u₁ < u₂ < ⋯` be the integers with at most two prime factors, counted with multiplicity.
Problem 1139 asks whether `limsup (u_{k+1} − u_k) / log k = ∞`.

[`Challenge.lean`](Challenge.lean) states, and [`Solution.lean`](Solution.lean) proves:

| Theorem | Statement |
| --- | --- |
| `Erdos1139Proof.erdos_1139` | With `u = Nat.nth (fun n ↦ 0 < n ∧ Ω n ≤ 2)`, the limsup in `EReal` of `(u (k + 1) − u k) / log (k + 1)` is `⊤`. This is `Erdos1139.erdos_1139` from formal-conjectures. |

Indexing from 0 and dividing by `log (k + 1)` instead of `log k` do not change the limsup. See
[`ErdosProofs/Erdos1139/README.md`](../../ErdosProofs/Erdos1139/README.md) for prior work and an
outline of the proof.

## Files

| File | Contents |
| --- | --- |
| [`Challenge.lean`](Challenge.lean) | The statement, importing only Mathlib. |
| [`Solution.lean`](Solution.lean) | Imports the proof development, which proves the statement under the same name. |
| [`Erdos1139/Proof.lean`](Erdos1139/Proof.lean) | The proof: [`ErdosProofs/Erdos1139/Main.lean`](../../ErdosProofs/Erdos1139/Main.lean), ported to Lean v4.35.0. |
| [`comparator.json`](comparator.json) | The [Comparator](https://github.com/leanprover/comparator) configuration. |
| [`formalization.yaml`](formalization.yaml) | Provenance, classification, automation and review metadata. |

## The statement

formal-conjectures builds with Lean v4.33.1, but Palomar requires Lean v4.35.0-rc2 or later, so
this project cannot depend on it. The statement of `Erdos1139.erdos_1139` uses only Mathlib
definitions (`Nat.nth`, `ArithmeticFunction.cardFactors`, `Filter.limsup`, `EReal`), so
`Challenge.lean` states it verbatim. Printed with `pp.all`, the statement in `Challenge.lean`, in
`Solution.lean`, in `ErdosProofs/Erdos1139/Main.lean` and in formal-conjectures are identical.

## The port

`Erdos1139/Proof.lean` imports Mathlib instead of the formal-conjectures statement and omits
`erdos_1139_fc`, which restates the theorem through that statement. Its other changes follow Mathlib
renames between the two toolchains; they are listed in the file's docstring.

## Build

```bash
lake exe cache get
lake build
```

`Solution.lean` builds without warnings, and `#print axioms Erdos1139Proof.erdos_1139` lists only
`propext`, `Classical.choice` and `Quot.sound`.
