/-
Copyright 2026 Bruce Lee.
Released under the Apache License, Version 2.0.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.EReal.Inv
public import Mathlib.Data.Nat.Nth
public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import Mathlib.Order.LiminfLimsup

/-!
# Erdős Problem 1139: statement

[Erdős Problem 1139](https://www.erdosproblems.com/1139) asks: if `u 0 < u 1 < ⋯` are the positive
integers with at most two prime factors, counted with multiplicity, is
`limsup (u (k + 1) - u k) / log k = ∞`?

This file states the result that `Solution.lean` proves, `Erdos1139Proof.erdos_1139`. The
statement is `Erdos1139.erdos_1139` from
[google-deepmind/formal-conjectures](https://github.com/google-deepmind/formal-conjectures)
(`FormalConjectures/ErdosProblems/1139.lean`), written the same way:

* `u := Nat.nth (fun n ↦ 0 < n ∧ Ω n ≤ 2)` enumerates the positive integers `n` with
  `Ω n ≤ 2` in increasing order, starting from index `0`, so `u 0 = 1`. Here `Ω n` is the number
  of prime factors of `n` counted with multiplicity.
* The quotient is taken in `EReal`, and `log k` is shifted to `Real.log (k + 1)` so that it is
  positive for `k ≥ 1`; the shift does not change the limit superior.
-/

@[expose] public section

open Nat Filter
open scoped ArithmeticFunction.Omega

namespace Erdos1139Proof

/-- Erdős Problem 1139: the gaps between consecutive positive integers with at most two prime
factors, divided by `log k`, have limit superior `⊤`. This is `Erdos1139.erdos_1139` from
formal-conjectures. -/
theorem erdos_1139 :
    letI u := Nat.nth (fun n ↦ 0 < n ∧ Ω n ≤ 2)
    atTop.limsup (fun k : ℕ ↦ (((u (k + 1) : ℝ) - (u k : ℝ)) / Real.log (↑k + 1) : EReal)) = ⊤ := by
  sorry

end Erdos1139Proof
