/-
Copyright 2026 Bruce Lee.
Released under the Apache License, Version 2.0.
-/
module

public import Mathlib.Algebra.Group.Pointwise.Set.Basic
public import Mathlib.Order.Filter.Cofinite

/-!
# Erdős Problem 881 for `k = 2`: statements

[Erdős Problem 881](https://www.erdosproblems.com/881) asks: if `A ⊆ ℕ` is an additive basis of
order `k` that is minimal, in the sense that `A \ B` is not a basis of order `k` for any infinite
`B ⊆ A`, must some infinite `B ⊆ A` leave `A \ B` a basis of order `k + 1`? The problem is open
for `k ≥ 3`.

This file states the two results that `Solution.lean` proves:

* `Erdos881K2.infinite_deletion_of_two_basis`: every asymptotic additive basis `A ⊆ ℕ` of order 2
  contains an infinite set `B` such that `A \ B` is an asymptotic additive basis of order 3. No
  minimality hypothesis is assumed.
* `Erdos881K2.erdos_881_two`: the case `k = 2` of Problem 881, in the formulation of
  [google-deepmind/formal-conjectures](https://github.com/google-deepmind/formal-conjectures)
  (`Erdos881.erdos_881` in `FormalConjectures/ErdosProblems/881.lean`). It follows from the first
  result, because a minimal basis of order 2 is in particular a basis of order 2.

## Conventions

The two definitions below restate, with the same names and meaning, the definitions that
formal-conjectures uses for this problem. Only Mathlib is imported here, so the definitions are
restated rather than imported; Comparator checks that they agree with the copies in the proof
development, which are taken verbatim from formal-conjectures.

* `n • A` is the pointwise `n`-fold sumset `A + ⋯ + A` of a set `A` (Mathlib's
  `Set.NSMul` instance, opened by `open scoped Pointwise`): the set of sums of exactly `n`
  elements of `A`, with repetition allowed. It is not the dilation `{n * a | a ∈ A}`.
* `A` may contain `0`. Since `0 + a = a`, a set containing `0` that is a basis of order `n` is a
  basis of every larger order, so in that case "exactly `n` summands" and "at most `n` summands"
  agree.
* "Asymptotic" means that all but finitely many natural numbers are sums of exactly `n` elements
  of `A`, which is the usual notion of an (asymptotic) additive basis in the literature on
  minimal bases. The result also holds when a basis of order `n` means "at most `n` summands":
  apply `infinite_deletion_of_two_basis` to `A ∪ {0}` and remove `0` from the deleted set.
-/

@[expose] public section

open Filter
open scoped Pointwise

namespace Set

/-- A set `A : Set M` is an asymptotic multiplicative basis of order `n` if all but finitely many
`a : M` are products of exactly `n` elements of `A`, that is, if `a ∈ A ^ n` for all `a` outside
a finite set.

`to_additive` generates from it the additive version used in the statements below,
`Set.IsAsymptoticAddBasisOfOrder`, whose body is `∀ᶠ a in cofinite, a ∈ n • A`: all but finitely
many `a : M` are sums of exactly `n` elements of `A`.

This is the definition of formal-conjectures (`FormalConjecturesForMathlib/Combinatorics/Additive/
Basis.lean`), written the same way, so that the generated additive definition is the same term. -/
@[to_additive
/-- A set `A : Set M` is an asymptotic additive basis of order `n` if all but finitely many
`a : M` are sums of exactly `n` elements of `A`, that is, if `a ∈ n • A` for all `a` outside a
finite set. This is `Set.IsAsymptoticAddBasisOfOrder` from formal-conjectures. -/]
def IsAsymptoticMulBasisOfOrder {M : Type*} [CommMonoid M] (A : Set M) (n : ℕ) : Prop :=
  ∀ᶠ a in cofinite, a ∈ A ^ n

end Set

namespace Erdos881

/-- A set `A ⊆ ℕ` is a minimal asymptotic additive basis of order `k` in the sense of
Problem 881 if it is an asymptotic additive basis of order `k`, and for every infinite
`B ⊆ A`, the set `A \ B` is not an asymptotic additive basis of order `k`.

This is `Erdos881.IsMinimalAsymptoticAddBasisOfOrder` from formal-conjectures. -/
def IsMinimalAsymptoticAddBasisOfOrder (k : ℕ) (A : Set ℕ) : Prop :=
  A.IsAsymptoticAddBasisOfOrder k ∧
    ∀ ⦃B : Set ℕ⦄, B ⊆ A → B.Infinite → ¬ (A \ B).IsAsymptoticAddBasisOfOrder k

end Erdos881

namespace Erdos881K2

/-- Every asymptotic additive basis `A ⊆ ℕ` of order 2 contains an infinite set `B` whose removal
leaves an asymptotic additive basis of order 3. No minimality hypothesis is assumed. -/
theorem infinite_deletion_of_two_basis {A : Set ℕ}
    (hA : A.IsAsymptoticAddBasisOfOrder 2) :
    ∃ B : Set ℕ, B ⊆ A ∧ B.Infinite ∧ (A \ B).IsAsymptoticAddBasisOfOrder 3 := by
  sorry

/-- Erdős Problem 881 for `k = 2`: if `A ⊆ ℕ` is a minimal asymptotic additive basis of order 2,
then some infinite `B ⊆ A` leaves `A \ B` an asymptotic additive basis of order 3. This is
`Erdos881.erdos_881` from formal-conjectures with `k = 2` (there written `k + 1 = 2 + 1`). -/
theorem erdos_881_two :
    ∀ A : Set ℕ, Erdos881.IsMinimalAsymptoticAddBasisOfOrder 2 A →
      ∃ B : Set ℕ, B ⊆ A ∧ B.Infinite ∧ (A \ B).IsAsymptoticAddBasisOfOrder 3 := by
  sorry

end Erdos881K2
