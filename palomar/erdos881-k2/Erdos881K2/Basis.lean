/-
Copyright 2025 The Formal Conjectures Authors.
Copyright 2026 Bruce Lee.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
module

public import Mathlib.Algebra.Group.Action.Pointwise.Set.Basic
public import Mathlib.Algebra.Group.Pointwise.Set.BigOperators
public import Mathlib.Algebra.Group.Pointwise.Set.Finite
public import Mathlib.Algebra.Order.Monoid.Canonical.Defs
public import Mathlib.Order.Filter.Cofinite
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Order.SuccPred.Basic

/-!
# Asymptotic additive bases, as defined in formal-conjectures

This module copies, from
[google-deepmind/formal-conjectures](https://github.com/google-deepmind/formal-conjectures)
at commit `c6f4b4bdab8fdabb19191a8a1648be21b81253b0`, the definitions that the statements of
Erdős Problem 881 use, together with the lemmas about them that the proof uses:

* `Set.IsAsymptoticAddBasisOfOrder` and its lemmas, from
  `FormalConjecturesForMathlib/Combinatorics/Additive/Basis.lean`;
* `Filter.cofinite_hasBasis_Ici` and `Filter.cofinite_eq_atTop`, from
  `FormalConjecturesForMathlib/Order/Filter/Cofinite.lean`;
* `Set.mul_mem_smul_set`, from
  `FormalConjecturesForMathlib/Algebra/Group/Action/Pointwise/Set/Basic.lean`;
* `Erdos881.IsMinimalAsymptoticAddBasisOfOrder`, from
  `FormalConjectures/ErdosProblems/881.lean`.

The declarations and their proofs are unchanged, except that unused declarations are omitted.
formal-conjectures is not a dependency because it does not yet build with the Lean toolchain this
project uses. `Challenge.lean` restates the two definitions, and Comparator checks that the
restatements agree with the definitions here.
-/

@[expose] public section

open Filter Set
open scoped Pointwise

namespace Filter

lemma cofinite_hasBasis_Ici {α : Type*} [LinearOrder α] [LocallyFiniteOrder α] [OrderBot α]
    [SuccOrder α] [NoMaxOrder α] : cofinite.HasBasis (fun (_ : α) ↦ True) (Set.Ici ·) := by
  constructor
  intro A
  simp only [mem_cofinite, true_and]
  constructor
  · intro hA
    obtain ⟨a, ha⟩ := Set.Finite.bddAbove hA
    use Order.succ a
    rw [← Set.compl_subset_compl, compl_Ici]
    exact Set.Subset.trans ha (Order.Iic_subset_Iio_succ a)
  · rintro ⟨a, ha⟩
    rw [← Set.compl_subset_compl, compl_Ici] at ha
    apply Set.Finite.subset _ ha
    exact finite_Iio a

theorem cofinite_eq_atTop {α : Type*} [LinearOrder α] [LocallyFiniteOrder α] [OrderBot α]
  [SuccOrder α] [NoMaxOrder α] :
    @cofinite α = atTop := by
  simp only [atTop_eq_generate_Ici, HasBasis.eq_generate cofinite_hasBasis_Ici, true_and]
  rfl

end Filter

namespace Set

section SMul
variable {M : Type*} [Monoid M] {a b : M} {s : Set M}

@[to_additive (attr := simp)]
lemma mul_mem_smul_set [IsLeftCancelMul M] : a * b ∈ a • s ↔ b ∈ s :=
  (mul_right_injective _).mem_set_image

end SMul

variable {M : Type*} [CommMonoid M] {A : Set M} {m n : ℕ}

/-- A set `A : Set M` is an asymptotic multiplicative basis of order `n` if the elements that can
be expressed as a product of `n` elements lying in `A` is cofinite. -/
@[to_additive
/-- A set `A : Set M` is an asymptotic additive basis of order `n` if the elements that
can be expressed as a sum of `n` elements lying in `A` is cofinite. -/]
def IsAsymptoticMulBasisOfOrder (A : Set M) (n : ℕ) : Prop := ∀ᶠ a in cofinite, a ∈ A ^ n

/-- A set `A : Set M` is an asymptotic multiplicative basis of order `n` if a cofinite set of
`a : M` can be written as `a = a₁ * ... * aₙ`, where each `aᵢ ∈ A`. -/
@[to_additive
/-- A set `A : Set M` is an asymptotic additive basis of order `n` if a cofinite set of
`a : M` can be written as `a = a₁ + ... + aₙ`, where each `aᵢ ∈ A`. -/]
lemma isAsymptoticMulBasisOfOrder_iff_prod :
    IsAsymptoticMulBasisOfOrder A n ↔ ∀ᶠ a in cofinite, ∃ (f : Fin n → M) (_ : ∀ i, f i ∈ A),
      ∏ i, f i = a := by
  have := Set.mem_finsetProd (t := .univ) (f := fun _ : Fin n ↦ A)
  simp_all [IsAsymptoticMulBasisOfOrder]

@[to_additive (attr := simp)]
protected lemma IsAsymptoticMulBasisOfOrder.of_finite [Finite M] :
    IsAsymptoticMulBasisOfOrder A n := by simp [IsAsymptoticMulBasisOfOrder]

/-- If `M` is infinite, then no set `A` is an asymptotic multiplicative basis of order `0`. -/
@[to_additive (attr := simp)
/-- If `M` is infinite, then no set `A` is an asymptotic additive basis of order `0`. -/]
lemma not_isAsymptoticMulBasisOfOrder_zero [Infinite M] : ¬IsAsymptoticMulBasisOfOrder A 0 := by
  simpa [IsAsymptoticMulBasisOfOrder, ← not_infinite] using Set.infinite_of_finite_compl (by simp)

@[to_additive]
protected lemma IsAsymptoticMulBasisOfOrder.ne_zero [Infinite M]
    (hA : IsAsymptoticMulBasisOfOrder A n) : n ≠ 0 := by rintro rfl; simp at hA

@[to_additive]
protected lemma IsAsymptoticMulBasisOfOrder.nonempty [Infinite M]
    (hA : A.IsAsymptoticMulBasisOfOrder n) : A.Nonempty := by
  by_contra!
  simp [this, IsAsymptoticMulBasisOfOrder, hA.ne_zero, finite_univ_iff,
    _root_.Infinite.not_finite] at hA

variable [LinearOrder M] [LocallyFiniteOrder M] [OrderBot M]

@[to_additive]
lemma IsAsymptoticMulBasisOfOrder.mono [CanonicallyOrderedMul M] [IsCancelMul M] (hmn : m ≤ n)
    (hA : A.IsAsymptoticMulBasisOfOrder m) : A.IsAsymptoticMulBasisOfOrder n := by
  cases finite_or_infinite M
  · simp
  obtain ⟨a, ha⟩ := hA.nonempty
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hmn
  refine ((hA.smul_set (a := a ^ n)).union <| finite_Iio <| a ^ n).subset ?_
  have : a ^ n • (A ^ m)ᶜ = (a ^ n • A ^ m)ᶜ \ Iio (a ^ n) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa
    · simp only [mem_sdiff, mem_compl_iff, mem_smul_set, smul_eq_mul, not_exists, not_and, mem_Iio,
        not_lt, le_iff_exists_mul, and_imp, forall_exists_index]
      rintro hx y rfl
      exact ⟨y, fun hy ↦ hx _ hy rfl, rfl⟩
  simp only [m.add_comm, pow_add, ofPred_mem_eq, this, sdiff_union_self, subset_def, mem_compl_iff,
    mem_union, mem_Iio]
  rintro b hb
  contrapose! hb
  exact smul_set_subset_mul (pow_mem_pow ha) hb.1

variable [SuccOrder M] [NoMaxOrder M]

@[to_additive]
lemma isAsymptoticMulBasisOfOrder_iff_atTop :
      IsAsymptoticMulBasisOfOrder A n ↔ ∀ᶠ a in atTop, a ∈ A ^ n := by
  rw [IsAsymptoticMulBasisOfOrder, cofinite_eq_atTop]

@[to_additive]
lemma isAsymptoticMulBasisOfOrder_iff_prod_atTop :
    IsAsymptoticMulBasisOfOrder A n ↔
      ∀ᶠ a in atTop, ∃ f : Fin n → M, (∀ i, f i ∈ A) ∧ ∏ i, f i = a := by
  simp [isAsymptoticMulBasisOfOrder_iff_prod, cofinite_eq_atTop]

end Set

namespace Erdos881

/--
We interpret "additive basis of order `k`" as an asymptotic additive basis of order `k`,
using the predicate `Set.IsAsymptoticAddBasisOfOrder` from additive combinatorics.

A *minimal* additive basis of order `k` is a set `A` such that
* `A` is an asymptotic additive basis of order `k`, and
* for every infinite subset `B ⊆ A`, the complement `A \ B` is *not*
  an asymptotic additive basis of order `k`.
-/
def IsMinimalAsymptoticAddBasisOfOrder (k : ℕ) (A : Set ℕ) : Prop :=
  A.IsAsymptoticAddBasisOfOrder k ∧
    ∀ ⦃B : Set ℕ⦄, B ⊆ A → B.Infinite → ¬ (A \ B).IsAsymptoticAddBasisOfOrder k

end Erdos881
