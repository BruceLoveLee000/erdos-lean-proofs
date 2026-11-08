/-
Copyright 2026 Bruce Lee.
Released under the Apache License, Version 2.0.
-/
import FormalConjectures.ErdosProblems.«881»

/-!
# Erdős Problem 881 for `k = 2`

[Erdős Problem 881](https://www.erdosproblems.com/881) asks: if `A ⊆ ℕ` is an additive basis of
order `k` that is minimal, in the sense that `A \ B` is not a basis of order `k` for any infinite
`B ⊆ A`, must some infinite `B ⊆ A` leave `A \ B` a basis of order `k + 1`?

This file proves the case `k = 2`, without the minimality hypothesis:
`infinite_deletion_of_two_basis` shows that every asymptotic basis of order two contains an
infinite set whose removal leaves an asymptotic basis of order three. `erdos_881_two` states the
case `k = 2` of `Erdos881.erdos_881` from google-deepmind/formal-conjectures.

As a corollary, `not_minimal_three_of_two_basis` answers a question of Erdős and Nathanson
(J. Number Theory 12 (1980), p. 155): no minimal asymptotic basis of order three is an asymptotic
basis of order two.

The proof splits on whether some positive difference occurs infinitely often in `A`.

* If it does, two fixed elements `x ≠ y` act as switches: infinitely many `b ∈ A` have `b + x` and
  `b + y` in `(A \ {b}) + (A \ {b})`. A sparse choice of such `b`, inside one residue class, can be
  removed together (`infinite_deletion_of_not_infinite_gaps`).
* If every positive difference occurs only finitely often, elements are removed one at a time
  while the representations used so far are protected, with one fixed coverage threshold
  (`infinite_deletion_of_finite_support_fusion`). The construction can only get stuck at a trap,
  and a two-basis with infinite gaps has none (`not_tail_trap_of_sparse_two`).

Conventions are those of formal-conjectures: `h • A` is the `h`-fold sumset with exactly `h`
summands, and `0` may belong to `A`.
-/

namespace Erdos881K2

open Set Filter
open scoped Pointwise

/-- Every asymptotic basis in the naturals is infinite. -/
lemma basis_infinite {h : ℕ} {A : Set ℕ} (hA : A.IsAsymptoticAddBasisOfOrder h) :
    A.Infinite := by
  intro hfin
  obtain ⟨M, hM⟩ := hfin.bddAbove
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp
    (Set.isAsymptoticAddBasisOfOrder_iff_sum_atTop.mp hA)
  obtain ⟨f, hf, hsum⟩ := hN (max N (h * M + 1)) (le_max_left _ _)
  have hb : ∑ i, f i ≤ h * M := by
    calc
      ∑ i, f i ≤ ∑ _ : Fin h, M := Finset.sum_le_sum fun i _ ↦ hM (hf i)
      _ = h * M := by simp
  have := le_max_right N (h * M + 1)
  omega

/-- A bounded finite set-mapping without fixed points has an infinite free subset. -/
lemma infinite_free_subset (d : ℕ) (f : ℕ → Finset ℕ) (S : Set ℕ)
    (hS : S.Infinite) (hcard : ∀ b ∈ S, (f b).card ≤ d)
    (hself : ∀ b ∈ S, b ∉ f b) :
    ∃ T ⊆ S, T.Infinite ∧ ∀ b ∈ T, ∀ c ∈ T, c ∉ f b := by
  classical
  induction d generalizing f S with
  | zero =>
      refine ⟨S, Set.Subset.rfl, hS, ?_⟩
      intro b hb c _ hc
      have hf : f b = ∅ := Finset.card_eq_zero.mp (by simpa using hcard b hb)
      simp [hf] at hc
  | succ d ih =>
      by_cases hinfinite : ∃ a, {b | b ∈ S ∧ a ∈ f b}.Infinite
      · obtain ⟨a, ha⟩ := hinfinite
        let S' : Set ℕ := {b | b ∈ S ∧ a ∈ f b}
        have hcard' : ∀ b ∈ S', ((f b).erase a).card ≤ d := by
          intro b hb
          rw [Finset.card_erase_of_mem hb.2]
          have := hcard b hb.1
          omega
        obtain ⟨T, hTS', hT, hfree⟩ := ih (fun b => (f b).erase a) S' ha hcard'
          (fun b hb hmem => hself b hb.1 (Finset.mem_of_mem_erase hmem))
        refine ⟨T, fun b hb => (hTS' hb).1, hT, ?_⟩
        intro b hb c hc hcb
        have hca : c ≠ a := by
          intro heq
          have hcf := (hTS' hc).2
          rw [← heq] at hcf
          exact hself c (hTS' hc).1 hcf
        exact hfree b hb c hc (Finset.mem_erase.mpr ⟨hca, hcb⟩)
      · have hincoming : ∀ a, {b | b ∈ S ∧ a ∈ f b}.Finite := by
          simpa only [not_exists, Set.not_infinite] using hinfinite
        have hext : ∀ t : Set ℕ, t.Finite →
            ∃ c, c ∈ S ∧ c ∉ t ∧ ∀ b ∈ t, c ∉ f b ∧ b ∉ f c := by
          intro t ht
          let bad : Set ℕ := t ∪ ⋃ b ∈ t, ((f b : Set ℕ) ∪ {c | c ∈ S ∧ b ∈ f c})
          have hbad : bad.Finite := ht.union (ht.biUnion fun b _ =>
            (f b).finite_toSet.union (hincoming b))
          obtain ⟨c, hcS, hc⟩ := hS.exists_notMem_finite hbad
          refine ⟨c, hcS, fun hct => hc (Or.inl hct), ?_⟩
          intro b hbt
          constructor
          · intro hcf
            apply hc
            right
            exact Set.mem_iUnion.mpr ⟨b, Set.mem_iUnion.mpr ⟨hbt, Or.inl hcf⟩⟩
          · intro hbf
            apply hc
            right
            exact Set.mem_iUnion.mpr ⟨b, Set.mem_iUnion.mpr ⟨hbt, Or.inr ⟨hcS, hbf⟩⟩⟩
        obtain ⟨u, hu⟩ := Set.seq_of_forall_finite_exists hext
        have hu_inj : Function.Injective u := by
          intro i j hij
          by_contra hne
          rcases lt_or_gt_of_ne hne with hlt | hgt
          · exact (hu j).2.1 (hij ▸ Set.mem_image_of_mem u hlt)
          · exact (hu i).2.1 (hij.symm ▸ Set.mem_image_of_mem u hgt)
        refine ⟨Set.range u, ?_, Set.infinite_range_of_injective hu_inj, ?_⟩
        · rintro b ⟨i, rfl⟩
          exact (hu i).1
        · rintro b ⟨i, rfl⟩ c ⟨j, rfl⟩
          rcases lt_trichotomy i j with hij | hij | hij
          · exact ((hu j).2.2 (u i) (Set.mem_image_of_mem u hij)).1
          · subst j
            exact hself (u i) (hu i).1
          · exact ((hu i).2.2 (u j) (Set.mem_image_of_mem u hij)).2

/-- An infinite set has an infinite part in one residue class. -/
lemma infinite_residue_part {S : Set ℕ} (hS : S.Infinite) {m : ℕ} (hm : 0 < m) :
    ∃ r : Fin m, {b : ℕ | b ∈ S ∧ b % m = r}.Infinite := by
  by_contra h
  have hfinite : ∀ r : Fin m, {b : ℕ | b ∈ S ∧ b % m = r}.Finite := by
    simpa only [not_exists, Set.not_infinite] using h
  apply hS
  apply (Set.finite_iUnion hfinite).subset
  intro b hb
  exact Set.mem_iUnion.mpr ⟨⟨b % m, Nat.mod_lt b hm⟩, hb, rfl⟩

/-- Candidates whose translates by two fixed partners have singleton-avoiding representations. -/
def twoSwitchCandidates (A : Set ℕ) (x y : ℕ) : Set ℕ :=
  {b | b ∈ A ∧ x ≠ b ∧ y ≠ b ∧
    b + x ∈ (A \ {b}) + (A \ {b}) ∧ b + y ∈ (A \ {b}) + (A \ {b})}

/-- Construct a three-term sumset membership. -/
lemma mem_three_sumset {A : Set ℕ} {u v w n : ℕ}
    (hu : u ∈ A) (hv : v ∈ A) (hw : w ∈ A) (heq : u + v + w = n) :
    n ∈ (3 : ℕ) • A := by
  rw [show (3 : ℕ) = 2 + 1 from rfl, succ_nsmul, two_nsmul]
  exact Set.mem_add.mpr ⟨u + v, Set.mem_add.mpr ⟨u, hu, v, hv, rfl⟩, w, hw, heq⟩

/-- A missing three-term sum, despite a switch at x, must use two deleted elements. -/
lemma missing_three_forces_deleted_pair {A C : Set ℕ} {N x n : ℕ}
    (hA : ∀ m, N ≤ m → m ∈ A + A) (hx : x ∈ C)
    (hswitch : ∀ b ∈ A \ C, b + x ∈ C + C)
    (hmissing : n ∉ (3 : ℕ) • C) (hn : N + x ≤ n) :
    ∃ u ∈ A \ C, ∃ v ∈ A \ C, x + u + v = n := by
  obtain ⟨u, hu, v, hv, huv⟩ := Set.mem_add.mp (hA (n - x) (by omega))
  have heq : u + v + x = n := by omega
  by_cases huC : u ∈ C
  · by_cases hvC : v ∈ C
    · exact (hmissing (mem_three_sumset huC hvC hx heq)).elim
    · obtain ⟨p, hp, q, hq, hpq⟩ := Set.mem_add.mp (hswitch v ⟨hv, hvC⟩)
      exact (hmissing (mem_three_sumset hp hq huC (by omega))).elim
  · by_cases hvC : v ∈ C
    · obtain ⟨p, hp, q, hq, hpq⟩ := Set.mem_add.mp (hswitch u ⟨hu, huC⟩)
      exact (hmissing (mem_three_sumset hp hq hvC (by omega))).elim
    · exact ⟨u, ⟨hu, huC⟩, v, ⟨hv, hvC⟩, by omega⟩

/-- Two switch shifts with disjoint translated deleted pair-sums suffice for thinning. -/
theorem three_basis_of_two_shift_switches {A C : Set ℕ} {x y : ℕ}
    (hA : A.IsAsymptoticAddBasisOfOrder 2) (hx : x ∈ C) (hy : y ∈ C)
    (hsx : ∀ b ∈ A \ C, b + x ∈ C + C)
    (hsy : ∀ b ∈ A \ C, b + y ∈ C + C)
    (hdisjoint : ∀ u ∈ A \ C, ∀ v ∈ A \ C,
      ∀ p ∈ A \ C, ∀ q ∈ A \ C, x + u + v ≠ y + p + q) :
    C.IsAsymptoticAddBasisOfOrder 3 := by
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp
    (Set.isAsymptoticAddBasisOfOrder_iff_atTop.mp hA)
  have hN' : ∀ m, N ≤ m → m ∈ A + A := by
    simpa only [two_nsmul] using hN
  apply Set.isAsymptoticAddBasisOfOrder_iff_atTop.mpr
  apply Filter.eventually_atTop.mpr
  refine ⟨N + x + y, ?_⟩
  intro n hn
  by_contra hmissing
  obtain ⟨u, hu, v, hv, huv⟩ :=
    missing_three_forces_deleted_pair hN' hx hsx hmissing (by omega)
  obtain ⟨p, hp, q, hq, hpq⟩ :=
    missing_three_forces_deleted_pair hN' hy hsy hmissing (by omega)
  exact hdisjoint u hu v hv p hp q hq (by omega)

/-- Infinitely many candidates for two fixed switches can be thinned simultaneously. -/
theorem infinite_deletion_of_two_switch_candidates {A : Set ℕ} {x y : ℕ}
    (hA : A.IsAsymptoticAddBasisOfOrder 2) (hx : x ∈ A) (hy : y ∈ A) (hxy : x ≠ y)
    (hS : (twoSwitchCandidates A x y).Infinite) :
    ∃ B ⊆ A, B.Infinite ∧ (A \ B).IsAsymptoticAddBasisOfOrder 3 := by
  classical
  let S := twoSwitchCandidates A x y
  have hwitness : ∀ b ∈ S, ∃ u v p q,
      u ∈ A \ {b} ∧ v ∈ A \ {b} ∧ p ∈ A \ {b} ∧ q ∈ A \ {b} ∧
      u + v = b + x ∧ p + q = b + y := by
    intro b hb
    obtain ⟨u, hu, v, hv, huv⟩ := Set.mem_add.mp hb.2.2.2.1
    obtain ⟨p, hp, q, hq, hpq⟩ := Set.mem_add.mp hb.2.2.2.2
    exact ⟨u, v, p, q, hu, hv, hp, hq, huv, hpq⟩
  choose u v p q hu hv hp hq heqx heqy using hwitness
  let f : ℕ → Finset ℕ := fun b =>
    if hb : b ∈ S then [u b hb, v b hb, p b hb, q b hb].toFinset else ∅
  have hcard : ∀ b ∈ S, (f b).card ≤ 4 := by
    intro b hb
    change (if h : b ∈ S then [u b h, v b h, p b h, q b h].toFinset else ∅).card ≤ 4
    rw [dif_pos hb]
    exact List.toFinset_card_le _
  have hself : ∀ b ∈ S, b ∉ f b := by
    intro b hb
    have hune : u b hb ≠ b := by simpa using (hu b hb).2
    have hvne : v b hb ≠ b := by simpa using (hv b hb).2
    have hpne : p b hb ≠ b := by simpa using (hp b hb).2
    have hqne : q b hb ≠ b := by simpa using (hq b hb).2
    simp [f, hb, Ne.symm hune, Ne.symm hvne, Ne.symm hpne, Ne.symm hqne]
  obtain ⟨T, hTS, hT, hfree⟩ := infinite_free_subset 4 f S hS hcard hself
  let m := x + y + 1
  obtain ⟨r, hr⟩ := infinite_residue_part hT (m := m) (by dsimp [m]; omega)
  let B : Set ℕ := {b | b ∈ T ∧ b % m = r}
  have hBT : B ⊆ T := fun b hb => hb.1
  have hBS : B ⊆ S := hBT.trans hTS
  have hBA : B ⊆ A := fun b hb => (hBS hb).1
  have hB : B.Infinite := hr
  have hCmem : ∀ b ∈ B, ∀ c ∈ f b, c ∈ A → c ∈ A \ B := by
    intro b hb c hcf hcA
    refine ⟨hcA, ?_⟩
    intro hcB
    exact hfree b (hBT hb) c (hBT hcB) hcf
  have hswitch : ∀ b ∈ B, b + x ∈ (A \ B) + (A \ B) ∧
      b + y ∈ (A \ B) + (A \ B) := by
    intro b hb
    have hbS := hBS hb
    have huC := hCmem b hb (u b hbS) (by simp [f, hbS]) (hu b hbS).1
    have hvC := hCmem b hb (v b hbS) (by simp [f, hbS]) (hv b hbS).1
    have hpC := hCmem b hb (p b hbS) (by simp [f, hbS]) (hp b hbS).1
    have hqC := hCmem b hb (q b hbS) (by simp [f, hbS]) (hq b hbS).1
    exact ⟨Set.mem_add.mpr ⟨_, huC, _, hvC, heqx b hbS⟩,
      Set.mem_add.mpr ⟨_, hpC, _, hqC, heqy b hbS⟩⟩
  have hdeleted : ∀ b ∈ A \ (A \ B), b ∈ B := by
    intro b hb
    by_contra hnot
    exact hb.2 ⟨hb.1, hnot⟩
  refine ⟨B, hBA, hB, three_basis_of_two_shift_switches (x := x) (y := y) hA ?_ ?_ ?_ ?_ ?_⟩
  · exact ⟨hx, fun hxB => (hBS hxB).2.1 rfl⟩
  · exact ⟨hy, fun hyB => (hBS hyB).2.2.1 rfl⟩
  · intro b hb
    exact (hswitch b (hdeleted b hb)).1
  · intro b hb
    exact (hswitch b (hdeleted b hb)).2
  · intro a ha b hb c hc d hd heq
    have hab : Nat.ModEq m a c := by
      change a % m = c % m
      rw [(hdeleted a ha).2, (hdeleted c hc).2]
    have hbd : Nat.ModEq m b d := by
      change b % m = d % m
      rw [(hdeleted b hb).2, (hdeleted d hd).2]
    have hmod : Nat.ModEq m (x + a + b) (y + c + d) := by rw [heq]
    have hmodxy := Nat.ModEq.add_right_cancel hab (Nat.ModEq.add_right_cancel hbd hmod)
    change x % m = y % m at hmodxy
    have hxm : x < m := by dsimp [m]; omega
    have hym : y < m := by dsimp [m]; omega
    exact hxy (by simpa only [Nat.mod_eq_of_lt hxm, Nat.mod_eq_of_lt hym] using hmodxy)

/-- Infinite gaps mean that each fixed positive difference occurs only finitely often. -/
def hasInfiniteGaps (A : Set ℕ) : Prop :=
  ∀ d : ℕ, 0 < d → {b : ℕ | b ∈ A ∧ b + d ∈ A}.Finite

/-- A fixed gap occurring infinitely often supplies two fixed switch partners. -/
theorem infinite_two_switch_candidates_of_repeated_gap {A : Set ℕ} {d : ℕ}
    (hd : 0 < d) (hP : {b : ℕ | b ∈ A ∧ b + d ∈ A}.Infinite) :
    ∃ x ∈ A, ∃ y ∈ A, x ≠ y ∧ (twoSwitchCandidates A x y).Infinite := by
  obtain ⟨u, hu⟩ := hP.nonempty
  obtain ⟨v, hv, huv⟩ := hP.exists_gt u
  refine ⟨u + d, hu.2, v + d, hv.2, by omega, ?_⟩
  have hinf := hP.sdiff (t := {u, v, u + d, v + d}) (by simp)
  apply hinf.mono
  intro b hb
  have hbu : b ≠ u := by intro heq; exact hb.2 (by simp [heq])
  have hbv : b ≠ v := by intro heq; exact hb.2 (by simp [heq])
  have hbux : b ≠ u + d := by intro heq; exact hb.2 (by simp [heq])
  have hbvy : b ≠ v + d := by intro heq; exact hb.2 (by simp [heq])
  have hbd : b + d ∈ A \ {b} := ⟨hb.1.2, by simp only [Set.mem_singleton_iff]; omega⟩
  refine ⟨hb.1.1, hbux.symm, hbvy.symm, ?_, ?_⟩
  · exact Set.mem_add.mpr ⟨b + d, hbd, u, ⟨hu.1, by simpa using hbu.symm⟩, by omega⟩
  · exact Set.mem_add.mpr ⟨b + d, hbd, v, ⟨hv.1, by simpa using hbv.symm⟩, by omega⟩

/-- Every two-basis with an infinitely repeated fixed gap admits the desired infinite thinning. -/
theorem infinite_deletion_of_not_infinite_gaps {A : Set ℕ}
    (hA : A.IsAsymptoticAddBasisOfOrder 2) (hgap : ¬ hasInfiniteGaps A) :
    ∃ B ⊆ A, B.Infinite ∧ (A \ B).IsAsymptoticAddBasisOfOrder 3 := by
  have hex : ∃ d : ℕ, 0 < d ∧ {b : ℕ | b ∈ A ∧ b + d ∈ A}.Infinite := by
    simpa only [hasInfiniteGaps, not_forall, Classical.not_imp, Set.not_finite, exists_prop] using hgap
  obtain ⟨d, hd, hP⟩ := hex
  obtain ⟨x, hx, y, hy, hxy, hS⟩ := infinite_two_switch_candidates_of_repeated_gap hd hP
  exact infinite_deletion_of_two_switch_candidates hA hx hy hxy hS

/-- The free-subset lemma still applies after protecting a finite set `P`. -/
lemma infinite_free_subset_avoiding (d : ℕ) (f : ℕ → Finset ℕ) (S : Set ℕ)
    (P : Finset ℕ) (hS : S.Infinite) (hcard : ∀ b ∈ S, (f b).card ≤ d)
    (hself : ∀ b ∈ S, b ∉ f b) :
    ∃ T ⊆ S, T.Infinite ∧ Disjoint T (P : Set ℕ) ∧
      ∀ b ∈ T, ∀ c ∈ T, c ∉ f b := by
  obtain ⟨T, hTS, hT, hfree⟩ := infinite_free_subset d f (S \ (P : Set ℕ))
    (hS.sdiff P.finite_toSet) (fun b hb => hcard b hb.1)
    (fun b hb => hself b hb.1)
  refine ⟨T, fun b hb => (hTS hb).1, hT, ?_, hfree⟩
  exact Set.disjoint_left.mpr (fun b hb hbp => (hTS hb).2 hbp)

/-- A stage of the greedy construction: elements deleted so far, the protected supports of the
representations already chosen, and the frontier below which coverage is secured. -/
structure SupportFusionState where
  deleted : Finset ℕ
  support : Finset ℕ
  frontier : ℕ

/-- An invariant for the greedy construction with one fixed threshold `N`: every good stage
covers `[N, frontier)` by representations inside its protected support, and every good stage
extends to a good stage that deletes one more element and pushes the frontier forward. -/
def FiniteSupportFusion (h : ℕ) (A : Set ℕ) : Prop :=
  ∃ N : ℕ, ∃ good : SupportFusionState → Prop,
    good ⟨∅, ∅, N⟩ ∧
    (∀ s, good s → (s.deleted : Set ℕ) ⊆ A ∧ Disjoint s.deleted s.support ∧
      ∀ n, N ≤ n → n < s.frontier → n ∈ h • (A ∩ (s.support : Set ℕ))) ∧
    ∀ s, good s → ∃ t, good t ∧ s.deleted ⊂ t.deleted ∧
      s.support ⊆ t.support ∧ s.frontier < t.frontier

/-- Running the greedy construction forever deletes an infinite set and keeps one coverage tail. -/
theorem infinite_deletion_of_finite_support_fusion {h : ℕ} {A : Set ℕ}
    (hf : FiniteSupportFusion h A) :
    ∃ B : Set ℕ, B ⊆ A ∧ B.Infinite ∧ (A \ B).IsAsymptoticAddBasisOfOrder h := by
  classical
  obtain ⟨N, good, hinit, hinv, hext⟩ := hf
  choose next hgood hnextD hnextP hnextF using hext
  let step : {s // good s} → {s // good s} := fun s =>
    ⟨next s.1 s.2, hgood s.1 s.2⟩
  let u : ℕ → {s // good s} := fun i =>
    Nat.rec ⟨⟨∅, ∅, N⟩, hinit⟩ (fun _ s => step s) i
  have hDstep : ∀ i, (u i).1.deleted ⊂ (u (i + 1)).1.deleted :=
    fun i => hnextD _ (u i).2
  have hPstep : ∀ i, (u i).1.support ⊆ (u (i + 1)).1.support :=
    fun i => hnextP _ (u i).2
  have hFstep : ∀ i, (u i).1.frontier < (u (i + 1)).1.frontier :=
    fun i => hnextF _ (u i).2
  have hDmono : Monotone (fun i => (u i).1.deleted) :=
    monotone_nat_of_le_succ (fun i => (hDstep i).le)
  have hPmono : Monotone (fun i => (u i).1.support) :=
    monotone_nat_of_le_succ hPstep
  have hDcard : StrictMono (fun i => (u i).1.deleted.card) :=
    strictMono_nat_of_lt_succ (fun i => Finset.card_lt_card (hDstep i))
  have hFmono : StrictMono (fun i => (u i).1.frontier) :=
    strictMono_nat_of_lt_succ hFstep
  let B : Set ℕ := {b | ∃ i, b ∈ (u i).1.deleted}
  have hB : B.Infinite := by
    intro hfin
    have hsub : ∀ i, (u i).1.deleted ⊆ hfin.toFinset := by
      intro i b hb
      exact hfin.mem_toFinset.mpr ⟨i, hb⟩
    have hbound := Finset.card_le_card (hsub (hfin.toFinset.card + 1))
    have hlower : hfin.toFinset.card + 1 ≤ (u (hfin.toFinset.card + 1)).1.deleted.card :=
      hDcard.id_le (hfin.toFinset.card + 1)
    exact (Nat.not_succ_le_self _) (hlower.trans hbound)
  have havoid : ∀ i, A ∩ ((u i).1.support : Set ℕ) ⊆ A \ B := by
    intro i b hb
    refine ⟨hb.1, ?_⟩
    rintro ⟨j, hj⟩
    rcases le_total i j with hij | hji
    · exact Finset.disjoint_left.mp (hinv _ (u j).2).2.1 hj (hPmono hij hb.2)
    · exact Finset.disjoint_left.mp (hinv _ (u i).2).2.1 (hDmono hji hj) hb.2
  refine ⟨B, ?_, hB, ?_⟩
  · rintro b ⟨i, hb⟩
    exact (hinv _ (u i).2).1 hb
  · rw [Set.isAsymptoticAddBasisOfOrder_iff_atTop, Filter.eventually_atTop]
    refine ⟨N, ?_⟩
    intro n hn
    have hnF : n < (u (n + 1)).1.frontier :=
      lt_of_lt_of_le (Nat.lt_succ_self n) (hFmono.id_le (n + 1))
    exact Set.nsmul_subset_nsmul_left (havoid (n + 1))
      ((hinv _ (u (n + 1)).2).2.2 n hn hnF)

/-- Every `n ≥ N` is a sum of `h` elements of `A`. -/
def TailCovered (h : ℕ) (A : Set ℕ) (N : ℕ) : Prop :=
  ∀ n, N ≤ n → n ∈ h • A

/-- The elements of `A` whose removal keeps the tail from `N` covered. -/
def tailRedundant (h : ℕ) (A : Set ℕ) (N : ℕ) : Set ℕ :=
  {a | a ∈ A ∧ TailCovered h (A \ {a}) N}

/-- A trap: after deleting some finite `D` above `L`, the tail from `N` is still covered but only
finitely many further single elements can be removed without losing coverage. -/
def TailTrapAbove (h : ℕ) (A : Set ℕ) (N L : ℕ) : Prop :=
  ∃ D : Finset ℕ, (D : Set ℕ) ⊆ A ∧ (∀ d ∈ D, L ≤ d) ∧
    TailCovered h (A \ (D : Set ℕ)) N ∧
    (tailRedundant h (A \ (D : Set ℕ)) N).Finite

/-- Protect complete witnesses for moving targets, with one bounded-size demand per candidate. -/
lemma simultaneous_full_witness_avoidance {h : ℕ} {C S : Set ℕ}
    (q : ℕ → ℕ) (P : Finset ℕ) (hS : S.Infinite)
    (hrep : ∀ b ∈ S, q b ∈ h • (C \ {b})) :
    ∃ T ⊆ S, T.Infinite ∧ Disjoint T (P : Set ℕ) ∧
      ∀ b ∈ T, q b ∈ h • (C \ T) := by
  classical
  have hex : ∀ b ∈ S, ∃ f : Fin h → ℕ,
      (∀ i, f i ∈ C \ {b}) ∧ (∑ i, f i) = q b := by
    intro b hb
    exact Set.mem_nsmul_iff_sum.mp (hrep b hb)
  choose f hf hsum using hex
  let F : ℕ → Finset ℕ := fun b =>
    if hb : b ∈ S then Finset.univ.image (f b hb) else ∅
  have hcard : ∀ b ∈ S, (F b).card ≤ h := by
    intro b hb
    simp only [F, dif_pos hb]
    exact Finset.card_image_le.trans (by simp)
  have hself : ∀ b ∈ S, b ∉ F b := by
    intro b hb hmem
    simp only [F, dif_pos hb, Finset.mem_image] at hmem
    obtain ⟨i, _, hi⟩ := hmem
    exact (hf b hb i).2 (by simp [hi])
  obtain ⟨T, hTS, hT, hTP, hfree⟩ :=
    infinite_free_subset_avoiding h F S P hS hcard hself
  refine ⟨T, hTS, hT, hTP, ?_⟩
  intro b hb
  have hbS := hTS hb
  apply Set.mem_nsmul_iff_sum.mpr
  refine ⟨f b hbS, ?_, hsum b hbS⟩
  intro i
  refine ⟨(hf b hbS i).1, ?_⟩
  intro hiT
  apply hfree b hb (f b hbS i) hiT
  simp [F, hbS]

/-- A missing singleton-deletion target uses that singleton in every full representation. -/
lemma private_target_of_not_tailRedundant {h N a : ℕ} {C : Set ℕ}
    (hC : TailCovered h C N) (ha : a ∈ C) (hnon : a ∉ tailRedundant h C N) :
    ∃ n, N ≤ n ∧ a ≤ n ∧ n ∈ h • C ∧
      ∀ f : Fin h → ℕ, (∀ i, f i ∈ C) → (∑ i, f i) = n → ∃ i, f i = a := by
  have hmissing : ¬ TailCovered h (C \ {a}) N := fun hs => hnon ⟨ha, hs⟩
  simp only [TailCovered, not_forall] at hmissing
  obtain ⟨n, hn, hmiss⟩ := hmissing
  have hhit : ∀ f : Fin h → ℕ, (∀ i, f i ∈ C) → (∑ i, f i) = n → ∃ i, f i = a := by
    intro f hf hsum
    by_contra havoid
    push Not at havoid
    exact hmiss (Set.mem_nsmul_iff_sum.mpr
      ⟨f, fun i => ⟨hf i, by simpa using havoid i⟩, hsum⟩)
  have hnC := hC n hn
  obtain ⟨f, hf, hsum⟩ := Set.mem_nsmul_iff_sum.mp hnC
  obtain ⟨i, hi⟩ := hhit f hf hsum
  refine ⟨n, hn, ?_, hnC, hhit⟩
  calc
    a = f i := hi.symm
    _ ≤ ∑ j, f j := Finset.single_le_sum (fun j _ => Nat.zero_le (f j)) (Finset.mem_univ i)
    _ = n := hsum

/-- Without a trap above `L`, the greedy construction never gets stuck. The protected finite set
stores every summand of the representations chosen so far. -/
theorem finite_support_fusion_of_no_tail_trap {h N L : ℕ} {A : Set ℕ}
    (hA : TailCovered h A N) (hno : ¬ TailTrapAbove h A N L) :
    FiniteSupportFusion h A := by
  classical
  let good : SupportFusionState → Prop := fun s =>
    (s.deleted : Set ℕ) ⊆ A ∧ (∀ d ∈ s.deleted, L ≤ d) ∧
      Disjoint s.deleted s.support ∧ TailCovered h (A \ (s.deleted : Set ℕ)) N ∧
      N ≤ s.frontier ∧
      ∀ n, N ≤ n → n < s.frontier → n ∈ h • (A ∩ (s.support : Set ℕ))
  refine ⟨N, good, ?_, ?_, ?_⟩
  · refine ⟨by simp, by simp, by simp, ?_, le_rfl, ?_⟩
    · simpa using hA
    · intro n hn hnN
      change n < N at hnN
      omega
  · intro s hs
    exact ⟨hs.1, hs.2.2.1, hs.2.2.2.2.2⟩
  · intro s hs
    have hred : (tailRedundant h (A \ (s.deleted : Set ℕ)) N).Infinite := by
      intro hfin
      exact hno ⟨s.deleted, hs.1, hs.2.1, hs.2.2.2.1, hfin⟩
    let C := A \ (s.deleted : Set ℕ)
    let S := tailRedundant h C N \ (Finset.range L : Set ℕ)
    have hS : S.Infinite := hred.sdiff (Finset.range L).finite_toSet
    obtain ⟨T, hTS, hT, hTP, hrep⟩ :=
      simultaneous_full_witness_avoidance (fun _ => s.frontier) s.support hS
        (fun b hb => hb.1.2 s.frontier hs.2.2.2.2.1)
    obtain ⟨b, hb⟩ := hT.nonempty
    have hbred := (hTS hb).1
    have hbD : b ∉ s.deleted := hbred.1.2
    have hbP : b ∉ s.support := fun hbp => Set.disjoint_left.mp hTP hb hbp
    have hbL : L ≤ b := by
      have hh := (hTS hb).2
      simpa only [Finset.mem_coe, Finset.mem_range, not_lt] using hh
    obtain ⟨f, hf, hsum⟩ := Set.mem_nsmul_iff_sum.mp (hrep b hb)
    let W : Finset ℕ := Finset.univ.image f
    let t : SupportFusionState :=
      ⟨insert b s.deleted, s.support ∪ W, s.frontier + 1⟩
    have hset : A \ (↑(insert b s.deleted) : Set ℕ) = C \ {b} := by
      ext x
      simp [C, and_assoc, and_comm]
    have htail : TailCovered h (A \ (↑(insert b s.deleted) : Set ℕ)) N := by
      rw [hset]
      exact hbred.2
    have hdisj : Disjoint (insert b s.deleted) (s.support ∪ W) := by
      apply Finset.disjoint_left.mpr
      intro x hxD hxP
      rcases Finset.mem_union.mp hxP with hxP | hxW
      · rcases Finset.mem_insert.mp hxD with rfl | hxD
        · exact hbP hxP
        · exact Finset.disjoint_left.mp hs.2.2.1 hxD hxP
      · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hxW
        rcases Finset.mem_insert.mp hxD with hfb | hfiD
        · exact (hf i).2 (hfb ▸ hb)
        · exact (hf i).1.2 hfiD
    have hfront : s.frontier ∈ h • (A ∩ (↑(s.support ∪ W) : Set ℕ)) := by
      apply Set.mem_nsmul_iff_sum.mpr
      refine ⟨f, ?_, hsum⟩
      intro i
      exact ⟨(hf i).1.1, Finset.mem_union_right _
        (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)⟩
    refine ⟨t, ?_, Finset.ssubset_insert hbD, Finset.subset_union_left, by dsimp [t]; omega⟩
    refine ⟨?_, ?_, hdisj, htail, ?_, ?_⟩
    · intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact hbred.1.1
      · exact hs.1 hx
    · intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact hbL
      · exact hs.2.1 x hx
    · dsimp [t]
      exact hs.2.2.2.2.1.trans (Nat.le_succ _)
    · intro n hn hnF
      change n < s.frontier + 1 at hnF
      by_cases hnold : n < s.frontier
      · exact Set.nsmul_subset_nsmul_left
          (show A ∩ (s.support : Set ℕ) ⊆ A ∩ (t.support : Set ℕ) from
            fun x hx => ⟨hx.1, Finset.mem_union_left _ hx.2⟩)
          (hs.2.2.2.2.2 n hn hnold)
      · have heq : n = s.frontier := by omega
        exact heq ▸ hfront

/-- Distinct fixed translates of an infinite-gap set have bounded intersections. -/
lemma translate_intersection_bounded {A : Set ℕ} (hgap : hasInfiniteGaps A)
    {x y : ℕ} (hxy : x ≠ y) :
    ∃ M, ∀ u ∈ A, ∀ v ∈ A, x + u = y + v → x + u ≤ M := by
  rcases lt_or_gt_of_ne hxy with hlt | hgt
  · obtain ⟨M, hM⟩ := (hgap (y - x) (by omega)).bddAbove
    refine ⟨y + M, ?_⟩
    intro u hu v hv heq
    have hvm : v ≤ M := hM ⟨hv, by convert hu using 1; omega⟩
    omega
  · obtain ⟨M, hM⟩ := (hgap (x - y) (by omega)).bddAbove
    refine ⟨x + M, ?_⟩
    intro u hu v hv heq
    have hum : u ≤ M := hM ⟨hu, by convert hv using 1; omega⟩
    omega

/-- Two separated anchors cannot both have a representation hitting a fixed finite stem
at a sufficiently large target. All shifts involve that fixed stem, not moving partners. -/
lemma eventually_not_two_stem_hits {A : Set ℕ} (hgap : hasInfiniteGaps A)
    (D : Finset ℕ) {x y : ℕ} (hsep : x + D.sup id < y) :
    ∃ U, ∀ n, U ≤ n →
      ¬ ((∃ d ∈ D, ∃ u ∈ A, x + d + u = n) ∧
        (∃ e ∈ D, ∃ v ∈ A, y + e + v = n)) := by
  classical
  have hne : ∀ d e : D, x + (d : ℕ) ≠ y + (e : ℕ) := by
    intro d e
    have hd : (d : ℕ) ≤ D.sup id := Finset.le_sup (f := id) d.property
    omega
  choose M hM using (fun d e : D => translate_intersection_bounded hgap (hne d e))
  let U := (Finset.univ : Finset (D × D)).sup (fun p => M p.1 p.2) + 1
  refine ⟨U, ?_⟩
  intro n hn hboth
  obtain ⟨⟨d, hd, u, hu, hdu⟩, e, he, v, hv, hev⟩ := hboth
  have hsmall := hM ⟨d, hd⟩ ⟨e, he⟩ u hu v hv (hdu.trans hev.symm)
  change x + d + u ≤ M ⟨d, hd⟩ ⟨e, he⟩ at hsmall
  have hbound : M ⟨d, hd⟩ ⟨e, he⟩ ≤ U - 1 := by
    exact Finset.le_sup (f := fun p : D × D => M p.1 p.2)
      (Finset.mem_univ (⟨d, hd⟩, ⟨e, he⟩))
  dsimp [U] at hn hbound
  omega

/-- A missing full triple representation forces a two-representation at an anchor to use
either the fixed stem or the proposed singleton deletion. -/
lemma missing_triple_anchor_alternative {A : Set ℕ} {D : Finset ℕ} {T b a n : ℕ}
    (hA : TailCovered 2 A T) (hb : b ∈ A \ (D : Set ℕ)) (hba : b ≠ a)
    (hn : T + b ≤ n) (hmiss : n ∉ (3 : ℕ) • ((A \ (D : Set ℕ)) \ {a})) :
    (∃ d ∈ D, ∃ u ∈ A, b + d + u = n) ∨ (∃ u ∈ A, b + a + u = n) := by
  have hrep : n - b ∈ A + A := by simpa only [two_nsmul] using hA (n - b) (by omega)
  obtain ⟨u, hu, v, hv, huv⟩ := Set.mem_add.mp hrep
  by_cases huD : u ∈ D
  · exact Or.inl ⟨u, huD, v, hv, by omega⟩
  by_cases hvD : v ∈ D
  · exact Or.inl ⟨v, hvD, u, hu, by omega⟩
  by_cases hua : u = a
  · exact Or.inr ⟨v, hv, by omega⟩
  by_cases hva : v = a
  · exact Or.inr ⟨u, hu, by omega⟩
  exact (hmiss (mem_three_sumset ⟨⟨hb.1, hb.2⟩, hba⟩
    ⟨⟨hu, huD⟩, hua⟩ ⟨⟨hv, hvD⟩, hva⟩ (by omega))).elim

set_option maxHeartbeats 1000000 in
/-- In a two-basis with infinite gaps, after deleting any finite `D` that keeps order-three coverage,
infinitely many further single elements remain removable. Three separated anchors bound the
targets that a removal can destroy; two larger anchors exclude them. -/
theorem infinite_tailRedundant_of_sparse_two {A : Set ℕ} {D : Finset ℕ} {N : ℕ}
    (hA : A.IsAsymptoticAddBasisOfOrder 2) (hgap : hasInfiniteGaps A)
    (hC : TailCovered 3 (A \ (D : Set ℕ)) N) :
    (tailRedundant 3 (A \ (D : Set ℕ)) N).Infinite := by
  classical
  obtain ⟨T, hT⟩ := Filter.eventually_atTop.mp
    (Set.isAsymptoticAddBasisOfOrder_iff_atTop.mp hA)
  have hCi := (basis_infinite hA).sdiff D.finite_toSet
  obtain ⟨x, hx⟩ := hCi.nonempty
  obtain ⟨y, hy, hxy⟩ := hCi.exists_gt (x + D.sup id)
  obtain ⟨z, hz, hyz⟩ := hCi.exists_gt (y + D.sup id)
  obtain ⟨Mxy, hMxy⟩ := translate_intersection_bounded hgap (x := x) (y := y) (by omega)
  obtain ⟨Mxz, hMxz⟩ := translate_intersection_bounded hgap (x := x) (y := z) (by omega)
  obtain ⟨Myz, hMyz⟩ := translate_intersection_bounded hgap (x := y) (y := z) (by omega)
  let M := Mxy + Mxz + Myz
  obtain ⟨p, hp, hpM⟩ := hCi.exists_gt (M + z)
  obtain ⟨q, hq, hpq⟩ := hCi.exists_gt (p + D.sup id)
  obtain ⟨Uxy, hUxy⟩ := eventually_not_two_stem_hits hgap D hxy
  obtain ⟨Uxz, hUxz⟩ := eventually_not_two_stem_hits hgap D (x := x) (y := z) (by omega)
  obtain ⟨Uyz, hUyz⟩ := eventually_not_two_stem_hits hgap D hyz
  obtain ⟨Upq, hUpq⟩ := eventually_not_two_stem_hits hgap D hpq
  let K := T + x + y + z + p + q + Uxy + Uxz + Uyz + Upq + M + 1
  have hlarge : ∀ a ∈ A \ (D : Set ℕ), K ≤ a →
      a ∈ tailRedundant 3 (A \ (D : Set ℕ)) N := by
    intro a ha haK
    by_contra hnon
    obtain ⟨n, _, han, _, hhit⟩ := private_target_of_not_tailRedundant hC ha hnon
    have hmiss : n ∉ (3 : ℕ) • ((A \ (D : Set ℕ)) \ {a}) := by
      intro hrep
      obtain ⟨f, hf, hsum⟩ := Set.mem_nsmul_iff_sum.mp hrep
      obtain ⟨i, hi⟩ := hhit f (fun i => (hf i).1) hsum
      exact (hf i).2 (by simpa using hi)
    dsimp [K] at haK
    let bad : ℕ → Prop := fun b => ∃ d ∈ D, ∃ u ∈ A, b + d + u = n
    let petal : ℕ → Prop := fun b => ∃ u ∈ A, b + u = n - a
    have halt : ∀ b ∈ A \ (D : Set ℕ), b ≠ a → T + b ≤ n → bad b ∨ petal b := by
      intro b hb hba hn
      rcases missing_triple_anchor_alternative hT hb hba hn hmiss with hbD | ⟨u, hu, heq⟩
      · exact Or.inl hbD
      · exact Or.inr ⟨u, hu, by omega⟩
    have hxalt : bad x ∨ petal x := halt x hx (by omega) (by omega)
    have hyalt : bad y ∨ petal y := halt y hy (by omega) (by omega)
    have hzalt : bad z ∨ petal z := halt z hz (by omega) (by omega)
    have hnxy : ¬ (bad x ∧ bad y) := hUxy n (by omega)
    have hnxz : ¬ (bad x ∧ bad z) := hUxz n (by omega)
    have hnyz : ¬ (bad y ∧ bad z) := hUyz n (by omega)
    have hpairs : (petal x ∧ petal y) ∨ (petal x ∧ petal z) ∨ (petal y ∧ petal z) := by
      rcases hxalt with hbx | hpx
      · exact Or.inr (Or.inr ⟨hyalt.resolve_left (fun hby => hnxy ⟨hbx, hby⟩),
          hzalt.resolve_left (fun hbz => hnxz ⟨hbx, hbz⟩)⟩)
      · rcases hyalt with hby | hpy
        · exact Or.inr (Or.inl ⟨hpx, hzalt.resolve_left (fun hbz => hnyz ⟨hby, hbz⟩)⟩)
        · exact Or.inl ⟨hpx, hpy⟩
    have htM : n - a ≤ M := by
      rcases hpairs with ⟨⟨u, hu, heu⟩, v, hv, hev⟩ |
        ⟨⟨u, hu, heu⟩, v, hv, hev⟩ | ⟨⟨u, hu, heu⟩, v, hv, hev⟩
      · have hh := hMxy u hu v hv (heu.trans hev.symm)
        dsimp [M]
        omega
      · have hh := hMxz u hu v hv (heu.trans hev.symm)
        dsimp [M]
        omega
      · have hh := hMyz u hu v hv (heu.trans hev.symm)
        dsimp [M]
        omega
    have hpalt : bad p ∨ petal p := halt p hp (by omega) (by omega)
    have hqalt : bad q ∨ petal q := halt q hq (by omega) (by omega)
    have hnpq : ¬ (bad p ∧ bad q) := hUpq n (by omega)
    have hlast : petal p ∨ petal q := by
      rcases hpalt with hbp | hpp
      · exact Or.inr (hqalt.resolve_left (fun hbq => hnpq ⟨hbp, hbq⟩))
      · exact Or.inl hpp
    rcases hlast with ⟨u, _, hu⟩ | ⟨u, _, hu⟩ <;> omega
  apply (hCi.sdiff (Finset.range K).finite_toSet).mono
  intro a ha
  apply hlarge a ha.1
  simpa only [Finset.mem_coe, Finset.mem_range, not_lt] using ha.2

/-- A two-basis with infinite gaps has no trap at order three. -/
lemma not_tail_trap_of_sparse_two {A : Set ℕ} {N L : ℕ}
    (hA : A.IsAsymptoticAddBasisOfOrder 2) (hgap : hasInfiniteGaps A) :
    ¬ TailTrapAbove 3 A N L := by
  rintro ⟨D, _, _, hC, hfin⟩
  exact infinite_tailRedundant_of_sparse_two hA hgap hC hfin

/-- Every order-two basis, without minimality, admits an infinite deletion preserving order three. -/
theorem infinite_deletion_of_two_basis {A : Set ℕ}
    (hA : A.IsAsymptoticAddBasisOfOrder 2) :
    ∃ B : Set ℕ, B ⊆ A ∧ B.Infinite ∧ (A \ B).IsAsymptoticAddBasisOfOrder 3 := by
  by_cases hgap : hasInfiniteGaps A
  · obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp
      (Set.isAsymptoticAddBasisOfOrder_iff_atTop.mp (hA.mono (show 2 ≤ 3 by omega)))
    exact infinite_deletion_of_finite_support_fusion
      (finite_support_fusion_of_no_tail_trap hN
        (not_tail_trap_of_sparse_two (L := 0) hA hgap))
  · exact infinite_deletion_of_not_infinite_gaps hA hgap

/-- A set that is minimal at order `k ≥ 3` in the sense of Problem 881 is not a basis of order two. -/
lemma not_two_basis_of_minimal_high_order {k : ℕ} {A : Set ℕ} (hk : 3 ≤ k)
    (hA : Erdos881.IsMinimalAsymptoticAddBasisOfOrder k A) :
    ¬ A.IsAsymptoticAddBasisOfOrder 2 := by
  intro htwo
  obtain ⟨B, hBA, hB, hbase⟩ := infinite_deletion_of_two_basis htwo
  exact hA.2 hBA hB (hbase.mono hk)

/-- Erdős Problem 881 for `k = 2`. -/
theorem erdos_881_two :
    ∀ A : Set ℕ, Erdos881.IsMinimalAsymptoticAddBasisOfOrder 2 A →
      ∃ B : Set ℕ, B ⊆ A ∧ B.Infinite ∧ (A \ B).IsAsymptoticAddBasisOfOrder 3 :=
  fun _ hA => infinite_deletion_of_two_basis hA.1

/-- Erdős and Nathanson (1980) asked whether a minimal asymptotic basis of order three can also
be an asymptotic basis of order two. It cannot: a two-basis `A` has a proper subset that is a
basis of order three. -/
theorem not_minimal_three_of_two_basis {A : Set ℕ} (hA : A.IsAsymptoticAddBasisOfOrder 2) :
    ∃ C : Set ℕ, C ⊂ A ∧ C.IsAsymptoticAddBasisOfOrder 3 := by
  obtain ⟨B, hBA, hB, hC⟩ := infinite_deletion_of_two_basis hA
  obtain ⟨b, hb⟩ := hB.nonempty
  exact ⟨A \ B, ⟨sdiff_subset, fun h => (h (hBA hb)).2 hb⟩, hC⟩

end Erdos881K2
