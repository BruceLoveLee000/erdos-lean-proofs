/-
Copyright 2026 Bruce Lee.
Released under the Apache License, Version 2.0.
-/
module

public import FormalConjectures.ErdosProblems.«1139»

/-!
# Erdős Problem 1139

[Erdős Problem 1139](https://www.erdosproblems.com/1139) asks: if `u 0 < u 1 < ⋯` are the positive
integers with at most two prime factors, counted with multiplicity, is
`limsup (u (k + 1) - u k) / log k = ∞`?

This file proves that it is. `erdos_1139` states the result with the sequence written out, and
`erdos_1139_fc` is `Erdos1139.erdos_1139` from google-deepmind/formal-conjectures.

The proof builds long runs of consecutive integers that each have at least three prime factors.
`large_holes` shows that for every `η > 0` and every `Y₀` there are `y ≥ Y₀` and `N ≥ y` with
`log (N + 1) ≤ η * y` such that `Ω (N + h) > 2` for all `1 ≤ h ≤ y`. Then `N` lies between two
consecutive terms `u k ≤ N < N + y < u (k + 1)`, and `k ≤ N` gives
`u (k + 1) - u k > y ≥ log (k + 1) / η`.

`N` comes from the Chinese remainder theorem (`hole_from_cover`): each `N + h` gets a divisor `d`
with `Ω d = 2` and `d < N + h`, either a product of two assigned primes or a prime square. The
residues of the small primes are chosen by averaging over all choices, a sieve with Euler-product
weights (`choose_cover`); offsets with a forced large prime factor are covered by bands of larger
primes (`Band`). The few offsets left uncovered are each given the square of a prime between `y`
and `y ^ 2`, and the modulus is small enough that `log (N + 1) ≤ η * y`.

The proof uses only Mathlib; formal-conjectures supplies only the statement.
-/

public section

namespace Erdos1139Proof

open Finset Filter
open scoped BigOperators ArithmeticFunction.Omega Topology

/- Prime counts and finite Euler products. -/
private def primes (n : ℕ) : Finset ℕ := (n + 1).primesBelow

private theorem mem_primes {p n : ℕ} : p ∈ primes n ↔ p ≤ n ∧ p.Prime := by
  simp [primes, Nat.mem_primesBelow]

private theorem primes_mono : Monotone primes := fun _a _b hab _p hp ↦
  mem_primes.mpr ⟨(mem_primes.mp hp).1.trans hab, (mem_primes.mp hp).2⟩

private theorem prod_primes (n : ℕ) : ∏ p ∈ primes n, p = primorial n := rfl

private theorem sum_log_primes (n : ℕ) :
    ∑ p ∈ primes n, Real.log (p : ℝ) ≤ Real.log 4 * n := by
  rw [← Real.log_prod (fun p hp ↦ Nat.cast_ne_zero.mpr (mem_primes.mp hp).2.ne_zero),
    ← Nat.cast_prod, prod_primes]
  have h := Chebyshev.theta_le_log4_mul_x (x := n) (Nat.cast_nonneg n)
  rw [Chebyshev.theta_eq_log_primorial, Nat.floor_natCast] at h
  exact h

private theorem log_two_bounds : (2 / 3 : ℝ) ≤ Real.log 2 ∧ Real.log 2 ≤ 1 := by
  constructor
  · linarith [Real.log_two_gt_d9]
  · exact (Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)).trans (by norm_num)

private theorem prime_count_upper {n : ℕ} (hn : 1 < n) :
    ((primes n).card : ℝ) ≤ 8 * n / Real.log n := by
  let lo := (primes n).filter (· ≤ n.sqrt)
  let hi := (primes n).filter (¬ · ≤ n.sqrt)
  have hlo : lo.card ≤ n.sqrt := by
    have ssub : lo ⊆ Icc 1 n.sqrt := by
      intro p hp
      exact mem_Icc.mpr ⟨(mem_primes.mp (mem_filter.mp hp).1).2.one_le, (mem_filter.mp hp).2⟩
    exact (card_le_card ssub).trans_eq (by simp [Nat.card_Icc])
  have hhi : ((hi.card : ℝ) * (Real.log n / 2)) ≤ Real.log 4 * n := calc
    _ = ∑ _p ∈ hi, Real.log n / 2 := by simp
    _ ≤ ∑ p ∈ hi, Real.log p := by
      refine sum_le_sum fun p hp ↦ ?_
      have hp' : n.sqrt < p := Nat.lt_of_not_ge (mem_filter.mp hp).2
      have hlogs : Real.log n ≤ Real.log ((p : ℝ) ^ 2) :=
        Real.log_le_log (Nat.cast_pos.mpr (by omega)) (by exact_mod_cast (Nat.sqrt_lt'.mp hp').le)
      rw [Real.log_pow] at hlogs
      norm_num at hlogs
      linarith
    _ ≤ ∑ p ∈ primes n, Real.log p :=
      sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun p hp _ ↦
        Real.log_nonneg (by exact_mod_cast (mem_primes.mp hp).2.one_le)
    _ ≤ _ := sum_log_primes n
  have hlog : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn)
  have hlog2 : Real.log (n : ℝ) ≤ 2 * Real.sqrt n := by
    rw [Real.sqrt_eq_rpow]
    have := Real.log_le_rpow_div (Nat.cast_nonneg (α := ℝ) n) (by norm_num : (0 : ℝ) < 1 / 2)
    linarith
  have hlo' : (lo.card : ℝ) * Real.log n ≤ 2 * n := calc
    _ ≤ Real.sqrt n * Real.log n :=
      mul_le_mul_of_nonneg_right ((Nat.cast_le.mpr hlo).trans (Real.nat_sqrt_le_real_sqrt)) hlog.le
    _ ≤ Real.sqrt n * (2 * Real.sqrt n) := mul_le_mul_of_nonneg_left hlog2 (Real.sqrt_nonneg _)
    _ = _ := by nlinarith [Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) n)]
  have hc : lo.card + hi.card = (primes n).card := card_filter_add_card_filter_not _
  apply (le_div_iff₀ hlog).mpr
  rw [← hc, Nat.cast_add, add_mul]
  have h4 : Real.log 4 ≤ 2 := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
    norm_num
    linarith [log_two_bounds.2]
  have hhi' := mul_le_mul_of_nonneg_right h4 (Nat.cast_nonneg (α := ℝ) n)
  linarith

private theorem prime_count_lower {n : ℕ} (hn : 12 ≤ n) :
    (n : ℝ) / (16 * Real.log n) ≤ (primes n).card := by
  let m := n / 2
  have hm : 4 ≤ m := by dsimp [m]; omega
  have hmpos : 0 < m := by omega
  have hmn : 2 * m ≤ n := by dsimp [m]; omega
  have hb : m.centralBinom ≤ n ^ (primes n).card := calc
    _ = ∏ p ∈ primes (2 * m), p ^ m.centralBinom.factorization p := by
      symm
      rw [primes, Nat.primesBelow, Finset.prod_filter_of_ne]
      · exact m.prod_pow_factorization_centralBinom
      · intro p _ hp
        by_contra hnp
        simp [Nat.factorization_eq_zero_of_not_prime _ hnp] at hp
    _ ≤ ∏ _p ∈ primes (2 * m), n := by
      refine prod_le_prod' fun _ _ ↦ ?_
      exact (Nat.pow_factorization_choose_le (k := m) (by omega : 0 < 2 * m)).trans hmn
    _ ≤ _ := by
      simp only [prod_const]
      exact Nat.pow_le_pow_right (by omega) (card_le_card (primes_mono hmn))
  have hpower : (4 : ℝ) ^ m ≤ (m : ℝ) * (n : ℝ) ^ (primes n).card := by
    exact_mod_cast (Nat.four_pow_lt_mul_centralBinom m hm).le.trans (Nat.mul_le_mul_left _ hb)
  have hlogs := Real.log_le_log (by positivity : 0 < (4 : ℝ) ^ m) hpower
  rw [Real.log_pow, Real.log_mul (Nat.cast_ne_zero.mpr (by omega)) (by positivity),
    Real.log_pow] at hlogs
  have hlogm : Real.log (m : ℝ) ≤ m :=
    (Real.log_le_sub_one_of_pos (Nat.cast_pos.mpr hmpos)).trans (by linarith)
  have h4 : (4 / 3 : ℝ) ≤ Real.log 4 := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
    norm_num
    linarith [log_two_bounds.1]
  have hmge : (n : ℝ) ≤ 3 * (m : ℝ) := by
    exact_mod_cast (show n ≤ 3 * m by dsimp [m]; omega)
  have hm4 := mul_le_mul_of_nonneg_left h4 (Nat.cast_nonneg (α := ℝ) m)
  apply (div_le_iff₀ (show 0 < 16 * Real.log (n : ℝ) from
    mul_pos (by norm_num) (Real.log_pos (by exact_mod_cast (show 1 < n by omega))))).mpr
  linarith

private theorem prod_dvd_of_pairwise_coprime {ι : Type*} (s : Finset ι) (d : ι → ℕ) (n : ℕ)
    (hc : Set.Pairwise (s : Set ι) (fun i j ↦ (d i).Coprime (d j)))
    (hd : ∀ i ∈ s, d i ∣ n) : (∏ i ∈ s, d i) ∣ n := by
  classical
  revert hc hd
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    intro hc hd
    rw [prod_insert hi]
    have hcop : (d i).Coprime (∏ j ∈ s, d j) := Nat.Coprime.prod_right fun j hj ↦
      hc (mem_insert_self _ _) (mem_insert_of_mem hj) (fun hij ↦ hi (hij ▸ hj))
    exact hcop.mul_dvd_of_dvd_of_dvd (hd i (mem_insert_self _ _))
      (ih (fun _ ha _ hb hab ↦ hc (mem_insert_of_mem ha) (mem_insert_of_mem hb) hab)
        (fun a ha ↦ hd a (mem_insert_of_mem ha)))

private theorem primes_log_div (n : ℕ) : ∑ p ∈ primes n, Real.log p / p ≤ 2 * Real.log n := by
  classical
  by_cases hn : n ≤ 1
  · have he : primes n = ∅ := eq_empty_iff_forall_notMem.mpr fun p hp ↦ by
      obtain ⟨hp1, hp2⟩ := mem_primes.mp hp
      have := hp2.two_le
      omega
    rw [he, sum_empty]
    obtain rfl | rfl : n = 0 ∨ n = 1 := by omega
    all_goals simp
  have hn' : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hDiv : (∏ p ∈ primes n, p ^ (n / p)) ∣ n.factorial := by
    refine prod_dvd_of_pairwise_coprime _ _ _ (fun p hp q hq hpq ↦ ?_) (fun p hp ↦ ?_)
    · exact ((Nat.coprime_primes (mem_primes.mp hp).2 (mem_primes.mp hq).2).mpr hpq).pow _ _
    · have hp' := (mem_primes.mp hp).2
      apply (hp'.pow_dvd_iff_le_factorization n.factorial_ne_zero).mpr
      rw [Nat.factorization_factorial hp' (show Nat.log p n < Nat.log p n + 2 by omega)]
      simpa using
        (single_le_sum (f := fun i ↦ n / p ^ i) (fun _ _ ↦ Nat.zero_le _) (a := 1)
          (show 1 ∈ Ico 1 (Nat.log p n + 2) by simp))
  have hlogs : (∑ p ∈ primes n, (↑(n / p) : ℝ) * Real.log p) ≤ (n : ℝ) * Real.log n := by
    calc
      _ = Real.log (↑(∏ p ∈ primes n, p ^ (n / p)) : ℝ) := by
        rw [Nat.cast_prod, Real.log_prod]
        · simp_rw [Nat.cast_pow, Real.log_pow]
        · intro p hp
          exact Nat.cast_ne_zero.mpr (pow_ne_zero _ (mem_primes.mp hp).2.ne_zero)
      _ ≤ Real.log (n.factorial : ℝ) := by
        apply Real.log_le_log
        · exact Nat.cast_pos.mpr (prod_pos fun p hp ↦ Nat.pow_pos (mem_primes.mp hp).2.pos)
        · exact_mod_cast Nat.le_of_dvd n.factorial_pos hDiv
      _ ≤ Real.log ((n : ℝ) ^ n) :=
        Real.log_le_log (Nat.cast_pos.mpr n.factorial_pos) (by exact_mod_cast Nat.factorial_le_pow n)
      _ = _ := Real.log_pow _ _
  suffices h : (n : ℝ) * (∑ p ∈ primes n, Real.log p / p) ≤ (n : ℝ) * (2 * Real.log n) from
    le_of_mul_le_mul_left h hn'
  rw [mul_sum]
  calc
    _ ≤ ∑ p ∈ primes n, 2 * ((↑(n / p) : ℝ) * Real.log p) := by
      refine sum_le_sum fun p hp ↦ ?_
      have hp' := mem_primes.mp hp
      have hp0 : (0 : ℝ) < p := Nat.cast_pos.mpr hp'.2.pos
      have h₂ : n ≤ 2 * (n / p) * p := by
        have hn1 : 1 ≤ n / p := (Nat.le_div_iff_mul_le hp'.2.pos).mpr (by simpa using hp'.1)
        calc
          _ ≤ (n / p + 1) * p := by
            have := Nat.div_add_mod n p
            have hm := Nat.mod_lt n hp'.2.pos
            rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm (n / p) p]
            omega
          _ ≤ _ := Nat.mul_le_mul_right _ (by omega)
      have h₃ : (n : ℝ) / p ≤ 2 * (↑(n / p) : ℝ) :=
        (div_le_iff₀ hp0).mpr (by exact_mod_cast h₂)
      have h₄ := mul_le_mul_of_nonneg_right h₃
        (Real.log_nonneg (by exact_mod_cast hp'.2.one_le : (1 : ℝ) ≤ p))
      calc
        _ = (n : ℝ) / p * Real.log p := by simp only [div_eq_mul_inv]; ring
        _ ≤ (2 * (↑(n / p) : ℝ)) * Real.log p := h₄
        _ = _ := by ring
    _ ≤ _ := by
      rw [← mul_sum]
      calc
        _ ≤ 2 * ((n : ℝ) * Real.log n) := mul_le_mul_of_nonneg_left hlogs (by norm_num)
        _ = _ := by ring

private noncomputable def euler (w : ℕ) (r : ℝ) : ℝ :=
  ∏ p ∈ primes w, (1 - (p : ℝ) ^ (-r))⁻¹

private theorem prime_rpow_lt_one {p : ℕ} (hp : p.Prime) {r : ℝ} (hr : 0 < r) :
    (p : ℝ) ^ (-r) < 1 :=
  Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hp.one_lt) (neg_neg_of_pos hr)

private theorem euler_pos (w : ℕ) {r : ℝ} (hr : 0 < r) : 0 < euler w r :=
  prod_pos fun _p hp ↦ inv_pos.mpr (sub_pos.mpr (prime_rpow_lt_one (mem_primes.mp hp).2 hr))

private theorem smooth_hasSum (w : ℕ) {r : ℝ} (hr : 0 < r) :
    HasSum (fun n : (w + 1).smoothNumbers ↦ (n.val : ℝ) ^ (-r)) (euler w r) := by
  let f : ℕ → ℝ := fun n ↦ (n : ℝ) ^ (-r)
  have hpow (p k : ℕ) : f (p ^ k) = (f p) ^ k := by
    dsimp [f]
    rw [Nat.cast_pow, ← Real.rpow_natCast_mul (Nat.cast_nonneg _), mul_comm,
      Real.rpow_mul (Nat.cast_nonneg _), Real.rpow_natCast]
  have hgeo {p : ℕ} (hp : p.Prime) :
      HasSum (fun k : ℕ ↦ f (p ^ k)) (1 - f p)⁻¹ := by
    simp_rw [hpow]
    exact hasSum_geometric_of_lt_one (Real.rpow_nonneg (Nat.cast_nonneg _) _) (prime_rpow_lt_one hp hr)
  have hs := (EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_tsum
    (f := f) (by simp [f])
    (fun {m n} _ ↦ by simp [f, Nat.cast_mul, Real.mul_rpow (Nat.cast_nonneg m) (Nat.cast_nonneg n)])
    (fun {p} hp ↦ (hgeo hp).summable.congr fun k ↦ (Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)).symm)
    (w + 1)).2
  have he : euler w r = ∏ p ∈ (w + 1).primesBelow, ∑' n, f (p ^ n) :=
    prod_congr rfl fun p hp ↦ (hgeo (Nat.prime_of_mem_primesBelow hp)).tsum_eq.symm
  rw [he]
  exact hs

private theorem sum_smooth_le_euler {s : Finset ℕ} {w : ℕ} {r : ℝ} (hr : 0 < r)
    (hs : ∀ n ∈ s, n ∈ (w + 1).smoothNumbers) :
    ∑ n ∈ s, (n : ℝ) ^ (-r) ≤ euler w r := by
  classical
  let t := s.subtype (· ∈ (w + 1).smoothNumbers)
  have ht : t.map (Function.Embedding.subtype _) = s := by
    ext n
    simp [t]
    exact fun hn ↦ hs n hn
  have hsum := smooth_hasSum w hr
  have he := hsum.summable.sum_le_tsum t (fun n _ ↦ Real.rpow_nonneg (Nat.cast_nonneg _) _)
  rw [hsum.tsum_eq] at he
  rw [← ht, sum_map]
  exact he

private theorem euler_ge_log (w : ℕ) : Real.log ((w : ℝ) + 1) ≤ euler w 1 := by
  have hs (n : ℕ) (hn : n ∈ Icc 1 w) : n ∈ (w + 1).smoothNumbers := by
    rw [Nat.mem_smoothNumbers]
    refine ⟨(Nat.lt_of_lt_of_le Nat.zero_lt_one (mem_Icc.mp hn).1).ne', fun p hp ↦ ?_⟩
    exact (Nat.le_of_mem_primeFactorsList hp).trans_lt (Nat.lt_succ_of_le (mem_Icc.mp hn).2)
  have h := sum_smooth_le_euler (w := w) (r := 1) (by norm_num) hs
  simp only [Real.rpow_neg_one] at h
  calc
    _ ≤ (harmonic w : ℝ) := by exact_mod_cast log_add_one_le_harmonic w
    _ = ∑ n ∈ Icc 1 w, (n : ℝ)⁻¹ := by rw [harmonic_eq_sum_Icc]; push_cast; rfl
    _ ≤ _ := h

private theorem exp_delta_bound (x s : ℝ) (hs : |x| ≤ s) :
    |Real.exp x - 1| ≤ |x| * Real.exp s := by
  have hs0 := (abs_nonneg _).trans hs
  by_cases hx : 0 ≤ x
  · rw [abs_of_nonneg hx, abs_of_nonneg (sub_nonneg.mpr ((Real.exp_le_exp.mpr hx).trans_eq' Real.exp_zero))]
    have hh := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (-x)) (Real.exp_nonneg x)
    rw [Real.exp_neg, inv_mul_cancel₀ (Real.exp_ne_zero _)] at hh
    calc
      _ ≤ x * Real.exp x := by linarith only [hh]
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ((le_abs_self _).trans hs)) hx
  · have hx' := le_of_not_ge hx
    have hle : Real.exp x ≤ 1 := (Real.exp_le_exp.mpr hx').trans_eq Real.exp_zero
    rw [abs_of_nonpos hx', abs_of_nonpos (sub_nonpos.mpr hle)]
    calc
      _ ≤ -x := by linarith [Real.add_one_le_exp x]
      _ ≤ _ := le_mul_of_one_le_right (neg_nonneg.mpr hx') (by simpa using Real.exp_le_exp.mpr hs0)

private theorem euler_compare {w : ℕ} {r r' s : ℝ}
    (hw : 1 < w) (hr : (1 / 2 : ℝ) ≤ r) (hr' : (1 / 2 : ℝ) ≤ r')
    (hs : max |r - 1| |r' - 1| * Real.log w ≤ s) :
    euler w r ≤ Real.exp (8 * Real.exp s * (|r - 1| + |r' - 1|) * Real.log w) * euler w r' := by
  have hr0 : 0 < r := by linarith
  have hr'0 : 0 < r' := by linarith
  apply (div_le_iff₀ (euler_pos w hr'0)).mp
  have hp (p) (hp : p ∈ primes w) : 1 < (p : ℝ) := by exact_mod_cast (mem_primes.mp hp).2.one_lt
  have hδ (p) (hpr : p ∈ primes w) (t : ℝ) (ht : |t - 1| ≤ max |r - 1| |r' - 1|) :
      |(p : ℝ) ^ (-t) - (p : ℝ)⁻¹| ≤ Real.exp s * |t - 1| * (Real.log p / p) := by
    have hlp := Real.log_nonneg (hp p hpr).le
    have hlog : Real.log (p : ℝ) ≤ Real.log w :=
      Real.log_le_log (zero_lt_one.trans (hp p hpr)) (by exact_mod_cast (mem_primes.mp hpr).1)
    have hlog' := Real.log_nonneg (by exact_mod_cast hw.le : (1 : ℝ) ≤ w)
    have hb : |(1 - t) * Real.log p| ≤ s := by
      rw [abs_mul, abs_of_nonneg hlp, abs_sub_comm]
      exact (mul_le_mul ht hlog hlp ((abs_nonneg _).trans (le_max_left _ _))).trans hs
    have hpos : 0 < (p : ℝ) := zero_lt_one.trans (hp p hpr)
    have he : (p : ℝ) ^ (-t) = (p : ℝ)⁻¹ * Real.exp ((1 - t) * Real.log p) := by
      rw [show -t = -1 + (1 - t) by ring, Real.rpow_add hpos, Real.rpow_neg_one,
        Real.rpow_def_of_pos hpos, mul_comm (1 - t)]
    rw [he, ← mul_sub_one, abs_mul, abs_of_nonneg (inv_nonneg.mpr hpos.le)]
    have hh := exp_delta_bound _ _ hb
    rw [abs_mul, abs_of_nonneg hlp, abs_sub_comm (1 : ℝ) t] at hh
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      mul_le_mul_of_nonneg_left hh (inv_nonneg.mpr hpos.le)
  have hden (p) (hpr : p ∈ primes w) (t : ℝ) (ht : 1 / 2 ≤ t) :
      (1 / 4 : ℝ) ≤ 1 - (p : ℝ) ^ (-t) := by
    have h1 : (p : ℝ) ^ (-t) ≤ (p : ℝ) ^ (-(1 / 2 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le (hp p hpr).le (by linarith)
    have h2 : (p : ℝ) ^ (-(1 / 2 : ℝ)) ≤ (2 : ℝ) ^ (-(1 / 2 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos (by norm_num)
        (by exact_mod_cast (mem_primes.mp hpr).2.two_le) (by norm_num)
    have h3 : (2 : ℝ) ^ (-(1 / 2 : ℝ)) ≤ 3 / 4 := by
      rw [Real.rpow_neg (by norm_num), ← Real.sqrt_eq_rpow]
      apply (inv_le_iff_one_le_mul₀ (Real.sqrt_pos.2 (by norm_num))).mpr
      have hsq := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
      nlinarith [Real.sqrt_nonneg (2 : ℝ)]
    linarith
  have hlocal (p) (hpr : p ∈ primes w) :
    Real.log ((1 - (p : ℝ) ^ (-r')) / (1 - (p : ℝ) ^ (-r))) ≤
      (4 * Real.exp s * (|r - 1| + |r' - 1|)) * (Real.log p / p) := by
    let a := (p : ℝ) ^ (-r)
    let b := (p : ℝ) ^ (-r')
    have ha : (1 / 4 : ℝ) ≤ 1 - a := hden p hpr r hr
    have hb : (1 / 4 : ℝ) ≤ 1 - b := hden p hpr r' hr'
    have hsub : a - b ≤ Real.exp s * (|r - 1| + |r' - 1|) * (Real.log p / p) := by
      have hδa := (le_abs_self (a - (p : ℝ)⁻¹)).trans (hδ p hpr r (le_max_left _ _))
      have hδb := (neg_le_abs (b - (p : ℝ)⁻¹)).trans (hδ p hpr r' (le_max_right _ _))
      rw [mul_add, add_mul]
      linarith
    change Real.log ((1 - b) / (1 - a)) ≤ _
    apply (Real.log_le_sub_one_of_pos (div_pos (by linarith) (by linarith))).trans
    have heq : (1 - b) / (1 - a) - 1 = (a - b) / (1 - a) := by
      field_simp
      ring
    rw [heq, div_le_iff₀ (by linarith)]
    have hcoef : 0 ≤ 4 * Real.exp s * (|r - 1| + |r' - 1|) * (Real.log p / p) := by
      exact mul_nonneg (by positivity) (div_nonneg (Real.log_nonneg (hp p hpr).le) (Nat.cast_nonneg _))
    have hmul := mul_le_mul_of_nonneg_left ha hcoef
    linarith
  have hlog : Real.log (euler w r / euler w r') ≤ _ := calc
    _ = ∑ p ∈ primes w, Real.log ((1 - (p : ℝ) ^ (-r')) / (1 - (p : ℝ) ^ (-r))) := by
      unfold euler
      rw [← prod_div_distrib, Real.log_prod]
      · apply sum_congr rfl
        intro p hpr
        rw [inv_div_inv]
      · intro p hpr
        exact div_ne_zero (inv_ne_zero (sub_pos.mpr (prime_rpow_lt_one (mem_primes.mp hpr).2 hr0)).ne')
          (inv_ne_zero (sub_pos.mpr (prime_rpow_lt_one (mem_primes.mp hpr).2 hr'0)).ne')
    _ ≤ ∑ p ∈ primes w, (4 * Real.exp s * (|r - 1| + |r' - 1|)) * (Real.log p / p) :=
      sum_le_sum hlocal
    _ ≤ 8 * Real.exp s * (|r - 1| + |r' - 1|) * Real.log w := by
      rw [← mul_sum]
      simpa [mul_comm, mul_left_comm, mul_assoc, show (8 : ℝ) = 4 * 2 by norm_num] using
        mul_le_mul_of_nonneg_left (primes_log_div w)
          (show 0 ≤ 4 * Real.exp s * (|r - 1| + |r' - 1|) by positivity)
  exact (Real.log_le_iff_le_exp (div_pos (euler_pos w hr0) (euler_pos w hr'0))).mp hlog

private theorem euler_le_zeta (w : ℕ) {r : ℝ} (hr : 1 < r) :
    euler w r ≤ 1 + 1 / (r - 1) := by
  let f : ℕ → ℝ := fun n ↦ (n : ℝ) ^ (-r)
  have hs : Summable f := Real.summable_nat_rpow.mpr (by linarith)
  rw [← (smooth_hasSum w (zero_lt_one.trans hr)).tsum_eq]
  calc
    _ ≤ ∑' n, f n := Summable.tsum_subtype_le f _ (fun n ↦ Real.rpow_nonneg (Nat.cast_nonneg _) _) hs
    _ = ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ r := by
      rw [hs.tsum_eq_zero_add]
      have hz : f 0 = 0 := by simp [f, Real.zero_rpow (show -r ≠ 0 by linarith)]
      rw [hz, zero_add]
      refine tsum_congr fun n ↦ ?_
      simp [f, Real.rpow_neg (by positivity : 0 ≤ (n : ℝ) + 1), one_div]
    _ ≤ _ := by
      have h := ZetaAsymptotics.zeta_limit_aux1 hr
      have hz : 0 ≤ ZetaAsymptotics.termTSum r :=
        tsum_nonneg fun n ↦ ZetaAsymptotics.term_nonneg (n + 1) r
      linarith [mul_nonneg (zero_lt_one.trans hr).le hz]

private noncomputable def eulerConst : ℝ := 3 * Real.exp (8 * Real.exp 1)

private theorem eulerConst_pos : 0 < eulerConst := by unfold eulerConst; positivity

private theorem euler_le_log {w : ℕ} (hw : 1 < w) :
    euler w 1 ≤ eulerConst * Real.log w := by
  have hlog : 0 < Real.log (w : ℝ) := Real.log_pos (by exact_mod_cast hw)
  let a := 1 / Real.log (w : ℝ)
  have ha : 0 < a := one_div_pos.mpr hlog
  have hsub : |1 + a - 1| = a := by rw [add_sub_cancel_left, abs_of_pos ha]
  have hparam : max |(1 : ℝ) - 1| |1 + a - 1| * Real.log w = 1 := by
    rw [hsub, sub_self, abs_zero, max_eq_right ha.le]
    exact one_div_mul_cancel hlog.ne'
  have hcomp := euler_compare hw (r := 1) (r' := 1 + a) (s := 1)
    (by norm_num) (by linarith) hparam.le
  have hζ := euler_le_zeta w (show 1 < 1 + a by linarith)
  have h1 : 1 ≤ 2 * Real.log (w : ℝ) := by
    have hh : Real.log 2 ≤ Real.log (w : ℝ) :=
      Real.log_le_log (by norm_num) (by exact_mod_cast hw)
    linarith [log_two_bounds.1]
  have hs : 1 / (1 + a - 1) = Real.log w := by
    rw [add_sub_cancel_left]
    exact one_div_one_div _
  calc
    _ ≤ Real.exp (8 * Real.exp 1) * euler w (1 + a) := by
      have heq : 8 * Real.exp 1 * (|(1 : ℝ) - 1| + |1 + a - 1|) * Real.log w = 8 * Real.exp 1 := by
        have haLog : a * Real.log w = 1 := by dsimp [a]; exact one_div_mul_cancel hlog.ne'
        rw [sub_self, abs_zero, zero_add, hsub, mul_assoc, haLog, mul_one]
      simpa only [heq] using hcomp
    _ ≤ Real.exp (8 * Real.exp 1) * (3 * Real.log w) := by
      rw [hs] at hζ
      exact mul_le_mul_of_nonneg_left (hζ.trans (by linarith)) (Real.exp_nonneg _)
    _ = _ := by unfold eulerConst; ring

private theorem sum_multiples_weighted {y d : ℕ} (c : ℝ) (hc : 0 ≤ c) :
    (∑ n ∈ Icc 1 y, if d ∣ n then c else 0) ≤ (y : ℝ) * (c / d) := by
  rw [← sum_filter, sum_const, nsmul_eq_mul]
  have hcount : ((Icc 1 y).filter (d ∣ ·)).card = y / d := by
    rw [← Nat.card_multiples' y d]
    congr 1
    ext n
    simp [Nat.one_le_iff_ne_zero, and_comm, and_left_comm]
  rw [hcount]
  calc
    _ ≤ (y : ℝ) / (d : ℝ) * c := mul_le_mul_of_nonneg_right (Nat.cast_div_le) hc
    _ = _ := by ring

private theorem divisor_product_average {ι : Type*} [Fintype ι]
    {κ : ι → Type*} [∀ i, Fintype (κ i)]
    (y : ℕ) (d : ∀ i, κ i → ℕ) (c : ∀ i, κ i → ℝ)
    (hc : ∀ i k, 0 ≤ c i k)
    (hco : ∀ i j, i ≠ j → ∀ k l, (d i k).Coprime (d j l)) :
    (∑ n ∈ Icc 1 y, ∏ i, ∑ k, if d i k ∣ n then c i k else 0) ≤
      (y : ℝ) * ∏ i, ∑ k, c i k / (d i k : ℝ) := by
  classical
  simp_rw [Fintype.prod_sum]
  rw [sum_comm, mul_sum]
  refine sum_le_sum fun a _ ↦ ?_
  have hdiv (n : ℕ) : (∏ i, d i (a i)) ∣ n ↔ ∀ i, d i (a i) ∣ n := by
    refine ⟨fun h i ↦ (dvd_prod_of_mem (fun j ↦ d j (a j)) (mem_univ i)).trans h, fun h ↦ ?_⟩
    exact prod_dvd_of_pairwise_coprime _ _ _
      (fun i _ j _ hij ↦ hco i j hij _ _) (fun i _ ↦ h i)
  have hprod (n : ℕ) :
    (∏ i, if d i (a i) ∣ n then c i (a i) else 0) =
      if (∏ i, d i (a i)) ∣ n then (∏ i, c i (a i)) else 0 := by
    by_cases h : (∏ i, d i (a i)) ∣ n
    · rw [if_pos h]
      exact prod_congr rfl fun i _ ↦ if_pos ((hdiv n).mp h i)
    · rw [if_neg h]
      obtain ⟨i, hi⟩ := not_forall.mp (mt (hdiv n).mpr h)
      exact prod_eq_zero (mem_univ i) (if_neg hi)
  simp_rw [hprod]
  simpa only [prod_div_distrib, ← Nat.cast_prod] using
    sum_multiples_weighted (y := y) _
      (prod_nonneg fun i _ ↦ hc i (a i))

private theorem sum_inv_sq_le {s : Finset ℕ} {b : ℕ} (hb : 0 < b)
    (hs : ∀ p ∈ s, b < p) : (∑ p ∈ s, (1 : ℝ) / p ^ 2) ≤ 1 / b := by
  classical
  let a := max b (s.sup id)
  have hsub : s ⊆ Ioc b a := by
    intro p hp
    exact mem_Ioc.mpr ⟨hs p hp, (le_sup (f := id) hp).trans (le_max_right _ _)⟩
  calc
    _ ≤ ∑ p ∈ Ioc b a, ((1 : ℝ) / (↑p - 1) - 1 / ↑p) := by
      calc
        _ ≤ ∑ p ∈ s, ((1 : ℝ) / (↑p - 1) - 1 / ↑p) := by
          refine sum_le_sum fun p hp ↦ ?_
          have hp' : (1 : ℝ) < p := by exact_mod_cast (show 1 < p by have := hs p hp; omega)
          have hdiff : 1 / (↑p - 1) - 1 / (p : ℝ) = 1 / ((p : ℝ) * (p - 1)) := by
            field_simp [show (p : ℝ) ≠ 0 by linarith, show (p : ℝ) - 1 ≠ 0 by linarith]
            ring
          rw [hdiff]
          apply one_div_le_one_div_of_le (mul_pos (by linarith) (by linarith))
          nlinarith
        _ ≤ _ := sum_le_sum_of_subset_of_nonneg hsub fun p hp _ ↦ by
          have hp' : (1 : ℝ) < p := by exact_mod_cast (show 1 < p by have := (mem_Ioc.mp hp).1; omega)
          exact sub_nonneg.mpr (one_div_le_one_div_of_le (by linarith) (by linarith))
    _ ≤ _ := by
      have htel (a : ℕ) (ha : b ≤ a) :
          (∑ p ∈ Ioc b a, ((1 : ℝ) / (↑p - 1) - 1 / ↑p)) = 1 / b - 1 / a := by
        induction a, ha using Nat.le_induction with
        | base => simp
        | succ a hab ih =>
          rw [sum_Ioc_succ_top hab, ih]
          push_cast
          ring
      rw [htel a (le_max_left _ _)]
      exact sub_le_self _ (by positivity)

/- Moments of the contribution of small prime factors. -/
private noncomputable def geomWeight (a : ℝ) : ℕ → ℝ
  | 0 => 1
  | k + 1 => (a - 1) * a ^ k

private theorem geomWeight_nonneg {a : ℝ} (ha : 1 ≤ a) (k : ℕ) : 0 ≤ geomWeight a k := by
  cases k <;> simp only [geomWeight]
  · norm_num
  · exact mul_nonneg (sub_nonneg.mpr ha) (pow_nonneg (zero_le_one.trans ha) _)

private theorem sum_geomWeight (a : ℝ) (k : ℕ) : ∑ i ∈ range (k + 1), geomWeight a i = a ^ k := by
  induction k with
  | zero => simp [geomWeight]
  | succ k ih =>
    rw [sum_range_succ, ih, geomWeight, pow_succ]
    ring

private theorem weighted_exponent_sum {a : ℝ} {p : ℕ} (ha : 1 ≤ a) (hp : 1 < p)
    (hap : a < p) (y : ℕ) :
    (∑ k : Fin (y + 1), geomWeight a k.val / (↑(p ^ k.val) : ℝ)) ≤
      (1 - (p : ℝ)⁻¹) / (1 - a / p) := by
  have hp0 : (0 : ℝ) < p := Nat.cast_pos.mpr (by omega)
  let b := a / (p : ℝ)
  have hb : 0 ≤ b := div_nonneg (zero_le_one.trans ha) hp0.le
  have hblt : b < 1 := (div_lt_one hp0).mpr hap
  let f : ℕ → ℝ := fun k ↦ geomWeight a k / (p : ℝ) ^ k
  have htail (k : ℕ) : f (k + 1) = ((a - 1) / p) * b ^ k := by
    simp only [f, b, geomWeight, pow_succ, div_pow]
    ring
  have hsumtail : HasSum (fun k : ℕ ↦ f (k + 1)) (((a - 1) / p) * (1 - b)⁻¹) := by
    simpa only [htail] using (hasSum_geometric_of_lt_one hb hblt).mul_left ((a - 1) / p)
  have hsum : Summable f := (summable_nat_add_iff 1).mp hsumtail.summable
  have ht := hsum.sum_le_tsum (range (y + 1)) fun i _ ↦
    div_nonneg (geomWeight_nonneg ha i) (pow_nonneg hp0.le _)
  rw [hsum.tsum_eq_zero_add, hsumtail.tsum_eq] at ht
  have hval : f 0 + (a - 1) / ↑p * (1 - b)⁻¹ = (1 - (p : ℝ)⁻¹) / (1 - a / p) := by
    dsimp [f, b]
    rw [geomWeight, pow_zero, div_one]
    have hpne := hp0.ne'
    have hbne : 1 - a / (p : ℝ) ≠ 0 := (sub_pos.mpr hblt).ne'
    have hnz : (p : ℝ) - a ≠ 0 := sub_ne_zero.mpr hap.ne'
    field_simp [hpne, hbne, hnz]
    ring
  rw [hval] at ht
  simp only [Nat.cast_pow]
  rw [Fin.sum_univ_eq_sum_range (f := f)]
  exact ht

private theorem sum_geom_dvd {y n p : ℕ} (hn : 0 < n) (hny : n ≤ y) (hp : p.Prime)
    (a : ℝ) :
    (∑ k : Fin (y + 1), if p ^ k.val ∣ n then geomWeight a k.val else 0) =
      a ^ n.factorization p := by
  have hf : n.factorization p ≤ y :=
    Nat.factorization_le_of_le_pow
      (hny.trans (Nat.lt_two_pow_self.le.trans (Nat.pow_le_pow_left hp.two_le _)))
  rw [Fin.sum_univ_eq_sum_range (f := fun k : ℕ ↦ if p ^ k ∣ n then geomWeight a k else 0)]
  simp only [hp.pow_dvd_iff_le_factorization hn.ne']
  rw [← sum_filter]
  have hfilt : (range (y + 1)).filter (· ≤ n.factorization p) = range (n.factorization p + 1) := by
    ext i
    simp only [mem_filter, mem_range]
    omega
  rw [hfilt, sum_geomWeight]

private theorem smooth_prod_factorization {w n : ℕ} {a : ℝ}
    (hn : n ∈ (w + 1).smoothNumbers) :
    (∏ p ∈ primes w, ((p : ℝ) ^ a) ^ n.factorization p) = (n : ℝ) ^ a := by
  have hf : n.factorization.support ⊆ primes w := by
    rw [Nat.support_factorization]
    exact Nat.primeFactors_subset_of_mem_smoothNumbers hn
  have hn0 := (Nat.mem_smoothNumbers.mp hn).1
  calc
    _ = ∏ p ∈ n.factorization.support, ((p : ℝ) ^ a) ^ n.factorization p := by
      refine (prod_subset hf fun p _ hp ↦ ?_).symm
      rw [Finsupp.notMem_support_iff.mp hp, pow_zero]
    _ = (↑(∏ p ∈ n.factorization.support, p ^ n.factorization p) : ℝ) ^ a := by
      rw [Nat.cast_prod, ← Real.finsetProd_rpow]
      · refine prod_congr rfl fun p _ ↦ ?_
        rw [Nat.cast_pow, ← Real.rpow_natCast_mul (Nat.cast_nonneg _), mul_comm,
          Real.rpow_mul (Nat.cast_nonneg _), Real.rpow_natCast]
      · intro p _
        positivity
    _ = _ := by
      exact congrArg (fun m : ℕ ↦ (m : ℝ) ^ a) (Nat.prod_factorization_pow_eq_self hn0)

private theorem smooth_count_moment {y w : ℕ} {a : ℝ} (ha : 0 ≤ a) (ha1 : a < 1) :
    (∑ n ∈ y.smoothNumbersUpTo (w + 1), (n : ℝ) ^ a) ≤
      (y : ℝ) * (euler w (1 - a) / euler w 1) := by
  classical
  let z (p : primes w) := (p.val : ℝ) ^ a
  have hz (p : primes w) : 1 ≤ z p :=
    Real.one_le_rpow (by exact_mod_cast (mem_primes.mp p.prop).2.one_le) ha
  have hz' (p : primes w) : z p < (p.val : ℝ) := by
    have hp1 : (1 : ℝ) < p.val := by exact_mod_cast (mem_primes.mp p.prop).2.one_lt
    convert Real.rpow_lt_rpow_of_exponent_lt hp1 ha1 using 1
    simp
  let f (n : ℕ) :=
    ∏ p : primes w, ∑ k : Fin (y + 1), if p.val ^ k.val ∣ n then geomWeight (z p) k.val else 0
  have hf0 (n : ℕ) : 0 ≤ f n :=
    prod_nonneg fun p _ ↦ sum_nonneg fun k _ ↦ by
      split_ifs
      · exact geomWeight_nonneg (hz p) _
      · exact le_rfl
  have hf (n : ℕ) (hn : n ∈ y.smoothNumbersUpTo (w + 1)) : f n = (n : ℝ) ^ a := by
    obtain ⟨hny, hns⟩ := Nat.mem_smoothNumbersUpTo.mp hn
    have hn0 := (Nat.mem_smoothNumbers.mp hns).1
    unfold f
    calc
      _ = ∏ p : primes w, (z p) ^ n.factorization p.val := by
        refine prod_congr rfl fun p _ ↦ ?_
        exact sum_geom_dvd (Nat.pos_of_ne_zero hn0) hny (mem_primes.mp p.prop).2 (z p)
      _ = ∏ p ∈ primes w, ((p : ℝ) ^ a) ^ n.factorization p :=
        Finset.prod_attach (primes w) (fun p ↦ ((p : ℝ) ^ a) ^ n.factorization p)
      _ = _ := smooth_prod_factorization hns
  have hprod := divisor_product_average (ι := (primes w : Type))
    (κ := fun _ ↦ Fin (y + 1)) y (fun p k ↦ p.val ^ k.val) (fun p k ↦ geomWeight (z p) k.val)
    (fun p k ↦ geomWeight_nonneg (hz p) _)
    (fun p q hpq k l ↦ ((Nat.coprime_primes (mem_primes.mp p.prop).2 (mem_primes.mp q.prop).2).mpr
      (fun h ↦ hpq (Subtype.ext h))).pow _ _)
  calc
    _ = ∑ n ∈ y.smoothNumbersUpTo (w + 1), f n := sum_congr rfl fun n hn ↦ (hf n hn).symm
    _ ≤ ∑ n ∈ Icc 1 y, f n :=
      sum_le_sum_of_subset_of_nonneg (fun n hn ↦ by
        obtain ⟨hny, hn'⟩ := Nat.mem_smoothNumbersUpTo.mp hn
        exact mem_Icc.mpr ⟨Nat.pos_of_ne_zero (Nat.mem_smoothNumbers.mp hn').1, hny⟩)
        (fun n _ _ ↦ hf0 n)
    _ ≤ _ := hprod
    _ ≤ (y : ℝ) * ∏ p : primes w, (1 - (p.val : ℝ)⁻¹) / (1 - z p / p.val) := by
      gcongr 1
      exact prod_le_prod
        (fun p _ ↦ sum_nonneg fun k _ ↦
          div_nonneg (geomWeight_nonneg (hz p) _) (Nat.cast_nonneg _))
        (fun p _ ↦ weighted_exponent_sum (hz p) (mem_primes.mp p.prop).2.one_lt (hz' p) y)
    _ = _ := by
      congr 1
      have he (p : primes w) : z p / p.val = (p.val : ℝ) ^ (-(1 - a)) := by
        dsimp [z]
        rw [show -(1 - a) = a - 1 by ring, Real.rpow_sub_one (by exact_mod_cast (mem_primes.mp p.prop).2.ne_zero)]
      simp_rw [he]
      simp only [euler, Real.rpow_neg_one, ← prod_div_distrib, inv_div_inv]
      exact prod_attach (primes w) (fun p ↦ (1 - (p : ℝ)⁻¹) / (1 - (p : ℝ) ^ (-(1 - a))))

private theorem exp_le_one_add_two_mul {x : ℝ} (hx : 0 ≤ x) (hhalf : x ≤ 1 / 2) :
    Real.exp x ≤ 1 + 2 * x := by
  have hn : 0 < 1 - x := by linarith
  have h := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (-x)) (Real.exp_nonneg x)
  rw [Real.exp_neg, inv_mul_cancel₀ (Real.exp_ne_zero x)] at h
  calc
    _ ≤ 1 / (1 - x) := (le_div_iff₀ hn).mpr (by linarith only [h])
    _ ≤ _ := (div_le_iff₀ hn).mpr (by nlinarith [mul_nonneg hx (show 0 ≤ 1 - 2 * x by linarith)])

/- Differences that create many collisions in the sieve. -/
private noncomputable def overlapSum (P : Finset ℕ) (d : ℕ) : ℝ :=
  ∑ p ∈ P with p ∣ d, (p : ℝ)⁻¹

private noncomputable def badDiffs (P : Finset ℕ) (H y : ℕ) : Finset ℕ := by
  classical
  exact (Icc 1 y).filter fun d ↦ 1 / (H : ℝ) ^ 3 < overlapSum P d

private theorem overlap_exponential {P : Finset ℕ} {H : ℕ}
    (hH : 2 ≤ H) (hP : ∀ p ∈ P, H ^ 10 < p ∧ p.Prime) (y : ℕ) :
    (∑ n ∈ Icc 1 y, Real.exp ((H : ℝ) ^ 6 * overlapSum P n)) ≤ 2 * y := by
  classical
  have hHR : (2 : ℝ) ≤ H := by exact_mod_cast hH
  have hH0 : (0 : ℝ) < H := by linarith
  let d (p : P) (b : Bool) : ℕ := if b then p.val else 1
  let c (p : P) (b : Bool) : ℝ := if b then 2 * ((H : ℝ) ^ 6 / p.val) else 1
  let f (n : ℕ) := ∏ p : P, ∑ b : Bool, if d p b ∣ n then c p b else 0
  have hf' (p : P) (n : ℕ) :
      (∑ b : Bool, if d p b ∣ n then c p b else 0) =
        1 + if p.val ∣ n then 2 * ((H : ℝ) ^ 6 / p.val) else 0 := by
    simp [d, c, add_comm]
  have hc (p : P) (b : Bool) : 0 ≤ c p b := by cases b <;> simp [c]; positivity
  have hco (p q : P) (hne : p ≠ q) (b e : Bool) : (d p b).Coprime (d q e) := by
    cases b <;> cases e <;> simp [d]
    exact (Nat.coprime_primes (hP p.val p.prop).2 (hP q.val q.prop).2).mpr
      (fun e ↦ hne (Subtype.ext e))
  have hall : (∑ n ∈ Icc 1 y, f n) ≤ (y : ℝ) * ∏ p : P, (1 + 2 * ((H : ℝ) ^ 6 / p.val ^ 2)) := by
    have he (p : P) : (∑ b : Bool, c p b / (d p b : ℝ)) = 1 + 2 * ((H : ℝ) ^ 6 / p.val ^ 2) := by
      simp [c, d, div_eq_mul_inv]
      ring
    simpa only [f, he] using divisor_product_average y d c hc hco
  have htail : (∑ p ∈ P, (1 : ℝ) / p ^ 2) ≤ 1 / ((H : ℝ) ^ 10) := by
    have hnat := sum_inv_sq_le (s := P) (b := H ^ 10) (by positivity) fun p hp ↦ (hP p hp).1
    simpa only [Nat.cast_pow] using hnat
  have hsmall : (2 * (H : ℝ) ^ 6 / (H : ℝ) ^ 10) ≤ 1 / 2 := by
    have hh : (H : ℝ) ^ 4 ≥ 4 := by nlinarith [pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hHR 4]
    rw [pow_add (H : ℝ) 6 4, mul_comm ((H : ℝ) ^ 6) ((H : ℝ) ^ 4),
      mul_div_mul_right _ _ (by positivity : (H : ℝ) ^ 6 ≠ 0)]
    apply (div_le_iff₀ (by positivity)).mpr
    linarith
  have hexp (n : ℕ) : Real.exp ((H : ℝ) ^ 6 * overlapSum P n) ≤ f n := by
    have hfilt : overlapSum P n = ∑ p ∈ P, if p ∣ n then (p : ℝ)⁻¹ else 0 :=
      sum_filter ..
    rw [hfilt, mul_sum, Real.exp_sum]
    let g (p : ℕ) := Real.exp ((H : ℝ) ^ 6 * (if p ∣ n then (p : ℝ)⁻¹ else 0))
    change (∏ p ∈ P, g p) ≤ f n
    have hco : (∏ p : P, g p.val) = ∏ p ∈ P, g p := Finset.prod_attach P g
    rw [← hco]
    unfold f
    refine prod_le_prod (fun p _ ↦ Real.exp_nonneg _) fun p _ ↦ ?_
    rw [hf' p n]
    dsimp [g]
    by_cases hp : p.val ∣ n
    · simp only [if_pos hp]
      have hp0 : (0 : ℝ) < p.val := Nat.cast_pos.mpr (hP p.val p.prop).2.pos
      have hpH : (H : ℝ) ^ 10 ≤ p.val := by exact_mod_cast (hP p.val p.prop).1.le
      have ht : (H : ℝ) ^ 6 * (p.val : ℝ)⁻¹ ≤ 1 / 2 := calc
        _ = (H : ℝ) ^ 6 / p.val := by rw [div_eq_mul_inv]
        _ ≤ (H : ℝ) ^ 6 / ((H : ℝ) ^ 10) :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) hpH
        _ ≤ _ := by
          have ha : 0 ≤ (H : ℝ) ^ 6 / (H : ℝ) ^ 10 := by positivity
          rw [mul_div_assoc] at hsmall
          linarith only [ha, hsmall]
      simpa [div_eq_mul_inv, mul_assoc] using
        exp_le_one_add_two_mul (show 0 ≤ (H : ℝ) ^ 6 * (p.val : ℝ)⁻¹ by positivity) ht
    · simp only [if_neg hp, mul_zero, Real.exp_zero, add_zero, le_rfl]
  calc
    _ ≤ ∑ n ∈ Icc 1 y, f n := sum_le_sum fun n _ ↦ hexp n
    _ ≤ _ := hall
    _ = (y : ℝ) * ∏ p ∈ P, (1 + 2 * ((H : ℝ) ^ 6 / p ^ 2)) := by
      congr 1
      exact Finset.prod_attach P (fun p ↦ 1 + 2 * ((H : ℝ) ^ 6 / p ^ 2))
    _ ≤ (y : ℝ) * Real.exp (2 * (H : ℝ) ^ 6 * (∑ p ∈ P, (1 : ℝ) / p ^ 2)) := by
      gcongr 1
      rw [mul_sum, Real.exp_sum]
      refine prod_le_prod (fun p _ ↦ by positivity) fun p _ ↦ ?_
      have he : 2 * (H : ℝ) ^ 6 * (1 / (p : ℝ) ^ 2) = 2 * ((H : ℝ) ^ 6 / (p : ℝ) ^ 2) := by ring
      rw [he, add_comm (1 : ℝ)]
      exact Real.add_one_le_exp _
    _ ≤ (y : ℝ) * Real.exp (2 * (H : ℝ) ^ 6 / (H : ℝ) ^ 10) := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg y)
      apply Real.exp_le_exp.mpr
      simpa [div_eq_mul_inv, mul_assoc] using mul_le_mul_of_nonneg_left htail (by positivity : 0 ≤ 2 * (H : ℝ) ^ 6)
    _ ≤ _ := by
      rw [mul_comm (2 : ℝ) (y : ℝ)]
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg y)
      have h0 : 0 ≤ 2 * (H : ℝ) ^ 6 / (H : ℝ) ^ 10 := by positivity
      linarith [exp_le_one_add_two_mul h0 hsmall]

private theorem badDiffs_card {P : Finset ℕ} {H : ℕ}
    (hH : 2 ≤ H) (hP : ∀ p ∈ P, H ^ 10 < p ∧ p.Prime) (y : ℕ) :
    ((badDiffs P H y).card : ℝ) ≤ 2 * y * Real.exp (-(H : ℝ) ^ 3) := by
  classical
  let s := badDiffs P H y
  have hH0 : (0 : ℝ) < H := by exact_mod_cast (show 0 < H by omega)
  have h : (s.card : ℝ) * Real.exp ((H : ℝ) ^ 3) ≤ 2 * y := calc
    _ = ∑ n ∈ s, Real.exp ((H : ℝ) ^ 3) := by simp
    _ ≤ ∑ n ∈ s, Real.exp ((H : ℝ) ^ 6 * overlapSum P n) := by
      refine sum_le_sum fun n hn ↦ Real.exp_le_exp.mpr ?_
      have hn' := (mem_filter.mp hn).2
      have hn₀ := mul_le_mul_of_nonneg_left hn'.le (pow_nonneg hH0.le 6)
      have heq : (H : ℝ) ^ 6 * (1 / (H : ℝ) ^ 3) = (H : ℝ) ^ 3 := by
        field_simp
      exact heq ▸ hn₀
    _ ≤ ∑ n ∈ Icc 1 y, Real.exp ((H : ℝ) ^ 6 * overlapSum P n) :=
      sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun n _ _ ↦ Real.exp_nonneg _)
    _ ≤ _ := overlap_exponential hH hP y
  rw [Real.exp_neg, ← div_eq_mul_inv]
  exact (le_div_iff₀ (Real.exp_pos _)).mpr h

/- Finite averages over independent residue choices. -/
private noncomputable def mean {α : Type*} (s : Finset α) (f : α → ℝ) : ℝ :=
  (∑ a ∈ s, f a) / s.card

private theorem mean_congr {α : Type*} {s : Finset α} {f g : α → ℝ}
    (h : ∀ a ∈ s, f a = g a) : mean s f = mean s g := by
  unfold mean
  rw [sum_congr rfl h]

private theorem mean_le {α : Type*} {s : Finset α} {f g : α → ℝ}
    (h : ∀ a ∈ s, f a ≤ g a) : mean s f ≤ mean s g :=
  div_le_div_of_nonneg_right (sum_le_sum h) (Nat.cast_nonneg _)

private theorem mean_const {α : Type*} {s : Finset α} (hs : s.Nonempty) (c : ℝ) :
    mean s (fun _ ↦ c) = c := by
  rw [mean, sum_const, nsmul_eq_mul, mul_comm, mul_div_cancel_right₀]
  exact Nat.cast_ne_zero.mpr hs.card_ne_zero

private theorem mean_mul {α : Type*} (s : Finset α) (f : α → ℝ) (c : ℝ) :
    mean s (fun x ↦ c * f x) = c * mean s f := by
  simp [mean, ← mul_sum, mul_div_assoc]

private theorem mean_add {α : Type*} (s : Finset α) (f g : α → ℝ) :
    mean s (fun x ↦ f x + g x) = mean s f + mean s g := by
  simp [mean, sum_add_distrib, add_div]

private theorem mean_sub {α : Type*} (s : Finset α) (f g : α → ℝ) :
    mean s (fun x ↦ f x - g x) = mean s f - mean s g := by
  simp [mean, sum_sub_distrib, sub_div]

private theorem mean_sum {α β : Type*} (s : Finset α) (t : Finset β) (f : α → β → ℝ) :
    mean s (fun a ↦ ∑ b ∈ t, f a b) = ∑ b ∈ t, mean s (fun a ↦ f a b) := by
  unfold mean
  rw [sum_comm, Finset.sum_div]

private theorem mean_of_forall_le {α : Type*} {s : Finset α} (hs : s.Nonempty) {f : α → ℝ} {c : ℝ}
    (h : ∀ a ∈ s, f a ≤ c) : mean s f ≤ c := (mean_le h).trans_eq (mean_const hs c)

private theorem exists_le_mean {α : Type*} {s : Finset α} (hs : s.Nonempty) (f : α → ℝ) :
    ∃ a ∈ s, f a ≤ mean s f := by
  by_contra! h
  have hsum := sum_lt_sum_of_nonempty hs h
  rw [sum_const, nsmul_eq_mul, mean, mul_div_cancel₀] at hsum
  · exact (lt_irrefl _ hsum).elim
  · exact Nat.cast_ne_zero.mpr hs.card_ne_zero

private theorem mean_pi_avoid {ι : Type*} [Fintype ι] [DecidableEq ι]
    {β : ι → Type*} [∀ i, DecidableEq (β i)]
    (A B : ∀ i, Finset (β i)) :
    mean (Fintype.piFinset A) (fun a ↦ if ∀ i, a i ∉ B i then (1 : ℝ) else 0) =
      ∏ i, (((A i \ B i).card : ℝ) / (A i).card) := by
  classical
  have hfilter : (Fintype.piFinset A).filter (fun a ↦ ∀ i, a i ∉ B i) =
      Fintype.piFinset (fun i ↦ A i \ B i) := by
    ext a
    simp only [mem_filter, Fintype.mem_piFinset]
    constructor
    · exact fun h i ↦ mem_sdiff.mpr ⟨h.1 i, h.2 i⟩
    · exact fun h ↦ ⟨fun i ↦ (mem_sdiff.mp (h i)).1, fun i ↦ (mem_sdiff.mp (h i)).2⟩
  rw [mean, ← sum_filter, hfilter, sum_const, nsmul_eq_mul, mul_one]
  simp [Fintype.card_piFinset, Nat.cast_prod, prod_div_distrib]

private def merge {ι : Type*} {β : ι → Type*} (P : ι → Prop) [DecidablePred P]
    (a b : ∀ i, β i) : ∀ i, β i := fun i ↦ if P i then a i else b i

private theorem mean_merge {ι : Type*} [Fintype ι] [DecidableEq ι]
    {β : ι → Type*} [∀ i, DecidableEq (β i)] (A : ∀ i, Finset (β i))
    (P : ι → Prop) [DecidablePred P]
    (f : (∀ i, β i) → ℝ) :
    mean (Fintype.piFinset A) f =
      mean (Fintype.piFinset A) (fun a ↦ mean (Fintype.piFinset A) (fun b ↦ f (merge P a b))) := by
  classical
  let s := Fintype.piFinset A
  by_cases hne : s.Nonempty
  · have hs0 : (s.card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hne.card_ne_zero
    have hswap (a b : ∀ i, β i) : merge P (merge P a b) (merge P b a) = a := by
      funext i
      by_cases hi : P i <;> simp [merge, hi]
    have hmem (a b : ∀ i, β i) (ha : a ∈ s) (hb : b ∈ s) :
        merge P a b ∈ s := by
      refine Fintype.mem_piFinset.mpr fun i ↦ ?_
      dsimp [merge]
      split_ifs
      · exact Fintype.mem_piFinset.mp ha i
      · exact Fintype.mem_piFinset.mp hb i
    have hf : (∑ x ∈ s ×ˢ s, f (merge P x.1 x.2)) = ∑ x ∈ s ×ˢ s, f x.1 := by
      refine sum_bij (fun x _ ↦ (merge P x.1 x.2, merge P x.2 x.1)) ?_ ?_ ?_ ?_
      · intro x hx
        exact mem_product.mpr ⟨hmem _ _ (mem_product.mp hx).1 (mem_product.mp hx).2,
          hmem _ _ (mem_product.mp hx).2 (mem_product.mp hx).1⟩
      · rintro ⟨a,b⟩ _ ⟨c,d⟩ _ h
        simpa only [hswap] using congrArg (fun x ↦ (merge P x.1 x.2, merge P x.2 x.1)) h
      · rintro ⟨a,b⟩ hx
        have hab := mem_product.mp hx
        exact ⟨(merge P a b, merge P b a),
          mem_product.mpr ⟨hmem _ _ hab.1 hab.2, hmem _ _ hab.2 hab.1⟩, Prod.ext (hswap _ _) (hswap _ _)⟩
      · exact fun _ _ ↦ rfl
    rw [sum_product, sum_product] at hf
    change mean s f = mean s (fun a ↦ mean s (fun b ↦ f (merge P a b)))
    simp only [mean, ← Finset.sum_div, hf, sum_const, nsmul_eq_mul, mul_comm (s.card : ℝ)]
    rw [← sum_mul, mul_div_cancel_right₀ _ hs0]
  · have h : s = ∅ := not_nonempty_iff_eq_empty.mp hne
    change mean s f = mean s (fun a ↦ mean s (fun b ↦ f (merge P a b)))
    simp [mean, h]

private noncomputable def sigma (P : Finset ℕ) : ℝ := ∏ p ∈ P, (1 - (p : ℝ)⁻¹)

private theorem sigma_pos {P : Finset ℕ} (hP : ∀ p ∈ P, 1 < p) : 0 < sigma P := by
  unfold sigma
  refine prod_pos fun p hp ↦ sub_pos.mpr ?_
  exact (inv_lt_one₀ (by exact_mod_cast (show 0 < p from (hP p hp).pos))).mpr
    (by exact_mod_cast hP p hp)

private theorem sigma_le_one {P : Finset ℕ} (hP : ∀ p ∈ P, 1 < p) : sigma P ≤ 1 := by
  unfold sigma
  apply prod_le_one
  · intro p hp
    exact sub_nonneg.mpr ((inv_lt_one₀
      (by exact_mod_cast (show 0 < p from (hP p hp).pos))).mpr (by exact_mod_cast hP p hp)).le
  · intro p _
    exact sub_le_self _ (by positivity)

private theorem sigma_primes (w : ℕ) : sigma (primes w) = (euler w 1)⁻¹ := by
  simp [sigma, euler, Real.rpow_neg_one, Finset.prod_inv_distrib]

private theorem log_one_sub_bounds {x : ℝ} (_hx : 0 ≤ x) (hhalf : x ≤ 1 / 2) :
    -x - 2 * x ^ 2 ≤ Real.log (1 - x) ∧ Real.log (1 - x) ≤ -x := by
  have hpos : 0 < 1 - x := by linarith
  constructor
  · have hi := Real.log_le_sub_one_of_pos (inv_pos.mpr hpos)
    rw [Real.log_inv] at hi
    have hbound : (1 - x)⁻¹ - 1 ≤ x + 2 * x ^ 2 := by
      have h0 : 0 ≤ x ^ 2 * (1 - 2 * x) :=
        mul_nonneg (sq_nonneg _) (by linarith)
      have he : (1 - x)⁻¹ - 1 = x / (1 - x) := by
        field_simp [hpos.ne']
        ring
      rw [he, div_le_iff₀ hpos]
      linarith [show (x + 2 * x ^ 2) * (1 - x) - x = x ^ 2 * (1 - 2 * x) by ring]
    linarith
  · linarith [Real.log_le_sub_one_of_pos hpos]

private theorem local_survive_bound {p v D : ℝ}
    (hp : 2 ≤ p) (hv : 0 ≤ v) (hvD : v ≤ D) (hsmall : 2 * D ≤ p - 1) :
    -10 * (D + 1) ^ 2 / p ^ 2 ≤ Real.log (1 - v / (p - 1)) - D * Real.log (1 - p⁻¹) ∧
    Real.log (1 - v / (p - 1)) - D * Real.log (1 - p⁻¹) ≤
      10 * (D + 1) ^ 2 / p ^ 2 + (D - v) / p := by
  have hp0 : 0 < p := by linarith
  have hp1 : 0 < p - 1 := by linarith
  have hD : 0 ≤ D := hv.trans hvD
  have hx : 0 ≤ v / (p - 1) := div_nonneg hv hp1.le
  have hx' : v / (p - 1) ≤ 1 / 2 := (div_le_iff₀ hp1).mpr (by linarith)
  have hy : 0 ≤ p⁻¹ := inv_nonneg.mpr hp0.le
  have hy' : p⁻¹ ≤ 1 / 2 := (inv_le_iff_one_le_mul₀ hp0).mpr (by linarith)
  have hlogx := log_one_sub_bounds hx hx'
  have hlogy := log_one_sub_bounds hy hy'
  have h1 : v / (p - 1) ≤ v / p + 2 * D / p ^ 2 := by
    have hdiff : v / (p - 1) - v / p = v / (p * (p - 1)) := by
      field_simp [hp0.ne', hp1.ne']
      ring
    have hbound : v / (p * (p - 1)) ≤ 2 * D / p ^ 2 := by
      have hden : p ^ 2 ≤ 2 * (p * (p - 1)) := by nlinarith [mul_nonneg hp0.le (show 0 ≤ p - 2 by linarith)]
      calc
        _ ≤ D / (p * (p - 1)) := div_le_div_of_nonneg_right hvD (by positivity)
        _ = (2 * D) / (2 * (p * (p - 1))) := by
          rw [mul_comm (2 : ℝ) D, mul_comm (2 : ℝ) (p * (p - 1)), mul_div_mul_right _ _ (by norm_num)]
        _ ≤ _ := div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos hp0) hden
    linarith
  have h2 : v / (p - 1) ≤ (2 * D) / p := by
    rw [div_le_div_iff₀ hp1 hp0]
    have hh := mul_le_mul_of_nonneg_right hvD hp0.le
    nlinarith [mul_nonneg hD (show 0 ≤ p - 2 by linarith)]
  have hsquare : (v / (p - 1)) ^ 2 ≤ (2 * D / p) ^ 2 := pow_le_pow_left₀ hx h2 2
  have h3 : v / p ≤ v / (p - 1) :=
    div_le_div_of_nonneg_left hv hp1 (by linarith)
  have h4 : 2 * D + 8 * D ^ 2 ≤ 10 * (D + 1) ^ 2 := by nlinarith
  have h5 : (2 * D + 8 * D ^ 2) / p ^ 2 ≤ 10 * (D + 1) ^ 2 / p ^ 2 :=
    div_le_div_of_nonneg_right h4 (by positivity)
  have h6 : (2 * D / p) ^ 2 = 4 * D ^ 2 / p ^ 2 := by ring
  rw [h6] at hsquare
  have hdlo := mul_le_mul_of_nonneg_left hlogy.1 hD
  have hdhi := mul_le_mul_of_nonneg_left hlogy.2 hD
  have hconst : 2 * D ≤ 10 * (D + 1) ^ 2 := by nlinarith
  have hconst' := div_le_div_of_nonneg_right hconst (show 0 ≤ p ^ 2 by positivity)
  constructor
  · linarith only [hlogx.1, hdhi, h1, hsquare, h5, hvD,
      div_le_div_of_nonneg_right hvD hp0.le,
      show (-10 * (D + 1) ^ 2 / p ^ 2) = -(10 * (D + 1) ^ 2 / p ^ 2) by ring,
      show D * -p⁻¹ = -(D / p) by ring,
      show (2 * D + 8 * D ^ 2) / p ^ 2 = 2 * D / p ^ 2 + 2 * (4 * D ^ 2 / p ^ 2) by ring]
  · linarith only [hlogx.2, hdlo, h3, hconst',
      show D * (-p⁻¹ - 2 * (p⁻¹) ^ 2) = -(D / p) - 2 * D / p ^ 2 by ring,
      show (D - v) / p = D / p - v / p by ring]

private theorem survive_product_bounds {P : Finset ℕ} {b D : ℕ} (hb : 0 < b)
    (hP : ∀ p ∈ P, b < p ∧ 2 ≤ p ∧ 2 * D ≤ p - 1)
    (v : ℕ → ℕ) (hv : ∀ p ∈ P, v p ≤ D) :
    let prob := ∏ p ∈ P, (1 - (v p : ℝ) / ((p : ℝ) - 1))
    let e := 10 * ((D : ℝ) + 1) ^ 2 / (b : ℝ)
    sigma P ^ D * Real.exp (-e) ≤ prob ∧
    prob ≤ sigma P ^ D * Real.exp (e + ∑ p ∈ P, (↑D - (v p : ℝ)) / (p : ℝ)) := by
  dsimp only
  have hσ : 0 < sigma P := sigma_pos (fun p hp ↦ by have := (hP p hp).2.1; omega)
  let f (p : ℕ) := 1 - (v p : ℝ) / ((p : ℝ) - 1)
  have hf (p) (hp : p ∈ P) : 0 < f p := by
    dsimp [f]
    apply sub_pos.mpr
    apply (div_lt_one (show 0 < (p : ℝ) - 1 by
      have : (2 : ℝ) ≤ p := by exact_mod_cast (hP p hp).2.1
      linarith)).mpr
    have h1 : (v p : ℝ) ≤ D := by exact_mod_cast hv p hp
    have h2nat : 2 * D + 1 ≤ p := by have := (hP p hp).2; omega
    have h2cast : (2 : ℝ) * D + 1 ≤ p := by exact_mod_cast h2nat
    have h2 : (2 : ℝ) * D ≤ (p : ℝ) - 1 := by linarith
    have h3 : (2 : ℝ) ≤ p := by exact_mod_cast (hP p hp).2.1
    linarith
  have hg (p) (hp : p ∈ P) : 0 < 1 - (p : ℝ)⁻¹ := by
    have hp1 : (1 : ℝ) < p := by exact_mod_cast (show 1 < p by have := (hP p hp).2.1; omega)
    exact sub_pos.mpr ((inv_lt_one₀ (zero_lt_one.trans hp1)).mpr hp1)
  have hpBound (p) (hp : p ∈ P) :=
    local_survive_bound (p := p) (v := (v p : ℝ)) (D := D)
      (by exact_mod_cast (hP p hp).2.1) (Nat.cast_nonneg _) (by exact_mod_cast hv p hp)
      (by
        have hnat : 2 * D + 1 ≤ p := by have := (hP p hp).2; omega
        have hcast : (2 : ℝ) * D + 1 ≤ p := by exact_mod_cast hnat
        linarith)
  have hSum :
      Real.log (∏ p ∈ P, f p) - (D : ℝ) * Real.log (sigma P) =
        ∑ p ∈ P, (Real.log (f p) - (D : ℝ) * Real.log (1 - (p : ℝ)⁻¹)) := by
    unfold sigma
    rw [Real.log_prod (fun p hp ↦ (hf p hp).ne'),
      Real.log_prod (fun p hp ↦ (hg p hp).ne'), mul_sum, sum_sub_distrib]
  have hz :
    ∑ p ∈ P, 10 * ((D : ℝ) + 1) ^ 2 / (p : ℝ) ^ 2 ≤ 10 * ((D : ℝ) + 1) ^ 2 / b := by
    simp only [div_eq_mul_inv, ← mul_sum]
    exact mul_le_mul_of_nonneg_left
      (by simpa only [one_div] using sum_inv_sq_le hb (fun p hp ↦ (hP p hp).1))
      (by positivity)
  have hLow := sum_le_sum (fun p hp ↦ (hpBound p hp).1)
  have hHigh := sum_le_sum (fun p hp ↦ (hpBound p hp).2)
  have hProd : 0 < ∏ p ∈ P, f p := prod_pos hf
  change sigma P ^ D * _ ≤ ∏ p ∈ P, f p ∧ (∏ p ∈ P, f p) ≤ _
  constructor
  · apply (Real.log_le_log_iff (mul_pos (pow_pos hσ _) (Real.exp_pos _)) hProd).mp
    rw [Real.log_mul (pow_ne_zero _ hσ.ne') (Real.exp_ne_zero _), Real.log_pow, Real.log_exp]
    simp_rw [show ∀ p : ℕ, -10 * ((D : ℝ) + 1) ^ 2 / (p : ℝ) ^ 2 =
      -(10 * ((D : ℝ) + 1) ^ 2 / (p : ℝ) ^ 2) by intro p; ring] at hLow
    rw [sum_neg_distrib] at hLow
    linarith
  · apply (Real.log_le_log_iff hProd (mul_pos (pow_pos hσ _) (Real.exp_pos _))).mp
    rw [Real.log_mul (pow_ne_zero _ hσ.ne') (Real.exp_ne_zero _), Real.log_pow, Real.log_exp]
    rw [sum_add_distrib] at hHigh
    linarith

private abbrev Assignment (w : ℕ) := (p : primes w) → Fin p.val

private def residue {w : ℕ} (p : primes w) (n : ℕ) : Fin p.val :=
  ⟨n % p.val, Nat.mod_lt n (mem_primes.mp p.prop).2.pos⟩

private def avoidThrough {w : ℕ} (a : Assignment w) (B n : ℕ) : Prop :=
  ∀ p : primes w, p.val ≤ B → a p ≠ residue p n

private def avoidAbove {w : ℕ} (a : Assignment w) (B n : ℕ) : Prop :=
  ∀ p : primes w, B < p.val → a p ≠ residue p n

private instance {w : ℕ} (a : Assignment w) (B n : ℕ) : Decidable (avoidAbove a B n) :=
  inferInstanceAs (Decidable (∀ p : primes w, B < p.val → a p ≠ residue p n))

private instance {w : ℕ} (a : Assignment w) (B n : ℕ) : Decidable (avoidThrough a B n) :=
  inferInstanceAs (Decidable (∀ p : primes w, p.val ≤ B → a p ≠ residue p n))

private def conditioned (w h : ℕ) : Finset (Assignment w) :=
  Fintype.piFinset fun p ↦ univ.erase (residue p h)

private theorem mem_conditioned {w h : ℕ} {a : Assignment w} :
    a ∈ conditioned w h ↔ ∀ p, a p ≠ residue p h := by
  simp [conditioned, Fintype.mem_piFinset]

private theorem conditioned_nonempty (w h : ℕ) : (conditioned w h).Nonempty := by
  refine Fintype.piFinset_nonempty.mpr fun p ↦ ?_
  apply card_pos.mp
  rw [card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin]
  have := (mem_primes.mp p.prop).2.two_le
  omega

private def tailPrimes (w B : ℕ) : Finset ℕ := (primes w).filter (B < ·)

private theorem sigma_tail_ge {w B : ℕ} (hBw : B ≤ w) :
    sigma (tailPrimes w B) = euler B 1 / euler w 1 := by
  have he : (primes w).filter (¬ B < ·) = primes B := by
    ext p
    simp only [mem_filter, mem_primes, not_lt]
    exact ⟨fun h ↦ ⟨h.2, h.1.2⟩, fun h ↦ ⟨⟨h.1.trans hBw, h.2⟩, h.1⟩⟩
  have hprod := prod_filter_mul_prod_filter_not (primes w) (B < ·) (fun p ↦ (1 - (p : ℝ)⁻¹))
  change sigma (tailPrimes w B) * sigma ((primes w).filter (¬ B < ·)) = sigma (primes w) at hprod
  rw [he, sigma_primes, sigma_primes] at hprod
  exact (eq_div_iff (inv_ne_zero (euler_pos B (by norm_num)).ne')).mpr hprod |>.trans (by
    rw [div_inv_eq_mul, inv_mul_eq_div])

private theorem mean_condition_indicator (w h : ℕ) (f : Assignment w → ℝ) :
    mean univ (fun a ↦ if a ∈ conditioned w h then f a else 0) =
      sigma (primes w) * mean (conditioned w h) f := by
  classical
  have hcard :
      ((conditioned w h).card : ℝ) / (Fintype.card (Assignment w)) = sigma (primes w) := by
    unfold conditioned sigma
    rw [Fintype.card_piFinset, Fintype.card_pi]
    simp only [card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin, Nat.cast_prod, ← prod_div_distrib]
    have he (p : primes w) : ((p.val - 1 : ℕ) : ℝ) / (p.val : ℝ) = 1 - (p.val : ℝ)⁻¹ := by
      rw [Nat.cast_sub (mem_primes.mp p.prop).2.one_le, Nat.cast_one, sub_div,
        div_self (Nat.cast_ne_zero.mpr (mem_primes.mp p.prop).2.ne_zero), one_div]
    simp_rw [he]
    exact Finset.prod_attach (primes w) (fun p ↦ 1 - (p : ℝ)⁻¹)
  rw [← hcard, mean, mean, ← sum_filter, filter_mem_eq_inter, univ_inter, card_univ]
  have hn : ((conditioned w h).card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (conditioned_nonempty w h).card_ne_zero
  field_simp [hn]

private theorem conditional_tail_survival (w B h : ℕ) (U : Finset ℕ) (hh : h ∈ U) :
    mean (conditioned w h) (fun a ↦ if ∀ n ∈ U, avoidAbove a B n then (1 : ℝ) else 0) =
      ∏ p : tailPrimes w B, (1 - ((U.image (· % p.val)).card - 1 : ℝ) / ((p.val : ℝ) - 1)) := by
  classical
  let S (p : primes w) : Finset (Fin p.val) := univ.erase (residue p h)
  let T (p : primes w) : Finset (Fin p.val) := if B < p.val then U.image (residue p) else ∅
  have hrewrite (a : Assignment w) :
      (∀ n ∈ U, avoidAbove a B n) ↔ ∀ p, a p ∉ T p := by
    unfold avoidAbove T
    constructor
    · intro H p
      by_cases hp : B < p.val
      · rw [if_pos hp]
        intro hm
        obtain ⟨n, hn, he⟩ := mem_image.mp hm
        exact (H n hn p hp) he.symm
      · simp [hp]
    · intro H n hn p hp he
      have hh' := H p
      rw [if_pos hp] at hh'
      exact hh' (mem_image.mpr ⟨n, hn, he.symm⟩)
  calc
    _ = ∏ p : primes w, (((S p \ T p).card : ℝ) / ((S p).card : ℝ)) := by
      simp_rw [hrewrite]
      exact mean_pi_avoid S T
    _ = ∏ p : primes w, if B < p.val then
        1 - ((U.image (· % p.val)).card - 1 : ℝ) / ((p.val : ℝ) - 1) else 1 := by
      refine prod_congr rfl fun p _ ↦ ?_
      by_cases hp : B < p.val
      · simp only [if_pos hp, T]
        have hmem := mem_image_of_mem (residue p) hh
        have hset : S p \ U.image (residue p) = (univ : Finset (Fin p.val)) \ U.image (residue p) := by
          ext z
          simp only [S, Finset.mem_sdiff, mem_erase, mem_univ, and_true, true_and]
          exact ⟨And.right, fun hz ↦ ⟨fun he ↦ hz (he.symm ▸ hmem), hz⟩⟩
        have hcardle : (U.image (residue p)).card ≤ p.val :=
          (card_le_card (show U.image (residue p) ⊆ univ by simp)).trans_eq (by simp)
        have hc : (U.image (residue p)).card = (U.image (· % p.val)).card := by
          have he : U.image (· % p.val) = (U.image (residue p)).image Fin.val := by
            rw [image_image]
            rfl
          rw [he, card_image_of_injective _ Fin.val_injective]
        rw [hset, card_sdiff_of_subset (subset_univ _), card_univ, Fintype.card_fin,
          Nat.cast_sub hcardle, hc]
        have hcast : ((S p).card : ℝ) = (p.val : ℝ) - 1 := by
          simp [S, card_erase_of_mem (mem_univ _), Nat.cast_sub (mem_primes.mp p.prop).2.one_le]
        rw [hcast]
        have hp1 : (1 : ℝ) < p.val := by exact_mod_cast (mem_primes.mp p.prop).2.one_lt
        field_simp [show (p.val : ℝ) - 1 ≠ 0 by linarith]
        ring
      · rw [if_neg hp, show T p = ∅ by simp [T, hp], sdiff_empty]
        exact div_self (Nat.cast_ne_zero.mpr ((Fintype.piFinset_nonempty.mp (conditioned_nonempty w h)) p).card_ne_zero)
    _ = _ := by
      let f (p : ℕ) := 1 - ((U.image (· % p)).card - 1 : ℝ) / ((p : ℝ) - 1)
      change (∏ p : primes w, if B < p.val then f p.val else 1) = ∏ p : tailPrimes w B, f p.val
      calc
        _ = ∏ p ∈ primes w, if B < p then f p else 1 :=
          Finset.prod_attach (primes w) (fun p ↦ if B < p then f p else 1)
        _ = ∏ p ∈ tailPrimes w B, f p := (prod_filter (B < ·) f).symm
        _ = _ := (Finset.prod_attach (tailPrimes w B) f).symm

/- Residue classes of offsets and bounds on their overlaps. -/
private def cell (S : Finset ℕ) (q r : ℕ) : Finset ℕ := S.filter (· % q = r)

private def distance (a b : ℕ) : ℕ := ((a : ℤ) - (b : ℤ)).natAbs

private theorem dvd_distance_iff {a b p : ℕ} : p ∣ distance a b ↔ a % p = b % p := by
  change _ ↔ a ≡ b [MOD p]
  rw [Nat.modEq_iff_dvd, distance, ← Int.natCast_dvd_natCast, Int.dvd_natAbs]
  rw [← neg_sub (a : ℤ) (b : ℤ), Int.dvd_neg]

private theorem distance_mem {a b y : ℕ} (ha : a ∈ Icc 1 y) (hb : b ∈ Icc 1 y) (hab : a ≠ b) :
    distance a b ∈ Icc 1 y := by
  rw [mem_Icc] at ha hb ⊢
  unfold distance
  omega

private theorem cell_card {S : Finset ℕ} {q r H y : ℕ} (hS : S ⊆ Icc 1 y) (h : y < H * q) :
    (cell S q r).card ≤ H := by
  have hq : 0 < q := by
    by_contra! hq
    simp [show q = 0 by omega] at h
  rw [← card_range H]
  refine card_le_card_of_injOn (fun n ↦ n / q) (fun n hn ↦ mem_range.mpr ?_) ?_
  · exact (Nat.div_lt_iff_lt_mul hq).mpr ((mem_Icc.mp (hS (mem_filter.mp hn).1)).2.trans_lt h)
  · intro a ha b hb hab
    have hmod : a % q = b % q := (mem_filter.mp ha).2.trans (mem_filter.mp hb).2.symm
    change a / q = b / q at hab
    exact (Nat.div_add_mod a q).symm.trans (by rw [hab, hmod]; exact Nat.div_add_mod b q)

private theorem cell_difference {a b q H y : ℕ} (ha : a ≤ y) (hb : b ≤ y)
    (hq : 0 < q) (h : y < H * q) (hmod : a % q = b % q) :
    ∃ i ∈ Icc (-(H : ℤ)) (H : ℤ), (a : ℤ) - (b : ℤ) = i * (q : ℤ) := by
  have haH := (Nat.div_lt_iff_lt_mul hq).mpr (ha.trans_lt h)
  have hbH := (Nat.div_lt_iff_lt_mul hq).mpr (hb.trans_lt h)
  have haI : ((a / q : ℕ) : ℤ) < H := by exact_mod_cast haH
  have hbI : ((b / q : ℕ) : ℤ) < H := by exact_mod_cast hbH
  have han : (0 : ℤ) ≤ ((a / q : ℕ) : ℤ) := Int.natCast_nonneg _
  have hbn : (0 : ℤ) ≤ ((b / q : ℕ) : ℤ) := Int.natCast_nonneg _
  refine ⟨((a / q : ℕ) : ℤ) - ((b / q : ℕ) : ℤ), mem_Icc.mpr ⟨by linarith, by linarith⟩, ?_⟩
  have hA : (q : ℤ) * (↑(a / q) : ℤ) + ↑(a % q) = (a : ℤ) := by exact_mod_cast Nat.div_add_mod a q
  have hB : (q : ℤ) * (↑(b / q) : ℤ) + ↑(b % q) = (b : ℤ) := by exact_mod_cast Nat.div_add_mod b q
  rw [hmod] at hA
  linear_combination -hA + hB

private theorem cell_mod_inj {S : Finset ℕ} {q r H y p : ℕ} (hS : S ⊆ Icc 1 y)
    (hq : q.Prime) (hp : p.Prime) (hpq : p < q) (hHq : y < H * q) (hHp : H < p) :
    Set.InjOn (· % p) (cell S q r : Set ℕ) := by
  intro a ha b hb hab
  have ha' := (mem_Icc.mp (hS (mem_filter.mp ha).1)).2
  have hb' := (mem_Icc.mp (hS (mem_filter.mp hb).1)).2
  obtain ⟨i, hi, he⟩ := cell_difference ha' hb' hq.pos hHq
    ((mem_filter.mp ha).2.trans (mem_filter.mp hb).2.symm)
  have hdiv := dvd_distance_iff.mpr hab
  rw [distance, he, Int.natAbs_mul, Int.natAbs_natCast] at hdiv
  have hiDiv : p ∣ i.natAbs := (hp.dvd_mul.mp hdiv).resolve_right
    (fun hd ↦ hpq.ne ((Nat.prime_dvd_prime_iff_eq hp hq).mp hd))
  by_contra! hn
  have hi0 : 0 < i.natAbs := by
    by_contra! h
    have hiZ : i = 0 := by omega
    simp [hiZ] at he
    exact hn (by omega)
  have hp_le := Nat.le_of_dvd hi0 hiDiv
  rw [mem_Icc] at hi
  omega

private theorem two_cells_inter_subset {S : Finset ℕ} {h y q q' : ℕ}
    (hS : S ⊆ Icc 1 y) (hh : h ∈ Icc 1 y) (hq : q.Prime) (hq' : q'.Prime)
    (hne : q ≠ q') (hProd : y < q * q') :
    cell S q (h % q) ∩ cell S q' (h % q') ⊆ {h} := by
  intro a ha
  rw [mem_singleton]
  obtain ⟨ha, ha'⟩ := mem_inter.mp ha
  have hd1 := dvd_distance_iff.mpr (mem_filter.mp ha).2
  have hd2 := dvd_distance_iff.mpr (mem_filter.mp ha').2
  by_contra hneq
  have hD := mem_Icc.mp (distance_mem (hS (mem_filter.mp ha).1) hh hneq)
  have hDiv := ((Nat.coprime_primes hq hq').mpr hne).mul_dvd_of_dvd_of_dvd hd1 hd2
  exact (not_le_of_gt hProd) ((Nat.le_of_dvd hD.1 hDiv).trans hD.2)

private theorem image_collision_le {A B : Finset ℕ} {p : ℕ}
    (ha : Set.InjOn (· % p) (A : Set ℕ)) (hb : Set.InjOn (· % p) (B : Set ℕ))
    (hdisj : Disjoint A B) :
    (A ∪ B).card - ((A ∪ B).image (· % p)).card ≤
      ((A ×ˢ B).filter (fun v ↦ p ∣ distance v.1 v.2)).card := by
  classical
  rw [card_union_of_disjoint hdisj, image_union]
  have he := card_union_add_card_inter (A.image (· % p)) (B.image (· % p))
  rw [card_image_of_injOn ha, card_image_of_injOn hb] at he
  have his : A.card + B.card - (A.image (· % p) ∪ B.image (· % p)).card =
    (A.image (· % p) ∩ B.image (· % p)).card := by omega
  rw [his]
  let T := (A ×ˢ B).filter (fun v ↦ p ∣ distance v.1 v.2)
  have hincl : A.image (· % p) ∩ B.image (· % p) ⊆ T.image (fun v ↦ v.1 % p) := by
    intro r hr
    obtain ⟨⟨a, ha, he⟩, ⟨b, hb, hb'⟩⟩ := mem_inter.mp hr |>.imp mem_image.mp mem_image.mp
    exact mem_image.mpr ⟨(a, b), mem_filter.mpr ⟨mem_product.mpr ⟨ha, hb⟩,
      dvd_distance_iff.mpr (he.trans hb'.symm)⟩, he⟩
  exact (card_le_card hincl).trans card_image_le

private theorem collision_sum_le {A B P : Finset ℕ}
    (ha : ∀ p ∈ P, Set.InjOn (· % p) (A : Set ℕ))
    (hb : ∀ p ∈ P, Set.InjOn (· % p) (B : Set ℕ))
    (hdisj : Disjoint A B) :
    (∑ p ∈ P, ((↑(A ∪ B).card : ℝ) - ↑((A ∪ B).image (· % p)).card) / (p : ℝ)) ≤
      ∑ a ∈ A, ∑ b ∈ B, overlapSum P (distance a b) := by
  classical
  calc
    _ ≤ ∑ p ∈ P, ((↑(((A ×ˢ B).filter (fun v ↦ p ∣ distance v.1 v.2)).card) : ℝ) / p) := by
      apply sum_le_sum
      intro p hp
      have h := image_collision_le (ha p hp) (hb p hp) hdisj
      rw [← Nat.cast_sub card_image_le]
      exact div_le_div_of_nonneg_right (Nat.cast_le.mpr h) (Nat.cast_nonneg _)
    _ = _ := by
      simp only [card_eq_sum_ones, Nat.cast_sum, Nat.cast_one, Finset.sum_div]
      simp_rw [sum_filter, overlapSum, sum_product, one_div]
      rw [sum_comm]
      refine sum_congr rfl fun a _ ↦ ?_
      rw [sum_comm]
      refine sum_congr rfl fun b _ ↦ ?_
      exact (sum_filter ..).symm

private def signed (T : Finset ℕ) : Finset ℤ :=
  T.image Int.ofNat ∪ T.image (fun n : ℕ ↦ -(n : ℤ))

private theorem signed_card (T : Finset ℕ) : (signed T).card ≤ 2 * T.card := by
  calc
    _ ≤ (T.image Int.ofNat).card + (T.image (fun n : ℕ ↦ -(n : ℤ))).card := card_union_le _ _
    _ ≤ T.card + T.card := Nat.add_le_add card_image_le card_image_le
    _ = _ := by omega

private theorem mem_signed_of_natAbs {T : Finset ℕ} {d : ℤ} (hd : d.natAbs ∈ T) :
    d ∈ signed T := by
  have h : d = (d.natAbs : ℤ) ∨ d = -(d.natAbs : ℤ) := by omega
  rcases h with he | he
  · exact mem_union.mpr (Or.inl (mem_image.mpr ⟨d.natAbs, hd, he.symm⟩))
  · exact mem_union.mpr (Or.inr (mem_image.mpr ⟨d.natAbs, hd, he.symm⟩))

private noncomputable def badPrimeChoices (S Q D : Finset ℕ) (q h : ℕ) : Finset ℕ :=
  Q.filter fun q' ↦ q' = q ∨
    ∃ a ∈ cell S q (h % q), ∃ b ∈ (cell S q' (h % q')).erase h, distance a b ∈ D

private noncomputable def badResidueChoices (S D : Finset ℕ) (q h : ℕ) : Finset ℕ :=
  (range q).filter fun r ↦ r = h % q ∨
    ∃ a ∈ cell S q (h % q), ∃ b ∈ cell S q r, distance a b ∈ D

private theorem badResidueChoices_card {S D : Finset ℕ} {q h y H : ℕ}
    (hS : S ⊆ Icc 1 y) (hHq : y < H * q) :
    (badResidueChoices S D q h).card ≤ 1 + 2 * H * D.card := by
  classical
  let B := (badResidueChoices S D q h).erase (h % q)
  let T := cell S q (h % q) ×ˢ signed D
  have hs : ∀ r ∈ B, ∃ (a : ℕ) (d : ℤ), (a, d) ∈ T ∧ Int.toNat ((a : ℤ) - d) % q = r := by
    intro r hr
    have h' := (mem_filter.mp (mem_erase.mp hr).2).2.resolve_left (mem_erase.mp hr).1
    obtain ⟨a, ha, b, hb, hd⟩ := h'
    refine ⟨a, (a : ℤ) - b, mem_product.mpr ⟨ha, mem_signed_of_natAbs hd⟩, ?_⟩
    have he : Int.toNat ((a : ℤ) - ((a : ℤ) - b)) = b := by omega
    rw [he]
    exact (mem_filter.mp hb).2
  have hsub : B ⊆ T.image (fun t ↦ Int.toNat ((t.1 : ℤ) - t.2) % q) := by
    intro r hr
    obtain ⟨a, d, ht, hr'⟩ := hs r hr
    exact mem_image.mpr ⟨(a, d), ht, hr'⟩
  have htag : B.card ≤ H * (2 * D.card) :=
    ((card_le_card hsub).trans card_image_le).trans
      (by rw [card_product]; exact Nat.mul_le_mul (cell_card hS hHq) (signed_card D))
  have hb : (badResidueChoices S D q h).card ≤ B.card + 1 := by
    by_cases hm : h % q ∈ badResidueChoices S D q h
    · rw [show B.card = (badResidueChoices S D q h).card - 1 from card_erase_of_mem hm]
      have := card_pos.mpr ⟨_, hm⟩
      omega
    · simp only [B, erase_eq_of_notMem hm, Nat.le_add_right]
  exact hb.trans (by simpa [Nat.mul_left_comm, Nat.mul_comm, Nat.mul_assoc, Nat.add_comm] using
    Nat.add_le_add_right htag 1)

private theorem badPrimeChoices_card {S Q D : Finset ℕ} {q h y H : ℕ}
    (hS : S ⊆ Icc 1 y) (hh : h ≤ y) (hq : 0 < q) (hHq : y < H * q)
    (hQ : ∀ q' ∈ Q, 0 < q' ∧ y < H * q') :
    (badPrimeChoices S Q D q h).card ≤ 1 + 2 * (2 * H + 1) ^ 2 * D.card := by
  classical
  let B := (badPrimeChoices S Q D q h).erase q
  let I := Icc (-(H : ℤ)) (H : ℤ)
  let T := I ×ˢ I ×ˢ signed D
  have hc : ∀ q' ∈ B, ∃ t ∈ T, t.2.1 ≠ 0 ∧ t.2.2 = t.1 * (q : ℤ) - t.2.1 * (q' : ℤ) := by
    intro q' hq'
    have hq'' := mem_filter.mp (mem_erase.mp hq').2
    obtain ⟨a, ha, b, hb, hdist⟩ := hq''.2.resolve_left (mem_erase.mp hq').1
    obtain ⟨i, hi, hi'⟩ := cell_difference (mem_Icc.mp (hS (mem_filter.mp ha).1)).2 hh hq hHq
      (mem_filter.mp ha).2
    obtain ⟨j, hj, hj'⟩ := cell_difference (mem_Icc.mp (hS (mem_filter.mp (mem_erase.mp hb).2).1)).2
      hh (hQ q' hq''.1).1 (hQ q' hq''.1).2 (mem_filter.mp (mem_erase.mp hb).2).2
    refine ⟨(i, j, (a : ℤ) - b), mem_product.mpr ⟨hi, mem_product.mpr ⟨hj, mem_signed_of_natAbs hdist⟩⟩, ?_, ?_⟩
    · change j ≠ 0
      intro hj0
      rw [hj0, zero_mul, sub_eq_zero] at hj'
      exact (mem_erase.mp hb).1 (by omega)
    · linear_combination hi' - hj'
  choose t ht htnz hteq using hc
  let g (q' : ℕ) := if hq' : q' ∈ B then t q' hq' else (0, 0, 0)
  have hB : B.card ≤ T.card := by
    refine card_le_card_of_injOn g (fun q' h ↦ ?_) ?_
    · change q' ∈ B at h
      change g q' ∈ T
      unfold g
      rw [dif_pos h]
      exact ht q' h
    · intro a ha b hb hab
      change a ∈ B at ha
      change b ∈ B at hb
      have ha' := hteq a ha
      have hb' := hteq b hb
      change g a = g b at hab
      unfold g at hab
      rw [dif_pos ha, dif_pos hb] at hab
      rw [← hab] at hb'
      have hmul : (t a ha).2.1 * (a : ℤ) = (t a ha).2.1 * (b : ℤ) := by linarith only [ha', hb']
      exact Int.ofNat_inj.mp (mul_left_cancel₀ (htnz a ha) hmul)
  have hI : I.card = 2 * H + 1 := by
    dsimp [I]
    rw [Int.card_Icc]
    omega
  have hT : T.card ≤ 2 * (2 * H + 1) ^ 2 * D.card := by
    simp only [T, card_product, hI]
    calc
      _ ≤ (2 * H + 1) * ((2 * H + 1) * (2 * D.card)) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (signed_card D))
      _ = _ := by ring
  have hb : (badPrimeChoices S Q D q h).card ≤ B.card + 1 := by
    by_cases hm : q ∈ badPrimeChoices S Q D q h
    · rw [show B.card = (badPrimeChoices S Q D q h).card - 1 from card_erase_of_mem hm]
      have := card_pos.mpr ⟨_, hm⟩
      omega
    · simp only [B, erase_eq_of_notMem hm, Nat.le_add_right]
  omega

private def survives {w : ℕ} (B : ℕ) (U : Finset ℕ) (a : Assignment w) : Prop :=
  ∀ n ∈ U, avoidAbove a B n

private instance {w : ℕ} (B : ℕ) (U : Finset ℕ) (a : Assignment w) :
    Decidable (survives B U a) :=
  inferInstanceAs (Decidable (∀ n ∈ U, avoidAbove a B n))

private noncomputable def weight {w : ℕ} (B : ℕ) (U : Finset ℕ) (a : Assignment w) : ℝ :=
  if survives B U a then (sigma (tailPrimes w B))⁻¹ ^ U.card else 0

private theorem tail_prime {w B p : ℕ} (hp : p ∈ tailPrimes w B) :
    B < p ∧ p ≤ w ∧ p.Prime :=
  ⟨(mem_filter.mp hp).2, mem_primes.mp (mem_filter.mp hp).1⟩

private theorem tail_sigma_pos (w B : ℕ) : 0 < sigma (tailPrimes w B) :=
  sigma_pos fun _ h ↦ (tail_prime h).2.2.one_lt

private theorem tail_sigma_le_one (w B : ℕ) : sigma (tailPrimes w B) ≤ 1 :=
  sigma_le_one fun _ h ↦ (tail_prime h).2.2.one_lt

private theorem weight_nonneg {w B : ℕ} (U : Finset ℕ) (a : Assignment w) :
    0 ≤ weight B U a := by
  unfold weight
  split_ifs
  · exact pow_nonneg (inv_nonneg.mpr (tail_sigma_pos w B).le) _
  · exact le_rfl

private theorem weight_le_pow {w B H : ℕ} {U : Finset ℕ} (hU : U.card ≤ H) (a : Assignment w) :
    weight B U a ≤ (sigma (tailPrimes w B))⁻¹ ^ H := by
  unfold weight
  have hσ1 : 1 ≤ (sigma (tailPrimes w B))⁻¹ :=
    (one_le_inv₀ (tail_sigma_pos w B)).mpr (tail_sigma_le_one w B)
  split_ifs
  · exact pow_le_pow_right₀ hσ1 hU
  · exact pow_nonneg (zero_le_one.trans hσ1) _

private theorem pow_mul_inv_pow {a : ℝ} (ha : a ≠ 0) {d n : ℕ} (hd : d ≤ n) :
    a ^ d * a⁻¹ ^ n = a⁻¹ ^ (n - d) := by
  rw [show n = d + (n - d) by omega, pow_add, ← mul_assoc, ← mul_pow, mul_inv_cancel₀ ha, one_pow,
    one_mul, Nat.add_sub_cancel_left]

private theorem norm_single {w B h : ℕ} {U : Finset ℕ} (hh : h ∈ U) (a : Assignment w) :
    sigma (tailPrimes w B) * weight B U a =
      if survives B U a then (sigma (tailPrimes w B))⁻¹ ^ (U.card - 1) else 0 := by
  unfold weight
  split_ifs
  · have hc : 1 ≤ U.card := card_pos.mpr ⟨h, hh⟩
    simpa only [pow_one] using pow_mul_inv_pow (tail_sigma_pos w B).ne' hc
  · exact mul_zero _

private theorem card_union_erase {A B : Finset ℕ} {h : ℕ} (hA : h ∈ A) (hAB : A ∩ B ⊆ {h}) :
    A ∪ B = A ∪ B.erase h ∧ Disjoint A (B.erase h) := by
  constructor
  · ext n
    simp only [mem_union, mem_erase]
    by_cases hn : n = h
    · subst n
      simp [hA]
    · simp [hn]
  · refine disjoint_left.mpr fun p hpA hpB ↦ ?_
    have h := hAB (mem_inter.mpr ⟨hpA, (mem_erase.mp hpB).2⟩)
    exact (mem_erase.mp hpB).1 (mem_singleton.mp h)

private theorem norm_pair {w B h : ℕ} {A C : Finset ℕ} (hh : h ∈ A) (hac : A ∩ C ⊆ {h})
    (a : Assignment w) :
    (sigma (tailPrimes w B)) ^ (if h ∈ C then 2 else 1 : ℕ) * (weight B A a * weight B C a) =
      if survives B (A ∪ C) a then (sigma (tailPrimes w B))⁻¹ ^ ((A ∪ C).card - 1) else 0 := by
  classical
  have he : survives B (A ∪ C) a ↔ survives B A a ∧ survives B C a := by
    unfold survives
    simp only [mem_union, or_imp, forall_and]
  have hcardA := card_pos.mpr ⟨h, hh⟩
  have hu := card_union_erase hh hac
  have hc : (A ∪ C).card = A.card + (C.erase h).card := by rw [hu.1, card_union_of_disjoint hu.2]
  let t := if h ∈ C then 2 else 1
  have ht : t ≤ A.card + C.card ∧ A.card + C.card - t = (A ∪ C).card - 1 := by
    by_cases hm : h ∈ C
    · have hpos := card_pos.mpr ⟨h, hm⟩
      simp only [t, if_pos hm]
      rw [hc, card_erase_of_mem hm]
      omega
    · simp only [t, if_neg hm]
      rw [hc, erase_eq_of_notMem hm]
      omega
  change (sigma (tailPrimes w B)) ^ t * _ = _
  by_cases hA : survives B A a <;> by_cases hC : survives B C a
  · have hU := he.mpr ⟨hA, hC⟩
    simp only [weight, if_pos hA, if_pos hC, if_pos hU]
    rw [← pow_add, pow_mul_inv_pow (tail_sigma_pos w B).ne' ht.1, ht.2]
  · have hU := mt he.mp (fun hu ↦ hC hu.2)
    simp [weight, hA, hC, hU]
  · have hU := mt he.mp (fun hu ↦ hA hu.1)
    simp [weight, hA, hC, hU]
  · have hU := mt he.mp (fun hu ↦ hA hu.1)
    simp [weight, hA, hC, hU]

private theorem conditional_normalized_weight {w H h : ℕ} {U : Finset ℕ} (hH : 2 ≤ H)
    (hh : h ∈ U) (hU : U.card ≤ 2 * H) :
    let B := H ^ 10
    let P := tailPrimes w B
    let D := U.card - 1
    let f := fun a : Assignment w ↦ if survives B U a then (sigma P)⁻¹ ^ D else 0
    Real.exp (-(1 / (H : ℝ))) ≤ mean (conditioned w h) f ∧
      mean (conditioned w h) f ≤
        Real.exp (1 / (H : ℝ) + ∑ p ∈ P, ((U.card : ℝ) - ↑(U.image (· % p)).card) / p) := by
  dsimp only
  let B := H ^ 10
  let P := tailPrimes w B
  let D := U.card - 1
  let v (p : ℕ) := (U.image (· % p)).card - 1
  let σ := sigma P
  have hσ : 0 < σ := tail_sigma_pos w B
  have hv : ∀ p ∈ P, v p ≤ D := fun _p _ ↦ Nat.sub_le_sub_right card_image_le _
  have hPosB : 0 < B := pow_pos (by omega) _
  have hHB : 4 * H + 1 ≤ B := by
    have hH4 : 2 ^ 9 ≤ H ^ 9 := Nat.pow_le_pow_left hH _
    rw [show B = H ^ 9 * H by rfl]
    have hh0 := Nat.mul_le_mul_right H hH4
    norm_num at hh0
    omega
  have hbound := survive_product_bounds (P := P) (D := D) hPosB (fun p hp ↦ by
    obtain ⟨hBp, _, hpr⟩ := tail_prime hp
    exact ⟨hBp, hpr.two_le, by dsimp [D]; omega⟩) v hv
  have hsurv := conditional_tail_survival w B h U hh
  have hs (p : ℕ) : (((U.image (· % p)).card - 1 : ℕ) : ℝ) =
      ((U.image (· % p)).card : ℝ) - 1 :=
    by
      have hc : 1 ≤ (U.image (· % p)).card :=
        card_pos.mpr ⟨_, mem_image_of_mem (· % p) hh⟩
      simpa only [Nat.cast_one] using (Nat.cast_sub hc : (_ : ℝ) = _)
  have hov : ∑ p ∈ P, ((D : ℝ) - (v p : ℝ)) / p =
      ∑ p ∈ P, ((U.card : ℝ) - ((U.image (· % p)).card : ℝ)) / p := by
    refine sum_congr rfl fun p _ ↦ ?_
    simp only [v, hs, D, Nat.cast_sub (card_pos.mpr ⟨h, hh⟩), Nat.cast_one]
    ring
  have hsurv' : mean (conditioned w h) (fun a ↦ if survives B U a then 1 else 0) =
    ∏ p ∈ P, (1 - (v p : ℝ) / ((p : ℝ) - 1)) := by
    simp_rw [v, hs]
    let f₀ (p : ℕ) := 1 - (((U.image (· % p)).card : ℝ) - 1) / ((p : ℝ) - 1)
    exact hsurv.trans (Finset.prod_attach P f₀)
  have Hpos : (0 : ℝ) < H := by exact_mod_cast (show 0 < H by omega)
  have herror : 10 * ((D : ℝ) + 1) ^ 2 / (B : ℝ) ≤ 1 / (H : ℝ) := by
    have hDc : (D : ℝ) + 1 ≤ 3 * (H : ℝ) := by
      have hDn : D + 1 ≤ 3 * H := by dsimp [D]; omega
      exact_mod_cast hDn
    have hconst : (90 : ℝ) ≤ (H : ℝ) ^ 7 := by
      have h2 : (2 : ℝ) ≤ H := by exact_mod_cast hH
      exact (by norm_num : (90 : ℝ) ≤ 2 ^ 7).trans (pow_le_pow_left₀ (by norm_num) h2 _)
    have hpow := pow_le_pow_left₀ (by positivity : 0 ≤ (D : ℝ) + 1) hDc 2
    dsimp [B]
    rw [Nat.cast_pow, div_le_div_iff₀ (pow_pos Hpos _) Hpos]
    calc
      _ ≤ 90 * (H : ℝ) ^ 3 := by nlinarith [mul_le_mul_of_nonneg_right hpow Hpos.le]
      _ ≤ (H : ℝ) ^ 7 * (H : ℝ) ^ 3 := mul_le_mul_of_nonneg_right hconst (by positivity)
      _ = _ := by ring
  have hmean : mean (conditioned w h) (fun a ↦ if survives B U a then σ⁻¹ ^ D else 0) =
    σ⁻¹ ^ D * (∏ p ∈ P, (1 - (v p : ℝ) / ((p : ℝ) - 1))) := by
    rw [← hsurv', ← mean_mul]
    refine mean_congr fun a _ ↦ ?_
    split_ifs <;> simp
  rw [hmean]
  rw [hov] at hbound
  have hinv : σ⁻¹ ^ D * σ ^ D = 1 := by rw [← mul_pow, inv_mul_cancel₀ hσ.ne', one_pow]
  constructor
  · have hl := mul_le_mul_of_nonneg_left hbound.1 (pow_nonneg (inv_nonneg.mpr hσ.le) D)
    change σ⁻¹ ^ D * (σ ^ D * _) ≤ _ at hl
    rw [← mul_assoc, hinv, one_mul] at hl
    exact (Real.exp_le_exp.mpr (neg_le_neg herror)).trans hl
  · have hu := mul_le_mul_of_nonneg_left hbound.2 (pow_nonneg (inv_nonneg.mpr hσ.le) D)
    change _ ≤ σ⁻¹ ^ D * (σ ^ D * _) at hu
    rw [← mul_assoc, hinv, one_mul] at hu
    exact hu.trans (Real.exp_le_exp.mpr (add_le_add_left herror _))

/- Weights for covering offsets that already have one forced prime factor. -/
private structure Band (y w : ℕ) where
  height : ℕ
  pool : Finset ℕ
  upper : ℕ
  height_ge : 4 ≤ height
  tail_le : height ^ 10 ≤ w
  nonempty : pool.Nonempty
  properties (q : ℕ) (hq : q ∈ pool) :
    q.Prime ∧ w < q ∧ y < height * q ∧ y < q ^ 2 ∧ pool.card ≤ q ∧ q ≤ upper

private noncomputable def bandCost {y w : ℕ} (b : Band y w) : ℝ :=
  (b.pool.card : ℝ) / ((b.upper : ℝ) * sigma (tailPrimes w (b.height ^ 10)))

private theorem bandCost_pos {y w : ℕ} (b : Band y w) : 0 < bandCost b := by
  have hU : 0 < b.upper := by
    obtain ⟨q, hq⟩ := b.nonempty
    exact (b.properties q hq).1.pos.trans_le (b.properties q hq).2.2.2.2.2
  exact div_pos (Nat.cast_pos.mpr b.nonempty.card_pos) (mul_pos (Nat.cast_pos.mpr hU) (tail_sigma_pos _ _))

private def smallSurvivors {w : ℕ} (a : Assignment w) (y B : ℕ) : Finset ℕ :=
  (Icc 1 y).filter (avoidThrough a B)

private theorem smallSurvivors_sub {w y B : ℕ} (a : Assignment w) :
    smallSurvivors a y B ⊆ Icc 1 y :=
  filter_subset _ _

private theorem h_in_smallSurvivors {w y B h : ℕ} {a : Assignment w}
    (hh : h ∈ Icc 1 y) (ha : a ∈ conditioned w h) :
    h ∈ smallSurvivors a y B :=
  mem_filter.mpr ⟨hh, fun p _ ↦ mem_conditioned.mp ha p⟩

private theorem cells_disjoint_residue {S : Finset ℕ} {q r r' : ℕ} (hne : r ≠ r') :
    Disjoint (cell S q r) (cell S q r') :=
  disjoint_left.mpr (fun _ hx hy ↦ hne ((mem_filter.mp hx).2.symm.trans (mem_filter.mp hy).2))

private theorem weight_le_all {w B H : ℕ} {U : Finset ℕ} (hBw : B ≤ w) (hU : U.card ≤ H)
    (a : Assignment w) : weight B U a ≤ (euler w 1) ^ H := by
  have hs : 1 ≤ euler B 1 := by
    unfold euler
    have hp (p) (hp : p ∈ primes B) : 1 ≤ (1 - (p : ℝ) ^ (-1 : ℝ))⁻¹ := by
      have h := prime_rpow_lt_one (mem_primes.mp hp).2 (by norm_num : (0 : ℝ) < 1)
      exact (one_le_inv₀ (sub_pos.mpr h)).mpr (sub_le_self _ (by positivity))
    simpa only [prod_const_one] using
      (prod_le_prod (s := primes B) (f := fun _ ↦ (1 : ℝ)) (fun _ _ ↦ zero_le_one) hp)
  have hsig : (sigma (tailPrimes w B))⁻¹ ≤ euler w 1 := by
    rw [sigma_tail_ge hBw, inv_div]
    exact div_le_self (euler_pos w (by norm_num)).le hs
  exact (weight_le_pow hU a).trans (pow_le_pow_left₀ (inv_nonneg.mpr (tail_sigma_pos w B).le) hsig _)

private theorem band_weight_single {y w h : ℕ} (b : Band y w) {S : Finset ℕ}
    (hS : S ⊆ Icc 1 y) (hh : h ∈ S) {q : ℕ} (hq : q ∈ b.pool) :
    let H := b.height
    let B := H ^ 10
    let σ := sigma (tailPrimes w B)
    let V := cell S q (h % q)
    let f := fun a : Assignment w ↦ σ * weight B V a
    Real.exp (-(1 / (H : ℝ))) ≤ mean (conditioned w h) f ∧
    mean (conditioned w h) f ≤ Real.exp (1 / (H : ℝ)) := by
  dsimp only
  let H := b.height
  let B := H ^ 10
  let V := cell S q (h % q)
  have hV : h ∈ V := mem_filter.mpr ⟨hh, rfl⟩
  have hprop := b.properties q hq
  have hcard : V.card ≤ H := cell_card hS hprop.2.2.1
  have hm (p : ℕ) (hp : p ∈ tailPrimes w B) :
      (V.image (· % p)).card = V.card := by
    obtain ⟨hpB, hpw, hpr⟩ := tail_prime hp
    apply card_image_of_injOn
    refine cell_mod_inj hS hprop.1 hpr (hpw.trans_lt hprop.2.1) hprop.2.2.1 ?_
    have hHB : H ≤ B := by
      dsimp [B]
      exact (by simp : H = H ^ 1).le.trans (Nat.pow_le_pow_right (by have := b.height_ge; omega) (by decide))
    exact hHB.trans_lt hpB
  have hb := conditional_normalized_weight (w := w) (H := H) (by have := b.height_ge; omega)
    hV (hcard.trans (by omega))
  have he : (∑ p ∈ tailPrimes w B, ((V.card : ℝ) - ↑(V.image (· % p)).card) / p) = 0 := by
    apply sum_eq_zero
    intro p hp
    rw [hm p hp, sub_self, zero_div]
  obtain ⟨hl, hu⟩ := hb
  let F : Assignment w → ℝ := fun a ↦ sigma (tailPrimes w B) * weight B V a
  change Real.exp (-(1 / (H : ℝ))) ≤ mean (conditioned w h) F ∧
    mean (conditioned w h) F ≤ Real.exp (1 / (H : ℝ))
  have hf := mean_congr (s := conditioned w h) (fun a _ ↦ norm_single (B := B) hV a)
  change mean (conditioned w h) F = _ at hf
  rw [hf]
  rw [he, add_zero] at hu
  exact ⟨hl, hu⟩

private theorem band_weight_pair {y w h : ℕ} (b : Band y w) {S : Finset ℕ}
    (hS : S ⊆ Icc 1 y) (hh : h ∈ S) {q q' r : ℕ} (hq : q ∈ b.pool) (hq' : q' ∈ b.pool)
    (hac : cell S q (h % q) ∩ cell S q' r ⊆ {h})
    (hGood : ∀ a ∈ cell S q (h % q), ∀ a' ∈ (cell S q' r).erase h,
      distance a a' ∉ badDiffs (tailPrimes w (b.height ^ 10)) b.height y) :
    let H := b.height
    let B := H ^ 10
    let σ := sigma (tailPrimes w B)
    let V := cell S q (h % q)
    let V' := cell S q' r
    let f := fun a : Assignment w ↦ σ ^ (if h ∈ V' then 2 else 1 : ℕ) *
      (weight B V a * weight B V' a)
    mean (conditioned w h) f ≤ Real.exp (2 / (H : ℝ)) := by
  dsimp only
  let H := b.height
  let B := H ^ 10
  let V := cell S q (h % q)
  let V' := cell S q' r
  have hV : h ∈ V := mem_filter.mpr ⟨hh, rfl⟩
  have hcards : V.card ≤ H ∧ V'.card ≤ H :=
    ⟨cell_card hS (b.properties q hq).2.2.1, cell_card hS (b.properties q' hq').2.2.1⟩
  have hH : 2 ≤ H := by have := b.height_ge; omega
  have hUnion := card_union_erase hV hac
  have hU : (V ∪ V').card ≤ 2 * H :=
    (card_union_le _ _).trans (by omega)
  have hMod (p : ℕ) (hp : p ∈ tailPrimes w B) (q0 : ℕ) (hq0 : q0 ∈ b.pool) (r0 : ℕ) :
      Set.InjOn (· % p) (cell S q0 r0 : Set ℕ) := by
    obtain ⟨hpB, hpw, hpr⟩ := tail_prime hp
    have hprop := b.properties q0 hq0
    refine cell_mod_inj hS hprop.1 hpr (hpw.trans_lt hprop.2.1) hprop.2.2.1 ?_
    have hHB : H ≤ B := by
      dsimp [B]
      exact (by simp : H = H ^ 1).le.trans (Nat.pow_le_pow_right (by omega) (by decide))
    exact hHB.trans_lt hpB
  have hsum := collision_sum_le (A := V) (B := V'.erase h) (P := tailPrimes w B)
    (fun p hp ↦ hMod p hp q hq _)
    (fun p hp ↦ (hMod p hp q' hq' r).mono (erase_subset _ _))
    hUnion.2
  rw [← hUnion.1] at hsum
  have hHR : (0 : ℝ) < H := by exact_mod_cast (show 0 < H by omega)
  have hsum' : (∑ a ∈ V, ∑ a' ∈ V'.erase h, overlapSum (tailPrimes w B) (distance a a')) ≤
      1 / (H : ℝ) := by
    calc
      _ ≤ ∑ _a ∈ V, ∑ _a' ∈ V'.erase h, 1 / (H : ℝ) ^ 3 := by
        refine sum_le_sum fun a ha ↦ sum_le_sum fun a' ha' ↦ ?_
        by_contra! hBad
        have hne : a ≠ a' := fun he ↦ (disjoint_left.mp hUnion.2) ha (he ▸ ha')
        have hadd1 := hS (mem_filter.mp ha).1
        have hadd2 := hS (mem_filter.mp (mem_erase.mp ha').2).1
        exact hGood a ha a' ha' (mem_filter.mpr ⟨distance_mem hadd1 hadd2 hne, hBad⟩)
      _ = (V.card : ℝ) * ((V'.erase h).card : ℝ) * (1 / (H : ℝ) ^ 3) := by simp [mul_assoc]
      _ ≤ (H : ℝ) * (H : ℝ) * (1 / (H : ℝ) ^ 3) := by
        have hc1 : (V.card : ℝ) ≤ H := by exact_mod_cast hcards.1
        have hc2 : ((V'.erase h).card : ℝ) ≤ H := by exact_mod_cast (card_erase_le (s := V') (a := h)).trans hcards.2
        gcongr
      _ = _ := by field_simp
  have hup := (conditional_normalized_weight (w := w) (H := H) hH (mem_union_left _ hV) hU).2
  have he := hsum.trans hsum'
  change mean (conditioned w h) (fun a ↦ (sigma (tailPrimes w B)) ^ (if h ∈ V' then 2 else 1 : ℕ) *
    (weight B V a * weight B V' a)) ≤ _
  rw [mean_congr (s := conditioned w h) (fun a _ ↦ norm_pair (B := B) hV hac a)]
  apply hup.trans
  apply Real.exp_le_exp.mpr
  change (∑ p ∈ tailPrimes w B, ((↑(V ∪ V').card : ℝ) - ↑((V ∪ V').image (· % p)).card) / p) ≤ 1 / (H : ℝ) at he
  change 1 / (H : ℝ) + (∑ p ∈ tailPrimes w B, ((↑(V ∪ V').card : ℝ) - ↑((V ∪ V').image (· % p)).card) / p) ≤ 2 / (H : ℝ)
  calc
    _ ≤ (1 / (H : ℝ)) + 1 / (H : ℝ) := add_le_add_right he _
    _ = _ := by ring

private noncomputable def bandX {y w : ℕ} (b : Band y w) (S : Finset ℕ) (h : ℕ) (a : Assignment w) : ℝ :=
  let B := b.height ^ 10
  let σ := sigma (tailPrimes w B)
  mean b.pool (fun q ↦ σ * weight B (cell S q (h % q)) a)

private noncomputable def bandY {y w : ℕ} (b : Band y w) (S : Finset ℕ) (h : ℕ) (a : Assignment w) : ℝ :=
  let B := b.height ^ 10
  let σ := sigma (tailPrimes w B)
  mean b.pool (fun q ↦ σ * weight B (cell S q (h % q)) a *
    (1 + mean (range q) (fun r ↦ weight B (cell S q r) a)))

private noncomputable def badBound (H y : ℕ) : ℝ :=
  1 + 4 * (2 * (H : ℝ) + 1) ^ 2 * (y : ℝ) * Real.exp (-(H : ℝ) ^ 3)

private theorem mean_swap {α β : Type*} (s : Finset α) (t : Finset β) (f : α → β → ℝ) :
    mean s (fun a ↦ mean t (f a)) = mean t (fun b ↦ mean s (fun a ↦ f a b)) := by
  simp only [mean, ← Finset.sum_div, div_div]
  rw [sum_comm, mul_comm]

private theorem mean_mul_right {α : Type*} (s : Finset α) (f : α → ℝ) (c : ℝ) :
    mean s (fun x ↦ f x * c) = mean s f * c := by
  simpa only [mul_comm] using mean_mul s f c

private theorem mean_sq {α : Type*} (s : Finset α) (f : α → ℝ) :
    mean s f ^ 2 = mean s (fun a ↦ mean s (fun b ↦ f a * f b)) := by
  rw [pow_two]
  simp_rw [mean_mul, mean_mul_right]

private theorem const_le_mean {α : Type*} {s : Finset α} (hs : s.Nonempty) {f : α → ℝ} {c : ℝ}
    (h : ∀ a ∈ s, c ≤ f a) : c ≤ mean s f := by
  rw [← mean_const hs c]
  exact mean_le h

private theorem mean_add_bad {α : Type*} [DecidableEq α] {s T : Finset α} (hs : s.Nonempty)
    (hT : T ⊆ s) (c d τ : ℝ) (hb : d * T.card ≤ τ * s.card) :
    mean s (fun a ↦ c + if a ∈ T then d else 0) ≤ c + τ := by
  rw [mean_add, mean_const hs c, add_le_add_iff_left, mean, ← sum_filter]
  have he : s.filter (· ∈ T) = T := by
    ext a
    rw [mem_filter]
    exact ⟨And.right, fun ha ↦ ⟨hT ha, ha⟩⟩
  rw [he, sum_const, nsmul_eq_mul]
  exact (div_le_iff₀ (Nat.cast_pos.mpr hs.card_pos)).mpr (mul_comm d (T.card : ℝ) ▸ hb)

private theorem band_moments_fixed {y w h : ℕ} (b : Band y w) {S : Finset ℕ}
    (hS : S ⊆ Icc 1 y) (hh : h ∈ S) {τ : ℝ} (hτ : τ ≤ 1)
    (hErr : (euler w 1) ^ (2 * b.height) * badBound b.height y ≤ τ * b.pool.card) :
    mean (conditioned w h) (fun a ↦ (bandX b S h a - 1) ^ 2) ≤ 6 / (b.height : ℝ) + τ ∧
    mean (conditioned w h) (fun a ↦ bandY b S h a) ≤ 5 := by
  classical
  let H := b.height
  let B := H ^ 10
  let P := tailPrimes w B
  let σ := sigma P
  let C := conditioned w h
  let D := badDiffs P H y
  let K := (euler w 1) ^ (2 * H)
  let W (q r : ℕ) (a : Assignment w) := weight B (cell S q r) a
  let X (q : ℕ) (a : Assignment w) := σ * W q (h % q) a
  have hH : 4 ≤ H := b.height_ge
  have hR : (4 : ℝ) ≤ H := by exact_mod_cast hH
  have hC : C.Nonempty := conditioned_nonempty w h
  have hσ : 0 ≤ σ := (tail_sigma_pos w B).le
  have hσ1 : σ ≤ 1 := tail_sigma_le_one w B
  have hD := badDiffs_card (P := P) (H := H) (by omega)
    (fun p hp ↦ ⟨(tail_prime hp).1, (tail_prime hp).2.2⟩) y
  have hD0 : 0 ≤ (D.card : ℝ) := Nat.cast_nonneg _
  have hK : 0 ≤ K := pow_nonneg (euler_pos _ (by norm_num)).le _
  have hτ0 : 0 ≤ τ := by
    have hf : 0 ≤ badBound H y := by unfold badBound; positivity
    exact nonneg_of_mul_nonneg_left ((mul_nonneg hK hf).trans hErr)
      (Nat.cast_pos.mpr b.nonempty.card_pos)
  have hW (q r : ℕ) (hq : q ∈ b.pool) (a : Assignment w) :
      0 ≤ W q r a ∧ W q r a ≤ (euler w 1) ^ H :=
    ⟨weight_nonneg _ _, weight_le_all b.tail_le (cell_card hS (b.properties q hq).2.2.1) a⟩
  have hBound (T : Finset ℕ) (hT : T.card ≤ 1 + 2 * (2 * H + 1) ^ 2 * D.card) :
      K * T.card ≤ τ * b.pool.card := by
    apply le_trans _ hErr
    apply mul_le_mul_of_nonneg_left _ hK
    unfold badBound
    have ht : (T.card : ℝ) ≤ 1 + 2 * (2 * (H : ℝ) + 1) ^ 2 * (D.card : ℝ) := by exact_mod_cast hT
    have hd : (D.card : ℝ) ≤ 2 * (y : ℝ) * Real.exp (-(H : ℝ) ^ 3) := hD
    have hmul := mul_le_mul_of_nonneg_left hd (show 0 ≤ 2 * (2 * (H : ℝ) + 1) ^ 2 by positivity)
    linarith only [ht, hmul, show 2 * (2 * (H : ℝ) + 1) ^ 2 * (2 * (y : ℝ) * Real.exp (-(H : ℝ) ^ 3)) =
      4 * (2 * (H : ℝ) + 1) ^ 2 * (y : ℝ) * Real.exp (-(H : ℝ) ^ 3) by ring]
  have hsg (q : ℕ) (hq : q ∈ b.pool) :
    Real.exp (-(1 / (H : ℝ))) ≤ mean C (X q) ∧
      mean C (X q) ≤ Real.exp (1 / (H : ℝ)) :=
    band_weight_single b hS hh hq
  have hpair1 (q q' : ℕ) (hq : q ∈ b.pool) (hq' : q' ∈ b.pool) :
      mean C (fun a ↦ X q a * X q' a) ≤ Real.exp (2 / (H : ℝ)) +
        if q' ∈ badPrimeChoices S b.pool D q h then K else 0 := by
    by_cases hbad : q' ∈ badPrimeChoices S b.pool D q h
    · rw [if_pos hbad]
      refine (mean_of_forall_le hC (fun a _ ↦ ?_)).trans (le_add_of_nonneg_left (Real.exp_nonneg _))
      have hx : X q a ≤ (euler w 1) ^ H :=
        (mul_le_of_le_one_left (hW q _ hq a).1 hσ1).trans (hW q _ hq a).2
      have hx' : X q' a ≤ (euler w 1) ^ H :=
        (mul_le_of_le_one_left (hW q' _ hq' a).1 hσ1).trans (hW q' _ hq' a).2
      rw [show K = (euler w 1) ^ H * (euler w 1) ^ H by simp [K, two_mul, pow_add]]
      exact mul_le_mul hx hx' (mul_nonneg hσ (hW q' _ hq' a).1) (pow_nonneg (euler_pos _ zero_lt_one).le _)
    · rw [if_neg hbad, add_zero]
      have hne : q ≠ q' := fun he ↦ hbad (mem_filter.mpr ⟨hq', Or.inl he.symm⟩)
      have hqq : y < q * q' := by
        rcases le_total q q' with h | h
        · exact ((b.properties _ hq).2.2.2.1).trans_le (by simpa [pow_two] using Nat.mul_le_mul_left q h)
        · exact ((b.properties _ hq').2.2.2.1).trans_le (by simpa [pow_two] using Nat.mul_le_mul_right q' h)
      have hi := two_cells_inter_subset hS (hS hh) (b.properties _ hq).1 (b.properties _ hq').1 hne hqq
      have hgood : ∀ c ∈ cell S q (h % q), ∀ c' ∈ (cell S q' (h % q')).erase h, distance c c' ∉ D :=
        fun c hc c' hc' hcD ↦ hbad (mem_filter.mpr ⟨hq', Or.inr ⟨c, hc, c', hc', hcD⟩⟩)
      have hb := band_weight_pair b hS hh hq hq' hi hgood
      have hf : h ∈ cell S q' (h % q') := mem_filter.mpr ⟨hh, rfl⟩
      apply le_trans (mean_le (fun a _ ↦ le_of_eq ?_)) hb
      simp only [X, W, if_pos hf, pow_two]
      ring
  have hpair2 (q r : ℕ) (hq : q ∈ b.pool) (hr : r ∈ range q) :
      mean C (fun a ↦ X q a * W q r a) ≤ Real.exp (2 / (H : ℝ)) +
        if r ∈ badResidueChoices S D q h then K else 0 := by
    by_cases hbad : r ∈ badResidueChoices S D q h
    · rw [if_pos hbad]
      refine (mean_of_forall_le hC (fun a _ ↦ ?_)).trans (le_add_of_nonneg_left (Real.exp_nonneg _))
      have hx : X q a ≤ (euler w 1) ^ H :=
        (mul_le_of_le_one_left (hW q _ hq a).1 hσ1).trans (hW q _ hq a).2
      rw [show K = (euler w 1) ^ H * (euler w 1) ^ H by simp [K, two_mul, pow_add]]
      exact mul_le_mul hx (hW q r hq a).2 (hW q r hq a).1 (pow_nonneg (euler_pos _ zero_lt_one).le _)
    · rw [if_neg hbad, add_zero]
      have hne : h % q ≠ r := fun he ↦ hbad (mem_filter.mpr ⟨hr, Or.inl he.symm⟩)
      have hi : cell S q (h % q) ∩ cell S q r ⊆ {h} := by
        rw [disjoint_iff_inter_eq_empty.mp (cells_disjoint_residue hne)]
        exact empty_subset _
      have hgood : ∀ c ∈ cell S q (h % q), ∀ c' ∈ (cell S q r).erase h, distance c c' ∉ D :=
        fun c hc c' hc' hcD ↦ hbad (mem_filter.mpr ⟨hr, Or.inr ⟨c, hc, c',
          (mem_erase.mp hc').2, hcD⟩⟩)
      have hb := band_weight_pair b hS hh hq hq hi hgood
      have hf : h ∉ cell S q r := fun hp ↦ hne (mem_filter.mp hp).2
      apply le_trans (mean_le (fun a _ ↦ le_of_eq ?_)) hb
      simp only [X, W, if_neg hf, pow_one, mul_assoc]
      rfl
  have hpairAvg1 (q : ℕ) (hq : q ∈ b.pool) :
      mean b.pool (fun q' ↦ mean C (fun a ↦ X q a * X q' a)) ≤ Real.exp (2 / (H : ℝ)) + τ := by
    let T := badPrimeChoices S b.pool D q h
    have ht := hBound T (badPrimeChoices_card hS (mem_Icc.mp (hS hh)).2
      (b.properties q hq).1.pos (b.properties q hq).2.2.1 fun q' hq' ↦
        ⟨(b.properties q' hq').1.pos, (b.properties q' hq').2.2.1⟩)
    exact (mean_le (fun q' hq' ↦ hpair1 q q' hq hq')).trans
      (mean_add_bad b.nonempty (filter_subset _ _) _ _ _ ht)
  have hpairAvg2 (q : ℕ) (hq : q ∈ b.pool) :
      mean (range q) (fun r ↦ mean C (fun a ↦ X q a * W q r a)) ≤ Real.exp (2 / (H : ℝ)) + τ := by
    let T := badResidueChoices S D q h
    have ht : T.card ≤ 1 + 2 * (2 * H + 1) ^ 2 * D.card := by
      refine (badResidueChoices_card hS (b.properties q hq).2.2.1).trans ?_
      have hc : H ≤ (2 * H + 1) ^ 2 := by nlinarith
      exact Nat.add_le_add_left (Nat.mul_le_mul_right D.card (Nat.mul_le_mul_left 2 hc)) 1
    have ht' := (hBound T ht).trans (mul_le_mul_of_nonneg_left
      (Nat.cast_le.mpr (b.properties q hq).2.2.2.2.1) hτ0)
    refine (mean_le (fun r hr ↦ hpair2 q r hq hr)).trans ?_
    refine mean_add_bad (nonempty_range_iff.mpr (b.properties q hq).1.pos.ne') (filter_subset _ _) _ _ _ ?_
    rwa [card_range]
  have hX1 : Real.exp (-(1 / (H : ℝ))) ≤ mean C (fun a ↦ bandX b S h a) := by
    change Real.exp (-(1 / (H : ℝ))) ≤ mean C (fun a ↦ mean b.pool (fun q ↦ X q a))
    rw [mean_swap]
    exact const_le_mean b.nonempty fun q hq ↦ (hsg q hq).1
  have hX2 : mean C (fun a ↦ bandX b S h a ^ 2) ≤ Real.exp (2 / (H : ℝ)) + τ := by
    change mean C (fun a ↦ mean b.pool (fun q ↦ X q a) ^ 2) ≤ _
    simp_rw [mean_sq]
    rw [mean_swap]
    refine mean_of_forall_le b.nonempty fun q hq ↦ ?_
    rw [mean_swap]
    exact hpairAvg1 q hq
  have hDif : mean C (fun a ↦ (bandX b S h a - 1) ^ 2) =
      mean C (fun a ↦ (bandX b S h a) ^ 2) - 2 * mean C (fun a ↦ bandX b S h a) + 1 := by
    have he : ∀ x : ℝ, (x - 1) ^ 2 = x ^ 2 - 2 * x + 1 := by intro; ring
    simp_rw [he]
    rw [mean_add, mean_sub, mean_mul, mean_const hC 1]
  have hH1 : 1 / (H : ℝ) ≤ 1 / 4 :=
    div_le_div_of_nonneg_left zero_le_one (by norm_num) hR
  have hH2 : 2 / (H : ℝ) ≤ 1 / 2 :=
    (div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 2) (by norm_num) hR).trans_eq (by norm_num)
  have hE1 := exp_le_one_add_two_mul (show 0 ≤ 1 / (H : ℝ) by positivity) (hH1.trans (by norm_num))
  have hE2 := exp_le_one_add_two_mul (show 0 ≤ 2 / (H : ℝ) by positivity) hH2
  have hE0 := Real.add_one_le_exp (-(1 / (H : ℝ)))
  constructor
  · rw [hDif]
    linarith only [hX1, hX2, hE0, hE2, show 2 * (2 / (H : ℝ)) + 2 * (1 / (H : ℝ)) = 6 / (H : ℝ) by ring]
  · change mean C (fun a ↦ mean b.pool (fun q ↦ X q a * (1 + mean (range q) (fun r ↦ W q r a)))) ≤ 5
    rw [mean_swap]
    refine mean_of_forall_le b.nonempty fun q hq ↦ ?_
    have he : ∀ a, X q a * (1 + mean (range q) (fun r ↦ W q r a)) =
      X q a + mean (range q) (fun r ↦ X q a * W q r a) := by
      intro a
      rw [mean_mul, mul_add, mul_one]
    simp_rw [he]
    rw [mean_add, mean_swap]
    have hmean := add_le_add (hsg q hq).2 (hpairAvg2 q hq)
    have h1 : 1 / (H : ℝ) ≤ 1 / 4 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hR
    have h2 : 2 / (H : ℝ) ≤ 1 / 2 := hH2
    linarith only [hmean, h1, h2, hτ, hE1, hE2]

private theorem avoidThrough_merge {w : ℕ} (a b : Assignment w) (B n : ℕ) :
    avoidThrough (merge (fun p ↦ p.val ≤ B) a b) B n ↔ avoidThrough a B n := by
  unfold avoidThrough merge
  exact forall_congr' fun p ↦ ⟨fun h hp ↦ by simpa [if_pos hp] using h hp,
    fun h hp ↦ by simpa [if_pos hp] using h hp⟩

private theorem avoidAbove_merge {w : ℕ} (a b : Assignment w) (B n : ℕ) :
    avoidAbove (merge (fun p ↦ p.val ≤ B) a b) B n ↔ avoidAbove b B n := by
  unfold avoidAbove merge
  exact forall_congr' fun p ↦ ⟨fun h hp ↦ by simpa [if_neg (not_le_of_gt hp)] using h hp,
    fun h hp ↦ by simpa [if_neg (not_le_of_gt hp)] using h hp⟩

private theorem weight_merge {w : ℕ} (a b : Assignment w) (B : ℕ) (U : Finset ℕ) :
    weight B U (merge (fun p ↦ p.val ≤ B) a b) = weight B U b := by
  unfold weight survives
  exact if_congr (forall₂_congr fun n _ ↦ avoidAbove_merge a b B n) rfl rfl

private theorem smallSurvivors_merge {w : ℕ} (a b : Assignment w) (y B : ℕ) :
    smallSurvivors (merge (fun p ↦ p.val ≤ B) a b) y B = smallSurvivors a y B := by
  ext n
  simp [smallSurvivors, avoidThrough_merge]

private theorem band_moments {y w h : ℕ} (b : Band y w) (hh : h ∈ Icc 1 y) {τ : ℝ}
    (hτ : τ ≤ 1)
    (hErr : (euler w 1) ^ (2 * b.height) * badBound b.height y ≤ τ * b.pool.card) :
    mean (conditioned w h) (fun a ↦ (bandX b (smallSurvivors a y (b.height ^ 10)) h a - 1) ^ 2) ≤
      6 / (b.height : ℝ) + τ ∧
    mean (conditioned w h) (fun a ↦ bandY b (smallSurvivors a y (b.height ^ 10)) h a) ≤ 5 := by
  let B := b.height ^ 10
  let A := conditioned w h
  have hA := conditioned_nonempty w h
  constructor
  · unfold conditioned
    rw [mean_merge _ (fun p : primes w ↦ p.val ≤ B)]
    refine mean_of_forall_le hA fun a ha ↦ ?_
    simp only [B, bandX, weight_merge, smallSurvivors_merge]
    exact (band_moments_fixed b (smallSurvivors_sub a) (h_in_smallSurvivors hh ha) hτ hErr).1
  · unfold conditioned
    rw [mean_merge _ (fun p : primes w ↦ p.val ≤ B)]
    refine mean_of_forall_le hA fun a ha ↦ ?_
    simp only [B, bandY, weight_merge, smallSurvivors_merge]
    exact (band_moments_fixed b (smallSurvivors_sub a) (h_in_smallSurvivors hh ha) hτ hErr).2

private noncomputable def bandProb {y w : ℕ} (b : Band y w) (a : Assignment w) (q r : ℕ) : ℝ :=
  let B := b.height ^ 10
  let S := smallSurvivors a y B
  let W (s : ℕ) := weight B (cell S q s) a
  W r / ((q : ℝ) + ∑ s ∈ range q, W s)

private theorem bandProb_nonneg {y w : ℕ} (b : Band y w) (a : Assignment w) (q r : ℕ) :
    0 ≤ bandProb b a q r :=
  div_nonneg (weight_nonneg _ _) (add_nonneg (Nat.cast_nonneg _) (sum_nonneg fun _ _ ↦ weight_nonneg _ _))

private theorem bandProb_sum_le_one {y w : ℕ} (b : Band y w) (a : Assignment w) (q : ℕ) :
    ∑ r ∈ range q, bandProb b a q r ≤ 1 := by
  by_cases hq : q = 0
  · simp [hq]
  unfold bandProb
  rw [← Finset.sum_div, div_le_one]
  · linarith [Nat.cast_nonneg (α := ℝ) q]
  · exact add_pos_of_pos_of_nonneg (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hq))
      (sum_nonneg fun _ _ ↦ weight_nonneg _ _)

private theorem bandProb_le_one {y w : ℕ} (b : Band y w) (a : Assignment w)
    {q r : ℕ} (hr : r < q) : bandProb b a q r ≤ 1 :=
  (single_le_sum (fun j _ ↦ bandProb_nonneg b a q j) (mem_range.mpr hr)).trans (bandProb_sum_le_one b a q)

private theorem cauchy_le {ι : Type*} (s : Finset ι) {r f g : ι → ℝ}
    (hr : ∀ i ∈ s, 0 ≤ r i) (hf : ∀ i ∈ s, 0 ≤ f i) (hg : ∀ i ∈ s, 0 ≤ g i)
    (h : ∀ i ∈ s, (r i) ^ 2 ≤ f i * g i) :
    (∑ i ∈ s, r i) ^ 2 ≤ (∑ i ∈ s, f i) * (∑ i ∈ s, g i) := by
  let v (i : ι) := Real.sqrt (f i * g i)
  have hb : ∀ i ∈ s, r i ≤ v i := by
    intro i hi
    rw [← Real.sqrt_sq (hr i hi)]
    exact Real.sqrt_le_sqrt (h i hi)
  calc
    _ ≤ (∑ i ∈ s, v i) ^ 2 := pow_le_pow_left₀ (sum_nonneg hr) (sum_le_sum hb) _
    _ ≤ _ := sum_sq_le_sum_mul_sum_of_sq_le_mul _ hf hg
      (fun i hi ↦ (Real.sq_sqrt (mul_nonneg (hf i hi) (hg i hi))).le)

private theorem band_cauchy {y w h : ℕ} (b : Band y w) (a : Assignment w) :
    let S := smallSurvivors a y (b.height ^ 10)
    (bandCost b * bandX b S h a) ^ 2 ≤
      (bandCost b * bandY b S h a) * (∑ q ∈ b.pool, bandProb b a q (h % q)) := by
  dsimp only
  let B := b.height ^ 10
  let S := smallSurvivors a y B
  let σ := sigma (tailPrimes w B)
  let x (q : ℕ) := σ * weight B (cell S q (h % q)) a
  let z (q : ℕ) : ℝ := 1 + mean (range q) (fun r ↦ weight B (cell S q r) a)
  let n : ℝ := b.pool.card
  let d : ℝ := b.upper * σ
  have hx (q : ℕ) : 0 ≤ x q := mul_nonneg (tail_sigma_pos w B).le (weight_nonneg _ _)
  have hz (q : ℕ) : 0 < z q := add_pos_of_pos_of_nonneg zero_lt_one
    (div_nonneg (sum_nonneg fun _ _ ↦ weight_nonneg _ _) (Nat.cast_nonneg _))
  have hd : 0 < d := by
    obtain ⟨q, hq⟩ := b.nonempty
    exact mul_pos (Nat.cast_pos.mpr ((b.properties q hq).1.pos.trans_le
      (b.properties q hq).2.2.2.2.2)) (tail_sigma_pos _ _)
  have hn : 0 < n := Nat.cast_pos.mpr b.nonempty.card_pos
  have heX : bandCost b * bandX b S h a = ∑ q ∈ b.pool, x q / d := by
    change n / d * ((∑ q ∈ b.pool, x q) / n) = _
    rw [← Finset.sum_div]
    field_simp [hn.ne', hd.ne']
  have heY : bandCost b * bandY b S h a = ∑ q ∈ b.pool, (x q * z q) / d := by
    change n / d * ((∑ q ∈ b.pool, x q * z q) / n) = _
    rw [← Finset.sum_div]
    field_simp [hn.ne', hd.ne']
  have hprob (q : ℕ) (hq : q ∈ b.pool) : (x q / z q) / d ≤ bandProb b a q (h % q) := by
    have hq0 : (0 : ℝ) < q := Nat.cast_pos.mpr (b.properties q hq).1.pos
    have hσ : 0 < σ := tail_sigma_pos w B
    have hh : (x q / z q) / d = weight B (cell S q (h % q)) a / ((b.upper : ℝ) * z q) := by
      dsimp [x, d]
      field_simp [hσ.ne', (hz q).ne', (show (b.upper : ℝ) ≠ 0 from
        (Nat.cast_ne_zero.mpr ((b.properties q hq).1.pos.trans_le (b.properties q hq).2.2.2.2.2).ne'))]
    have hden : (q : ℝ) * z q = (q : ℝ) + ∑ s ∈ range q, weight B (cell S q s) a := by
      dsimp [z, mean]
      rw [card_range]
      field_simp [hq0.ne']
    rw [hh]
    change _ ≤ weight B (cell S q (h % q)) a / _
    rw [← hden]
    exact div_le_div_of_nonneg_left (weight_nonneg _ _) (mul_pos hq0 (hz q))
      (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (b.properties q hq).2.2.2.2.2) (hz q).le)
  rw [heX, heY]
  apply cauchy_le
  · exact fun q _ ↦ div_nonneg (hx q) hd.le
  · exact fun q _ ↦ div_nonneg (mul_nonneg (hx q) (hz q).le) hd.le
  · exact fun q _ ↦ bandProb_nonneg b a _ _
  · intro q hq
    have hEq : (x q / d) ^ 2 = (x q * z q / d) * (x q / z q / d) := by
      field_simp [(hz q).ne']
    rw [hEq]
    exact mul_le_mul_of_nonneg_left (hprob q hq) (div_nonneg (mul_nonneg (hx q) (hz q).le) hd.le)

private noncomputable def miss {ι : Type*} {y w : ℕ} (J : Finset ι) (b : ι → Band y w)
    (h : ℕ) (a : Assignment w) : ℝ :=
  ∏ j ∈ J, ∏ q ∈ (b j).pool, (1 - bandProb (b j) a q (h % q))

private theorem miss_bounds {ι : Type*} {y w : ℕ} (J : Finset ι) (b : ι → Band y w)
    (h : ℕ) (a : Assignment w) :
    0 ≤ miss J b h a ∧ miss J b h a ≤ 1 ∧
      miss J b h a ≤ Real.exp (-(∑ j ∈ J, ∑ q ∈ (b j).pool, bandProb (b j) a q (h % q))) := by
  have hb (j : ι) (q : ℕ) (hq : q ∈ (b j).pool) :
      0 ≤ 1 - bandProb (b j) a q (h % q) :=
    sub_nonneg.mpr (bandProb_le_one _ _ (Nat.mod_lt _ ((b j).properties _ hq).1.pos))
  refine ⟨prod_nonneg (fun j _ ↦ prod_nonneg (hb j)), prod_le_one
    (fun j _ ↦ prod_nonneg (hb j))
    (fun j _ ↦ prod_le_one (hb j) (fun q _ ↦ sub_le_self _ (bandProb_nonneg _ _ _ _))), ?_⟩
  unfold miss
  simp_rw [← sum_neg_distrib, Real.exp_sum]
  exact prod_le_prod (fun j _ ↦ prod_nonneg (hb j)) fun j _ ↦
    prod_le_prod (hb j) fun q _ ↦ by linarith only [Real.add_one_le_exp (-(bandProb (b j) a q (h % q)))]

private theorem mean_miss_le {ι : Type*} {y w h : ℕ} (J : Finset ι) (hJ : J.Nonempty)
    (b : ι → Band y w) (hh : h ∈ Icc 1 y) {ε τ : ℝ} (hτ : τ ≤ 1)
    (hErr : ∀ j ∈ J, (euler w 1) ^ (2 * (b j).height) * badBound (b j).height y ≤ τ * (b j).pool.card)
    (hε : ∀ j ∈ J, 6 / ((b j).height : ℝ) + τ ≤ ε) :
    mean (conditioned w h) (miss J b h) ≤ 4 * ε + 20 / (∑ j ∈ J, bandCost (b j)) := by
  let c (j : ι) := bandCost (b j)
  let A := ∑ j ∈ J, c j
  have hA : 0 < A := sum_pos (fun j _ ↦ bandCost_pos (b j)) hJ
  let C := conditioned w h
  let X (j : ι) (a : Assignment w) := bandX (b j) (smallSurvivors a y ((b j).height ^ 10)) h a
  let Y (j : ι) (a : Assignment w) := bandY (b j) (smallSurvivors a y ((b j).height ^ 10)) h a
  let P (j : ι) (a : Assignment w) := ∑ q ∈ (b j).pool, bandProb (b j) a q (h % q)
  let V (a : Assignment w) := ∑ j ∈ J, c j * (X j a - 1) ^ 2
  let T (a : Assignment w) := ∑ j ∈ J, c j * Y j a
  have hCauchy (a : Assignment w) :
      (∑ j ∈ J, c j * X j a) ^ 2 ≤ T a * (∑ j ∈ J, P j a) := by
    have hX (j : ι) : 0 ≤ X j a := div_nonneg
      (sum_nonneg fun _ _ ↦ mul_nonneg (tail_sigma_pos _ _).le (weight_nonneg _ _)) (Nat.cast_nonneg _)
    have hY (j : ι) : 0 ≤ Y j a := div_nonneg (sum_nonneg fun _ _ ↦
      mul_nonneg (mul_nonneg (tail_sigma_pos _ _).le (weight_nonneg _ _))
        (add_nonneg zero_le_one (div_nonneg (sum_nonneg fun _ _ ↦ weight_nonneg _ _) (Nat.cast_nonneg _))))
      (Nat.cast_nonneg _)
    exact cauchy_le _
      (fun j _ ↦ mul_nonneg (bandCost_pos _).le (hX j))
      (fun j _ ↦ mul_nonneg (bandCost_pos _).le (hY j))
      (fun j _ ↦ sum_nonneg fun _ _ ↦ bandProb_nonneg _ _ _ _)
      (fun j _ ↦ band_cauchy (h := h) (b j) a)
  have hVy (a : Assignment w) : 0 ≤ V a :=
    sum_nonneg fun _ _ ↦ mul_nonneg (bandCost_pos _).le (sq_nonneg _)
  have ht (a : Assignment w) : 0 ≤ T a := by
    unfold T Y bandY
    exact sum_nonneg fun j _ ↦ mul_nonneg (bandCost_pos _).le
      (div_nonneg (sum_nonneg fun _ _ ↦ mul_nonneg
        (mul_nonneg (tail_sigma_pos _ _).le (weight_nonneg _ _))
        (add_nonneg zero_le_one
          (div_nonneg (sum_nonneg fun _ _ ↦ weight_nonneg _ _) (Nat.cast_nonneg _))))
        (Nat.cast_nonneg _))
  have hpoint (a : Assignment w) : miss J b h a ≤ (4 / A) * V a + (4 / A ^ 2) * T a := by
    by_cases hX : A / 2 ≤ ∑ j ∈ J, c j * X j a
    · have hb : A ^ 2 / 4 ≤ T a * (∑ j ∈ J, P j a) := by
        rw [show A ^ 2 / 4 = (A / 2) ^ 2 by ring]
        exact (pow_le_pow_left₀ (by positivity) hX 2).trans (hCauchy a)
      let v := ∑ j ∈ J, P j a
      have hv : 0 ≤ v := sum_nonneg fun _ _ ↦ sum_nonneg fun _ _ ↦ bandProb_nonneg _ _ _ _
      have hf : Real.exp (-v) ≤ 1 / (1 + v) := by
        rw [Real.exp_neg, one_div]
        exact (inv_le_inv₀ (Real.exp_pos _) (by positivity)).mpr
          (by simpa [add_comm] using Real.add_one_le_exp v)
      refine (miss_bounds J b h a).2.2.trans (hf.trans (le_trans (b := (4 / A ^ 2) * T a) ?_ ?_))
      · rw [div_le_iff₀ (show 0 < 1 + v by positivity)]
        have hb' : A ^ 2 ≤ 4 * T a * v := by linarith only [hb]
        have hterm : 0 ≤ T a := ht a
        rw [div_mul_eq_mul_div, div_mul_eq_mul_div, le_div_iff₀ (sq_pos_of_pos hA)]
        nlinarith only [hb', hterm]
      · linarith [mul_nonneg (div_nonneg (by norm_num : (0 : ℝ) ≤ 4) hA.le) (hVy a)]
    · have hs : (A / 2) ≤ ∑ j ∈ J, c j * (1 - X j a) := by
        simp only [mul_sub, mul_one, sum_sub_distrib]
        change _ ≤ A - _
        linarith
      have hsq := sum_sq_le_sum_mul_sum_of_sq_le_mul J (r := fun j ↦ c j * (1 - X j a))
        (f := c) (g := fun j ↦ c j * (X j a - 1) ^ 2)
        (fun j _ ↦ (bandCost_pos (b j)).le) (fun j _ ↦ mul_nonneg (bandCost_pos (b j)).le (sq_nonneg _))
        (fun j _ ↦ le_of_eq (by ring))
      have hV' : (A / 2) ^ 2 ≤ A * V a :=
        (pow_le_pow_left₀ (by positivity) hs 2).trans hsq
      have hle : 1 ≤ (4 / A) * V a := by
        rw [div_mul_eq_mul_div, le_div_iff₀ hA, one_mul]
        have h' : A * A ≤ A * (4 * V a) := by nlinarith only [hV']
        exact le_of_mul_le_mul_left h' hA
      exact (miss_bounds J b h a).2.1.trans (hle.trans
        (le_add_of_nonneg_right (mul_nonneg (div_nonneg (by norm_num) (sq_nonneg _)) (ht a))))
  have hv : mean C V ≤ ε * A := by
    unfold V
    rw [mean_sum]
    simp_rw [mean_mul]
    calc
      _ ≤ ∑ j ∈ J, c j * ε := sum_le_sum fun j hj ↦
        mul_le_mul_of_nonneg_left ((band_moments (b j) hh hτ (hErr j hj)).1.trans (hε j hj))
          (bandCost_pos (b j)).le
      _ = _ := by rw [← sum_mul, mul_comm]
  have ht' : mean C T ≤ 5 * A := by
    unfold T
    rw [mean_sum]
    simp_rw [mean_mul]
    calc
      _ ≤ ∑ j ∈ J, c j * 5 := sum_le_sum fun j hj ↦
        mul_le_mul_of_nonneg_left (band_moments (b j) hh hτ (hErr j hj)).2 (bandCost_pos (b j)).le
      _ = _ := by rw [← sum_mul, mul_comm]
  calc
    _ ≤ mean C (fun a ↦ (4 / A) * V a + (4 / A ^ 2) * T a) := mean_le (fun a _ ↦ hpoint a)
    _ ≤ (4 / A) * (ε * A) + (4 / A ^ 2) * (5 * A) := by
      rw [mean_add, mean_mul, mean_mul]
      exact add_le_add (mul_le_mul_of_nonneg_left hv (by positivity))
        (mul_le_mul_of_nonneg_left ht' (by positivity))
    _ = _ := by
      change (4 / A) * (ε * A) + (4 / A ^ 2) * (5 * A) = 4 * ε + 20 / A
      field_simp [hA.ne']
      ring

/- Choose actual residues by averaging the number of uncovered offsets. -/
private theorem choose_one_residue (F : Finset ℕ) {q : ℕ} (hq : 0 < q) (p W : ℕ → ℝ)
    (hp : ∀ r ∈ range q, 0 ≤ p r) (hW : ∀ n ∈ F, 0 ≤ W n)
    (hp1 : ∑ r ∈ range q, p r ≤ 1) :
    ∃ r ∈ range q, (∑ n ∈ F with n % q ≠ r, W n) ≤ ∑ n ∈ F, (1 - p (n % q)) * W n := by
  classical
  let C (r : ℕ) := ∑ n ∈ F with n % q ≠ r, W n
  obtain ⟨r, hr, hmin⟩ := exists_min_image (range q) C (nonempty_range_iff.mpr hq.ne')
  refine ⟨r, hr, ?_⟩
  change C r ≤ _
  let P := ∑ s ∈ range q, p s
  have hF : C r ≤ ∑ n ∈ F, W n :=
    sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun n hn _ ↦ hW n hn)
  have hk : C r = (∑ s ∈ range q, p s * C r) + (1 - P) * ∑ n ∈ F with n % q ≠ r, W n := by
    rw [← sum_mul]
    change C r = P * C r + (1 - P) * C r
    ring
  calc
    _ = _ := hk
    _ ≤ (∑ s ∈ range q, p s * C s) + (1 - P) * ∑ n ∈ F, W n :=
      add_le_add (sum_le_sum fun s hs ↦ mul_le_mul_of_nonneg_left (hmin s hs) (hp s hs))
        (mul_le_mul_of_nonneg_left hF (sub_nonneg.mpr hp1))
    _ = _ := by
      have he (n : ℕ) : (∑ s ∈ range q with n % q ≠ s, p s) = P - p (n % q) := by
        have hrange : n % q ∈ range q := mem_range.mpr (Nat.mod_lt _ hq)
        have hfilt : (range q).filter (n % q ≠ ·) = (range q).erase (n % q) := by
          ext s
          simp only [mem_filter, mem_erase]
          tauto
        rw [hfilt]
        change _ = (∑ s ∈ range q, p s) - p (n % q)
        linarith only [sum_erase_add (range q) p hrange]
      have hsum : (∑ s ∈ range q, p s * C s) =
          ∑ n ∈ F, (P - p (n % q)) * W n := by
        calc
          _ = ∑ s ∈ range q, ∑ n ∈ F, if n % q ≠ s then p s * W n else 0 := by
            refine sum_congr rfl fun s _ ↦ ?_
            rw [← sum_filter]
            exact mul_sum .. 
          _ = _ := by
            rw [sum_comm]
            refine sum_congr rfl fun n _ ↦ ?_
            rw [← sum_filter, ← Finset.sum_mul, he]
      rw [hsum, mul_sum, ← sum_add_distrib]
      refine sum_congr rfl fun n _ ↦ ?_
      ring

private theorem choose_many_residues {ι : Type*} [DecidableEq ι]
    (Q : Finset ι) (F : Finset ℕ) (q : ι → ℕ) (p : ι → ℕ → ℝ)
    (hq : ∀ i ∈ Q, 0 < q i) (hp : ∀ i ∈ Q, ∀ r ∈ range (q i), 0 ≤ p i r)
    (hp1 : ∀ i ∈ Q, ∑ r ∈ range (q i), p i r ≤ 1) :
    ∃ r : ι → ℕ, (∀ i ∈ Q, r i < q i) ∧
      (↑(F.filter fun n ↦ ∀ i ∈ Q, n % q i ≠ r i).card : ℝ) ≤
        ∑ n ∈ F, ∏ i ∈ Q, (1 - p i (n % q i)) := by
  classical
  induction Q using Finset.induction_on generalizing F with
  | empty => exact ⟨fun _ ↦ 0, by simp⟩
  | @insert i Q hi ih =>
    let V (n : ℕ) := ∏ j ∈ Q, (1 - p j (n % q j))
    have hq₀ (j) (hj : j ∈ Q) := hq j (mem_insert_of_mem hj)
    have hp₀ (j) (hj : j ∈ Q) := hp j (mem_insert_of_mem hj)
    have h1 (j) (hj : j ∈ Q) := hp1 j (mem_insert_of_mem hj)
    have hV (n : ℕ) : 0 ≤ V n := by
      refine prod_nonneg fun j hj ↦ sub_nonneg.mpr ?_
      exact (single_le_sum (hp₀ j hj) (mem_range.mpr (Nat.mod_lt _ (hq₀ j hj)))).trans (h1 j hj)
    obtain ⟨r, hr, hrV⟩ := choose_one_residue F (hq i (mem_insert_self _ _)) (p i) V
      (hp i (mem_insert_self _ _)) (fun n _ ↦ hV n) (hp1 i (mem_insert_self _ _))
    obtain ⟨f, hf, hC⟩ := ih (F.filter (· % q i ≠ r)) hq₀ hp₀ h1
    let r' (j : ι) := if j = i then r else f j
    refine ⟨r', ?_, ?_⟩
    · intro j hj
      rcases mem_insert.mp hj with he | hj'
      · subst j
        simpa [r'] using mem_range.mp hr
      · have hne : j ≠ i := fun e ↦ hi (e ▸ hj')
        simpa [r', hne] using hf j hj'
    · have he :
        (F.filter fun n ↦ ∀ j ∈ insert i Q, n % q j ≠ r' j) =
          ((F.filter (· % q i ≠ r)).filter fun n ↦ ∀ j ∈ Q, n % q j ≠ f j) := by
        ext n
        simp only [mem_filter, forall_mem_insert, r', if_true]
        have hcon : (∀ j ∈ Q, n % q j ≠ (if j = i then r else f j)) ↔ ∀ j ∈ Q, n % q j ≠ f j := by
          refine forall_congr' fun j ↦ ?_
          constructor <;> intro h hj <;> have hne : j ≠ i := fun e ↦ hi (e ▸ hj)
          · simpa [hne] using h hj
          · simpa [hne] using h hj
        rw [hcon, and_assoc]
      rw [he]
      refine hC.trans (hrV.trans_eq ?_)
      exact sum_congr rfl fun n _ ↦ (prod_insert (f := fun j ↦ 1 - p j (n % q j)) hi).symm

private def smallHits {w : ℕ} (a : Assignment w) (h : ℕ) : Finset (primes w) :=
  univ.filter fun p ↦ a p = residue p h

private theorem smallHits_eq_empty {w h : ℕ} {a : Assignment w} :
    smallHits a h = ∅ ↔ a ∈ conditioned w h := by
  rw [mem_conditioned, eq_empty_iff_forall_notMem]
  simp [smallHits]

private theorem mean_one_small_hit (w h : ℕ) (p : primes w) :
    mean univ (fun a : Assignment w ↦
      if a p = residue p h ∧ ∀ q : primes w, q ≠ p → a q ≠ residue q h then (1 : ℝ) else 0) =
      sigma (primes w) / ((p.val : ℝ) - 1) := by
  classical
  let T (q : primes w) : Finset (Fin q.val) :=
    if q = p then univ.erase (residue q h) else {residue q h}
  have hstat (a : Assignment w) : (a p = residue p h ∧ ∀ q : primes w, q ≠ p → a q ≠ residue q h) ↔
      ∀ q : primes w, a q ∉ T q := by
    constructor
    · rintro ⟨hp, hq⟩ q
      by_cases he : q = p
      · subst q
        simp [T, hp]
      · simpa [T, he] using hq q he
    · intro h
      refine ⟨?_, fun q hne ↦ ?_⟩
      · simpa [T] using h p
      · simpa [T, hne] using h q
  simp_rw [hstat]
  have hx := mean_pi_avoid (fun q : primes w ↦ (univ : Finset (Fin q.val))) T
  rw [Fintype.piFinset_univ] at hx
  rw [hx]
  let f (q : primes w) : ℝ := ((univ \ T q).card : ℝ) / ((univ : Finset (Fin q.val)).card)
  let g (q : primes w) : ℝ := 1 - (q.val : ℝ)⁻¹
  have hnot (q : primes w) (hne : q ≠ p) : f q = g q := by
    dsimp [f, g, T]
    rw [if_neg hne, sdiff_singleton_eq_erase, card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin,
      Nat.cast_sub (mem_primes.mp q.prop).2.one_le, Nat.cast_one, sub_div,
      div_self (Nat.cast_ne_zero.mpr (mem_primes.mp q.prop).2.ne_zero), one_div]
  have hp : f p = 1 / (p.val : ℝ) := by
    have he : (univ : Finset (Fin p.val)) \ (univ.erase (residue p h)) = {residue p h} := by
      ext n
      simp [Finset.mem_sdiff]
    simp [f, T, he]
  have hf : (∏ q : primes w, f q) = f p * ∏ q ∈ univ.erase p, g q := by
    rw [← mul_prod_erase _ _ (mem_univ p)]
    exact congrArg (fun x ↦ f p * x) (prod_congr rfl fun q hq ↦ hnot q (mem_erase.mp hq).1)
  have hσ : sigma (primes w) = g p * ∏ q ∈ univ.erase p, g q := by
    rw [sigma, ← Finset.prod_attach]
    exact (mul_prod_erase _ _ (mem_univ p)).symm
  change (∏ q : primes w, f q) = _
  rw [hf, hp, hσ]
  have hp1 : (1 : ℝ) < p.val := by exact_mod_cast (mem_primes.mp p.prop).2.one_lt
  unfold g
  field_simp [show (p.val : ℝ) ≠ 0 by linarith, show (p.val : ℝ) - 1 ≠ 0 by linarith]

private theorem mean_at_most_one (w h : ℕ) :
    mean univ (fun a : Assignment w ↦ if (smallHits a h).card ≤ 1 then (1 : ℝ) else 0) ≤
      sigma (primes w) * (1 + ∑ p : primes w, (1 : ℝ) / ((p.val : ℝ) - 1)) := by
  classical
  have he (a : Assignment w) : (if (smallHits a h).card ≤ 1 then (1 : ℝ) else 0) ≤
      (if a ∈ conditioned w h then 1 else 0) + ∑ p : primes w,
        if a p = residue p h ∧ ∀ q : primes w, q ≠ p → a q ≠ residue q h then 1 else 0 := by
    have hn : ∀ p : primes w, (0 : ℝ) ≤
        if a p = residue p h ∧ ∀ q : primes w, q ≠ p → a q ≠ residue q h then 1 else 0 := by
      intro p
      split_ifs <;> norm_num
    by_cases hh : (smallHits a h).card ≤ 1
    · rw [if_pos hh]
      by_cases h0 : smallHits a h = ∅
      · rw [if_pos (smallHits_eq_empty.mp h0)]
        exact le_add_of_nonneg_right (sum_nonneg fun p _ ↦ hn p)
      · have h1 : (smallHits a h).card = 1 := by
          have hp := card_pos.mpr (nonempty_iff_ne_empty.mpr h0)
          omega
        obtain ⟨p, hp⟩ := card_eq_one.mp h1
        have ha : a p = residue p h :=
          (mem_filter.mp (by rw [hp]; exact mem_singleton_self p : p ∈ smallHits a h)).2
        have hq (q) (hne : q ≠ p) : a q ≠ residue q h := by
          intro he
          have hh' : q ∈ smallHits a h := mem_filter.mpr ⟨mem_univ _, he⟩
          rw [hp, mem_singleton] at hh'
          exact hne hh'
        have hs := single_le_sum (f := fun p : primes w ↦
          if a p = residue p h ∧ ∀ q : primes w, q ≠ p → a q ≠ residue q h then (1 : ℝ) else 0)
          (fun q _ ↦ hn q) (mem_univ p)
        dsimp at hs
        rw [if_pos (show a p = residue p h ∧ ∀ q : primes w, q ≠ p → a q ≠ residue q h from ⟨ha, hq⟩)] at hs
        exact hs.trans (le_add_of_nonneg_left (by split_ifs <;> norm_num))
    · rw [if_neg hh]
      exact add_nonneg (by split_ifs <;> norm_num) (sum_nonneg fun p _ ↦ hn p)
  refine (mean_le (fun a _ ↦ he a)).trans_eq ?_
  rw [mean_add, mean_condition_indicator w h (fun _ ↦ 1), mean_const (conditioned_nonempty w h), mul_one,
    mean_sum]
  simp_rw [mean_one_small_hit, div_eq_mul_inv, ← mul_sum]
  ring

/- Count offsets with too few forced factors after the sieve. -/
private theorem inv_sum_le_log_euler (w : ℕ) :
    (∑ p : primes w, (1 : ℝ) / ((p.val : ℝ) - 1)) ≤ 2 * Real.log (euler w 1) := by
  unfold euler
  rw [Real.log_prod]
  · have hr (p : ℕ) := prime_rpow_lt_one (p := p)
    have he (p : ℕ) (hp : p ∈ primes w) :
        1 / ((p : ℝ) - 1) ≤ 2 * Real.log ((1 - (p : ℝ) ^ (-1 : ℝ))⁻¹) := by
      have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (mem_primes.mp hp).2.two_le
      have hpos : 0 < 1 - (p : ℝ)⁻¹ :=
        sub_pos.mpr ((inv_lt_one₀ (by linarith)).mpr (by linarith))
      rw [Real.rpow_neg_one, Real.log_inv]
      have hg := Real.log_le_sub_one_of_pos hpos
      have ho : 1 / ((p : ℝ) - 1) ≤ 2 / p := by
        rw [div_le_div_iff₀ (by linarith) (by linarith)]
        linarith
      have ho' : 1 / ((p : ℝ) - 1) ≤ 2 * (p : ℝ)⁻¹ := by simpa only [div_eq_mul_inv] using ho
      linarith only [hg, ho']
    rw [show (∑ p : primes w, (1 : ℝ) / ((p.val : ℝ) - 1)) =
      ∑ p ∈ primes w, (1 : ℝ) / ((p : ℝ) - 1) from sum_attach (primes w) (fun p ↦ (1 : ℝ) / ((p : ℝ) - 1))]
    rw [mul_sum]
    exact sum_le_sum he
  · exact fun p hp ↦ inv_ne_zero (sub_pos.mpr
      (prime_rpow_lt_one (mem_primes.mp hp).2 zero_lt_one)).ne'

private theorem sigma_le_inv_log {w : ℕ} (hw : 1 < w) :
    sigma (primes w) ≤ 1 / Real.log w := by
  rw [sigma_primes, one_div]
  have hlog : 0 < Real.log (w : ℝ) := Real.log_pos (by exact_mod_cast hw)
  apply (inv_le_inv₀ (euler_pos w zero_lt_one) hlog).mpr
  exact (Real.log_le_log (Nat.cast_pos.mpr (by omega)) (by linarith)).trans (euler_ge_log w)

private noncomputable def fewHitsRate (w : ℕ) : ℝ :=
  (1 + 2 * Real.log (eulerConst * Real.log w)) / Real.log w

private theorem fewHits_mean {w : ℕ} (hw : 2 ≤ w) (h : ℕ) :
    mean univ (fun a : Assignment w ↦ if (smallHits a h).card ≤ 1 then (1 : ℝ) else 0) ≤
      fewHitsRate w := by
  let t := ∑ p : primes w, (1 : ℝ) / ((p.val : ℝ) - 1)
  have ht : 0 ≤ t := by
    refine sum_nonneg fun p _ ↦ one_div_nonneg.mpr ?_
    have hp : (2 : ℝ) ≤ p.val := by exact_mod_cast (mem_primes.mp p.prop).2.two_le
    linarith
  have hlog : 0 < Real.log (w : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < w by omega))
  have hcomp := Real.log_le_log (euler_pos w zero_lt_one) (euler_le_log (show 1 < w by omega))
  have hsum := inv_sum_le_log_euler w
  calc
    _ ≤ sigma (primes w) * (1 + t) := mean_at_most_one w h
    _ ≤ (1 / Real.log w) * (1 + t) := mul_le_mul_of_nonneg_right
      (sigma_le_inv_log (show 1 < w by omega)) (by positivity)
    _ ≤ _ := by
      unfold fewHitsRate
      rw [mul_comm, ← div_eq_mul_one_div]
      apply div_le_div_of_nonneg_right _ hlog.le
      linarith only [hsum, hcomp]

private theorem choose_cover {ι : Type*} {w y : ℕ} (hw : 2 ≤ w) (J : Finset ι) (hJ : J.Nonempty)
    (b : ι → Band y w) (D₀ D₁ : Finset ℕ) (hD₁ : D₁ ⊆ Icc 1 y)
    {ε τ : ℝ} (hτ : τ ≤ 1) (hε : ∀ j ∈ J, 6 / ((b j).height : ℝ) + τ ≤ ε)
    (hErr : ∀ j ∈ J, (euler w 1) ^ (2 * (b j).height) * badBound (b j).height y ≤ τ * (b j).pool.card) :
    ∃ (a : Assignment w) (r : (ι × ℕ) → ℕ) (F : Finset ℕ),
      (F.card : ℝ) ≤ D₀.card * fewHitsRate w +
        D₁.card * sigma (primes w) * (4 * ε + 20 / (∑ j ∈ J, bandCost (b j))) ∧
      (∀ j ∈ J, ∀ q ∈ (b j).pool, r (j,q) < q) ∧
      (∀ h ∈ D₀, h ∉ F → 1 < (smallHits a h).card) ∧
      (∀ h ∈ D₁, h ∉ F → (smallHits a h).Nonempty ∨
        ∃ j ∈ J, ∃ q ∈ (b j).pool, h % q = r (j,q)) := by
  classical
  let A := ∑ j ∈ J, bandCost (b j)
  let M : Assignment w → ℝ := fun a ↦
    (∑ h ∈ D₀, if (smallHits a h).card ≤ 1 then (1 : ℝ) else 0) +
      ∑ h ∈ D₁, if a ∈ conditioned w h then miss J b h a else 0
  have hM : mean univ M ≤ (D₀.card : ℝ) * fewHitsRate w +
      (D₁.card : ℝ) * sigma (primes w) * (4 * ε + 20 / A) := by
    unfold M
    rw [mean_add, mean_sum, mean_sum]
    have hσ (h : ℕ) := mean_condition_indicator w h (miss J b h)
    simp_rw [hσ]
    calc
      _ ≤ (∑ _h ∈ D₀, fewHitsRate w) + ∑ _h ∈ D₁, sigma (primes w) * (4 * ε + 20 / A) :=
        add_le_add (sum_le_sum fun h _ ↦ fewHits_mean hw h) (sum_le_sum fun h hh ↦
          mul_le_mul_of_nonneg_left (mean_miss_le J hJ b (hD₁ hh) hτ hErr hε)
            (sigma_pos (fun _ hp ↦ (mem_primes.mp hp).2.one_lt)).le)
      _ = _ := by simp [mul_assoc]
  have hne : (univ : Finset (Assignment w)).Nonempty :=
    (conditioned_nonempty w 0).mono (subset_univ _)
  obtain ⟨a, _, hMa⟩ := exists_le_mean hne M
  let Q := J.biUnion fun j ↦ ((b j).pool).image (fun q ↦ (j,q))
  let U := D₁.filter fun h ↦ a ∈ conditioned w h
  have hQ (j : ι) (q : ℕ) : (j,q) ∈ Q ↔ j ∈ J ∧ q ∈ (b j).pool := by
    simp [Q, mem_biUnion, mem_image]
  have hQ' (u : ι × ℕ) : u ∈ Q ↔ u.1 ∈ J ∧ u.2 ∈ (b u.1).pool := hQ _ _
  obtain ⟨r, hr, hR⟩ := choose_many_residues Q U Prod.snd (fun u ↦ bandProb (b u.1) a u.2)
    (fun u hu ↦ ((b u.1).properties _ (hQ' u |>.mp hu |>.2)).1.pos)
    (fun u _ r _ ↦ bandProb_nonneg _ _ _ _)
    (fun u _ ↦ bandProb_sum_le_one _ _ _)
  let F₀ := D₀.filter fun h ↦ (smallHits a h).card ≤ 1
  let F₁ := U.filter fun h ↦ ∀ u ∈ Q, h % u.2 ≠ r u
  have hprod (h : ℕ) :
      (∏ u ∈ Q, (1 - bandProb (b u.1) a u.2 (h % u.2))) = miss J b h a := by
    unfold Q miss
    rw [prod_biUnion]
    · refine prod_congr rfl fun j _ ↦ ?_
      rw [prod_image]
      intro p _ q _ he
      exact congrArg Prod.snd he
    · intro j _ k _ hjk
      refine disjoint_left.mpr ?_
      intro u hu hv
      obtain ⟨p, hp, hpe⟩ := mem_image.mp hu
      obtain ⟨q, hq, hqe⟩ := mem_image.mp hv
      exact hjk (congrArg Prod.fst (hpe.trans hqe.symm))
  have hR' : (F₁.card : ℝ) ≤ ∑ h ∈ U, miss J b h a := by
    simpa only [F₁, hprod] using hR
  refine ⟨a, r, F₀ ∪ F₁, ?_, fun j hj q hq ↦ hr _ ((hQ _ _).mpr ⟨hj, hq⟩), ?_, ?_⟩
  · calc
      _ ≤ (F₀.card : ℝ) + F₁.card := by exact_mod_cast card_union_le F₀ F₁
      _ ≤ M a := by
        unfold M
        simp only [← sum_filter, sum_const, nsmul_eq_mul, mul_one]
        exact add_le_add_right hR' _
      _ ≤ _ := hMa.trans hM
  · intro h hh hF
    by_contra! hBad
    exact hF (mem_union_left _ (mem_filter.mpr ⟨hh, hBad⟩))
  · intro h hh hF
    by_cases hhit : (smallHits a h).Nonempty
    · exact Or.inl hhit
    · right
      by_contra! hmiss
      have h0 : a ∈ conditioned w h := smallHits_eq_empty.mp (not_nonempty_iff_eq_empty.mp hhit)
      exact hF (mem_union_right _ (mem_filter.mpr ⟨mem_filter.mpr ⟨hh, h0⟩, fun u hu ↦
        hmiss u.1 (hQ' u |>.mp hu |>.1) u.2 (hQ' u |>.mp hu |>.2)⟩))

/- Count offsets with only small factors or with one large factor. -/
private theorem sqrt_lt_if_nat_sqrt_lt {n y : ℕ} (h : y.sqrt < n) :
    Real.sqrt y < (n : ℝ) := by
  have hsq : (y : ℝ) < (n : ℝ) ^ 2 := by exact_mod_cast Nat.sqrt_lt'.mp h
  have hs := Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) y)
  by_contra! hn
  nlinarith [pow_le_pow_left₀ (Nat.cast_nonneg (α := ℝ) n) hn 2]

private theorem smooth_tail {s : Finset ℕ} {y w : ℕ} {a : ℝ}
    (hy : 0 < y) (ha : 0 ≤ a) (ha1 : a < 1)
    (hs : ∀ n ∈ s, n ∈ (w + 1).smoothNumbers ∧ y.sqrt < n) :
    (∑ n ∈ s, (n : ℝ)⁻¹) ≤ (y : ℝ) ^ (-a / 2) * euler w (1 - a) := by
  calc
    _ ≤ ∑ n ∈ s, (y : ℝ) ^ (-a / 2) * (n : ℝ) ^ (-(1 - a)) := by
      refine sum_le_sum fun n hn ↦ ?_
      have hn' := (hs n hn).1
      have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (Nat.mem_smoothNumbers.mp hn').1)
      have hy0 : (0 : ℝ) < y := Nat.cast_pos.mpr hy
      rw [← Real.rpow_neg_one, show (-1 : ℝ) = -a + -(1 - a) by ring, Real.rpow_add hn0]
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hn0.le _)
      calc
        _ ≤ (Real.sqrt y) ^ (-a) :=
          Real.rpow_le_rpow_of_nonpos (Real.sqrt_pos.mpr hy0) (sqrt_lt_if_nat_sqrt_lt (hs n hn).2).le (by linarith)
        _ = _ := by rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hy0.le]; congr 1; ring
    _ ≤ _ := by
      rw [← mul_sum]
      exact mul_le_mul_of_nonneg_left (sum_smooth_le_euler (by linarith) (fun n hn ↦ (hs n hn).1))
        (Real.rpow_nonneg (Nat.cast_nonneg _) _)

private theorem smooth_count_bound {y w : ℕ} {a : ℝ} (hy : 0 < y)
    (ha : 0 ≤ a) (ha1 : a < 1) :
    ((y.smoothNumbersUpTo (w + 1)).card : ℝ) ≤ y.sqrt +
      (y : ℝ) * (y : ℝ) ^ (-a / 2) * (euler w (1 - a) / euler w 1) := by
  classical
  let s := y.smoothNumbersUpTo (w + 1)
  let lo := s.filter (· ≤ y.sqrt)
  let hi := s.filter (¬ · ≤ y.sqrt)
  have hcard : lo.card + hi.card = s.card := card_filter_add_card_filter_not _
  have hLo : lo.card ≤ y.sqrt := by
    have hf : lo ⊆ Icc 1 y.sqrt := by
      intro n hn
      obtain ⟨_, hn'⟩ := Nat.mem_smoothNumbersUpTo.mp (mem_filter.mp hn).1
      exact mem_Icc.mpr ⟨Nat.pos_of_ne_zero (Nat.mem_smoothNumbers.mp hn').1, (mem_filter.mp hn).2⟩
    exact (card_le_card hf).trans_eq (by simp [Nat.card_Icc])
  have hY0 : (0 : ℝ) < y := Nat.cast_pos.mpr hy
  have hHi : (hi.card : ℝ) ≤ (y : ℝ) ^ (-a / 2) * ((y : ℝ) * (euler w (1 - a) / euler w 1)) := calc
    _ = ∑ _n ∈ hi, (1 : ℝ) := by simp
    _ ≤ ∑ n ∈ hi, (y : ℝ) ^ (-a / 2) * (n : ℝ) ^ a := by
      refine sum_le_sum fun n hn ↦ ?_
      have hsqr := sqrt_lt_if_nat_sqrt_lt (Nat.lt_of_not_ge (mem_filter.mp hn).2)
      have hpow := Real.rpow_le_rpow (Real.sqrt_nonneg (y : ℝ)) hsqr.le ha
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hY0.le] at hpow
      have hni : (y : ℝ) ^ (-a / 2) * (y : ℝ) ^ ((1 / 2 : ℝ) * a) = 1 := by
        rw [← Real.rpow_add hY0, show -a / 2 + (1 / 2 : ℝ) * a = 0 by ring, Real.rpow_zero]
      exact hni ▸ mul_le_mul_of_nonneg_left hpow (Real.rpow_nonneg hY0.le _)
    _ ≤ (y : ℝ) ^ (-a / 2) * (∑ n ∈ s, (n : ℝ) ^ a) := by
      rw [← mul_sum]
      exact mul_le_mul_of_nonneg_left
        (sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun n _ _ ↦ Real.rpow_nonneg (Nat.cast_nonneg n) _)
        (Real.rpow_nonneg hY0.le _)
    _ ≤ _ := mul_le_mul_of_nonneg_left (smooth_count_moment ha ha1) (Real.rpow_nonneg hY0.le _)
  rw [← hcard, Nat.cast_add]
  have hlo' : (lo.card : ℝ) ≤ y.sqrt := Nat.cast_le.mpr hLo
  calc
    _ ≤ _ := add_le_add hlo' hHi
    _ = _ := by ring

private def primeMultiples (y v : ℕ) (s : Finset ℕ) : Finset ℕ :=
  s.biUnion fun m ↦ (((primes (y / m)).filter (v < ·)).image (fun p ↦ p * m))

private theorem mem_primeMultiples {y v h : ℕ} {s : Finset ℕ} :
    h ∈ primeMultiples y v s ↔
      ∃ m ∈ s, ∃ p, p.Prime ∧ v < p ∧ p ≤ y / m ∧ p * m = h := by
  simp only [primeMultiples, mem_biUnion, mem_image, mem_filter, mem_primes]
  constructor
  · rintro ⟨m, hm, p, ⟨⟨hym, hp⟩, hv⟩, hh⟩
    exact ⟨m, hm, p, hp, hv, hym, hh⟩
  · rintro ⟨m, hm, p, hp, hv, hym, hh⟩
    exact ⟨m, hm, p, ⟨⟨hym, hp⟩, hv⟩, hh⟩

private theorem primeMultiples_subset {y v : ℕ} {s : Finset ℕ} (hpos : ∀ m ∈ s, 0 < m) :
    primeMultiples y v s ⊆ Icc 1 y := by
  intro h hh
  obtain ⟨m, hm, p, hp, _, hd, rfl⟩ := mem_primeMultiples.mp hh
  exact mem_Icc.mpr ⟨mul_pos hp.pos (hpos m hm), (Nat.le_div_iff_mul_le (hpos m hm)).mp hd⟩

private theorem primeMultiples_count {y v : ℕ} {s : Finset ℕ} {L : ℝ}
    (hL : 0 < L) (hm : ∀ m ∈ s, 0 < m)
    (hlog : ∀ m ∈ s, v < y / m → 1 < y / m ∧ L ≤ Real.log (y / m : ℕ)) :
    ((primeMultiples y v s).card : ℝ) ≤ (8 * (y : ℝ) / L) * ∑ m ∈ s, (m : ℝ)⁻¹ := by
  unfold primeMultiples
  have hnat : (s.biUnion fun m ↦ (((primes (y / m)).filter (v < ·)).image (fun p ↦ p * m))).card ≤
      ∑ m ∈ s, (((primes (y / m)).filter (v < ·)).image (fun p ↦ p * m)).card := card_biUnion_le
  have hsum : _ ≤ (↑(∑ m ∈ s, (((primes (y / m)).filter (v < ·)).image (fun p ↦ p * m)).card) : ℝ) :=
    Nat.cast_le.mpr hnat
  rw [Nat.cast_sum] at hsum
  apply hsum.trans
  rw [mul_sum]
  refine sum_le_sum fun m hm' ↦ ?_
  have hm0 : (0 : ℝ) < m := Nat.cast_pos.mpr (hm m hm')
  by_cases hvm : v < y / m
  · have hp := hlog m hm' hvm
    have hd : (0 : ℝ) ≤ (y / m : ℕ) := Nat.cast_nonneg _
    calc
      _ ≤ ((primes (y / m)).card : ℝ) := Nat.cast_le.mpr
        (card_image_le.trans (card_filter_le _ _))
      _ ≤ 8 * (↑(y / m) : ℝ) / Real.log (y / m : ℕ) := prime_count_upper hp.1
      _ ≤ 8 * ((y : ℝ) / m) / L :=
        div_le_div_of_nonneg_left (by positivity) hL hp.2 |>.trans
          (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left Nat.cast_div_le (by norm_num)) hL.le)
      _ = _ := by ring
  · have he : (primes (y / m)).filter (v < ·) = ∅ := by
      refine eq_empty_iff_forall_notMem.mpr fun p hp ↦ ?_
      exact hvm ((mem_filter.mp hp).2.trans_le (mem_primes.mp (mem_filter.mp hp).1).1)
    rw [he, image_empty, card_empty, Nat.cast_zero]
    positivity

private theorem sum_inv_Icc (n : ℕ) : ∑ m ∈ Icc 1 n, (m : ℝ)⁻¹ ≤ 1 + Real.log n := by
  have he : (∑ m ∈ Icc 1 n, (m : ℝ)⁻¹) = (harmonic n : ℝ) := by
    rw [harmonic_eq_sum_Icc]
    push_cast
    rfl
  rw [he]
  exact harmonic_le_one_add_log n

private theorem log_div_small_index {y m : ℕ} (hy : 4 ≤ y) (hm : 0 < m)
    (hmy : m ≤ y.sqrt) : 1 < y / m ∧ Real.log (y : ℝ) / 3 ≤ Real.log (y / m : ℕ) := by
  let v := y / m
  have hm' : m ≤ v := by
    apply (Nat.le_div_iff_mul_le hm).mpr
    exact (Nat.mul_le_mul hmy hmy).trans (Nat.sqrt_le y)
  have hyv : y ≤ 2 * v ^ 2 := by
    have h₀ := Nat.div_add_mod y m
    have h₁ := Nat.mod_lt y hm
    have h₂ : y ≤ m * (v + 1) := by
      rw [mul_add, mul_one]
      change m * v + y % m = y at h₀
      omega
    calc
      _ ≤ _ := h₂
      _ ≤ v * (v + 1) := Nat.mul_le_mul_right _ hm'
      _ ≤ _ := by nlinarith
  have hv : 1 < v := by
    by_contra! h
    have h' := Nat.pow_le_pow_left h 2
    omega
  have hyv' : (y : ℝ) ≤ 2 * (v : ℝ) ^ 2 := by exact_mod_cast hyv
  have hlog := Real.log_le_log (Nat.cast_pos.mpr (by omega : 0 < y)) hyv' 
  rw [Real.log_mul (by norm_num) (pow_ne_zero _ (Nat.cast_ne_zero.mpr (by omega))), Real.log_pow] at hlog
  have h₂ : Real.log 2 ≤ Real.log (v : ℝ) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hv)
  refine ⟨hv, ?_⟩
  change Real.log (y : ℝ) / 3 ≤ Real.log (v : ℝ)
  norm_num at hlog
  linarith only [hlog,h₂]

private theorem one_large_count {y w : ℕ} {a : ℝ} (hy : 4 ≤ y) (hw : 1 < w)
    (ha : 0 ≤ a) (ha1 : a < 1) :
    ((primeMultiples y w (y.smoothNumbersUpTo (w + 1))).card : ℝ) ≤
      24 * (y : ℝ) / Real.log y * euler w 1 +
      8 * (y : ℝ) / Real.log w * ((y : ℝ) ^ (-a / 2) * euler w (1 - a)) := by
  classical
  let s := y.smoothNumbersUpTo (w + 1)
  let lo := s.filter (· ≤ y.sqrt)
  let hi := s.filter (¬ · ≤ y.sqrt)
  have hy0 : 0 < y := by omega
  have hpos (m : ℕ) (hm : m ∈ s) : 0 < m :=
    Nat.pos_of_ne_zero (Nat.mem_smoothNumbers.mp (Nat.mem_smoothNumbersUpTo.mp hm).2).1
  have hlogy : 0 < Real.log (y : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  have hlogw : 0 < Real.log (w : ℝ) := Real.log_pos (by exact_mod_cast hw)
  have hSplit : primeMultiples y w s = primeMultiples y w lo ∪ primeMultiples y w hi := by
    unfold primeMultiples
    rw [← Finset.union_biUnion, filter_union_filter_not_eq]
  have hl := primeMultiples_count (v := w) (y := y) (s := lo) (L := Real.log y / 3) (by positivity)
    (fun m hm ↦ hpos m (mem_filter.mp hm).1) (fun m hm _ ↦
      log_div_small_index hy (hpos m (mem_filter.mp hm).1) (mem_filter.mp hm).2)
  have hh := primeMultiples_count (v := w) (y := y) (s := hi) (L := Real.log w) hlogw
    (fun m hm ↦ hpos m (mem_filter.mp hm).1) (fun m _ h ↦
      ⟨hw.trans h, Real.log_le_log (Nat.cast_pos.mpr (by omega)) (by exact_mod_cast h.le)⟩)
  have hLe := sum_smooth_le_euler (s := lo) (r := 1) (w := w) zero_lt_one
    (fun n hn ↦ (Nat.mem_smoothNumbersUpTo.mp (mem_filter.mp hn).1).2)
  simp only [Real.rpow_neg_one] at hLe
  have hHe := smooth_tail (s := hi) (w := w) (y := y) hy0 ha ha1
    (fun n hn ↦ ⟨(Nat.mem_smoothNumbersUpTo.mp (mem_filter.mp hn).1).2,
      Nat.lt_of_not_ge (mem_filter.mp hn).2⟩)
  rw [hSplit]
  calc
    _ ≤ ((primeMultiples y w lo).card : ℝ) + (primeMultiples y w hi).card := by
      exact_mod_cast card_union_le _ _
    _ ≤ _ := add_le_add (hl.trans (mul_le_mul_of_nonneg_left hLe (by positivity)))
      (hh.trans (mul_le_mul_of_nonneg_left hHe (by positivity)))
    _ = _ := by ring

private theorem beyond_main_count {y z H : ℕ} (hZ : 1 < z) (hy : 4 ≤ y)
    (hLog : Real.log (y : ℝ) / 2 ≤ Real.log (z : ℝ)) :
    ((primeMultiples y z (Icc 1 H)).card : ℝ) ≤ 16 * (y : ℝ) / Real.log y * (1 + Real.log H) := by
  have hlogy : 0 < Real.log (y : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  have h := primeMultiples_count (v := z) (y := y) (s := Icc 1 H) (L := Real.log y / 2) (by positivity)
    (fun _ hm ↦ (mem_Icc.mp hm).1) (fun m _ hl ↦
      ⟨hZ.trans hl, hLog.trans (Real.log_le_log (Nat.cast_pos.mpr (by omega)) (by exact_mod_cast hl.le))⟩)
  calc
    _ ≤ _ := h.trans (mul_le_mul_of_nonneg_left (sum_inv_Icc H) (by positivity))
    _ = _ := by ring

/- Combine the divisibility conditions using the Chinese remainder theorem. -/
section
open Nat

private theorem omega_gt_two_of_proper_dvd {d n : ℕ}
    (hd : Ω d = 2) (hdiv : d ∣ n) (hlt : d < n) : 2 < Ω n := by
  obtain ⟨m, rfl⟩ := hdiv
  have hm : 1 < m := by
    by_contra! h
    have : d * m ≤ d * 1 := Nat.mul_le_mul_left d h
    omega
  have hd0 : d ≠ 0 := by
    intro h
    simp [h] at hlt
  rw [ArithmeticFunction.cardFactors_mul hd0 (by omega), hd]
  have := ArithmeticFunction.cardFactors_pos_iff_one_lt.mpr hm
  omega

private theorem crt_squares {ι : Type*} (s : Finset ι) (p r : ι → ℕ)
    (hp : ∀ i ∈ s, (p i).Prime) (hinj : Set.InjOn p s) :
    ∃ a < ∏ i ∈ s, p i ^ 2, ∀ i ∈ s, p i ^ 2 ∣ a + r i := by
  let a₀ : ι → ℕ := fun i ↦ p i ^ 2 - r i % (p i ^ 2)
  have hne : ∀ i ∈ s, p i ^ 2 ≠ 0 := fun i hi ↦ pow_ne_zero _ (hp i hi).ne_zero
  have hco : Set.Pairwise s (fun i j ↦ (p i ^ 2).Coprime (p j ^ 2)) := by
    intro i hi j hj hij
    have hpij : p i ≠ p j := fun h ↦ hij (hinj hi hj h)
    exact ((Nat.coprime_primes (hp i hi) (hp j hj)).mpr hpij).pow 2 2
  let a := Nat.chineseRemainderOfFinset a₀ (fun i ↦ p i ^ 2) s hne hco
  refine ⟨a, Nat.chineseRemainderOfFinset_lt_prod _ _ _ _, ?_⟩
  intro i hi
  have hmod := (a.prop i hi).add (Nat.mod_modEq (r i) (p i ^ 2)).symm
  have hsum : a₀ i + r i % (p i ^ 2) = p i ^ 2 :=
    Nat.sub_add_cancel (Nat.mod_lt _ (Nat.pos_of_ne_zero (hne i hi))).le
  rw [hsum] at hmod
  exact Nat.modEq_zero_iff_dvd.mp (hmod.trans (Nat.modEq_zero_iff_dvd.mpr dvd_rfl))

end
private theorem is_smooth_of_no_large {w n : ℕ} (hn : 0 < n)
    (h : ∀ p, p.Prime → p ∣ n → p ≤ w) : n ∈ (w + 1).smoothNumbers := by
  refine Nat.mem_smoothNumbers.mpr ⟨hn.ne', fun p hp ↦ Nat.lt_succ_of_le ?_⟩
  exact h _ (Nat.prime_of_mem_primeFactorsList hp) (Nat.dvd_of_mem_primeFactorsList hp)

private theorem offset_classification {y w z H n : ℕ} (hy : y = z * H) (hHz : H < w)
    (hwz : w ≤ z) (hn : n ∈ Icc 1 y) :
    let S := y.smoothNumbersUpTo (w + 1)
    n ∈ S ∪ primeMultiples y z (Icc 1 H) ∨
      (∃ p, p.Prime ∧ w < p ∧ p ≤ z ∧ p ∣ n ∧ n ∈ primeMultiples y w S) ∨
      ∃ p q, p.Prime ∧ q.Prime ∧ w < p ∧ p ≤ z ∧ w < q ∧ q ≤ z ∧ p * q ∣ n := by
  dsimp only
  have hn' := mem_Icc.mp hn
  have hny : 0 < n := hn'.1
  have hz0 : 0 < z := by omega
  by_cases hlarge : ∃ p, p.Prime ∧ w < p ∧ p ∣ n
  · obtain ⟨p, hp, hpw, ⟨m, hm⟩⟩ := hlarge
    have hm0 : 0 < m := by
      by_contra! hh
      rw [show m = 0 by omega, mul_zero] at hm
      omega
    have hpm : p ≤ y / m := (Nat.le_div_iff_mul_le hm0).mpr (hm ▸ hn'.2)
    by_cases hpz : z < p
    · left
      apply mem_union_right
      have hmH : m ≤ H := by
        apply Nat.le_of_mul_le_mul_left _ hz0
        calc
          z * m ≤ p * m := Nat.mul_le_mul_right m hpz.le
          _ ≤ z * H := by simpa [← hy, ← hm] using hn'.2
      exact mem_primeMultiples.mpr ⟨m, mem_Icc.mpr ⟨hm0, hmH⟩, p, hp, hpz, hpm, hm.symm⟩
    · right
      by_cases hq : ∃ q, q.Prime ∧ w < q ∧ q ∣ m
      · right
        obtain ⟨q, hq, hqw, hqd⟩ := hq
        have hdiv : p * q ∣ n := hm ▸ Nat.mul_dvd_mul_left p hqd
        have hzq : q ≤ z := by
          by_contra! h
          have hL : z * H < q * p :=
            Nat.mul_lt_mul_of_lt_of_le h (hHz.trans hpw).le (by omega)
          exact (not_lt_of_ge ((Nat.le_of_dvd hny hdiv).trans hn'.2)) (by simpa [hy, mul_comm] using hL)
        exact ⟨p, q, hp, hq, hpw, le_of_not_gt hpz, hqw, hzq, hdiv⟩
      · left
        refine ⟨p, hp, hpw, le_of_not_gt hpz, ⟨m, hm⟩, mem_primeMultiples.mpr ⟨m, ?_, p, hp, hpw, hpm, hm.symm⟩⟩
        refine Nat.mem_smoothNumbersUpTo.mpr ⟨?_, is_smooth_of_no_large hm0 ?_⟩
        · exact (Nat.le_of_dvd hny ⟨p, by simpa [mul_comm] using hm⟩).trans hn'.2
        · exact fun q hqp hqd ↦ le_of_not_gt fun hqw ↦ hq ⟨q, hqp, hqw, hqd⟩
  · left
    exact mem_union_left _ (Nat.mem_smoothNumbersUpTo.mpr ⟨hn'.2, is_smooth_of_no_large hny
      fun p hp hd ↦ le_of_not_gt fun hwp ↦ hlarge ⟨p, hp, hwp, hd⟩⟩)

set_option maxHeartbeats 3000000 in
private theorem hole_from_cover {ι : Type*} {y w H z x : ℕ}
    (hy : y = z * H) (hHw : H < w) (hwz : w ≤ z) (hzx : z ≤ x) (hxy : x ≤ y)
    (hY : 4 ≤ y) (J : Finset ι) (b : ι → Band y w)
    (hband : ∀ j ∈ J, ∀ q ∈ (b j).pool, z < q ∧ q ≤ x)
    (hdisj : Set.Pairwise (J : Set ι) fun i j ↦ Disjoint (b i).pool (b j).pool)
    (F : Finset ℕ) (hpatch : F.card ≤ (primes (y ^ 2) \ primes y).card)
    (a : Assignment w) (r : (ι × ℕ) → ℕ)
    (h₀ : ∀ n ∈ y.smoothNumbersUpTo (w + 1) ∪ primeMultiples y z (Icc 1 H),
      n ∉ F → 1 < (smallHits a n).card)
    (h₁ : ∀ n ∈ primeMultiples y w (y.smoothNumbersUpTo (w + 1)), n ∉ F →
      (smallHits a n).Nonempty ∨ ∃ j ∈ J, ∃ q ∈ (b j).pool, n % q = r (j,q)) :
    ∃ N : ℕ, y ≤ N ∧ Real.log ((N : ℝ) + 1) ≤
      Real.log ((y : ℝ) + 2) + 4 * (x : ℝ) + 4 * Real.log y * (F.card : ℝ) ∧
        ∀ h ∈ Icc 1 y, 2 < Ω (N + h) := by
  classical
  let P := primes (y ^ 2) \ primes y
  have hpCard : Fintype.card F ≤ Fintype.card P := by simpa [P] using hpatch
  let e : F ↪ P := ((Fintype.equivFin F).toEmbedding.trans (Fin.castLEEmb hpCard)).trans
    (Fintype.equivFin P).symm.toEmbedding
  let p (h : F) : ℕ := (e h).val
  have hp (h : F) : y < p h ∧ p h ≤ y ^ 2 ∧ (p h).Prime := by
    have hmem := mem_sdiff.mp (e h).prop
    have hp' := mem_primes.mp hmem.1
    exact ⟨lt_of_not_ge (fun h ↦ hmem.2 (mem_primes.mpr ⟨h, hp'.2⟩)), hp'⟩
  have hpinj : Function.Injective p := fun _ _ hh ↦ e.injective (Subtype.ext hh)
  let P' := F.attach.image p
  have hP'disj : Disjoint (primes x) P' := by
    refine disjoint_left.mpr fun q hq hq' ↦ ?_
    obtain ⟨h, _, he⟩ := mem_image.mp hq'
    exact (not_lt_of_ge ((mem_primes.mp hq).1.trans hxy)) (he ▸ (hp h).1)
  let T := primes x ∪ P'
  have hprime (q : ℕ) (hq : q ∈ T) : q.Prime := by
    rcases mem_union.mp hq with hl | hr
    · exact (mem_primes.mp hl).2
    · obtain ⟨h, _, he⟩ := mem_image.mp hr
      exact he ▸ (hp h).2.2
  let r₀ (q : ℕ) : ℕ :=
    if hq : q ∈ primes w then (a ⟨q, hq⟩).val
    else if hc : ∃ j ∈ J, q ∈ (b j).pool then r (Classical.choose hc, q)
    else if he : ∃ h : F, p h = q then (Classical.choose he).val
    else 0
  have hSmall {q : ℕ} (hq : q ∈ primes w) : r₀ q = (a ⟨q,hq⟩).val := dif_pos hq
  have hLarge {j : ι} (hj : j ∈ J) {q : ℕ} (hq : q ∈ (b j).pool) : r₀ q = r (j,q) := by
    have hN : q ∉ primes w := fun hc ↦ not_lt_of_ge ((mem_primes.mp hc).1.trans hwz) (hband j hj q hq).1
    let hex : ∃ j ∈ J, q ∈ (b j).pool := ⟨j, hj, hq⟩
    have hu : Classical.choose hex = j := by
      by_contra hh
      have hh' := Classical.choose_spec hex
      exact (disjoint_left.mp (hdisj hh'.1 hj hh)) hh'.2 hq
    unfold r₀
    rw [dif_neg hN, dif_pos hex, hu]
  have hPatch (h : F) : r₀ (p h) = h.val := by
    have hN : p h ∉ primes w := fun hq ↦
      not_lt_of_ge ((mem_primes.mp hq).1.trans (hwz.trans (hzx.trans hxy))) (hp h).1
    have hb : ¬ ∃ j ∈ J, p h ∈ (b j).pool := by
      rintro ⟨j, hj, hh⟩
      exact not_lt_of_ge ((hband j hj _ hh).2.trans hxy) (hp h).1
    let he : ∃ h' : F, p h' = p h := ⟨h,rfl⟩
    have hh : Classical.choose he = h := hpinj (Classical.choose_spec he)
    unfold r₀
    rw [dif_neg hN, dif_neg hb, dif_pos he, hh]
  have hZero {q : ℕ} (hq : w < q) (hqz : q ≤ z) : r₀ q = 0 := by
    have hN : q ∉ primes w := fun hh ↦ not_lt_of_ge (mem_primes.mp hh).1 hq
    have hB : ¬ ∃ j ∈ J, q ∈ (b j).pool := by
      rintro ⟨j,hj,hjq⟩
      exact not_lt_of_ge hqz (hband j hj q hjq).1
    have hP : ¬ ∃ h : F, p h = q := by
      rintro ⟨h, rfl⟩
      exact not_lt_of_ge (hqz.trans (hzx.trans hxy)) (hp h).1
    unfold r₀
    rw [dif_neg hN, dif_neg hB, dif_neg hP]
  obtain ⟨N₀, hN₀, hcrt⟩ := crt_squares T id r₀ hprime (fun _ _ _ _ hv ↦ hv)
  let M := ∏ q ∈ T, q ^ 2
  have hM : 0 < M := by have : N₀ < M := hN₀; omega
  let N := N₀ + (y + 1) * M
  have hNM : M ≤ N := by
    exact (Nat.le_mul_of_pos_left _ (by omega : 0 < y + 1)).trans (Nat.le_add_left _ _)
  have hNy : y ≤ N := by
    have hl := Nat.mul_le_mul_left (y + 1) hM
    dsimp [N]
    omega
  have hDivM {q : ℕ} (hq : q ∈ T) : q ^ 2 ∣ M := dvd_prod_of_mem (· ^ 2) hq
  have hDiv {q : ℕ} (hq : q ∈ T) : q ^ 2 ∣ N + r₀ q := by
    have hd := (hDivM hq).trans (dvd_mul_left M (y + 1))
    change q ^ 2 ∣ N₀ + (y + 1) * M + r₀ q
    rw [Nat.add_right_comm]
    exact (hcrt q hq).add hd
  have hAllSmall {q : ℕ} (hq : q ∈ primes w) : q ∈ T :=
    mem_union_left _ (primes_mono (hwz.trans hzx) hq)
  have hAllLarge {q : ℕ} (hq : q.Prime) (hq' : q ≤ x) : q ∈ T :=
    mem_union_left _ (mem_primes.mpr ⟨hq', hq⟩)
  have hDivByResidue {q h : ℕ} (hq : q ∈ T) (hr : h % q = r₀ q) : q ∣ N + h := by
    have hd : q ∣ N + r₀ q := (dvd_pow_self q (by decide : (2 : ℕ) ≠ 0)).trans (hDiv hq)
    have hmod : h ≡ r₀ q [MOD q] := hr ▸ (Nat.mod_modEq h q).symm
    exact Nat.modEq_zero_iff_dvd.mp
      ((Nat.ModEq.refl N).add hmod |>.trans (Nat.modEq_zero_iff_dvd.mpr hd))
  have hSmallHit {h : ℕ} {q : primes w} (hq : q ∈ smallHits a h) : q.val ∣ N + h :=
    hDivByResidue (hAllSmall q.prop) (by rw [hSmall q.prop, (mem_filter.mp hq).2]; rfl)
  have hMainHit {h q : ℕ} (hq : q.Prime) (hqw : w < q) (hqz : q ≤ z) (hqh : q ∣ h) :
      q ∣ N + h := hDivByResidue (hAllLarge hq (hqz.trans hzx))
    ((Nat.dvd_iff_mod_eq_zero.mp hqh).trans (hZero hqw hqz).symm)
  have hTwo {h p q : ℕ} (hh : 0 < h) (hp : p ∈ T) (hq : q ∈ T) (hne : p ≠ q)
      (hpD : p ∣ N + h) (hqD : q ∣ N + h) : 2 < Ω (N + h) := by
    have pp := hprime _ hp
    have qp := hprime _ hq
    have hcop := (Nat.coprime_primes pp qp).mpr hne
    have hf : Ω (p * q) = 2 := by
      rw [ArithmeticFunction.cardFactors_mul pp.ne_zero qp.ne_zero,
        ArithmeticFunction.cardFactors_apply_prime pp, ArithmeticFunction.cardFactors_apply_prime qp]
    have hProdM : p * q ∣ M := hcop.mul_dvd_of_dvd_of_dvd
      ((dvd_pow_self p (by decide : (2 : ℕ) ≠ 0)).trans (hDivM hp))
      ((dvd_pow_self q (by decide : (2 : ℕ) ≠ 0)).trans (hDivM hq))
    exact omega_gt_two_of_proper_dvd hf (hcop.mul_dvd_of_dvd_of_dvd hpD hqD)
      (lt_of_le_of_lt ((Nat.le_of_dvd hM hProdM).trans hNM) (by omega))
  have hSquare {h q : ℕ} (hh : 0 < h) (hq : q ∈ T) (hqD : q ^ 2 ∣ N + h) :
      2 < Ω (N + h) :=
    omega_gt_two_of_proper_dvd (ArithmeticFunction.cardFactors_apply_prime_pow (hprime _ hq)) hqD
      (lt_of_le_of_lt ((Nat.le_of_dvd hM (hDivM hq)).trans hNM) (by omega))
  refine ⟨N, hNy, ?_, ?_⟩
  · have hlt : N₀ < M := hN₀
    have hNbound : N + 1 ≤ (y + 2) * M := by
      dsimp [N]
      rw [show y + 2 = (y + 1) + 1 by omega, Nat.add_mul (y + 1) 1 M, Nat.one_mul]
      omega
    have hLogs : Real.log (M : ℝ) ≤ 4 * (x : ℝ) + 4 * Real.log y * (F.card : ℝ) := by
      unfold M T
      rw [prod_union hP'disj, Nat.cast_mul, Real.log_mul]
      · simp only [Nat.cast_prod]
        rw [Real.log_prod, Real.log_prod]
        · simp_rw [Nat.cast_pow, Real.log_pow, Nat.cast_ofNat, ← mul_sum]
          have h4 : Real.log 4 ≤ 2 := by
            rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
            norm_num
            linarith [log_two_bounds.2]
          have hbase := (sum_log_primes x).trans (mul_le_mul_of_nonneg_right h4 (Nat.cast_nonneg _))
          have hpatchlog : (∑ q ∈ P', Real.log (q : ℝ)) ≤ (F.card : ℝ) * (2 * Real.log y) := by
            have hh : P'.card = F.card := by
              unfold P'
              rw [card_image_of_injective _ hpinj, card_attach]
            rw [← hh, ← nsmul_eq_mul, ← sum_const]
            refine sum_le_sum fun q hq ↦ ?_
            obtain ⟨h,_,rfl⟩ := mem_image.mp hq
            have ht := Real.log_le_log (Nat.cast_pos.mpr (hp h).2.2.pos)
              (by exact_mod_cast (hp h).2.1 : (p h : ℝ) ≤ (y : ℝ) ^ 2)
            rw [Real.log_pow] at ht
            exact_mod_cast ht
          linarith only [hbase, hpatchlog]
        all_goals
          intro q hq
          exact Nat.cast_ne_zero.mpr (pow_ne_zero _ (hprime q (by simp [T, hq])).ne_zero)
      all_goals
        exact Nat.cast_ne_zero.mpr (prod_ne_zero_iff.mpr fun q hq ↦
          pow_ne_zero _ (hprime q (by simp [T, hq])).ne_zero)
    calc
      _ ≤ Real.log (((y + 2) * M : ℕ) : ℝ) :=
        Real.log_le_log (by positivity) (by exact_mod_cast hNbound)
      _ = Real.log ((y : ℝ) + 2) + Real.log (M : ℝ) := by
        push_cast
        rw [Real.log_mul (by positivity) (Nat.cast_ne_zero.mpr hM.ne')]
      _ ≤ _ := by linarith
  · intro h hh
    have hh0 : 0 < h := (mem_Icc.mp hh).1
    by_cases hf : h ∈ F
    · let q : ℕ := p ⟨h,hf⟩
      have hq : q ∈ T := mem_union_right _ (mem_image.mpr ⟨⟨h,hf⟩, mem_attach _ _, rfl⟩)
      have hd := hDiv hq
      rw [hPatch ⟨h,hf⟩] at hd
      exact hSquare hh0 hq hd
    rcases offset_classification hy hHw hwz hh with hcase | hcase | hcase
    · have ht := h₀ h hcase hf
      obtain ⟨p, hp, q, hq, hne⟩ := one_lt_card.mp ht
      exact hTwo hh0 (hAllSmall p.prop) (hAllSmall q.prop) (fun he ↦ hne (Subtype.ext he))
        (hSmallHit hp) (hSmallHit hq)
    · obtain ⟨p, hp, hpw, hpz, hpd, hm⟩ := hcase
      rcases h₁ h hm hf with ⟨q, hq⟩ | ⟨j,hj,q,hq,hr⟩
      · have hn : q.val ≠ p := (lt_of_le_of_lt (mem_primes.mp q.prop).1 hpw).ne
        exact hTwo hh0 (hAllSmall q.prop) (hAllLarge hp (hpz.trans hzx)) hn
          (hSmallHit hq) (hMainHit hp hpw hpz hpd)
      · have hq' := b j |>.properties q hq
        have hN : p ≠ q := (hpz.trans_lt (hband j hj q hq).1).ne
        have hqT := hAllLarge hq'.1 (hband j hj q hq).2
        exact hTwo hh0 (hAllLarge hp (hpz.trans hzx)) hqT hN (hMainHit hp hpw hpz hpd)
          (hDivByResidue hqT (hr.trans (hLarge hj hq).symm))
    · obtain ⟨p, q, hp, hq, hpw, hpz, hqw, hqz, hmul⟩ := hcase
      have hpT := hAllLarge hp (hpz.trans hzx)
      by_cases he : p = q
      · subst q
        have hsq : p ^ 2 ∣ h := by simpa [pow_two] using hmul
        have hdiv := hDiv hpT
        rw [hZero hpw hpz, Nat.add_zero] at hdiv
        exact hSquare hh0 hpT (hdiv.add hsq)
      · exact hTwo hh0 hpT (hAllLarge hq (hqz.trans hzx)) he
          (hMainHit hp hpw hpz ((dvd_mul_right p q).trans hmul))
          (hMainHit hq hqw hqz ((dvd_mul_left q p).trans hmul))

/- Choose sieve ranges and bound the logarithm of the modulus. -/
private def scaleBase : ℕ := 1024

private theorem scaleBase_eq : scaleBase = 2 ^ 10 := by decide

private theorem scaleBase_log : Real.log (scaleBase : ℝ) ≤ 10 := by
  rw [scaleBase_eq, Nat.cast_pow, Nat.cast_two, Real.log_pow]
  norm_num
  linarith [log_two_bounds.2]

private theorem scaleBase_pos : 0 < scaleBase := by decide

private theorem log_scale_floor {y H z : ℕ} (hy : y = H * z) (hH : 0 < H) (hy0 : 0 < y)
    (h : H ^ 2 ≤ y) : (Real.log (y : ℝ)) / 2 ≤ Real.log (z : ℝ) := by
  have hz : H ≤ z := by
    rw [hy, pow_two] at h
    exact Nat.le_of_mul_le_mul_left h hH
  have hsq : y ≤ z ^ 2 := by rw [hy, pow_two]; exact Nat.mul_le_mul_right _ hz
  have hl := Real.log_le_log (Nat.cast_pos.mpr hy0) (by exact_mod_cast hsq : (y : ℝ) ≤ (z : ℝ) ^ 2)
  rw [Real.log_pow] at hl
  norm_num at hl
  linarith only [hl]

private theorem band_pool_bound {y z : ℕ} (hz : 12 ≤ z) (hzy : scaleBase * z ≤ y)
    (hLog : Real.log (y : ℝ) / 2 ≤ Real.log (z : ℝ)) :
    ((primes (scaleBase * z) \ primes z).card : ℝ) ≥ (scaleBase * (z : ℝ)) / (32 * Real.log y) := by
  have hzy' : z ≤ scaleBase * z := Nat.le_mul_of_pos_left _ scaleBase_pos
  have hy' : 12 ≤ y := hz.trans (hzy'.trans hzy)
  have hlogy : 0 < Real.log (y : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  have hl := prime_count_lower (hz.trans hzy')
  have hu := prime_count_upper (show 1 < z by omega)
  have hzPos : 0 < Real.log (z : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < z by omega))
  have hll : (scaleBase * (z : ℝ)) / (16 * Real.log y) ≤ ((primes (scaleBase * z)).card : ℝ) := by
    have h := Real.log_le_log (Nat.cast_pos.mpr (by omega : 0 < scaleBase * z)) (Nat.cast_le.mpr hzy)
    rw [← Nat.cast_mul]
    exact (div_le_div_of_nonneg_left (by positivity)
      (mul_pos (by norm_num) (Real.log_pos (by exact_mod_cast (show 1 < scaleBase * z by omega))))
      (mul_le_mul_of_nonneg_left h (by norm_num))).trans hl
  have huu : ((primes z).card : ℝ) ≤ 16 * (z : ℝ) / Real.log y := by
    refine hu.trans ?_
    calc
      _ ≤ (8 * (z : ℝ)) / (Real.log y / 2) := div_le_div_of_nonneg_left (by positivity) (by positivity) hLog
      _ = _ := by ring
  rw [card_sdiff_of_subset (primes_mono hzy'), Nat.cast_sub (card_le_card (primes_mono hzy'))]
  norm_num [scaleBase] at hll ⊢
  have he1 : (1024 : ℝ) * (z : ℝ) / (16 * Real.log y) = 64 * ((z : ℝ) / Real.log y) := by
    field_simp [hlogy.ne']
    norm_num
  have he2 : (1024 : ℝ) * (z : ℝ) / (32 * Real.log y) = 32 * ((z : ℝ) / Real.log y) := by
    field_simp [hlogy.ne']
    norm_num
  rw [he1] at hll
  rw [he2]
  linarith only [hll, huu, show (0 : ℝ) ≤ (z : ℝ) / Real.log y by positivity,
    show 16 * (z : ℝ) / Real.log y = 16 * ((z : ℝ) / Real.log y) by ring]

private def buildBand {y w z H : ℕ} (hH : 4 ≤ H) (hB : H ^ 10 ≤ w)
    (hz : w < z) (hz12 : 12 ≤ z) (hy : y = H * z) (hHz : H ≤ z)
    (hUpper : scaleBase * z ≤ y) (hLog : Real.log (y : ℝ) / 2 ≤ Real.log (z : ℝ))
    (hHuge : 16 * (scaleBase : ℝ) ≤ Real.log y) : Band y w := by
  let Q := primes (scaleBase * z) \ primes z
  have hQbound := band_pool_bound hz12 hUpper hLog
  have hzPos : 0 < z := by omega
  have hy1 : 1 < y := by rw [hy]; nlinarith
  have hylog : 0 < Real.log (y : ℝ) := Real.log_pos (by exact_mod_cast hy1)
  have hQ : Q.Nonempty := card_pos.mp (Nat.cast_pos.mp
    (lt_of_lt_of_le (div_pos (by
      have h : (0 : ℝ) < scaleBase := Nat.cast_pos.mpr scaleBase_pos
      exact mul_pos h (Nat.cast_pos.mpr hzPos)) (mul_pos (by norm_num) hylog)) hQbound))
  refine ⟨H, Q, scaleBase * z, hH, hB, hQ, ?_⟩
  intro q hq
  obtain ⟨hqu, hqp⟩ := mem_primes.mp (mem_sdiff.mp hq).1
  have hqz : z < q := lt_of_not_ge fun h ↦ (mem_sdiff.mp hq).2 (mem_primes.mpr ⟨h, hqp⟩)
  have h1 := Nat.mul_lt_mul_of_pos_left hqz (by omega : 0 < H)
  have h2 : y ≤ z ^ 2 := by rw [hy, pow_two]; exact Nat.mul_le_mul_right _ hHz
  have hCard : Q.card ≤ q := by
    have hzu : z ≤ scaleBase * z := Nat.le_mul_of_pos_left _ scaleBase_pos
    have hZlog : Real.log (z : ℝ) ≤ Real.log ((scaleBase * z : ℕ) : ℝ) :=
      Real.log_le_log (Nat.cast_pos.mpr hzPos) (Nat.cast_le.mpr hzu)
    have hcmp := hLog.trans hZlog
    have hpop := prime_count_upper (show 1 < scaleBase * z from (show 1 < z by omega).trans_le hzu)
    have hbound : (Q.card : ℝ) ≤ (16 * (scaleBase : ℝ) * (z : ℝ)) / Real.log y := calc
      _ ≤ ((primes (scaleBase * z)).card : ℝ) := by exact_mod_cast card_le_card (sdiff_subset (s := primes (scaleBase * z)))
      _ ≤ _ := hpop
      _ ≤ (8 * ((scaleBase * z : ℕ) : ℝ)) / (Real.log y / 2) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hcmp
      _ = _ := by push_cast; ring
    have hle : 16 * (scaleBase : ℝ) * (z : ℝ) / Real.log y ≤ z := by
      apply (div_le_iff₀ hylog).mpr
      simpa only [mul_comm (Real.log (y : ℝ)) (z : ℝ)] using
        mul_le_mul_of_nonneg_right hHuge (Nat.cast_nonneg z)
    exact (Nat.cast_le.mp (hbound.trans hle)).trans hqz.le
  exact ⟨hqp, hz.trans hqz, hy ▸ h1, h2.trans_lt (Nat.pow_lt_pow_left hqz (by decide)), hCard, hqu⟩

private theorem harmonic_two_powers (m n : ℕ) :
    (n : ℝ) / 2 ≤ ∑ j ∈ Ico ((2 : ℕ) ^ m) (2 ^ (m + n)), (j : ℝ)⁻¹ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h₁ : 2 ^ m ≤ (2 : ℕ) ^ (m + n) := Nat.pow_le_pow_right (by decide) (by omega)
    have h₂ : 2 ^ (m + n) ≤ (2 : ℕ) ^ (m + (n + 1)) := Nat.pow_le_pow_right (by decide) (by omega)
    let b := 2 ^ (m + n)
    have hb0 : 0 < b := by dsimp [b]; positivity
    have hu : (2 : ℕ) ^ (m + (n + 1)) = 2 * b := by rw [← Nat.add_assoc, pow_succ']
    have hlocal : (1 : ℝ) / 2 ≤ ∑ j ∈ Ico b (2 * b), (j : ℝ)⁻¹ := by
      have hcard : (Ico b (2 * b)).card = b := by rw [Nat.card_Ico]; omega
      have hbound : (∑ _j ∈ Ico b (2 * b), (2 * (b : ℝ))⁻¹) ≤ ∑ j ∈ Ico b (2 * b), (j : ℝ)⁻¹ := by
        refine sum_le_sum fun j hj ↦ ?_
        have hj0 : (0 : ℝ) < j := Nat.cast_pos.mpr (hb0.trans_le (mem_Ico.mp hj).1)
        have hj2 : (j : ℝ) ≤ 2 * (b : ℝ) := by exact_mod_cast (mem_Ico.mp hj).2.le
        exact (inv_le_inv₀ (by positivity) hj0).mpr hj2
      rw [sum_const, nsmul_eq_mul, hcard] at hbound
      have hval : (b : ℝ) * (2 * (b : ℝ))⁻¹ = 1 / 2 := by field_simp
      rwa [hval] at hbound
    rw [← Ico_union_Ico_eq_Ico h₁ h₂, sum_union (Ico_disjoint_Ico_consecutive _ _ _), hu]
    change (↑(n + 1) : ℝ) / 2 ≤ (∑ j ∈ Ico (2 ^ m) b, (j : ℝ)⁻¹) + ∑ j ∈ Ico b (2*b), (j : ℝ)⁻¹
    push_cast
    linarith only [ih, hlocal]

private theorem exp_neg_le_inv {x : ℝ} (hx : 0 < x) : Real.exp (-x) ≤ x⁻¹ := by
  rw [Real.exp_neg]
  exact (inv_le_inv₀ (Real.exp_pos x) hx).mpr (by linarith [Real.add_one_le_exp x])

private theorem band_error_uniform {y w m L : ℕ} (b : Band y w)
    (hm : 1 ≤ m) (hL : m ≤ L) (hH : m ≤ b.height) (hHL : b.height ≤ L)
    (hy : 0 < y) (hlog : 0 < Real.log (y : ℝ))
    (hQ : (y : ℝ) / (32 * (b.height : ℝ) * Real.log y) ≤ (b.pool.card : ℝ))
    (hLlog : Real.log (y : ℝ) ≤ (L : ℝ) ^ 101)
    (hLsqrt : (L : ℝ) ^ 104 ≤ Real.sqrt y)
    (hWs : (euler w 1) ^ (2 * b.height) ≤ Real.sqrt y)
    (hWe : (euler w 1) ^ (2 * b.height) ≤ Real.exp ((b.height : ℝ) ^ 3 / 4))
    (hle : Real.log y ≤ Real.exp ((b.height : ℝ) ^ 3 / 4)) :
    (euler w 1) ^ (2 * b.height) * badBound b.height y ≤ (20000 / (m : ℝ)) * b.pool.card := by
  let H : ℝ := b.height
  let E := (euler w 1) ^ (2 * b.height)
  let Y : ℝ := y
  have hH1 : 1 ≤ H := Nat.one_le_cast.mpr (hm.trans hH)
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast hm.trans hL
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hHL' : H ≤ (L : ℝ) := Nat.cast_le.mpr hHL
  have hmH : (m : ℝ) ≤ H := Nat.cast_le.mpr hH
  have hml : (m : ℝ) ≤ L := by exact_mod_cast hL
  have hY0 : 0 < Y := Nat.cast_pos.mpr hy
  have hD : 0 < 32 * H * Real.log Y := by positivity
  have hE : 0 ≤ E := pow_nonneg (euler_pos w zero_lt_one).le _
  have hlog' : 0 < Real.log Y := hlog
  have h1 : (32 * H * Real.log Y / Y) * E ≤ 32 / (m : ℝ) := by
    have hm0 : (0 : ℝ) < m := by positivity
    have hY := Real.sq_sqrt hY0.le
    have hs := Real.sqrt_pos.mpr hY0
    calc
      _ ≤ (32 * H * Real.log Y / Y) * Real.sqrt Y := mul_le_mul_of_nonneg_left hWs
        (by positivity)
      _ = 32 * H * Real.log Y / Real.sqrt Y := by
        field_simp [hY0.ne', hs.ne']
        rw [hY]
      _ ≤ 32 * (L : ℝ) * (L : ℝ) ^ 101 / (L : ℝ) ^ 104 := by
        have hh : 32 * H * Real.log Y ≤ 32 * (L : ℝ) * (L : ℝ) ^ 101 := by gcongr
        exact (div_le_div_of_nonneg_right hh hs.le).trans
          (div_le_div_of_nonneg_left (by positivity) (by positivity) hLsqrt)
      _ ≤ _ := by
        rw [div_le_div_iff₀ (by positivity) hm0]
        have hpow : (L : ℝ) ^ 103 ≤ (L : ℝ) ^ 104 := pow_le_pow_right₀ hL1 (by decide)
        have hm : (L : ℝ) ^ 102 * m ≤ (L : ℝ) ^ 103 := by
          have hh := mul_le_mul_of_nonneg_left hml (pow_nonneg (zero_le_one.trans hL1) 102)
          rwa [← pow_succ] at hh
        have ht := mul_le_mul_of_nonneg_left (hm.trans hpow) (show (0 : ℝ) ≤ 32 by norm_num)
        linarith only [ht, show (32 * (L : ℝ) * (L : ℝ) ^ 101) * m =
           32 * ((L : ℝ) ^ 102 * m) by ring]
  have h2 : (32 * H * Real.log Y / Y) * E * (4 * (2 * H + 1) ^ 2 * Y * Real.exp (-H ^ 3)) ≤
      18432 / (m : ℝ) := by
    have hsq : (2 * H + 1) ^ 2 ≤ (3 * H) ^ 2 :=
      pow_le_pow_left₀ (by positivity) (by linarith) _
    have hExp : 32 * H * Real.log Y * E * (4 * (2 * H + 1) ^ 2) ≤
        1152 * H ^ 3 * (Real.exp (H ^ 3 / 4) * Real.exp (H ^ 3 / 4)) := by
      calc
        _ ≤ 32 * H * Real.exp (H ^ 3 / 4) * Real.exp (H ^ 3 / 4) * (4 * (3 * H) ^ 2) := by
          gcongr
        _ = _ := by ring
    have he : H ^ 3 * Real.exp (-(H ^ 3 / 2)) ≤ 16 / (m : ℝ) := by
      have hv : 0 < H ^ 3 / 4 := by positivity
      have hb := exp_neg_le_inv hv
      have hf : H ^ 3 * Real.exp (-(H ^ 3 / 4)) ≤ 4 := by
        refine (mul_le_mul_of_nonneg_left hb (by positivity)).trans_eq ?_
        field_simp
      have hc : (m : ℝ) ≤ H ^ 3 := hmH.trans ((by simp : H ^ 1 = H).ge.trans
        (pow_le_pow_right₀ hH1 (by decide)))
      calc
        _ = (H ^ 3 * Real.exp (-(H ^ 3 / 4))) * Real.exp (-(H ^ 3 / 4)) := by
          rw [mul_assoc, ← Real.exp_add]
          congr 2
          ring
        _ ≤ 4 * (H ^ 3 / 4)⁻¹ :=
          mul_le_mul hf hb (Real.exp_nonneg _) (by norm_num)
        _ = 16 / H ^ 3 := by ring
        _ ≤ _ := div_le_div_of_nonneg_left (by norm_num) (by positivity) hc
    calc
      _ = (32 * H * Real.log Y * E * (4 * (2 * H + 1) ^ 2)) * Real.exp (-H ^ 3) := by
        field_simp [hY0.ne']
      _ ≤ _ := (mul_le_mul_of_nonneg_right hExp (Real.exp_nonneg _)).trans ?_
    rw [← Real.exp_add, mul_assoc (1152 * H ^ 3), ← Real.exp_add]
    rw [show H ^ 3 / 4 + H ^ 3 / 4 + -H ^ 3 = -(H ^ 3 / 2) by ring, mul_assoc]
    exact (mul_le_mul_of_nonneg_left he (by norm_num)).trans_eq (by ring)
  have hSum : (32 * H * Real.log Y / Y) * (E * badBound b.height y) ≤ 20000 / (m : ℝ) := by
    unfold badBound
    change (32 * H * Real.log Y / Y) * (E * (1 + 4 * (2 * H + 1) ^ 2 * Y * Real.exp (-H ^ 3))) ≤ _
    rw [mul_add, mul_one, mul_add, ← mul_assoc]
    have hle' := add_le_add h1 h2
    exact hle'.trans (by
      rw [← add_div]
      exact div_le_div_of_nonneg_right (by norm_num) (Nat.cast_nonneg m))
  have hrat : E * badBound b.height y ≤ (20000 / (m : ℝ)) * (Y / (32 * H * Real.log Y)) := by
    rw [← mul_div_assoc]
    apply (le_div_iff₀ hD).mpr
    have he := (div_le_iff₀ hY0).mp (by
      simpa only [div_mul_eq_mul_div] using hSum :
        (32 * H * Real.log Y * (E * badBound b.height y)) / Y ≤ 20000 / (m : ℝ))
    exact mul_comm (E * badBound b.height y) (32 * H * Real.log Y) ▸ he
  exact hrat.trans (mul_le_mul_of_nonneg_left hQ (by positivity))

private theorem enough_patch_primes {y : ℕ} (hy : 16384 ≤ y) :
    y ≤ (primes (y ^ 2) \ primes y).card := by
  have hy1 : 1 < y := by omega
  have hlog : 0 < Real.log (y : ℝ) := Real.log_pos (by exact_mod_cast hy1)
  have hy0 : (0 : ℝ) < y := by positivity
  have hsqrt : (128 : ℝ) ≤ Real.sqrt y := by
    rw [Real.le_sqrt (by norm_num) hy0.le]
    exact_mod_cast hy
  have hLogs : Real.log (y : ℝ) ≤ 2 * Real.sqrt y := by
    rw [Real.sqrt_eq_rpow]
    have h := Real.log_le_rpow_div hy0.le (by norm_num : (0 : ℝ) < 1 / 2)
    linarith
  have hlog' : 64 * Real.log (y : ℝ) ≤ y := by
    calc
      _ ≤ 128 * Real.sqrt y := by linarith
      _ ≤ (Real.sqrt y) ^ 2 := by nlinarith [mul_nonneg (show 0 ≤ Real.sqrt y - 128 by linarith) (Real.sqrt_nonneg y)]
      _ = _ := Real.sq_sqrt hy0.le
  have hYY : y ≤ y ^ 2 := by nlinarith
  have hll := prime_count_lower (n := y ^ 2) (by nlinarith : 12 ≤ y ^ 2)
  push_cast at hll
  rw [Real.log_pow] at hll
  have hh : (2 : ℝ) * y ≤ ((primes (y ^ 2)).card : ℝ) := by
    refine le_trans ?_ hll
    apply (le_div_iff₀ (show 0 < 16 * (↑(2 : ℕ) * Real.log (y : ℝ)) by positivity)).mpr
    norm_num
    nlinarith only [mul_le_mul_of_nonneg_left hlog' hy0.le]
  have hP : (primes y).card ≤ y := by
    calc
      _ ≤ (Icc 1 y).card := card_le_card (fun q hq ↦
        mem_Icc.mpr ⟨(mem_primes.mp hq).2.one_le, (mem_primes.mp hq).1⟩)
      _ = _ := by simp [Nat.card_Icc]
  rw [card_sdiff_of_subset (primes_mono hYY)]
  have hNat : 2 * y ≤ (primes (y ^ 2)).card := by exact_mod_cast hh
  omega

private theorem real_atTop_nat (t : ℝ) : ∀ᶠ n : ℕ in atTop, t ≤ (n : ℝ) :=
  tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop t)

private theorem eulerConst_ge_one : 1 ≤ eulerConst := by
  unfold eulerConst
  have h := Real.one_le_exp_iff.mpr (show 0 ≤ 8 * Real.exp 1 by positivity)
  linarith

private theorem big_power_bound {L : ℕ} (h : 2 ≤ L) : L ^ 104 ≤ (2 : ℕ) ^ (L ^ 100) := by
  calc
    _ ≤ ((2 : ℕ) ^ L) ^ 104 := Nat.pow_le_pow_left Nat.lt_two_pow_self.le _
    _ = (2 : ℕ) ^ (L * 104) := by rw [pow_mul]
    _ ≤ _ := by
      apply Nat.pow_le_pow_right (by decide)
      have h104 : 104 ≤ L ^ 7 := (by decide : 104 ≤ (2 : ℕ) ^ 7).trans (Nat.pow_le_pow_left h _)
      calc
        L * 104 ≤ L ^ 7 * L := by simpa only [mul_comm L 104] using Nat.mul_le_mul_right L h104
        _ = L ^ 8 := (pow_succ L 7).symm
        _ ≤ _ := Nat.pow_le_pow_right (by omega) (by decide)

private theorem scale_pow_axis (m : ℕ) : m ^ 2 ≤ scaleBase ^ m := by
  calc
    _ ≤ ((2 : ℕ) ^ m) ^ 2 := Nat.pow_le_pow_left Nat.lt_two_pow_self.le _
    _ ≤ ((2 : ℕ) ^ m) ^ 10 := Nat.pow_le_pow_right (by positivity) (by decide)
    _ = _ := by rw [scaleBase_eq, ← pow_mul, ← pow_mul, mul_comm m 10]

set_option maxHeartbeats 0 in
private theorem large_holes (η : ℝ) (hη : 0 < η) (hη1 : η ≤ 1) (Y₀ : ℕ) :
    ∃ (y N : ℕ), Y₀ ≤ y ∧ y ≤ N ∧ Real.log ((N : ℝ) + 1) ≤ η * y ∧
      ∀ h ∈ Icc 1 y, 2 < Ω (N + h) := by
  classical
  let C := eulerConst
  let c := 1002 + |Real.log C|
  have hC : 0 < C := eulerConst_pos
  have hC1 : 1 ≤ C := eulerConst_ge_one
  have hc : 1002 ≤ c := by dsimp [c]; linarith [abs_nonneg (Real.log C)]
  have hc' : 0 < c := by linarith
  let τ := η / (32768 * C)
  have hτ : 0 < τ := div_pos hη (by positivity)
  have hτ1 : τ ≤ 1 := (div_le_one (by positivity : 0 < 32768 * C)).mpr (by linarith)
  obtain ⟨K, hK⟩ := exists_nat_ge (max 1 (128000 * C / (4 * τ)))
  have hK1 : (1 : ℝ) ≤ K := (le_max_left _ _).trans hK
  have hKpos : 0 < K := by exact_mod_cast (show (0 : ℝ) < K from zero_lt_one.trans_le hK1)
  let s : ℝ := 16 * K
  let T := Real.exp (8 * Real.exp s * s)
  have hs : 0 < s := by dsimp [s]; positivity
  have hT : 0 ≤ T := Real.exp_nonneg _
  have htlim : Tendsto (fun u : ℕ ↦ T * ((u : ℝ) * Real.exp (-(u : ℝ)))) atTop (𝓝 0) := by
    have h := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp tendsto_natCast_atTop_atTop
    simpa using h.const_mul T
  have hmin : 0 < min 1 (η / (384 * c)) := lt_min zero_lt_one (div_pos hη (by positivity))
  have huv := htlim.eventually (gt_mem_nhds hmin)
  have hsome : ∀ᶠ u : ℕ in atTop, max Y₀ 16384 ≤ u ∧
      (8 * c ≤ (u : ℝ)) ∧ (4 * s ≤ (u : ℝ)) ∧
      32 * (scaleBase : ℝ) ≤ (u : ℝ) ∧ 20000 / τ ≤ (u : ℝ) ∧
      200000 * c / η ≤ (u : ℝ) ∧ (8 * (scaleBase : ℝ) + 8) / η ≤ (u : ℝ) ∧
      T * ((u : ℝ) * Real.exp (-(u : ℝ))) ≤ min 1 (η / (384 * c)) := by
    filter_upwards [eventually_ge_atTop (max Y₀ 16384), real_atTop_nat (8 * c),
      real_atTop_nat (4 * s), real_atTop_nat (32 * ↑scaleBase), real_atTop_nat (20000 / τ),
      real_atTop_nat (200000 * c / η), real_atTop_nat ((8 * ↑scaleBase + 8) / η), huv]
      with u h1 h2 h3 h4 h5 h6 h7 h8
    exact ⟨h1, h2, h3, h4, h5, h6, h7, h8.le⟩
  obtain ⟨u, hu, huC, hus, huR, huErr, huDef, huCost, huTilt⟩ := hsome.exists
  have hu0 : 0 < u := by omega
  have hu2 : 2 ≤ u := by omega
  have hUR : (0 : ℝ) < u := Nat.cast_pos.mpr hu0
  -- The bands range from m to m². Their contributions sum to a constant
  -- multiple of K, while the smooth-number error tends to zero as u grows.
  let m := 2 ^ (K * u)
  let L := scaleBase ^ (m ^ 2)
  let w := 2 ^ (L ^ 100)
  let y := w ^ u
  have hum : u ≤ m := calc
    _ ≤ (2 : ℕ) ^ u := Nat.lt_two_pow_self.le
    _ ≤ _ := Nat.pow_le_pow_right (by decide) (by have := Nat.mul_le_mul_right u hKpos; simpa)
  have hm1 : 1 ≤ m := hu0.trans_le hum
  have hm2 : 2 ≤ m := hu2.trans hum
  have hmL : m ^ 2 ≤ L := by
    calc
      _ ≤ (2 : ℕ) ^ (m ^ 2) := Nat.lt_two_pow_self.le
      _ ≤ _ := Nat.pow_le_pow_left (by decide : 2 ≤ scaleBase) _
  have hLm : m ≤ L := (by nlinarith : m ≤ m ^ 2).trans hmL
  have hL2 : 2 ≤ L := hm2.trans hLm
  have hL104 : L ^ 104 ≤ w := big_power_bound hL2
  have hLpow : L ^ 2 ≤ L ^ 104 := Nat.pow_le_pow_right (by omega) (by decide)
  have hLw : L < w := (show L < L ^ 2 by nlinarith).trans_le (hLpow.trans hL104)
  have hw2 : 2 ≤ w := hL2.trans hLw.le
  have hwY : w ^ 2 ≤ y := Nat.pow_le_pow_right (by omega) hu2
  have hmy : m ≤ y := hLm.trans (hLw.le.trans ((by nlinarith : w ≤ w ^ 2).trans hwY))
  have hY₀ : Y₀ ≤ y := (le_max_left _ _).trans (hu.trans (hum.trans hmy))
  have hybig : 16384 ≤ y := (le_max_right _ _).trans (hu.trans (hum.trans hmy))
  have hy0 : 0 < y := by omega
  have hYR : (0 : ℝ) < y := Nat.cast_pos.mpr hy0
  have hlogy : 0 < Real.log (y : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  have hlogw : 0 < Real.log (w : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < w by omega))
  have hly : Real.log (y : ℝ) = (u : ℝ) * Real.log w := by
    change Real.log ((w ^ u : ℕ) : ℝ) = _
    rw [Nat.cast_pow, Real.log_pow]
  have hlw : Real.log (w : ℝ) = (L : ℝ) ^ 100 * Real.log 2 := by
    change Real.log (((2 : ℕ) ^ (L ^ 100) : ℕ) : ℝ) = _
    rw [Nat.cast_pow, Nat.cast_two, Real.log_pow, Nat.cast_pow]
  have hlL : Real.log (L : ℝ) = (m : ℝ) ^ 2 * Real.log scaleBase := by
    change Real.log ((scaleBase ^ (m ^ 2) : ℕ) : ℝ) = _
    rw [Nat.cast_pow, Real.log_pow, Nat.cast_pow]
  have hLogL : Real.log (L : ℝ) ≤ 10 * (m : ℝ) ^ 2 := by
    rw [hlL, mul_comm (10 : ℝ)]
    exact mul_le_mul_of_nonneg_left scaleBase_log (sq_nonneg _)
  have hMR : (m : ℝ) ≤ L := by exact_mod_cast hLm
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm1
  have hUR' : (u : ℝ) ≤ m := by exact_mod_cast hum
  have hM2L : (m : ℝ) ^ 2 ≤ L := by exact_mod_cast hmL
  have hL1 : (1 : ℝ) ≤ L := hmR.trans hMR
  have hL0 : (0 : ℝ) < L := zero_lt_one.trans_le hL1
  have hlogwLow : (L : ℝ) ^ 100 / 2 ≤ Real.log w := by
    rw [hlw, div_eq_mul_one_div]
    exact mul_le_mul_of_nonneg_left (by linarith [log_two_bounds.1]) (pow_nonneg hL0.le _)
  have hlogwHigh : Real.log (w : ℝ) ≤ (L : ℝ) ^ 100 := by
    rw [hlw]
    exact mul_le_of_le_one_right (pow_nonneg hL0.le _) log_two_bounds.2
  have hLlog : Real.log (y : ℝ) ≤ (L : ℝ) ^ 101 := by
    rw [hly, pow_succ, mul_comm ((L : ℝ) ^ 100)]
    exact mul_le_mul (hUR'.trans hMR) hlogwHigh hlogw.le hL0.le
  have huLn : (u : ℝ) ≤ Real.log w := by
    have hle := pow_le_pow_right₀ hL1 (show 2 ≤ 100 by decide)
    have hLbig : 2 ≤ (L : ℝ) := by exact_mod_cast hL2
    have hl := mul_nonneg (show 0 ≤ (L : ℝ) - 2 by linarith) hL0.le
    nlinarith only [hle, hl, hUR',hMR,hlogwLow]
  have hlogHuge : 16 * (scaleBase : ℝ) ≤ Real.log y := by
    rw [hly]
    have h1 : 1 ≤ (u : ℝ) := by exact_mod_cast hu0
    have hle := le_mul_of_one_le_left hlogw.le h1
    linarith only [huR, huLn, hle]
  have hLsqrt : (L : ℝ) ^ 104 ≤ Real.sqrt y := by
    have hr : (w : ℝ) ^ 2 ≤ y := by exact_mod_cast hwY
    exact (show (L : ℝ) ^ 104 ≤ w from by exact_mod_cast hL104).trans
      ((Real.le_sqrt (Nat.cast_nonneg w) hYR.le).mpr hr)
  have hwSqrt : (w : ℝ) ≤ Real.sqrt y :=
    (Real.le_sqrt (Nat.cast_nonneg _) hYR.le).mpr (by exact_mod_cast hwY)
  have hLogLogW : Real.log (Real.log (w : ℝ)) ≤ 1000 * (m : ℝ) ^ 2 := by
    rw [hlw, Real.log_mul (pow_ne_zero _ hL0.ne') (by linarith [log_two_bounds.1]), Real.log_pow]
    have hloglog2 := Real.log_nonpos (by linarith [log_two_bounds.1] : 0 ≤ Real.log 2) log_two_bounds.2
    norm_num
    linarith only [hLogL, hloglog2]
  have hLogLogY : Real.log (Real.log (y : ℝ)) ≤ c * (m : ℝ) ^ 2 := by
    rw [hly, Real.log_mul hUR.ne' hlogw.ne']
    have hlogu : Real.log (u : ℝ) ≤ u := (Real.log_le_sub_one_of_pos hUR).trans (sub_le_self _ zero_le_one)
    have huM : (u : ℝ) ≤ (m : ℝ) ^ 2 := hUR'.trans (by nlinarith)
    have hcM := mul_le_mul_of_nonneg_right hc (sq_nonneg (m : ℝ))
    linarith only [hlogu, huM, hLogLogW, hcM]
  have hLogE : Real.log (euler w 1) ≤ c * (m : ℝ) ^ 2 := by
    have h := Real.log_le_log (euler_pos w zero_lt_one) (euler_le_log (show 1 < w by omega))
    change Real.log (euler w 1) ≤ Real.log (C * Real.log w) at h
    rw [Real.log_mul hC.ne' hlogw.ne'] at h
    have HM : (1 : ℝ) ≤ (m : ℝ) ^ 2 := one_le_pow₀ hmR
    have ha := le_mul_of_one_le_right (abs_nonneg (Real.log C)) HM
    dsimp [c]
    linarith only [h, hLogLogW, le_abs_self (Real.log C), ha, HM,
      show (1002 + |Real.log C|) * (m : ℝ) ^ 2 =
        1002 * (m : ℝ) ^ 2 + |Real.log C| * (m : ℝ) ^ 2 by ring]
  have hRate : fewHitsRate w ≤ 3 * c * (m : ℝ) ^ 2 / Real.log w := by
    unfold fewHitsRate
    change (1 + 2 * Real.log (C * Real.log w)) / Real.log w ≤ _
    rw [Real.log_mul hC.ne' hlogw.ne']
    apply div_le_div_of_nonneg_right _ hlogw.le
    have HM : (1 : ℝ) ≤ (m : ℝ) ^ 2 := one_le_pow₀ hmR
    have ha := le_mul_of_one_le_right (abs_nonneg (Real.log C)) HM
    dsimp [c]
    nlinarith only [hLogLogW, le_abs_self (Real.log C), ha, HM, abs_nonneg (Real.log C)]
  have hMulLog : η / 2 ≥ (8 * (scaleBase : ℝ) + 8) / (2 * (m : ℝ)) := by
    have h := (div_le_iff₀ hη).mp (huCost.trans hUR')
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith only [h]
  let J := Ico m (m ^ 2)
  have hJ : J.Nonempty := nonempty_Ico.mpr (show m < m ^ 2 by nlinarith)
  let H (j : ℕ) := scaleBase ^ j
  let z (j : ℕ) := y / H j
  have hEq (j : ℕ) (hj : j ≤ m ^ 2) : y = H j * z j := by
    have hHd : H j ∣ y := by
      have hHle : H j ≤ L := Nat.pow_le_pow_right scaleBase_pos hj
      have hjL : 10 * j ≤ L ^ 100 := by
        have hbound : 10 * (m ^ 2) ≤ L ^ 100 := by
          have hp : L ^ 2 ≤ L ^ 100 := Nat.pow_le_pow_right (by omega) (by decide)
          have hL10 : 10 ≤ L := by
            have hd : (scaleBase : ℕ) ^ 1 ≤ scaleBase ^ (m ^ 2) :=
              Nat.pow_le_pow_right scaleBase_pos (by nlinarith)
            exact (by decide : 10 ≤ scaleBase ^ 1).trans hd
          rw [Nat.mul_comm 10 (m ^ 2)]
          exact (Nat.mul_le_mul hmL hL10).trans (by simpa only [pow_two] using hp)
        exact (Nat.mul_le_mul_left 10 hj).trans hbound
      have hd : H j ∣ w := by
        dsimp [H, w]
        rw [scaleBase_eq, ← pow_mul]
        exact pow_dvd_pow 2 hjL
      exact hd.trans (dvd_pow_self w hu0.ne')
    exact (Nat.mul_div_cancel' hHd).symm
  have hPos (j : ℕ) : 0 < H j := pow_pos scaleBase_pos _
  have hHsmall (j : ℕ) (hj : j ≤ m ^ 2) : H j ≤ L := Nat.pow_le_pow_right scaleBase_pos hj
  have hZbig (j : ℕ) (hj : j ≤ m ^ 2) : w < z j := by
    have hwHit : w * H j < y :=
      (Nat.mul_lt_mul_of_pos_left ((hHsmall j hj).trans_lt hLw) (by omega : 0 < w)).trans_le
        (by simpa [pow_two] using hwY)
    by_contra! h
    have hbad := Nat.mul_le_mul_right (H j) h
    rw [mul_comm (z j), ← hEq j hj] at hbad
    exact hwHit.not_ge hbad
  have hHZ (j : ℕ) (hj : j ≤ m ^ 2) : H j ≤ z j :=
    (hHsmall j hj).trans ((hLw.trans (hZbig j hj)).le)
  have hUpper (j : ℕ) (hj : j ≤ m ^ 2) (hj1 : 1 ≤ j) : scaleBase * z j ≤ y := by
    rw [hEq j hj]
    exact Nat.mul_le_mul_right _ ((pow_one scaleBase).ge.trans (Nat.pow_le_pow_right scaleBase_pos hj1))
  have hLogZ (j : ℕ) (hj : j ≤ m ^ 2) : Real.log (y : ℝ) / 2 ≤ Real.log (z j : ℝ) :=
    log_scale_floor (hEq j hj) (hPos j) hy0 (by
      rw [hEq j hj, pow_two]
      exact Nat.mul_le_mul_left _ (hHZ j hj))
  let bands (j : J) : Band y w := by
    have hj := mem_Ico.mp j.prop
    have hjm : j.val ≤ m ^ 2 := hj.2.le
    have hH1 : 4 ≤ H j.val := by
      change 4 ≤ scaleBase ^ j.val
      exact (by decide : 4 ≤ scaleBase).trans
        ((pow_one scaleBase).ge.trans (Nat.pow_le_pow_right scaleBase_pos (hm1.trans hj.1)))
    have hB : (H j.val) ^ 10 ≤ w := calc
      _ ≤ L ^ 10 := Nat.pow_le_pow_left (hHsmall _ hjm) _
      _ ≤ L ^ 104 := Nat.pow_le_pow_right (show 0 < L by omega) (by decide)
      _ ≤ _ := hL104
    exact buildBand hH1 hB (hZbig _ hjm) (by have := hZbig _ hjm; omega) (hEq _ hjm) (hHZ _ hjm)
      (hUpper _ hjm (hm1.trans hj.1)) (hLogZ _ hjm) hlogHuge
  let z₀ := z (m ^ 2)
  let x := scaleBase * z m
  have hxY : x ≤ y := hUpper m (by nlinarith) hm1
  have hzW : w ≤ z₀ := (hZbig _ le_rfl).le
  have hzx : z₀ ≤ x :=
    (Nat.div_le_div_left (hHsmall m (by nlinarith)) (hPos m)).trans
      (Nat.le_mul_of_pos_left _ scaleBase_pos)
  have hqbounds (j : J) (_ : j ∈ (univ : Finset J)) (q : ℕ) (hq : q ∈ (bands j).pool) :
      z₀ < q ∧ q ≤ x := by
    have hj := mem_Ico.mp j.prop
    have hq' : q ∈ primes (scaleBase * z j.val) \ primes (z j.val) := hq
    have hq0 := mem_primes.mp (mem_sdiff.mp hq').1
    have hqz : z j.val < q := lt_of_not_ge fun h ↦ (mem_sdiff.mp hq').2 (mem_primes.mpr ⟨h, hq0.2⟩)
    exact ⟨(Nat.div_le_div_left (hHsmall _ hj.2.le) (hPos _)).trans_lt hqz,
      hq0.1.trans (Nat.mul_le_mul_left _ (Nat.div_le_div_left (Nat.pow_le_pow_right scaleBase_pos hj.1) (hPos _)))⟩
  have hDisj : Set.Pairwise ((univ : Finset J) : Set J) fun i j ↦ Disjoint (bands i).pool (bands j).pool := by
    have hf (i j : J) (hij : i.val < j.val) : Disjoint (bands i).pool (bands j).pool := by
      have hpow : H i.val * scaleBase ≤ H j.val := by
        rw [← pow_succ]
        exact Nat.pow_le_pow_right scaleBase_pos hij
      have hZ : scaleBase * z j.val ≤ z i.val := by
        apply Nat.le_of_mul_le_mul_left _ (hPos i.val)
        calc
          _ = (H i.val * scaleBase) * z j.val := by ring
          _ ≤ H j.val * z j.val := Nat.mul_le_mul_right _ hpow
          _ = _ := (hEq _ (mem_Ico.mp j.prop).2.le).symm.trans (hEq _ (mem_Ico.mp i.prop).2.le)
      exact disjoint_left.mpr fun q hqi hqj ↦ by
        have hqi' : q ∈ primes (scaleBase * z i.val) \ primes (z i.val) := hqi
        have hqj' : q ∈ primes (scaleBase * z j.val) \ primes (z j.val) := hqj
        have hqj₀ := mem_primes.mp (mem_sdiff.mp hqj').1
        exact (mem_sdiff.mp hqi').2 (mem_primes.mpr ⟨hqj₀.1.trans hZ, hqj₀.2⟩)
    intro i _ j _ hij
    rcases lt_or_gt_of_ne (fun eq ↦ hij (Subtype.ext eq)) with h | h
    · exact hf i j h
    · exact (hf j i h).symm
  have hPool (j : J) : (scaleBase * (z j.val : ℝ)) / (32 * Real.log y) ≤ ((bands j).pool.card : ℝ) :=
    band_pool_bound (by have := hZbig _ (mem_Ico.mp j.prop).2.le; omega)
      (hUpper _ (mem_Ico.mp j.prop).2.le (hm1.trans (mem_Ico.mp j.prop).1))
      (hLogZ _ (mem_Ico.mp j.prop).2.le)
  have hPool' (j : J) : (y : ℝ) / (32 * (H j.val : ℝ) * Real.log y) ≤ ((bands j).pool.card : ℝ) := by
    refine le_trans ?_ (hPool j)
    have hE : (y : ℝ) = (H j.val : ℝ) * (z j.val : ℝ) := by exact_mod_cast hEq _ (mem_Ico.mp j.prop).2.le
    have hh : (0 : ℝ) < H j.val := Nat.cast_pos.mpr (hPos _)
    have he : (y : ℝ) / (H j.val : ℝ) = z j.val :=
      (div_eq_iff hh.ne').mpr (hE.trans (mul_comm (H j.val : ℝ) (z j.val : ℝ)))
    rw [show 32 * (H j.val : ℝ) * Real.log y = (H j.val : ℝ) * (32 * Real.log y) by ring, ← div_div, he]
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact le_mul_of_one_le_left (Nat.cast_nonneg _) (by norm_num [scaleBase])
  have hErr (j : J) (_ : j ∈ (univ : Finset J)) :
      (euler w 1) ^ (2 * (bands j).height) * badBound (bands j).height y ≤ τ * (bands j).pool.card := by
    have hj := mem_Ico.mp j.prop
    have hHL : H j.val ≤ L := hHsmall _ hj.2.le
    have hHm : m ^ 2 ≤ H j.val := (scale_pow_axis m).trans (Nat.pow_le_pow_right scaleBase_pos hj.1)
    have hHc : (m : ℝ) ^ 2 ≤ H j.val := by exact_mod_cast hHm
    have hHR : (0 : ℝ) < H j.val := Nat.cast_pos.mpr (hPos _)
    have hHCR : (H j.val : ℝ) ≤ L := by exact_mod_cast hHL
    have hmuC : 8 * c ≤ m := huC.trans hUR'
    have hG : 8 * c * (m : ℝ) ^ 2 ≤ (H j.val : ℝ) ^ 2 := by
      have hA := mul_le_mul_of_nonneg_right hmuC (sq_nonneg (m : ℝ))
      have hB := pow_le_pow_left₀ (sq_nonneg (m : ℝ)) hHc 2
      nlinarith only [hA,hB, mul_nonneg (show 0 ≤ (m : ℝ) - 1 by linarith) (pow_nonneg (zero_le_one.trans hmR) 3)]
    have hBound1 : (euler w 1) ^ (2 * H j.val) ≤ Real.sqrt y := by
      apply (Real.log_le_log_iff (pow_pos (euler_pos w zero_lt_one) _) (Real.sqrt_pos.mpr hYR)).mp
      rw [Real.log_pow, Real.log_sqrt hYR.le, Nat.cast_mul, Nat.cast_two]
      have hYY := mul_le_mul_of_nonneg_left hLogE (show 0 ≤ 2 * (H j.val : ℝ) by positivity)
      have hBB : 2 * (H j.val : ℝ) * (c * (m : ℝ) ^ 2) ≤ 2 * c * (L : ℝ) ^ 2 := by
        have hM := mul_le_mul hHCR hM2L (sq_nonneg (m : ℝ)) hL0.le
        have := mul_le_mul_of_nonneg_left hM (show 0 ≤ 2 * c by positivity)
        nlinarith only [this]
      have hcL : 8 * c ≤ L := hmuC.trans hMR
      have hSmall : 2 * c * (L : ℝ) ^ 2 ≤ (L : ℝ) ^ 100 / 4 := by
        have hCD := mul_le_mul_of_nonneg_right hcL (sq_nonneg (L : ℝ))
        have hQ := pow_le_pow_right₀ hL1 (show 3 ≤ 100 by decide)
        nlinarith only [hCD,hQ]
      have hLWy : (L : ℝ) ^ 100 / 2 ≤ Real.log y := by
        rw [hly]
        exact hlogwLow.trans (le_mul_of_one_le_left hlogw.le (by exact_mod_cast hu0))
      linarith only [hYY, hBB, hSmall, hLWy]
    have hBound2 : (euler w 1) ^ (2 * H j.val) ≤ Real.exp ((H j.val : ℝ) ^ 3 / 4) := by
      apply (Real.log_le_log_iff (pow_pos (euler_pos w zero_lt_one) _) (Real.exp_pos _)).mp
      rw [Real.log_pow, Real.log_exp, Nat.cast_mul, Nat.cast_two]
      have hE := mul_le_mul_of_nonneg_left hLogE (show 0 ≤ 2 * (H j.val : ℝ) by positivity)
      have hGH := mul_le_mul_of_nonneg_right hG hHR.le
      nlinarith only [hE, hGH]
    have hLogLE : Real.log y ≤ Real.exp ((H j.val : ℝ) ^ 3 / 4) := by
      apply (Real.log_le_log_iff hlogy (Real.exp_pos _)).mp
      rw [Real.log_exp]
      have hH1 : (1 : ℝ) ≤ H j.val := by
        exact hmR.trans ((by nlinarith [hmR] : (m : ℝ) ≤ (m : ℝ) ^ 2).trans hHc)
      have hPow : (H j.val : ℝ) ^ 2 ≤ (H j.val : ℝ) ^ 3 := pow_le_pow_right₀ hH1 (by decide)
      linarith only [hLogLogY,hG,hPow,mul_nonneg hc'.le (sq_nonneg (m : ℝ))]
    have hMle : m ≤ H j.val := (by nlinarith : m ≤ m ^ 2).trans hHm
    have hh := band_error_uniform (bands j) hm1 hLm hMle hHL hy0 hlogy (hPool' j)
      hLlog hLsqrt hBound1 hBound2 hLogLE
    have hErr : 20000 / (m : ℝ) ≤ τ :=
      (div_le_iff₀ (zero_lt_one.trans_le hmR)).mpr ((div_le_iff₀ hτ).mp (huErr.trans hUR') |>.trans_eq (by ring))
    exact hh.trans (mul_le_mul_of_nonneg_right hErr (Nat.cast_nonneg _))
  have hTol (j : J) (_ : j ∈ (univ : Finset J)) : 6 / ((bands j).height : ℝ) + τ ≤ 2 * τ := by
    have hmj : m ≤ H j.val :=
      (by nlinarith : m ≤ m ^ 2).trans ((scale_pow_axis m).trans
        (Nat.pow_le_pow_right scaleBase_pos (mem_Ico.mp j.prop).1))
    have hCast : (m : ℝ) ≤ (bands j).height := by exact_mod_cast hmj
    have hb : 6 / ((bands j).height : ℝ) ≤ τ := calc
      _ ≤ 20000 / ((bands j).height : ℝ) := div_le_div_of_nonneg_right (by norm_num) (Nat.cast_nonneg _)
      _ ≤ 20000 / (u : ℝ) := div_le_div_of_nonneg_left (by norm_num) hUR (hUR'.trans hCast)
      _ ≤ _ := (div_le_iff₀ hUR).mpr (by
        have hh := (div_le_iff₀ hτ).mp huErr
        nlinarith only [hh])
    linarith
  let A := ∑ j : J, bandCost (bands j)
  have hBL (j : J) : 1 / (3200 * C * (u : ℝ) * (j.val : ℝ)) ≤ bandCost (bands j) := by
    have hj := mem_Ico.mp j.prop
    have hjR : (0 : ℝ) < j.val := Nat.cast_pos.mpr (hm1.trans hj.1)
    let B := (H j.val) ^ 10
    have hB1 : 1 < B := by
      have hh := (bands j).height_ge
      change 4 ≤ H j.val at hh
      exact lt_of_lt_of_le (by omega : 1 < H j.val)
        ((pow_one _).ge.trans (Nat.pow_le_pow_right (hPos _) (by decide)))
    have hlogB : Real.log (B : ℝ) ≤ 100 * (j.val : ℝ) := by
      dsimp [B, H]
      simp only [Nat.cast_pow, Real.log_pow, Nat.cast_ofNat]
      have hh := mul_le_mul_of_nonneg_left scaleBase_log (Nat.cast_nonneg j.val)
      linarith only [hh]
    have hsig : sigma (tailPrimes w B) ≤ C * (100 * (j.val : ℝ)) / Real.log w := by
      have hBw : B ≤ w := (bands j).tail_le
      rw [sigma_tail_ge hBw]
      refine div_le_div₀ (by positivity) ?_ hlogw ?_
      · exact (euler_le_log hB1).trans (mul_le_mul_of_nonneg_left hlogB hC.le)
      · exact (Real.log_le_log (Nat.cast_pos.mpr (by omega : 0 < w)) (by linarith)).trans (euler_ge_log w)
    let Rz : ℝ := (scaleBase : ℝ) * (z j.val : ℝ)
    have hRz : 0 < Rz := by
      dsimp [Rz]
      exact mul_pos (Nat.cast_pos.mpr scaleBase_pos) (Nat.cast_pos.mpr ((by omega : 0 < w).trans (hZbig _ hj.2.le)))
    change _ ≤ ((bands j).pool.card : ℝ) / ((↑(scaleBase * z j.val) : ℝ) * sigma (tailPrimes w B))
    rw [Nat.cast_mul]
    change _ ≤ ((bands j).pool.card : ℝ) / (Rz * sigma (tailPrimes w B))
    calc
      _ = (Rz / (32 * Real.log (y : ℝ))) / (Rz * (C * (100 * (j.val : ℝ)) / Real.log w)) := by
        rw [hly]
        field_simp [hRz.ne', hUR.ne', hC.ne', hjR.ne', hlogw.ne']
        ring
      _ ≤ _ := div_le_div₀ (by positivity) (hPool j)
        (mul_pos hRz (tail_sigma_pos w B)) (mul_le_mul_of_nonneg_left hsig hRz.le)
  have hA : (K : ℝ) / (6400 * C) ≤ A := by
    have hh := harmonic_two_powers (K * u) (K * u)
    have he : (2 : ℕ) ^ (K * u + K * u) = m ^ 2 := by rw [pow_add, pow_two]
    rw [he] at hh
    have hh' : (K : ℝ) * (u : ℝ) / 2 ≤ ∑ j ∈ J, (j : ℝ)⁻¹ := by exact_mod_cast hh
    have hb : (∑ j : J, 1 / (3200 * C * (u : ℝ) * (j.val : ℝ))) ≤ A := sum_le_sum fun j _ ↦ hBL j
    have hfac : (∑ j : J, 1 / (3200 * C * (u : ℝ) * (j.val : ℝ))) =
        (1 / (3200 * C * (u : ℝ))) * ∑ j ∈ J, (j : ℝ)⁻¹ := by
      have ht : (∑ j : J, 1 / (3200 * C * (u : ℝ) * (j.val : ℝ))) =
          ∑ j ∈ J, 1 / (3200 * C * (u : ℝ) * (j : ℝ)) :=
        sum_attach J (fun j ↦ 1 / (3200 * C * (u : ℝ) * (j : ℝ)))
      rw [ht, mul_sum]
      refine sum_congr rfl fun j _ ↦ ?_
      ring
    have hd := mul_le_mul_of_nonneg_left hh' (show 0 ≤ 1 / (3200 * C * (u : ℝ)) by positivity)
    rw [← hfac] at hd
    refine le_trans ?_ (hd.trans hb)
    field_simp [hC.ne', hUR.ne']
    norm_num
  have hA0 : 0 < A := (div_pos (Nat.cast_pos.mpr hKpos) (by positivity)).trans_le hA
  have hMiss : 4 * (2 * τ) + 20 / A ≤ 12 * τ := by
    have hb : 20 / A ≤ 4 * τ := by
      have hd := (le_max_right _ _ : 128000 * C / (4 * τ) ≤ _).trans hK
      apply (div_le_iff₀ hA0).mpr
      have hKmul := (div_le_iff₀ (show 0 < 4 * τ by positivity)).mp hd
      have hKdiv := (div_le_iff₀ (show 0 < 6400 * C by positivity)).mp hA
      have hx := mul_le_mul_of_nonneg_right hKdiv (show 0 ≤ 4 * τ by positivity)
      apply le_of_mul_le_mul_right ?_ hC
      nlinarith only [hKmul,hx]
    linarith only [hb]
  let α := s / Real.log w
  have hα : 0 < α := div_pos hs hlogw
  have hα2 : α ≤ 1 / 2 := by
    apply (div_le_iff₀ hlogw).mpr
    linarith only [hus, huLn, hs]
  have hTilt : euler w (1 - α) ≤ T * euler w 1 := by
    have hαlog : α * Real.log w = s := div_mul_cancel₀ _ hlogw.ne'
    have hparam : max |(1 - α) - 1| |(1 : ℝ) - 1| * Real.log w ≤ s := by
      rw [show 1 - α - 1 = -α by ring, abs_neg, abs_of_pos hα, sub_self, abs_zero,
        max_eq_left hα.le, hαlog]
    have h := euler_compare (show 1 < w by omega) (by linarith : 1 / 2 ≤ 1 - α)
      (by norm_num : (1 / 2 : ℝ) ≤ 1) hparam
    simpa only [show 1 - α - 1 = -α by ring, abs_neg, abs_of_pos hα, sub_self, abs_zero,
      add_zero, mul_assoc, hαlog, T] using h
  have hTailPow : (y : ℝ) ^ (-α / 2) = Real.exp (-(8 * (K : ℝ) * u)) := by
    rw [Real.rpow_def_of_pos hYR, hly]
    congr 1
    unfold α s
    field_simp [hlogw.ne']
    ring
  have hTailSmall : T * ((u : ℝ) * Real.exp (-(8 * (K : ℝ) * u))) ≤ 1 := by
    have he : Real.exp (-(8 * (K : ℝ) * u)) ≤ Real.exp (-(u : ℝ)) :=
      Real.exp_le_exp.mpr (by nlinarith [mul_nonneg (show (0 : ℝ) ≤ K - 1 by linarith) hUR.le])
    exact (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left he hUR.le) hT).trans (huTilt.trans (min_le_left _ _))
  let S := y.smoothNumbersUpTo (w + 1)
  let D₀ := S ∪ primeMultiples y z₀ (Icc 1 L)
  let D₁ := primeMultiples y w S
  have hD₁sub : D₁ ⊆ Icc 1 y :=
    primeMultiples_subset (fun _ hm ↦ Nat.pos_of_ne_zero (Nat.mem_smoothNumbers.mp (Nat.mem_smoothNumbersUpTo.mp hm).2).1)
  have hD₁ : (D₁.card : ℝ) * sigma (primes w) ≤ (32 * C) * ((y : ℝ) / Real.log y) := by
    have hB := one_large_count (show 4 ≤ y by omega) (show 1 < w by omega) hα.le (by linarith)
    have hE := euler_le_log (show 1 < w by omega)
    have hBr : (D₁.card : ℝ) ≤ (24 * C * (y : ℝ) / u) +
        8 * C * (y : ℝ) * (T * Real.exp (-(8 * (K : ℝ) * u))) := by
      unfold D₁ S
      refine hB.trans ?_
      rw [hly, hTailPow]
      calc
        _ ≤ 24 * (y : ℝ) / ((u : ℝ) * Real.log w) * (C * Real.log w) +
            8 * (y : ℝ) / Real.log w * (Real.exp (-(8 * (K : ℝ) * u)) * (T * (C * Real.log w))) := by
          repeat apply add_le_add
          · exact mul_le_mul_of_nonneg_left hE (by positivity)
          · exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
              (hTilt.trans (mul_le_mul_of_nonneg_left hE hT)) (Real.exp_nonneg _)) (by positivity)
        _ = _ := by field_simp [hUR.ne', hlogw.ne']
    have hSig := sigma_le_inv_log (show 1 < w by omega)
    calc
      _ ≤ ((24 * C * (y : ℝ) / u) + 8 * C * (y : ℝ) *
        (T * Real.exp (-(8 * (K : ℝ) * u)))) * (1 / Real.log w) :=
        mul_le_mul hBr hSig (sigma_pos (fun _ hp ↦ (mem_primes.mp hp).2.one_lt)).le (by positivity)
      _ = (24 * C + 8 * C * (T * ((u : ℝ) * Real.exp (-(8 * (K : ℝ) * u))))) *
        ((y : ℝ) / Real.log y) := by rw [hly]; field_simp [hUR.ne', hlogw.ne']
      _ ≤ _ := mul_le_mul_of_nonneg_right (by nlinarith [mul_le_mul_of_nonneg_left hTailSmall hC.le]) (by positivity)
  have hD₀count : (D₀.card : ℝ) ≤ Real.sqrt y + (y : ℝ) * (T * Real.exp (-(8 * (K : ℝ) * u))) +
      16 * (y : ℝ) / Real.log y * (1 + Real.log L) := by
    have hs0 := smooth_count_bound (y := y) (w := w) hy0 hα.le (by linarith)
    have hs1 := beyond_main_count (z := z₀) (H := L) (by omega : 1 < z₀)
      (show 4 ≤ y by omega) (hLogZ _ le_rfl)
    have hR : euler w (1 - α) / euler w 1 ≤ T := (div_le_iff₀ (euler_pos _ zero_lt_one)).mpr hTilt
    rw [hTailPow] at hs0
    have hss : (S.card : ℝ) ≤ Real.sqrt y + (y : ℝ) * (T * Real.exp (-(8 * (K : ℝ) * u))) := by
      have h := mul_le_mul_of_nonneg_left hR (show 0 ≤ (y : ℝ) * Real.exp (-(8 * (K : ℝ) * u)) by positivity)
      have hNat := (Real.nat_sqrt_le_real_sqrt (a := y))
      linarith only [h, hs0, hNat]
    have hh : (D₀.card : ℝ) ≤ (S.card : ℝ) + (primeMultiples y z₀ (Icc 1 L)).card := by
      exact_mod_cast card_union_le S (primeMultiples y z₀ (Icc 1 L))
    exact hh.trans (add_le_add hss hs1)
  have hD₀ : (D₀.card : ℝ) * fewHitsRate w ≤ (η / 64) * ((y : ℝ) / Real.log y) := by
    let g := Real.exp (-(8 * (K : ℝ) * u))
    have hNonneg : 0 ≤ fewHitsRate w := by
      unfold fewHitsRate
      apply div_nonneg _ hlogw.le
      have hlog1 : 1 ≤ Real.log (w : ℝ) := by linarith only [huLn, show (2 : ℝ) ≤ u by exact_mod_cast hu2]
      have hg := Real.log_nonneg (hlog1.trans (le_mul_of_one_le_left hlogw.le hC1))
      linarith only [hg]
    have h1 : (u : ℝ) * (m : ℝ) ^ 2 * (Real.sqrt y / (y : ℝ)) ≤ 1 / (m : ℝ) := by
      have hS := Real.sq_sqrt hYR.le
      have hYS := Real.sqrt_pos.mpr hYR
      have hRatio : Real.sqrt (y : ℝ) / (y : ℝ) = 1 / Real.sqrt (y : ℝ) := by
        field_simp [hYS.ne', hYR.ne']
        exact hS
      have hYS' : (L : ℝ) ^ 104 ≤ Real.sqrt y := hLsqrt
      rw [hRatio]
      have hM4 : (m : ℝ) ^ 4 ≤ Real.sqrt y :=
        (pow_le_pow_left₀ (zero_le_one.trans hmR) hMR 4).trans
          ((pow_le_pow_right₀ hL1 (by decide : 4 ≤ 104)).trans hYS')
      rw [← div_eq_mul_one_div, div_le_div_iff₀ hYS (zero_lt_one.trans_le hmR)]
      have hh := mul_le_mul_of_nonneg_right hUR' (pow_nonneg (zero_le_one.trans hmR) 3)
      nlinarith only [hM4,hh]
    have h2 : (u : ℝ) * (m : ℝ) ^ 2 * (T * g) ≤ T * ((u : ℝ) * Real.exp (-(u : ℝ))) := by
      have hExp : (m : ℝ) ^ 2 = Real.exp (2 * (K : ℝ) * (u : ℝ) * Real.log 2) := by
        dsimp [m]
        simp only [Nat.cast_pow, Nat.cast_two]
        rw [← pow_mul]
        rw [show 2 * (K : ℝ) * (u : ℝ) * Real.log 2 = (↑((K * u) * 2) : ℝ) * Real.log 2 by push_cast; ring,
          Real.exp_nat_mul, Real.exp_log (show (0 : ℝ) < 2 by norm_num)]
      have hcomp : (m : ℝ) ^ 2 * g ≤ Real.exp (-(u : ℝ)) := by
        rw [hExp]
        unfold g
        rw [← Real.exp_add]
        apply Real.exp_le_exp.mpr
        have hm' := mul_le_mul_of_nonneg_left log_two_bounds.2 (by positivity : 0 ≤ 2 * (K : ℝ) * u)
        have hkU := mul_le_mul_of_nonneg_right hK1 hUR.le
        nlinarith only [hm',hkU,hUR]
      have hh := mul_le_mul_of_nonneg_left hcomp (show 0 ≤ T * (u : ℝ) by positivity)
      nlinarith only [hh]
    have h3 : (u : ℝ) * (m : ℝ) ^ 2 * (16 * (1 + Real.log L) / Real.log y) ≤ 352 / (m : ℝ) := by
      have hrewrite : (u : ℝ) * (m : ℝ) ^ 2 * (16 * (1 + Real.log L) / Real.log y) =
          16 * (m : ℝ) ^ 2 * (1 + Real.log L) / Real.log w := by
        rw [hly]
        field_simp [hUR.ne', hlogw.ne']
      rw [hrewrite]
      have hNum : 16 * (m : ℝ) ^ 2 * (1 + Real.log L) ≤ 176 * (L : ℝ) ^ 2 := by
        have hf : 1 + Real.log (L : ℝ) ≤ 11 * (L : ℝ) := by linarith only [hLogL, hM2L, hL1]
        have hg := mul_le_mul hM2L hf
          (by linarith [Real.log_nonneg hL1] : 0 ≤ 1 + Real.log (L : ℝ)) hL0.le
        nlinarith only [hg]
      calc
        _ ≤ 176 * (L : ℝ) ^ 2 / ((L : ℝ) ^ 100 / 2) :=
          (div_le_div_of_nonneg_right hNum hlogw.le).trans
            (div_le_div_of_nonneg_left (by positivity) (by positivity) hlogwLow)
        _ ≤ _ := by
          rw [div_le_div_iff₀ (by positivity) (zero_lt_one.trans_le hmR)]
          have hL3 := pow_le_pow_right₀ hL1 (show 3 ≤ 100 by decide)
          have hml := mul_le_mul_of_nonneg_left hMR (show 0 ≤ (L : ℝ) ^ 2 by positivity)
          nlinarith only [hL3,hml]
    have hRateY : (D₀.card : ℝ) * fewHitsRate w ≤
        3 * c * (353 / (m : ℝ) + T * ((u : ℝ) * Real.exp (-(u : ℝ)))) *
          ((y : ℝ) / Real.log y) := by
      have hSum : ((u : ℝ) * (m : ℝ) ^ 2) *
          (Real.sqrt y / (y : ℝ) + T * g + 16 * (1 + Real.log L) / Real.log y) ≤
          353 / (m : ℝ) + T * ((u : ℝ) * Real.exp (-(u : ℝ))) := by
        rw [mul_add,mul_add]
        linarith only [h1,h2,h3, show 1 / (m : ℝ) + 352 / m = 353 / m by ring]
      have hcount : (D₀.card : ℝ) ≤ (y : ℝ) *
          (Real.sqrt y / (y : ℝ) + T * g + 16 * (1 + Real.log L) / Real.log y) := hD₀count.trans_eq (by
            dsimp [g]
            field_simp [hYR.ne',hlogy.ne'])
      have hU := mul_le_mul hcount hRate hNonneg (by positivity)
      have hCoef : 0 ≤ 3 * c * ((y : ℝ) / Real.log y) := by positivity
      refine hU.trans ?_
      calc
        _ = (3 * c * ((y : ℝ) / Real.log y)) * (((u : ℝ) * (m : ℝ) ^ 2) *
          (Real.sqrt y / (y : ℝ) + T * g + 16 * (1 + Real.log L) / Real.log y)) := by
            rw [hly]
            field_simp [hYR.ne',hUR.ne',hlogw.ne']
        _ ≤ _ := (mul_le_mul_of_nonneg_left hSum hCoef).trans_eq (by ring)
    have ha : 3 * c * (353 / (m : ℝ)) ≤ η / 128 := by
      have hu' := (div_le_iff₀ hη).mp (huDef.trans hUR')
      rw [← mul_div_assoc]
      exact (div_le_iff₀ (zero_lt_one.trans_le hmR)).mpr (by nlinarith only [hu',hc'])
    have hb : 3 * c * (T * ((u : ℝ) * Real.exp (-(u : ℝ)))) ≤ η / 128 := by
      have hh := huTilt.trans (min_le_right _ _)
      apply le_trans (mul_le_mul_of_nonneg_left hh (by positivity))
      field_simp [hc'.ne']
      norm_num
    exact hRateY.trans (mul_le_mul_of_nonneg_right (by nlinarith only [ha,hb]) (by positivity))
  have hU : (univ : Finset J).Nonempty := by
    obtain ⟨j, hj⟩ := hJ
    exact ⟨⟨j,hj⟩, mem_univ _⟩
  obtain ⟨a,r,F,hF,hr,h₀,h₁⟩ := choose_cover hw2 (univ : Finset J) hU
    bands D₀ D₁ hD₁sub hτ1 hTol hErr
  have hF' : (F.card : ℝ) ≤ (η / 8) * ((y : ℝ) / Real.log y) := by
    have h0 : 0 ≤ 12 * τ := by positivity
    have h1 : 0 ≤ (D₁.card : ℝ) * sigma (primes w) :=
      mul_nonneg (Nat.cast_nonneg _) (sigma_pos (fun _ hp ↦ (mem_primes.mp hp).2.one_lt)).le
    have hD₁' := mul_le_mul hD₁ hMiss (by positivity : 0 ≤ 4 * (2 * τ) + 20 / A)
      (by positivity : 0 ≤ 32 * C * ((y : ℝ) / Real.log y))
    have hFin := hF.trans (add_le_add hD₀ hD₁')
    have hh : 32 * C * (12 * τ) ≤ η / 64 := by
      dsimp [τ]
      field_simp [hC.ne']
      linarith
    nlinarith only [hFin, mul_le_mul_of_nonneg_right hh (show 0 ≤ (y : ℝ) / Real.log y by positivity)]
  have hFc : F.card ≤ y := by
    have hLogY : (1 : ℝ) ≤ Real.log y := by
      have hr : 16 * (scaleBase : ℝ) ≥ 1 := by norm_num [scaleBase]
      exact hr.trans hlogHuge
    have hF'' : (F.card : ℝ) ≤ y := hF'.trans
      (mul_le_of_le_one_left (div_nonneg (Nat.cast_nonneg _) hlogy.le) (by linarith : η / 8 ≤ 1) |>.trans
        (div_le_self (Nat.cast_nonneg _) hLogY))
    exact_mod_cast hF''
  obtain ⟨N, hN, hLogN, hPart⟩ := hole_from_cover (by simpa only [H,z₀,mul_comm] using hEq (m ^ 2) le_rfl)
    hLw hzW hzx hxY (show 4 ≤ y by omega) (univ : Finset J) bands hqbounds hDisj F
    (hFc.trans (enough_patch_primes hybig)) a r h₀ h₁
  have hxCost : (4 : ℝ) * (x : ℝ) ≤ (4 * (scaleBase : ℝ) / m) * y := by
    dsimp [x,z]
    have h0 : (m : ℝ) ≤ (H m : ℝ) := by exact_mod_cast (by nlinarith : m ≤ m ^ 2).trans (scale_pow_axis m)
    have hdiv : (↑(y / H m) : ℝ) ≤ (y : ℝ) / m :=
      Nat.cast_div_le.trans (div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by positivity) h0)
    have h := mul_le_mul_of_nonneg_left hdiv (show (0 : ℝ) ≤ 4 * ↑scaleBase by positivity)
    push_cast
    nlinarith only [h, show 4 * (scaleBase : ℝ) * ((y : ℝ) / m) =
      (4 * (scaleBase : ℝ) / (m : ℝ)) * y by ring]
  have hEndLog : Real.log ((y : ℝ) + 2) ≤ (4 / (m : ℝ)) * y := by
    have hv := Real.log_le_rpow_div (show 0 ≤ (y : ℝ) + 2 by positivity) (by norm_num : (0 : ℝ) < 1 / 2)
    rw [← Real.sqrt_eq_rpow] at hv
    have hS : Real.sqrt ((y : ℝ) + 2) ≤ 2 * Real.sqrt y := by
      apply (Real.sqrt_le_left (by positivity)).mpr
      rw [mul_pow, Real.sq_sqrt hYR.le]
      have hyy : (1 : ℝ) ≤ y := by exact_mod_cast (show 1 ≤ y by omega)
      linarith
    have hmS : (m : ℝ) ≤ Real.sqrt y := hMR.trans
      ((by exact_mod_cast hLw.le : (L : ℝ) ≤ w).trans hwSqrt)
    have hYS := Real.sq_sqrt hYR.le
    rw [div_mul_eq_mul_div, le_div_iff₀ (zero_lt_one.trans_le hmR)]
    have hmul := mul_le_mul_of_nonneg_right hmS (Real.sqrt_nonneg y)
    have hlog' : Real.log ((y : ℝ) + 2) ≤ 4 * Real.sqrt y := by linarith only [hv,hS]
    have hmul2 := mul_le_mul_of_nonneg_right hlog' (zero_le_one.trans hmR)
    nlinarith only [hYS,hmul,hmul2]
  have hCost : Real.log ((y : ℝ) + 2) + 4 * (x : ℝ) ≤ (η / 2) * y := by
    refine (add_le_add hEndLog hxCost).trans ?_
    rw [← add_mul]
    apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
    linarith only [hMulLog, show 4 / (m : ℝ) + 4 * (scaleBase : ℝ) / m =
      (8 * (scaleBase : ℝ) + 8) / (2 * (m : ℝ)) by ring]
  have hFC := mul_le_mul_of_nonneg_left hF' (show 0 ≤ 4 * Real.log (y : ℝ) by positivity)
  have hfinal : Real.log ((N : ℝ) + 1) ≤ η * y := by
    have herr : 4 * Real.log (y : ℝ) * (η / 8 * ((y : ℝ) / Real.log y)) = (η / 2) * y := by
      field_simp [hlogy.ne']
      ring
    linarith only [hLogN,hCost,hFC,herr]
  exact ⟨y,N,hY₀,hN,hfinal,hPart⟩


end Erdos1139Proof

open Nat Filter
open scoped ArithmeticFunction.Omega

namespace Erdos1139Proof

/-- Erdős Problem 1139: the gaps between consecutive positive integers with at most two prime
factors, divided by `log k`, have limit superior `⊤`. -/
theorem erdos_1139 :
    letI u := Nat.nth (fun n ↦ 0 < n ∧ Ω n ≤ 2)
    atTop.limsup (fun k : ℕ ↦ (((u (k + 1) : ℝ) - (u k : ℝ)) / Real.log (↑k + 1) : EReal)) = ⊤ := by
  classical
  let a : ℕ → Prop := fun n ↦ 0 < n ∧ Ω n ≤ 2
  let u := Nat.nth a
  have hinf : {n | a n}.Infinite :=
    Nat.infinite_setOfPred_prime.mono fun n (hn : n.Prime) ↦
      ⟨hn.pos, by rw [ArithmeticFunction.cardFactors_apply_prime hn]; decide⟩
  have hu : StrictMono u := Nat.nth_strictMono hinf
  have hmem (k : ℕ) : a (u k) := Nat.nth_mem_of_infinite hinf k
  let f := fun k : ℕ ↦ (((u (k + 1) : ℝ) - (u k : ℝ)) / Real.log (↑k + 1) : EReal)
  change atTop.limsup f = ⊤
  by_contra hn
  obtain ⟨r, hr, _⟩ := EReal.lt_iff_exists_real_btwn.mp (lt_top_iff_ne_top.mpr hn)
  apply (not_le_of_gt hr)
  apply Filter.le_limsup_of_frequently_le'
  rw [Filter.frequently_atTop]
  intro K
  let R := max 1 r
  have hR1 : 1 ≤ R := le_max_left _ _
  have hR : 0 < R := zero_lt_one.trans_le hR1
  obtain ⟨y,N,hy,hN,hL,hHole⟩ := large_holes (1 / R) (one_div_pos.mpr hR)
    ((div_le_one hR).mpr hR1) (u (K + 1))
  have hX : u (K + 1) ≤ N := hy.trans hN
  have hex : ∃ i, N < u i := ⟨N + 1, (Nat.lt_succ_self _).trans_le (hu.id_le _)⟩
  let i := Nat.find hex
  have hright : N < u i := Nat.find_spec hex
  have hil : K + 1 < i := by
    by_contra! hi
    have := hu.monotone hi
    omega
  let k := i - 1
  have hk_i : k + 1 = i := by dsimp [k]; omega
  have hkK : K ≤ k := by dsimp [k]; omega
  have hkpos : 0 < k := by dsimp [k]; omega
  have hleft : u k ≤ N := by
    by_contra! h
    have hk_lt_i : k < i := by omega
    exact Nat.find_min hex hk_lt_i h
  have hright' : N + y < u (k + 1) := by
    by_contra! h
    have hN' : N < u (k + 1) := by rwa [hk_i]
    let d := u (k + 1) - N
    have hd : N + d = u (k + 1) := by dsimp [d]; omega
    have hdmem : d ∈ Finset.Icc 1 y := Finset.mem_Icc.mpr (by dsimp [d]; omega)
    have hbad := hHole d hdmem
    rw [hd] at hbad
    exact (not_le_of_gt hbad) (hmem _).2
  refine ⟨k, hkK, ?_⟩
  apply EReal.coe_le_coe_iff.mpr
  have hlogpos : 0 < Real.log ((k : ℝ) + 1) :=
    Real.log_pos (by exact_mod_cast show 1 < k + 1 by omega)
  apply (le_div_iff₀ hlogpos).mpr
  have hlog : Real.log ((k : ℝ) + 1) ≤ Real.log ((N : ℝ) + 1) := by
    have hkR : (k : ℝ) ≤ N := Nat.cast_le.mpr ((hu.id_le k).trans hleft)
    exact Real.log_le_log (add_pos_of_nonneg_of_pos (Nat.cast_nonneg k) zero_lt_one)
      (by linarith only [hkR])
  have hRlog := mul_le_mul_of_nonneg_left (hlog.trans hL) hR.le
  have hRcancel : R * (1 / R * (y : ℝ)) = y := by field_simp [hR.ne']
  rw [hRcancel] at hRlog
  have hrR : r ≤ R := le_max_right _ _
  have hrlog := mul_le_mul_of_nonneg_right hrR hlogpos.le
  have hleftR : (u k : ℝ) ≤ N := Nat.cast_le.mpr hleft
  have hrightR : (N : ℝ) + y < u (k + 1) := by exact_mod_cast hright'
  linarith only [hrlog,hRlog,hleftR,hrightR]

/-- `Erdos1139.erdos_1139` from google-deepmind/formal-conjectures, stated through its type:
the same statement as `erdos_1139`. -/
theorem erdos_1139_fc : type_of% @Erdos1139.erdos_1139 :=
  erdos_1139

end Erdos1139Proof

end
