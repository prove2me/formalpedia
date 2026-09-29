-- Prove2me | solution 1 for TruthFractalDimensionDeepening.tendsto_dimEstimate_densityTheory
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-20T06:04:23.431423+00:00
-- url     : https://prove2.me/submissions/a3172c67-a7ab-4731-9a24-544eae2c2d06

import Mathlib
import Definitions.Def_Algebra_TruthFractalDimensionDeepening

open TruthFractalDimensionDeepening Filter Topology Finset in
theorem solution (m : ℕ) (R : Finset ℕ) (hR : R ⊆ Finset.range m)
    (hm : 1 ≤ m) :
    Tendsto (dimEstimate (densityTheory m R)) atTop (nhds (R.card / m)) := by
  have hm0 : 0 < m := hm
  -- the count is `2 ^ (number of free indices)`
  have hcount : ∀ n, count (densityTheory m R) n
      = 2 ^ ((range n).filter (fun i => i % m ∈ R)).card := by
    intro n
    unfold count densityTheory
    rw [Fintype.card_piFinset]
    have h1 : ∀ i : Fin n, ((if (i : ℕ) % m ∈ R then (univ : Finset Bool) else {false}).card)
        = if (i : ℕ) % m ∈ R then 2 else 1 := by
      intro i
      split_ifs <;> simp
    simp only [h1]
    rw [Finset.prod_ite, prod_const, prod_const_one, mul_one]
    congr 1
    rw [card_filter, card_filter]
    exact Fin.sum_univ_eq_sum_range (fun i => if i % m ∈ R then 1 else 0) n
  -- counting residues: each `v ∈ R` occurs `n / m` or `n / m + 1` times below `n`
  have hfree : ∀ n, ((range n).filter (fun i => i % m ∈ R)).card
      = ∑ v ∈ R, (n / m + if v % m < n % m then 1 else 0) := by
    intro n
    rw [card_eq_sum_card_fiberwise (s := (range n).filter (fun i => i % m ∈ R))
      (f := fun i => i % m) (t := R) (by intro i hi; exact (mem_filter.1 (mem_coe.1 hi)).2)]
    refine sum_congr rfl fun v hv => ?_
    have hvm : v < m := mem_range.1 (hR hv)
    rw [← Nat.count_modEq_card (b := n) hm0 v, Nat.count_eq_card_filter_range]
    congr 1
    ext i
    simp only [mem_filter, mem_range, Nat.ModEq, Nat.mod_eq_of_lt hvm]
    constructor
    · rintro ⟨⟨hi, -⟩, h⟩
      exact ⟨hi, h⟩
    · rintro ⟨hi, h⟩
      exact ⟨⟨hi, h ▸ hv⟩, h⟩
  have hlowN : ∀ n, R.card * (n / m) ≤ ((range n).filter (fun i => i % m ∈ R)).card := by
    intro n
    rw [hfree n, ← smul_eq_mul, ← sum_const]
    exact sum_le_sum fun v _ => Nat.le_add_right _ _
  have hupN : ∀ n, ((range n).filter (fun i => i % m ∈ R)).card ≤ R.card * (n / m + 1) := by
    intro n
    rw [hfree n, ← smul_eq_mul, ← sum_const]
    refine sum_le_sum fun v _ => ?_
    split_ifs <;> omega
  -- the dimension estimate is the free-index density
  have hdim : ∀ n, dimEstimate (densityTheory m R) n
      = (((range n).filter (fun i => i % m ∈ R)).card : ℝ) / n := by
    intro n
    unfold dimEstimate
    rw [hcount n]
    push_cast
    rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one]
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm0
  have hlo : Tendsto (fun n : ℕ => (R.card : ℝ) / m - R.card / n) atTop
      (nhds ((R.card : ℝ) / m)) := by
    simpa using (tendsto_const_nhds (x := (R.card : ℝ) / m)).sub
      (tendsto_const_div_atTop_nhds_zero_nat (R.card : ℝ))
  have hhi : Tendsto (fun n : ℕ => (R.card : ℝ) / m + R.card / n) atTop
      (nhds ((R.card : ℝ) / m)) := by
    simpa using (tendsto_const_nhds (x := (R.card : ℝ) / m)).add
      (tendsto_const_div_atTop_nhds_zero_nat (R.card : ℝ))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with n hn
    rw [hdim n]
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hq : (n : ℝ) / m - 1 ≤ ((n / m : ℕ) : ℝ) := by
      have h1 : n < n / m * m + m := Nat.lt_div_mul_add hm0
      have h2 : (n : ℝ) < ((n / m : ℕ) : ℝ) * m + m := by exact_mod_cast h1
      rw [div_sub_one hmR.ne', div_le_iff₀ hmR]
      linarith
    have h3 : (R.card : ℝ) * ((n : ℝ) / m - 1) ≤ ((range n).filter (fun i => i % m ∈ R)).card :=
      (mul_le_mul_of_nonneg_left hq (Nat.cast_nonneg _)).trans (by exact_mod_cast hlowN n)
    rw [le_div_iff₀ hn0]
    have e : ((R.card : ℝ) / m - R.card / n) * n = (R.card : ℝ) * ((n : ℝ) / m - 1) := by
      field_simp
    rw [e]
    exact h3
  · filter_upwards [eventually_ge_atTop 1] with n hn
    rw [hdim n]
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hq : ((n / m : ℕ) : ℝ) ≤ (n : ℝ) / m := Nat.cast_div_le
    have h3 : (((range n).filter (fun i => i % m ∈ R)).card : ℝ) ≤ (R.card : ℝ) * ((n : ℝ) / m + 1) := by
      have h4 : (((range n).filter (fun i => i % m ∈ R)).card : ℝ) ≤ (R.card : ℝ) * ((n / m : ℕ) + 1) := by
        exact_mod_cast hupN n
      exact h4.trans (mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg _))
    rw [div_le_iff₀ hn0]
    have e : ((R.card : ℝ) / m + R.card / n) * n = (R.card : ℝ) * ((n : ℝ) / m + 1) := by
      field_simp
    rw [e]
    exact h3
