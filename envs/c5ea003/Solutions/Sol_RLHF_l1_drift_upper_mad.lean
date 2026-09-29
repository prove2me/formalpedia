-- Prove2me | solution 1 for RLHF.l1_drift_upper_mad
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-20T04:01:55.137553+00:00
-- url     : https://prove2.me/submissions/f250151b-36b7-482f-b8b9-2ea803dd9893

import Mathlib
import Definitions.Def_Algebra_RLHFDriftCore
import Definitions.Def_Algebra_RLHFMeanAbsoluteDeviation

open RLHF Finset in
theorem solution {Ω : Type*} [Fintype Ω] [Nonempty Ω] {β : ℝ} {r p : Ω → ℝ} (hβ : 0 < β)
    (hp : IsPosDist p) (hr : rewardRange r ≤ β) :
    l1Dist (gibbsPolicy β r p) p ≤ mad p r / β + 2 * (variance p r / β ^ 2) := by
  obtain ⟨hpos, htot⟩ := hp
  set m := mean p r with hm
  set c : Ω → ℝ := fun y => (r y - m) / β with hcdef
  set Z := ∑ y, p y * Real.exp (c y) with hZdef
  set V := variance p r / β ^ 2 with hVdef
  set A := mad p r / β with hAdef
  -- the centred, rescaled reward stays in `[-1, 1]`
  have hsup : ∀ y, r y ≤ univ.sup' univ_nonempty r := fun y => le_sup' r (mem_univ y)
  have hinf : ∀ y, univ.inf' univ_nonempty r ≤ r y := fun y => inf'_le r (mem_univ y)
  have hmle : m ≤ univ.sup' univ_nonempty r := by
    calc m = ∑ y, p y * r y := rfl
      _ ≤ ∑ y, p y * univ.sup' univ_nonempty r :=
          sum_le_sum fun y _ => mul_le_mul_of_nonneg_left (hsup y) (hpos y).le
      _ = univ.sup' univ_nonempty r := by rw [← sum_mul, htot, one_mul]
  have hmge : univ.inf' univ_nonempty r ≤ m := by
    calc univ.inf' univ_nonempty r = ∑ y, p y * univ.inf' univ_nonempty r := by
          rw [← sum_mul, htot, one_mul]
      _ ≤ ∑ y, p y * r y :=
          sum_le_sum fun y _ => mul_le_mul_of_nonneg_left (hinf y) (hpos y).le
      _ = m := rfl
  have hc : ∀ y, |c y| ≤ 1 := by
    intro y
    have h1 : |r y - m| ≤ β := by
      rw [abs_le]
      have := hsup y
      have := hinf y
      unfold rewardRange at hr
      constructor <;> linarith
    show |(r y - m) / β| ≤ 1
    rw [abs_div, abs_of_pos hβ, div_le_one hβ]
    exact h1
  -- first and second moments of `c`
  have hEc : ∑ y, p y * c y = 0 := by
    have h1 : ∀ y, p y * c y = (p y * r y - m * p y) / β := by
      intro y
      simp only [hcdef]
      ring
    rw [sum_congr rfl fun y _ => h1 y, ← sum_div, sum_sub_distrib, ← mul_sum, htot]
    simp [hm, mean]
  have hsumV : ∑ y, p y * c y ^ 2 = V := by
    rw [hVdef, variance, sum_div]
    refine sum_congr rfl fun y _ => ?_
    simp only [hcdef]
    ring
  have hsumA : ∑ y, p y * |c y| = A := by
    rw [hAdef, mad, sum_div]
    refine sum_congr rfl fun y _ => ?_
    simp only [hcdef]
    rw [abs_div, abs_of_pos hβ]
    ring
  have hV0 : 0 ≤ V := by
    rw [← hsumV]
    exact sum_nonneg fun y _ => mul_nonneg (hpos y).le (sq_nonneg _)
  have hA1 : A ≤ 1 := by
    rw [← hsumA]
    calc ∑ y, p y * |c y| ≤ ∑ y, p y * 1 :=
          sum_le_sum fun y _ => mul_le_mul_of_nonneg_left (hc y) (hpos y).le
      _ = 1 := by rw [← sum_mul, htot, one_mul]
  -- the normaliser: `1 ≤ Z ≤ 1 + V`
  have hZ1 : 1 ≤ Z := by
    calc (1 : ℝ) = ∑ y, p y * (c y + 1) := by
          rw [sum_congr rfl fun y _ => mul_add (p y) (c y) 1, sum_add_distrib, hEc]
          simp [htot]
      _ ≤ Z := sum_le_sum fun y _ =>
          mul_le_mul_of_nonneg_left (Real.add_one_le_exp (c y)) (hpos y).le
  have hZ2 : Z ≤ 1 + V := by
    calc Z ≤ ∑ y, p y * (1 + c y + c y ^ 2) := sum_le_sum fun y _ => by
          have := (abs_le.1 (Real.abs_exp_sub_one_sub_id_le (hc y))).2
          exact mul_le_mul_of_nonneg_left (by linarith) (hpos y).le
      _ = 1 + V := by
          simp only [mul_add, sum_add_distrib, hEc, hsumV, mul_one, htot]
          ring
  have hZpos : 0 < Z := by linarith
  have hZne : Z ≠ 0 := hZpos.ne'
  -- the Gibbs policy in centred form
  have hsplit : ∀ y, Real.exp (r y / β) = Real.exp (m / β) * Real.exp (c y) := by
    intro y
    rw [← Real.exp_add]
    congr 1
    simp only [hcdef]
    field_simp
    ring
  have hpart : partition β r p = Real.exp (m / β) * Z := by
    simp only [partition, hsplit, hZdef, mul_sum]
    exact sum_congr rfl fun y _ => by ring
  have hπ : ∀ y, gibbsPolicy β r p y = p y * Real.exp (c y) / Z := by
    intro y
    simp only [gibbsPolicy]
    rw [hpart, hsplit, mul_left_comm, mul_div_mul_left _ _ (Real.exp_pos _).ne']
  have hl1 : l1Dist (gibbsPolicy β r p) p = (∑ y, p y * |Real.exp (c y) - Z|) / Z := by
    rw [l1Dist, sum_div]
    refine sum_congr rfl fun y _ => ?_
    rw [hπ y]
    have h1 : p y * Real.exp (c y) / Z - p y = p y * (Real.exp (c y) - Z) / Z := by
      field_simp
    rw [h1, abs_div, abs_mul, abs_of_pos (hpos y), abs_of_pos hZpos]
  -- pointwise: `|e^c - Z| ≤ c² + |c| + (Z - 1)`
  have hpt : ∀ y, |Real.exp (c y) - Z| ≤ c y ^ 2 + |c y| + (Z - 1) := by
    intro y
    have h1 := abs_le.1 (Real.abs_exp_sub_one_sub_id_le (hc y))
    have h2 := le_abs_self (c y)
    have h3 := neg_abs_le (c y)
    rw [abs_le]
    constructor <;> linarith
  have hS : ∑ y, p y * |Real.exp (c y) - Z| ≤ A + 2 * V := by
    calc ∑ y, p y * |Real.exp (c y) - Z| ≤ ∑ y, p y * (c y ^ 2 + |c y| + (Z - 1)) :=
          sum_le_sum fun y _ => mul_le_mul_of_nonneg_left (hpt y) (hpos y).le
      _ = V + A + (Z - 1) := by
          simp only [mul_add, sum_add_distrib, hsumV, hsumA, ← sum_mul, htot, one_mul]
      _ ≤ A + 2 * V := by linarith
  have hS0 : 0 ≤ ∑ y, p y * |Real.exp (c y) - Z| :=
    sum_nonneg fun y _ => mul_nonneg (hpos y).le (abs_nonneg _)
  rw [hl1]
  exact (div_le_self hS0 hZ1).trans hS
