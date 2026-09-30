-- Prove2me | solution 1 for lean_workbook_plus_17334
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T07:59:24.565219+00:00
-- url     : https://prove2.me/submissions/53032753-4b0f-45bb-bd5d-b87da1ebcabc

import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open MeasureTheory Set Filter
open scoped Topology

noncomputable def fourFactorKernel (t : ℝ) : ℝ :=
  (1 - t) ^ 2 / (6 * (1 + t) * (1 + t ^ 2))

theorem four_factor_beta_integral (k : ℕ) :
    (∫ t : ℝ in 0..1, t ^ k * (1 - t) ^ 3 / 6) =
      1 / ((k : ℝ) + 1) / (k + 2) / (k + 3) / (k + 4) := by
  have hi (j : ℕ) : IntervalIntegrable (fun t : ℝ => t ^ j) volume 0 1 :=
    (continuous_id.pow j).intervalIntegrable 0 1
  have hp : (fun t : ℝ => t ^ k * (1 - t) ^ 3 / 6) =
      fun t => (t ^ k - 3 * t ^ (k + 1) + 3 * t ^ (k + 2) - t ^ (k + 3)) / 6 := by
    funext t
    simp only [pow_add]
    ring
  rw [hp, intervalIntegral.integral_div,
    intervalIntegral.integral_sub ((hi k).sub ((hi (k + 1)).const_mul 3) |>.add
      ((hi (k + 2)).const_mul 3)) (hi (k + 3)),
    intervalIntegral.integral_add ((hi k).sub ((hi (k + 1)).const_mul 3))
      ((hi (k + 2)).const_mul 3),
    intervalIntegral.integral_sub (hi k) ((hi (k + 1)).const_mul 3)]
  simp only [intervalIntegral.integral_const_mul, integral_pow,
    one_pow, zero_pow (Nat.succ_ne_zero _), sub_zero, Nat.cast_add, Nat.cast_one,
    Nat.cast_ofNat]
  have h1 : (k : ℝ) + 1 ≠ 0 := by positivity
  have h2 : (k : ℝ) + 2 ≠ 0 := by positivity
  have h3 : (k : ℝ) + 3 ≠ 0 := by positivity
  have h4 : (k : ℝ) + 4 ≠ 0 := by positivity
  field_simp
  ring

theorem four_factor_geometric_hasSum (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    HasSum (fun n : ℕ => t ^ (4 * n) * (1 - t) ^ 3 / 6) (fourFactorKernel t) := by
  by_cases he : t = 1
  · subst t
    simpa [fourFactorKernel] using (hasSum_zero : HasSum (fun _ : ℕ => (0 : ℝ)) 0)
  have ht1 : t < 1 := lt_of_le_of_ne ht.2 he
  have hp : t ^ 4 < 1 := pow_lt_one₀ ht.1 ht1 (by decide)
  have hg := (hasSum_geometric_of_lt_one (pow_nonneg ht.1 4) hp).mul_right
    ((1 - t) ^ 3 / 6)
  have hn : 1 - t ^ 4 ≠ 0 := by linarith
  have ha : 1 + t ≠ 0 := by linarith [ht.1]
  have hb : 1 + t ^ 2 ≠ 0 := by positivity
  convert hg using 1
  · funext n
    rw [pow_mul]
    ring
  · dsimp [fourFactorKernel]
    field_simp
    ring

theorem four_factor_kernel_continuous :
    ContinuousOn fourFactorKernel (Icc (0 : ℝ) 1) := by
  apply ContinuousOn.div
    ((continuous_const.sub continuous_id).pow 2).continuousOn
    (by fun_prop)
  intro t ht
  have ha : 0 < 1 + t := by linarith [ht.1]
  positivity

theorem four_factor_kernel_integral :
    (∫ t : ℝ in 0..1, fourFactorKernel t) = Real.log 2 / 4 - Real.pi / 24 := by
  let F : ℝ → ℝ := fun t =>
    Real.log (1 + t) / 3 - Real.log (1 + t ^ 2) / 12 - Real.arctan t / 6
  have hd (t : ℝ) (ht : t ∈ uIcc (0 : ℝ) 1) : HasDerivAt F (fourFactorKernel t) t := by
    rw [uIcc_of_le (by norm_num)] at ht
    have ha : 1 + t ≠ 0 := by linarith [ht.1]
    have hb : 1 + t ^ 2 ≠ 0 := by positivity
    have h := (((((hasDerivAt_id t).const_add 1).log ha).div_const 3).sub
      (((((hasDerivAt_id t).pow 2).const_add 1).log hb).div_const 12)).sub
      ((Real.hasDerivAt_arctan t).div_const 6)
    convert h using 1
    dsimp [fourFactorKernel]
    field_simp
    ring
  have hi : IntervalIntegrable fourFactorKernel volume 0 1 :=
    four_factor_kernel_continuous.intervalIntegrable_of_Icc (by norm_num)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi]
  dsimp [F]
  rw [Real.arctan_one, Real.arctan_zero]
  rw [show (0 : ℝ) ^ 2 = 0 by ring]
  simp only [one_pow, add_zero, Real.log_one, zero_div, sub_zero]
  rw [show (1 : ℝ) + 1 = 2 by ring]
  ring

theorem four_factor_series_hasSum :
    HasSum (fun n : ℕ => 1 / (4 * (n : ℝ) + 1) / (4 * n + 2) /
      (4 * n + 3) / (4 * n + 4)) (Real.log 2 / 4 - Real.pi / 24) := by
  let f : ℕ → ℝ → ℝ := fun n t => t ^ (4 * n) * (1 - t) ^ 3 / 6
  have hs (t : ℝ) (ht : t ∈ uIoc (0 : ℝ) 1) : HasSum (fun n => f n t) (fourFactorKernel t) := by
    apply four_factor_geometric_hasSum
    rw [uIoc_of_le (by norm_num)] at ht
    exact ⟨ht.1.le, ht.2⟩
  have hi : IntervalIntegrable (fun t => ∑' n, f n t) volume 0 1 := by
    apply (intervalIntegrable_congr (fun t ht => (hs t ht).tsum_eq)).mpr
    exact four_factor_kernel_continuous.intervalIntegrable_of_Icc (by norm_num)
  have h := intervalIntegral.hasSum_integral_of_dominated_convergence f
    (fun n => (show Continuous (f n) by dsimp [f]; fun_prop).aestronglyMeasurable)
    (fun n => ae_of_all _ fun t ht => by
      rw [uIoc_of_le (by norm_num)] at ht
      have hn : 0 ≤ f n t := by
        dsimp [f]
        exact div_nonneg (mul_nonneg (pow_nonneg ht.1.le _)
          (pow_nonneg (sub_nonneg.mpr ht.2) _)) (by norm_num)
      rw [Real.norm_of_nonneg hn])
    (ae_of_all _ fun t ht => (hs t ht).summable) hi
    (ae_of_all _ fun t ht => hs t ht)
  rw [four_factor_kernel_integral] at h
  apply h.congr_fun
  intro n
  dsimp [f]
  rw [four_factor_beta_integral]
  simp only [Nat.cast_mul, Nat.cast_ofNat]

theorem solution (u : ℕ → ℝ)
    (h : ∀ n, u n = 1 / (4 * n + 1) / (4 * n + 2) / (4 * n + 3) / (4 * n + 4)) :
    ∃ l, ∑' n : ℕ, u n = l := by
  refine ⟨Real.log 2 / 4 - Real.pi / 24, ?_⟩
  exact (four_factor_series_hasSum.congr_fun h).tsum_eq

#print axioms fourFactorKernel
#print axioms four_factor_beta_integral
#print axioms four_factor_geometric_hasSum
#print axioms four_factor_kernel_continuous
#print axioms four_factor_kernel_integral
#print axioms four_factor_series_hasSum
#print axioms solution
