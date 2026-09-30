-- Prove2me | solution 1 for lean_workbook_plus_9574
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T08:02:09.321727+00:00
-- url     : https://prove2.me/submissions/1e1d4740-dce1-4b4c-add7-5ae1ea8fbb1a

import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open MeasureTheory Set Filter Finset
open scoped Topology

noncomputable def fourPeriodicSign (n : ℕ) : ℝ :=
  (-1) ^ (((n + 1) * (n + 4)) / 2)

noncomputable def fourPeriodicHarmonic (n : ℕ) : ℝ :=
  fourPeriodicSign n / (n + 1)

theorem four_periodic_sign_initial : fourPeriodicSign 0 = 1 ∧ fourPeriodicSign 1 = -1 := by
  change (-1 : ℝ) ^ 2 = 1 ∧ (-1 : ℝ) ^ 5 = -1
  constructor <;> ring

theorem four_periodic_sign_antiperiod (n : ℕ) :
    fourPeriodicSign (n + 2) = -fourPeriodicSign n := by
  have he : (n + 2 + 1) * (n + 2 + 4) = (n + 1) * (n + 4) + 2 * (2 * n + 7) := by ring
  unfold fourPeriodicSign
  rw [he, Nat.add_mul_div_left, pow_add, pow_add, pow_mul]
  · rw [show (-1 : ℝ) ^ 2 = 1 by ring, one_pow,
      show (-1 : ℝ) ^ 7 = -1 by ring]
    ring
  · decide

theorem four_periodic_sign_period (n : ℕ) : fourPeriodicSign (n + 4) = fourPeriodicSign n := by
  rw [show n + 4 = (n + 2) + 2 by omega, four_periodic_sign_antiperiod,
    four_periodic_sign_antiperiod, neg_neg]

theorem four_periodic_sign_abs (n : ℕ) : |fourPeriodicSign n| = 1 := by
  exact abs_neg_one_pow _

theorem four_periodic_finite_generating (N : ℕ) (t : ℝ) :
    (1 + t ^ 2) * (∑ n ∈ range N, fourPeriodicSign n * t ^ n) =
      1 - t - fourPeriodicSign N * t ^ N - fourPeriodicSign (N + 1) * t ^ (N + 1) := by
  induction N with
  | zero => simp [four_periodic_sign_initial.1, four_periodic_sign_initial.2]
  | succ N ih =>
      rw [sum_range_succ, mul_add, ih, show N + 1 + 1 = N + 2 by omega,
        four_periodic_sign_antiperiod]
      simp only [pow_succ]
      ring

theorem four_periodic_partial_polynomial (N : ℕ) (t : ℝ) :
    (∑ n ∈ range N, fourPeriodicSign n * t ^ n) =
      (1 - t - fourPeriodicSign N * t ^ N - fourPeriodicSign (N + 1) * t ^ (N + 1)) /
        (1 + t ^ 2) := by
  apply (eq_div_iff (by positivity : (1 : ℝ) + t ^ 2 ≠ 0)).mpr
  rw [mul_comm]
  exact four_periodic_finite_generating N t

theorem four_periodic_partial_bound (N : ℕ) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    |∑ n ∈ range N, fourPeriodicSign n * t ^ n| ≤ 3 := by
  have hab (n : ℕ) : |fourPeriodicSign n * t ^ n| = t ^ n := by
    rw [abs_mul, four_periodic_sign_abs, one_mul, abs_of_nonneg (pow_nonneg ht.1 _)]
  have hp (n : ℕ) : t ^ n ≤ 1 := pow_le_one₀ ht.1 ht.2
  have hb : |1 - t - fourPeriodicSign N * t ^ N - fourPeriodicSign (N + 1) * t ^ (N + 1)| ≤ 3 := by
    have h1 := abs_sub (1 - t) (fourPeriodicSign N * t ^ N)
    have h2 := abs_sub (1 - t - fourPeriodicSign N * t ^ N)
      (fourPeriodicSign (N + 1) * t ^ (N + 1))
    rw [abs_of_nonneg (sub_nonneg.mpr ht.2), hab N] at h1
    rw [hab (N + 1)] at h2
    linarith [hp N, hp (N + 1), ht.1]
  rw [four_periodic_partial_polynomial, abs_div,
    abs_of_pos (by positivity : (0 : ℝ) < 1 + t ^ 2)]
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 1 + t ^ 2)).mpr
  nlinarith [sq_nonneg t]

theorem four_periodic_partial_limit (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t < 1) :
    Tendsto (fun N => ∑ n ∈ range N, fourPeriodicSign n * t ^ n)
      atTop (𝓝 ((1 - t) / (1 + t ^ 2))) := by
  have hp : Tendsto (fun N : ℕ => t ^ N) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one ht0 ht1
  have hc : Tendsto (fun N : ℕ => fourPeriodicSign N * t ^ N) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simpa only [Real.norm_eq_abs, abs_mul, four_periodic_sign_abs, one_mul,
      abs_of_nonneg (pow_nonneg ht0 _)] using hp
  have hc' : Tendsto (fun N : ℕ => fourPeriodicSign (N + 1) * t ^ (N + 1)) atTop (𝓝 0) :=
    (tendsto_add_atTop_iff_nat 1).mpr hc
  simp_rw [four_periodic_partial_polynomial]
  simpa only [sub_zero] using ((tendsto_const_nhds.sub hc).sub hc').div_const (1 + t ^ 2)

theorem four_periodic_integral_partial (N : ℕ) :
    (∫ t : ℝ in 0..1, ∑ n ∈ range N, fourPeriodicSign n * t ^ n) =
      ∑ n ∈ range N, fourPeriodicHarmonic n := by
  rw [intervalIntegral.integral_finset_sum]
  · apply sum_congr rfl
    intro n hn
    rw [intervalIntegral.integral_const_mul, integral_pow]
    simp only [one_pow, zero_pow (Nat.succ_ne_zero _), sub_zero]
    dsimp [fourPeriodicHarmonic]
    ring
  · intro n hn
    exact (continuous_const.mul (continuous_id.pow n)).intervalIntegrable 0 1

theorem four_periodic_integral_value :
    (∫ t : ℝ in 0..1, (1 - t) / (1 + t ^ 2)) = Real.pi / 4 - Real.log 2 / 2 := by
  let F : ℝ → ℝ := fun t => Real.arctan t - Real.log (1 + t ^ 2) / 2
  have hd (t : ℝ) (ht : t ∈ uIcc (0 : ℝ) 1) :
      HasDerivAt F ((1 - t) / (1 + t ^ 2)) t := by
    have hb : 1 + t ^ 2 ≠ 0 := by positivity
    have h := (Real.hasDerivAt_arctan t).sub
      (((((hasDerivAt_id t).pow 2).const_add 1).log hb).div_const 2)
    convert h using 1
    dsimp only [id_eq, Pi.pow_apply]
    field_simp
    ring
  have hi : IntervalIntegrable (fun t : ℝ => (1 - t) / (1 + t ^ 2)) volume 0 1 :=
    (show Continuous (fun t : ℝ => (1 - t) / (1 + t ^ 2)) from
      (continuous_const.sub continuous_id).div (by fun_prop) (fun _ => by positivity)).intervalIntegrable 0 1
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi]
  dsimp [F]
  rw [Real.arctan_one, Real.arctan_zero, show (0 : ℝ) ^ 2 = 0 by ring]
  simp only [one_pow, add_zero, Real.log_one, zero_div, sub_zero]
  rw [show (1 : ℝ) + 1 = 2 by ring]

theorem four_periodic_harmonic_ordered_value :
    Tendsto (fun N => ∑ n ∈ range N, fourPeriodicHarmonic n) atTop
      (𝓝 (Real.pi / 4 - Real.log 2 / 2)) := by
  have h := intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (μ := volume) (a := (0 : ℝ)) (b := 1)
    (F := fun N t => ∑ n ∈ range N, fourPeriodicSign n * t ^ n)
    (fun _ => (3 : ℝ))
    (Eventually.of_forall fun N => (show Continuous
      (fun t : ℝ => ∑ n ∈ range N, fourPeriodicSign n * t ^ n) by fun_prop).aestronglyMeasurable)
    (Eventually.of_forall fun N => ae_of_all _ fun t ht => by
      rw [uIoc_of_le (by norm_num)] at ht
      exact four_periodic_partial_bound N t ⟨ht.1.le, ht.2⟩)
    intervalIntegrable_const
    (by
      filter_upwards [volume.ae_ne (1 : ℝ)] with t hne ht
      rw [uIoc_of_le (by norm_num)] at ht
      exact four_periodic_partial_limit t ht.1.le (lt_of_le_of_ne ht.2 hne))
  simpa only [four_periodic_integral_partial, four_periodic_integral_value] using h

theorem four_periodic_harmonic_abs (n : ℕ) : |fourPeriodicHarmonic n| = 1 / (n + 1) := by
  simp only [fourPeriodicHarmonic, abs_div, four_periodic_sign_abs,
    abs_of_pos (show 0 < (n : ℝ) + 1 by positivity)]

theorem four_periodic_harmonic_not_absolutely_summable :
    ¬ Summable (fun n => |fourPeriodicHarmonic n|) := by
  simp only [four_periodic_harmonic_abs]
  intro h
  apply Real.not_summable_one_div_natCast
  apply (summable_nat_add_iff 1).mp
  simpa only [Nat.cast_add, Nat.cast_one] using h

theorem four_periodic_harmonic_not_summable : ¬ Summable fourPeriodicHarmonic :=
  fun h => four_periodic_harmonic_not_absolutely_summable h.abs

theorem four_periodic_harmonic_absolute_divergence :
    Tendsto (fun N => ∑ n ∈ range N, |fourPeriodicHarmonic n|) atTop atTop := by
  rw [← not_summable_iff_tendsto_nat_atTop_of_nonneg (fun n => abs_nonneg (fourPeriodicHarmonic n))]
  exact four_periodic_harmonic_not_absolutely_summable

theorem four_periodic_harmonic_source (n : ℕ) :
    fourPeriodicHarmonic n = (-1 : ℝ) ^ (((n + 1) * (n + 1 + 3)) / 2) / ((n : ℝ) + 1) := by
  simp only [fourPeriodicHarmonic, fourPeriodicSign, Nat.add_assoc, Nat.reduceAdd]

theorem solution : ∀ n : ℕ, |(-1 : ℝ) ^ ((n * (n + 3)) / 2) / n| = 1 / n := by
  intro n
  simp only [abs_div, abs_neg_one_pow,
    abs_of_nonneg (show (0 : ℝ) ≤ (n : ℝ) by positivity)]

#print axioms fourPeriodicSign
#print axioms fourPeriodicHarmonic
#print axioms four_periodic_sign_initial
#print axioms four_periodic_sign_antiperiod
#print axioms four_periodic_sign_period
#print axioms four_periodic_sign_abs
#print axioms four_periodic_finite_generating
#print axioms four_periodic_partial_polynomial
#print axioms four_periodic_partial_bound
#print axioms four_periodic_partial_limit
#print axioms four_periodic_integral_partial
#print axioms four_periodic_integral_value
#print axioms four_periodic_harmonic_ordered_value
#print axioms four_periodic_harmonic_abs
#print axioms four_periodic_harmonic_not_absolutely_summable
#print axioms four_periodic_harmonic_not_summable
#print axioms four_periodic_harmonic_absolute_divergence
#print axioms four_periodic_harmonic_source
#print axioms solution
