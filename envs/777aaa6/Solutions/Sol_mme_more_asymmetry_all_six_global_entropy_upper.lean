-- Prove2me | solution 1 for mme_more_asymmetry_all_six_global_entropy_upper
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-07T05:03:58.120316+00:00
-- url     : https://prove2.me/submissions/54cc9f4c-2547-4258-b261-5b7b0287212d

import Definitions.Def_mme_more_asymmetry_rational_global_entropy_data
import Theorems.Thm_mme_log_interval_of_exact_rational_series_certificate
import Theorems.Thm_mme_modern_entropyNat_upper_from_positive_reference
import Mathlib.Tactic.NormNum

open MME.MoreAsymmetryGlobalWitness BigOperators Finset
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

private def seriesLength : Fin 6 → Fin 45 → ℕ :=
  ![![1, 2, 1, 3, 4, 3, 1, 2, 1, 2, 3, 3, 4, 4, 3, 3, 2, 5, 3, 2, 1, 2, 3, 1, 3, 4, 1, 1, 4, 3, 4, 4, 2, 4, 4, 3, 3, 3, 3, 2, 3, 1, 2, 2, 2], ![1, 4, 2, 4, 6, 4, 1, 4, 1, 3, 5, 4, 5, 5, 4, 4, 3, 1, 4, 3, 1, 3, 4, 7, 3, 5, 1, 1, 5, 3, 6, 5, 3, 5, 6, 3, 4, 4, 4, 2, 5, 2, 4, 4, 1], ![2, 2, 6, 3, 4, 3, 2, 2, 1, 2, 3, 3, 4, 4, 3, 4, 2, 1, 3, 2, 1, 2, 3, 1, 3, 4, 1, 1, 4, 3, 4, 4, 2, 4, 4, 3, 3, 3, 3, 1, 4, 1, 2, 2, 2], ![1, 2, 1, 3, 5, 3, 1, 2, 2, 2, 4, 3, 4, 4, 3, 4, 2, 2, 3, 3, 1, 3, 3, 2, 3, 4, 1, 1, 4, 3, 5, 4, 3, 4, 5, 3, 3, 3, 3, 1, 4, 6, 2, 2, 1], ![1, 3, 2, 3, 5, 3, 7, 2, 1, 2, 4, 4, 5, 5, 4, 4, 2, 2, 4, 3, 1, 3, 4, 1, 3, 5, 1, 1, 5, 3, 5, 5, 3, 5, 5, 3, 4, 4, 3, 1, 4, 2, 2, 3, 2], ![2, 2, 1, 3, 4, 2, 1, 2, 1, 2, 3, 3, 4, 4, 3, 3, 2, 2, 3, 2, 1, 2, 3, 1, 3, 4, 1, 1, 4, 3, 4, 4, 2, 4, 4, 3, 3, 3, 3, 5, 3, 1, 2, 2, 1]]

private theorem rational_certificates :
    ∀ (r : Fin 6) (a : Fin 45),
      let q := reference r a
      let t := logParameter r a
      let k := logScale r a
      let n := seriesLength r a
      0 < q ∧ 0 ≤ t ∧ t < 1 ∧
      q * 2 ^ k = (1 + t) / (1 - t) ∧
      logLower r a + k * (69314718057 / 100000000000 : ℚ) ≤
        2 * ∑ i ∈ range n, t ^ (2 * i + 1) / (2 * i + 1) ∧
      2 * ((∑ i ∈ range n, t ^ (2 * i + 1) / (2 * i + 1)) +
        t ^ (2 * n + 1) / (1 - t ^ 2)) -
        k * (69314718055 / 100000000000 : ℚ) ≤ 0 := by decide +kernel

private theorem all_logs (r : Fin 6) (a : Fin 45) :
    (logLower r a : ℝ) ≤ Real.log (reference r a : ℝ) := by
  obtain ⟨hq, ht0, ht1, hscale, hlo, hhi⟩ := rational_certificates r a
  exact (mme_log_interval_of_exact_rational_series_certificate
    (reference r a) (logParameter r a) (logLower r a) 0
    (logScale r a) (seriesLength r a) hq ht0 ht1 hscale hlo hhi).1

private theorem alpha_sum_rational : ∀ r : Fin 6, ∑ a, alpha r a = 1 := by decide +kernel
private theorem reference_sum_rational : ∀ r : Fin 6, ∑ a, reference r a = 1 := by decide +kernel
private theorem reference_pos_rational : ∀ (r : Fin 6) (a : Fin 45), 0 < reference r a := by decide +kernel
private theorem potential_bound_rational : ∀ r : Fin 6,
    -(∑ a, alpha r a * potential r a) + epsilon r ≤ entropyUpper r := by decide +kernel

theorem solution (r : Fin 6) (rho : Fin 45 → ℝ)
    (hrho : ∀ a, 0 ≤ rho a) (hrhoSum : ∑ a, rho a = 1)
    (hmarg : ∀ (mode : Fin 3) (j : Fin 9),
      mme_modern_marginal (fun a ↦ coarseAddress a mode) rho j =
      mme_modern_marginal (fun a ↦ coarseAddress a mode)
        (fun a ↦ (alpha r a : ℝ)) j) :
    (∑ a, Real.negMulLog (rho a)) ≤ (entropyUpper r : ℝ) := by
  have hy : ∀ a, (0 : ℝ) < (reference r a : ℝ) := by
    intro a
    exact_mod_cast reference_pos_rational r a
  have halphaSum : ∑ a, (alpha r a : ℝ) = 1 := by
    exact_mod_cast alpha_sum_rational r
  have hySum : ∑ a, (reference r a : ℝ) = 1 := by
    exact_mod_cast reference_sum_rational r
  have hlog : ∀ a,
      (lambdaZero r : ℝ) +
        (lambdaModes r 0 (coarseAddress a 0) : ℝ) +
        (lambdaModes r 1 (coarseAddress a 1) : ℝ) +
        (lambdaModes r 2 (coarseAddress a 2) : ℝ) -
        (epsilon r : ℝ) ≤ Real.log (reference r a : ℝ) := by
    intro a
    have h := all_logs r a
    simpa only [logLower, potential, Rat.cast_sub, Rat.cast_add] using h
  have h := mme_modern_entropyNat_upper_from_positive_reference
    (fun a ↦ coarseAddress a 0) (fun a ↦ coarseAddress a 1)
    (fun a ↦ coarseAddress a 2) rho
    (fun a ↦ (alpha r a : ℝ)) (fun a ↦ (reference r a : ℝ))
    (lambdaZero r : ℝ) (fun j ↦ (lambdaModes r 0 j : ℝ))
    (fun j ↦ (lambdaModes r 1 j : ℝ)) (fun j ↦ (lambdaModes r 2 j : ℝ))
    (epsilon r : ℝ) hrho hy hrhoSum halphaSum hySum
    (hmarg 0) (hmarg 1) (hmarg 2) hlog
  have hbound : -(∑ a, (alpha r a : ℝ) * (potential r a : ℝ)) +
      (epsilon r : ℝ) ≤ (entropyUpper r : ℝ) := by
    exact_mod_cast potential_bound_rational r
  apply h.trans
  simpa only [potential, Rat.cast_add] using hbound
