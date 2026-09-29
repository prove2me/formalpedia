-- Prove2me | solution 1 for mme_more_asymmetry_parent11_all_six_recursive_entropy_upper
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-07T05:30:05.099446+00:00
-- url     : https://prove2.me/submissions/d7e384fb-548b-45f1-8703-5deb8746a153

import Definitions.Def_mme_more_asymmetry_recursive_parent11_entropy_data
import Theorems.Thm_mme_log_interval_of_exact_rational_series_certificate
import Theorems.Thm_mme_modern_entropyNat_upper_from_positive_reference
import Mathlib.Tactic.NormNum

open MME.MoreAsymmetryRecursiveWitness11 BigOperators Finset
set_option autoImplicit false
set_option warningAsError true

private theorem source_coherence :
    (∀ a : Fin 4,
      (∑ mode : Fin 3, (leftAddress a mode).val) = 4 ∧
      (∑ mode : Fin 3, (rightAddress a mode).val) = 4 ∧
      ∀ mode : Fin 3,
        (leftAddress a mode).val + (rightAddress a mode).val =
          (parentAddress mode).val) ∧
    (∀ (r : Fin 6) (a : Fin 4) (mode : Fin 3),
      (offsetAddress a mode).val + lambdaLow mode = (leftAddress a mode).val ∧
      (offsetAddress a mode).val < lambdaWidth mode ∧
      lambdaModes r mode (leftAddress a mode) =
        lambdaPacked r mode (offsetAddress a mode)) ∧
    (∀ (r : Fin 6) (a : Fin 4),
      childAddress (leftChild r a) = leftAddress a ∧
      childAddress (rightChild r a) = rightAddress a ∧
      childSourceId (leftChild r a) = leftChildSourceId r a ∧
      childSourceId (rightChild r a) = rightChildSourceId r a ∧
      childParentId (leftChild r a) = parentSourceId ∧
      childParentId (rightChild r a) = parentSourceId ∧
      childRegion (leftChild r a) = r ∧
      childRegion (rightChild r a) = r) ∧
    (∀ (r : Fin 6) (a : Fin 4), 0 ≤ alpha r a) ∧
    (∀ r : Fin 6, 0 ≤ regionWeight r) ∧
    (∑ r : Fin 6, regionWeight r) = 1 := by decide +kernel

private theorem rational_certificates :
    ∀ (r : Fin 6) (a : Fin 4),
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

private theorem all_logs (r : Fin 6) (a : Fin 4) :
    (logLower r a : ℝ) ≤ Real.log (reference r a : ℝ) := by
  obtain ⟨hq, ht0, ht1, hscale, hlo, hhi⟩ := rational_certificates r a
  exact (mme_log_interval_of_exact_rational_series_certificate
    (reference r a) (logParameter r a) (logLower r a) 0
    (logScale r a) (seriesLength r a) hq ht0 ht1 hscale hlo hhi).1

private theorem alpha_sum_rational : ∀ r : Fin 6, ∑ a, alpha r a = 1 := by decide +kernel
private theorem reference_sum_rational : ∀ r : Fin 6, ∑ a, reference r a = 1 := by decide +kernel
private theorem reference_pos_rational : ∀ (r : Fin 6) (a : Fin 4), 0 < reference r a := by decide +kernel
private theorem potential_bound_rational : ∀ r : Fin 6,
    -(∑ a, alpha r a * potential r a) + epsilon r ≤ entropyUpper r := by decide +kernel

theorem solution (r : Fin 6) (rho : Fin 4 → ℝ)
    (hrho : ∀ a, 0 ≤ rho a) (hrhoSum : ∑ a, rho a = 1)
    (hmarg : ∀ (mode : Fin 3) (j : Fin 5),
      mme_modern_marginal (fun a ↦ leftAddress a mode) rho j =
      mme_modern_marginal (fun a ↦ leftAddress a mode)
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
        (lambdaModes r 0 (leftAddress a 0) : ℝ) +
        (lambdaModes r 1 (leftAddress a 1) : ℝ) +
        (lambdaModes r 2 (leftAddress a 2) : ℝ) -
        (epsilon r : ℝ) ≤ Real.log (reference r a : ℝ) := by
    intro a
    have h := all_logs r a
    simpa only [logLower, potential, Rat.cast_sub, Rat.cast_add] using h
  have h := mme_modern_entropyNat_upper_from_positive_reference
    (fun a ↦ leftAddress a 0) (fun a ↦ leftAddress a 1)
    (fun a ↦ leftAddress a 2) rho
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

