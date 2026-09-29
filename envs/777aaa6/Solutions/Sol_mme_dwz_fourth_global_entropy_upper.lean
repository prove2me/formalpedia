-- Prove2me | solution 1 for mme_dwz_fourth_global_entropy_upper
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-07T06:49:55.04929+00:00
-- url     : https://prove2.me/submissions/da30b90d-25c1-40bc-b011-b504eb9b2429

import Definitions.Def_mme_dwz_fourth_rational_global_entropy_data
import Theorems.Thm_mme_log_interval_of_exact_rational_series_certificate
import Theorems.Thm_mme_modern_entropyNat_upper_from_positive_reference
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

open MME.DWZFourthGlobalWitness BigOperators Finset
set_option autoImplicit false
set_option warningAsError true

private def seriesLength : Fin 45 → ℕ :=
  ![4, 2, 7, 4, 6, 4, 2, 3, 4, 2, 4, 4, 5, 5, 4, 4, 3, 7, 4, 3, 1, 3, 4, 2, 4, 5, 1, 1, 5, 4, 6, 5, 3, 5, 6, 4, 4, 4, 4, 2, 4, 2, 3, 3, 4]

private abbrev Certified (a : Fin 45) : Prop :=
  let q := reference a
  let t := logParameter a
  let k := logScale a
  let n := seriesLength a
  0 < q ∧ 0 ≤ t ∧ t < 1 ∧
  q * 2 ^ k = (1 + t) / (1 - t) ∧
  logLower a + k * (69314718057 / 100000000000 : ℚ) ≤
    2 * ∑ i ∈ range n, t ^ (2 * i + 1) / (2 * i + 1) ∧
  2 * ((∑ i ∈ range n, t ^ (2 * i + 1) / (2 * i + 1)) +
    t ^ (2 * n + 1) / (1 - t ^ 2)) -
    k * (69314718055 / 100000000000 : ℚ) ≤ 0

private theorem cert_0 : Certified 0 := by decide +kernel
private theorem cert_1 : Certified 1 := by decide +kernel
private theorem cert_2 : Certified 2 := by decide +kernel
private theorem cert_3 : Certified 3 := by decide +kernel
private theorem cert_4 : Certified 4 := by decide +kernel
private theorem cert_5 : Certified 5 := by decide +kernel
private theorem cert_6 : Certified 6 := by decide +kernel
private theorem cert_7 : Certified 7 := by decide +kernel
private theorem cert_8 : Certified 8 := by decide +kernel
private theorem cert_9 : Certified 9 := by decide +kernel
private theorem cert_10 : Certified 10 := by decide +kernel
private theorem cert_11 : Certified 11 := by decide +kernel
private theorem cert_12 : Certified 12 := by decide +kernel
private theorem cert_13 : Certified 13 := by decide +kernel
private theorem cert_14 : Certified 14 := by decide +kernel
private theorem cert_15 : Certified 15 := by decide +kernel
private theorem cert_16 : Certified 16 := by decide +kernel
private theorem cert_17 : Certified 17 := by decide +kernel
private theorem cert_18 : Certified 18 := by decide +kernel
private theorem cert_19 : Certified 19 := by decide +kernel
private theorem cert_20 : Certified 20 := by decide +kernel
private theorem cert_21 : Certified 21 := by decide +kernel
private theorem cert_22 : Certified 22 := by decide +kernel
private theorem cert_23 : Certified 23 := by decide +kernel
private theorem cert_24 : Certified 24 := by decide +kernel
private theorem cert_25 : Certified 25 := by decide +kernel
private theorem cert_26 : Certified 26 := by decide +kernel
private theorem cert_27 : Certified 27 := by decide +kernel
private theorem cert_28 : Certified 28 := by decide +kernel
private theorem cert_29 : Certified 29 := by decide +kernel
private theorem cert_30 : Certified 30 := by decide +kernel
private theorem cert_31 : Certified 31 := by decide +kernel
private theorem cert_32 : Certified 32 := by decide +kernel
private theorem cert_33 : Certified 33 := by decide +kernel
private theorem cert_34 : Certified 34 := by decide +kernel
private theorem cert_35 : Certified 35 := by decide +kernel
private theorem cert_36 : Certified 36 := by decide +kernel
private theorem cert_37 : Certified 37 := by decide +kernel
private theorem cert_38 : Certified 38 := by decide +kernel
private theorem cert_39 : Certified 39 := by decide +kernel
private theorem cert_40 : Certified 40 := by decide +kernel
private theorem cert_41 : Certified 41 := by decide +kernel
private theorem cert_42 : Certified 42 := by decide +kernel
private theorem cert_43 : Certified 43 := by decide +kernel
private theorem cert_44 : Certified 44 := by decide +kernel

private theorem certificates (a : Fin 45) : Certified a := by
  fin_cases a
  · exact cert_0
  · exact cert_1
  · exact cert_2
  · exact cert_3
  · exact cert_4
  · exact cert_5
  · exact cert_6
  · exact cert_7
  · exact cert_8
  · exact cert_9
  · exact cert_10
  · exact cert_11
  · exact cert_12
  · exact cert_13
  · exact cert_14
  · exact cert_15
  · exact cert_16
  · exact cert_17
  · exact cert_18
  · exact cert_19
  · exact cert_20
  · exact cert_21
  · exact cert_22
  · exact cert_23
  · exact cert_24
  · exact cert_25
  · exact cert_26
  · exact cert_27
  · exact cert_28
  · exact cert_29
  · exact cert_30
  · exact cert_31
  · exact cert_32
  · exact cert_33
  · exact cert_34
  · exact cert_35
  · exact cert_36
  · exact cert_37
  · exact cert_38
  · exact cert_39
  · exact cert_40
  · exact cert_41
  · exact cert_42
  · exact cert_43
  · exact cert_44

private theorem all_logs (a : Fin 45) :
    (logLower a : ℝ) ≤ Real.log (reference a : ℝ) := by
  obtain ⟨hq, ht0, ht1, hscale, hlo, hhi⟩ := certificates a
  exact (mme_log_interval_of_exact_rational_series_certificate
    (reference a) (logParameter a) (logLower a) 0
    (logScale a) (seriesLength a) hq ht0 ht1 hscale hlo hhi).1

private theorem alpha_sum : ∑ a, alpha a = 1 := by decide +kernel
private theorem reference_sum : ∑ a, reference a = 1 := by decide +kernel
private theorem reference_pos : ∀ a : Fin 45, 0 < reference a := by decide +kernel
private theorem upper_exact : -(∑ a, alpha a * potential a) + epsilon ≤ entropyUpper := by
  decide +kernel

theorem solution (rho : Fin 45 → ℝ)
    (hrho : ∀ a, 0 ≤ rho a) (hrhoSum : ∑ a, rho a = 1)
    (hmarg : ∀ (mode : Fin 3) (j : Fin 9),
      mme_modern_marginal (fun a ↦ coarseAddress a mode) rho j =
      mme_modern_marginal (fun a ↦ coarseAddress a mode)
        (fun a ↦ (alpha a : ℝ)) j) :
    (∑ a, Real.negMulLog (rho a)) ≤ (entropyUpper : ℝ) := by
  have hy : ∀ a, (0 : ℝ) < (reference a : ℝ) := by
    intro a
    exact_mod_cast reference_pos a
  have halphaSum : ∑ a, (alpha a : ℝ) = 1 := by
    exact_mod_cast alpha_sum
  have hySum : ∑ a, (reference a : ℝ) = 1 := by
    exact_mod_cast reference_sum
  have hlog : ∀ a,
      (lambdaZero : ℝ) + (lambdaModes 0 (coarseAddress a 0) : ℝ) +
        (lambdaModes 1 (coarseAddress a 1) : ℝ) +
        (lambdaModes 2 (coarseAddress a 2) : ℝ) -
        (epsilon : ℝ) ≤ Real.log (reference a : ℝ) := by
    intro a
    simpa only [logLower, potential, Rat.cast_sub, Rat.cast_add] using all_logs a
  have h := mme_modern_entropyNat_upper_from_positive_reference
    (fun a ↦ coarseAddress a 0) (fun a ↦ coarseAddress a 1)
    (fun a ↦ coarseAddress a 2) rho
    (fun a ↦ (alpha a : ℝ)) (fun a ↦ (reference a : ℝ))
    (lambdaZero : ℝ) (fun j ↦ (lambdaModes 0 j : ℝ))
    (fun j ↦ (lambdaModes 1 j : ℝ)) (fun j ↦ (lambdaModes 2 j : ℝ))
    (epsilon : ℝ) hrho hy hrhoSum halphaSum hySum
    (hmarg 0) (hmarg 1) (hmarg 2) hlog
  have hbound : -(∑ a, (alpha a : ℝ) * (potential a : ℝ)) +
      (epsilon : ℝ) ≤ (entropyUpper : ℝ) := by
    exact_mod_cast upper_exact
  apply h.trans
  simpa only [potential, Rat.cast_add] using hbound
