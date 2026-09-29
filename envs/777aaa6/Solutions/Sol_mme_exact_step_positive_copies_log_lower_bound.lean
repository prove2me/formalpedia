-- Prove2me | solution 1 for mme_exact_step_positive_copies_log_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-22T14:02:24.943085+00:00
-- url     : https://prove2.me/submissions/268fb2c4-0539-4824-8d28-3c9dbb6539d2

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Theorems.Thm_mme_recursive_profiled_CW_exact_step
import Definitions.Def_mme_recursive_profiled_CW_data
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

open MME MME.ProfiledCW
set_option autoImplicit false

/-- Repair divides the selected count by its power-of-eight budget;
the integer rounding loses strictly less than one additional copy. -/
private theorem mme_exact_step_copies_gt_normalized_count_sub_one
    {ell N : ℕ} {P : Predicate N} (E : ExactStep ell N P) {B : ℝ}
    (hB : B ≤ E.count) :
    B / (8 : ℝ) ^ E.stage.repairExponent - 1 < E.copies := by
  have hd : 0 < 8 ^ E.stage.repairExponent := pow_pos (by decide) _
  have hn : E.count < 8 ^ E.stage.repairExponent * (E.copies + 1) := by
    have hmod := Nat.mod_lt E.count hd
    have h := Nat.mod_add_div E.count (8 ^ E.stage.repairExponent)
    dsimp [ExactStep.copies]
    nlinarith
  have hr : (E.count : ℝ) < (8 : ℝ) ^ E.stage.repairExponent * ((E.copies : ℝ) + 1) := by
    exact_mod_cast hn
  have hdR : 0 < (8 : ℝ) ^ E.stage.repairExponent := pow_pos (by norm_num) _
  have h : B / (8 : ℝ) ^ E.stage.repairExponent < (E.copies : ℝ) + 1 :=
    (div_lt_iff₀ hdR).mpr (hB.trans_lt (by simpa only [mul_comm] using hr))
  linarith


/-- Once the selected-count lower bound is at least twice the repair budget,
there are surviving copies and their log count loses only the explicit repair
cost and one log-two rounding allowance. -/
theorem solution
    {ell N : ℕ} {P : Predicate N} (E : ExactStep ell N P) {B : ℝ}
    (hB : B ≤ E.count) (hlarge : 2 * (8 : ℝ) ^ E.stage.repairExponent ≤ B) :
    0 < E.copies ∧ Real.log B -
      (E.stage.repairExponent : ℝ) * Real.log 8 - Real.log 2 < Real.log E.copies := by
  let D : ℝ := (8 : ℝ) ^ E.stage.repairExponent
  have hD : 0 < D := pow_pos (by norm_num) _
  have hBpos : 0 < B := lt_of_lt_of_le (mul_pos (by norm_num) hD) hlarge
  have htwo : 2 ≤ B / D := (le_div_iff₀ hD).mpr hlarge
  have hcopy := mme_exact_step_copies_gt_normalized_count_sub_one E hB
  have hlower : B / D / 2 < (E.copies : ℝ) := by
    change B / D - 1 < (E.copies : ℝ) at hcopy
    linarith
  have hpos : 0 < B / D / 2 := div_pos (div_pos hBpos hD) (by norm_num)
  have hcopies : 0 < (E.copies : ℝ) := hpos.trans hlower
  refine ⟨by exact_mod_cast hcopies, ?_⟩
  have hlog := Real.log_lt_log hpos hlower
  rw [Real.log_div (div_pos hBpos hD).ne' (by norm_num : (2 : ℝ) ≠ 0),
    Real.log_div hBpos.ne' hD.ne'] at hlog
  simpa only [D, Real.log_pow] using hlog


#print axioms solution
