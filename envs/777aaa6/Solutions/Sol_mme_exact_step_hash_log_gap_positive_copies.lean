-- Prove2me | solution 1 for mme_exact_step_hash_log_gap_positive_copies
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-22T14:07:11.542011+00:00
-- url     : https://prove2.me/submissions/fd1f671b-e5d8-4697-bf5e-b2345c625e36

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Ring
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
private theorem mme_exact_step_positive_copies_log_lower_bound
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


/-- The selected-count bound separates into the target count, hash scale,
and the subexponential progression loss after taking logarithms. -/
private theorem mme_hash_selected_bound_log (A Q : ℝ) (hA : 0 < A) (hQ : 0 < Q) :
    Real.log (A * Real.exp (-4 * Real.sqrt (Real.log Q)) / (32 * Q)) =
      Real.log A - Real.log Q - 4 * Real.sqrt (Real.log Q) - Real.log 32 := by
  rw [Real.log_div (mul_pos hA (Real.exp_pos _)).ne' (mul_pos (by norm_num) hQ).ne',
    Real.log_mul hA.ne' (Real.exp_ne_zero _), Real.log_exp,
    Real.log_mul (by norm_num : (32 : ℝ) ≠ 0) hQ.ne']
  ring

/-- A logarithmic gap between the target count and hash losses pays the
repair budget and gives an explicit positive-copy rate for the exact step. -/
theorem solution
    {ell N : ℕ} {P : Predicate N} (E : ExactStep ell N P)
    (A Q : ℝ) (hA : 0 < A) (hQ : 0 < Q)
    (hcount : A * Real.exp (-4 * Real.sqrt (Real.log Q)) / (32 * Q) ≤ E.count)
    (hgap : Real.log 32 + Real.log 2 +
      (E.stage.repairExponent : ℝ) * Real.log 8 ≤
      Real.log A - Real.log Q - 4 * Real.sqrt (Real.log Q)) :
    0 < E.copies ∧ Real.log A - Real.log Q - 4 * Real.sqrt (Real.log Q) -
      (E.stage.repairExponent : ℝ) * Real.log 8 - Real.log 32 - Real.log 2 <
        Real.log E.copies := by
  let B := A * Real.exp (-4 * Real.sqrt (Real.log Q)) / (32 * Q)
  have hB : 0 < B := div_pos (mul_pos hA (Real.exp_pos _)) (mul_pos (by norm_num) hQ)
  have hD : 0 < 2 * (8 : ℝ) ^ E.stage.repairExponent :=
    mul_pos (by norm_num) (pow_pos (by norm_num) _)
  have hlog := mme_hash_selected_bound_log A Q hA hQ
  have hlarge : 2 * (8 : ℝ) ^ E.stage.repairExponent ≤ B := by
    apply (Real.log_le_log_iff hD hB).mp
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (pow_ne_zero _ (by norm_num)),
      Real.log_pow]
    change Real.log 2 + _ ≤ Real.log
      (A * Real.exp (-4 * Real.sqrt (Real.log Q)) / (32 * Q))
    rw [hlog]
    linarith
  obtain ⟨hpos, hrate⟩ := mme_exact_step_positive_copies_log_lower_bound E hcount hlarge
  refine ⟨hpos, ?_⟩
  rw [hlog] at hrate
  linarith


#print axioms solution
