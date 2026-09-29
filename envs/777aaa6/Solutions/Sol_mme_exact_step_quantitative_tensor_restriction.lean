-- Prove2me | solution 1 for mme_exact_step_quantitative_tensor_restriction
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-22T13:55:22.761281+00:00
-- url     : https://prove2.me/submissions/785508bc-0315-4368-9c11-58651c6a6509

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

universe u

/-- The actual tensor restriction retains the post-repair copy count,
with its quantitative lower bound including the integer-rounding loss. -/
theorem solution
    {K : Type u} [Field K] {ell N : ℕ} {P : Predicate N}
    (E : ExactStep ell N P) {B : ℝ} (hB : B ≤ E.count) :
    TensorObj.Restrict
      (TensorObj.bigAdd (fun _ : Fin E.copies => tensor K E.output)) (tensor K P) ∧
      B / (8 : ℝ) ^ E.stage.repairExponent - 1 < E.copies := by
  exact ⟨mme_recursive_profiled_CW_exact_step E,
    mme_exact_step_copies_gt_normalized_count_sub_one E hB⟩


#print axioms solution
