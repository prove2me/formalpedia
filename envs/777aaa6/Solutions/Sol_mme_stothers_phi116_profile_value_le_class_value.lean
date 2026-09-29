-- Prove2me | solution 1 for mme_stothers_phi116_profile_value_le_class_value
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-05T07:52:21.956042+00:00
-- url     : https://prove2.me/submissions/78a7377c-0bfc-4efd-9238-a9a6a333a568

import Mathlib.Analysis.MeanInequalities
import Mathlib.Tactic
import Definitions.Def_mme_stothers_fourth_data

open MME
universe u

theorem solution (tau a : Real) (haPos : 0 < a) (haLt : a < 1) :
    4 * (((2 * MME.StothersFourth.L 6 tau) / a) ^ a *
      ((MME.StothersFourth.E 6 tau ^ (2 : ℕ)) / (1 - a)) ^ (1 - a)) ≤
      MME.StothersFourth.classValue 6 tau 5 := by
  have hL : 0 < MME.StothersFourth.L 6 tau := by
    rw [MME.StothersFourth.L]
    positivity
  have hE : 0 < MME.StothersFourth.E 6 tau := by
    rw [MME.StothersFourth.E]
    positivity
  have hA : 0 < 2 * MME.StothersFourth.L 6 tau := by positivity
  have hB : 0 < MME.StothersFourth.E 6 tau ^ (2 : ℕ) := by positivity
  have ha0 : 0 ≤ a := haPos.le
  have hb0 : 0 ≤ 1 - a := by linarith
  have hamgm := Real.geom_mean_le_arith_mean2_weighted ha0 hb0
    (div_nonneg hA.le ha0) (div_nonneg hB.le hb0) (by ring)
  have ha_ne : a ≠ 0 := ne_of_gt haPos
  have hb_ne : 1 - a ≠ 0 := ne_of_gt (sub_pos.mpr haLt)
  have hsum : a * ((2 * MME.StothersFourth.L 6 tau) / a) +
      (1 - a) * ((MME.StothersFourth.E 6 tau ^ (2 : ℕ)) / (1 - a)) =
      2 * MME.StothersFourth.L 6 tau + MME.StothersFourth.E 6 tau ^ (2 : ℕ) := by
    field_simp
  rw [hsum] at hamgm
  simpa [MME.StothersFourth.classValue, add_comm] using
    (mul_le_mul_of_nonneg_left hamgm (by norm_num : (0 : ℝ) ≤ 4))
