-- Prove2me | Theorems.Thm_lean_workbook_plus_64392
-- name    : lean_workbook_plus_64392
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/71fab2f8-2ada-4c33-b0ef-0fca888c8ff8
-- statement:
--   Shouldn't need much time to $ {b\over a} < \mu_s \;\;$. We can use any (inertial) pole (or axis as you say) to calculate the torques . For instance, taking the center ( actually barycenter) we have at the tipping critical angle: $ F_{fr} {a\over 2} = N {b\over 2} \Rightarrow {F_{fr}\over N} = {b\over a} \;$ , where $ F_{fr} $ is the friction force an $ N $ the normal contact force with the incline. For tipping occur before sliding $ F_{fr} < \mu_s N \Rightarrow {{F_{fr}}\over N} < \mu_s \;$ , so...
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_64392 (a b : ℝ) (μ_s : ℝ) (h₀ : 0 < a ∧ 0 < b) (h₁ : 0 < μ_s) (h₂ : b / a < μ_s) : b / a < μ_s   :=  by sorry
