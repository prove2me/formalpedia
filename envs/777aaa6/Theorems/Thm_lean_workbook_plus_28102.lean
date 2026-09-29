-- Prove2me | Theorems.Thm_lean_workbook_plus_28102
-- name    : lean_workbook_plus_28102
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/e6d1b670-af94-488a-9b55-482be9af0b47
-- statement:
--   A basic cellular phone plan costs $ 20 per month for 60 calling minutes. Additional time costs $ 0.40 per minute. The formula C = 20 + 0.40(x − 60) gives the monthly cost for this plan, C, for x calling minutes, where x > 60. How many calling minutes are possible for a monthly cost of at least $ 28 and at most $ 40?
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_28102 (x : ℝ) (h₁ : 20 + 0.4 * (x - 60) ≥ 28) (h₂ : 20 + 0.4 * (x - 60) ≤ 40) : 80 ≤ x ∧ x ≤ 110   :=  by sorry
