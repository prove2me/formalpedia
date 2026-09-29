-- Prove2me | Theorems.Thm_lean_workbook_plus_15336
-- name    : lean_workbook_plus_15336
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/9bfc124d-9f8f-410a-9354-ee43387764b2
-- statement:
--   prove for any three real numbers a,b,c the inequality \n\n $ 3(a^{2}-a-1)(b^{2}-b-1)(c^{2}-c+1) \ge (abc)^{2}-abc+1 $
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_15336 : ∀ a b c : ℝ, 3 * (a ^ 2 - a - 1) * (b ^ 2 - b - 1) * (c ^ 2 - c + 1) ≥ (abc) ^ 2 - abc + 1   :=  by sorry
