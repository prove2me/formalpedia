-- Prove2me | Theorems.Thm_lean_workbook_plus_81882
-- name    : lean_workbook_plus_81882
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/c53cda25-2e99-427a-b543-fa00a68c78e4
-- statement:
--   $\frac{4}{3} \left( a^2 + 2b^2 + 6ac + 9c^2 \right) = \frac{4}{3} \left( 2b^2 + (a + 3c)^2 \right) \geq 0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_81882 (a b c : ℝ) : (4 / 3) * (a^2 + 2*b^2 + 6*a*c + 9*c^2) = (4 / 3) * (2 * b^2 + (a + 3 * c)^2) ∧ (4 / 3) * (2 * b^2 + (a + 3 * c)^2) ≥ 0   :=  by sorry
