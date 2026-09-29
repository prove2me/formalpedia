-- Prove2me | Theorems.Thm_lean_workbook_plus_19855
-- name    : lean_workbook_plus_19855
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/f534bb71-9595-4a7f-a4fe-2e72a3c5ac9e
-- statement:
--   Prove or disprove the inequality: $(ab+bc+ca)(a^4+b^4+c^4 ) \ge 3(a^2 b^4+b^2 c^4+c^2 a^4 )$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_19855 : ∀ a b c : ℝ, (a * b + b * c + c * a) * (a ^ 4 + b ^ 4 + c ^ 4) ≥ 3 * (a ^ 2 * b ^ 4 + b ^ 2 * c ^ 4 + c ^ 2 * a ^ 4)   :=  by sorry
