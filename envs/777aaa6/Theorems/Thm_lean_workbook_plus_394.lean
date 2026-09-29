-- Prove2me | Theorems.Thm_lean_workbook_plus_394
-- name    : lean_workbook_plus_394
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/352f3463-f6e6-4991-b62c-f430e8597cd2
-- statement:
--   Prove that\n$4\sum_{cyc}a b^2 c^3 + 2\sum_{cyc}b c^5 + 2\sum_{cyc}a^2 c^4\geq 6a^2 b^2 c^2 + 3\sum_{cyc}a b c^4+ 3\sum_{cyc}a^3 b^3$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_394 : ∀ a b c : ℝ, 4 * (a * b^2 * c^3 + b * c^2 * a^3 + c * a^2 * b^3) + 2 * (b * c^5 + c * a^5 + a * b^5) + 2 * (a^2 * c^4 + b^2 * a^4 + c^2 * b^4) ≥ 6 * a^2 * b^2 * c^2 + 3 * (a * b * c^4 + b * c * a^4 + c * a * b^4) + 3 * (a^3 * b^3 + b^3 * c^3 + c^3 * a^3)   :=  by sorry
