-- Prove2me | Theorems.Thm_lean_workbook_plus_5094
-- name    : lean_workbook_plus_5094
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/152881c4-563c-48ff-9b91-4d109095e7c5
-- statement:
--   If $abc=1$, prove that $\frac{1}{(a^2+2*b^2+3)} +\frac{1}{b^2+2*c^2+3} +\frac{1}{c^2+2*a^2+3} \leq \frac{1}{2}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_5094 : a * b * c = 1 → (1 / (a ^ 2 + 2 * b ^ 2 + 3) + 1 / (b ^ 2 + 2 * c ^ 2 + 3) + 1 / (c ^ 2 + 2 * a ^ 2 + 3)) ≤ 1 / 2   :=  by sorry
