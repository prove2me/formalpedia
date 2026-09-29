-- Prove2me | Theorems.Thm_lean_workbook_plus_5040
-- name    : lean_workbook_plus_5040
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/f051ac67-a94c-4040-ab79-32b162158e75
-- statement:
--   Let $a = 1 + x,\ b = 1 - x$ where $x \geq 0$ . The problem becomes: $14 + \sqrt{2 - x^2} \geq |x^4-9x^2|$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_5040 : ∀ x ≥ 0, 14 + Real.sqrt (2 - x ^ 2) ≥ |x ^ 4 - 9 * x ^ 2|   :=  by sorry
