-- Prove2me | Theorems.Thm_lean_workbook_plus_27803
-- name    : lean_workbook_plus_27803
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/8ca65930-f743-46b9-b340-85eede47860d
-- statement:
--   Show that $2\cdot (\sum a^2)^2\geq 3\cdot \sum (a^3b+ab^3)$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_27803 (a b c : ℝ) :
  2 * (a^2 + b^2 + c^2)^2 ≥ 3 * (a^3 * b + b^3 * c + c^3 * a + a * b^3 + b * c^3 + c * a^3)   :=  by sorry
