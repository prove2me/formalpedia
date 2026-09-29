-- Prove2me | Theorems.Thm_lean_workbook_plus_9733
-- name    : lean_workbook_plus_9733
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/d2c05974-efcf-44f7-9ad9-3fba7c79b48a
-- statement:
--   I claim that $ x^4 + y^4 + z^4 + 2x^2y^2 + 2y^2z^2 + 2z^2x^2 \ge 3xyz(x + y + z)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_9733 (x y z : ℝ) : (x^4 + y^4 + z^4 + 2 * x^2 * y^2 + 2 * y^2 * z^2 + 2 * z^2 * x^2) ≥ 3 * x * y * z * (x + y + z)   :=  by sorry
