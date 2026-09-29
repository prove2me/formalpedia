-- Prove2me | Theorems.Thm_lean_workbook_plus_1216
-- name    : lean_workbook_plus_1216
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/2d158193-328f-4a68-9683-3c80c7ba9d20
-- statement:
--   Prove that $ a^2b^2+b^2c^2+c^2a^2 \ge abc(a+b+c) $
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_1216 (a b c: ℝ) : a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * a ^ 2 ≥ a * b * c * (a + b + c)   :=  by sorry
