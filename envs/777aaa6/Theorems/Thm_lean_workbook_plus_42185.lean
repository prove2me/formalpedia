-- Prove2me | Theorems.Thm_lean_workbook_plus_42185
-- name    : lean_workbook_plus_42185
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/815a8f2e-92cb-4ae1-9bad-2c0efb2d6e48
-- statement:
--   $2(a^4+b^4) \geq 2(ab^3+ba^3)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_42185 (a b : ℝ) : 2 * (a^4 + b^4) ≥ 2 * (a * b^3 + b * a^3)   :=  by sorry
