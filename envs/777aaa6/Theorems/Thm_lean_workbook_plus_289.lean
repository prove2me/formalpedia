-- Prove2me | Theorems.Thm_lean_workbook_plus_289
-- name    : lean_workbook_plus_289
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/671b60bd-85aa-44ea-a6e4-69cfae54202d
-- statement:
--   Inequality follows from these three am-gm inequalities. \n $ a^4b^2+b^4c^2 \geq 2b^3a^2c$ \n $ a^4b^2+c^4a^2\geq 2a^3c^2b$ \n $ b^4c^2+c^4a^2\geq 2c^3b^2a$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_289 (a b c : ℝ) :
  a^4 * b^2 + b^4 * c^2 ≥ 2 * b^3 * a^2 * c ∧
  a^4 * b^2 + c^4 * a^2 ≥ 2 * a^3 * c^2 * b ∧
  b^4 * c^2 + c^4 * a^2 ≥ 2 * c^3 * b^2 * a   :=  by sorry
