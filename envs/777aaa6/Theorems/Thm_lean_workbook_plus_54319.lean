-- Prove2me | Theorems.Thm_lean_workbook_plus_54319
-- name    : lean_workbook_plus_54319
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/a3e3ec6e-b93d-4d7e-918e-ca7e51d00d11
-- statement:
--   Given $(a - b)^2 \geq 0$, prove that $a^2 + b^2 \geq 2ab$ for any real numbers a and b.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_54319 (a b: ℝ) : (a - b) ^ 2 ≥ 0 → a ^ 2 + b ^ 2 ≥ 2 * a * b   :=  by sorry
