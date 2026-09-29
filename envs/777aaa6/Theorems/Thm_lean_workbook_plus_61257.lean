-- Prove2me | Theorems.Thm_lean_workbook_plus_61257
-- name    : lean_workbook_plus_61257
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/6459f978-83c5-49c3-ae1c-96c35e08025f
-- statement:
--   Prove that $ 9(a^6 + b^6 + c^6) + 6a^2b^2c^2 \geq 7(a^3b^3 + b^3c^3 + c^3a^3) + 4abc(a^3 + b^3 + c^3)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_61257 (a b c : ℝ) : 9 * (a ^ 6 + b ^ 6 + c ^ 6) + 6 * a ^ 2 * b ^ 2 * c ^ 2 ≥ 7 * (a ^ 3 * b ^ 3 + b ^ 3 * c ^ 3 + c ^ 3 * a ^ 3) + 4 * a * b * c * (a ^ 3 + b ^ 3 + c ^ 3)   :=  by sorry
