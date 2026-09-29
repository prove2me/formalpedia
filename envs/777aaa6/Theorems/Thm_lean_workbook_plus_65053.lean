-- Prove2me | Theorems.Thm_lean_workbook_plus_65053
-- name    : lean_workbook_plus_65053
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/c3453335-c4ec-457f-b4d3-59302966e639
-- statement:
--   Prove that $a^4 + b^4 + c^4 \ge (a^3b + b^3a) + ( c^3a + a^3c) + (bc^3 + cb^3) \ge 2(a^2b^2 + b^2c^2 + c^2a^2)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_65053 : ∀ a b c : ℝ, a ^ 4 + b ^ 4 + c ^ 4 ≥ (a ^ 3 * b + b ^ 3 * a) + (c ^ 3 * a + a ^ 3 * c) + (b * c ^ 3 + c * b ^ 3) ∧ (a ^ 3 * b + b ^ 3 * a) + (c ^ 3 * a + a ^ 3 * c) + (b * c ^ 3 + c * b ^ 3) ≥ 2 * (a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * a ^ 2)   :=  by sorry
