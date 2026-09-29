-- Prove2me | Theorems.Thm_lean_workbook_plus_18472
-- name    : lean_workbook_plus_18472
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/740931a2-37af-4d55-b05e-948e4e3b775c
-- statement:
--   So $(l_a l_b+l_b l_c+l_c l_a )^2 \leq 3 (l_a^2 l_b^2+l_b^2 l_c^2+l_c^2 l_a^2) $
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_18472 (l_a l_b l_c : ℝ) : (l_a * l_b + l_b * l_c + l_c * l_a) ^ 2 ≤ 3 * (l_a ^ 2 * l_b ^ 2 + l_b ^ 2 * l_c ^ 2 + l_c ^ 2 * l_a ^ 2)   :=  by sorry
