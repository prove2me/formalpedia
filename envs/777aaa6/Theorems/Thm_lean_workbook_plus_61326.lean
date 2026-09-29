-- Prove2me | Theorems.Thm_lean_workbook_plus_61326
-- name    : lean_workbook_plus_61326
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/07c872d9-6b2f-47c8-9a42-d6369c4ae2c9
-- statement:
--   So we need $3a^4-6a^3+8a^2-6a+3 \geq 0$ when $a\geq 0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_61326 (a : ℝ) (ha : 0 ≤ a) : 3 * a ^ 4 - 6 * a ^ 3 + 8 * a ^ 2 - 6 * a + 3 ≥ 0   :=  by sorry
