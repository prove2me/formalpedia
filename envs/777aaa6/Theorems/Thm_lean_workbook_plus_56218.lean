-- Prove2me | Theorems.Thm_lean_workbook_plus_56218
-- name    : lean_workbook_plus_56218
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/38b6bf3c-3432-46ee-8de4-37d7b1e74d63
-- statement:
--   Prove that for $ a,b,c > 0$,\n\n $ 2a^2c + 2b^2a + a^2b + 2bc^2 + c^2a + b^2c - 9abc\geq 0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_56218 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : 2 * a^2 * c + 2 * b^2 * a + a^2 * b + 2 * b * c^2 + c^2 * a + b^2 * c - 9 * a * b * c ≥ 0   :=  by sorry
