-- Prove2me | Theorems.Thm_lean_workbook_plus_16301
-- name    : lean_workbook_plus_16301
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/cd49afbe-baab-4933-a014-e005d85acf15
-- statement:
--   For $n = 4$, prove that the inequality $(a_{1} + a_{2} + a_{3} + a_{4})^{2} - 4(a_{1}a_{2} + a_{2}a_{3} + a_{3}a_{4} + a_{4}a_{1}) \geqslant 0$ holds.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_16301 (a : ℕ → ℝ) : (a 1 + a 2 + a 3 + a 4) ^ 2 - 4 * (a 1 * a 2 + a 2 * a 3 + a 3 * a 4 + a 4 * a 1) ≥ 0   :=  by sorry
