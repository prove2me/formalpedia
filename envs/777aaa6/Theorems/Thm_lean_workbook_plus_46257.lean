-- Prove2me | Theorems.Thm_lean_workbook_plus_46257
-- name    : lean_workbook_plus_46257
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/863f82b2-4632-46f5-ab21-959955b7991c
-- statement:
--   Check $a^2b + b^2c + c^2a \ge \frac{1}{3}(a + b + c) (ab + bc + ca)$ for $a = 3/4, b = 2, c = 1/4$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_46257 : (3 / 4 : ℝ) ^ 2 * 2 + 2 ^ 2 * (1 / 4) + (1 / 4) ^ 2 * (3 / 4) ≥ 1 / 3 * (3 / 4 + 2 + 1 / 4) * (3 / 4 * 2 + 2 * 1 / 4 + 1 / 4 * 3 / 4)   :=  by sorry
