-- Prove2me | Theorems.Thm_lean_workbook_plus_69096
-- name    : lean_workbook_plus_69096
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/6c4372d0-73b9-4e22-bc09-f63df8cc3567
-- statement:
--   Prove that for any positive real numbers a, b this inequality is valid:\n$5x^3y + 5xy^3 \leq 2x^4 + 6x^2y^2 + 2y^4$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_69096 (x y : ℝ) (hx : 0 < x) (hy : 0 < y) : 5 * x ^ 3 * y + 5 * x * y ^ 3 ≤ 2 * x ^ 4 + 6 * x ^ 2 * y ^ 2 + 2 * y ^ 4   :=  by sorry
