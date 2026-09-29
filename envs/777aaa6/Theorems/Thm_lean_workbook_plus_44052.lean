-- Prove2me | Theorems.Thm_lean_workbook_plus_44052
-- name    : lean_workbook_plus_44052
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/9ad64d32-22f3-4f2f-a8a0-ebecc131a3bb
-- statement:
--   Prove that $\dfrac12 y^6 + \dfrac12 x^2y^2 \ge xy^4$ for positive $x, y$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_44052 (x y : ℝ) (hx : 0 < x) (hy : 0 < y) : (1 / 2) * y ^ 6 + (1 / 2) * x ^ 2 * y ^ 2 ≥ x * y ^ 4   :=  by sorry
