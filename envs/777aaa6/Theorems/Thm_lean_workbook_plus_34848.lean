-- Prove2me | Theorems.Thm_lean_workbook_plus_34848
-- name    : lean_workbook_plus_34848
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/1d8869d4-80ac-4e68-be4f-fbaa1eb4e980
-- statement:
--   Prove that $\dfrac12 y^6 + \dfrac12 x^4y^4 \ge x^2y^5$ for positive $x, y$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_34848 (x y : ℝ) (hx : 0 < x) (hy : 0 < y) : (1 / 2) * y ^ 6 + (1 / 2) * x ^ 4 * y ^ 4 ≥ x ^ 2 * y ^ 5   :=  by sorry
