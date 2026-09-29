-- Prove2me | Theorems.Thm_lean_workbook_plus_22401
-- name    : lean_workbook_plus_22401
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/68a7d9fc-2b15-4074-97ab-88dde30d73b2
-- statement:
--   Prove that $ \frac{2}{x} < 1 + \frac{1}{x^2}$ for $ x > 1$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_22401 (x : ℝ) (hx : 1 < x) : 2 / x < 1 + 1 / x ^ 2   :=  by sorry
