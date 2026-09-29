-- Prove2me | Theorems.Thm_lean_workbook_plus_63572
-- name    : lean_workbook_plus_63572
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/4d239f92-60c0-43d6-b8c1-7442ac4956b8
-- statement:
--   $$x^4+y^4+z^4\geq x^2y^2+y^2z^2+x^2z^2$$ by AM-GM with $\frac{x^4+y^4}{2}\geq x^2y^2$ and summing cyclically,
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_63572 (x y z : ℝ) : x ^ 4 + y ^ 4 + z ^ 4 ≥ x ^ 2 * y ^ 2 + y ^ 2 * z ^ 2 + x ^ 2 * z ^ 2   :=  by sorry
