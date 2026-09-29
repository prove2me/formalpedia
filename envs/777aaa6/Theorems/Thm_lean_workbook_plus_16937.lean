-- Prove2me | Theorems.Thm_lean_workbook_plus_16937
-- name    : lean_workbook_plus_16937
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/712824a0-a743-4929-9250-e1abe82a7dfd
-- statement:
--   Let $f(x) = 2x(1-x)^2$ , then the max occurs when $f'(x) = 6x^2 - 8x + 2 = 0$ , which has roots $x = \frac{1}{3}$ and $x=1$ . Hence, \n\n $f(x) \leq f(\frac{1}{3}) = 2(\frac{1}{3})(\frac{2}{3})^2 = \frac{8}{27}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_16937 :
  IsGreatest {y : ℝ | ∃ x, 0 ≤ x ∧ x ≤ 1 ∧ y = 2 * x * (1 - x)^2} (8 / 27)   :=  by sorry
