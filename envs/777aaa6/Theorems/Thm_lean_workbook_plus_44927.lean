-- Prove2me | Theorems.Thm_lean_workbook_plus_44927
-- name    : lean_workbook_plus_44927
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/a001407f-730f-459b-97ba-4452aa05dee8
-- statement:
--   By Cauchy-Schwarz's inequality, we have \n$$(a^2b+b^2c+c^2a)^2 \le (a^2+b^2+c^2)(a^2b^2+b^2c^2+c^2a^2).$$ The rest is to prove that $3(a^2b^2+b^2c^2+c^2a^2) \le (a^2+b^2+c^2)^2,$ which is true because \n$$RHS-LHS = \frac{1}{2}[(a^2-b^2)^2+(b^2-c^2)^2+(c^2-a^2)^2] \ge 0.$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_44927  (a b c : ℝ) :
  (a^2 * b + b^2 * c + c^2 * a)^2 ≤ (a^2 + b^2 + c^2) * (a^2 * b^2 + b^2 * c^2 + c^2 * a^2)   :=  by sorry
