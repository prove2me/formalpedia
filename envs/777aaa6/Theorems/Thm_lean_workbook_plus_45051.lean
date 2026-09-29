-- Prove2me | Theorems.Thm_lean_workbook_plus_45051
-- name    : lean_workbook_plus_45051
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/7d819e49-4f84-4d43-b3f9-557521745c80
-- statement:
--   Case 1( $\mathbf{a}$ is even): Thus $x=2b+y$ for some natural number $b$ . Then: $[x]=[2b+y]=2b$ and $\left[ {\frac{x}{2}} \right] = \left[ {\frac{{2b + y}}{2}} \right] = \left[ {b + \frac{y}{2}} \right] = b$ because $y/2$ is less than $1$ . So, $\left[ x \right] - 2\left[ {\frac{x}{2}} \right] = 2b - 2b = 0$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_45051  (x : ℕ)
  (h₀ : Even x) :
  (x : ℤ) - 2 * (x / 2) = 0   :=  by sorry
