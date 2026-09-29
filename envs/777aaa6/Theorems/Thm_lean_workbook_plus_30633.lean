-- Prove2me | Theorems.Thm_lean_workbook_plus_30633
-- name    : lean_workbook_plus_30633
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/31e27d40-a33a-430c-89e4-38382ccf04d8
-- statement:
--   Given $a + c = b + d$ and $k^2 = a^2 + b^2 - 2ab \cos{\alpha} = c^2 + d^2 - 2cd \cos{\beta}$, where $k$ is the length of a diagonal and $\alpha, \beta$ are angles. Show that $ab(1 - \cos{\alpha}) = cd(1 - \cos{\beta})$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_30633 (a b c d k : ℝ) (hab : a + c = b + d) (hk : k^2 = a^2 + b^2 - 2 * a * b * Real.cos α) (hk' : k^2 = c^2 + d^2 - 2 * c * d * Real.cos β) : a * b * (1 - Real.cos α) = c * d * (1 - Real.cos β)   :=  by sorry
