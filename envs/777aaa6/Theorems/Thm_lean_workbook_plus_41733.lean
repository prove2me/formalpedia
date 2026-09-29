-- Prove2me | Theorems.Thm_lean_workbook_plus_41733
-- name    : lean_workbook_plus_41733
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/5cc38d30-d39e-48db-98bb-1d8ec494d5ee
-- statement:
--   Thus with the assumption $x >0$ we get that $x \le 1$ $\implies$ $\frac{1}{x} \ge 1$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_41733  (x : ℝ)
  (h₀ : 0 < x)
  (h₁ : x ≤ 1) :
  1 / x ≥ 1   :=  by sorry
