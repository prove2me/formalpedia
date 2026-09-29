-- Prove2me | Theorems.Thm_lean_workbook_plus_51768
-- name    : lean_workbook_plus_51768
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/3f93ecdc-0460-498a-b9ce-cdc493982a5a
-- statement:
--   Prove that $\frac{1}{a-1}-\frac{1}{a+n}+\frac{1}{{{(a+n+1)}^{2}}}\le \frac{1}{a-1}-\frac{1}{a+n+1}\Leftrightarrow (a+n+2)(a+n)\le {{(a+n+1)}^{2}}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_51768  (a n : ℝ)
  (h₀ : 1 < a)
  (h₁ : 0 < n) :
  1 / (a - 1) - 1 / (a + n) + 1 / (a + n + 1)^2 ≤ 1 / (a - 1) - 1 / (a + n + 1) ↔ (a + n + 2) * (a + n) ≤ (a + n + 1)^2   :=  by sorry
