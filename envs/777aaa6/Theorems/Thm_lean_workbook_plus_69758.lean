-- Prove2me | Theorems.Thm_lean_workbook_plus_69758
-- name    : lean_workbook_plus_69758
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/e0394a73-b19f-41d0-ab28-d3e5d32b15c9
-- statement:
--   This is easy.Rewrite the ineq as\n\n $\frac{a(c+1)+b(a+1)+c(b+1)}{(a+1)(b+1)(c+1)}\ge \frac{3}{4}$\n\n $\Leftrightarrow 1-\frac{1+abc}{(a+1)(b+1)(c+1)}\ge \frac{3}{4}$\n\n $\Leftrightarrow (a+1)(b+1)(c+1)\ge 8$ now this follows from multiplying the inequalities $a+1\ge 2\sqrt{a},b+1\ge 2\sqrt{b},c+1\ge 2\sqrt{c}$ and $abc=1$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_69758  (a b c : ℝ)
  (h₀ : 0 < a ∧ 0 < b ∧ 0 < c)
  (h₁ : a * b * c = 1) :
  (a + 1) * (b + 1) * (c + 1) ≥ 8   :=  by sorry
