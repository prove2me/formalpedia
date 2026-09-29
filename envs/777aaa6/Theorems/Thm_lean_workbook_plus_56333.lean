-- Prove2me | Theorems.Thm_lean_workbook_plus_56333
-- name    : lean_workbook_plus_56333
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/7d68cdcb-777c-479a-936f-b5f66715cd6c
-- statement:
--   Prove that $42-92a+26a^2+54a^3-27a^4\geq0$ for $0\leq a\leq\frac{4}{3}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_56333 ∀ a : ℝ, 0<=a ∧ a<=4/3 → 42-92*a+26*a^2+54*a^3-27*a^4 >=0   :=  by sorry
