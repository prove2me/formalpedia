-- Prove2me | Theorems.Thm_lean_workbook_plus_2893
-- name    : lean_workbook_plus_2893
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/09212b4c-1f60-403d-b88f-beffbfb497e7
-- statement:
--   Let $x\in[0,1)$ : $\sum_{n=0}^{+\infty}x^n=\frac 1{1-x}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_2893 (x : ℝ) (hx : 0 ≤ x ∧ x < 1) :
  ∑' n : ℕ, x ^ n = 1 / (1 - x)   :=  by sorry
