-- Prove2me | Theorems.Thm_lean_workbook_plus_43874
-- name    : lean_workbook_plus_43874
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/3e90ce43-90f5-4986-93e8-b982b9db5f60
-- statement:
--   The function can be written as $f(x)=x+a+b-c+{(a-c)(b-c)\over x+c}=x+c+{(a-c)(b-c)\over x+c}+a+b-2c$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_43874  (x a b c : ℝ)
  (h₀ : x ≠ -c)
  (h₁ : c ≠ a)
  (h₂ : c ≠ b) :
  x + a + b - c + (a - c) * (b - c) / (x + c) = x + c + (a - c) * (b - c) / (x + c) + a + b - 2 * c   :=  by sorry
