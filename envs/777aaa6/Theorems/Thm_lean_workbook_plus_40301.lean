-- Prove2me | Theorems.Thm_lean_workbook_plus_40301
-- name    : lean_workbook_plus_40301
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/8b72c5eb-cdfc-4a79-b7a8-c65ad31a8b5e
-- statement:
--   The function is defined like $f(0)=10$ and $f(x)=e^{x^2}$ for $x\neq 0$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_40301 (f : ℝ → ℝ) (hf: f 0 = 10 ∧ ∀ x, x ≠ 0 → f x = Real.exp (x^2)) : f x = if x = 0 then 10 else Real.exp (x^2)   :=  by sorry
