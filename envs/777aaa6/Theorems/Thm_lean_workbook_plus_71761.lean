-- Prove2me | Theorems.Thm_lean_workbook_plus_71761
-- name    : lean_workbook_plus_71761
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/b3c97894-fa07-4479-aeab-2693eef38756
-- statement:
--   We have $ x^{3}e^{x}=\sum_{n=0}^{\infty}\frac1{n!}x^{n+3}$ ; taking two derivatives, $ (6x+6x^{2}+x^{3})e^{x}=\sum_{n=0}^{\infty}\frac{(n+3)(n+2)}{n!}x^{n+1}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_71761 : ∀ x : ℝ, x^3 * exp x = ∑' n : ℕ, x^(n+3) / n! ∧ (6*x + 6*x^2 + x^3) * exp x = ∑' n : ℕ, ((n+3)*(n+2)/n!) * x^(n+1)   :=  by sorry
