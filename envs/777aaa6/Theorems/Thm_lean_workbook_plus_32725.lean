-- Prove2me | Theorems.Thm_lean_workbook_plus_32725
-- name    : lean_workbook_plus_32725
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/e22ea0a7-5a05-4d24-9d26-5f1aad131c27
-- statement:
--   Given $P(x)=x^4+ax^3+bx^2+cx+d$ and $P(1)=10, P(2)=20, P(3)=30$, compute $P(10)+P(-6)$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_32725 (a b c d : ℝ) (P : ℝ → ℝ) (hP : P = fun x : ℝ => x^4 + a*x^3 + b*x^2 + c*x + d) : P 1 = 10 ∧ P 2 = 20 ∧ P 3 = 30 → P 10 + P (-6) = 8104   :=  by sorry
