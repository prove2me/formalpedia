-- Prove2me | Theorems.Thm_lean_workbook_plus_63699
-- name    : lean_workbook_plus_63699
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/52005f7e-8f69-41ca-b827-dc2328223189
-- statement:
--   Given a polynomial equation $ a_n\cdot x^{n}+...+a_1\cdot x+a_0=0$, how do you solve it for real numbers?
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_63699 (n : ℕ) (a : ℕ → ℝ) (x : ℝ) : ∑ i in Finset.range (n+1), a i * x ^ i = 0 ↔ ∃ k, x = k ∧ ∑ i in Finset.range (n+1), a i * k ^ i = 0   :=  by sorry
