-- Prove2me | Theorems.Thm_lean_workbook_plus_40309
-- name    : lean_workbook_plus_40309
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/54c9c319-9061-4527-a4d5-58a1e00a9387
-- statement:
--   Given that $ a_{0} = 1, a_{1} = 1$ and $ n(n - 1)a_{n} = (n - 1)(n - 2)a_{n - 1}-(n - 3)a_{n-2}$ find $ \sum_{n = 0}^{\infty}{a_{n}}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_40309 (a : ℕ → ℝ) (h : a 0 = 1 ∧ a 1 = 1 ∧ ∀ n, n * (n - 1) * a n = (n - 1) * (n - 2) * a (n - 1) - (n - 3) * a (n - 2)) : ∑' n : ℕ, a n = Real.exp 1   :=  by sorry
