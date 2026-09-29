-- Prove2me | Theorems.Thm_lean_workbook_plus_15582
-- name    : lean_workbook_plus_15582
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/e0e9d0e5-192d-45f8-a5ab-57295fcf4121
-- statement:
--   Show that $\sum\limits_{k=1}^{n} \ln \left(1 + \frac{1}{k} \right) = \ln n$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_15582 : ∀ n : ℕ, ∑ k in Finset.Icc 1 n, Real.log (1 + 1 / k) = Real.log n   :=  by sorry
