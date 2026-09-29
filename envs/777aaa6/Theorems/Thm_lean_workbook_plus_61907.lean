-- Prove2me | Theorems.Thm_lean_workbook_plus_61907
-- name    : lean_workbook_plus_61907
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/3d47f995-8fc0-4440-8906-431732455715
-- statement:
--   Prove the inequalities $ 0<n\left( \sqrt[n]{2} -1 \right) -\left( \frac{1}{n+1} +\frac{1}{n+2} +\cdots +\frac{1}{n+n}\right) <\frac{1}{2n} , $ where $ n\ge 2. $
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_61907 : ∀ n : ℕ, 2 ≤ n → 0 < n * (2^(1 / n) - 1) - (∑ i in Finset.Icc 1 n, 1 / (n + i)) ∧ n * (2^(1 / n) - 1) - (∑ i in Finset.Icc 1 n, 1 / (n + i)) < 1 / (2 * n)   :=  by sorry
