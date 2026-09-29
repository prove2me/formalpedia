-- Prove2me | Theorems.Thm_lean_workbook_plus_43355
-- name    : lean_workbook_plus_43355
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/77913197-6fd5-4367-af9a-0ce4486679d4
-- statement:
--   Prove that: $\sum_{i = 0}^n \binom{n}{i}\cdot i \cdot (1 - p)^{i} p^{n - i} = np$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_43355 : ∀ n : ℕ, ∀ p : ℝ, (∑ i in Finset.range (n + 1), (n.choose i) * i * (1 - p)^i * p^(n - i)) = n * p   :=  by sorry
