-- Prove2me | Theorems.Thm_lean_workbook_plus_54218
-- name    : lean_workbook_plus_54218
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/d3f381ad-5ea1-41ab-b27c-0d7d9a18b2ab
-- statement:
--   Prove that $\sum_{i=0}^n \left( (3 i+1)^2+(3 i+2)^2\right) = (n+1) (6 n^2+12 n+5 )$ and $\sum_{i=1}^{n} (3i)^2 = \frac 32 n (n+1) (2 n+1)$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_54218 : ∀ n : ℕ, ∑ i in Finset.range (n+1), ((3 * i + 1)^2 + (3 * i + 2)^2) = (n + 1) * (6 * n ^ 2 + 12 * n + 5) ∧ ∑ i in Finset.range (n+1), (3 * i) ^ 2 = 3 / 2 * n * (n + 1) * (2 * n + 1)   :=  by sorry
