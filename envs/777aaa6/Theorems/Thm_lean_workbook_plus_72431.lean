-- Prove2me | Theorems.Thm_lean_workbook_plus_72431
-- name    : lean_workbook_plus_72431
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/df49672c-3e55-4bb7-a633-c78d1f34deb9
-- statement:
--   Use the Euler-Maclaurin summation formula to prove that $\sum_{k=0}^{n}k^2 = \frac{n(n+1)(2n+1)}{6}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_72431 : ∀ n, ∑ k in Finset.range (n + 1), k ^ 2 = n * (n + 1) * (2 * n + 1) / 6   :=  by sorry
