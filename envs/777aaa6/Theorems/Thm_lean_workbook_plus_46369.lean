-- Prove2me | Theorems.Thm_lean_workbook_plus_46369
-- name    : lean_workbook_plus_46369
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/9c12acaf-f010-4cf5-b2ae-86d0c409e7d7
-- statement:
--   Prove that $1+3+6+\ldots+n(n+1)/2=n(n+1)(n+3)/6$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_46369 : ∀ n, ∑ i in Finset.range (n + 1), i * (i + 1) / 2 = n * (n + 1) * (n + 3) / 6   :=  by sorry
