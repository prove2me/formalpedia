-- Prove2me | Theorems.Thm_lean_workbook_plus_40201
-- name    : lean_workbook_plus_40201
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/cdae0ef7-5075-4562-9157-59088c39ba4b
-- statement:
--   Prove that $ \sum^{n}_{r=0}(-1)^{r}r\binom{n}{r}=0 $ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_40201 : ∀ n : ℕ, ∑ r in Finset.range (n+1), (-1 : ℤ)^r * r * Nat.choose n r = 0   :=  by sorry
