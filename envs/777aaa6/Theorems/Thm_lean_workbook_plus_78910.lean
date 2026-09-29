-- Prove2me | Theorems.Thm_lean_workbook_plus_78910
-- name    : lean_workbook_plus_78910
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/bf6b27ea-7b4c-4680-b1c9-820830389a88
-- statement:
--   Prove that, for all natural numbers $ n$ , $ \displaystyle\sum_{x=1}^{n}x=\frac{n{(}n+1{)}}{2}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_78910 : 
  ∀ n : ℕ, (∑ x in Finset.range (n + 1), x = n * (n + 1) / 2)   :=  by sorry
