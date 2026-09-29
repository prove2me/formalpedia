-- Prove2me | Theorems.Thm_lean_workbook_plus_66049
-- name    : lean_workbook_plus_66049
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/cf5ba1d0-7936-4c73-8ccb-db1f9c839ed6
-- statement:
--   Clearly, the LHS is equal to $\frac{n+2}{2} \left( \binom{2n}{0}+\binom{2n}{2}+\binom{2n}{4}+\dotsc+\binom{2n}{2n} \right)=(n+2)2^{2n-2}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_66049 : ∀ n : ℕ, ∑ i in Finset.range (n+1), (Nat.choose (2 * n) (2 * i)) = 2^(2 * n - 2) * (n + 2)   :=  by sorry
