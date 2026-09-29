-- Prove2me | Theorems.Thm_lean_workbook_plus_47300
-- name    : lean_workbook_plus_47300
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/05012d46-35c7-47c5-8e01-6a49c02ad9b3
-- statement:
--   Suppose we place $k$ green flags and $r$ blue flags on one of the posts. It is well-known that there are ${r+1 \choose k}$ ways to arrange the flags such that no two green flags are consecutive. So the answer is $$\sum_{r=0}^{10} \sum_{k=0}^9 {r+1 \choose k}{11-r \choose 9-k} - 2{11 \choose 9}$$ when we subtract the two cases where one flagpole is empty. By Vandermonde's, this is $$\sum_{r=0}^{10} {12 \choose 9} - 2{11 \choose 9} = 220 \cdot 11 - 110 = 2\boxed{310}$$ arrangements.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_47300 :
  ∑ r in Finset.range 11, ∑ k in Finset.range 10, (Nat.choose (r + 1) k * Nat.choose (11 - r) (9 - k)) - 2 * Nat.choose 11 9 = 310   :=  by sorry
