-- Prove2me | Theorems.Thm_lean_workbook_plus_75557
-- name    : lean_workbook_plus_75557
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/cf63f91e-d215-4fb6-8854-b8ef0c919f11
-- statement:
--   Even if you didn't know that $6$ is a perfect number, you could easily find that the divisors of $6$ excluding itself are $1,2,3$ and the sum is $1+2+3=\boxed{6}.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_75557 :
  ∑ k in (Nat.properDivisors 6), k = 6   :=  by sorry
