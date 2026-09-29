-- Prove2me | Theorems.Thm_lean_workbook_plus_72972
-- name    : lean_workbook_plus_72972
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/3e963f5d-fc2c-4775-bebc-d8b1c0eec677
-- statement:
--   There is a bijection of such numbers $n$ into numbers whose writing base $3$ contains at most $6$ digits. Just write $2$ instead of $9$ and this is the writing in base $3$ . So the answer is just the number of multiples of $7$ between $1$ and $3^6-1$ . By FLT, $3^6-1$ is divisible by $7$ so the answer is $\frac{3^6-1}{7}=104$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_72972 :
  Finset.card (Finset.filter (λ n => 7∣n) (Finset.Icc 1 (3^6 - 1))) = 104   :=  by sorry
