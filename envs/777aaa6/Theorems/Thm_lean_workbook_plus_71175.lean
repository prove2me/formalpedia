-- Prove2me | Theorems.Thm_lean_workbook_plus_71175
-- name    : lean_workbook_plus_71175
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/77f606b7-fe85-4141-909d-eae0cd8d16bf
-- statement:
--   Note that $2 \cdot 3 \cdot 5 = 30$ and floor of $\frac{1000}{30} = 33$ . So, we want nonnegative integers $a,b,c$ such that $2^a 3^b 5^c < 34$ . We can take $a = 5$ which gives one solution. $a = 4$ gives one solution again. $a = 3$ gives two solutions. $a= 2$ gives $3$ solutions. In addition, $a=1$ gives $1+2+1+1 = 5$ solutions. Finally $a = 0$ gives $4 + 2 + 1 = 7$ solutions. Adding it all up, we have this case gives, $1 + 1+2+3+5+7 = 19$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_71175 :
  ∑ k in Finset.filter (λ x => 30 * x < 1000) (Finset.Icc 1 33), (Nat.div 1000 (30 * k)) = 19   :=  by sorry
