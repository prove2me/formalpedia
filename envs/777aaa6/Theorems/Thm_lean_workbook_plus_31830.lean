-- Prove2me | Theorems.Thm_lean_workbook_plus_31830
-- name    : lean_workbook_plus_31830
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/e23cfee3-fbb1-49be-8753-1fe6901a11a1
-- statement:
--   I think it would be $\dbinom{6+4-1}{4}=126.$ Here is the idea: \n\nLet $f(i)=6+x_1+x_2+\ldots+x_i$ where $x_1,x_2,\ldots,x_i$ are non-negative integers. Then the number of such non-decreasing functions is equal to the number of non-negative integer solutions of $x_1+x_2+x_3+x_4+x_5 \leq 4$ which is equal to the number of non-negative integer solutions of the equation $x_1+x_2+x_3+x_4+x_5+y=4.$ \n\nSo, the answer is $\dbinom{4+6-1}{4}=126.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_31830 Nat.choose (6 + 4 - 1) 4 = 126   :=  by sorry
