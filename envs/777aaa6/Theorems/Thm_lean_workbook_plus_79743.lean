-- Prove2me | Theorems.Thm_lean_workbook_plus_79743
-- name    : lean_workbook_plus_79743
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/76f8518e-a0f7-4dca-946d-91e99cbdb3fb
-- statement:
--   We can consider each element separately. \nWe first realize that any element must appear in at least 1 set, but cannot appear in all three sets. \n\nFor any element $i,$ we can place it in 6 ways: $A_1 ; A_2; A_3 ; A_1A_2; A_1A_3$ and $A_2A_3$ \n\nThere are 10 elements in $\{1,2 \cdots , 10\},$ and each element can be chosen independently from the others, so our answer is $6^{10}=2^{10}3^{10}.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_79743 6^10 = 2^10*3^10   :=  by sorry
