-- Prove2me | Theorems.Thm_lean_workbook_plus_19271
-- name    : lean_workbook_plus_19271
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/95c4a2bf-8c7e-4da1-b9f7-1f73bb55795a
-- statement:
--   This is a basic conditional probability problem, so let $A$ be the event that the sum of the two dice is 8 and $B$ the event that at least one die does not show a 5. You are basically looking for $P(A|B)=\frac{P(A\cap B)}{P(B)}$ .\nHere we have $A=\{(2,6),(3,5),(4,4),(5,3)(6,2)\}$ and $B$ has 25 elements (too lazy to list them, but you can get the idea that out of the 36 ordered pairs, take out those with a 5 in it, so there are $5^2=25$ .)\n$A\cap B=\{(2,6),(4,4),(6,2)\}$ , so $P(A\cap B)=\frac{3}{36}$ . Similarly, $P(B)=\frac{25}{36}$ .\nThus, $P(A|B)=\frac{\frac{3}{36}}{\frac{25}{36}}=\frac{3}{25}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_19271 :
  (3 : ℝ) / 25  = (3 / 36) / (25 / 36)   :=  by sorry
