-- Prove2me | Theorems.Thm_lean_workbook_plus_41134
-- name    : lean_workbook_plus_41134
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/037404d8-b847-4f1a-a4fd-f48399a549c1
-- statement:
--   Let us call the house point $H$ , the construction site point $C$ , and the school point $S$ . The total number of ways from $H$ to $S$ is $\binom{11}{5}=462$ . However we need to subtract the ways to go to $C$ , which is $\binom{5}{3}=10$ , therefore the answer I am getting is $\boxed{452}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_41134 (Nat.choose 11 5) - (Nat.choose 5 3) = 452   :=  by sorry
