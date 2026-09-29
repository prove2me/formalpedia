-- Prove2me | Theorems.Thm_lean_workbook_plus_1021
-- name    : lean_workbook_plus_1021
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/70eb6ed8-cd23-492f-a702-c25baaed3e03
-- statement:
--   Notice that we can do casework on all equations from $x+y+z=0, x+y+z=1,..., x+y+z=23$ . By stars and bars, the number of solutions to each equation is $\binom{2}{2}, \binom{3}{2}, \binom{4}{2},\cdots,\binom{25}{2}$ , respectively. Adding up all these cases and using the hockey stick identity, we get a final answer of $\binom{2}{2}+\binom{3}{2}+\binom{4}{2}+\cdots+\binom{25}{2}=\binom{26}{3}=\boxed{2600}$ solutions.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_1021 ∑ k in Finset.Icc 0 23, (k+2).choose 2 = (26).choose 3   :=  by sorry
