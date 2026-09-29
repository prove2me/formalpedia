-- Prove2me | Theorems.Thm_lean_workbook_plus_60818
-- name    : lean_workbook_plus_60818
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/e65deb6a-a624-4a46-b0ce-56f7ba5bfcf9
-- statement:
--   Explanation for the correct solution: First, choose 4 spots for the freshmen out of 10, then 3 spots for the sophomores out of the remaining 6, then 2 spots for the juniors, and finally 1 spot for the senior. This gives $\binom{10}{4}\cdot\binom{6}{3}\cdot\binom{3}{2}\cdot\binom{1}{1}=12600$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_60818 :
  10! / (4! * 6!) * (6! / (3! * 3!)) * (3! / (2! * 1!)) * (1! / (1! * 0!)) = 12600   :=  by sorry
