-- Prove2me | Theorems.Thm_lean_workbook_plus_57716
-- name    : lean_workbook_plus_57716
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/92f4121c-9ff1-49e4-85a7-e4c8a8029984
-- statement:
--   To be divisible by $1000$ , there must be at least $3$ factors of $2$ and $3$ factors of $5$ . It is quite obvious that there will always be more factors of 2 than 5, so it suffices to find the least positive integer $n$ such that n! has 3 factors of 5. Since one factor of 5 is added at 5!, 10!, and 15!, the least positive integer $n$ such that n! is divisible by 1000 is 15.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_57716 :
  IsLeast {n : ℕ | 1000∣(n!)} 15   :=  by sorry
