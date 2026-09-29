-- Prove2me | Theorems.Thm_lean_workbook_plus_58052
-- name    : lean_workbook_plus_58052
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/3ecafe89-91c2-4ac0-9612-87af26708714
-- statement:
--   The total number of ways to arrange the people is $8!$ . Let's count the number of arrangements in which at least one of the restricted people stands at an end using PIE. Call the restricted people $A$ and $B$ . If one of $A$ or $B$ is standing at at end, then we can arrange the rest of the people in $7!$ ways, with $4$ choices for $A$ and $B$ ( $2$ ends for each person). This is an initial count of $4\times7!$ , but we must subtract off the arrangements in which both $A$ and $B$ are standing at an end. There are $2$ ways to arrange $A$ and $B$ and $6!$ ways to arrange the rest of the people for a total of $2\times6!$ arrangements. Hence, the desired quantity is $$8!-(4\times7!-2\times6!)=6!(56-(28-2))$$ $$=6!\times30=\boxed{21600}.$$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_58052 8! - (4*7! - 2*6!) = 21600   :=  by sorry
