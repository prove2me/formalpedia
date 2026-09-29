-- Prove2me | Theorems.Thm_lean_workbook_plus_53978
-- name    : lean_workbook_plus_53978
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/52e1f164-33ec-4b50-9863-7d770d153c69
-- statement:
--   Find all minimum possible value \n $\lvert\;a-1 \rvert+\lvert\;b-2\rvert + \lvert\;c-3\rvert + \lvert3a+2b+c\rvert$ where $a,b,c \in R$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_53978 (a b c: ℝ) : 10 / 3 ≤ |a - 1| + |b - 2| + |c - 3| + |3 * a + 2 * b + c|   :=  by sorry
