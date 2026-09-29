-- Prove2me | Theorems.Thm_WorkbookSource_problem_35638
-- name    : WorkbookSource.problem_35638
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T12:41:07.437713+00:00
-- url     : https://prove2.me/theorems/f5fb4a73-5b4c-444c-9624-9a34c957ad28
-- title:
--   A strict quadratic bound from a sum of squares
-- statement:
--   Let $ a,b,c \in R^+$ be such that $ (a+b)^2+(b+c)^2+(c+a)^2=3$ . prove that $ 2bc+3(b^2+c^2) <6$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_35638` (Apache-2.0). The complete source proposition and its explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_35638; Apache-2.0

import Mathlib
open Real

theorem WorkbookSource.problem_35638 (a b c: ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c): (a+b)^2+(b+c)^2+(c+a)^2=3 → 2*b*c+3*(b^2+c^2)<6  :=  by sorry
