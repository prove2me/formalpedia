-- Prove2me | Theorems.Thm_WorkbookSource_problem_50698
-- name    : WorkbookSource.problem_50698
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T22:08:58.668241+00:00
-- url     : https://prove2.me/theorems/e6357b19-5d12-4253-8e8a-a1451fb00d45
-- title:
--   A factorial quotient for four steps
-- statement:
--   Number of paths from $(0,0)$ to $(2,2)$ : $4!/(2!*2!)=6$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_50698` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_50698; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_50698 :
  Nat.factorial 4 / (Nat.factorial 2 * Nat.factorial 2) = 6  :=  by sorry
