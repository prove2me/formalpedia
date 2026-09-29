-- Prove2me | Theorems.Thm_WorkbookSource_problem_28151
-- name    : WorkbookSource.problem_28151
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T22:01:36.143009+00:00
-- url     : https://prove2.me/theorems/d1a25668-c28c-43f5-b8fb-a19a43973eeb
-- title:
--   Comparing powers of four and three
-- statement:
--   Which is larger? $ x = 4^{321}$ or $ y = 3^{421}$.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_28151` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_28151; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_28151 : (4:ℝ)^(321) < 3^(421)  :=  by sorry
