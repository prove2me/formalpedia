-- Prove2me | Theorems.Thm_WorkbookSource_problem_31990
-- name    : WorkbookSource.problem_31990
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T21:59:00.855812+00:00
-- url     : https://prove2.me/theorems/cc81d5ee-e8e9-4d86-a9be-f6db84270a50
-- title:
--   Comparing adjacent-base large powers
-- statement:
--   Which is larger? $ 100^{101}$ or $ 101^{100}$ ?
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_31990` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_31990; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_31990 : (100:ℝ)^101 > 101^100  :=  by sorry
