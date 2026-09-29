-- Prove2me | Theorems.Thm_WorkbookSource_problem_46411
-- name    : WorkbookSource.problem_46411
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T14:37:15.87183+00:00
-- url     : https://prove2.me/theorems/9275df64-6ad8-4405-95cd-5d719a354264
-- title:
--   An exact square-root evaluation
-- statement:
--   Compute $\sqrt{96\times 98 - 71\times 73}.$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_46411` (Apache-2.0). The complete source proposition and its explicit variable declarations are preserved. Notation repair: Expanded scoped notation into Nat.totient or Real.sqrt; the elaborated mathematical expression and binders are unchanged.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_46411; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_46411 (x : ℕ) (hx: x = 5) : Real.sqrt (96 * 98 - 71 * 73) = 65  :=  by sorry
