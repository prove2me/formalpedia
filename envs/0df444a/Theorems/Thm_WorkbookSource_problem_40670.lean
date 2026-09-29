-- Prove2me | Theorems.Thm_WorkbookSource_problem_40670
-- name    : WorkbookSource.problem_40670
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T21:40:12.545993+00:00
-- url     : https://prove2.me/theorems/3bba6102-ea0a-40f9-b2dc-afa734bf0e17
-- title:
--   A power of two modulo seven
-- statement:
--   The remainder is
--
--   $$2^{20}\bmod7=4.$$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_40670` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_40670; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_40670 :
  (2^20) % 7 = 4  :=  by sorry
