-- Prove2me | Theorems.Thm_WorkbookSource_problem_34138
-- name    : WorkbookSource.problem_34138
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T14:59:33.304132+00:00
-- url     : https://prove2.me/theorems/681c1747-2beb-47f2-bc5a-66e1dddc6912
-- title:
--   A square of five modulo one hundred
-- statement:
--   The following modular identity holds:
--
--   $$5^{2\cdot1}\equiv25\pmod{100}.$$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_34138` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_34138; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_34138 :
  (5^(2*1) ≡ 25 [ZMOD 100])  :=  by sorry
