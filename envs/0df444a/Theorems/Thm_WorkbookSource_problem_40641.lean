-- Prove2me | Theorems.Thm_WorkbookSource_problem_40641
-- name    : WorkbookSource.problem_40641
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T21:40:13.94698+00:00
-- url     : https://prove2.me/theorems/36c5019c-cf1e-49eb-809d-3e209fd042fa
-- title:
--   The last digit of a power of twelve
-- statement:
--   The last decimal digit of $12^{100}$ is $6$:
--
--   $$12^{100}\equiv6\pmod{10}.$$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_40641` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_40641; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_40641 : 12 ^ 100 ≡ 6 [ZMOD 10]  :=  by sorry
