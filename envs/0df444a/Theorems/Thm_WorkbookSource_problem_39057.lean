-- Prove2me | Theorems.Thm_WorkbookSource_problem_39057
-- name    : WorkbookSource.problem_39057
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T21:39:51.852384+00:00
-- url     : https://prove2.me/theorems/e6d712a6-31cf-4e7f-82ee-016943f033ca
-- title:
--   A sum of two powers is not divisible by five
-- statement:
--   The natural number $2^{29}+2^{15}+1$ is not divisible by $5$.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_39057` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_39057; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_39057 : ¬(5 ∣ (2^29 + 2^15 + 1))  :=  by sorry
