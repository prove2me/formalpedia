-- Prove2me | Theorems.Thm_WorkbookSource_problem_24837
-- name    : WorkbookSource.problem_24837
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T22:01:33.422924+00:00
-- url     : https://prove2.me/theorems/afb05638-7d2e-4fc8-b30a-9079384fb828
-- title:
--   Multiplying a power by its base
-- statement:
--   Prove that $ 2000(2000^{2000}) = 2000^{2001}$.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_24837` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_24837; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_24837 : 2000 * (2000 ^ 2000) = 2000 ^ 2001  :=  by sorry
