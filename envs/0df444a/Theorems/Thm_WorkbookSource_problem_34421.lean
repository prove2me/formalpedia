-- Prove2me | Theorems.Thm_WorkbookSource_problem_34421
-- name    : WorkbookSource.problem_34421
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T14:37:03.996801+00:00
-- url     : https://prove2.me/theorems/444e826d-0e33-4df1-b1ca-5d2fd10b9b09
-- title:
--   Solving a linear congruence modulo five
-- statement:
--   Find the value of j that satisfies $2j+1\equiv 4\pmod{5}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_34421` (Apache-2.0). The complete source proposition and its explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_34421; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_34421 (j : ℕ) : (2 * j + 1 ≡ 4 [ZMOD 5]) ↔ j ≡ 4 [ZMOD 5]  :=  by sorry
