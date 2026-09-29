-- Prove2me | Theorems.Thm_WorkbookSource_problem_32495
-- name    : WorkbookSource.problem_32495
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T21:59:12.673133+00:00
-- url     : https://prove2.me/theorems/88b46052-cc0c-4647-a8f9-dd0ddb3f4aeb
-- title:
--   The digit-sum congruence for 123
-- statement:
--   Apply properties of $\pmod{9}$ to show that $123 \equiv 1+2+3 \pmod{9}$.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_32495` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_32495; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_32495 : 123 ≡ (1 + 2 + 3) [ZMOD 9]  :=  by sorry
