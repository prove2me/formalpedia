-- Prove2me | Theorems.Thm_WorkbookSource_problem_56689
-- name    : WorkbookSource.problem_56689
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T14:14:05.623109+00:00
-- url     : https://prove2.me/theorems/769a49de-b9a2-4a2e-9eab-ca2d4d35ce97
-- title:
--   A difference of two absolute polynomial values
-- statement:
--   Find the value of $|2a^3 - 3a^2 - 2a + 1| - |2a^3 - 3a^2 - 3a - 2009|$ given $a = 2009$.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_56689` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_56689; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_56689 (a : ℝ) (h : a = 2009) : |2*a^3 - 3*a^2 - 2*a + 1| - |2*a^3 - 3*a^2 - 3*a - 2009| = 4019  :=  by sorry
