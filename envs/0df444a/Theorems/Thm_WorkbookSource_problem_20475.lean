-- Prove2me | Theorems.Thm_WorkbookSource_problem_20475
-- name    : WorkbookSource.problem_20475
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T14:13:24.012748+00:00
-- url     : https://prove2.me/theorems/8bbc6e12-a73e-4ee4-a42d-9458ba672df6
-- title:
--   Odd powers preserve a zero sum
-- statement:
--   If $a + b = 0$ and $n$ is odd, prove that $a^n + b^n = 0$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_20475` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_20475; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_20475 (a b : ℝ) (n : ℕ) (hn : Odd n) (hab : a + b = 0) : a^n + b^n = 0  :=  by sorry
