-- Prove2me | Theorems.Thm_WorkbookSource_problem_10314
-- name    : WorkbookSource.problem_10314
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T14:11:28.06298+00:00
-- url     : https://prove2.me/theorems/8bba7ac5-860b-40f7-86d1-160e15e96df2
-- title:
--   An exponential lower bound for every natural number
-- statement:
--   Prove that $3^n \ge 2n + 1$ for $n \in \mathbb{Z^+}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_10314` (Apache-2.0). The complete source proposition and its explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_10314; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_10314 (n : ℕ) : 3^n ≥ 2*n + 1  :=  by sorry
