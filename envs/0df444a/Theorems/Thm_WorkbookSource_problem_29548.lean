-- Prove2me | Theorems.Thm_WorkbookSource_problem_29548
-- name    : WorkbookSource.problem_29548
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T14:36:51.936281+00:00
-- url     : https://prove2.me/theorems/ba12bdf1-4c26-434e-bc69-049a9464144e
-- title:
--   The fifteenth term of an integer recurrence
-- statement:
--   Let $ a_0 = 2$ , $ a_1 = 9$ , and $ a_n = 2a_{n - 1} - 4a_{n - 2}.$ Compute $ a_{15}$ .
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_29548` (Apache-2.0). The complete source proposition and its explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_29548; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_29548 (a : ℕ → ℤ) (a0 : a 0 = 2) (a1 : a 1 = 9) (a_rec : ∀ n, n ≥ 2 → a n = 2 * a (n - 1) - 4 * a (n - 2)) : a 15 = -2^16  :=  by sorry
