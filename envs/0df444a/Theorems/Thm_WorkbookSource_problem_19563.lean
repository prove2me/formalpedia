-- Prove2me | Theorems.Thm_WorkbookSource_problem_19563
-- name    : WorkbookSource.problem_19563
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T14:13:22.210203+00:00
-- url     : https://prove2.me/theorems/5e90fde6-56f1-4922-8a08-4efed4c7e046
-- title:
--   Combining two rational terms involving a natural power
-- statement:
--   Prove that: $S_1=\frac{n}{n+1}-\frac{n}{(n+1)n^n}=\frac{n(n^n-1)}{n^n(n+1)}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_19563` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_19563; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_19563 (n : ℕ) (hn : n ≠ 0) : (n : ℝ) / (n + 1) - (n : ℝ) / ((n + 1) * n ^ n) = (n * (n ^ n - 1)) / (n ^ n * (n + 1))  :=  by sorry
