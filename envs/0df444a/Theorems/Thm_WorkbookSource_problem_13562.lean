-- Prove2me | Theorems.Thm_WorkbookSource_problem_13562
-- name    : WorkbookSource.problem_13562
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T14:47:41.298992+00:00
-- url     : https://prove2.me/theorems/34b2b8ab-2c49-48b2-938f-88c4abb9ae71
-- title:
--   A binomial sum at multiples of three
-- statement:
--   Compute $\sum_{k=0}^{15}\binom{46}{3k}.$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_13562` (Apache-2.0). The complete source proposition and its explicit variable declarations are preserved. Notation repair: Update legacy finite-sum notation. Restore the missing colon separating theorem name and proposition.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_13562; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_13562 : ∑ k ∈ Finset.range 16, choose 46 (3 * k) = 23456248059221  :=  by sorry
