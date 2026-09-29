-- Prove2me | Theorems.Thm_WorkbookSource_problem_7425
-- name    : WorkbookSource.problem_7425
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T14:47:32.708344+00:00
-- url     : https://prove2.me/theorems/fe8bee95-e91b-45ca-b95e-4b560b3caeca
-- title:
--   Counting a residue class in a thousand-number interval
-- statement:
--   How many integers between $1000$ and $2000$ are congruent to $2 (mod 7)?$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_7425` (Apache-2.0). The complete source proposition and its explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_7425; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_7425 : Finset.card (Finset.filter (λ x => x % 7 = 2) (Finset.Icc 1000 2000)) = 143  :=  by sorry
