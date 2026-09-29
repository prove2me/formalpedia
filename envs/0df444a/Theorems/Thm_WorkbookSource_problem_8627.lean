-- Prove2me | Theorems.Thm_WorkbookSource_problem_8627
-- name    : WorkbookSource.problem_8627
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T14:46:09.800341+00:00
-- url     : https://prove2.me/theorems/43ce3a47-26cf-494b-8851-5498d0ba19e6
-- title:
--   A logarithm bound on its full real domain
-- statement:
--   Prove: $ \forall x \in ]-1;+\infty[ ; ln(x+1) \leq x $.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_8627` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved. The related Open record plus_50985 has the same complete domain; this restores a source-checked representative.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_8627; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_8627 (x : ℝ) (hx : -1 < x) : Real.log (x + 1) ≤ x  :=  by sorry
