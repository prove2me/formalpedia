-- Prove2me | Theorems.Thm_WorkbookSource_problem_22878
-- name    : WorkbookSource.problem_22878
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T21:50:33.517136+00:00
-- url     : https://prove2.me/theorems/34fadfce-b487-43a6-8d27-8bd325c53f71
-- title:
--   Subtracting two binomial coefficients
-- statement:
--   Subtract $\binom{20}{5}$ from $\binom{24}{5}$.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_22878` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_22878; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_22878 : (choose 24 5) - (choose 20 5) = 27000  :=  by sorry
