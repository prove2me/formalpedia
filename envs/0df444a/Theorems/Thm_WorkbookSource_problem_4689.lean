-- Prove2me | Theorems.Thm_WorkbookSource_problem_4689
-- name    : WorkbookSource.problem_4689
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T14:11:24.121455+00:00
-- url     : https://prove2.me/theorems/1e3d7436-9fd7-49d3-b798-85821c423573
-- title:
--   Factoring an integer quartic
-- statement:
--   Express $n^4-20n^2+4$ as a product of two quadratic polynomials.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_4689` (Apache-2.0). The complete source proposition and its explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_4689; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_4689 : ∀ n : ℤ, n^4 - 20*n^2 + 4 = (n^2 - 4*n - 2)*(n^2 + 4*n - 2)  :=  by sorry
