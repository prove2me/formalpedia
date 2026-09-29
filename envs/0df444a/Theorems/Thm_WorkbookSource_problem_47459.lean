-- Prove2me | Theorems.Thm_WorkbookSource_problem_47459
-- name    : WorkbookSource.problem_47459
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T14:13:55.344539+00:00
-- url     : https://prove2.me/theorems/60236cda-ce85-46dc-aae4-f26a17cbc5ad
-- title:
--   The norm of twice a specified real number
-- statement:
--   So $k=-11-\frac{37}2$ and $\boxed{|2k|=59}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_47459` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_47459; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_47459 (k : ℝ) (h : k = -11 - 37 / 2) : ‖2 * k‖ = 59  :=  by sorry
