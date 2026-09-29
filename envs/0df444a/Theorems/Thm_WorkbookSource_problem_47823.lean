-- Prove2me | Theorems.Thm_WorkbookSource_problem_47823
-- name    : WorkbookSource.problem_47823
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T22:03:48.770462+00:00
-- url     : https://prove2.me/theorems/5b748895-0884-496b-8eba-592d0bd4053e
-- title:
--   Multiplying three rational factors
-- statement:
--   $\frac{1}{4}\cdot\frac{2}{9}\cdot\frac{1}{2}=\boxed{\frac{1}{36}}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_47823` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_47823; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_47823 (a : ℚ) (h : a = 1 / 4 * (2 / 9 * (1 / 2))) : a = 1 / 36  :=  by sorry
