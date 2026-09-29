-- Prove2me | Theorems.Thm_WorkbookSource_problem_54150
-- name    : WorkbookSource.problem_54150
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T21:40:42.37445+00:00
-- url     : https://prove2.me/theorems/4defd369-bb88-4fb6-8975-5fd887cc2785
-- title:
--   Dividing a quadratic by a linear expression
-- statement:
--   $(a^2+1)/(a+k)=a-k+(k^2+1)/(a+k)$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_54150` (Apache-2.0). The complete source proposition and its explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_54150; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_54150 (a k : ℝ) (h : a ≠ -k) : (a^2 + 1) / (a + k) = a - k + (k^2 + 1) / (a + k)  :=  by sorry
