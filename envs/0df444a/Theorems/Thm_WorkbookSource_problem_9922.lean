-- Prove2me | Theorems.Thm_WorkbookSource_problem_9922
-- name    : WorkbookSource.problem_9922
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T14:46:25.167389+00:00
-- url     : https://prove2.me/theorems/6d4c1820-8475-4709-98bf-f5e628af42c3
-- title:
--   Adding six unit lower bounds
-- statement:
--   Let $a\geq 1,\ b\geq 1,\ c\geq 1,\ d\geq 1,\ e\geq 1,\ f\geq 1$ . Prove that $a+b+c+d+e+f\geq 6$ .
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_9922` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_9922; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_9922 (a b c d e f : ℝ) (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c) (hd : 1 ≤ d) (he : 1 ≤ e) (hf : 1 ≤ f) : a + b + c + d + e + f ≥ 6  :=  by sorry
