-- Prove2me | Theorems.Thm_WorkbookSource_problem_46416
-- name    : WorkbookSource.problem_46416
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T21:50:55.984191+00:00
-- url     : https://prove2.me/theorems/ebb83a2b-4818-45f2-bc27-58f07da74acf
-- title:
--   Dividing by a product of fractions
-- statement:
--   $\frac{5}{\frac12\frac16}=\boxed{60}$
--
--   Source: InternLM Lean-Workbook, record lean_workbook_46416; Apache-2.0. Complete source proposition preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_46416; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_46416 (a : ℚ) (h : a = 5 / (1 / 2 * 1 / 6)) : a = 60  :=  by sorry
