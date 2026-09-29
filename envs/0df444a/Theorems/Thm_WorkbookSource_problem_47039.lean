-- Prove2me | Theorems.Thm_WorkbookSource_problem_47039
-- name    : WorkbookSource.problem_47039
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T21:50:58.405489+00:00
-- url     : https://prove2.me/theorems/49173301-d6cd-4c8a-8380-557b00860403
-- title:
--   Strict monotonicity of a rational expression
-- statement:
--   If $ x > y > -1$ , prove that $ \frac{x}{1+x} > \frac{y}{1+y}$ .
--
--   Source: InternLM Lean-Workbook, record lean_workbook_47039; Apache-2.0. Complete source proposition preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_47039; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_47039 (x y : ℝ) (h : x > y) (h' : y > -1) : (x / (1 + x)) > (y / (1 + y))  :=  by sorry
