-- Prove2me | Theorems.Thm_WorkbookSource_problem_53513
-- name    : WorkbookSource.problem_53513
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T22:09:14.098536+00:00
-- url     : https://prove2.me/theorems/c0d23b4b-bf59-412f-a317-a38ebe1ba606
-- title:
--   The sign of a quadratic on its root interval
-- statement:
--   If $x > 0$ and $y < 0$, prove that $y^2 + y - 2 \leq 0$ for all $y$ in $[-2, 1]$.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_53513` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_53513; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_53513 (y : ℝ) (hy : -2 ≤ y ∧ y ≤ 1) : y^2 + y - 2 ≤ 0  :=  by sorry
