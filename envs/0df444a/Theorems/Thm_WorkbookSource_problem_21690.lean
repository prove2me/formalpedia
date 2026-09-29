-- Prove2me | Theorems.Thm_WorkbookSource_problem_21690
-- name    : WorkbookSource.problem_21690
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T22:01:29.706557+00:00
-- url     : https://prove2.me/theorems/916f0452-c7c5-4d70-804c-b39689b8d358
-- title:
--   Simplifying a square-root coefficient
-- statement:
--   $\rm P(0,\dfrac{-1}{2}): f(0)=\dfrac{1}{\sqrt{2}}\cdot 2f(\dfrac{-1}{2})\Leftrightarrow 2f(0)=2\sqrt{2}f(\dfrac{-1}{2})$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_21690` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_21690; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_21690 (f : ℝ → ℝ) (hf: f (0:ℝ) = 1 / Real.sqrt 2 * 2 * f (-1/2)) : 2 * f 0 = 2 * Real.sqrt 2 * f (-1/2)  :=  by sorry
