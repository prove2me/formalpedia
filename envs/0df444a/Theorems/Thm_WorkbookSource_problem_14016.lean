-- Prove2me | Theorems.Thm_WorkbookSource_problem_14016
-- name    : WorkbookSource.problem_14016
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T15:02:58.476376+00:00
-- url     : https://prove2.me/theorems/70ecd8e2-b5b3-413d-a2f2-dfcb63dfa5eb
-- title:
--   A double-angle value from a sine-cosine sum
-- statement:
--   Given $\sin x+\cos x=\tfrac{6}{5}$, find $\sin2x$.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_14016` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_14016; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_14016 (x : ℝ) (h : sin x + cos x = 6/5) : sin (2 * x) = 11/25  :=  by sorry
