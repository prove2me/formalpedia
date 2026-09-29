-- Prove2me | Theorems.Thm_WorkbookSource_problem_21745
-- name    : WorkbookSource.problem_21745
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T21:50:27.4654+00:00
-- url     : https://prove2.me/theorems/55311461-1562-4c57-8869-f265f6b69c95
-- title:
--   Adding two cubic terms
-- statement:
--   Given $\sqrt{x}=a^3-4=4-b^3$, show that $a^3+b^3-8=0$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_21745` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_21745; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_21745 (x a b : ℝ) (hx : x ≥ 0 ∧ a^3 - 4 = 4 - b^3) : a^3 + b^3 - 8 = 0  :=  by sorry
