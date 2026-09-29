-- Prove2me | Theorems.Thm_WorkbookSource_problem_40557
-- name    : WorkbookSource.problem_40557
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T21:40:09.040648+00:00
-- url     : https://prove2.me/theorems/e0c63c41-233f-4590-aa65-da3acad862c0
-- title:
--   Solving a two-equation linear system
-- statement:
--   For real $x,y$,
--
--   $$\bigl(2x+6+2y=0\ \text{and}\ 4y+2+2x=0\bigr)\quad\Longleftrightarrow\quad(x=-5\ \text{and}\ y=2).$$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_40557` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_40557; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_40557 (x y : ℝ) : (2*x+6+2*y=0 ∧ 4*y+2+2*x=0) ↔ (x = -5 ∧ y = 2)  :=  by sorry
