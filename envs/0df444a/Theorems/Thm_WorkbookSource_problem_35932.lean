-- Prove2me | Theorems.Thm_WorkbookSource_problem_35932
-- name    : WorkbookSource.problem_35932
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T14:59:47.272103+00:00
-- url     : https://prove2.me/theorems/593c940e-9bcf-45e2-b1a1-74c0cacc03a6
-- title:
--   Solving a shifted strict inequality
-- statement:
--   For every real number $x$,
--
--   $$x+2<1\quad\Longleftrightarrow\quad x<-1.$$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_35932` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_35932; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_35932 (x : ℝ) : x + 2 < 1 ↔ x < -1  :=  by sorry
