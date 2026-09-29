-- Prove2me | Theorems.Thm_WorkbookSource_problem_33749
-- name    : WorkbookSource.problem_33749
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T14:59:56.423557+00:00
-- url     : https://prove2.me/theorems/5cc5a408-5adc-4051-9550-9207c1535833
-- title:
--   A product inequality and its difference factor
-- statement:
--   For real numbers $a,b,c,d$,
--
--   $$ (a+b)(c+d)\le 2(ac+bd)\quad\Longleftrightarrow\quad(a-b)(c-d)\ge0. $$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_33749` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_33749; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_33749  (a b c d : ℝ) :
  (a + b) * (c + d) ≤ 2 * (a * c + b * d) ↔ (a - b) * (c - d) ≥ 0  :=  by sorry
