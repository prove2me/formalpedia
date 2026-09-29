-- Prove2me | Theorems.Thm_WorkbookSource_problem_44582
-- name    : WorkbookSource.problem_44582
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T21:50:43.441525+00:00
-- url     : https://prove2.me/theorems/9e87ba5f-8b5f-499f-b3de-f3146efe1e66
-- title:
--   Factoring a fifth-degree equation
-- statement:
--   (Solution) $x^5-2x^2-9x-6=0\Leftrightarrow (x+1)^2(x-2)(x^2+3)=0$
--
--   Source: InternLM Lean-Workbook, record lean_workbook_44582; Apache-2.0. Complete source proposition preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_44582; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_44582 (x : ℝ) : x^5 - 2 * x^2 - 9 * x - 6 = 0 ↔ (x + 1)^2 * (x - 2) * (x^2 + 3) = 0  :=  by sorry
