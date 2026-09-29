-- Prove2me | Theorems.Thm_WorkbookSource_problem_6696
-- name    : WorkbookSource.problem_6696
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T14:39:55.958216+00:00
-- url     : https://prove2.me/theorems/7b7dc712-9f67-4888-9b8b-27fedf975b00
-- title:
--   A cancellation identity for six real variables
-- statement:
--   prove: $ \left ( (b - a)(d - c)(f - e) - (b - c)(d - e)(f - a) \right ) + \left ( (b - c)(a - e)(f - d) + (c - a)(e - f)(d - b) \right ) = 0$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_6696` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_6696; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_6696 (a b c d e f : ℝ) : (b - a) * (d - c) * (f - e) - (b - c) * (d - e) * (f - a) + (b - c) * (a - e) * (f - d) + (c - a) * (e - f) * (d - b) = 0  :=  by sorry
