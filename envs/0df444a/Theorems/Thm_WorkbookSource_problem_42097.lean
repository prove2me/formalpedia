-- Prove2me | Theorems.Thm_WorkbookSource_problem_42097
-- name    : WorkbookSource.problem_42097
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T21:40:30.783453+00:00
-- url     : https://prove2.me/theorems/8eb930ec-fd0a-4af5-9d7d-95dc4a63280d
-- title:
--   Expanding a symmetric cubic product
-- statement:
--   For real $a,b,c$,
--
--   $$a^3+b^3+c^3+ab(a+b)+bc(b+c)+ca(c+a)=(a^2+b^2+c^2)(a+b+c).$$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_42097` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_42097; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_42097 (a b c : ℝ) : a^3 + b^3 + c^3 + a * b * (a + b) + b * c * (b + c) + c * a * (c + a) = (a^2 + b^2 + c^2) * (a + b + c)  :=  by sorry
