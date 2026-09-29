-- Prove2me | Theorems.Thm_WorkbookSource_problem_1096
-- name    : WorkbookSource.problem_1096
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T14:39:14.170617+00:00
-- url     : https://prove2.me/theorems/2a220bd6-d446-4145-90ee-1d062d03f57c
-- title:
--   Rearranging a symmetric cubic inequality
-- statement:
--   By am-gm $, \ \ c+ab\le \frac{c^2+1}{2}+\frac{a^2+b^2}{2}$ . Then
--
--    $ \ (ab+bc+ca)-abc\le \frac{c^2+1}{2}+\frac{a^2+b^2}{2} \ \ \ \iff \ \ \ a^2+b^2+c^2+2abc+1\ge 2(ab+bc+ca)$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_1096` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_1096; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_1096  (a b c : ℝ) :
  a * b + b * c + c * a - a * b * c ≤ (c^2 + 1) / 2 + (a^2 + b^2) / 2 ↔
  a^2 + b^2 + c^2 + 2 * a * b * c + 1 ≥ 2 * (a * b + b * c + c * a)  :=  by sorry
