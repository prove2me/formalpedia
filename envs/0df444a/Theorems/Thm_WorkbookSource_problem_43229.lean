-- Prove2me | Theorems.Thm_WorkbookSource_problem_43229
-- name    : WorkbookSource.problem_43229
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T21:40:39.127027+00:00
-- url     : https://prove2.me/theorems/272bcc85-739a-48d9-b215-cbe4f7c944b4
-- title:
--   Rewriting a symmetric cubic inequality
-- statement:
--   For real $a,b,c$, set $S=ab(a+b)+bc(b+c)+ca(c+a)$. Then
--
--   $$S\ge\frac34(a+b)(b+c)(c+a)\quad\Longleftrightarrow\quad S\ge6abc.$$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_43229` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_43229; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_43229  (a b c : ℝ) :
  a * b * (a + b) + b * c * (b + c) + c * a * (c + a) ≥
  (3 * (a + b) * (b + c) * (c + a)) / 4 ↔
  a * b * (a + b) + b * c * (b + c) + c * a * (c + a) ≥
  6 * a * b * c  :=  by sorry
