-- Prove2me | Theorems.Thm_WorkbookSource_problem_4319
-- name    : WorkbookSource.problem_4319
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T14:39:38.28289+00:00
-- url     : https://prove2.me/theorems/94335f32-e841-4817-9024-97e4f6c21102
-- title:
--   A five-variable quadratic inequality under a pair-product constraint
-- statement:
--   Let $a,b,c,d,e$ be real numbrs such that $ab+bc+ca=12de$ . Prove that
--
--    $32(a^2+b^2+c^2+d^2+e^2)\ge 7(a+b+c+d+e)^2$ .
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_4319` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_4319; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_4319 (a b c d e : ℝ) (h : a * b + b * c + c * a = 12 * d * e) :
    32 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 + e ^ 2) ≥ 7 * (a + b + c + d + e) ^ 2  :=  by sorry
