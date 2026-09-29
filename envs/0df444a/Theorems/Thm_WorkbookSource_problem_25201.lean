-- Prove2me | Theorems.Thm_WorkbookSource_problem_25201
-- name    : WorkbookSource.problem_25201
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T12:40:40.969408+00:00
-- url     : https://prove2.me/theorems/319ad390-bfb7-4a34-aeb4-6497b05bf996
-- title:
--   A weighted square inequality
-- statement:
--   prove that : $(px+qy)^2\leq px^2+qy^2$ for numbers $p,q > 0 $ and $p+q < 1 $
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_25201` (Apache-2.0). The complete source proposition and its explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_25201; Apache-2.0

import Mathlib
open Real

theorem WorkbookSource.problem_25201 (x y : ℝ) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (hpq : p + q < 1) : (p * x + q * y) ^ 2 ≤ p * x ^ 2 + q * y ^ 2  :=  by sorry
