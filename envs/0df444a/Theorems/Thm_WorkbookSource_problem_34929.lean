-- Prove2me | Theorems.Thm_WorkbookSource_problem_34929
-- name    : WorkbookSource.problem_34929
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T14:59:55.070994+00:00
-- url     : https://prove2.me/theorems/199097fe-caf2-4036-a28c-d4ce9a025e79
-- title:
--   Simplifying a quadratic constraint
-- statement:
--   Let $x,y,z$ be real numbers satisfying
--
--   $$(x+y)^2+(y+z)^2+(z+x)^2+4(x^2+yz+xz+yx)=128.$$
--
--   Then
--
--   $$x^2+y^2+z^2+3(xy+xz+yz)=64-2x^2.$$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_34929` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_34929; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_34929 (x y z : ℝ) : (x + y) ^ 2 + (y + z) ^ 2 + (z + x) ^ 2 + 4 * (x ^ 2 + y * z + x * z + y * x) = 128 → x ^ 2 + y ^ 2 + z ^ 2 + 3 * (x * y + x * z + y * z) = 64 - 2 * x ^ 2  :=  by sorry
