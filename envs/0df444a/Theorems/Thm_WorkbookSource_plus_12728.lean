-- Prove2me | Theorems.Thm_WorkbookSource_plus_12728
-- name    : WorkbookSource.plus_12728
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T14:15:16.619054+00:00
-- url     : https://prove2.me/theorems/c7da4ac8-2400-4109-9a50-d0519aa912a2
-- title:
--   A counterexample to a six-variable polynomial inequality
-- statement:
--   Find a counterexample for the inequality: $4(a^{2}+x^{2})(b^{2}+y^{2})(c^{2}+z^{2})\geq 3(abx+bcy+caz)^{2}$ for real numbers $a, b, c, x, y, z$.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_12728` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_12728; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_12728 : ∃ a b c x y z : ℝ, ¬(4 * (a ^ 2 + x ^ 2) * (b ^ 2 + y ^ 2) * (c ^ 2 + z ^ 2) ≥ 3 * (a * b * x + b * c * y + c * a * z) ^ 2)   :=  by sorry
