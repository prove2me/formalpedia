-- Prove2me | Theorems.Thm_WorkbookSource_problem_7972
-- name    : WorkbookSource.problem_7972
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T14:13:06.32835+00:00
-- url     : https://prove2.me/theorems/76f229cc-1a25-485a-8595-fb85873982d9
-- title:
--   A three-factor sum-of-two-squares identity
-- statement:
--   Prove that $(a^{2}+x^{2})(b^{2}+y^{2})(c^{2}+z^{2})=(ayz+bxz+cxy-abc)^2+(xbc+yac+zab-xyz)^2$ where $a, b, c, x, y, z$ are non-negative numbers.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_7972` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_7972; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_7972 (a b c x y z: ℝ) : (a ^ 2 + x ^ 2) * (b ^ 2 + y ^ 2) * (c ^ 2 + z ^ 2) = (a * y * z + b * x * z + c * x * y - a * b * c) ^ 2 + (x * b * c + y * a * c + z * a * b - x * y * z) ^ 2  :=  by sorry
