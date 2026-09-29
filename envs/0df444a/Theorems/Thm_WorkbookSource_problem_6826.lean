-- Prove2me | Theorems.Thm_WorkbookSource_problem_6826
-- name    : WorkbookSource.problem_6826
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T14:39:52.586532+00:00
-- url     : https://prove2.me/theorems/93126a8a-b969-4ee0-8619-81c4d769b607
-- title:
--   A cyclic inequality between three quadratic products
-- statement:
--   Let $ a,$ $ b,$ $ c$ be real numbers. Prove that
--    $ \begin{aligned} (a^2 + 2ab & + 3b^2)(b^2 + 2bc + 3c^2)(c^2 + 2ca + 3a^2) \ge
--    & \ge 8(a^2 + ab + bc)(b^2 + bc + ca)(c^2 + ca + ab).\end{aligned}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_6826` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_6826; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_6826 (a b c : ℝ) : (a^2 + 2 * a * b + 3 * b^2) * (b^2 + 2 * b * c + 3 * c^2) * (c^2 + 2 * c * a + 3 * a^2) ≥ 8 * (a^2 + a * b + b * c) * (b^2 + b * c + c * a) * (c^2 + c * a + a * b)  :=  by sorry
