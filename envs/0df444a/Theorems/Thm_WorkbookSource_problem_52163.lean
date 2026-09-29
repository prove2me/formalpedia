-- Prove2me | Theorems.Thm_WorkbookSource_problem_52163
-- name    : WorkbookSource.problem_52163
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T13:02:41.782848+00:00
-- url     : https://prove2.me/theorems/ff00808b-bea0-40e8-a145-0a1a0086f966
-- title:
--   A symmetric cubic inequality
-- statement:
--   Let $ a,b,c \ge 0$ . prove that
--
--    $ abc + 5(a + b + c)^3 \ge 17(a + b)(b + c)(c + a)$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_52163` (Apache-2.0). The complete source proposition and its explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_52163; Apache-2.0

import Mathlib
open Real

theorem WorkbookSource.problem_52163 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) : a * b * c + 5 * (a + b + c) ^ 3 ≥ 17 * (a + b) * (b + c) * (c + a)  :=  by sorry
