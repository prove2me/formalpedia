-- Prove2me | Theorems.Thm_WorkbookSource_problem_49786
-- name    : WorkbookSource.problem_49786
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T22:08:51.200023+00:00
-- url     : https://prove2.me/theorems/0e1f05bc-447a-4fe9-a367-29789b4d271d
-- title:
--   Expanding a symmetric cubic expression
-- statement:
--   Prove that for a, b, c > 0:
--    $ (a + b + c)^3 - \left(\sum_{cyc} a(a^2 + 3b^2 + 3c^2)\right)\ge 0\iff 6abc\ge 0$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_49786` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_49786; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_49786 (a b c : ℝ) :
  (a + b + c) ^ 3 - (a * (a ^ 2 + 3 * b ^ 2 + 3 * c ^ 2) + b * (b ^ 2 + 3 * c ^ 2 + 3 * a ^ 2) + c * (c ^ 2 + 3 * a ^ 2 + 3 * b ^ 2)) ≥ 0 ↔ 6 * a * b * c ≥ 0  :=  by sorry
