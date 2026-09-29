-- Prove2me | Theorems.Thm_WorkbookSource_plus_9631
-- name    : WorkbookSource.plus_9631
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T22:51:15.115243+00:00
-- url     : https://prove2.me/theorems/f0dd8662-5496-47c2-8670-f77226d2428c
-- title:
--   A symmetric quartic inequality with mixed coefficients
-- statement:
--   Prove that for all real numbers $a$, $b$, and $c$, the following inequality holds:
--   $352(a^4+b^4+c^4)-536[a^3(b+c)+b^3(c+a)+c^3(a+b)]+411(a^2b^2+b^2c^2+c^2a^2)+336(a^2bc+b^2ca+c^2ab)\geq 0.$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_9631` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_9631; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_9631 (a b c : ℝ) : 352 * (a ^ 4 + b ^ 4 + c ^ 4) - 536 * (a ^ 3 * (b + c) + b ^ 3 * (c + a) + c ^ 3 * (a + b)) + 411 * (a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * a ^ 2) + 336 * (a ^ 2 * b * c + b ^ 2 * c * a + c ^ 2 * a * b) ≥ 0   :=  by sorry
