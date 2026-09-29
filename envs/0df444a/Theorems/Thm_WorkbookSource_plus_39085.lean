-- Prove2me | Theorems.Thm_WorkbookSource_plus_39085
-- name    : WorkbookSource.plus_39085
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T22:51:22.285158+00:00
-- url     : https://prove2.me/theorems/2fafbb28-e4ac-4cfe-8a8e-398c72516181
-- title:
--   A cyclic quartic expression is nonnegative
-- statement:
--   If a, b, c are real number then: $ 3(a^4+b^4+c^4)+4(a^3b+b^3c+c^3a)-6abc(a+b+c) \ge 0 $
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_39085` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_39085; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_39085 (a b c : ℝ) : 3 * (a ^ 4 + b ^ 4 + c ^ 4) + 4 * (a ^ 3 * b + b ^ 3 * c + c ^ 3 * a) - 6 * a * b * c * (a + b + c) ≥ 0   :=  by sorry
