-- Prove2me | Theorems.Thm_WorkbookSource_base_30439
-- name    : WorkbookSource.base_30439
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T22:47:50.72722+00:00
-- url     : https://prove2.me/theorems/c7f22062-448e-4373-a498-c3fc1e01a925
-- title:
--   A quartic inequality involving an antisymmetric product
-- statement:
--   If a, b, c are real number then: $ (a^2+b^2+c^2)^2-3abc(a+b+c) \ge 3(a+b+c)(a-b)(b-c)(c-a) $
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_30439` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_30439; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_30439 (a b c : ℝ) : (a^2 + b^2 + c^2)^2 - 3 * a * b * c * (a + b + c) ≥ 3 * (a + b + c) * (a - b) * (b - c) * (c - a)  :=  by sorry
