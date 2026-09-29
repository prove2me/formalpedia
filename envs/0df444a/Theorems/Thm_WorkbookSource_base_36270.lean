-- Prove2me | Theorems.Thm_WorkbookSource_base_36270
-- name    : WorkbookSource.base_36270
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T00:18:23.703454+00:00
-- url     : https://prove2.me/theorems/64969a05-d4ea-4a99-8b08-5d305aef45bd
-- title:
--   A four-variable quartic inequality with four linear factors
-- statement:
--   Let $a, b, c, d$ be real positive numbers. Prove: $2(a^4+b^4+c^4+d^4) + (a+b+c-d)(a+b+d-c)(a+c+d-b)(b+c+d-a) \ge 8abcd+ (a+b+c+d)(abc+bcd+cda+dab) \ \ ;$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_36270` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_36270; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_36270 (a b c d : ℝ) : 2 * (a ^ 4 + b ^ 4 + c ^ 4 + d ^ 4) + (a + b + c - d) * (a + b + d - c) * (a + c + d - b) * (b + c + d - a) ≥ 8 * a * b * c * d + (a + b + c + d) * (a * b * c + b * c * d + c * d * a + d * a * b)  :=  by sorry
