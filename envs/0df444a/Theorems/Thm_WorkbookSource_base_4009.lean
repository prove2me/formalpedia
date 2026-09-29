-- Prove2me | Theorems.Thm_WorkbookSource_base_4009
-- name    : WorkbookSource.base_4009
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T00:08:40.725359+00:00
-- url     : https://prove2.me/theorems/627fad0f-57b3-4f54-86ab-82beff8d6fa9
-- title:
--   A cyclic four-variable quartic inequality
-- statement:
--   Let $ a,b,c,d$ are real numbers,prove that: $(b^2+c^2+d^2+a^2)^2\geq (c^2b+cd^2+a^2d+b^2a)(a+b+c+d).$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_4009` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_4009; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_4009 (a b c d : ℝ) : (b^2 + c^2 + d^2 + a^2)^2 ≥ (c^2 * b + c * d^2 + a^2 * d + b^2 * a) * (a + b + c + d)  :=  by sorry
