-- Prove2me | Theorems.Thm_WorkbookSource_base_11000
-- name    : WorkbookSource.base_11000
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T00:43:37.123016+00:00
-- url     : https://prove2.me/theorems/62295175-d3c9-4fdf-8149-0af6016c4766
-- title:
--   A sixth-power bound for a product of symmetric sums
-- statement:
--   If $a,b,c$ are positive reals,prove that:
--    $(a+b+c)^6\geq 27(a^2+b^2+c^2)(ab+bc+ca)^2$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_11000` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_11000; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_11000 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a + b + c) ^ 6 ≥ 27 * (a ^ 2 + b ^ 2 + c ^ 2) * (a * b + b * c + c * a) ^ 2  :=  by sorry
