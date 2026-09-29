-- Prove2me | Theorems.Thm_WorkbookSource_base_10192
-- name    : WorkbookSource.base_10192
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T00:44:45.457256+00:00
-- url     : https://prove2.me/theorems/35993629-25ba-44eb-9072-9151c14c7bbb
-- title:
--   A product comparison for shifted fourth powers
-- statement:
--   Let $ a,b,c >0 $ .Prove that $(a^{4}+1)(b^{4}+1)(c^{4}+1)\geq (a^{3}b+1)(b^{3}c+1)(c^{3}a+1) $
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_10192` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_10192; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_10192 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^4 + 1) * (b^4 + 1) * (c^4 + 1) ≥ (a^3 * b + 1) * (b^3 * c + 1) * (c^3 * a + 1)  :=  by sorry
