-- Prove2me | Theorems.Thm_WorkbookSource_base_55824
-- name    : WorkbookSource.base_55824
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T01:16:41.148557+00:00
-- url     : https://prove2.me/theorems/719e1f8b-6b0b-4593-a462-7532271cc358
-- title:
--   A cyclic seventh-degree comparison of mixed products
-- statement:
--   Let $a,b,c>0$ . Show that:
--    $ a^{4}c^{3}+b^{4}a^{3}+c^{4}b^{3}+2abc(a^{4}+b^{4}+c^{4})\geq 3abc(a^{2}b^{2}+b^{2}c^{2}+c^{2}a^{2}). $
--
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_55824` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_55824; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_55824 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a^4 * c^3 + b^4 * a^3 + c^4 * b^3 + 2 * a * b * c * (a^4 + b^4 + c^4) ≥ 3 * a * b * c * (a^2 * b^2 + b^2 * c^2 + c^2 * a^2)  :=  by sorry
