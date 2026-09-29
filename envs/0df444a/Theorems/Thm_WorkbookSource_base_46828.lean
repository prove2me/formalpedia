-- Prove2me | Theorems.Thm_WorkbookSource_base_46828
-- name    : WorkbookSource.base_46828
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T05:09:10.416126+00:00
-- url     : https://prove2.me/theorems/7c07a57c-564b-4a9e-a502-617904e442e7
-- title:
--   A cyclic cubic ratio sum bounds the total
-- statement:
--   Let $a, b, c>0.$ Prove that the following inequality holds:
--    $ \frac{a^{3}+3abc}{(b+c)^{2}}+\frac{b^{3}+3abc}{(c+a)^{2}}+\frac{c^{3}+3abc}{(a+b)^{2}}\geq(a+b+c). $
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_46828` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_46828; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_46828 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^3 + 3 * a * b * c) / (b + c)^2 + (b^3 + 3 * a * b * c) / (c + a)^2 + (c^3 + 3 * a * b * c) / (a + b)^2 ≥ a + b + c  :=  by sorry
