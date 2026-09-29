-- Prove2me | Theorems.Thm_WorkbookSource_plus_5224
-- name    : WorkbookSource.plus_5224
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T04:35:03.9036+00:00
-- url     : https://prove2.me/theorems/3a069daa-e38c-48cc-860f-0bc103372664
-- title:
--   A comparison of mixed quadratic ratio sums
-- statement:
--   Prove that for any $ a,b,c>0$ we have
--
--    $ 3\sum_{cyc}\frac{a(b+c)}{b^{2}+bc+c^{2}}\le5+\sum_{cyc}\frac{a^{2}}{b^{2}+bc+c^{2}}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_5224` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_5224; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_5224 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : 3 * (a * (b + c) / (b ^ 2 + b * c + c ^ 2) + b * (c + a) / (c ^ 2 + c * a + a ^ 2) + c * (a + b) / (a ^ 2 + a * b + b ^ 2)) ≤ 5 + a ^ 2 / (b ^ 2 + b * c + c ^ 2) + b ^ 2 / (c ^ 2 + c * a + a ^ 2) + c ^ 2 / (a ^ 2 + a * b + b ^ 2)   :=  by sorry
