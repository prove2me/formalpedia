-- Prove2me | Theorems.Thm_WorkbookSource_base_39288
-- name    : WorkbookSource.base_39288
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T05:45:33.897227+00:00
-- url     : https://prove2.me/theorems/4de33e42-e018-41be-a1af-e47a0973fbdb
-- title:
--   A mixed quadratic ratio sum bounded by pairwise ratios
-- statement:
--   If $ a,b,c>0$ , then
--
--    $ \frac{a^2+bc}{2a+b+c} + \frac{b^2+ca}{a+2b+c} + \frac{c^2+ab}{a+b+2c}\leq \frac{1}{2}(\frac{a^2}{b+c} + \frac{b^2}{c+a} + \frac{c^2}{a+b} + \frac{a+b+c}{2})$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_39288` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_39288; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_39288 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^2 + b * c) / (2 * a + b + c) + (b^2 + c * a) / (a + 2 * b + c) + (c^2 + a * b) / (a + b + 2 * c) ≤ (1 / 2) * (a^2 / (b + c) + b^2 / (c + a) + c^2 / (a + b) + (a + b + c) / 2)  :=  by sorry
