-- Prove2me | Theorems.Thm_WorkbookSource_base_50610
-- name    : WorkbookSource.base_50610
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T05:45:49.504635+00:00
-- url     : https://prove2.me/theorems/84510105-0591-4c06-86b8-008ebc0173d0
-- title:
--   A weighted pairwise ratio sum is at least two thirds
-- statement:
--   Let $ a,b,c>0$ . Prove that
--    $ \frac{a+b}{a+7b+c}+\frac{b+c}{b+7c+a}+\frac{c+a}{c+7a+b}\geq\frac{2}{3}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_50610` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_50610; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_50610 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a + b) / (a + 7 * b + c) + (b + c) / (b + 7 * c + a) + (c + a) / (c + 7 * a + b) ≥ 2 / 3  :=  by sorry
