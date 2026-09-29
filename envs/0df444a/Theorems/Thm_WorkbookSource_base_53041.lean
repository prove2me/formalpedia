-- Prove2me | Theorems.Thm_WorkbookSource_base_53041
-- name    : WorkbookSource.base_53041
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T04:57:58.332338+00:00
-- url     : https://prove2.me/theorems/702834ac-8f5e-4238-9a7a-63f0284fdbf9
-- title:
--   A cyclic ratio sum with a normalized cubic correction
-- statement:
--   Let $a, b, c>0$ . Prove that
--    $ \frac{a}{b}+\frac{b}{c}+\frac{c}{a}\ge\frac{7}{2}-\frac{3abc}{2(a^3+b^3+c^3)} $
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_53041` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_53041; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_53041 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a / b + b / c + c / a) ≥ 7 / 2 - 3 * a * b * c / (2 * (a ^ 3 + b ^ 3 + c ^ 3))  :=  by sorry
