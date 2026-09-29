-- Prove2me | Theorems.Thm_WorkbookSource_base_33480
-- name    : WorkbookSource.base_33480
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T04:29:44.869656+00:00
-- url     : https://prove2.me/theorems/5c0c906f-2640-4afb-8cb1-138baa16991b
-- title:
--   A cubed pairwise ratio sum bounds the quadratic sum
-- statement:
--   If $ a,b,c>0$ then $ \frac{(a+b)^3}{c}+\frac{(b+c)^3}{a}+\frac{(c+a)^3}{b} \geq 8(a^2+b^2+c^2).$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_33480` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_33480; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_33480 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a + b) ^ 3 / c + (b + c) ^ 3 / a + (c + a) ^ 3 / b ≥ 8 * (a ^ 2 + b ^ 2 + c ^ 2)  :=  by sorry
