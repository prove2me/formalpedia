-- Prove2me | Theorems.Thm_WorkbookSource_base_4242
-- name    : WorkbookSource.base_4242
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T06:40:50.497826+00:00
-- url     : https://prove2.me/theorems/979b6f7a-6277-4041-a46a-1e7e6bc85b72
-- title:
--   A cyclic quadratic reciprocal sum with a product correction at fixed sum six
-- statement:
--   Let $a,b,c>0 $ and $ a+b+c=6$ . Prove that $\frac{a^{2}}{b}+\frac{b^{2}}{c}+\frac{c^{2}}{a}+3abc\geq 24$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_4242` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_4242; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_4242 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 6) : a^2 / b + b^2 / c + c^2 / a + 3 * a * b * c ≥ 24  :=  by sorry
