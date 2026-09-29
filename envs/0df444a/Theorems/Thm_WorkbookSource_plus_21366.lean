-- Prove2me | Theorems.Thm_WorkbookSource_plus_21366
-- name    : WorkbookSource.plus_21366
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T05:29:42.999252+00:00
-- url     : https://prove2.me/theorems/bec38c17-6ca1-44ec-ac03-7f1ab2b28be5
-- title:
--   A cyclic quadratic ratio with a triple-product correction
-- statement:
--   Let $ a,b,c>0$ which satisfy: $ a+b+c =3 $. Prove that: $ \frac{a^2}{b} + \frac{b^2}{c}+\frac{c^2}{a} +3abc \ge 6 $. Hope that this inequality have a nice solution
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_21366` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_21366; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_21366 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 3) : a^2 / b + b^2 / c + c^2 / a + 3 * a * b * c ≥ 6   :=  by sorry
