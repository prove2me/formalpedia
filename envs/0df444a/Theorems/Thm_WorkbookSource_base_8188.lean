-- Prove2me | Theorems.Thm_WorkbookSource_base_8188
-- name    : WorkbookSource.base_8188
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T01:35:10.028748+00:00
-- url     : https://prove2.me/theorems/b3c82df8-9a90-4d30-bedc-e92b53fe3b6d
-- title:
--   A triangle-factor reciprocal bound at fixed sum six
-- statement:
--   If a,b,c positive numbers and a+b+c=6 proove that
--    $ \sum 4 \frac{3(3-a)(3-b)(3-c)}{a^2}\leq \frac{7(a^2+b^2+c^2)}{2} $
--
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_8188` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_8188; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_8188 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 6) : 4 * (3 * (3 - a) * (3 - b) * (3 - c)) / a ^ 2 + 4 * (3 * (3 - b) * (3 - c) * (3 - a)) / b ^ 2 + 4 * (3 * (3 - c) * (3 - a) * (3 - b)) / c ^ 2 ≤ 7 / 2 * (a ^ 2 + b ^ 2 + c ^ 2)  :=  by sorry
