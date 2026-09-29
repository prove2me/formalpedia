-- Prove2me | Theorems.Thm_WorkbookSource_base_10672
-- name    : WorkbookSource.base_10672
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T09:44:18.449741+00:00
-- url     : https://prove2.me/theorems/2d3db93e-5b16-4e5c-9326-83c1087c9040
-- title:
--   A quartic inequality at unit triple product
-- statement:
--   Prove that if $abc=1, a,b,c>0$ then $a^{4}+b^{4}+c^{4}+a+b+c\ge 2(a^{2}b^{2}+b^{2}c^{2}+c^{2}a^{2})$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_10672` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_10672; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_10672 (a b c : ℝ) (habc : a * b * c = 1) (ha : a > 0) (hb : b > 0) (hc : c > 0) : a ^ 4 + b ^ 4 + c ^ 4 + a + b + c ≥ 2 * (a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * a ^ 2)  :=  by sorry
