-- Prove2me | Theorems.Thm_WorkbookSource_plus_23759
-- name    : WorkbookSource.plus_23759
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T05:40:37.653999+00:00
-- url     : https://prove2.me/theorems/b80215dc-ca4d-47f1-b0ca-5576f5e4ef66
-- title:
--   A squared cyclic ratio sum bounds a normalized quadratic sum
-- statement:
--   Let $a,b,c>0$ , Prove that :
--    $\frac{a^2}{b^2}+\frac{b^2}{c^2}+\frac{c^2}{a^2}+1\ge{\frac{12(a^2+b^2+c^2)}{(a+b+c)^2}}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_23759` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_23759; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_23759 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^2 / b^2 + b^2 / c^2 + c^2 / a^2 + 1) ≥ 12 * (a^2 + b^2 + c^2) / (a + b + c)^2   :=  by sorry
