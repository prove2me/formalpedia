-- Prove2me | Theorems.Thm_WorkbookSource_base_33090
-- name    : WorkbookSource.base_33090
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T05:51:36.774239+00:00
-- url     : https://prove2.me/theorems/e6858c4b-51cd-4374-8edc-5d94166abded
-- title:
--   A pairwise ratio sum bounds a normalized symmetric cubic expression
-- statement:
--   If $ a,b,c>0 $ prove that:
--    $ \sum_{cyc}\frac{a}{b+c}\ge\frac{27[a^2(b+c)+b^2(c+a)+c^2(a+b)]}{4(a+b+c)^3} $
--
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_33090` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_33090; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_33090 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a / (b + c) + b / (c + a) + c / (a + b)) ≥ 27 * (a^2 * (b + c) + b^2 * (c + a) + c^2 * (a + b)) / (4 * (a + b + c)^3)  :=  by sorry
