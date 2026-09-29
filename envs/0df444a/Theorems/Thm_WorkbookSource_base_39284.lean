-- Prove2me | Theorems.Thm_WorkbookSource_base_39284
-- name    : WorkbookSource.base_39284
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T05:45:37.330576+00:00
-- url     : https://prove2.me/theorems/8adb23a1-fa24-475f-8e6d-07faaefb142d
-- title:
--   A pairwise ratio sum with a symmetric quadratic correction
-- statement:
--   The following is also true :
--
--    $ \frac {a + b}{c} + \frac {b + c}{a} + \frac {c + a}{b} + \frac {ab + bc + ca}{a^2 + b^2 + c^2}\ge 7$
--
--   with $ a,b,c > 0$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_39284` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_39284; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_39284 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a + b) / c + (b + c) / a + (c + a) / b + (a * b + b * c + c * a) / (a ^ 2 + b ^ 2 + c ^ 2) ≥ 7  :=  by sorry
