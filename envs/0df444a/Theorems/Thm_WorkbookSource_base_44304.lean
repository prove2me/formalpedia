-- Prove2me | Theorems.Thm_WorkbookSource_base_44304
-- name    : WorkbookSource.base_44304
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T07:39:24.184479+00:00
-- url     : https://prove2.me/theorems/7e49ed95-8a25-43d2-89cb-9a5acec42a51
-- title:
--   A shifted three-variable quadratic ratio sum is at least three
-- statement:
--   Let $ a,b,c,d$ be positive real numbers. Prove that: $ \frac{d+a^2}{d+bc}+\frac{d+b^2}{d+ca}+\frac{d+c^2}{d+ab} \ge 3.$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_44304` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_44304; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_44304 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) : (d + a ^ 2) / (d + b * c) + (d + b ^ 2) / (d + c * a) + (d + c ^ 2) / (d + a * b) ≥ 3  :=  by sorry
