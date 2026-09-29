-- Prove2me | Theorems.Thm_WorkbookSource_plus_7401
-- name    : WorkbookSource.plus_7401
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T10:11:36.169385+00:00
-- url     : https://prove2.me/theorems/07ab9b5d-f7f8-4ce4-95bd-c991f5862714
-- title:
--   A cubic lower bound with a mixed quadratic constraint
-- statement:
--   Let $a,b,c> 0$ and $a+b^2+c^2=4 .$ Prove that
--    $$a+b^2+c^3 \geq \frac{104}{27}$$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_7401` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_7401; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_7401 (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (habc : a + b^2 + c^2 = 4) : a + b^2 + c^3 ≥ 104 / 27   :=  by sorry
