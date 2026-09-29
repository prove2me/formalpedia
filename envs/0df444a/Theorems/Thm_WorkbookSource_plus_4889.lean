-- Prove2me | Theorems.Thm_WorkbookSource_plus_4889
-- name    : WorkbookSource.plus_4889
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T09:32:30.587136+00:00
-- url     : https://prove2.me/theorems/fb14d3f1-e7c8-4a15-9b24-12dbfe8daebe
-- title:
--   A determinant square bounded by a product of sums and squared differences
-- statement:
--   Let $a,b,c,d \geq 0$ . Prove that $$(ad-bc)^2 \leq (a+b)(c+d)((a-c)^2+(b-d)^2).$$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_4889` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_4889; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_4889 (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) : (a * d - b * c) ^ 2 ≤ (a + b) * (c + d) * ((a - c) ^ 2 + (b - d) ^ 2)   :=  by sorry
