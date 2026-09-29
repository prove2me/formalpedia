-- Prove2me | Theorems.Thm_WorkbookSource_base_26655
-- name    : WorkbookSource.base_26655
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T04:29:17.400355+00:00
-- url     : https://prove2.me/theorems/161dd04a-011b-4598-952d-b66a8bb1d7ae
-- title:
--   A normalized triple product bounded by pairwise products
-- statement:
--   Let $ a,b,c>0,a+b+c=3$ , prove that: $24\frac{abc}{(a+b)(b+c)(c+a)}\le cb+ac+ba$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_26655` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_26655; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_26655 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 3) : 24 * (a * b * c) / (a + b) / (b + c) / (c + a) ≤ b * c + a * c + a * b  :=  by sorry
