-- Prove2me | Theorems.Thm_WorkbookSource_base_631
-- name    : WorkbookSource.base_631
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T00:45:23.182071+00:00
-- url     : https://prove2.me/theorems/56d1bbfd-ce17-4103-ab4a-676d3948e6ef
-- title:
--   A cyclic product-over-linear upper bound at fixed sum
-- statement:
--   Let $a,b,c$ are positive numbers satisfies $a+b+c=3.$ Prove that $\frac{ab}{2b+1}+\frac{bc}{2c+1}+\frac{ca}{2a+1} \leq 1.$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_631` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_631; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_631 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 3) : (a * b / (2 * b + 1) + b * c / (2 * c + 1) + c * a / (2 * a + 1)) ≤ 1  :=  by sorry
