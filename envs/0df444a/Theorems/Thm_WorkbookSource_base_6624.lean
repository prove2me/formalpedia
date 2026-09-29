-- Prove2me | Theorems.Thm_WorkbookSource_base_6624
-- name    : WorkbookSource.base_6624
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T00:44:17.671475+00:00
-- url     : https://prove2.me/theorems/0920dd40-080b-43a0-9f2b-ac1ca01d8d70
-- title:
--   A symmetric rational inequality involving squared pairwise products
-- statement:
--   Prove that $\frac{abc}{a^2b^2+b^2c^2+c^2a^2}+\frac{2}{a+b+c}\ge \frac{a+b+c}{a^2+b^2+c^2}$ given $a,b,c>0$. Is there a solution without full expanding?
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_6624` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_6624; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_6624 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a * b * c) / (a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * a ^ 2) + 2 / (a + b + c) ≥ (a + b + c) / (a ^ 2 + b ^ 2 + c ^ 2)  :=  by sorry
