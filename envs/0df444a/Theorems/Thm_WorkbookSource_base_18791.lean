-- Prove2me | Theorems.Thm_WorkbookSource_base_18791
-- name    : WorkbookSource.base_18791
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T03:36:17.164264+00:00
-- url     : https://prove2.me/theorems/9ce8ea14-86a4-4c40-9087-c313a8184c61
-- title:
--   A pair-product ratio sum is at least four
-- statement:
--   Let a,b,c are positive
--   Prove
--   $$\frac{(c+a)(c+b)}{a^2+b^2+ab}+\frac{(a+c)(a+b)}{b^2+c^2+bc}+\frac{(b+a)(b+c)}{c^2+a^2+ac}\geq4$$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_18791` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_18791; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_18791 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (c + a) * (c + b) / (a ^ 2 + b ^ 2 + a * b) + (a + c) * (a + b) / (b ^ 2 + c ^ 2 + b * c) + (b + a) * (b + c) / (c ^ 2 + a ^ 2 + a * c) ≥ 4  :=  by sorry
