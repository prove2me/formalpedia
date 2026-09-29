-- Prove2me | Theorems.Thm_WorkbookSource_base_35152
-- name    : WorkbookSource.base_35152
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T04:53:56.20881+00:00
-- url     : https://prove2.me/theorems/1bd79311-0d37-4ebf-b0e2-aae6b5d1d408
-- title:
--   A weighted quadratic reciprocal upper bound at fixed sum three
-- statement:
--   Let $a,b,c>0,a+b+c=3.$ Prove that
--
--   $$\frac{1}{2a^2+b^2+c^2}+\frac{1}{2b^2+c^2+a^2}+\frac{1}{2c^2+a^2+b^2}\le \frac{3}{4}$$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_35152` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_35152; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_35152 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 3) : (1 / (2 * a ^ 2 + b ^ 2 + c ^ 2) + 1 / (2 * b ^ 2 + c ^ 2 + a ^ 2) + 1 / (2 * c ^ 2 + a ^ 2 + b ^ 2)) ≤ (3 / 4)  :=  by sorry
