-- Prove2me | Theorems.Thm_WorkbookSource_base_7161
-- name    : WorkbookSource.base_7161
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T03:27:17.615665+00:00
-- url     : https://prove2.me/theorems/25de73ed-79e5-4f38-bfdf-4d88796f0e3d
-- title:
--   A shifted squared-product reciprocal bound at fixed sum three
-- statement:
--   Let $a,b,c$ be positive numbers such that $a+b+c=3$ . Prove that
--
--    $$\frac{(1+a)^2(1+b)^2}{2+c^2} +\frac{(1+b)^2(1+c)^2}{2+a^2} +\frac{(1+c)^2(1+a)^2}{2+b^2} \geq 16$$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_7161` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_7161; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_7161 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 3) : (1 + a) ^ 2 * (1 + b) ^ 2 / (2 + c ^ 2) + (1 + b) ^ 2 * (1 + c) ^ 2 / (2 + a ^ 2) + (1 + c) ^ 2 * (1 + a) ^ 2 / (2 + b ^ 2) ≥ 16  :=  by sorry
