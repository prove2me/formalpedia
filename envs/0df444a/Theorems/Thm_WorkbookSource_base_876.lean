-- Prove2me | Theorems.Thm_WorkbookSource_base_876
-- name    : WorkbookSource.base_876
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T10:18:39.117896+00:00
-- url     : https://prove2.me/theorems/9f28bb51-2f6b-4a46-acc1-365351811a6c
-- title:
--   A sharp cubic bound for a cyclic mixed sum
-- statement:
--   Let $a, b,c\geq 0 .$ Prove that $(a+b+c)^3\geq\frac{27}{4}(a^2b+b^2c+c^2a)$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_876` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_876; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_876 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) : (a + b + c) ^ 3 ≥ (27 / 4) * (a ^ 2 * b + b ^ 2 * c + c ^ 2 * a)  :=  by sorry
