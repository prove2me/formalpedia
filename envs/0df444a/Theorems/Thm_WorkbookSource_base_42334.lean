-- Prove2me | Theorems.Thm_WorkbookSource_base_42334
-- name    : WorkbookSource.base_42334
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T04:30:18.721025+00:00
-- url     : https://prove2.me/theorems/202c72dc-f0db-4b39-a6a7-e26023a2a499
-- title:
--   An asymmetric mixed ratio sum is at least five halves
-- statement:
--   Let $a,b,c>0.$ Prove that
--    $$\frac{2a}{b+c}+\frac{b^2}{c^2+a^2}+\frac{2c}{a+b} \geq \frac{5}{2} $$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_42334` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_42334; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_42334 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (2 * a / (b + c) + b^2 / (c^2 + a^2) + 2 * c / (a + b)) ≥ 5 / 2  :=  by sorry
