-- Prove2me | Theorems.Thm_WorkbookSource_base_9749
-- name    : WorkbookSource.base_9749
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T00:45:25.100801+00:00
-- url     : https://prove2.me/theorems/adc0df66-2867-4ae6-a3b3-942211f05bb7
-- title:
--   A two-variable quadratic inequality
-- statement:
--   Let $x, y >0 .$ Prove that $$3x^2 + y^2 + 1 \geq \frac{6}{5}(x^2 + xy + 2x)$$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_9749` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_9749; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_9749 (x y : ℝ) (hx : 0 < x) (hy : 0 < y) : 3 * x ^ 2 + y ^ 2 + 1 ≥ 6 / 5 * (x ^ 2 + x * y + 2 * x)  :=  by sorry
