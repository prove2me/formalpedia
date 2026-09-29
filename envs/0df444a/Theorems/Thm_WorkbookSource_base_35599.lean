-- Prove2me | Theorems.Thm_WorkbookSource_base_35599
-- name    : WorkbookSource.base_35599
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T05:04:05.01817+00:00
-- url     : https://prove2.me/theorems/88dece22-7519-402e-a5da-187b07e762e3
-- title:
--   An asymmetric reciprocal comparison
-- statement:
--   Let $a,b,c>0$ . Prove that
--    $$\frac{1}{a} + \frac{2}{b} + \frac{2}{c} \ge 2\left( \frac{1}{a + b} + \frac{3}{b + c}+ \frac{1}{c + a} \right)$$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_35599` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_35599; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_35599 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : 1 / a + 2 / b + 2 / c ≥ 2 * (1 / (a + b) + 3 / (b + c) + 1 / (c + a))  :=  by sorry
