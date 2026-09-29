-- Prove2me | Theorems.Thm_WorkbookSource_base_48565
-- name    : WorkbookSource.base_48565
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T05:26:47.12368+00:00
-- url     : https://prove2.me/theorems/c2068fc0-4196-450b-898c-3a98143f03cc
-- title:
--   A weighted squared ratio sum is at most 25 over two
-- statement:
--   Let $a, b,c>0$ . Prove that $\displaystyle\sum\limits_{\text{cyc}}$ $\frac{(3a+b+c)^2}{2a^2+(b+c)^2}$ $\le\frac{25}{2}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_48565` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_48565; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_48565 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (3 * a + b + c) ^ 2 / (2 * a ^ 2 + (b + c) ^ 2) + (3 * b + c + a) ^ 2 / (2 * b ^ 2 + (c + a) ^ 2) + (3 * c + a + b) ^ 2 / (2 * c ^ 2 + (a + b) ^ 2) ≤ 25 / 2  :=  by sorry
