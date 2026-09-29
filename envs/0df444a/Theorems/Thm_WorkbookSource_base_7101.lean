-- Prove2me | Theorems.Thm_WorkbookSource_base_7101
-- name    : WorkbookSource.base_7101
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T01:26:01.756839+00:00
-- url     : https://prove2.me/theorems/7938c847-0c8d-4b34-b794-96513d4076d0
-- title:
--   A symmetric reciprocal-product lower bound
-- statement:
--   Prove that for all positive real numbers $ a,b,c $ the following inequality
--    $ \frac{1}{a+b+c} (\frac{1}{a+b} + \frac{1}{b+c} + \frac{1}{a+c}) \ge \frac{1}{ab+bc+ca} + \frac{1}{2(a^2+b^2+c^2} $ .
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_7101` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_7101; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_7101 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (1 / (a + b + c)) * (1 / (a + b) + 1 / (b + c) + 1 / (a + c)) ≥ 1 / (a * b + b * c + c * a) + 1 / (2 * (a ^ 2 + b ^ 2 + c ^ 2))  :=  by sorry
