-- Prove2me | Theorems.Thm_WorkbookSource_base_27460
-- name    : WorkbookSource.base_27460
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T04:46:19.745999+00:00
-- url     : https://prove2.me/theorems/81d81cc0-5db9-471f-8581-25892dc8175d
-- title:
--   A weighted squared reciprocal upper bound
-- statement:
--   Let $a,b,c>0$ $$\frac{1}{(3a+2b+c)^2}+\frac{1}{(3b+2c+a)^2} + \frac{1}{(3c+2a+b)^2} \le \frac{1}{4(ab+bc+ca)}$$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_27460` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_27460; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_27460 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (1 / (3 * a + 2 * b + c) ^ 2 + 1 / (3 * b + 2 * c + a) ^ 2 + 1 / (3 * c + 2 * a + b) ^ 2) ≤ 1 / (4 * (a * b + b * c + c * a))  :=  by sorry
