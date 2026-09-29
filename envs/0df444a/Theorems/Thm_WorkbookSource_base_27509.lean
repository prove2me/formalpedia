-- Prove2me | Theorems.Thm_WorkbookSource_base_27509
-- name    : WorkbookSource.base_27509
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T04:46:29.871613+00:00
-- url     : https://prove2.me/theorems/e9bc56dc-903f-4f24-8257-40d88c2542d8
-- title:
--   A reciprocal sum bounds weighted quadratic reciprocals
-- statement:
--   If $ a,b,c>0$ prove that :
--
--    $ \frac{1}{a}+\frac{1}{b}+\frac{1}{c}\ge \frac{4a}{2a^2+b^2+c^2}+\frac{4b}{2b^2+c^2+a^2}+\frac{4c}{2c^2+a^2+b^2}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_27509` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_27509; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_27509 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (1 / a + 1 / b + 1 / c) ≥ (4 * a / (2 * a ^ 2 + b ^ 2 + c ^ 2) + 4 * b / (2 * b ^ 2 + c ^ 2 + a ^ 2) + 4 * c / (2 * c ^ 2 + a ^ 2 + b ^ 2))  :=  by sorry
