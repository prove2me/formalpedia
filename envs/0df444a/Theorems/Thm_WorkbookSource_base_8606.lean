-- Prove2me | Theorems.Thm_WorkbookSource_base_8606
-- name    : WorkbookSource.base_8606
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T01:38:34.720358+00:00
-- url     : https://prove2.me/theorems/3c40c4f6-d7db-42a9-8a3b-44928a4e1f7b
-- title:
--   A weighted quadratic reciprocal upper bound
-- statement:
--   For $ a,b,c$ positive reals, show: $ \frac{6a}{9a^2+5(a+b+c)^2} + \frac{6b}{9b^2+5(a+b+c)^2} + \frac{6c}{9c^2+5(a+b+c)^2} \leq \frac{1}{a+b+c}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_8606` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_8606; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_8606 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (6 * a) / (9 * a ^ 2 + 5 * (a + b + c) ^ 2) + (6 * b) / (9 * b ^ 2 + 5 * (a + b + c) ^ 2) + (6 * c) / (9 * c ^ 2 + 5 * (a + b + c) ^ 2) ≤ 1 / (a + b + c)  :=  by sorry
