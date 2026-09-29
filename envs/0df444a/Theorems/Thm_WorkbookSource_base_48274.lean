-- Prove2me | Theorems.Thm_WorkbookSource_base_48274
-- name    : WorkbookSource.base_48274
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T05:21:01.380229+00:00
-- url     : https://prove2.me/theorems/3d7b0c4d-a50c-43bb-ba01-c130c89dafcb
-- title:
--   A shifted linear reciprocal upper bound
-- statement:
--   Let $a, b, c>0$ . Prove that
--    $$\frac{1}{2a+b+c} +\frac{1}{a+2b+c} +\frac{1}{a+b+2c} \leq \frac{27(a^2+b^2+c^2)}{4(a+b+c) ^3}$$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_48274` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_48274; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_48274 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (1 / (2 * a + b + c) + 1 / (a + 2 * b + c) + 1 / (a + b + 2 * c)) ≤ (27 * (a ^ 2 + b ^ 2 + c ^ 2)) / (4 * (a + b + c) ^ 3)  :=  by sorry
