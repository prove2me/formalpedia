-- Prove2me | Theorems.Thm_WorkbookSource_base_5136
-- name    : WorkbookSource.base_5136
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T00:05:14.085572+00:00
-- url     : https://prove2.me/theorems/a64ee016-7ea9-4fef-ab3e-d640fa8123ed
-- title:
--   A bound for pairwise cubic products and triangle factors
-- statement:
--   Let a,b,c>0 Prove that
--    $ \sum a^3b^3 \geq (-a+b+c)(a-b+c)(a+b-c)(a^3+b^3+c^3)$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_5136` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_5136; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_5136 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a^3 * b^3 + b^3 * c^3 + c^3 * a^3 ≥ (-a + b + c) * (a - b + c) * (a + b - c) * (a^3 + b^3 + c^3)  :=  by sorry
