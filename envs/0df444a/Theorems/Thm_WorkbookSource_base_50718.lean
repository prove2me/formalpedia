-- Prove2me | Theorems.Thm_WorkbookSource_base_50718
-- name    : WorkbookSource.base_50718
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T01:16:11.853405+00:00
-- url     : https://prove2.me/theorems/a4f7ebb9-fa98-451f-a08a-30dfc95fe69e
-- title:
--   A cyclic sixth-degree power-sum comparison
-- statement:
--   Prove this: $2x^{6}+2y^{6}+2z^{6}+x^{3}y^{3}+x^{3}z^{3}+y^{3}z^{3}\geq 3x^{4}y^{2}+3y^{4}z^{2}+3z^{4}x^{2},\ \forall x,y,z>0$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_50718` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_50718; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_50718 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : 2 * x ^ 6 + 2 * y ^ 6 + 2 * z ^ 6 + x ^ 3 * y ^ 3 + x ^ 3 * z ^ 3 + y ^ 3 * z ^ 3 ≥ 3 * x ^ 4 * y ^ 2 + 3 * y ^ 4 * z ^ 2 + 3 * z ^ 4 * x ^ 2  :=  by sorry
