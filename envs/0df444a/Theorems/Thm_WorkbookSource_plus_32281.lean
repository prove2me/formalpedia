-- Prove2me | Theorems.Thm_WorkbookSource_plus_32281
-- name    : WorkbookSource.plus_32281
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T13:11:30.566737+00:00
-- url     : https://prove2.me/theorems/329b93b9-cf50-486f-9dbd-dbd6771c3952
-- title:
--   A symmetric bound including zero boundary values
-- statement:
--   Let $a,b,c\ge 0$ and $a+b+c=1.$ Prove that
--    $$a^2+b^2+c^2+4abc\le 1$$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_32281` (Apache-2.0). The complete source proposition and its explicit variable declarations are preserved. This statement includes nonnegative boundary values; the related positive-variable records plus_16237 and source57253 require all three variables to be positive.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_32281; Apache-2.0

import Mathlib
open Real

theorem WorkbookSource.plus_32281 (a b c : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) (hab : a + b + c = 1) : a^2 + b^2 + c^2 + 4 * a * b * c ≤ 1   :=  by sorry
