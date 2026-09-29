-- Prove2me | Theorems.Thm_WorkbookSource_plus_50825
-- name    : WorkbookSource.plus_50825
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T13:11:55.436579+00:00
-- url     : https://prove2.me/theorems/6597b789-a479-4903-bd25-e0308cfabd05
-- title:
--   A quadratic bound with a mixed constraint
-- statement:
--   Let $a,b,c> 0$ and $a+b+c^2=4 .$ Prove that
--    $$a^2+b^2+c^2 \geq \frac{7}{2}$$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_50825` (Apache-2.0). The complete source proposition and its explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_50825; Apache-2.0

import Mathlib
open Real

theorem WorkbookSource.plus_50825 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c^2 = 4) : a^2 + b^2 + c^2 ≥ 7 / 2   :=  by sorry
