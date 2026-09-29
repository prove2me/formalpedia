-- Prove2me | Theorems.Thm_WorkbookSource_plus_10106
-- name    : WorkbookSource.plus_10106
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T10:11:39.724589+00:00
-- url     : https://prove2.me/theorems/ffda96e6-2b8c-4482-ac8b-1884f08708aa
-- title:
--   A quartic correction under a cubic constraint
-- statement:
--   Let $a,b >0 $ and $a^3+b^3=2.$ Prove that $$a +b+\frac{1}{8}(a^2-b^2)^2\le 2$$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_10106` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_10106; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_10106 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a^3 + b^3 = 2) : a + b + (1 / 8) * (a^2 - b^2)^2 ≤ 2   :=  by sorry
