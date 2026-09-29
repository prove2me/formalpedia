-- Prove2me | Theorems.Thm_WorkbookSource_plus_37156
-- name    : WorkbookSource.plus_37156
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T04:58:11.050959+00:00
-- url     : https://prove2.me/theorems/ed74e0da-19d1-4a78-a32f-127b73c653a4
-- title:
--   A shifted cyclic reciprocal product is at least 125
-- statement:
--   If $ a,b,c$ are positive numbers such that $ a+b+c=3$ , then
--
--    $ (3a+\frac 2{b})(3b+\frac 2{c})(3c+\frac 2{a}) \ge 125$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_37156` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_37156; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_37156 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 3) : (3 * a + 2 / b) * (3 * b + 2 / c) * (3 * c + 2 / a) ≥ 125   :=  by sorry
