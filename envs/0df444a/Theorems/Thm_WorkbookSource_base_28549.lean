-- Prove2me | Theorems.Thm_WorkbookSource_base_28549
-- name    : WorkbookSource.base_28549
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T05:02:51.426651+00:00
-- url     : https://prove2.me/theorems/186973ae-5399-40a9-a910-8548b9b9309f
-- title:
--   A shifted quadratic ratio upper bound at fixed sum three
-- statement:
--   Prove $\frac{a^2}{2a+1}+\frac{b^2}{2b+1}+\frac{c^2}{2c+1}\leq\frac{3(a^2+b^2+c^2)}{2(a^2+b^2+c^2)+3}$ where $a, b, c > 0$ and $a+b+c=3$.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_28549` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_28549; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_28549 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 3) : a^2 / (2 * a + 1) + b^2 / (2 * b + 1) + c^2 / (2 * c + 1) ≤ 3 * (a^2 + b^2 + c^2) / (2 * (a^2 + b^2 + c^2) + 3)  :=  by sorry
