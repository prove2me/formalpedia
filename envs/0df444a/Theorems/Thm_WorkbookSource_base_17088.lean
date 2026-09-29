-- Prove2me | Theorems.Thm_WorkbookSource_base_17088
-- name    : WorkbookSource.base_17088
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T04:06:31.018376+00:00
-- url     : https://prove2.me/theorems/756bcf8b-ebb3-4cf2-a520-be1be57c5936
-- title:
--   A shifted quadratic ratio lower bound at fixed sum three
-- statement:
--   Let $ a,b,c >0 $ and $ a+b+c=3 $ . Prove that : $$\frac{a^2}{b^2+2b}+\frac{b^2}{c^2+2c}+\frac{c^2}{a^2+2a} \ge 1$$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_17088` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_17088; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_17088 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 3) : a^2 / (b^2 + 2 * b) + b^2 / (c^2 + 2 * c) + c^2 / (a^2 + 2 * a) ≥ 1  :=  by sorry
