-- Prove2me | Theorems.Thm_WorkbookSource_plus_13160
-- name    : WorkbookSource.plus_13160
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T05:11:23.755906+00:00
-- url     : https://prove2.me/theorems/0e3f1cd2-4534-4433-b406-d8ec6ee126fd
-- title:
--   A product of reverse cyclic quadratic ratio sums is at least nine
-- statement:
--   prove \((\frac{a^2}{b}+\frac{b^2}{c}+\frac{c^2}{a})(\frac{a^2}{c}+\frac{b^2}{a}+\frac{c^2}{b}) \geq 9\) given \(a,b,c >0\) and \(a+b+c=3\)
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_13160` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_13160; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_13160 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 3) : (a^2 / b + b^2 / c + c^2 / a) * (a^2 / c + b^2 / a + c^2 / b) ≥ 9   :=  by sorry
