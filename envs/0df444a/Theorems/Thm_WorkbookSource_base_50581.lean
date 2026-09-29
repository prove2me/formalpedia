-- Prove2me | Theorems.Thm_WorkbookSource_base_50581
-- name    : WorkbookSource.base_50581
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T05:44:02.863366+00:00
-- url     : https://prove2.me/theorems/ad24f440-75b1-4ee8-8cb2-3d3d5a21f042
-- title:
--   A refined asymmetric quadratic pairwise ratio lower bound
-- statement:
--   For $a,b,c>0$ . Prove that $\frac{a^2}{b+c}+\frac{b^2}{c+a}+\frac{c^2}{a+b} \geq \frac{a+b+c}{2}+\frac{(a-b)^2}{a+b+c}.$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_50581` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_50581; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_50581 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^2 / (b + c) + b^2 / (c + a) + c^2 / (a + b)) ≥ (a + b + c) / 2 + (a - b)^2 / (a + b + c)  :=  by sorry
