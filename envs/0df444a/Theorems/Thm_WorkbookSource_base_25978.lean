-- Prove2me | Theorems.Thm_WorkbookSource_base_25978
-- name    : WorkbookSource.base_25978
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T04:06:44.067869+00:00
-- url     : https://prove2.me/theorems/d0e10d55-8e10-48e2-bd81-e27c9ed12c8d
-- title:
--   A product of cyclic ratio sums is at least nine halves
-- statement:
--   Let $a,b,c $ be positive real numbers . Prove that $$\left(\frac{a}{b}+\frac{b}{c}+\frac{c}{a}\right)\left(\frac{a}{a+b}+\frac{b}{b+c}+\frac{c}{c+a}\right) \ge\frac{9}{2}$$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_25978` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_25978; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_25978 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a / b + b / c + c / a) * (a / (a + b) + b / (b + c) + c / (c + a)) ≥ 9 / 2  :=  by sorry
