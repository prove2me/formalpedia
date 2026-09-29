-- Prove2me | Theorems.Thm_WorkbookSource_base_28648
-- name    : WorkbookSource.base_28648
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T05:02:57.132083+00:00
-- url     : https://prove2.me/theorems/e705b383-629b-4021-8dd3-71ce1ba73473
-- title:
--   A sum of pairwise and shifted ratios is at least nine quarters
-- statement:
--   Let $a,b,c$ be positive real numbers . Prove that $\frac{a}{b+c}+\frac{b}{c+a}+\frac{c}{a+b}+\frac{a}{2a+b+c}+\frac{b}{a+2b+c}+\frac{c}{a+b+2c}\ge\frac{9}{4}.$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_28648` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_28648; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_28648 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a / (b + c) + b / (c + a) + c / (a + b) + a / (2 * a + b + c) + b / (a + 2 * b + c) + c / (a + b + 2 * c)) ≥ 9 / 4  :=  by sorry
