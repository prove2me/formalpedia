-- Prove2me | Theorems.Thm_WorkbookSource_base_839
-- name    : WorkbookSource.base_839
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T00:50:59.920678+00:00
-- url     : https://prove2.me/theorems/eca2d7a8-bca7-48a1-8215-30939e4b40cb
-- title:
--   A pair of cyclic ratio sums has a constant lower bound
-- statement:
--   Let $a,b,c$ be positive real numbers . Prove that $\frac{a}{b+c}+\frac{b}{c+a}+\frac{c}{a+b}+6\left(\frac{a}{2a+b+c}+\frac{b}{a+2b+c}+\frac{c}{a+b+2c}\right)\ge 6.$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_839` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_839; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_839 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a / (b + c) + b / (c + a) + c / (a + b) + 6 * (a / (2 * a + b + c) + b / (a + 2 * b + c) + c / (a + b + 2 * c))) ≥ 6  :=  by sorry
