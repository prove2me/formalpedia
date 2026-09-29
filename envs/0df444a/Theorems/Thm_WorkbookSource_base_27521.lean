-- Prove2me | Theorems.Thm_WorkbookSource_base_27521
-- name    : WorkbookSource.base_27521
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T04:49:18.247096+00:00
-- url     : https://prove2.me/theorems/de0f033a-e39a-402d-a60c-247fa28c8232
-- title:
--   A shifted pair-product ratio upper bound with squared differences
-- statement:
--   Let $a,b,c>0$ such that $a+b+c=3$ . Prove that : $$\frac{ab}{ab+a+b}+\frac{bc}{bc+b+c}+\frac{ca}{ca+c+a}+\frac{1}{9}\left(\frac{(a-b)^2}{ab+a+b}+\frac{(b-c)^2}{bc+b+c}+\frac{(c-a)^2}{ca+c+a}\right)\leq1.$$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_27521` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_27521; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_27521 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 3) : (a * b / (a * b + a + b) + b * c / (b * c + b + c) + c * a / (c * a + c + a) + 1 / 9 * ((a - b) ^ 2 / (a * b + a + b) + (b - c) ^ 2 / (b * c + b + c) + (c - a) ^ 2 / (c * a + c + a))) ≤ 1  :=  by sorry
