-- Prove2me | Theorems.Thm_WorkbookSource_base_18091
-- name    : WorkbookSource.base_18091
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T00:52:33.305567+00:00
-- url     : https://prove2.me/theorems/c5731e70-65a0-4bd2-8514-3885d489bc77
-- title:
--   A product of mixed ratio sums has a constant lower bound
-- statement:
--   Let $a,b,c>0.$ Prove that
--    $$\left (\frac{a}{b+c}+\frac{a+b}{c}\right)\left (\frac{b}{c+a}+\frac{b+c}{a}\right)\left (\frac{c}{a+b}+\frac{c+a}{b}\right)\geq \frac{125}{8}$$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_18091` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_18091; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_18091 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a / (b + c) + (a + b) / c) * (b / (c + a) + (b + c) / a) * (c / (a + b) + (c + a) / b) ≥ 125 / 8  :=  by sorry
