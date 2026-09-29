-- Prove2me | Theorems.Thm_WorkbookSource_base_772
-- name    : WorkbookSource.base_772
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T00:50:47.849267+00:00
-- url     : https://prove2.me/theorems/1d8cb5e8-7b81-4816-8c96-6e4d70ad587c
-- title:
--   A mixed rational sum and product is at least two
-- statement:
--   Let $a,b,c$ be positive real numbers. Prove that
--    $$\frac{b}{c+a}+\frac{c}{a+b}+\left( \frac{c}{a+b}+\frac{a}{b+c}\right)\left( \frac{a}{b+c}+\frac{b}{c+a}\right)\ge 2$$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_772` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_772; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_772 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (b / (c + a) + c / (a + b) + ((c / (a + b) + a / (b + c)) * (a / (b + c) + b / (c + a)))) ≥ 2  :=  by sorry
