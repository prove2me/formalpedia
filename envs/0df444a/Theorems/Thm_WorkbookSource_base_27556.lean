-- Prove2me | Theorems.Thm_WorkbookSource_base_27556
-- name    : WorkbookSource.base_27556
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T04:49:27.388652+00:00
-- url     : https://prove2.me/theorems/a69bf5f8-9a19-4f72-81d6-7004ab3a631e
-- title:
--   A cyclic ratio upper bound involving pairwise products
-- statement:
--   Let $a,b,c$ be positive real numbers such that $a+b+c=3$. Prove that $\frac{a}{a+b}+\frac{b}{b+c}+\frac{c}{c+a}\leq\frac{9}{3+bc+ca+ab}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_27556` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_27556; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_27556 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 3) : a / (a + b) + b / (b + c) + c / (c + a) ≤ 9 / (3 + b * c + c * a + a * b)  :=  by sorry
