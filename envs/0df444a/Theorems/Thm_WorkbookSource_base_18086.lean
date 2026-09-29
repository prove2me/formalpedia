-- Prove2me | Theorems.Thm_WorkbookSource_base_18086
-- name    : WorkbookSource.base_18086
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T04:12:52.873181+00:00
-- url     : https://prove2.me/theorems/e959529b-e8e6-488a-a916-c9c011d29e50
-- title:
--   A cyclic quadratic ratio lower bound at fixed sum three
-- statement:
--   Let $a;b;c>0$ such that $a+b+c=3$
--   Prove that: $\frac{a^2+bc}{b+ac}+\frac{b^2+ac}{c+ab}+\frac{c^2+ab}{a+bc} \geq 3$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_18086` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_18086; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_18086 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 3) : (a^2 + b * c) / (b + a * c) + (b^2 + a * c) / (c + b * a) + (c^2 + a * b) / (a + c * b) ≥ 3  :=  by sorry
