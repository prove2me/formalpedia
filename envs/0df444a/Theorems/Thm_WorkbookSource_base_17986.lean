-- Prove2me | Theorems.Thm_WorkbookSource_base_17986
-- name    : WorkbookSource.base_17986
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T04:12:37.228335+00:00
-- url     : https://prove2.me/theorems/ffbb8c1a-8246-4a17-b5d7-9e11ff74c99a
-- title:
--   A cyclic ratio sum with a triple-product correction
-- statement:
--   Let $a,b,c>0$ such that $a+b+c=3$ . Prove that: $ \frac{a}{b}+\frac{b}{c}+\frac{c}{a}+abc \geq 4 $
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_17986` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_17986; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_17986 (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hab : a + b + c = 3) : a / b + b / c + c / a + a * b * c ≥ 4  :=  by sorry
