-- Prove2me | Theorems.Thm_WorkbookSource_base_34270
-- name    : WorkbookSource.base_34270
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T04:47:10.14089+00:00
-- url     : https://prove2.me/theorems/0ecf26c2-ba44-4b8d-81ed-faf99523ea7e
-- title:
--   A shifted mixed quadratic ratio upper bound at fixed sum three
-- statement:
--   Let $a,b,c$ be positive reals such that $a+b+c=3.$ Prove that $\frac{a}{a^2+bc+1}+\frac{b}{b^2+ca+1}+\frac{c}{c^2+ab+1} \le 1$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_34270` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_34270; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_34270 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 3) : a / (a ^ 2 + b * c + 1) + b / (b ^ 2 + c * a + 1) + c / (c ^ 2 + a * b + 1) ≤ 1  :=  by sorry
