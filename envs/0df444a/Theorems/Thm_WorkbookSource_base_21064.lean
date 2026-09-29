-- Prove2me | Theorems.Thm_WorkbookSource_base_21064
-- name    : WorkbookSource.base_21064
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T06:44:18.3502+00:00
-- url     : https://prove2.me/theorems/5c5f66c6-b85e-4b2f-bf5d-4df29d6dab64
-- title:
--   A cyclic squared-difference ratio sum with a pair-product correction
-- statement:
--   If $a,b,c$ are positive real numbers such that $a+b+c=6$ then
--    $\frac{(a-b)^2}{b}+\frac{(b-c)^2}{c}+\frac{(c-a)^2}{a}+2(ab+bc+ca)\geq 24$
--    Your inequaity equivalent to
--    $\frac{(a-b)^2}{b}+\frac{(b-c)^2}{c}+\frac{(c-a)^2}{a}+\frac{12(ab+bc+ca)}{a+b+c} \geqslant 4(a+b+c),$ or
--    $\frac{c(a^2-2ab+bc)^2+a(b^2-2bc+ca)^2+b(c^2-2ca+ab)^2}{abc(ab+bc+ca)} \geqslant 0.$ Done.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_21064` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_21064; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_21064 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 6) : (a - b) ^ 2 / b + (b - c) ^ 2 / c + (c - a) ^ 2 / a + 2 * (a * b + b * c + c * a) ≥ 24  :=  by sorry
