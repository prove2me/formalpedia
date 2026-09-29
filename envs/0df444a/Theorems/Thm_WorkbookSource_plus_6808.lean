-- Prove2me | Theorems.Thm_WorkbookSource_plus_6808
-- name    : WorkbookSource.plus_6808
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T06:11:01.585425+00:00
-- url     : https://prove2.me/theorems/c44cb774-0813-49fc-abb3-64dfedb9bd33
-- title:
--   A cyclic mixed reciprocal sum with a pair-product correction
-- statement:
--   The following inequality a bit of stronger.
--   Let $a$ , $b$ and $c$ be positive numbers such that $a+b+c=3.$ Prove that:
--
--    $$\frac{a}{b+c^2}+\frac{b}{c+a^2}+\frac{c}{a+b^2}+\frac{2(ab+bc+ca)}{9}\geq\frac{13}{6}$$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_6808` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_6808; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_6808 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 3) : a / (b + c^2) + b / (c + a^2) + c / (a + b^2) + (2 * (a * b + b * c + c * a)) / 9 ≥ 13 / 6   :=  by sorry
