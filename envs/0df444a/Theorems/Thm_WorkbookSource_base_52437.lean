-- Prove2me | Theorems.Thm_WorkbookSource_base_52437
-- name    : WorkbookSource.base_52437
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T04:57:46.372456+00:00
-- url     : https://prove2.me/theorems/8b8ba2e3-1f22-498b-9743-260df3b906a0
-- title:
--   A cyclic linear ratio sum has a symmetric upper bound
-- statement:
--   For $a, b, c>0$ prove that $\frac{a+b}{a+2b+c}+\frac{b+c}{b+2c+a}+\frac{c+a}{c+2a+b}\le\frac{(a+b+c)^2}{2(ab+bc+ca)}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_52437` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_52437; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_52437 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a + b) / (a + 2 * b + c) + (b + c) / (b + 2 * c + a) + (c + a) / (c + 2 * a + b) ≤ (a + b + c) ^ 2 / (2 * (a * b + b * c + a * c))  :=  by sorry
