-- Prove2me | Theorems.Thm_WorkbookSource_base_16702
-- name    : WorkbookSource.base_16702
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T04:05:36.143575+00:00
-- url     : https://prove2.me/theorems/1edfaf3b-e888-46f3-8243-968f824f6074
-- title:
--   A cyclic quadratic ratio upper bound involving symmetric sums
-- statement:
--   Given $a,b,c>0$ . Prove that $\frac{a^2}{b+c}+\frac{b^2}{c+a}+\frac{c^2}{a+b}\le \frac{3(a^3+b^3+c^3)}{2(ab+bc+ca)}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_16702` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_16702; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_16702 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^2 / (b + c) + b^2 / (c + a) + c^2 / (a + b)) ≤ (3 * (a^3 + b^3 + c^3)) / (2 * (a * b + b * c + a * c))  :=  by sorry
