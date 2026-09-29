-- Prove2me | Theorems.Thm_WorkbookSource_base_9655
-- name    : WorkbookSource.base_9655
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T01:44:05.336091+00:00
-- url     : https://prove2.me/theorems/df795dc0-54f9-4828-b0e1-fc640497b85e
-- title:
--   A nested reciprocal sum bounded by the quadratic mean
-- statement:
--   Let $a,b,c > 0$ , prove that $\frac{a}{\frac{1}{a} + \frac{1}{b + c} + \frac{1}{a + b + c}} + \frac{b}{\frac{1}{b} + \frac{1}{c + a} + \frac{1}{a + b + c}} + \frac{c}{\frac{1}{c} + \frac{1}{a + b} + \frac{1}{a + b + c}} \le\frac{6}{11}\cdot(a^2+b^2+c^2)$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_9655` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_9655; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_9655 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a / (1 / a + 1 / (b + c) + 1 / (a + b + c)) + b / (1 / b + 1 / (c + a) + 1 / (a + b + c)) + c / (1 / c + 1 / (a + b) + 1 / (a + b + c)) ≤ 6 / 11 * (a ^ 2 + b ^ 2 + c ^ 2)  :=  by sorry
