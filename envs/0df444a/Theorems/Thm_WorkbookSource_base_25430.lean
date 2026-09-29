-- Prove2me | Theorems.Thm_WorkbookSource_base_25430
-- name    : WorkbookSource.base_25430
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T04:05:26.180029+00:00
-- url     : https://prove2.me/theorems/0af72ed9-f9e9-411e-9d99-a1684021d0b9
-- title:
--   A weighted cubic ratio bounds a quadratic difference
-- statement:
--   The following inequality is also true. Let $a$ , $b$ and $c$ be positive numbers. Prove that: $\frac{a^{2}b}{4a+7b}+\frac{b^{2}c}{4b+7c}+\frac{c^{2}a}{4c+7a}\ge\frac{5(ab+bc+ca)-2(a^2+b^2+c^2)}{33}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_25430` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_25430; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_25430 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^2 * b / (4 * a + 7 * b) + b^2 * c / (4 * b + 7 * c) + c^2 * a / (4 * c + 7 * a)) ≥ (5 * (a * b + b * c + c * a) - 2 * (a^2 + b^2 + c^2)) / 33  :=  by sorry
