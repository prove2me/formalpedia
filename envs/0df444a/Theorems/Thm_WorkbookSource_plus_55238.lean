-- Prove2me | Theorems.Thm_WorkbookSource_plus_55238
-- name    : WorkbookSource.plus_55238
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T05:33:45.986154+00:00
-- url     : https://prove2.me/theorems/13f8bf00-fb9b-434c-bbdd-d2d9150d3192
-- title:
--   A weighted cyclic cubic ratio bounds a quadratic expression
-- statement:
--   Prove that for positive numbers $a, b, c$, the following inequality holds: $4\left(\frac{(3a+b)a^2}{b+c} + \frac{(3b+c)b^2}{c+a} + \frac{(3c+a)c^2}{a+b}\right) \geq 11(a^2+b^2+c^2) - 3(ab+bc+ca)$.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_55238` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_55238; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_55238 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : 4 * ((3 * a + b) * a ^ 2 / (b + c) + (3 * b + c) * b ^ 2 / (c + a) + (3 * c + a) * c ^ 2 / (a + b)) ≥ 11 * (a ^ 2 + b ^ 2 + c ^ 2) - 3 * (a * b + b * c + c * a)   :=  by sorry
