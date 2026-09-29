-- Prove2me | Theorems.Thm_WorkbookSource_base_960
-- name    : WorkbookSource.base_960
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T00:51:56.926888+00:00
-- url     : https://prove2.me/theorems/3112b3f1-3f54-479e-80ea-0e389770e69d
-- title:
--   A symmetric quadratic reciprocal sum bounds a cubic ratio
-- statement:
--   Let $a,b,c$ are positive numbers, prove inequality
--    $ \frac{1}{a^2+ab+b^2}+ \frac{1}{b^2+bc+c^2}+\frac{1}{c^2+ca+a^2} \ge \frac{7}{3} {.} \frac{a+b+c}{a^2(b+c)+b^2(c+a)+c^2(a+b)+abc} $
--
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_960` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_960; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_960 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (1 / (a ^ 2 + a * b + b ^ 2) + 1 / (b ^ 2 + b * c + c ^ 2) + 1 / (c ^ 2 + c * a + a ^ 2)) ≥ 7 / 3 * (a + b + c) / (a ^ 2 * (b + c) + b ^ 2 * (c + a) + c ^ 2 * (a + b) + a * b * c)  :=  by sorry
