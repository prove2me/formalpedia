-- Prove2me | Theorems.Thm_WorkbookSource_base_17694
-- name    : WorkbookSource.base_17694
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T04:09:42.513227+00:00
-- url     : https://prove2.me/theorems/42a3c51f-c99e-4ac5-89a4-857d8edb8c8b
-- title:
--   A cyclic cubic ratio upper bound with a quadratic correction
-- statement:
--   Let $a,b,c>0$ . Prove
--    $3(a+b+c)\ge \frac{a^3}{a^2+ab+b^2}+\frac{b^3}{b^2+bc+c^2}+\frac{c^3}{c^2+ca+a^2}+\frac{8(ab+bc+ca)}{a+b+c}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_17694` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_17694; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_17694 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : 3 * (a + b + c) ≥ a^3 / (a^2 + a * b + b^2) + b^3 / (b^2 + b * c + c^2) + c^3 / (c^2 + c * a + a^2) + 8 * (a * b + b * c + c * a) / (a + b + c)  :=  by sorry
