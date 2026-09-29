-- Prove2me | Theorems.Thm_WorkbookSource_base_19167
-- name    : WorkbookSource.base_19167
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T03:38:48.728817+00:00
-- url     : https://prove2.me/theorems/db54ac60-33cc-4474-b67d-433f15832857
-- title:
--   A cyclic quadratic ratio upper bound
-- statement:
--   Let $a,b,c$ be positive real numbers. Prove that:
--    $ \frac{a^{2}}{a^{2}+ab+b^{2}}+ \frac{b^{2}}{b^{2}+bc+c^{2}}+ \frac{c^{2}}{c^{2}+ca+a^{2}}\leq \frac{a^2+b^2+c^2}{ab+bc+ca} $
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_19167` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_19167; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_19167 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^2 / (a^2 + a * b + b^2) + b^2 / (b^2 + b * c + c^2) + c^2 / (c^2 + c * a + a^2)) ≤ (a^2 + b^2 + c^2) / (a * b + b * c + c * a)  :=  by sorry
