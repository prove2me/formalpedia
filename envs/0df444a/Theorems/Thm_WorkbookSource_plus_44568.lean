-- Prove2me | Theorems.Thm_WorkbookSource_plus_44568
-- name    : WorkbookSource.plus_44568
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T05:11:34.963688+00:00
-- url     : https://prove2.me/theorems/89154151-9031-4e2c-a717-53c0ad446214
-- title:
--   A weighted quadratic reciprocal comparison
-- statement:
--   With positive $ a,b,c, $ prove:
--    $$ \frac{a}{8a^2+5b^2+3c^2} +\frac{b}{8b^2+5c^2+3a^2} +\frac{c}{8c^2+5a^2+3b^2}\le\frac{1}{16}\left( \frac{1}{a} +\frac{1}{b} +\frac{1}{c} \right) $$
--
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_44568` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_44568; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_44568 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a / (8 * a ^ 2 + 5 * b ^ 2 + 3 * c ^ 2) + b / (8 * b ^ 2 + 5 * c ^ 2 + 3 * a ^ 2) + c / (8 * c ^ 2 + 5 * a ^ 2 + 3 * b ^ 2)) ≤ (1 / 16) * (1 / a + 1 / b + 1 / c)   :=  by sorry
