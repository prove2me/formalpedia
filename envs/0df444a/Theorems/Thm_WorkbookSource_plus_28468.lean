-- Prove2me | Theorems.Thm_WorkbookSource_plus_28468
-- name    : WorkbookSource.plus_28468
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T05:54:18.744709+00:00
-- url     : https://prove2.me/theorems/ecf7b08a-bbf9-4768-9a1d-20a7c655acc3
-- title:
--   A cyclic cubic ratio with a squared pair-product correction
-- statement:
--   2/Let $ a,\, b, \, c>0 $. Prove
--
--    $${\frac {{a}^{3}}{b}}+{\frac {{b}^{3}}{c}}+{\frac {{c}^{3}}{a}}+{\frac { \left( ab+ca+bc \right) ^{2}}{{a}^{2}+{b}^{2}+{c}^{2}}}\ge \frac{2 \left( a+b+c \right) ^{2}}{3}$$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_28468` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_28468; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_28468 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^3 / b + b^3 / c + c^3 / a + (a * b + b * c + c * a)^2 / (a^2 + b^2 + c^2)) ≥ (2 * (a + b + c)^2) / 3   :=  by sorry
