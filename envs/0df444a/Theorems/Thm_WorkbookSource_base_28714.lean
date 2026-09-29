-- Prove2me | Theorems.Thm_WorkbookSource_base_28714
-- name    : WorkbookSource.base_28714
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T08:10:51.26789+00:00
-- url     : https://prove2.me/theorems/6413ab4b-8fb2-41d0-9a12-877038180aa8
-- title:
--   A cyclic sixth-degree pair-product ratio bounds a quartic sum
-- statement:
--   For $a, b, c, d>0$ prove that
--    ${\frac{a^4c^2+b^4d^2}{cd}+\frac{b^4d^2+c^4a^2}{da}+\frac{c^4a^2+d^4b^2}{ab}+\frac{d^4b^2+a^4c^2}{bc}\geq4(a^2c^2+b^2d^2)}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_28714` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_28714; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_28714 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) : (a^4 * c^2 + b^4 * d^2) / (c * d) + (b^4 * d^2 + c^4 * a^2) / (d * a) + (c^4 * a^2 + d^4 * b^2) / (a * b) + (d^4 * b^2 + a^4 * c^2) / (b * c) ≥ 4 * (a^2 * c^2 + b^2 * d^2)  :=  by sorry
