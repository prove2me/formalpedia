-- Prove2me | Theorems.Thm_WorkbookSource_base_55249
-- name    : WorkbookSource.base_55249
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T05:27:19.225596+00:00
-- url     : https://prove2.me/theorems/9b51fdee-5b13-4a9f-839e-e62be5a445d3
-- title:
--   A weighted linear ratio sum with a quadratic correction
-- statement:
--   If $a, b, c>0$ prove that
--    $\frac{2a+c}{2a+b+c}+\frac{2b+a}{2b+c+a}+\frac{2c+b}{2c+a+b}\ge 2+\frac{1}{4}\cdot\frac{ab+bc+ca}{a^2+b^2+c^2}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_55249` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_55249; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_55249 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (2 * a + c) / (2 * a + b + c) + (2 * b + a) / (2 * b + c + a) + (2 * c + b) / (2 * c + a + b) ≥ 2 + 1 / 4 * (a * b + b * c + c * a) / (a ^ 2 + b ^ 2 + c ^ 2)  :=  by sorry
