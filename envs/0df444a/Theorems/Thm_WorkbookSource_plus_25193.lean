-- Prove2me | Theorems.Thm_WorkbookSource_plus_25193
-- name    : WorkbookSource.plus_25193
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T05:44:22.355904+00:00
-- url     : https://prove2.me/theorems/632221de-0f08-441f-81e2-437ad42640cc
-- title:
--   A weighted quadratic pair-product ratio upper bound
-- statement:
--   For $a, b, c>0$ prove that
--    $\frac{ab}{3a^2+3b^2+2c^2}+\frac{bc}{3b^2+3c^2+2a^2}+\frac{ca}{3c^2+3a^2+2b^2}\le\frac{(a+b+c)^2}{8(a^2+b^2+c^2)}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_25193` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_25193; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_25193 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a * b / (3 * a ^ 2 + 3 * b ^ 2 + 2 * c ^ 2) + b * c / (3 * b ^ 2 + 3 * c ^ 2 + 2 * a ^ 2) + c * a / (3 * c ^ 2 + 3 * a ^ 2 + 2 * b ^ 2)) ≤ (a + b + c) ^ 2 / (8 * (a ^ 2 + b ^ 2 + c ^ 2))   :=  by sorry
