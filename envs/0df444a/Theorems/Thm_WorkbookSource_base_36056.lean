-- Prove2me | Theorems.Thm_WorkbookSource_base_36056
-- name    : WorkbookSource.base_36056
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T23:55:36.327051+00:00
-- url     : https://prove2.me/theorems/e0bf3ea4-d8c0-4d5d-bc52-be888c268615
-- title:
--   A cyclic quartic inequality with asymmetric coefficients
-- statement:
--   For positive real numbers $a, b, c$ prove the inequality
--    $$a^3b+b^3c+c^3a+4(ab^3+bc^3+ca^3)\geq 4(a^2b^2+b^2c^2+c^2a^2)+abc(a+b+c)$$
--
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_36056` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_36056; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_36056 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a^3 * b + b^3 * c + c^3 * a + 4 * (a * b^3 + b * c^3 + c * a^3) ≥ 4 * (a^2 * b^2 + b^2 * c^2 + c^2 * a^2) + a * b * c * (a + b + c)  :=  by sorry
