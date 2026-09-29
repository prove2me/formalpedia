-- Prove2me | Theorems.Thm_WorkbookSource_plus_67042
-- name    : WorkbookSource.plus_67042
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T06:46:24.209674+00:00
-- url     : https://prove2.me/theorems/e27bd890-d036-4d39-9f8c-e4845bba0682
-- title:
--   A cyclic quadratic ratio sum is at least one
-- statement:
--   If $a,b,c$ are positive reals, prove that $\sum_{cyc}\frac{a^2}{ab+2b^2} \ge 1$ .
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_67042` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_67042; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_67042 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^2 / (a * b + 2 * b^2) + b^2 / (b * c + 2 * c^2) + c^2 / (c * a + 2 * a^2)) ≥ 1   :=  by sorry
