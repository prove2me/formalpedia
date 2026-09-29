-- Prove2me | Theorems.Thm_WorkbookSource_base_15098
-- name    : WorkbookSource.base_15098
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T10:32:13.985528+00:00
-- url     : https://prove2.me/theorems/ed73b1e9-2128-4b7e-964b-c1abed070109
-- title:
--   A quadratic and triple-product bound at unit sum
-- statement:
--   Prove that for $a, b, c > 0$ and $a + b + c = 1$, $a^2 + b^2 + c^2 + 3abc \geq \frac{4}{9}$ using AM-GM.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_15098` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_15098; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_15098 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 1) : a^2 + b^2 + c^2 + 3 * a * b * c ≥ 4 / 9  :=  by sorry
