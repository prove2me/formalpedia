-- Prove2me | Theorems.Thm_WorkbookSource_plus_45396
-- name    : WorkbookSource.plus_45396
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T05:15:55.781668+00:00
-- url     : https://prove2.me/theorems/325260d5-ecc3-44dc-adad-2b6d3a0aedf3
-- title:
--   A cyclic fifth-power ratio sum bounds the quadratic sum
-- statement:
--   Let $a, b, c$ be positive reals. Show that $\frac{a^5}{bc^2} + \frac{b^5}{ca^2} + \frac{c^5}{ab^2} \ge a^2 + b^2 + c^2.$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_45396` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_45396; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_45396 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a^5 / b / c^2 + b^5 / c / a^2 + c^5 / a / b^2 ≥ a^2 + b^2 + c^2   :=  by sorry
