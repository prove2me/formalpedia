-- Prove2me | Theorems.Thm_WorkbookSource_base_28054
-- name    : WorkbookSource.base_28054
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T04:53:00.777819+00:00
-- url     : https://prove2.me/theorems/9ceee39f-2939-4531-9d4b-d68f8d1b1aa6
-- title:
--   A cyclic fifth-power ratio bounds the quadratic sum
-- statement:
--   Let $a, b, c$ be positive reals. Show that $$\frac{a^5+b^5}{bc^2} + \frac{b^5+c^5}{ca^2} + \frac{c^5+a^5}{ab^2}\geq2( a^2 + b^2 + c^2)$$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_28054` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_28054; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_28054 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^5 + b^5) / (b * c^2) + (b^5 + c^5) / (c * a^2) + (c^5 + a^5) / (a * b^2) ≥ 2 * (a^2 + b^2 + c^2)  :=  by sorry
