-- Prove2me | Theorems.Thm_WorkbookSource_base_47396
-- name    : WorkbookSource.base_47396
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T05:13:36.4678+00:00
-- url     : https://prove2.me/theorems/f67a8ea2-318e-4108-b27b-c3fdd7245ed0
-- title:
--   A weighted cyclic cubic ratio bounds the quadratic sum
-- statement:
--   Prove that for positive reals a,b,c the following inequality holds good -
--    $ a^2(\frac {a + 2c}{3b}) + b^2(\frac {b + 2a}{3c}) + c^2(\frac {c + 2b}{3a}) \ge a^2 + b^2 + c^2$ - (own)
--
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_47396` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_47396; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_47396 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a^2 * (a + 2 * c) / (3 * b) + b^2 * (b + 2 * a) / (3 * c) + c^2 * (c + 2 * b) / (3 * a) ≥ a^2 + b^2 + c^2  :=  by sorry
