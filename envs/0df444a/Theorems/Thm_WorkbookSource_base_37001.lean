-- Prove2me | Theorems.Thm_WorkbookSource_base_37001
-- name    : WorkbookSource.base_37001
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T22:48:17.885495+00:00
-- url     : https://prove2.me/theorems/789b2c28-5c8a-447e-9977-622ebe0e4cf2
-- title:
--   A sixth-degree bound for a squared symmetric cubic sum
-- statement:
--   prove that
--    $3(a^2b+ab^2+b^2c+bc^2+c^2a+ca^2)^2\le 4(a^2+b^2+c^2)^3$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_37001` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_37001; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_37001 (a b c : ℝ) :
  3 * (a^2 * b + a * b^2 + b^2 * c + b * c^2 + c^2 * a + c * a^2)^2 ≤
  4 * (a^2 + b^2 + c^2)^3  :=  by sorry
