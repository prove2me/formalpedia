-- Prove2me | Theorems.Thm_WorkbookSource_base_374
-- name    : WorkbookSource.base_374
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T23:03:25.05695+00:00
-- url     : https://prove2.me/theorems/c0159cf4-d5f7-43b9-929c-8df4105103cf
-- title:
--   A product bound for two cyclic cubic sums
-- statement:
--   Show that for positive reals $a,b,c$ ,
--
--    $$(a^2b + b^2c + c^2a)(ab^2 + bc^2 + ca^2) \geq 9a^2b^2c^2$$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_374` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_374; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_374 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^2 * b + b^2 * c + c^2 * a) * (a * b^2 + b * c^2 + c * a^2) ≥ 9 * a^2 * b^2 * c^2  :=  by sorry
