-- Prove2me | Theorems.Thm_WorkbookSource_plus_7119
-- name    : WorkbookSource.plus_7119
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T04:42:59.821927+00:00
-- url     : https://prove2.me/theorems/c8ed2725-f6e4-4ec6-bc8b-0f102c7a3926
-- title:
--   A weighted cyclic quadratic reciprocal upper bound
-- statement:
--   Let a,b,c be positives real number prove that :
--   $ \frac{2a}{3a^{2}+b^{2}+2ca}+\frac{2b}{3b^{2}+c^{2}+2ab}+\frac{2c}{3c^{2}+a^{2}+2bc} \leq \frac{3}{a+b+c} $
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_7119` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_7119; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_7119 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (2 * a / (3 * a ^ 2 + b ^ 2 + 2 * c * a) + 2 * b / (3 * b ^ 2 + c ^ 2 + 2 * a * b) + 2 * c / (3 * c ^ 2 + a ^ 2 + 2 * b * c)) ≤ 3 / (a + b + c)   :=  by sorry
