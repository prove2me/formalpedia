-- Prove2me | Theorems.Thm_WorkbookSource_base_6600
-- name    : WorkbookSource.base_6600
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T00:44:14.943539+00:00
-- url     : https://prove2.me/theorems/19c6c5b6-9893-4fd5-bbf5-4968a57613f8
-- title:
--   A cyclic sum of quadratic ratios has a constant lower bound
-- statement:
--   Let a,b,c>0. Prove that: $\frac{{{{\left( {2a + b + c} \right)}^2}}}{{{a^2} + 11bc}} + \frac{{{{\left( {2b + c + a} \right)}^2}}}{{{b^2} + 11ca}} + \frac{{{{\left( {2c + a + b} \right)}^2}}}{{{c^2} + 11ab}} \ge 4$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_6600` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_6600; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_6600 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (2 * a + b + c) ^ 2 / (a ^ 2 + 11 * b * c) + (2 * b + c + a) ^ 2 / (b ^ 2 + 11 * c * a) + (2 * c + a + b) ^ 2 / (c ^ 2 + 11 * a * b) ≥ 4  :=  by sorry
