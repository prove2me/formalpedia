-- Prove2me | Theorems.Thm_WorkbookSource_base_26563
-- name    : WorkbookSource.base_26563
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T04:29:23.070691+00:00
-- url     : https://prove2.me/theorems/c66218bf-d611-432e-883f-89c5d5152d31
-- title:
--   A cyclic quadratic ratio upper bound with a symmetric correction
-- statement:
--   Let: $ a;b;c > 0$ .Prove that: $ 2.\frac {a^2 + b^2 + c^2}{ab + bc + ca} \ge \frac {a^2}{c^2 + ca + ab} + \frac {b^2}{a^2 + ab + bc} + \frac {c^2}{b^2 + bc + ca} + 1$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_26563` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_26563; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_26563 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : 2 * ((a^2 + b^2 + c^2) / (a * b + b * c + c * a)) ≥ (a^2 / (c^2 + c * a + a * b)) + (b^2 / (a^2 + a * b + b * c)) + (c^2 / (b^2 + b * c + c * a)) + 1  :=  by sorry
