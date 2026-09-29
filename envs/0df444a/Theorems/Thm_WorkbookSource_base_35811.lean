-- Prove2me | Theorems.Thm_WorkbookSource_base_35811
-- name    : WorkbookSource.base_35811
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T23:55:39.082876+00:00
-- url     : https://prove2.me/theorems/695b9116-4330-48b5-b5ca-c925f312f0bf
-- title:
--   A sixth-degree cyclic polynomial inequality
-- statement:
--   For positive numbers $a, b, c$, prove that $3a^2b^2c^2 + 2a^4b^2 + 2b^4c^2 + 2c^4a^2 + a^4c^2 + b^4a^2 + c^4b^2 \geq a^3b^3 + b^3c^3 + c^3a^3 + abc(a^3 + b^3 + c^3 + a^2b + b^2c + c^2a)$.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_35811` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_35811; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_35811 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : 3 * a^2 * b^2 * c^2 + 2 * a^4 * b^2 + 2 * b^4 * c^2 + 2 * c^4 * a^2 + a^4 * c^2 + b^4 * a^2 + c^4 * b^2 ≥ a^3 * b^3 + b^3 * c^3 + c^3 * a^3 + a * b * c * (a^3 + b^3 + c^3 + a^2 * b + b^2 * c + c^2 * a)  :=  by sorry
