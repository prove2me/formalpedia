-- Prove2me | Theorems.Thm_lean_workbook_plus_8657
-- name    : lean_workbook_plus_8657
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/865d8460-1487-407e-8416-b8c1743538b4
-- statement:
--   Let $ a,b,c$ be positive reals, show that \n $ a^3b^2 + b^3c^2 + c^3a^2 \geq a^2b^2c + b^2c^2a + c^2a^2b$ . \n
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_8657 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a^3 * b^2 + b^3 * c^2 + c^3 * a^2 ≥ a^2 * b^2 * c + b^2 * c^2 * a + c^2 * a^2 * b   :=  by sorry
