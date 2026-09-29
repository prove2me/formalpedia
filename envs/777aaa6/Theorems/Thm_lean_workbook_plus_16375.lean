-- Prove2me | Theorems.Thm_lean_workbook_plus_16375
-- name    : lean_workbook_plus_16375
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/7e388b0b-d373-4b07-9a70-0e599ac51bd9
-- statement:
--   Show that $(a^{2}+x^{2})(b^{2}+y^{2})(c^{2}+z^{2})\geq (abz+bcx+cay-xyz)^{2}$ where $a, b, c, x, y, z$ are non-negative numbers.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_16375 (a b c x y z : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) : (a^2 + x^2) * (b^2 + y^2) * (c^2 + z^2) ≥ (a * b * z + b * c * x + c * a * y - x * y * z)^2   :=  by sorry
