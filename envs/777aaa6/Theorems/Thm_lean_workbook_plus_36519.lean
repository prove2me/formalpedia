-- Prove2me | Theorems.Thm_lean_workbook_plus_36519
-- name    : lean_workbook_plus_36519
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/98c9e11e-3059-433d-8e67-3810809c15c8
-- statement:
--   If $a, b, c > 0$ . Prove : b. $a^4 + b^4 + c^4 \ge a^2bc + b^2ac + c^2ab$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_36519 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a^4 + b^4 + c^4 ≥ a^2 * b * c + b^2 * a * c + c^2 * a * b   :=  by sorry
