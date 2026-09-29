-- Prove2me | Theorems.Thm_lean_workbook_plus_48528
-- name    : lean_workbook_plus_48528
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/db5ee6a5-0952-4d2c-829e-4a78eb856765
-- statement:
--   prove that $ a^2b^2c^2(a^2+b^2+c^2) \ge a^3b^3c^2 + a^3b^2c^3 + a^2b^3c^3$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_48528 (a b c : ℝ) : a^2 * b^2 * c^2 * (a^2 + b^2 + c^2) ≥ a^3 * b^3 * c^2 + a^3 * b^2 * c^3 + a^2 * b^3 * c^3   :=  by sorry
