-- Prove2me | Theorems.Thm_lean_workbook_plus_51130
-- name    : lean_workbook_plus_51130
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/55f95edc-4bcc-4e2a-82c0-4f027cfba04d
-- statement:
--   Thus, it remains to prove that $ \sum_{cyc}(a^{2}b^{2}-a^{2}bc+2a^{4}+4a^{2}b^{2})\geq\sum_{cyc}(2a^{3}b+2a^{3}c+2a^{2}bc)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_51130 (a b c : ℝ) : (a^2 * b^2 - a^2 * b * c + 2 * a^4 + 4 * a^2 * b^2) + (b^2 * c^2 - b^2 * c * a + 2 * b^4 + 4 * b^2 * c^2) + (c^2 * a^2 - c^2 * a * b + 2 * c^4 + 4 * c^2 * a^2) ≥ (2 * a^3 * b + 2 * a^3 * c + 2 * a^2 * b * c) + (2 * b^3 * c + 2 * b^3 * a + 2 * b^2 * c * a) + (2 * c^3 * a + 2 * c^3 * b + 2 * c^2 * a * b)   :=  by sorry
