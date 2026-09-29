-- Prove2me | Theorems.Thm_lean_workbook_plus_49236
-- name    : lean_workbook_plus_49236
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/be657bc7-1809-4d7b-809c-ea87ebd3417e
-- statement:
--   Prove the inequality: $a^3b^2+b^3c^2+c^3a^2\ge a^3bc+b^3ac+c^3ab$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_49236 : ∀ a b c : ℝ, a^3 * b^2 + b^3 * c^2 + c^3 * a^2 ≥ a^3 * b * c + b^3 * a * c + c^3 * a * b   :=  by sorry
