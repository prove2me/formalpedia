-- Prove2me | Theorems.Thm_lean_workbook_plus_48710
-- name    : lean_workbook_plus_48710
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/92835e90-06f9-4bdb-b606-3c5f01270914
-- statement:
--   Prove that $a^4 + b^4 + c^4 + a^2b^2 + b^2c^2 + c^2a^2 \geq a^3b + ab^3 + b^3c + bc^3 + c^3a + ca^3$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_48710 : ∀ a b c : ℝ, a ^ 4 + b ^ 4 + c ^ 4 + a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * a ^ 2 ≥ a ^ 3 * b + a * b ^ 3 + b ^ 3 * c + b * c ^ 3 + c ^ 3 * a + c * a ^ 3   :=  by sorry
