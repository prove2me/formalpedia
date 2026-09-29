-- Prove2me | Theorems.Thm_lean_workbook_plus_60545
-- name    : lean_workbook_plus_60545
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/073615c9-bd8c-4a2e-8919-374cc38d685f
-- statement:
--   Prove that if we have equations $ax + by = c$ and $dx + ey = f$, then $(a + d)x + (b + e)y = c + f$ also passes through the intersection of the lines with the original equations.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_60545 (a b c d e f : ℝ) : (a * x + b * y = c ∧ d * x + e * y = f) → (a + d) * x + (b + e) * y = c + f   :=  by sorry
