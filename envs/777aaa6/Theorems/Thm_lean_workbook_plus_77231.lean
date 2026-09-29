-- Prove2me | Theorems.Thm_lean_workbook_plus_77231
-- name    : lean_workbook_plus_77231
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/171c5a76-091b-4c3e-91de-d12ce02de202
-- statement:
--   Prove that a|a or provide a counterexample, where the notation 'm|n' implies that n is divisible by m. You must also specify $ a\\neq0.$ Unless that's the counterexample you're looking for.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_77231 (a : ℤ) (ha : a ≠ 0) : a ∣ a   :=  by sorry
