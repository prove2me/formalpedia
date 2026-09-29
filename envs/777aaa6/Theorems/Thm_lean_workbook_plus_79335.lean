-- Prove2me | Theorems.Thm_lean_workbook_plus_79335
-- name    : lean_workbook_plus_79335
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/ffbfa1f5-dc40-4780-bf33-f6c384a287bf
-- statement:
--   Prove the identity $\cos{\left(\frac{\pi}{2^{n+1}}\right)} = 2\cos^2{\left(\frac{\pi}{2^{n+2}}\right)} - 1$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_79335 : ∀ n : ℕ, (cos (π / 2 ^ (n + 1)) : ℝ) = 2 * cos (π / 2 ^ (n + 2)) ^ 2 - 1   :=  by sorry
