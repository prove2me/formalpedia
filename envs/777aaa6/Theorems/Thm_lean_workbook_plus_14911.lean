-- Prove2me | Theorems.Thm_lean_workbook_plus_14911
-- name    : lean_workbook_plus_14911
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/e2b6098f-7a0b-4ac9-8905-65f1790e3615
-- statement:
--   On the interval $\left[0,\dfrac{\pi}{2} \right], \sin x$ is strictly increasing and $\cos x$ is strictly decreasing.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_14911 : ∀ x y : ℝ, x ∈ Set.Icc 0 (π / 2) ∧ y ∈ Set.Icc 0 (π / 2) → x < y → sin x < sin y ∧ cos y < cos x   :=  by sorry
