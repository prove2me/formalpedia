-- Prove2me | Theorems.Thm_lean_workbook_plus_4779
-- name    : lean_workbook_plus_4779
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/0db44b5a-c512-43a7-a6c7-64d74ba9b586
-- statement:
--   Prove that $ \frac {a^2(b + c)}{b^2 + c^2} + \frac {b^2(c + a)}{c^2 + a^2} + \frac {c^2(a + b)}{a^2 + b^2} \geq a + b + c$ using Chebyshev's and Nesbitt's inequalities.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_4779 : ∀ a b c : ℝ, (a^2 * (b + c) / (b^2 + c^2) + b^2 * (c + a) / (c^2 + a^2) + c^2 * (a + b) / (a^2 + b^2) ≥ a + b + c)   :=  by sorry
