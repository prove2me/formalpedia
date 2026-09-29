-- Prove2me | Theorems.Thm_lean_workbook_plus_10318
-- name    : lean_workbook_plus_10318
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/5c257d5d-ca51-4a94-919f-1b546d17430b
-- statement:
--   Prove: $( (\frac{1}{\sqrt{3}})^2 + (\frac{1}{\sqrt{3}})^2 + (\frac{1}{\sqrt{3}})^2 ) * ( (3 - a)^2 + (3 - b)^2 + (3 - c)^2 ) \geq (\frac{3 - a}{\sqrt{3}} + \frac{3 - b}{\sqrt{3}} + \frac{3 - c}{\sqrt{3}})^2
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_10318 {a b c : ℝ} : (1 / Real.sqrt 3 ^ 2 + 1 / Real.sqrt 3 ^ 2 + 1 / Real.sqrt 3 ^ 2) * ((3 - a) ^ 2 + (3 - b) ^ 2 + (3 - c) ^ 2) ≥ (1 / Real.sqrt 3 * (3 - a) + 1 / Real.sqrt 3 * (3 - b) + 1 / Real.sqrt 3 * (3 - c)) ^ 2   :=  by sorry
