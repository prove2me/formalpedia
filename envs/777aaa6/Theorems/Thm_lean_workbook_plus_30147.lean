-- Prove2me | Theorems.Thm_lean_workbook_plus_30147
-- name    : lean_workbook_plus_30147
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/ca980f74-74bd-4e27-85cd-066f0568452a
-- statement:
--   $sin a sin b=\frac{1}{2}(cos(a-b)-cos(a+b))$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_30147 : ∀ a b : ℝ, sin a * sin b = 1/2 * (cos (a - b) - cos (a + b))   :=  by sorry
