-- Prove2me | Theorems.Thm_lean_workbook_plus_58283
-- name    : lean_workbook_plus_58283
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/49dba101-e759-4fc5-9087-b25c3939fe81
-- statement:
--   By law of sines on triangle $ADB$ and $CDB$ , we have: \n\n $$\frac{BC}{sin(30^\circ)} = \frac{BD}{sin(90^\circ - \alpha)}$$ $$\frac{AB}{sin(30^\circ)}= \frac{BD}{sin(30^\circ-\alpha)}$$ Multipling both and using the length condition: \n\n $$sin(30^\circ-\alpha)sin(90^\circ-\alpha) = \frac{1}{4}$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_58283 :
  ∀ α : ℝ, (30 < α ∧ α < 90 ∧ sin (30 - α) * sin (90 - α) = 1 / 4)   :=  by sorry
