-- Prove2me | Theorems.Thm_lean_workbook_plus_68269
-- name    : lean_workbook_plus_68269
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/2c0ce34e-0fbd-4d35-8af6-c18b48aaf119
-- statement:
--   $\cos(2x)=\cos(x+x)=\cos^{2}(x)-\sin^{2}(x)$\n\nbut $\cos^{2}(x)=1-\sin^{2}(x)$\n\nthen, $\cos(2x)=1-2\sin^{2}(x)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_68269 : ∀ x : ℝ, Real.cos (2 * x) = 1 - 2 * (Real.sin x)^2   :=  by sorry
