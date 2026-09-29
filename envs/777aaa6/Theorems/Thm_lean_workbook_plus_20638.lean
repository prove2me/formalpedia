-- Prove2me | Theorems.Thm_lean_workbook_plus_20638
-- name    : lean_workbook_plus_20638
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/4d88feed-9692-4e2e-81b3-19193b6d3021
-- statement:
--   $ \iff $ $\cos 2x\left(\sin (x+\frac{\pi}3)-1\right)=0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_20638 : ∀ x : ℝ, cos 2*x * (sin (x + π/3) - 1) = 0 ↔ cos 2*x = 0 ∨ sin (x + π/3) = 1   :=  by sorry
