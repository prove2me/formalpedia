-- Prove2me | Theorems.Thm_lean_workbook_plus_69790
-- name    : lean_workbook_plus_69790
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/48278571-a506-47d0-ad79-ff9aceba4d3a
-- statement:
--   Prove that $\sin(\frac{a}{2})(\sin(\frac{a}{2})-1) \geq -\frac{1}{4}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_69790 : ∀ a : ℝ, sin (a / 2) * (sin (a / 2) - 1) ≥ -1 / 4   :=  by sorry
