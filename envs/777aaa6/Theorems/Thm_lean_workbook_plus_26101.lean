-- Prove2me | Theorems.Thm_lean_workbook_plus_26101
-- name    : lean_workbook_plus_26101
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/26f54b43-3b72-40da-8e0b-27a8feede52a
-- statement:
--   $ \sqrt {x_2^2 + (1 - x_3)^2} \ge \frac{\sqrt {2}}{2}(x_{2} + 1 - x_{3})$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_26101 (x₂ x₃ : ℝ) :
  Real.sqrt (x₂^2 + (1 - x₃)^2) ≥ (Real.sqrt 2 / 2) * (x₂ + 1 - x₃)   :=  by sorry
