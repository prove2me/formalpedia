-- Prove2me | Theorems.Thm_lean_workbook_plus_40
-- name    : lean_workbook_plus_40
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/ddeae32b-26bb-4b03-9b22-6afd34b69fdd
-- statement:
--   The correct answer is $A$ . \nIf $0< \\theta < \\frac{\\pi}{4}$ then $\\cos \\theta >\\sin\\theta$ and the rest is easy.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_40 :
  ∀ θ : ℝ, 0 < θ ∧ θ < Real.pi / 4 → Real.cos θ > Real.sin θ   :=  by sorry
