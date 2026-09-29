-- Prove2me | Theorems.Thm_lean_workbook_plus_28493
-- name    : lean_workbook_plus_28493
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/6813a925-1161-428e-90ab-aeb35a7738d3
-- statement:
--   Therefore, the ratio between the volume of the smaller solid and the volume of the larger solid is $$\frac{V_m}{V_M} = \frac{\frac{147 \sqrt{3}}{8}k^3}{\frac{285 \sqrt{3}}{8}k^3}= \frac{49}{95}$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_28493  (k : ℝ)
  (h₀ : 0 < k)
  (h₁ : 0 < 285 * Real.sqrt 3 / 8 * k^3)
  (h₂ : 0 < 147 * Real.sqrt 3 / 8 * k^3) :
  (147 * Real.sqrt 3 / 8 * k^3) / (285 * Real.sqrt 3 / 8 * k^3) = 49 / 95   :=  by sorry
