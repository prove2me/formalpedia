-- Prove2me | Theorems.Thm_lean_workbook_plus_76550
-- name    : lean_workbook_plus_76550
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/5b860424-12bc-49dd-a822-2f1baa160a54
-- statement:
--   prove that: $\sqrt{a^{2}+\frac{1}{a}}\geq \frac{a+3}{2\sqrt{2}} $
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_76550 (a : ℝ) (ha : a > 0) : Real.sqrt (a^2 + 1/a) ≥ (a + 3) / (2 * Real.sqrt 2)   :=  by sorry
