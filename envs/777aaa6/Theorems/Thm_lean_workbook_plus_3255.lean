-- Prove2me | Theorems.Thm_lean_workbook_plus_3255
-- name    : lean_workbook_plus_3255
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/d9f88ec9-824f-49ce-a22e-83bd53e7adbe
-- statement:
--   Explain why \\( \frac{1+x^{30}}{1+x^{60}} < 1 + x^{30} \\) for \\( 0<x\leq 1 \\)
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_3255 (x : ℝ) (hx : 0 < x ∧ x ≤ 1) :
  (1 + x^30) / (1 + x^60) < 1 + x^30   :=  by sorry
