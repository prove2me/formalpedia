-- Prove2me | Theorems.Thm_lean_workbook_plus_51211
-- name    : lean_workbook_plus_51211
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/5bd8fcb2-22e3-478a-ad9a-11a1501a1b4c
-- statement:
--   Now apply QM-AM: $\sqrt{\frac{y^2+x^2+x^2}{3}}\geq\frac{y+x+x}{3}\Rightarrow \sqrt{2x^2+y^2}\geq\frac{2x+y}{\sqrt{3}}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_51211  (x y : ℝ) :
  Real.sqrt (2 * x^2 + y^2) ≥ (2 * x + y) / Real.sqrt 3   :=  by sorry
