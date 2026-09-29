-- Prove2me | Theorems.Thm_lean_workbook_plus_30378
-- name    : lean_workbook_plus_30378
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/fe43a54e-4ec3-4205-ab01-da824150136a
-- statement:
--   Prove that in a right-angled triangle $ABC$, $ \sqrt{b^{2}+c^{2}}\geq\frac{\sqrt{2}}{2}(b+c)$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_30378 (b c : ℝ) (h : b > 0 ∧ c > 0) (hab : b * b + c * c = 1) : Real.sqrt (b * b + c * c) ≥ Real.sqrt 2 / 2 * (b + c)   :=  by sorry
