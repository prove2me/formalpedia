-- Prove2me | Theorems.Thm_lean_workbook_plus_17311
-- name    : lean_workbook_plus_17311
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/082ef6d5-271c-4683-9db9-4e6fe88ce9ff
-- statement:
--   Prove that in a right-angled triangle $ABC$, $ \sqrt{\frac{b^{2}+c^{2}}{2}}\geq\frac{b+c}{2}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_17311 (b c : ℝ) : Real.sqrt ((b^2 + c^2) / 2) ≥ (b + c) / 2   :=  by sorry
