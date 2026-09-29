-- Prove2me | Theorems.Thm_lean_workbook_plus_38511
-- name    : lean_workbook_plus_38511
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/b3c9a299-37fe-472f-b308-0eac0e62b9f6
-- statement:
--   Prove the lemma: $(x^3y^3)^m = x^{3m}y^{3m}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_38511 (x y : ℝ) (m : ℤ) : (x^3*y^3)^m = x^(3*m)*y^(3*m)   :=  by sorry
