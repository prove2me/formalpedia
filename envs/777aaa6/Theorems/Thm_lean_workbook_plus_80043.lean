-- Prove2me | Theorems.Thm_lean_workbook_plus_80043
-- name    : lean_workbook_plus_80043
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/e8fd02e6-a58d-42fa-a0c3-45c799dc7168
-- statement:
--   Prove that $\sqrt{a^{2}+b^{2}+ab}\geq\frac{\sqrt{3}}{2}(a+b)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_80043 (a b: ℝ) : Real.sqrt (a ^ 2 + b ^ 2 + a * b) ≥ Real.sqrt 3 / 2 * (a + b)   :=  by sorry
