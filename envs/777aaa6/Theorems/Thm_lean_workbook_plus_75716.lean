-- Prove2me | Theorems.Thm_lean_workbook_plus_75716
-- name    : lean_workbook_plus_75716
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/801ea3fa-8b0d-48da-8dad-b861c97414c1
-- statement:
--   Given $(b+c)^{2}+(b-c)^{2}=2\left(b^{2}+c^{2}\right)$, prove that $|b-c|=\sqrt{2\left(b^{2}+c^{2}\right)-(b+c)^{2}}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_75716 (b c : ℝ) : |b - c| = Real.sqrt (2 * (b^2 + c^2) - (b + c)^2)   :=  by sorry
