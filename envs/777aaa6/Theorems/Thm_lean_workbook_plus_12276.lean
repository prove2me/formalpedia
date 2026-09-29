-- Prove2me | Theorems.Thm_lean_workbook_plus_12276
-- name    : lean_workbook_plus_12276
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/6dbfbc0b-49d4-44e4-9ec2-65f9f1231a23
-- statement:
--   Prove or disprove the inequality $(\mu^2+1)(x^4+y^2z^2)\geq(\mu x^2+yz)^2$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_12276 (x y z μ : ℝ) : (μ^2 + 1) * (x^4 + y^2 * z^2) ≥ (μ * x^2 + y * z)^2   :=  by sorry
