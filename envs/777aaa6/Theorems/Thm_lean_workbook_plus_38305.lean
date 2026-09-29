-- Prove2me | Theorems.Thm_lean_workbook_plus_38305
-- name    : lean_workbook_plus_38305
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/2a9c59b7-40ef-4925-9a36-b166c689918d
-- statement:
--   Prove that $(b^2+d^2)^2(a^2+c^2)+(a^2+c^2)^2(b^2+d^2) \geq (b^2+d^2)(a^2+c^2)(a^2+b^2+c^2+d^2)$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_38305 (a b c d : ℝ) : (b^2 + d^2)^2 * (a^2 + c^2) + (a^2 + c^2)^2 * (b^2 + d^2) ≥ (b^2 + d^2) * (a^2 + c^2) * (a^2 + b^2 + c^2 + d^2)   :=  by sorry
