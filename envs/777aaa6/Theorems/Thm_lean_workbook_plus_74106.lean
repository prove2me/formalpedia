-- Prove2me | Theorems.Thm_lean_workbook_plus_74106
-- name    : lean_workbook_plus_74106
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/def2fd8d-288e-4143-a53d-0404cc4c37d7
-- statement:
--   Show that the simplified inequality $\sqrt{(a^2 + b^2)(4b^2 + a^2)} \geq 3ab$ follows from the Cauchy-Schwarz inequality.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_74106 (a b : ℝ) : Real.sqrt ((a^2 + b^2) * (4 * b^2 + a^2)) ≥ 3 * a * b   :=  by sorry
