-- Prove2me | Theorems.Thm_lean_workbook_plus_2460
-- name    : lean_workbook_plus_2460
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/a1463718-876e-47db-8d1b-3cda6db99917
-- statement:
--   By Cauchy-Schwarz inequality; $(a^2b+c^2d)(b+d) \geq bd(a+c)^2$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_2460 (a b c d : ℝ) : (a^2 * b + c^2 * d) * (b + d) ≥ b * d * (a + c)^2   :=  by sorry
