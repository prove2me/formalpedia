-- Prove2me | Theorems.Thm_lean_workbook_plus_19517
-- name    : lean_workbook_plus_19517
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/04e79627-ce2d-4d10-8b17-1091f4cf4c85
-- statement:
--   Note that for all $a,b \ge 0$ we have ${a^2} + ab + {b^2} \ge \frac{3}{4}{\left( {a + b} \right)^2}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_19517 (a b : ℝ) (hab : a ≥ 0 ∧ b ≥ 0) : a^2 + a*b + b^2 ≥ 3/4 * (a + b)^2   :=  by sorry
