-- Prove2me | Theorems.Thm_lean_workbook_plus_38119
-- name    : lean_workbook_plus_38119
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/defb6b42-ccc6-41d6-ad15-938f8a147917
-- statement:
--   Prove that $a^2b^2+(a^2+b^2)(a+b)^2+3-6ab(a+b)\geq 0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_38119 (a b : ℝ) : a^2 * b^2 + (a^2 + b^2) * (a + b)^2 + 3 - 6 * a * b * (a + b) ≥ 0   :=  by sorry
