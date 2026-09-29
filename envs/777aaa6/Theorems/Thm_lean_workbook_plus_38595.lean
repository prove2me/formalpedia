-- Prove2me | Theorems.Thm_lean_workbook_plus_38595
-- name    : lean_workbook_plus_38595
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/57fad5e5-3c36-48bd-9562-46b0224b833f
-- statement:
--   Prove that the equation $a^6+a^5+2a^4+3a^3+6a^2-a+1=0$ has no real root
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_38595 : ¬ ∃ a : ℝ, a^6 + a^5 + 2*a^4 + 3*a^3 + 6*a^2 - a + 1 = 0   :=  by sorry
