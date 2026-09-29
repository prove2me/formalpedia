-- Prove2me | Theorems.Thm_lean_workbook_plus_27167
-- name    : lean_workbook_plus_27167
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/52bc9e2d-1eb8-4376-a4e8-5d8de81b7953
-- statement:
--   For $a,b,c,d$, show that $a^4+b^4+c^4+d^4\geq a^2bc+b^2cd+c^2da+d^2ab$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_27167 : ∀ a b c d : ℝ, a^4+b^4+c^4+d^4 ≥ a^2*b*c + b^2*c*d + c^2*d*a + d^2*a*b   :=  by sorry
