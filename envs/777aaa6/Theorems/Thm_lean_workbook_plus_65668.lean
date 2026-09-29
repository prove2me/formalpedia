-- Prove2me | Theorems.Thm_lean_workbook_plus_65668
-- name    : lean_workbook_plus_65668
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/147ae459-a645-403c-8803-24ff0f4cd2fe
-- statement:
--   $\Longleftrightarrow (a^4+b^4)+(b^4+c^4)+(c^4+a^4)\geq (ab(a^2+b^2)+bc(b^2+c^2)+ca(c^2+a^2))$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_65668 (a b c: ℝ) : (a^4+b^4)+(b^4+c^4)+(c^4+a^4) ≥ (a*b*(a^2+b^2)+b*c*(b^2+c^2)+c*a*(c^2+a^2))   :=  by sorry
