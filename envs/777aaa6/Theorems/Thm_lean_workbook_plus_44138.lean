-- Prove2me | Theorems.Thm_lean_workbook_plus_44138
-- name    : lean_workbook_plus_44138
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/7048620b-eaa0-4c0f-811f-e4b30bee4b8c
-- statement:
--   Let $a,b$ be positive reals. Prove that \n ${{a}^{2}}+{{b}^{2}}+\frac{1}{12}\ge 3ab(1-ab)\Leftrightarrow 12{{a}^{2}}+12{{b}^{2}}+1\ge 36ab(1-ab)\Leftrightarrow {{(a-b)}^{2}}+{{(6ab-1)}^{2}}\ge 0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_44138 (a b : ℝ) : a^2 + b^2 + 1 / 12 ≥ 3 * a * b * (1 - a * b) ↔ 12 * a^2 + 12 * b^2 + 1 ≥ 36 * a * b * (1 - a * b)   :=  by sorry
