-- Prove2me | Theorems.Thm_lean_workbook_plus_18377
-- name    : lean_workbook_plus_18377
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/96b274f2-ef20-4037-acf6-647c1c80cd11
-- statement:
--   Prove that $1/2\,{a}^{3}+1/2\,{b}^{3}+1/2\,{c}^{3}+9/2\,bca\leq {a}^{2} \left( b+c \right) +{b}^{2} \left( c+a \right) +{c}^{2} \left( a+b \right)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_18377 : ∀ a b c : ℝ, (1/2 * a^3 + 1/2 * b^3 + 1/2 * c^3 + 9/2 * b * c * a) ≤ (a^2 * (b + c) + b^2 * (c + a) + c^2 * (a + b))   :=  by sorry
