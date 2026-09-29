-- Prove2me | Theorems.Thm_lean_workbook_plus_50840
-- name    : lean_workbook_plus_50840
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/bec17602-f832-4ba0-937d-798102ed6e70
-- statement:
--   Prove that $\left( {a}^{2}+bc \right) ^{-1}+ \left( {b}^{2}+ac \right) ^{-1}+ \left( {c}^{2}+ab \right) ^{-1}\geq 3\, \left( ab+ac+bc \right) ^{-1}+{\frac {243}{2}}\,{\frac {{a}^{2}{b}^{2}{c}^{2}}{ \left( a+b+c \right) ^{2} \left( ab+ac+bc \right) ^{3}}}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_50840 : ∀ a b c : ℝ, (a^2 + b * c)^(-1:ℤ) + (b^2 + a * c)^(-1:ℤ) + (c^2 + a * b)^(-1:ℤ) ≥ 3 * (a * b + a * c + b * c)^(-1:ℤ) + (243 / 2) * (a^2 * b^2 * c^2) / ((a + b + c)^2 * (a * b + a * c + b * c)^3)   :=  by sorry
